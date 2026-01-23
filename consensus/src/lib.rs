// Copyright(C) Facebook, Inc. and its affiliates.
use config::{Committee, Stake};
use crypto::Hash as _;
use crypto::{Digest, PublicKey};
use log::{debug, info, log_enabled, warn};
use primary::{Certificate, Round};
use std::cmp::{max, Ordering};
use std::collections::{HashMap, HashSet, VecDeque};
use tokio::sync::mpsc::{Receiver, Sender};

#[cfg(test)]
#[path = "tests/consensus_tests.rs"]
pub mod consensus_tests;

/// The representation of the DAG in memory.
type Dag = HashMap<Round, HashMap<PublicKey, (Digest, Certificate)>>;

/// The state that needs to be persisted for crash-recovery.
struct State {
    /// The last committed round.
    last_committed_round: Round,
    // Keeps the last committed round for each authority. This map is used to clean up the dag and
    // ensure we don't commit twice the same certificate.
    last_committed: HashMap<PublicKey, Round>,
    /// Keeps the latest committed certificate (and its parents) for every authority. Anything older
    /// must be regularly cleaned up through the function `update`.
    dag: Dag,
    /// Tracks the rounds in which each authority produced committed certificates.
    activity_rounds: HashMap<PublicKey, VecDeque<Round>>,
    /// Tracks recent commit delays for each authority (commit round - certificate round).
    delay_history: HashMap<PublicKey, VecDeque<Round>>,
    /// Tracks recent anchor (leader) votes for structural contribution scoring.
    anchor_history: VecDeque<AnchorRecord>,
    /// Cached reputation scores for each authority.
    reputations: HashMap<PublicKey, f64>,
}

struct AnchorRecord {
    round: Round,
    voters: HashSet<PublicKey>,
}

impl State {
    fn new(genesis: Vec<Certificate>) -> Self {
        let genesis = genesis
            .into_iter()
            .map(|x| (x.origin(), (x.digest(), x)))
            .collect::<HashMap<_, _>>();

        Self {
            last_committed_round: 0,
            last_committed: genesis.iter().map(|(x, (_, y))| (*x, y.round())).collect(),
            dag: [(0, genesis)].iter().cloned().collect(),
            activity_rounds: HashMap::new(),
            delay_history: HashMap::new(),
            anchor_history: VecDeque::new(),
            reputations: HashMap::new(),
        }
    }

    /// Update and clean up internal state base on committed certificates.
    fn update(&mut self, certificate: &Certificate, gc_depth: Round) {
        self.last_committed
            .entry(certificate.origin())
            .and_modify(|r| *r = max(*r, certificate.round()))
            .or_insert_with(|| certificate.round());

        let last_committed_round = *self.last_committed.values().max().unwrap();
        self.last_committed_round = last_committed_round;

        for (name, round) in &self.last_committed {
            self.dag.retain(|r, authorities| {
                authorities.retain(|n, _| n != name || r >= round);
                !authorities.is_empty() && r + gc_depth >= last_committed_round
            });
        }
    }

    fn track_commit(&mut self, certificate: &Certificate, commit_round: Round) {
        let min_round = commit_round.saturating_sub(49);
        let rounds = self
            .activity_rounds
            .entry(certificate.origin())
            .or_insert_with(VecDeque::new);
        rounds.push_back(certificate.round());
        while rounds.front().map_or(false, |r| *r < min_round) {
            rounds.pop_front();
        }

        let delay = commit_round.saturating_sub(certificate.round());
        let delays = self
            .delay_history
            .entry(certificate.origin())
            .or_insert_with(VecDeque::new);
        delays.push_back(delay);
        while delays.len() > 50 {
            delays.pop_front();
        }
    }

    fn record_anchor(&mut self, leader: &Certificate) {
        let anchor_round = leader.round();
        let min_round = anchor_round.saturating_sub(99);
        self.anchor_history.retain(|record| record.round >= min_round);

        let voters = leader.votes.iter().map(|(name, _)| *name).collect();
        self.anchor_history.push_back(AnchorRecord {
            round: anchor_round,
            voters,
        });
    }
}

pub struct Consensus {
    /// The committee information.
    committee: Committee,
    /// The depth of the garbage collector.
    gc_depth: Round,

    /// Receives new certificates from the primary. The primary should send us new certificates only
    /// if it already sent us its whole history.
    rx_primary: Receiver<Certificate>,
    /// Outputs the sequence of ordered certificates to the primary (for cleanup and feedback).
    tx_primary: Sender<Certificate>,
    /// Outputs the sequence of ordered certificates to the application layer.
    tx_output: Sender<Certificate>,

    /// The genesis certificates.
    genesis: Vec<Certificate>,
}

impl Consensus {
    pub fn spawn(
        committee: Committee,
        gc_depth: Round,
        rx_primary: Receiver<Certificate>,
        tx_primary: Sender<Certificate>,
        tx_output: Sender<Certificate>,
    ) {
        tokio::spawn(async move {
            Self {
                committee: committee.clone(),
                gc_depth,
                rx_primary,
                tx_primary,
                tx_output,
                genesis: Certificate::genesis(&committee),
            }
            .run()
            .await;
        });
    }

    async fn run(&mut self) {
        // The consensus state (everything else is immutable).
        let mut state = State::new(self.genesis.clone());

        // Listen to incoming certificates.
        while let Some(certificate) = self.rx_primary.recv().await {
            debug!("Processing {:?}", certificate);
            let round = certificate.round();

            // Add the new certificate to the local storage.
            state
                .dag
                .entry(round)
                .or_insert_with(HashMap::new)
                .insert(certificate.origin(), (certificate.digest(), certificate));

            // Try to order the dag to commit. Start from the highest round for which we have at least
            // 2f+1 certificates. This is because we need them to reveal the common coin.
            let r = round - 1;

            // We only elect leaders for even round numbers.
            if r % 2 != 0 || r < 4 {
                continue;
            }

            // Get the certificate's digest of the leaders of round r-2. If we already ordered this leader,
            // there is nothing to do.
            let leader_round = r - 2;
            let initial_last_committed_round = state.last_committed_round;
            if leader_round <= initial_last_committed_round {
                continue;
            }
            let leaders = self.leader_candidates(leader_round, &state.dag, &state);
            if leaders.is_empty() {
                continue;
            }

            let mut sequence = Vec::new();
            let mut anchors = Vec::new();
            let commit_round = r;
            for (leader_digest, leader) in leaders {
                // Check if the leader has f+1 support from its children (ie. round r-1).
                let stake: Stake = state
                    .dag
                    .get(&(r - 1))
                    .expect("We should have the whole history by now")
                    .values()
                    .filter(|(_, x)| x.header.parents.contains(&leader_digest))
                    .map(|(_, x)| self.committee.stake(&x.origin()))
                    .sum();

                // If it is the case, we can commit the leader. But first, we need to recursively go back to
                // the last committed leader, and commit all preceding leaders in the right order. Committing
                // a leader block means committing all its dependencies.
                if stake < self.committee.validity_threshold() {
                    debug!("Leader {:?} does not have enough support", leader);
                    break;
                }

                // Get an ordered list of past leaders that are linked to the current leader.
                debug!("Leader {:?} has enough support", leader);
                for leader in self.order_leaders(&leader, &state).iter().rev() {
                    // Starting from the oldest leader, flatten the sub-dag referenced by the leader.
                    for x in self.order_dag(leader, &state) {
                        // Update and clean up internal state.
                        state.update(&x, self.gc_depth);
                        state.track_commit(&x, commit_round);

                        // Add the certificate to the sequence.
                        sequence.push(x);
                    }
                    anchors.push(leader.clone());
                }
            }

            for anchor in anchors {
                state.record_anchor(&anchor);
                self.update_reputations(&mut state);
            }

            // Log the latest committed round of every authority (for debug).
            if log_enabled!(log::Level::Debug) {
                for (name, round) in &state.last_committed {
                    debug!("Latest commit of {}: Round {}", name, round);
                }
            }

            // Output the sequence in the right order.
            for certificate in sequence {
                #[cfg(not(feature = "benchmark"))]
                info!("Committed {}", certificate.header);

                #[cfg(feature = "benchmark")]
                for digest in certificate.header.payload.keys() {
                    // NOTE: This log entry is used to compute performance.
                    info!("Committed {} -> {:?}", certificate.header, digest);
                }

                self.tx_primary
                    .send(certificate.clone())
                    .await
                    .expect("Failed to send certificate to primary");

                if let Err(e) = self.tx_output.send(certificate).await {
                    warn!("Failed to output certificate: {}", e);
                }
            }
        }
    }

    /// Returns the certificate (and the certificate's digest) originated by the leader of the
    /// specified round (if any).
    fn leader_candidates<'a>(
        &self,
        round: Round,
        dag: &'a Dag,
        state: &State,
    ) -> Vec<(Digest, Certificate)> {
        // Elect the leaders based on the highest reputation scores.
        let mut keys: Vec<_> = self.committee.authorities.keys().cloned().collect();
        keys.sort();
        let mut scored: Vec<_> = keys
            .into_iter()
            .map(|key| {
                let score = state
                    .reputations
                    .get(&key)
                    .copied()
                    .unwrap_or_else(|| self.reputation_score(state, &key));
                (key, score)
            })
            .collect();
        scored.sort_by(|(left_key, left_score), (right_key, right_score)| {
            right_score
                .partial_cmp(left_score)
                .unwrap_or(Ordering::Equal)
                .then_with(|| left_key.cmp(right_key))
        });
        let leaders_to_try = self
            .committee
            .size()
            .saturating_sub(self.committee.size().saturating_sub(1) / 3);

        let mut leaders = Vec::new();
        if let Some(entries) = dag.get(&round) {
            for (key, _) in scored.into_iter().take(leaders_to_try) {
                if let Some((digest, certificate)) = entries.get(&key) {
                    leaders.push((digest.clone(), certificate.clone()));
                }
            }
        }
        leaders
    }

    /// Order the past leaders that we didn't already commit.
    fn order_leaders(&self, leader: &Certificate, state: &State) -> Vec<Certificate> {
        let mut to_commit = vec![leader.clone()];
        let mut leader = leader;
        for r in (state.last_committed_round + 2..leader.round())
            .rev()
            .step_by(2)
        {
            // Get the certificate proposed by the previous leader.
            let candidates = self.leader_candidates(r, &state.dag, state);
            let prev_leader = match candidates.first() {
                Some((_, leader)) => leader,
                None => continue,
            };

            // Check whether there is a path between the last two leaders.
            if self.linked(leader, prev_leader, &state.dag) {
                to_commit.push(prev_leader.clone());
                leader = prev_leader;
            }
        }
        to_commit
    }

    /// Checks if there is a path between two leaders.
    fn linked(&self, leader: &Certificate, prev_leader: &Certificate, dag: &Dag) -> bool {
        let mut parents = vec![leader];
        for r in (prev_leader.round()..leader.round()).rev() {
            parents = dag
                .get(&(r))
                .expect("We should have the whole history by now")
                .values()
                .filter(|(digest, _)| parents.iter().any(|x| x.header.parents.contains(digest)))
                .map(|(_, certificate)| certificate)
                .collect();
        }
        parents.contains(&prev_leader)
    }

    /// Flatten the dag referenced by the input certificate. This is a classic depth-first search (pre-order):
    /// https://en.wikipedia.org/wiki/Tree_traversal#Pre-order
    fn order_dag(&self, leader: &Certificate, state: &State) -> Vec<Certificate> {
        debug!("Processing sub-dag of {:?}", leader);
        let mut ordered = Vec::new();
        let mut already_ordered = HashSet::new();

        let mut buffer = vec![leader];
        while let Some(x) = buffer.pop() {
            debug!("Sequencing {:?}", x);
            ordered.push(x.clone());
            for parent in &x.header.parents {
                let (digest, certificate) = match state
                    .dag
                    .get(&(x.round() - 1))
                    .map(|x| x.values().find(|(x, _)| x == parent))
                    .flatten()
                {
                    Some(x) => x,
                    None => continue, // We already ordered or GC up to here.
                };

                // We skip the certificate if we (1) already processed it or (2) we reached a round that we already
                // committed for this authority.
                let mut skip = already_ordered.contains(&digest);
                skip |= state
                    .last_committed
                    .get(&certificate.origin())
                    .map_or_else(|| false, |r| r == &certificate.round());
                if !skip {
                    buffer.push(certificate);
                    already_ordered.insert(digest);
                }
            }
        }

        // Ensure we do not commit garbage collected certificates.
        ordered.retain(|x| x.round() + self.gc_depth >= state.last_committed_round);

        // Ordering the output by round is not really necessary but it makes the commit sequence prettier.
        ordered.sort_by_key(|x| x.round());
        ordered
    }

    fn update_reputations(&self, state: &mut State) {
        for authority in self.committee.authorities.keys() {
            let score = self.reputation_score(state, authority);
            state.reputations.insert(*authority, score);
        }
    }

    fn reputation_score(&self, state: &State, authority: &PublicKey) -> f64 {
        let activity_rounds = state.activity_rounds.get(authority);
        let unique_rounds: HashSet<Round> = activity_rounds
            .map(|rounds| rounds.iter().copied().collect())
            .unwrap_or_default();
        let activity = unique_rounds.len() as f64 / 50.0;

        let timely = match state.delay_history.get(authority) {
            Some(delays) if !delays.is_empty() => {
                let mut values: Vec<_> = delays.iter().copied().collect();
                values.sort_unstable();
                let mid = values.len() / 2;
                let median = if values.len() % 2 == 0 {
                    (values[mid - 1] + values[mid]) as f64 / 2.0
                } else {
                    values[mid] as f64
                };
                (-0.3 * median).exp()
            }
            _ => 0.0,
        };

        let (anchors, votes) = if state.anchor_history.is_empty() {
            (0usize, 0usize)
        } else {
            let total = state.anchor_history.len();
            let voted = state
                .anchor_history
                .iter()
                .filter(|record| record.voters.contains(authority))
                .count();
            (total, voted)
        };
        let structure = if anchors == 0 {
            0.0
        } else {
            votes as f64 / anchors as f64
        };

        0.45 * activity + 0.30 * timely + 0.25 * structure
    }
}
