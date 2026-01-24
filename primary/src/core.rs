// Copyright(C) Facebook, Inc. and its affiliates.
use crate::aggregators::{CertificatesAggregator, VotesAggregator};
use crate::error::{DagError, DagResult};
use crate::messages::{Certificate, Header, Vote};
use crate::primary::{PrimaryMessage, Round};
use crate::synchronizer::Synchronizer;
use async_recursion::async_recursion;
use bytes::Bytes;
use config::Committee;
use crypto::Hash as _;
use crypto::{Digest, PublicKey, SignatureService};
use log::{debug, error, warn};
use network::{CancelHandler, ReliableSender};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use store::Store;
use tokio::sync::mpsc::{Receiver, Sender};

#[cfg(test)]
#[path = "tests/core_tests.rs"]
pub mod core_tests;

pub struct Core {
    /// The public key of this primary.
    name: PublicKey,
    /// The committee information.
    committee: Committee,
    /// The persistent storage.
    store: Store,
    /// Handles synchronization with other nodes and our workers.
    synchronizer: Synchronizer,
    /// Service to sign headers.
    signature_service: SignatureService,
    /// The current consensus round (used for cleanup).
    consensus_round: Arc<AtomicU64>,
    /// The depth of the garbage collector.
    gc_depth: Round,

    /// Receiver for dag messages (headers, votes, certificates).
    /// 网络来的 primary-to-primary 消息（Header/Vote/Certificate）
    rx_primaries: Receiver<PrimaryMessage>,
    /// Receives loopback headers from the `HeaderWaiter`.
    /// 之前因为“缺父/缺payload”暂停的 header，依赖补齐后回投
    rx_header_waiter: Receiver<Header>,
    /// Receives loopback certificates from the `CertificateWaiter`.
    /// 之前因为“缺祖先”暂停的 certificate，补齐后回投
    rx_certificate_waiter: Receiver<Certificate>,
    /// Receives our newly created headers from the `Proposer`.
    /// Proposer 产生的新 header（本节点准备提案）
    rx_proposer: Receiver<Header>,
    /// Output all certificates to the consensus layer.
    /// 把已验证/已处理的 certificate 发给共识层（例如 Narwhal 的 DAG 输入）
    tx_consensus: Sender<Certificate>,
    /// Send valid a quorum of certificates' ids to the `Proposer` (along with their round).
    /// 当某轮收齐足够证书（quorum）后，把 parents 列表发给 proposer 生成下一轮 header
    tx_proposer: Sender<(Vec<Digest>, Round)>,

    /// The last garbage collected round.
    /// 内存 GC 清理到的最老轮次（防止处理太旧消息）
    gc_round: Round,
    /// The authors of the last voted headers.
    /// 记录本轮对哪些作者的 header 投过票，避免一轮对同作者投多次
    last_voted: HashMap<Round, HashSet<PublicKey>>,
    /// The set of headers we are currently processing.
    /// 正在处理的 header（防止重复处理、避免循环）
    processing: HashMap<Round, HashSet<Digest>>,
    /// Tracks votes and related headers for local certificate assembly.
    /// 按 header 本地聚合 votes，达到阈值就产出 certificate
    votes_aggregators: HashMap<Digest, VoteState>,
    /// Votes that arrived before their header is available locally.
    /// header 未到时的暂存 vote
    pending_votes: HashMap<Digest, Vec<Vote>>,
    /// Aggregates certificates to use as parents for new headers.
    /// 收集同轮 certificate，凑到 quorum 就把 digest 列表发给 proposer 当 parents
    certificates_aggregators: HashMap<Round, Box<CertificatesAggregator>>,
    /// A network sender to send the batches to the other workers.
    /// 可靠广播/点对点发送
    network: ReliableSender,
    /// Keeps the cancel handlers of the messages we sent.
    /// 记录每轮发送的消息的取消句柄（便于 GC 时停止重试/重发）
    cancel_handlers: HashMap<Round, Vec<CancelHandler>>,
}

struct VoteState {
    header: Header,
    aggregator: VotesAggregator,
}

impl Core {
    #[allow(clippy::too_many_arguments)]
    pub fn spawn(
        name: PublicKey,
        committee: Committee,
        store: Store,
        synchronizer: Synchronizer,
        signature_service: SignatureService,
        consensus_round: Arc<AtomicU64>,
        gc_depth: Round,
        rx_primaries: Receiver<PrimaryMessage>,
        rx_header_waiter: Receiver<Header>,
        rx_certificate_waiter: Receiver<Certificate>,
        rx_proposer: Receiver<Header>,
        tx_consensus: Sender<Certificate>,
        tx_proposer: Sender<(Vec<Digest>, Round)>,
    ) {
        tokio::spawn(async move {
            Self {
                name,
                committee,
                store,
                synchronizer,
                signature_service,
                consensus_round,
                gc_depth,
                rx_primaries,
                rx_header_waiter,
                rx_certificate_waiter,
                rx_proposer,
                tx_consensus,
                tx_proposer,
                gc_round: 0,
                last_voted: HashMap::with_capacity(2 * gc_depth as usize),
                processing: HashMap::with_capacity(2 * gc_depth as usize),
                votes_aggregators: HashMap::with_capacity(2 * gc_depth as usize),
                pending_votes: HashMap::with_capacity(2 * gc_depth as usize),
                certificates_aggregators: HashMap::with_capacity(2 * gc_depth as usize),
                network: ReliableSender::new(),
                cancel_handlers: HashMap::with_capacity(2 * gc_depth as usize),
            }
                .run()
                .await;
        });
    }

    /// 处理自己刚提议的 header
    async fn process_own_header(&mut self, header: Header) -> DagResult<()> {
        // Broadcast the new header in a reliable manner.
        // 找到其他所有 primary 的 primary_to_primary 地址列表（排除自己）
        let addresses = self
            .committee
            .others_primaries(&self.name)
            .iter()
            .map(|(_, x)| x.primary_to_primary)
            .collect();
        // 封装header
        let bytes = bincode::serialize(&PrimaryMessage::Header(header.clone()))
            .expect("Failed to serialize our own header");
        // 广播header
        let handlers = self.network.broadcast(addresses, Bytes::from(bytes)).await;
        // 记录返回的cancel_handlers
        self.cancel_handlers
            .entry(header.round)
            .or_insert_with(Vec::new)
            .extend(handlers);

        // Process the header.
        // 本地处理header
        self.process_header(&header).await
    }

    /// 验证依赖、持久化header、投票
    #[async_recursion]
    async fn process_header(&mut self, header: &Header) -> DagResult<()> {
        debug!("Processing {:?}", header);
        // Indicate that we are processing this header.
        // 在 processing 里标记：这个 header 正在处理，避免重复/循环
        self.processing
            .entry(header.round)
            .or_insert_with(HashSet::new)
            .insert(header.id.clone());

        // Ensure we have the parents. If at least one parent is missing, the synchronizer returns an empty
        // vector; it will gather the missing parents (as well as all ancestors) from other nodes and then
        // reschedule processing of this header.
        // 确保父证书齐全（缺就同步并暂停）
        let parents = self.synchronizer.get_parents(header).await?;
        if parents.is_empty() {
            debug!("Processing of {} suspended: missing parent(s)", header.id);
            // 如果为空返回Ok相当于暂停
            return Ok(());
        }

        // Check the parent certificates. Ensure the parents form a quorum and are all from the previous round.
        // 验证父证书必须来自上一轮
        let mut stake = 0;
        // 验证该header上一轮的parents加起来是否满足阈值，足够支撑他成为DAG顶点
        for x in parents {
            ensure!(
                x.round() + 1 == header.round,
                DagError::MalformedHeader(header.id.clone())
            );
            stake += self.committee.stake(&x.origin());
        }
        //
        ensure!(
            stake >= self.committee.quorum_threshold(),
            DagError::HeaderRequiresQuorum(header.id.clone())
        );

        // Ensure we have the payload. If we don't, the synchronizer will ask our workers to get it, and then
        // reschedule processing of this header once we have it.
        // 确保payload在本地，不在就让worker去拉并暂停
        if self.synchronizer.missing_payload(header).await? {
            debug!("Processing of {} suspended: missing payload", header);
            return Ok(());
        }

        // Store the header.
        // 持久化header
        let bytes = bincode::serialize(header).expect("Failed to serialize header");
        self.store.write(header.id.to_vec(), bytes).await;

        // Process any pending votes for this header.
        if let Some(votes) = self.pending_votes.remove(&header.id) {
            for vote in votes {
                self.process_vote_with_header(vote, header).await?;
            }
        }

        // Check if we can vote for this header.
        // 生成vote，每轮对一个author只投一次
        if self
            .last_voted//
            .entry(header.round)
            .or_insert_with(HashSet::new)
            .insert(header.author)
        {
            // Make a vote and broadcast it.
            // 创建投票并广播给所有节点
            let vote = Vote::new(header, &self.name, &mut self.signature_service).await;
            debug!("Created {:?}", vote);
            // 广播 vote
            let addresses = self
                .committee
                .others_primaries(&self.name)
                .iter()
                .map(|(_, x)| x.primary_to_primary)
                .collect();
            let bytes = bincode::serialize(&PrimaryMessage::Vote(vote.clone()))
                .expect("Failed to serialize our own vote");
            let handlers = self.network.broadcast(addresses, Bytes::from(bytes)).await;
            self.cancel_handlers
                .entry(header.round)
                .or_insert_with(Vec::new)
                .extend(handlers);

            // 本地也处理 vote 以进行证书聚合
            self.process_vote(vote)
                .await
                .expect("Failed to process our own vote");
        }
        Ok(())
    }

    /// 聚合 votes，够阈值就组装证书
    #[async_recursion]
    async fn process_vote(&mut self, vote: Vote) -> DagResult<()> {
        debug!("Processing {:?}", vote);

        // Try to find the header locally; if unavailable, stash the vote for later.
        if let Some(state) = self.votes_aggregators.get(&vote.id) {
            let header = state.header.clone();
            return self.process_vote_with_header(vote, &header).await;
        }

        if let Some(bytes) = self.store.read(vote.id.to_vec()).await? {
            let header: Header =
                bincode::deserialize(&bytes).expect("Failed to deserialize stored header");
            return self.process_vote_with_header(vote, &header).await;
        }

        self.pending_votes
            .entry(vote.id.clone())
            .or_insert_with(Vec::new)
            .push(vote);
        Ok(())
    }

    async fn process_vote_with_header(&mut self, vote: Vote, header: &Header) -> DagResult<()> {
        ensure!(
            vote.id == header.id && vote.origin == header.author && vote.round == header.round,
            DagError::UnexpectedVote(vote.id.clone())
        );

        let state = self.votes_aggregators.entry(header.id.clone()).or_insert_with(|| {
            VoteState {
                header: header.clone(),
                aggregator: VotesAggregator::new(),
            }
        });

        if let Some(certificate) = state.aggregator.append(vote, &self.committee, &state.header)? {
            debug!("Assembled {:?}", certificate);
            self.votes_aggregators.remove(&certificate.header.id);
            self.pending_votes.remove(&certificate.header.id);

            // Process the new certificate locally (no broadcast).
            self.process_certificate(certificate)
                .await
                .expect("Failed to process valid certificate");
        }
        Ok(())
    }

    /// 确保证书依赖齐全、持久化证书、触发 proposer、送共识
    #[async_recursion]
    async fn process_certificate(&mut self, certificate: Certificate) -> DagResult<()> {
        debug!("Processing {:?}", certificate);

        // Process the header embedded in the certificate if we haven't already voted for it (if we already
        // voted, it means we already processed it). Since this header got certified, we are sure that all
        // the data it refers to (ie. its payload and its parents) are available. We can thus continue the
        // processing of the certificate even if we don't have them in store right now.
        // 如果这个 header 没在 processing 里，说明还没处理/投票过
        // 因为 certificate 已经存在，意味着父与 payload 理论上可获得，所以可以补处理
        if !self
            .processing
            .get(&certificate.header.round)
            .map_or_else(|| false, |x| x.contains(&certificate.header.id))
        {
            // This function may still throw an error if the storage fails.
            self.process_header(&certificate.header).await?;
        }

        // Ensure we have all the ancestors of this certificate yet. If we don't, the synchronizer will gather
        // them and trigger re-processing of this certificate.
        // 确保祖先齐全（缺就同步并暂停）
        // deliver_certificate拉取缺失的祖先并进行重试
        if !self.synchronizer.deliver_certificate(&certificate).await? {
            debug!(
                "Processing of {:?} suspended: missing ancestors",
                certificate
            );
            return Ok(());
        }

        // Store the certificate.
        // 持久化证书
        let bytes = bincode::serialize(&certificate).expect("Failed to serialize certificate");
        self.store.write(certificate.digest().to_vec(), bytes).await;

        // Check if we have enough certificates to enter a new dag round and propose a header.
        // 这一轮已经产生了足够多的DAG节点就进入下一轮
        if let Some(parents) = self
            .certificates_aggregators
            .entry(certificate.round())
            .or_insert_with(|| Box::new(CertificatesAggregator::new()))
            .append(certificate.clone(), &self.committee)?
        {
            // Send it to the `Proposer`.
            // 发给 proposer，让 proposer 基于这些 parents 构造新 header
            self.tx_proposer
                .send((parents, certificate.round()))
                .await
                .expect("Failed to send certificate");
        }

        // Send it to the consensus layer.
        // 把certificate发给共识层
        let id = certificate.header.id.clone();
        if let Err(e) = self.tx_consensus.send(certificate).await {
            warn!(
                "Failed to deliver certificate {} to the consensus: {}",
                id, e
            );
        }
        Ok(())
    }

    // 验证header签名
    fn sanitize_header(&mut self, header: &Header) -> DagResult<()> {
        ensure!(
            self.gc_round <= header.round,
            DagError::TooOld(header.id.clone(), header.round)
        );

        // Verify the header's signature.
        // 验header签名
        header.verify(&self.committee)?;

        // TODO [issue #3]: Prevent bad nodes from sending junk headers with high round numbers.

        Ok(())
    }

    // 验证投票签名
    fn sanitize_vote(&mut self, vote: &Vote) -> DagResult<()> {
        ensure!(
            self.gc_round <= vote.round,
            DagError::TooOld(vote.digest(), vote.round)
        );

        // Verify the vote.
        vote.verify(&self.committee).map_err(DagError::from)
    }

    // 验证 certificate签名
    fn sanitize_certificate(&mut self, certificate: &Certificate) -> DagResult<()> {
        ensure!(
            self.gc_round <= certificate.round(),
            DagError::TooOld(certificate.digest(), certificate.round())
        );

        // Verify the certificate (and the embedded header).
        certificate.verify(&self.committee).map_err(DagError::from)
    }

    // Main loop listening to incoming messages.
    pub async fn run(&mut self) {
        loop {
            // 循环同时监听四个消息输入源
            let result = tokio::select! {
                // We receive here messages from other primaries.
                // 来自其他primary的消息，内容包括Header/Vote/Certificate
                // 先验签再进入各自的处理逻辑
                Some(message) = self.rx_primaries.recv() => {
                    match message {
                        PrimaryMessage::Header(header) => {
                            match self.sanitize_header(&header) {
                                Ok(()) => self.process_header(&header).await,
                                error => error
                            }

                        },
                        PrimaryMessage::Vote(vote) => {
                            match self.sanitize_vote(&vote) {
                                Ok(()) => self.process_vote(vote).await,
                                error => error
                            }
                        },
                        PrimaryMessage::Certificate(certificate) => {
                            match self.sanitize_certificate(&certificate) {
                                Ok(()) =>  self.process_certificate(certificate).await,
                                error => error
                            }
                        },
                        _ => panic!("Unexpected core message")
                    }
                },

                // We receive here loopback headers from the `HeaderWaiter`. Those are headers for which we interrupted
                // execution (we were missing some of their dependencies) and we are now ready to resume processing.
                // 之前暂停的 header，依赖齐了就继续处理
                Some(header) = self.rx_header_waiter.recv() => self.process_header(&header).await,

                // We receive here loopback certificates from the `CertificateWaiter`. Those are certificates for which
                // we interrupted execution (we were missing some of their ancestors) and we are now ready to resume
                // processing.
                // 之前暂停的 certificate，祖先齐了继续处理
                Some(certificate) = self.rx_certificate_waiter.recv() => self.process_certificate(certificate).await,

                // We also receive here our new headers created by the `Proposer`.
                // proposer 生成 header（本节点提案），Core 广播并开始收 vote
                Some(header) = self.rx_proposer.recv() => self.process_own_header(header).await,
            };
            match result {
                Ok(()) => (),
                Err(DagError::StoreError(e)) => {
                    error!("{}", e);
                    panic!("Storage failure: killing node.");
                }
                Err(e @ DagError::TooOld(..)) => debug!("{}", e),
                Err(e) => warn!("{}", e),
            }

            // Cleanup internal state.
            let round = self.consensus_round.load(Ordering::Relaxed);
            if round > self.gc_depth {
                let gc_round = round - self.gc_depth;
                self.last_voted.retain(|k, _| k >= &gc_round);
                self.processing.retain(|k, _| k >= &gc_round);
                self.votes_aggregators
                    .retain(|_, state| state.header.round >= gc_round);
                self.pending_votes.retain(|_, votes| {
                    votes
                        .first()
                        .map_or(false, |vote| vote.round >= gc_round)
                });
                self.certificates_aggregators.retain(|k, _| k >= &gc_round);
                self.cancel_handlers.retain(|k, _| k >= &gc_round);
                self.gc_round = gc_round;
            }
        }
    }
}
