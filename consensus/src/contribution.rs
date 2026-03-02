use config::Stake;
use crypto::PublicKey;
use primary::Round;
use std::collections::{HashMap, HashSet, VecDeque};

/// Keep track of recent participation (certificate production) and derive contribution weights.
// 用来记录最近参与度（产生证书），并据此派生权重
#[derive(Default)]
pub struct ContributionWindow {
    horizon: usize,                       // 窗口长度（最多看最近几轮）
    rounds: VecDeque<HashSet<PublicKey>>, // 每轮贡献者集合队列(按时间顺序)
    scores: HashMap<PublicKey, u64>,      // 每个节点在窗口内出现次数
    authored_blocks: HashMap<PublicKey, u64>,
    total_blocks: u64,
    a: f64,
    b: f64,
}

// 构造函数
impl ContributionWindow {
    pub fn new(horizon: usize) -> Self {
        Self {
            horizon: horizon.max(1),
            rounds: VecDeque::new(),
            scores: HashMap::new(),
            authored_blocks: HashMap::new(),
            total_blocks: 0,
            a: 0.4,
            b: 5.0,
        }
    }

    /// Record one newly observed block/certificate authored by `author`.
    pub fn record_block(&mut self, author: PublicKey) {
        *self.authored_blocks.entry(author).or_insert(0) += 1;
        self.total_blocks += 1;
    }
    /// Record all authorities that contributed certificates for a round.
    /// 记录一轮的贡献
    pub fn record_round(&mut self, contributors: impl IntoIterator<Item = PublicKey>) {
        // 转成HashSet去重，防止同一轮一个节点重复计分
        let contributors: HashSet<_> = contributors.into_iter().collect();
        // 遍历本轮贡献者
        for contributor in &contributors {
            *self.scores.entry(*contributor).or_insert(0) += 1;
        }
        // 把本轮集合压入窗口尾部
        self.rounds.push_back(contributors);
        // 如果窗口唱过horizon，开始淘汰最旧轮次
        while self.rounds.len() > self.horizon {
            // 从队首弹出过期轮次贡献者集合
            if let Some(expired) = self.rounds.pop_front() {
                for contributor in expired {
                    if let Some(score) = self.scores.get_mut(&contributor) {
                        *score = score.saturating_sub(1);
                        if *score == 0 {
                            self.scores.remove(&contributor);
                        }
                    }
                }
            }
        }
    }
    /// Contribution(i) = f(p_i) = 1 / (1 + e^(-a * (p_i - b))).
    ///
    /// p_i is the cumulative block production proportion in percentage points [0, 100].
    pub fn contribution(&self, authority: &PublicKey) -> f64 {
        if self.total_blocks == 0 {
            return 0.0;
        }

        let authored = self
            .authored_blocks
            .get(authority)
            .copied()
            .unwrap_or_default();
        let p_i = (authored as f64 / self.total_blocks as f64) * 100.0;
        1.0 / (1.0 + (-self.a * (p_i - self.b)).exp())
    }

    /// Convert contribution score to stake multiplier in [1, 2).
    pub fn weighted_stake(&self, authority: &PublicKey, base_stake: Stake) -> Stake {
        let multiplier = 1.0 + self.contribution(authority);
        (base_stake as f64 * multiplier).round() as Stake
    }

    pub fn should_use_contribution_weight(round: Round) -> bool {
        round >= 4
    }
}

#[cfg(test)]
mod tests {
    use super::ContributionWindow;
    use crypto::generate_keypair;
    use rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn window_updates_scores() {
        let mut rng = StdRng::from_seed([7; 32]);
        let (a, _) = generate_keypair(&mut rng);
        let (b, _) = generate_keypair(&mut rng);

        let mut window = ContributionWindow::new(2);
        window.record_round([a]);
        assert_eq!(window.weighted_stake(&a, 1), 2);
        assert_eq!(window.weighted_stake(&b, 1), 1);

        window.record_round([a, b]);
        assert_eq!(window.weighted_stake(&a, 1), 2);
        assert_eq!(window.weighted_stake(&b, 1), 2);

        window.record_round([b]);
        assert_eq!(window.weighted_stake(&a, 1), 2);
        assert_eq!(window.weighted_stake(&b, 1), 2);
    }
}
