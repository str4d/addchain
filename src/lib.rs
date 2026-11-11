//! *Library for generating addition chains*
//!
//! An addition chain `C` for some positive integer `n` is a sequence of integers that
//! have the following properties:
//!
//! - The first integer is 1.
//! - The last integer is `n`.
//! - Integers only appear once.
//! - Every integer is either the sum of two earlier integers, or double an earlier
//!   integer.
//!
//! An addition chain corresponds to a series of `len(C) - 1` primitive operations
//! (doubling and addition) that can be used to compute a target integer. An *optimal*
//! addition chain for `n` has the shortest possible length, and therefore requires the
//! fewest operations to compute `n`. This is particularly useful in cryptographic
//! algorithms such as modular exponentiation, where `n` is usually at least `2^128`.
//!
//! # Example
//!
//! To compute the number 87, we can represent it in binary as `1010111`, and then using
//! the binary double-and-add algorithm (where we double for every bit, and add 1 for
//! every bit that is set to 1) we have the following steps:
//! ```text
//!  i | n_i | Operation | b_i
//! ---|-----|-----------|-----
//!  0 |  1  |           |  1
//!  1 |  2  | n_0 * 2   |  0
//!  2 |  4  | n_1 * 2   |  1
//!  3 |  5  | n_2 + n_0 |
//!  4 | 10  | n_3 * 2   |  0
//!  5 | 20  | n_4 * 2   |  1
//!  6 | 21  | n_5 + n_0 |
//!  7 | 42  | n_6 * 2   |  1
//!  8 | 43  | n_7 + n_0 |
//!  9 | 86  | n_8 * 2   |  1
//! 10 | 87  | n_9 + n_0 |
//! ```
//!
//! This corresponds to the addition chain `[1, 2, 4, 5, 10, 20, 21, 42, 43, 86, 87]`,
//! which has length 11. However, the optimal addition chain length for 87 is 10, and
//! several addition chains can be constructed with optimal length. One such chain is
//! `[1, 2, 3, 6, 7, 10, 20, 40, 80, 87]`, which corresponds to the following steps:
//! ```text
//!  i | n_i | Operation
//! ---|-----|----------
//!  0 |  1  |
//!  1 |  2  | n_0 * 2
//!  2 |  3  | n_1 + n_0
//!  3 |  6  | n_2 * 2
//!  4 |  7  | n_3 + n_0
//!  5 | 10  | n_4 + n_2
//!  6 | 20  | n_5 * 2
//!  7 | 40  | n_6 * 2
//!  8 | 80  | n_7 * 2
//!  9 | 87  | n_8 + n_4
//! ```
//!
//! # Usage
//!
//! ```
//! use addchain::{build_addition_chain, Step};
//! use num_bigint::BigUint;
//!
//! assert_eq!(
//!     build_addition_chain(BigUint::from(87u32)),
//!     vec![
//!         Step::Double { index: 0 },
//!         Step::Add { left: 1, right: 0 },
//!         Step::Double { index: 2 },
//!         Step::Add { left: 3, right: 0 },
//!         Step::Add { left: 4, right: 2 },
//!         Step::Double { index: 5 },
//!         Step::Double { index: 6 },
//!         Step::Double { index: 7 },
//!         Step::Add { left: 8, right: 4 },
//!     ],
//! );
//! ```

use num_bigint::BigUint;
use num_traits::One;

mod bbbd;
mod bos_coster;
mod cwm_asa;
mod ky_hybrid;

/// The error kinds returned by `addchain` APIs.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// The provided chain is invalid.
    InvalidChain,
}

/// Returns the shortest addition chain we can find for the given number, using all
/// available algorithms.
#[allow(clippy::needless_pass_by_value)]
pub fn find_shortest_chain(n: BigUint) -> Vec<BigUint> {
    find_chain(&n, CostModel::Same)
}

/// Returns the lowest-cost addition chain we can find using all available algorithms.
///
/// Equal-cost ties prefer BBBD.
fn find_chain(n: &BigUint, cost_model: CostModel) -> Vec<BigUint> {
    let mut best = prune_chain(bbbd::find_shortest_chain(n.clone()));
    let algorithms: &[fn(&BigUint, CostModel) -> Vec<BigUint>] = &[
        bos_coster::find_chain,
        cwm_asa::find_chain,
        ky_hybrid::find_chain,
    ];
    for algorithm in algorithms {
        let candidate = prune_chain(algorithm(n, cost_model));
        if cost_model.cost(&candidate) < cost_model.cost(&best) {
            best = candidate;
        }
    }
    best
}

/// Retains only values needed by the target's selected operand dependencies.
fn prune_chain(chain: Vec<BigUint>) -> Vec<BigUint> {
    debug_assert!(chain.windows(2).all(|pair| pair[0] < pair[1]));
    let mut needed = vec![false; chain.len()];
    needed[chain.len() - 1] = true;
    for i in (1..chain.len()).rev() {
        if needed[i] {
            let (left, right) =
                increasing_pair(&chain[..i], &chain[i]).expect("generated chain is valid");
            needed[left] = true;
            needed[right] = true;
        }
    }
    chain
        .into_iter()
        .zip(needed)
        .filter_map(|(value, needed)| if needed { Some(value) } else { None })
        .collect()
}

/// Finds the pair with the smallest larger index in a strictly increasing prefix.
fn increasing_pair(prefix: &[BigUint], target: &BigUint) -> Option<(usize, usize)> {
    // The larger operand must be at least half the target.
    let mut low = 0;
    let mut high = prefix.len();
    while low < high {
        let middle = low + (high - low) / 2;
        if &prefix[middle] + &prefix[middle] < *target {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    if low == prefix.len() {
        return None;
    }
    let (mut larger, mut smaller) = (low, low);
    while larger < prefix.len() {
        let sum = &prefix[larger] + &prefix[smaller];
        match sum.cmp(target) {
            std::cmp::Ordering::Equal => return Some((larger, smaller)),
            std::cmp::Ordering::Less => larger += 1,
            std::cmp::Ordering::Greater => {
                if smaller == 0 {
                    return None;
                }
                smaller -= 1;
            }
        }
    }
    None
}

/// The relative cost of doubling and addition when selecting a chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CostModel {
    /// Doubling and addition have the same cost, so fewer steps is better.
    Same,
}

impl CostModel {
    /// Scores a valid, nonempty addition chain.
    ///
    /// Smaller costs are better.
    fn cost(self, chain: &[BigUint]) -> usize {
        match self {
            CostModel::Same => chain.len() - 1,
        }
    }
}

/// A single step in computing an addition chain.
#[derive(Debug, PartialEq)]
pub enum Step {
    Double { index: usize },
    Add { left: usize, right: usize },
}

/// Converts an addition chain into a series of steps.
#[allow(clippy::needless_pass_by_value)]
pub fn build_steps(chain: Vec<BigUint>) -> Result<Vec<Step>, Error> {
    match chain.first() {
        Some(n) if n.is_one() => (),
        _ => return Err(Error::InvalidChain),
    }

    let increasing = chain.windows(2).all(|pair| pair[0] < pair[1]);
    let mut steps = Vec::with_capacity(chain.len() - 1);

    for (i, val) in chain.iter().enumerate().skip(1) {
        let mut pair = None;
        if increasing {
            pair = increasing_pair(&chain[..i], val);
        } else {
            // Find the pair of previous values that add to this one
            'search: for (j, left) in chain[..i].iter().enumerate() {
                for (k, right) in chain[..=j].iter().enumerate() {
                    if val == &(left + right) {
                        // Found the pair!
                        pair = Some((j, k));
                        break 'search;
                    }
                }
            }
        }

        // We must always find a matching pair
        steps.push(match pair {
            Some((j, k)) if j == k => Step::Double { index: j },
            Some((j, k)) => Step::Add { left: j, right: k },
            None => return Err(Error::InvalidChain),
        });
    }

    Ok(steps)
}

/// Generates a series of steps that will compute an addition chain for the given number.
/// The addition chain is the shortest we can find using all available algorithms.
pub fn build_addition_chain(n: BigUint) -> Vec<Step> {
    build_steps(find_shortest_chain(n)).expect("chain is valid")
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::{build_steps, Error, Step};

    #[test]
    fn equal_cost_model() {
        use super::{find_chain, find_shortest_chain, CostModel};

        assert_eq!(CostModel::Same.cost(&[BigUint::from(1u32)]), 0);
        assert_eq!(
            CostModel::Same.cost(&[BigUint::from(1u32), BigUint::from(2u32)]),
            1
        );
        for value in &[1u32, 2, 87, 255, 384] {
            let n = BigUint::from(*value);
            let bbbd = super::prune_chain(crate::bbbd::find_shortest_chain(n.clone()));
            let cwm = super::prune_chain(crate::cwm_asa::find_chain(&n, CostModel::Same));
            let mut expected = if cwm.len() < bbbd.len() { cwm } else { bbbd };
            let algorithms: &[fn(&BigUint, CostModel) -> Vec<BigUint>] =
                &[crate::bos_coster::find_chain, crate::ky_hybrid::find_chain];
            for algorithm in algorithms {
                let candidate = super::prune_chain(algorithm(&n, CostModel::Same));
                if candidate.len() < expected.len() {
                    expected = candidate;
                }
            }
            assert_eq!(find_chain(&n, CostModel::Same), expected);
            assert_eq!(find_shortest_chain(n), expected);
        }
    }

    #[test]
    fn steps_from_valid_chains() {
        assert_eq!(
            build_steps(vec![
                BigUint::from(1u32),
                BigUint::from(2u32),
                BigUint::from(3u32),
            ]),
            Ok(vec![
                Step::Double { index: 0 },
                Step::Add { left: 1, right: 0 }
            ]),
        );

        assert_eq!(
            build_steps(vec![
                BigUint::from(1u32),
                BigUint::from(2u32),
                BigUint::from(4u32),
                BigUint::from(8u32),
            ]),
            Ok(vec![
                Step::Double { index: 0 },
                Step::Double { index: 1 },
                Step::Double { index: 2 },
            ]),
        );

        assert_eq!(
            build_steps(vec![
                BigUint::from(1u32),
                BigUint::from(2u32),
                BigUint::from(3u32),
                BigUint::from(6u32),
                BigUint::from(7u32),
                BigUint::from(10u32),
                BigUint::from(20u32),
                BigUint::from(40u32),
                BigUint::from(80u32),
                BigUint::from(87u32),
            ]),
            Ok(vec![
                Step::Double { index: 0 },
                Step::Add { left: 1, right: 0 },
                Step::Double { index: 2 },
                Step::Add { left: 3, right: 0 },
                Step::Add { left: 4, right: 2 },
                Step::Double { index: 5 },
                Step::Double { index: 6 },
                Step::Double { index: 7 },
                Step::Add { left: 8, right: 4 },
            ]),
        );
    }

    fn reference_steps(chain: &[BigUint]) -> Result<Vec<Step>, Error> {
        if chain.first() != Some(&BigUint::from(1u32)) {
            return Err(Error::InvalidChain);
        }
        let mut steps = Vec::new();
        for i in 1..chain.len() {
            let mut found = None;
            'search: for j in 0..i {
                for k in 0..=j {
                    if &chain[j] + &chain[k] == chain[i] {
                        found = Some(if j == k {
                            Step::Double { index: j }
                        } else {
                            Step::Add { left: j, right: k }
                        });
                        break 'search;
                    }
                }
            }
            steps.push(found.ok_or(Error::InvalidChain)?);
        }
        Ok(steps)
    }

    #[test]
    fn conversion_matches_original_search() {
        // Includes valid and invalid sorted sequences and ambiguous sums.
        for mask in 0..(1u32 << 12) {
            let mut chain = vec![BigUint::from(1u32)];
            for bit in 0..12 {
                if mask & (1 << bit) != 0 {
                    chain.push(BigUint::from(bit + 2u32));
                }
            }
            assert_eq!(build_steps(chain.clone()), reference_steps(&chain));
        }
        for values in &[
            vec![],
            vec![1u32],
            vec![1, 2, 4, 3, 6],
            vec![1, 2, 2, 4],
            vec![1, 0, 2],
            vec![1, 2, 4, 3, 9],
        ] {
            let chain: Vec<_> = values.iter().map(|v| BigUint::from(*v)).collect();
            assert_eq!(build_steps(chain.clone()), reference_steps(&chain));
        }
        for n in 1..=1024u32 {
            let chain = super::find_shortest_chain(BigUint::from(n));
            assert_eq!(build_steps(chain.clone()), reference_steps(&chain));
        }
    }

    #[test]
    fn supplied_exponent() {
        let n = BigUint::parse_bytes(
            b"39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff",
            16,
        )
        .unwrap();
        let chain = super::find_shortest_chain(n.clone());
        assert_eq!(chain.last(), Some(&n));
        assert!(chain.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(chain.len() - 1 <= 263);
        assert!(build_steps(chain).is_ok());
    }

    #[test]
    fn increasing_pair_matches_nested_search() {
        for mask in 0..(1u32 << 10) {
            let prefix: Vec<_> = (0..10u32)
                .filter(|bit| mask & (1u32 << bit) != 0)
                .map(|v| BigUint::from(v + 1))
                .collect();
            for target in 0..=21u32 {
                let target = BigUint::from(target);
                let mut expected = None;
                'search: for j in 0..prefix.len() {
                    for k in 0..=j {
                        if &prefix[j] + &prefix[k] == target {
                            expected = Some((j, k));
                            break 'search;
                        }
                    }
                }
                assert_eq!(super::increasing_pair(&prefix, &target), expected);
            }
        }
    }

    #[test]
    fn pruning_removes_unused_dependencies() {
        let chain = [1u32, 2, 3, 4, 6, 8, 12]
            .iter()
            .map(|v| BigUint::from(*v))
            .collect();
        let expected: Vec<_> = [1u32, 2, 3, 6, 12]
            .iter()
            .map(|v| BigUint::from(*v))
            .collect();
        let pruned = super::prune_chain(chain);
        assert_eq!(pruned, expected);
        assert_eq!(super::prune_chain(pruned.clone()), pruned);
        assert!(build_steps(pruned).is_ok());
        assert_eq!(
            super::prune_chain(vec![BigUint::from(1u32)]),
            vec![BigUint::from(1u32)]
        );
    }

    #[test]
    fn pruning_supplied_exponent() {
        use super::CostModel;
        let n = BigUint::parse_bytes(
            b"39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff",
            16,
        )
        .unwrap();
        let candidates = vec![
            ("BBBD", crate::bbbd::find_shortest_chain(n.clone())),
            (
                "Bos–Coster",
                crate::bos_coster::find_chain(&n, CostModel::Same),
            ),
            ("CWM-ASA", crate::cwm_asa::find_chain(&n, CostModel::Same)),
            (
                "KY Hybrid",
                crate::ky_hybrid::find_chain(&n, CostModel::Same),
            ),
        ];
        for (name, chain) in candidates {
            let original = chain.len();
            let pruned = super::prune_chain(chain);
            println!(
                "{}: {} -> {} operations",
                name,
                original - 1,
                pruned.len() - 1
            );
            assert!(pruned.len() <= original);
            assert_eq!(pruned.last(), Some(&n));
            assert!(pruned.windows(2).all(|w| w[0] < w[1]));
            assert!(build_steps(pruned.clone()).is_ok());
            assert_eq!(super::prune_chain(pruned.clone()), pruned);
        }
    }

    #[test]
    fn invalid_chains() {
        // First element is not one.
        assert_eq!(
            build_steps(vec![BigUint::from(2u32), BigUint::from(3u32),]),
            Err(Error::InvalidChain),
        );

        // Missing an element of a pair.
        assert_eq!(
            build_steps(vec![
                BigUint::from(1u32),
                BigUint::from(4u32),
                BigUint::from(8u32),
            ]),
            Err(Error::InvalidChain),
        );
    }
}
