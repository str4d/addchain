//! Addition chains derived from Bos and Coster, "Addition chain heuristics",
//! CWI Report CS-R8945 (1989), §§4–6, pp. 3–7.
//! https://ir.cwi.nl/pub/5809/5809D.pdf
//!
//! Section 5 splits the exponent into windows, computes an addition sequence
//! containing their values, then doubles and adds the windows into place. We
//! use left-to-right odd windows and search widths 2–16; the report
//! gives properties of a better window distribution, but not its procedure.
//!
//! `choose_reduction` uses a local deterministic score in place of the paper's
//! incompletely specified weight function.
//!
//! Approximation is restricted to already-pending remainders; halving allows
//! any binary remainder, which is recursively constructed if not yet present.

use std::collections::BTreeSet;

use num_bigint::BigUint;
use num_traits::{One, Zero};

/// Find a chain for a positive target. The empty chain denotes zero, which has
/// no addition chain under the paper's definition (§2, p. 1).
pub(super) fn find_chain(n: &BigUint, cost_model: crate::CostModel) -> Vec<BigUint> {
    if n.is_zero() {
        return Vec::new();
    }
    if n.is_one() {
        return vec![BigUint::one()];
    }

    // Include a binary chain: window precomputation can otherwise outweigh
    // the long part, particularly for small or very sparse exponents.
    let mut best = window_chain(n, 1);
    let maximum = (n.bits() as usize).min(16);
    for width in 2..=maximum {
        let candidate = window_chain(n, width);
        if cost_model.cost(&candidate) < cost_model.cost(&best) {
            best = candidate;
        }
    }
    best
}

/// §5, pp. 3–5. The leading odd window initializes the accumulator;
/// subsequent windows consume their bit length in doublings and one addition.
/// Zero bits between windows consume only doublings.
fn window_chain(n: &BigUint, width: usize) -> Vec<BigUint> {
    let bits = n.bits() as usize;
    let mut chunks = Vec::new();
    let mut remaining = bits;
    while remaining > 0 {
        let top = n >> (remaining - 1);
        if (&top & BigUint::one()).is_zero() {
            chunks.push((1, BigUint::zero()));
            remaining -= 1;
            continue;
        }
        let mut bottom = remaining.saturating_sub(width);
        while ((n >> bottom) & BigUint::one()).is_zero() {
            bottom += 1;
        }
        let length = remaining - bottom;
        let mask = (BigUint::one() << length) - BigUint::one();
        chunks.push((length, (n >> bottom) & mask));
        remaining = bottom;
    }
    let first = chunks[0].1.clone();

    let targets: BTreeSet<_> = chunks
        .iter()
        .filter(|(_, value)| !value.is_zero())
        .map(|(_, value)| value.clone())
        .collect();
    let mut values: BTreeSet<BigUint> = addition_sequence(targets).into_iter().collect();
    let mut accumulator = first;
    for &(chunk_width, ref value) in chunks.iter().skip(1) {
        for _ in 0..chunk_width {
            accumulator <<= 1;
            values.insert(accumulator.clone());
        }
        if !value.is_zero() {
            accumulator += value;
            values.insert(accumulator.clone());
        }
    }
    debug_assert_eq!(&accumulator, n);
    // Values from precomputation above n are unnecessary, as are any duplicates
    // encountered by the long part. Positive summands precede their sum.
    values.into_iter().filter(|value| value <= n).collect()
}

/// §6, pp. 6–7. Reduce the largest pending target until only 1 and 2 remain.
/// Newly inserted values are strictly smaller than the removed target; hence
/// the procedure terminates even if a value is requested more than once.
fn addition_sequence(targets: impl IntoIterator<Item = BigUint>) -> Vec<BigUint> {
    let mut pending: BTreeSet<BigUint> = targets.into_iter().filter(|v| !v.is_zero()).collect();
    pending.insert(BigUint::one());
    pending.insert(BigUint::from(2u32));
    let mut all = pending.clone();
    while let Some(f) = pending.iter().next_back().cloned() {
        if f <= BigUint::from(2u32) {
            break;
        }
        let insertions = choose_reduction(&f, &pending);
        pending.remove(&f);
        for value in insertions {
            debug_assert!(value < f && !value.is_zero());
            pending.insert(value.clone());
            all.insert(value);
        }
    }
    all.into_iter().collect()
}

/// Prefer fewer new values, then fewer bits in the largest new value.
#[allow(clippy::op_ref)]
fn choose_reduction(f: &BigUint, pending: &BTreeSet<BigUint>) -> Vec<BigUint> {
    let lower: Vec<_> = pending.range(..f).cloned().collect();
    let mut best: Option<(usize, usize, Vec<BigUint>)> = None;
    let mut consider = |values: Vec<BigUint>| {
        let mut unique = BTreeSet::new();
        for v in values {
            if v.is_zero() || &v >= f {
                return;
            }
            unique.insert(v);
        }
        let cost = (
            unique.iter().filter(|v| !pending.contains(*v)).count(),
            unique.iter().next_back().map_or(0, |v| v.bits() as usize),
        );
        if match best.as_ref() {
            Some((count, bits, _)) => cost < (*count, *bits),
            None => true,
        } {
            best = Some((cost.0, cost.1, unique.into_iter().collect()));
        }
    };

    // Approximation (§6, p. 6): f=a+b+epsilon, insert a+epsilon when
    // epsilon is already pending. epsilon=0 is a direct sum (including a=b).
    for (i, a) in lower.iter().enumerate() {
        for b in &lower[i..] {
            if a + b > *f {
                break;
            }
            let epsilon = f - a - b;
            if epsilon.is_zero() {
                consider(Vec::new());
                return Vec::new();
            }
            if pending.contains(&epsilon) {
                consider(vec![a + &epsilon]);
            }
        }
    }

    // Division (§6, p. 7): use the paper's p=3,5,9,17. The chosen
    // addition chains for p are 1,2,3; 1,2,4,5; 1,2,4,8,9; and
    // 1,2,4,8,16,17, respectively. Scaling them by q=f/p gives f.
    for &(p, last_power) in &[(3u32, 1usize), (5, 2), (9, 3), (17, 4)] {
        let divisor = BigUint::from(p);
        if f % &divisor == BigUint::zero() {
            let q = f / &divisor;
            let values = (0..=last_power).map(|j| &q << j).collect();
            consider(values);
        }
    }

    // Halving (§6, p. 7): f=k*2^u+d, 0<=d<2^u. Insert k and
    // k*2,...,k*2^u; the last addition is with d when d>0.
    // The paper's example f=382, u=4 gives k=23 and d=14.
    for u in 1..f.bits() as usize {
        let k = f >> u;
        if k.is_zero() {
            break;
        }
        let multiple = &k << u;
        let d = f - &multiple;
        let mut values: Vec<_> = (0..=u)
            .filter(|&j| j < u || !d.is_zero())
            .map(|j| &k << j)
            .collect();
        if !d.is_zero() {
            values.push(d);
        }
        consider(values);
    }

    // Lucas (§6, p. 7): u_0=a, u_1=a+r, u_(i+1)=u_i+u_(i-1).
    // Check small positive r already in the protosequence. A known r
    // constructs u_1; subsequent terms are sums of the prior two.
    for a in &lower {
        for r in lower.iter().take_while(|r| *r <= &BigUint::from(8u32)) {
            let mut before = a.clone();
            let mut current = a + r;
            let mut values = vec![current.clone()];
            for _ in 2..=12 {
                let next = &before + &current;
                if &next >= f {
                    if &next == f && values.len() >= 2 {
                        consider(values);
                    }
                    break;
                }
                values.push(next.clone());
                before = current;
                current = next;
            }
        }
    }

    best.expect("halving always yields a reduction").2
}

#[cfg(test)]
mod tests {
    use super::{addition_sequence, find_chain, window_chain};
    use num_bigint::BigUint;
    use num_traits::{One, Zero};
    use std::collections::BTreeSet;

    #[allow(clippy::block_in_if_condition_stmt)]
    fn valid(chain: &[BigUint], target: &BigUint) {
        assert_eq!(chain.first(), Some(&BigUint::one()));
        assert_eq!(chain.last(), Some(target));
        let mut available = BTreeSet::new();
        available.insert(BigUint::one());
        for value in chain.iter().skip(1) {
            assert!(available.iter().all(|earlier| earlier < value));
            assert!(
                available.iter().any(|a| {
                    let b = value - a;
                    available.contains(&b)
                }),
                "{} is not the sum of earlier values in {:?}",
                value,
                chain
            );
            available.insert(value.clone());
        }
    }

    #[test]
    fn zero_one_and_duplicates() {
        assert!(find_chain(&BigUint::zero(), crate::CostModel::Same).is_empty());
        assert_eq!(
            find_chain(&BigUint::one(), crate::CostModel::Same),
            vec![BigUint::one()]
        );
        let sequence = addition_sequence([4u32, 23, 4, 23, 17].iter().map(|&x| x.into()));
        valid(&sequence, &BigUint::from(23u32));
        assert!(sequence.contains(&BigUint::from(17u32)));
    }

    #[test]
    fn published_examples() {
        // §2, p. 2: 15 admits a five-step chain.
        valid(
            &find_chain(&BigUint::from(15u32), crate::CostModel::Same),
            &BigUint::from(15u32),
        );
        let n = BigUint::parse_bytes(b"26235947428953663183191", 10).unwrap();
        // §5, pp. 4–5: the paper compares window constructions for this n;
        // our left-to-right odd windows are not its optimized distribution.
        valid(&window_chain(&n, 5), &n);
        valid(&window_chain(&n, 10), &n);
        valid(&find_chain(&n, crate::CostModel::Same), &n);
        println!(
            "paper exponent: window 5={} window 10={} selected={}",
            window_chain(&n, 5).len() - 1,
            window_chain(&n, 10).len() - 1,
            find_chain(&n, crate::CostModel::Same).len() - 1
        );
    }

    #[test]
    fn small_and_real_exponents() {
        for n in 1..=2048u32 {
            valid(
                &find_chain(&BigUint::from(n), crate::CostModel::Same),
                &BigUint::from(n),
            );
        }
        let n = BigUint::parse_bytes(
            b"39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff",
            16,
        )
        .unwrap();
        let chain = find_chain(&n, crate::CostModel::Same);
        valid(&chain, &n);
        println!("{}-bit exponent: {} operations", n.bits(), chain.len() - 1);
    }
}
