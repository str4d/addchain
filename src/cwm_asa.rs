//! Cross Window Method with Addition Sequence Algorithm (CWM-ASA).
//!
//! Implements the algorithm from Ding, Guo, Guan, Song, Zhang, and Liu,
//! "Some New Methods to Generate Short Addition Chains", TCHES 2023(2),
//! pp. 270–285, Sections 3.2–3.3, Algorithms 5–7.
//! https://doi.org/10.46586/tches.v2023.i2.270-285
//!
//! Algorithm line numbers below refer to the published TCHES version:
//! Algorithm 5 on p. 278, and Algorithms 6–7 on p. 279.
//!
//! Two interpretations of the published pseudocode are important:
//! - Algorithm 5's window indices disagree with the precomputation layout for
//!   odd k and partial windows. We use the stated layout a || 0^s || b, with
//!   R = ceil(k/2) bits on the right, including the boundary cases omitted in
//!   the pseudocode. This also reproduces the partial windows in Figure 6.
//! - Algorithm 6 resumes at the predecessor x: inserted binary multiples
//!   already have constructions, while a new remainder below x shifts its
//!   index. We locate x directly instead of maintaining the pseudocode's
//!   conditional index adjustment.

// Keep compatibility with compilers predating usize::div_ceil.
#![allow(clippy::manual_div_ceil)]

use std::collections::BTreeSet;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};

/// Searches the parameter range used in Section 4, retaining the first candidate
/// on ties. Capping the span at the input length avoids redundant windows.
pub(super) fn find_chain(n: &BigUint) -> Vec<BigUint> {
    let bits = n.bits() as usize;
    let mut best = chain(n, 1, 0);
    if n == &(BigUint::one() << (bits - 1)) {
        return best;
    }
    for k in 1..=20.min(bits) {
        for s in 0..=20.min(bits - k) {
            let candidate = chain(n, k, s);
            if candidate.len() < best.len() {
                best = candidate;
            }
        }
    }
    best
}

/// Algorithm 7, with Algorithm 5's construction (lines 22–31) deferred until after
/// selecting the precomputation.
fn chain(n: &BigUint, k: usize, s: usize) -> Vec<BigUint> {
    // Algorithm 7, line 1: obtain the used windows N from Algorithm 5.
    let windows = windows(n, k, s);

    // Algorithm 7, line 2: construct ASA(N).
    let mut sequence = addition_sequence(windows.iter().map(|w| w.1.clone()));

    // Algorithm 7, lines 3–5: select the shorter precomputation. The original
    // precomputation length is given in Section 3.2, pp. 276–277. For s=0,
    // the odd dictionary has no additional 2. For s>0 and R=1, step (2)'s
    // first power is the already-constructed 2.
    let right = (k + 1) / 2;
    let original_len = (1usize << (k - 1))
        + if s == 0 {
            0
        } else {
            s + usize::from(right > 1)
        };
    if original_len <= sequence.len() {
        sequence = precomputation(k, s);
    }

    // Algorithm 5's construction is not necessarily increasing relative to
    // the precomputation. Set union removes reused values; sorting is valid
    // because both positive summands are smaller than their sum. Discard the
    // unused precomputation values above n so the target is always last.
    let mut values: BTreeSet<_> = sequence.into_iter().filter(|v| v <= n).collect();

    // Algorithm 5, lines 22–23: initialize from the largest occupied position.
    let (mut position, mut value) = windows[0].clone();

    // Algorithm 5, lines 24–30: double between positions (line 25), then add
    // each recorded window (lines 26–28).
    for &(next_position, ref window) in windows.iter().skip(1) {
        while position > next_position {
            value <<= 1;
            values.insert(value.clone());
            position -= 1;
        }
        value += window;
        values.insert(value.clone());
    }

    // Algorithm 5, lines 24–30: remaining positions with no recorded window.
    while position > 0 {
        value <<= 1;
        values.insert(value.clone());
        position -= 1;
    }
    debug_assert_eq!(&value, n);
    values.into_iter().collect()
}

/// Extracts and records windows M.
///
/// Algorithm 5, lines 6–21. The right-part width R comes from lines 1–5. Each pair is
/// (least-significant-bit position, odd window value); the shifted windows partition the
/// set bits of n. The result is sorted for construction in lines 22–30.
fn windows(n: &BigUint, k: usize, s: usize) -> Vec<(usize, BigUint)> {
    assert!(k > 0);
    let mut remaining = n.clone();
    let mut result = Vec::new();
    let right = (k + 1) / 2;

    while !remaining.is_zero() {
        // Lines 7–11: skip leading zeros and find the longest odd window.
        let top = remaining.bits() as usize;
        let mut bottom = top.saturating_sub(k + s);
        while (&remaining >> bottom).is_even() {
            bottom += 1;
        }
        let width = top - bottom;
        let mut window = &remaining >> bottom;
        if s > 0 {
            if width > right + s {
                // Lines 12–14, using the layout described in Section 3.2:
                // keep at most L high bits and R low bits, clearing the gap.
                let low_mask = (BigUint::one() << right) - BigUint::one();
                window = ((&window >> (right + s)) << (right + s)) + (&window & low_mask);
            } else if width > right {
                // Lines 15–18, including the omitted width = R+s case:
                // the high bit lies in the gap; use a short ordinary window.
                bottom = top.saturating_sub(right);
                while (&remaining >> bottom).is_even() {
                    bottom += 1;
                }
                window = &remaining >> bottom;
            }
        }

        // Line 19: aligned subtraction and M_j = w. Recomputing the highest
        // remaining bit on the next iteration replaces the i = i-c update.
        remaining -= &window << bottom;
        result.push((bottom, window));
    }

    result.sort_by_key(|w| std::cmp::Reverse(w.0));
    result
}

/// Builds an addition sequence containing all targets.
///
/// Algorithm 6. The inserted scaled binary chain constructs `q*x`, and the remainder
/// constructs `y = q*x + r`.
fn addition_sequence(targets: impl Iterator<Item = BigUint>) -> Vec<BigUint> {
    // Lines 1–3: sort the targets, include 1 and 2, and start at the largest.
    let mut sequence: Vec<_> = targets.collect::<BTreeSet<_>>().into_iter().collect();
    insert(&mut sequence, BigUint::one());
    insert(&mut sequence, BigUint::from(2u32));
    let mut j = sequence.len() - 1;

    while j > 1 {
        // Lines 4–5: decompose adjacent targets as y = q*x + remainder.
        let x = sequence[j - 1].clone();
        let (q, remainder) = sequence[j].div_rem(&x);

        // Line 6: insert BM_x(q*x), using Algorithm 1's binary construction
        // (lines 1–7, p. 272) scaled by x.
        let mut multiple = x.clone();
        for bit in (0..q.bits() - 1).rev() {
            multiple <<= 1;
            insert(&mut sequence, multiple.clone());
            if (&q >> bit as usize).is_odd() {
                multiple += &x;
                insert(&mut sequence, multiple.clone());
            }
        }

        // Lines 7–10: insert the nonzero remainder if absent.
        if !remainder.is_zero() {
            insert(&mut sequence, remainder);
        }

        // Lines 9 and 11: resume at x, accounting for any inserted remainder.
        j = sequence.binary_search(&x).expect("predecessor is retained");
    }

    sequence
}

/// Original CWM precomputation.
///
/// Algorithm 5, lines 1–5. Its construction is specified in Section 3.2, steps (1)–(3) on
/// p. 276, with the `s = 0` case on p. 277.
fn precomputation(k: usize, s: usize) -> Vec<BigUint> {
    let right = if s == 0 { k } else { (k + 1) / 2 };

    // Section 3.2, step (1): odd numbers from 1 to 2^R - 1, and 2.
    let mut sequence = vec![BigUint::one(), BigUint::from(2u32)];
    for odd in (3..(1usize << right)).step_by(2) {
        sequence.push(BigUint::from(odd));
    }

    if s > 0 {
        // Section 3.2, step (2): interval expansion powers.
        for bit in right..=right + s {
            insert(&mut sequence, BigUint::one() << bit);
        }

        // Section 3.2, step (3): combine high parts with odd low parts.
        let base = BigUint::one() << (right + s);
        for high in 1..(1usize << (k - right)) {
            for odd in (1..(1usize << right)).step_by(2) {
                sequence.push(&base * BigUint::from(high) + BigUint::from(odd));
            }
        }
    }

    sequence
}

/// Sorted-set insertion used by Algorithm 6, lines 2, 6, and 8, and by the
/// precomputation's interval expansion. Not a separate algorithm in the paper.
fn insert(sequence: &mut Vec<BigUint>, value: BigUint) {
    if let Err(index) = sequence.binary_search(&value) {
        sequence.insert(index, value);
    }
}

#[cfg(test)]
mod tests {
    use super::{addition_sequence, chain, precomputation, windows};
    use num_bigint::BigUint;
    use num_traits::One;

    fn validate(chain: &[BigUint], target: &BigUint) {
        assert_eq!(chain.first(), Some(&BigUint::one()));
        assert_eq!(chain.last(), Some(target));
        assert!(chain.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(crate::build_steps(chain.to_vec()).is_ok());
    }

    #[test]
    fn figure_6_windows() {
        let n = BigUint::parse_bytes(b"11111011100011001101001", 2).unwrap();
        let extracted = windows(&n, 6, 3);
        // Section 3.2, Figure 6, in extraction order (before position sorting).
        let expected = [
            (14, 0b1_1100_0111u32),
            (18, 0b11),
            (3, 0b1100_0101),
            (0, 0b100_0001),
        ];
        for &(position, value) in &expected {
            assert!(
                extracted.contains(&(position, BigUint::from(value))),
                "{:?}",
                extracted
            );
        }
        assert_eq!(extracted.len(), expected.len());
        let result = chain(&n, 6, 3);
        validate(&result, &n);
    }

    #[test]
    fn asa_multiple_and_remainder_insertions() {
        for targets in &[
            vec![1u32],
            vec![31],
            vec![3, 100],
            vec![7, 23, 101],
            vec![3, 3, 17],
        ] {
            let sequence = addition_sequence(targets.iter().map(|v| BigUint::from(*v)));
            validate(&sequence, sequence.last().unwrap());
            for target in targets {
                assert!(sequence.contains(&BigUint::from(*target)));
            }
        }
        // A scaled binary chain for 100/3 inserts several values above x;
        // the remainder below x must still be processed.
        let sequence =
            addition_sequence(vec![BigUint::from(3u32), BigUint::from(100u32)].into_iter());
        assert!(sequence.contains(&BigUint::from(99u32)));
    }

    #[test]
    fn asa_target_pairs() {
        for x in 1..=64u32 {
            for y in x..=128u32 {
                let targets = vec![BigUint::from(x), BigUint::from(y)];
                let sequence = addition_sequence(targets.into_iter());
                validate(&sequence, sequence.last().unwrap());
            }
        }
    }

    #[test]
    fn portfolio_small_inputs() {
        let mut improvements = 0;
        for value in 1..=2048u32 {
            let n = BigUint::from(value);
            let baseline = crate::bbbd::find_shortest_chain(n.clone());
            let result = crate::find_shortest_chain(n.clone());
            validate(&result, &n);
            assert!(result.len() <= baseline.len());
            if result.len() < baseline.len() {
                improvements += 1;
            }
        }
        assert!(improvements > 0);
        println!("CWM-ASA improves {} of 2048 small inputs", improvements);
    }

    #[test]
    fn large_inputs() {
        let mut state = 0x1234_5678u32;
        for bits in &[128usize, 256, 512, 1024, 2048, 4096] {
            let dense = (BigUint::one() << *bits) - BigUint::one();
            let sparse = (BigUint::one() << (*bits - 1)) + BigUint::from(65537u32);
            let mut bytes = vec![0u8; bits / 8];
            for byte in &mut bytes {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                *byte = state as u8;
            }
            bytes[0] |= 128;
            let random = BigUint::from_bytes_be(&bytes);
            for (name, n) in &[("dense", dense), ("sparse", sparse), ("random", random)] {
                let baseline = crate::bbbd::find_shortest_chain(n.clone());
                let start = std::time::Instant::now();
                let result = crate::find_shortest_chain(n.clone());
                let elapsed = start.elapsed();
                // Also validate CWM-ASA itself when BBBD wins the comparison.
                validate(&chain(n, 7, 3), n);
                println!(
                    "{}-bit {}: BBBD {}, portfolio {}, {:?}",
                    bits,
                    name,
                    baseline.len() - 1,
                    result.len() - 1,
                    elapsed
                );
                validate(&result, n);
                assert!(result.len() <= baseline.len());
            }
        }
    }

    #[test]
    fn precomputation_cost() {
        for k in 1..=5 {
            for s in 0..=5 {
                let right = (k + 1) / 2;
                let expected = (1usize << (k - 1))
                    + if s == 0 {
                        0
                    } else {
                        s + usize::from(right > 1)
                    };
                assert_eq!(precomputation(k, s).len() - 1, expected, "k={}, s={}", k, s);
            }
        }
    }

    #[test]
    fn exhaustive_small_parameters() {
        for k in 1..=5 {
            for s in 0..=5 {
                let precomputed = precomputation(k, s);
                validate(&precomputed, precomputed.last().unwrap());
                for n in 1..=255u32 {
                    let n = BigUint::from(n);
                    let extracted = windows(&n, k, s);
                    let mut reconstructed = BigUint::from(0u32);
                    for (position, window) in &extracted {
                        assert!(
                            precomputed.contains(window),
                            "k={}, s={}, window={}",
                            k,
                            s,
                            window
                        );
                        reconstructed += window << *position;
                    }
                    assert_eq!(reconstructed, n);
                    validate(&chain(&n, k, s), &n);
                }
            }
        }
    }
}
