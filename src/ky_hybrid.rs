//! Kunihiro–Yamamoto Hybrid method, combining the Run-length and Window methods.
//!
//! Kunihiro and Yamamoto, "New Methods for Generating Short Addition Chains",
//! IEICE Trans. Fundamentals E83-A(1), pp. 60–67 (2000), Section 3.3.
//!
//! The Hybrid dictionary and parsing include the Run-length method of
//! Section 3.1 when `k = 2` (and the Window method when `k = t`).
//! We evaluate actual chain lengths across a bounded parameter range rather
//! than minimizing the paper's *average* lengths, Eqs. (7) and (10).

use std::collections::BTreeSet;

use num_bigint::BigUint;
use num_traits::One;

/// Finds a short ordinary addition chain for a positive exponent.
///
/// Section 3 leaves the choice of `t` and `k` to the implementer. The bounds
/// here limit dictionary size and search time; `k = t = 1` always supplies a
/// binary-method candidate, even for much longer inputs.
pub(super) fn find_chain(n: &BigUint, cost_model: crate::CostModel) -> Vec<BigUint> {
    assert!(
        *n >= BigUint::one(),
        "addition chains require a positive target"
    );
    let bits = n.to_str_radix(2);
    let bits = bits.as_bytes();
    let mut best = chain(bits, n, 1, 1);
    let max_k = bits.len().min(8);
    let max_t = bits.len().min(48);
    for k in 1..=max_k {
        for t in k..=max_t {
            let candidate = chain(bits, n, k, t);
            if cost_model.cost(&candidate) < cost_model.cost(&best) {
                best = candidate;
            }
        }
    }
    best
}

/// Section 3.3, Step 2: all odd numbers below `2^k`, followed by the
/// successive odd numbers `2^i - 1` for `k < i <= t`. Its explicit chain
/// uses `2` to reach the first odd number and, for each additional Mersenne
/// number, doubles the preceding one and adds `1`.
fn dictionary(k: usize, t: usize) -> Vec<BigUint> {
    assert!(k >= 1 && k <= t);
    let mut values = vec![BigUint::one()];
    if k > 1 {
        values.push(BigUint::from(2u32));
        for odd in (3..(1usize << k)).step_by(2) {
            values.push(BigUint::from(odd));
        }
    }
    for width in k + 1..=t {
        values.push((BigUint::one() << width) - BigUint::from(2u32));
        values.push((BigUint::one() << width) - BigUint::one());
    }
    values
}

/// Section 3.3, Step 3, Phases 1(a), 1(b), and 2. With `k = 2`, this is
/// also Section 3.1, Step 3. The final group may be shorter than `k` or
/// `t`, as noted below Table 1 in Section 4.
///
/// The first group's nonzero odd part already belongs to the dictionary, so
/// we start at that value rather than applying the first doubling/star pair
/// to `1` (the first-parsing exception in Section 2.2, Note 9). Taking the
/// union of dictionary and main-procedure values removes any other repeated
/// values at their concatenation; sorting is valid since every operation adds
/// strictly smaller positive operands.
fn chain(bits: &[u8], n: &BigUint, k: usize, t: usize) -> Vec<BigUint> {
    let mut values: BTreeSet<_> = dictionary(k, t).into_iter().filter(|v| v <= n).collect();
    let mut position = 0;
    let mut current: Option<BigUint> = None;
    while position < bits.len() {
        // Phase 2: zero bits between groups are plain doublings.
        if bits[position] == b'0' {
            let value = current.as_mut().expect("the leading bit is one");
            *value <<= 1;
            values.insert(value.clone());
            position += 1;
            continue;
        }

        // Phase 1(a) parses a k-bit window if it contains a zero. Phase
        // 1(b) instead consumes a run of at most t ones. At the end of the
        // exponent a truncated k-bit window is processed in the same way.
        let end = (position + k).min(bits.len());
        let window = &bits[position..end];
        let (width, odd_width, addend) = if window.contains(&b'0') {
            let odd_width = window.iter().rposition(|&bit| bit == b'1').unwrap() + 1;
            let mut odd = BigUint::one();
            for &bit in &window[1..odd_width] {
                odd <<= 1;
                if bit == b'1' {
                    odd += 1u32;
                }
            }
            (window.len(), odd_width, odd)
        } else {
            let mut width = window.len();
            while width < t && position + width < bits.len() && bits[position + width] == b'1' {
                width += 1;
            }
            (width, width, (BigUint::one() << width) - BigUint::one())
        };

        if let Some(value) = current.as_mut() {
            // Phases 1(a)/(b): double once per bit of the odd addend,
            // add it, then double for the remaining trailing zeros.
            for _ in 0..odd_width {
                *value <<= 1;
                values.insert(value.clone());
            }
            *value += &addend;
            values.insert(value.clone());
        } else {
            debug_assert!(values.contains(&addend));
            current = Some(addend);
        }
        let value = current.as_mut().unwrap();
        for _ in odd_width..width {
            *value <<= 1;
            values.insert(value.clone());
        }
        position += width;
    }
    debug_assert_eq!(current.as_ref(), Some(n));
    values.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::{chain, dictionary, find_chain};
    use num_bigint::BigUint;
    use num_traits::One;

    fn validate(chain: &[BigUint], n: &BigUint) {
        assert_eq!(chain.first(), Some(&BigUint::one()));
        assert_eq!(chain.last(), Some(n));
        assert!(chain.windows(2).all(|w| w[0] < w[1]));
        assert!(crate::build_steps(chain.to_vec()).is_ok());
    }

    #[test]
    fn section_3_1_example() {
        let n = BigUint::from(445u32);
        assert_eq!(
            dictionary(2, 3),
            [1u32, 2, 3, 6, 7]
                .iter()
                .cloned()
                .map(BigUint::from)
                .collect::<Vec<_>>()
        );
        let expected = [1u32, 2, 3, 6, 7, 12, 24, 48, 55, 110, 111, 222, 444, 445]
            .iter()
            .cloned()
            .map(BigUint::from)
            .collect::<Vec<_>>();
        assert_eq!(chain(n.to_str_radix(2).as_bytes(), &n, 2, 3), expected);
        validate(&expected, &n);
    }

    #[test]
    fn section_3_3_example() {
        let n = BigUint::from(75_064_310u32);
        let result = chain(n.to_str_radix(2).as_bytes(), &n, 3, 5);
        validate(&result, &n);
        assert_eq!(
            dictionary(3, 5),
            [1u32, 2, 3, 5, 7, 14, 15, 30, 31]
                .iter()
                .cloned()
                .map(BigUint::from)
                .collect::<Vec<_>>()
        );
        // Section 3.3 reports 40 operations; eliminating repeated values
        // at concatenation cannot increase the operation count.
        assert!(result.len() - 1 <= 40, "{}", result.len() - 1);
    }

    #[test]
    fn exhaustive_small_inputs_and_parameters() {
        for n in 1..=512u32 {
            let n = BigUint::from(n);
            let bits = n.to_str_radix(2);
            for k in 1..=bits.len().min(5) {
                for t in k..=bits.len().min(8) {
                    validate(&chain(bits.as_bytes(), &n, k, t), &n);
                }
            }
            validate(&find_chain(&n, crate::CostModel::Same), &n);
        }
    }

    #[test]
    fn large_and_dense_inputs() {
        let target = BigUint::parse_bytes(
            b"39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff",
            16,
        )
        .unwrap();
        // Bounded search gives 272 operations (k = 4, t = 4); this method
        // does not improve on the 267-operation baseline for this input.
        assert_eq!(find_chain(&target, crate::CostModel::Same).len() - 1, 272);
        for n in &[
            target,
            (BigUint::one() << 512usize) - BigUint::one(),
            (BigUint::one() << 1023usize) + BigUint::from(65537u32),
        ] {
            validate(&find_chain(n, crate::CostModel::Same), n);
        }
    }
}
