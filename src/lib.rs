//! Library for generating addition chains.

use num_bigint::BigUint;
use num_traits::One;

mod bbbd;

/// The error kinds returned by `addchain` APIs.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// The provided chain is invalid.
    InvalidChain,
}

/// Returns the shortest addition chain we can find for the given number, using all
/// available algorithms.
pub fn find_shortest_chain(n: BigUint) -> Vec<BigUint> {
    bbbd::find_shortest_chain(n)
}

/// A single step in computing an addition chain.
#[derive(Debug, PartialEq)]
pub enum Step {
    Double { index: usize },
    Add { left: usize, right: usize },
}

/// Converts an addition chain into a series of steps.
pub fn build_steps(chain: Vec<BigUint>) -> Result<Vec<Step>, Error> {
    match chain.get(0) {
        Some(n) if n.is_one() => (),
        _ => return Err(Error::InvalidChain),
    }

    let mut steps = vec![];

    for (i, val) in chain.iter().enumerate().skip(1) {
        // Find the pair of previous values that add to this one
        'search: for (j, left) in chain[..i].iter().enumerate() {
            for (k, right) in chain[..=j].iter().enumerate() {
                if val == &(left + right) {
                    // Found the pair!
                    if j == k {
                        steps.push(Step::Double { index: j })
                    } else {
                        steps.push(Step::Add { left: j, right: k });
                    }
                    break 'search;
                }
            }
        }

        // We must always find a matching pair
        if steps.len() != i {
            return Err(Error::InvalidChain);
        }
    }

    Ok(steps)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::{build_steps, Error, Step};

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
