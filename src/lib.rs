//! Library for generating addition chains.

use num_bigint::BigUint;

mod bbbd;

/// Returns the shortest addition chain we can find for the given number, using all
/// available algorithms.
pub fn find_shortest_chain(n: BigUint) -> Vec<BigUint> {
    bbbd::find_shortest_chain(n)
}
