# Changelog
All notable changes will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- Additional algorithms:
  - Bos–Coster-derived window and addition-sequence heuristics, including
    minimum-count/product window distribution
  - Cross Window Method with Addition Sequence Algorithm
  - Kunihiro–Yamamoto Hybrid method

### Changed
- Reduced `build_steps` pair-search work from cubic to quadratic in chain length
  for strictly increasing chains.

## [0.2.1] - 2026-02-26
### Fixed
- Fixed an edge case where duplicate values would occur in some addition chains.

## [0.2.0] - 2020-08-15
### Changed
- Migrated to `num-bigint 0.3`.

## [0.1.0] - 2019-12-19

Initial release!
