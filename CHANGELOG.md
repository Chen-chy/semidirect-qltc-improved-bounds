# Changelog

## 0.1.0-draft — 2026-09-09 source snapshot

Reorganized the supplied material around the four-dimensional theorem only. Added a standalone theorem statement, proof manuscript with explicit cubical incidence, notation and dependency ledgers, versioned bibliography, reproducibility instructions, and publishing notes.

Retained the exact finite chain construction and reference results; limited the public geometry entry point to dimension four, added input validation and explicit output paths, and prevented optimized Python from bypassing assertions. Added bounded exhaustive/regression tests and a finite-only GitHub Actions workflow.

Kept prior Lean proof terms byte-for-byte in a separate unverified formalization directory. Preserved the missing-toolchain history without upgrading it to a passing result. No full Lean theorem was completed, no remote CI was run, and no GitHub Release was created.

Corrected bibliographic metadata to follow the pinned records: the local product-expansion paper lists Kalachev before Panteleev, and the DLV title uses “higher-dimensional”. No new priority, novelty or optimality claim is introduced.

## Publication wording update — 2026-09-09

- Highlight the claimed one-logarithm improvement over the pinned DLV benchmark in both READMEs and release notes.
- Add a source-linked comparison and distinguish asymptotic guarantees from finite performance and global priority.
- Retain all mathematical statements and verification boundaries.

- Make English the default README; retain Chinese as README.zh-CN.md.
