# 0.1.0-draft — Improved qLTC parameter guarantees

This source snapshot contains the four-dimensional semidirect qLTC theorem manuscript, its external-dependency ledger, and exact finite structural checks. The parameters recorded in the manuscript are constant rate and locality, distance $\Omega(n/\log^2 n)$, and global soundness $\Omega(1/\log^2 n)$ along the specified infinite length sequence.

The headline claim is a one-logarithm improvement in both lower-bound guarantees over DLV (arXiv:2402.07476v3, Theorem 1.1), retaining constant rate and locality. See [comparison and scope](docs/COMPARISON.md). This is a manuscript claim, not an unqualified best-known or finite-performance claim.

The release separates the mathematical manuscript, finite computational evidence, and unfinished Lean source. Passing finite checks do not certify the asymptotic theorem. The Lean modules have not been kernel-verified, and the complete existence theorem is not implemented.

Reproduce with `python scripts/verify.py`. Consult [the verification record](verification/packaging_run/summary.json), [scope](docs/VERIFICATION_STATUS.zh-CN.md), and [licensing status](RIGHTS.md) before citing or redistributing this snapshot.

These notes are prepared for a maintainer-created prerelease. They do not assert that the tag, remote repository, or release already exists.
