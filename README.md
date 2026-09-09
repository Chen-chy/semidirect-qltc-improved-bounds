# Improved qLTCs via Semidirect Products: A Proposed One-Logarithm Gain in Distance and Soundness

[简体中文](README.zh-CN.md) · [Theorem](docs/THEOREM.zh-CN.md) · [Proof manuscript](docs/PROOF.zh-CN.md) · [References](REFERENCES.md)

**We propose a semidirect-product qLTC construction that improves the DLV distance and global soundness lower bounds from inverse-log-cubed to inverse-log-squared losses, while retaining constant rate and constant check weight.** This is a draft research claim awaiting independent verification of the general argument; the finite checks below do not establish the asymptotic result.

A research manuscript and exact finite structural checks for the semidirect-product construction at **$t=4,j=2$**. The claimed family has fixed local data and, along a specified unbounded sequence of block lengths,

$$
k=\Theta(n),\quad d_X,d_Z=\Omega(n/\log^2 n),\quad
m=\Theta(n),\quad w_{\max},\Delta_{\max}=O(1),\quad
\rho=\Omega(1/\log^2 n).
$$

The mathematical argument uses the explicitly versioned external inputs of Kaufman–Lubotzky, Kalachev–Panteleev, and Dinur–Lin–Vidick. The semidirect coset geometry yields a directional component fraction $\eta=b^{-2}$; the chosen classical family has $b=\Theta(\log n)$. See the [dependency ledger](docs/DEPENDENCIES.zh-CN.md) for the precise interfaces.

**This is not a kernel-verified theorem.** The proof manuscript, bounded finite computations, and uncompiled Lean source are separate artifacts. A passing regular CI run certifies only the repository and finite tests. No claim of peer review, priority, novelty, or optimality is made.

## Main comparison

| Construction | Encoded qubits | Distance guarantee | Global soundness guarantee | Check weight |
| --- | --- | --- | --- | --- |
| DLV, arXiv:2402.07476v3, Theorem 1.1 | $\Theta(n)$ | $\Omega(n/\log^3 n)$ | $\Omega(1/\log^3 n)$ | $O(1)$ |
| This manuscript | $\Theta(n)$ | $\Omega(n/\log^2 n)$ | $\Omega(1/\log^2 n)$ | $O(1)$ |

The claimed improvement concerns asymptotic lower bounds, not measured finite-size performance or an upper bound on what the DLV family can achieve. This remains an almost-good qLTC result. We do not assert an unqualified world-best result; see the [comparison and scope](docs/COMPARISON.md).

## Reproduce

Python 3.10+ and its standard library suffice:

```bash
python scripts/verify.py
```

Run from the repository root. Results are written to `.artifacts/verification/`; checked-in baselines are never overwritten. Optimized Python (`-O`) is rejected. The checks enumerate actual left cosets and construct two finite four-dimensional complexes over GF(2), testing square-zero differentials, ranks, and equality of homology dimensions under shifting. These examples are not asserted to satisfy the asymptotic theorem's robustness or spectral hypotheses.

For every Pauli error, the tester uses **distance to the centralizer**, not distance to the stabilizer group. The proof also describes the corresponding syndrome-diagonal distance observable for arbitrary quantum states. The tester retains all listed local checks, including redundant ones.

## Layout and limits

`docs/` contains the Chinese theorem, full proof manuscript, notation, dependency and reproduction notes. `experiments/` contains exact finite checks; `tests/` contains bounded exhaustive and regression tests; `formalization/lean4/` contains the earlier uncompiled conditional formalization attempt, with its outstanding obligations. `verification/` contains baseline certificates and the actual packaging-run record.

There is no complete implemented asymptotic code-family generator, certified large robust local tuple, or decoder in this release. The full Lean existence theorem is not completed. Compiling the conditional modules would not by itself complete that theorem.

This is the `0.1.0-draft` source snapshot, not an already published GitHub release. Author names, affiliations, repository URL, DOI, and a project-wide license have not been assigned. See [RIGHTS](RIGHTS.md), [provenance](provenance/README.md), and [publishing instructions](docs/PUBLISHING.zh-CN.md).
