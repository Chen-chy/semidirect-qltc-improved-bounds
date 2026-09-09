# Parameter comparison and claim scope

[中文首页](../README.zh-CN.md) · [English overview](../README.md)

Comparison checked on 2026-09-09. This is a targeted source check, not an exhaustive priority review or an independent verification of the full manuscript.

## Direct benchmark

Dinur, Lin and Vidick, [arXiv:2402.07476v3](https://arxiv.org/html/2402.07476v3), Theorem 1.1 and Corollary 3.9, give constant rate, constant check weight, distance $\Omega(n/\log^3 n)$ and soundness $\Omega(1/\log^3 n)$. The present manuscript claims exponent two in both denominators, with the same asymptotic rate and locality regime, along its specified infinite length sequence.

This is a one-logarithm improvement in the stated lower-bound guarantees. It does not establish a matching upper bound for either family, better finite-size constants, practical superiority, or an implemented generator for the full family. The DLV paper states a polynomial-time construction; this release supplies a proof manuscript and finite examples, not a complete implementation of its asymptotic family.

## Related results and distinct objectives

Li, Li and Liu, [arXiv:2604.01874v1](https://arxiv.org/html/2604.01874v1), Theorem 1.1, give qLTC distance and soundness with logarithmic exponent $2r-1$ for $r\ge2$, together with transversal logical gates. Its minimum displayed qLTC exponent is three. The present manuscript does not establish those transversal-gate properties; this comparison concerns distance and soundness only.

Cross, He, Natarajan, Szegedy and Zhu, [Quantum 8, 1501 (2024)](https://quantum-journal.org/papers/q-2024-10-18-1501/), construct constant-soundness qLTCs with different parameter tradeoffs. Thus inverse-log-squared soundness by itself is not a best-soundness claim.

## Wording supported by this release

> A semidirect-product qLTC manuscript claiming a one-logarithm improvement over the DLV distance and global soundness guarantees, at constant rate and locality.

The mathematical argument and its external inputs require review. Finite tests do not certify asymptotic bounds. Full Lean verification is unfinished. We do not claim a solution to the good-qLTC problem, optimal logarithmic exponents, or comprehensive priority over all literature.
