# Contributing and reviewing

The active scope is the $t=4,j=2$ result. Please separate mathematical corrections, finite-code changes, and formalization work into independently reviewable changes. The project license has not yet been chosen; see [RIGHTS](RIGHTS.md) before contributing under assumed terms.

For mathematical changes, cite the claim ID from [claims.json](claims.json), state the exact hypotheses, and identify any changed constants, normalizations, or dependencies. An issue reporting a potential gap is useful even without a replacement proof. Do not infer a global statement from a bounded computation.

For code changes, run `python scripts/verify.py` and include the command, interpreter version, and result. Do not overwrite baseline certificates merely to obtain passing tests. Assertions must remain enabled. Runtime reports belong in `.artifacts/`, not in the reference baseline.

For Lean changes, use the fixed toolchain in `formalization/lean4/`. Include actual build and axiom-audit logs, and distinguish module compilation from the closed infinite-family theorem. Do not introduce `sorry`, `admit`, additional axioms, or kernel-check bypasses to relabel an unfinished proof as complete. A type-correct conditional theorem still needs its hypotheses established.

No automatic release, merge, or permission change is performed by the included CI. Author and license decisions remain with the repository owner.
