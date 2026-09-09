"""Exact checks of displayed constant substitutions, not external theorems."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


def check() -> dict:
    nu = Fraction(1, 32)
    beta = 2 - (1 + 2 * nu) ** 4
    if beta != Fraction(47551, 65536) or beta <= 0:
        raise AssertionError("Positive-rate bracket mismatch")
    # Multiplication of the two monomial denominators (8D)^9 and
    # 2*(4096*D^5)^4: coefficients and exponents are checked separately.
    coefficient = 8**9 * 2 * 4096**4
    exponent = 9 + 5 * 4
    if coefficient != 2**76 or exponent != 29:
        raise AssertionError("Cycle-transfer first denominator mismatch")
    # Compare the two candidates at a bounded set of degrees as a regression.
    for degree in range(1, 65):
        first = Fraction(1, (8 * degree)**9 * 2 * (4096 * degree**5)**4)
        conservative = Fraction(1, 2**76 * degree**29)
        second = Fraction(1, 3 * 2**20 * degree**7)
        if first != conservative or second < conservative:
            raise AssertionError(f"Transfer substitution failed at D={degree}")
        for ell in range(1, 5):
            # Divide the face-block systolic coefficient by the upper n/N bound.
            derived = Fraction(3, 2**17 * degree**6) / (24 * ell * degree**4)
            if derived != Fraction(1, 2**20 * ell * degree**10):
                raise AssertionError("Binary distance normalization mismatch")
    return {
        "status": "PASS",
        "arithmetic": "exact rational/integer identities",
        "nu": str(nu),
        "beta": str(beta),
        "rate_lower_beta_over_24": str(beta / 24),
        "cycle_first_term_denominator": "2^76 * D^29",
        "cycle_second_term_denominator": "3 * 2^20 * D^7",
        "binary_distance_coefficient": "gamma / (2^20 * ell * D^10)",
        "note": "Checks substitutions only; these do not verify the cited external theorems.",
    }


def main() -> None:
    if not __debug__:
        raise SystemExit("Refusing optimized Python: verification requires assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(check(), ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
