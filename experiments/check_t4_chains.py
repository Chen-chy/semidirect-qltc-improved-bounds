"""Exact finite tests of the t=4 cubical construction, not asymptotic certificates.

Uses A=F_2^2, Q=C_2 (coordinate swap), all calculations over F_2.
Checks actual quotient permutations, square-zero differentials, and the
homology-dimension identity under shifting directions {3,4}.
The small local codes/graphs are NOT asserted to satisfy the qLTC hypotheses.
Python standard library only.
"""
from itertools import product
from pathlib import Path
import json
import time
import argparse
if __package__:
    from .semidirect_sanity import P, ONE, tmul, in_lambda, mul, inv
else:
    from semidirect_sanity import P, ONE, tmul, in_lambda, mul, inv


def quotient():
    group = tuple(product(P, repeat=4))
    lam = tuple(x for x in group if in_lambda(x))
    unseen, reps, lookup = set(group), [], {}
    while unseen:
        rep = min(unseen)
        coset = {tmul(rep, z) for z in lam}
        assert coset <= unseen
        idx = len(reps)
        reps.append(rep)
        for x in coset:
            lookup[x] = idx
        unseen -= coset
    return reps, lookup


def rank(columns):
    pivots = {}
    for col in columns:
        if not isinstance(col, int) or col < 0:
            raise ValueError("GF(2) bit-vector columns must be nonnegative integers")
        while col:
            pivot = col.bit_length() - 1
            if pivot in pivots:
                col ^= pivots[pivot]
            else:
                pivots[pivot] = col
                break
    return len(pivots)


def null_basis(h, degree):
    if not isinstance(degree, int) or degree < 0:
        raise ValueError("degree must be a nonnegative integer")
    if any(len(row) != degree or any(x not in (0, 1) for x in row) for row in h):
        raise ValueError("Local matrix must be rectangular and binary")
    rows = [sum(x << j for j, x in enumerate(row)) for row in h]
    candidates = [v for v in range(1, 1 << degree)
                  if all((v & r).bit_count() % 2 == 0 for r in rows)]
    basis = []
    for v in candidates:
        if rank(basis + [v]) > len(basis):
            basis.append(v)
    assert len(basis) == degree - rank(rows)
    return [[(v >> j) & 1 for j in range(degree)] for v in basis]


def build_complex(generators, h, shift, reps, lookup):
    degree = len(generators)
    if len(h) != 4 or not isinstance(shift, int) or not 0 <= shift < 16:
        raise ValueError("Exactly four local matrices and a four-bit shift are required")
    if degree == 0 or len(set(generators)) != degree:
        raise ValueError("A nonempty set of distinct generators is required")
    if any(len(row) != degree or any(v not in (0, 1) for v in row)
           for matrix in h for row in matrix):
        raise ValueError("All local rows must be binary and have generator-set width")
    dims = [len(a) for a in h]
    perms = {}
    iperms = {}
    for i in range(4):
        for a, p in enumerate(generators):
            e = tuple(p if i == j else ONE for j in range(4))
            ie = tuple(inv(p) if i == j else ONE for j in range(4))
            perms[i, a] = [lookup[tmul(e, x)] for x in reps]
            iperms[i, a] = [lookup[tmul(ie, x)] for x in reps]
    bases = [[] for _ in range(5)]
    # coordinate triple = (generator or -1, flag or -1, coefficient or -1)
    for mask in range(16):
        grade = (mask ^ shift).bit_count()
        axes = [[(a, -1, -1) for a in range(degree)] if mask >> i & 1
                else [(-1, b, c) for b in range(2) for c in range(dims[i])]
                for i in range(4)]
        for x in range(len(reps)):
            for coordinates in product(*axes):
                bases[grade].append((mask, x, coordinates))
    indices = [{key: idx for idx, key in enumerate(basis)} for basis in bases]
    differentials = []
    for grade in range(4):
        cols = []
        for mask, x, coordinates in bases[grade]:
            out = 0
            for i in range(4):
                present, reversed_axis = bool(mask >> i & 1), bool(shift >> i & 1)
                if present == reversed_axis:
                    # Only moves increasing |mask XOR shift|.
                    if not reversed_axis:
                        _, b, c = coordinates[i]
                        for a in range(degree):
                            if h[i][c][a]:
                                y = x if b == 0 else iperms[i, a][x]
                                target = list(coordinates)
                                target[i] = (a, -1, -1)
                                row = indices[grade + 1][(mask | (1 << i), y, tuple(target))]
                                out ^= 1 << row
                    else:
                        a, _, _ = coordinates[i]
                        for b in range(2):
                            y = x if b == 0 else perms[i, a][x]
                            for c in range(dims[i]):
                                if h[i][c][a]:
                                    target = list(coordinates)
                                    target[i] = (-1, b, c)
                                    row = indices[grade + 1][(mask ^ (1 << i), y, tuple(target))]
                                    out ^= 1 << row
            cols.append(out)
        differentials.append(cols)
    composition_columns = 0
    for i in range(3):
        for col in differentials[i]:
            out = 0
            while col:
                bit = col & -col
                out ^= differentials[i + 1][bit.bit_length() - 1]
                col ^= bit
            assert out == 0, ('square-zero failure', grade, i)
            composition_columns += 1
    ranks = [rank(d) for d in differentials]
    sizes = [len(b) for b in bases]
    homology = [sizes[i] - (ranks[i - 1] if i else 0)
                - (ranks[i] if i < 4 else 0) for i in range(5)]
    expected = [0] * 5
    for mask in range(16):
        sz = len(reps) * degree ** mask.bit_count() * 2 ** (4 - mask.bit_count())
        for i in range(4):
            if not mask >> i & 1:
                sz *= dims[i]
        expected[(mask ^ shift).bit_count()] += sz
    assert sizes == expected
    return dict(dimensions=sizes, differential_ranks=ranks,
                homology_dimensions=homology, square_zero_columns=composition_columns)


def main():
    if not __debug__:
        raise SystemExit("Refusing optimized Python: these checks require assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    start = time.perf_counter()
    reps, lookup = quotient()
    cases = [
        ([(0, 1), (1, 0)], [[[1, 1]]] * 4),
        ([(0, 1), (1, 0), (2, 0)],
         [[[1, 1, 1]], [[1, 0, 1]], [[1, 0, 1], [0, 1, 1]], [[1, 0, 1], [0, 1, 0]]])
    ]
    results = []
    for generators, h in cases:
        assert set(generators) == {inv(x) for x in generators}
        assert ONE not in generators
        original = build_complex(generators, h, 0, reps, lookup)
        duals = [h[i] if i < 2 else null_basis(h[i], len(generators)) for i in range(4)]
        shifted = build_complex(generators, duals, 12, reps, lookup)
        assert original['homology_dimensions'] == shifted['homology_dimensions']
        result = dict(degree=len(generators), local_row_counts=list(map(len, h)),
                      original=original, shifted=shifted,
                      shifting_homology_identity=True)
        results.append(result)
        print(json.dumps(result, ensure_ascii=False), flush=True)
    summary = dict(status='PASS', arithmetic='exact GF(2), integer XOR',
                   scope='finite structural checks only; not asymptotic qLTC verification',
                   base_size=len(reps), cases=results, seconds=time.perf_counter()-start)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
