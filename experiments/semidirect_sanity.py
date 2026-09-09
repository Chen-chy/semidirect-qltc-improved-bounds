"""Exact quotient/orbit checks for A=F_2^2, Q=C_2 acting by swapping bits.
Standard library only. Run: python semidirect_sanity.py
This checks the finite geometry, not spectral expansion or quantum-code parameters.
"""
from itertools import product
from collections import Counter
import argparse
import json
import sys
from pathlib import Path

P = tuple(product(range(4), range(2)))
ONE = (0, 0)
def act(g, a):
    return a if g == 0 else ((a & 1) << 1) | ((a >> 1) & 1)
def mul(x, y):
    a, g = x
    b, h = y
    return (a ^ act(g, b), g ^ h)
def inv(x):
    a, g = x
    return (act(g, a), g)
def tmul(x, y):
    if len(x) != len(y):
        raise ValueError("Direct-product elements must have equal lengths")
    return tuple(mul(a, b) for a, b in zip(x, y))
def tinv(x):
    return tuple(inv(a) for a in x)
def in_lambda(x):
    total = 0
    for a, g in x:
        total ^= a
    return len({g for a, g in x}) == 1 and total == 0

def audit(t=4):
    if t != 4:
        raise ValueError("This release audits t=4 only")
    H = tuple(product(P, repeat=t))
    Lam = tuple(x for x in H if in_lambda(x))
    Lset = set(Lam)
    assert all(tinv(x) in Lset for x in Lam)
    assert all(tmul(x, y) in Lset for x in Lam for y in Lam)
    # Enumerate left cosets x Lambda directly, without the quotient-size formula.
    unseen = set(H)
    cosets = []
    lookup = {}
    while unseen:
        rep = min(unseen)
        coset = {tmul(rep, z) for z in Lam}
        assert coset <= unseen
        cid = len(cosets)
        cosets.append((rep, coset))
        for z in coset:
            lookup[z] = cid
        unseen.difference_update(coset)
    assert len(lookup) == len(H)
    permutations = []
    counts = []
    for i in range(t):
        actions = []
        for p in P:
            h = tuple(p if j == i else ONE for j in range(t))
            action = []
            for rep, coset in cosets:
                images = {lookup[tmul(h, z)] for z in coset}
                assert len(images) == 1  # well-defined on the whole coset
                action.append(images.pop())
            actions.append(tuple(action))
        permutations.append(actions)
        todo = set(range(len(cosets)))
        orbit_sizes = []
        while todo:
            x = min(todo)
            orb = {f[x] for f in actions}
            assert orb <= todo
            orbit_sizes.append(len(orb))
            todo.difference_update(orb)
        counts.append(Counter(orbit_sizes))
    # Check commutation for all group elements from distinct coordinate directions.
    for i in range(t):
        for j in range(i):
            for f in permutations[i]:
                for g in permutations[j]:
                    assert all(f[g[x]] == g[f[x]] for x in range(len(cosets)))
    assert all(c == counts[0] for c in counts)
    assert len(Lam) == 128 and len(cosets) == 32
    assert counts[0] == Counter({8: 4})
    assert all(len({f[x] for f in actions}) == len(P)
               for actions in permutations for x in range(len(cosets)))
    lam = ((1, 0), (1, 0), ONE, ONE)
    h = ((0, 1), ONE, ONE, ONE)
    assert in_lambda(lam)
    assert not in_lambda(tmul(tmul(h, lam), tinv(h)))
    return dict(t=t, group_order=len(H), subgroup_order=len(Lam),
                quotient_size=len(cosets), direction_count=t, orbit_size=8,
                orbits_per_direction=4, all_cosets_well_defined=True,
                cross_direction_commutation=True, free_on_every_coset=True,
                nonnormality_witness=True)

def main():
    if not __debug__:
        raise SystemExit("Refusing optimized Python: these checks require assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
