"""Bounded independent checks of the GF(2) routines and finite group laws."""
from itertools import product
import unittest

from experiments.check_t4_chains import rank, null_basis, build_complex, quotient
from experiments.semidirect_sanity import P, ONE, act, mul, inv, tmul, audit


def span(vectors):
    """Independent exhaustive span construction, deliberately not elimination."""
    result = {0}
    for vector in vectors:
        result |= {x ^ vector for x in tuple(result)}
    return result


class BinaryAlgebraTests(unittest.TestCase):
    def test_rank_matches_exhaustive_span(self):
        for width in range(4):
            for count in range(4):
                for rows in product(range(1 << width), repeat=count):
                    self.assertEqual(1 << rank(rows), len(span(rows)), (width, rows))

    def test_null_basis_matches_exhaustive_kernel(self):
        for width in range(4):
            for count in range(4):
                for rows in product(range(1 << width), repeat=count):
                    matrix = [[(row >> j) & 1 for j in range(width)] for row in rows]
                    basis = null_basis(matrix, width)
                    encoded = [sum(v << j for j, v in enumerate(row)) for row in basis]
                    kernel = {v for v in range(1 << width)
                              if all((v & row).bit_count() % 2 == 0 for row in rows)}
                    self.assertEqual(span(encoded), kernel)
                    self.assertEqual(len(basis), width - rank(rows))

    def test_rank_rejects_negative_column(self):
        with self.assertRaises(ValueError):
            rank([-1])

    def test_null_basis_rejects_ragged_input(self):
        with self.assertRaises(ValueError):
            null_basis([[1, 0], [1]], 2)

    def test_null_basis_rejects_nonbinary_input(self):
        with self.assertRaises(ValueError):
            null_basis([[1, 2]], 2)

    def test_null_basis_rejects_negative_degree(self):
        with self.assertRaises(ValueError):
            null_basis([], -1)


class GroupTests(unittest.TestCase):
    def test_associativity(self):
        for x, y, z in product(P, repeat=3):
            self.assertEqual(mul(mul(x, y), z), mul(x, mul(y, z)))

    def test_identity_and_inverse(self):
        for x in P:
            self.assertEqual(mul(ONE, x), x)
            self.assertEqual(mul(x, ONE), x)
            self.assertEqual(mul(x, inv(x)), ONE)
            self.assertEqual(mul(inv(x), x), ONE)

    def test_action_respects_addition(self):
        for g, a, b in product(range(2), range(4), range(4)):
            self.assertEqual(act(g, a ^ b), act(g, a) ^ act(g, b))

    def test_direct_product_length_check(self):
        with self.assertRaises(ValueError):
            tmul((ONE,), (ONE, ONE))

    def test_public_geometry_scope_is_t4(self):
        with self.assertRaises(ValueError):
            audit(3)

    def test_quotient_enumerates_every_group_element(self):
        reps, lookup = quotient()
        self.assertEqual(len(reps), 32)
        self.assertEqual(len(lookup), 8**4)
        self.assertEqual(set(lookup.values()), set(range(32)))


class ConstructorInputTests(unittest.TestCase):
    def test_constructor_rejects_missing_direction(self):
        with self.assertRaises(ValueError):
            build_complex([(0, 1)], [[[1]]] * 3, 0, [], {})

    def test_constructor_rejects_out_of_range_shift(self):
        with self.assertRaises(ValueError):
            build_complex([(0, 1)], [[[1]]] * 4, 16, [], {})

    def test_constructor_rejects_repeated_generator(self):
        with self.assertRaises(ValueError):
            build_complex([(0, 1), (0, 1)], [[[1, 1]]] * 4, 0, [], {})


if __name__ == "__main__":
    unittest.main()
