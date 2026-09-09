"""Small exact checks of the metric used by the theorem's quantum tester.

Enumerates one-row commuting CSS matrices, not large qLTC constructions.
"""
from itertools import product
import unittest

from experiments.check_t4_chains import rank
from experiments.check_parameters import check


def syndrome(rows, vector):
    return sum(((row & vector).bit_count() % 2) << i for i, row in enumerate(rows))


class MetricTests(unittest.TestCase):
    def test_minimum_filling_equals_distance_to_kernel(self):
        for width in range(1, 4):
            for count in range(4):
                for rows in product(range(1 << width), repeat=count):
                    kernel = [v for v in range(1 << width) if syndrome(rows, v) == 0]
                    fillings = {}
                    for v in range(1 << width):
                        s = syndrome(rows, v)
                        fillings[s] = min(fillings.get(s, width + 1), v.bit_count())
                    for v in range(1 << width):
                        distance = min((v ^ k).bit_count() for k in kernel)
                        self.assertEqual(fillings[syndrome(rows, v)], distance)
                    self.assertEqual(len(fillings), 1 << rank(rows))

    def test_css_centralizer_union_weight_bounds(self):
        for width in range(1, 5):
            words = range(1 << width)
            for hx, hz in product(words, repeat=2):
                if (hx & hz).bit_count() % 2:
                    continue
                ker_x = [x for x in words if (hz & x).bit_count() % 2 == 0]
                ker_z = [z for z in words if (hx & z).bit_count() % 2 == 0]
                dx = [min((x ^ k).bit_count() for k in ker_x) for x in words]
                dz = [min((z ^ k).bit_count() for k in ker_z) for z in words]
                minimum = {}
                for x, z in product(words, repeat=2):
                    s = ((hz & x).bit_count() % 2, (hx & z).bit_count() % 2)
                    minimum[s] = min(minimum.get(s, width + 1), (x | z).bit_count())
                for x, z in product(words, repeat=2):
                    s = ((hz & x).bit_count() % 2, (hx & z).bit_count() % 2)
                    distance = minimum[s]
                    self.assertLessEqual(max(dx[x], dz[z]), distance)
                    self.assertLessEqual(distance, dx[x] + dz[z])
                    # A single parity equation has exact sector constant one.
                    self.assertGreaterEqual(sum(s), distance)

    def test_displayed_parameter_substitutions(self):
        self.assertEqual(check()["beta"], "47551/65536")


if __name__ == "__main__":
    unittest.main()
