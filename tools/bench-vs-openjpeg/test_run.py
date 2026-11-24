import struct
import unittest

from run import check_source, compare_dumps, read_dump, sha


def dump(width, height, values, signed=0):
    return struct.pack("<7Q", width, height, 1, width, height, 8, signed) + \
        struct.pack("<" + ("q" if signed else "Q") * len(values), *values)


class ComparisonTests(unittest.TestCase):
    def test_lossy_difference_statistics(self):
        result = compare_dumps(dump(2, 1, [5, 9]), dump(2, 1, [4, 12]))
        self.assertEqual((result["samples"], result["differing_samples"],
                          result["maximum_absolute_difference"]), (2, 2, 3))

    def test_signed_samples_are_not_unsigned_distances(self):
        result = compare_dumps(dump(1, 1, [-1], 1), dump(1, 1, [1], 1))
        self.assertEqual(result["maximum_absolute_difference"], 2)

    def test_incomplete_or_different_geometry_is_rejected(self):
        with self.assertRaises(ValueError):
            read_dump(dump(2, 1, [1]))
        with self.assertRaises(ValueError):
            compare_dumps(dump(2, 1, [1, 2]), dump(1, 2, [1, 2]))

    def test_equal_but_wrong_lossless_decoders_do_not_pass_source_oracle(self):
        case = dict(width=2, height=1, channels=1,
                    expected_lossless_samples_sha256=sha(bytes([1, 2])))
        check_source(dump(2, 1, [1, 2]), case)
        with self.assertRaises(ValueError):
            check_source(dump(2, 1, [0, 0]), case)


if __name__ == "__main__":
    unittest.main()
