import struct
import unittest

from run import check_source, compare_dumps, read_dump, sha
from profile_baseline import parse_report


def dump(width, height, values, signed=0):
    return struct.pack("<7Q", width, height, 1, width, height, 8, signed) + \
        struct.pack("<" + ("q" if signed else "Q") * len(values), *values)


class ComparisonTests(unittest.TestCase):
    def test_perf_padding_and_extra_ipc_column_do_not_drop_samples(self):
        result = parse_report(
            "# Overhead;Symbol;IPC\n"
            " 11.36% ;[.] jpeg2000_decoder::mq::MqDecoder::decode ;- -\n"
            " 1.44%  ;[.] _ZN16jpeg2000_decoder9transform7rowwise9lift_rows ;- -\n"
        )
        self.assertEqual(result, {"MQ": 11.36, "DWT": 1.44})

    def test_component_transform_is_not_misclassified_as_wavelet_transform(self):
        result = parse_report(
            " 0.73% ;[.] jpeg2000_decoder::image::component_transform::inverse_component_values ;- -\n"
            " 2.00% ;[.] opj_idwt53_v ;- -\n"
        )
        self.assertEqual(result, {"MCT": 0.73, "DWT": 2.0})

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
