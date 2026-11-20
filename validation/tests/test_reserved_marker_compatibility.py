import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import framework
import numerical


class ReservedMarkerCompatibilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.subject = framework.build_subject()
        cls.fixture = (framework.VALIDATION / "fixtures" / "hayro-reserved-marker"
                       / "codestream_reserved_marker.j2k").read_bytes()

    def decode(self, path):
        process, _, limited = framework._run_process_bounded(
            [str(self.subject), "decode", "raw", str(path)], 10.0,
            numerical.NATIVE_OUTPUT_BYTES,
            numerical._limit_native_process if framework.resource is not None else None,
        )
        self.assertFalse(limited)
        observation = framework.parse_subject_output(
            process.stdout, process.stderr, process.returncode,
        )
        self.assertFalse(observation.get("execution_failed", False))
        return observation

    def test_exact_reported_stream_and_entire_parameterless_range_decode_strictly(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "reserved.j2k"
            for marker in range(0x30, 0x40):
                with self.subTest(marker=marker):
                    data = bytearray(self.fixture)
                    data[60] = marker
                    path.write_bytes(data)
                    actual = self.decode(path)
                    self.assertTrue(actual["accepted"])
                    image = actual["image"]
                    self.assertEqual((image["width"], image["height"]), (128, 96))
                    self.assertEqual(len(image["components"]), 1)
                    component = image["components"][0]
                    self.assertEqual((component["precision"], component["signed"]), (8, False))
                    self.assertEqual(len(component["samples"]), 128 * 96)
                    self.assertEqual(
                        hashlib.sha256(bytes(component["samples"])).hexdigest(),
                        "b99f348fe8bd86f3bb26bad6217f37abfa5e182244dff74459b1bec27c1d8106",
                    )

    def test_adjacent_unknown_markers_and_truncated_prefix_remain_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "invalid.j2k"
            for marker in (0x2F, 0x40):
                data = bytearray(self.fixture)
                data[60] = marker
                path.write_bytes(data)
                self.assertFalse(self.decode(path)["accepted"])
            path.write_bytes(self.fixture[:60])
            self.assertFalse(self.decode(path)["accepted"])


if __name__ == "__main__":
    unittest.main()
