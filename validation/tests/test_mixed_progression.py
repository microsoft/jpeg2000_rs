"""Original issue #425 streams, compared against native OpenJPEG 2.5.4 planes."""

import os
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import framework
import numerical


FIXTURES = Path(__file__).resolve().parents[1] / "fixtures" / "hayro-mixed-progression"
ORDERS = ("cprl", "pcrl", "rpcl")


class MixedProgressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.subject = framework.build_subject()
        cls.reference = [
            framework.parse_pgx(FIXTURES / f"reference_{component}.pgx")["image"]["components"][0]
            for component in range(3)
        ]

    def test_strict_original_streams_match_every_reference_sample(self):
        for order in ORDERS:
            with self.subTest(order=order):
                process, _ = numerical._run_checked([
                    str(self.subject), "decode", "raw",
                    str(FIXTURES / f"packets_mixed_levels_{order}.j2k"),
                ], 30.0)
                decoded = framework.parse_subject_output(
                    process.stdout, process.stderr, process.returncode,
                )
                self.assertTrue(decoded["accepted"], decoded)
                self.assertEqual((decoded["image"]["width"], decoded["image"]["height"]), (128, 96))
                self.assertEqual(decoded["image"]["components"], self.reference)

    def test_original_streams_still_obey_work_limits(self):
        for order in ORDERS:
            with self.subTest(order=order):
                process, _, limited = framework._run_process_bounded([
                    str(self.subject), "decode-limited", "raw",
                    str(FIXTURES / f"packets_mixed_levels_{order}.j2k"),
                    "work-units", "1",
                ], 30.0, 16384, None)
                self.assertFalse(limited)
                self.assertEqual(framework.parse_subject_output(
                    process.stdout, process.stderr, process.returncode,
                ), {"accepted": False, "category": "LimitExceeded"})
                self.assertIn(b"WorkUnits", process.stdout)

    def test_truncated_original_stream_is_not_recovered_in_strict_mode(self):
        work = framework.RESULTS_DIR / f"mixed-progression-{os.getpid()}"
        work.mkdir(parents=True, exist_ok=False)
        damaged = work / "truncated.j2k"
        try:
            data = (FIXTURES / "packets_mixed_levels_pcrl.j2k").read_bytes()
            damaged.write_bytes(data[:-3])
            process, _, limited = framework._run_process_bounded([
                str(self.subject), "decode", "raw", str(damaged),
            ], 30.0, 16384, None)
            self.assertFalse(limited)
            result = framework.parse_subject_output(
                process.stdout, process.stderr, process.returncode,
            )
            self.assertFalse(result["accepted"], result)
            self.assertFalse(result.get("execution_failed", False), result)
        finally:
            damaged.unlink(missing_ok=True)
            work.rmdir()


if __name__ == "__main__":
    unittest.main()
