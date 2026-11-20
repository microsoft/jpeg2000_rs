import json
import os
from pathlib import Path
import shutil
import sys
import unittest
import uuid

from generate_fixtures import ROOT, coding_metadata, jp2_parts, samples, sha
from measure import measure
from run import check_outcome, configuration_environment
from summarize import geometric, interval

HERE = Path(__file__).resolve().parent


class FixtureTests(unittest.TestCase):
    def test_integer_source_hashes(self):
        expected = json.loads((HERE / "cohort-v1.json").read_text())
        for source in expected["sources"]:
            self.assertEqual(sha(samples(source["channels"], source["pattern"] == "noisy")),
                             source["samples_sha256"])

    def test_generated_cohort_exact_bytes_and_metadata(self):
        generated = ROOT / "target/consumer-tuning/fixtures/manifest.json"
        if not generated.exists():
            self.skipTest("generate fixtures before byte identity test")
        expected = json.loads((HERE / "cohort-v1.json").read_text())
        actual = json.loads(generated.read_text())
        self.assertEqual(actual, expected)
        for fixture in actual["fixtures"]:
            data = (generated.parent / fixture["path"]).read_bytes()
            self.assertEqual(sha(data), fixture["sha256"])
            if fixture["group"] == "generated-1024":
                raw = jp2_parts(data)[0] if fixture["format"] == "jp2" else data
                self.assertEqual(coding_metadata(raw), fixture["coding"])
                self.assertEqual(sha(raw), fixture["codestream_sha256"])

    def test_bad_source_or_shape_is_not_accepted(self):
        fixture = {"id": "test", "group": "generated-1024", "width": 1, "height": 1,
                   "channels": 1, "expected_lossless_samples_sha256": "expected"}
        with self.assertRaises(ValueError):
            check_outcome("hayro-scalar", fixture, {"status": "ok"})
        with self.assertRaises(ValueError):
            check_outcome("current", fixture, {"samples_sha256_u8_interleaved": "expected"})
        check_outcome("current", fixture, {"width": 1, "height": 1, "channels": 1,
                                          "samples_sha256_u8_interleaved": "expected"})


class MeasurementTests(unittest.TestCase):
    def test_failure_retains_raw_process_evidence(self):
        scratch = ROOT / "target/consumer-tuning/tests"
        scratch.mkdir(parents=True, exist_ok=True)
        directory = scratch / uuid.uuid4().hex
        directory.mkdir()
        try:
            prefix = directory / "process"
            measured = measure([sys.executable, "-c", "print('retained'); raise SystemExit(7)"], prefix)
            self.assertEqual(measured["returncode"], 7)
            self.assertEqual(measured["exit"], 7)
            self.assertIn("retained", Path(str(prefix) + ".stdout").read_text())
            self.assertGreater(measured["max_process_rss_kib"], 0)
            with self.assertRaises(FileExistsError):
                measure(["true"], prefix)
        finally:
            shutil.rmtree(directory)

    def test_one_factor_configurations(self):
        generic = configuration_environment("generic", Path("build"), Path("calls"))
        for name, changed in [("cpu", "RUSTFLAGS"), ("thinlto", "CARGO_PROFILE_RELEASE_LTO"),
                              ("cgu1", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS")]:
            env = configuration_environment(name, Path("build"), Path("calls"))
            self.assertEqual([key for key in generic if generic[key] != env[key]], [changed])

    def test_compiler_wrapper_preserves_jobserver_fds(self):
        scratch = ROOT / "target/consumer-tuning/tests"
        scratch.mkdir(parents=True, exist_ok=True)
        directory = scratch / uuid.uuid4().hex
        directory.mkdir()
        read_fd, write_fd = os.pipe()
        try:
            env = dict(os.environ, CARGO_MAKEFLAGS=f"--jobserver-auth={read_fd},{write_fd}")
            command = [sys.executable, "-c", f"import os; os.fstat({read_fd}); os.fstat({write_fd})"]
            measured = measure(command, directory / "fd", env=env, preserve_jobserver=True)
            self.assertEqual(measured["returncode"], 0)
        finally:
            os.close(read_fd)
            os.close(write_fd)
            shutil.rmtree(directory)

    def test_ratio_summary_keeps_direction_and_uncertainty(self):
        self.assertAlmostEqual(geometric([0.5, 2]), 1)
        self.assertEqual(interval([0.9, 0.9]), [0.9, 0.9])
        low, high = interval([0.8, 1.2])
        self.assertLess(low, 1)
        self.assertGreater(high, 1)


if __name__ == "__main__":
    unittest.main()
