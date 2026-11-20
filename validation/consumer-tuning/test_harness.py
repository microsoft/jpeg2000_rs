import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import sys
import unittest
import uuid

from generate_fixtures import ROOT, coding_metadata, generate, jp2_parts, samples, sha
from measure import measure
from run import check_outcome, configuration_environment
from summarize import geometric, interval, summarize

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

    def test_prepare_frozen_inputs_without_any_native_encoder(self):
        scratch = ROOT / "target/consumer-tuning/tests"
        scratch.mkdir(parents=True, exist_ok=True)
        directory = scratch / uuid.uuid4().hex
        directory.mkdir()
        try:
            generate(None, directory)
            self.assertEqual(sha((directory / "manifest.json").read_bytes()),
                             "5c33c9699031796f293e4cb5357c56748367793cbd21c59e7ddaba219069c954")
            for fixture in json.loads((directory / "manifest.json").read_text())["fixtures"]:
                self.assertEqual(sha((directory / fixture["path"]).read_bytes()), fixture["sha256"])
            self.assertFalse((directory / "native-reencode").exists())
        finally:
            shutil.rmtree(directory)

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

    def test_build_rss_includes_children_spawned_by_worker_threads(self):
        scratch = ROOT / "target/consumer-tuning/tests"
        scratch.mkdir(parents=True, exist_ok=True)
        directory = scratch / uuid.uuid4().hex
        directory.mkdir()
        try:
            child = "import time; data=bytearray(48*1024*1024); time.sleep(0.3)"
            parent = ("import subprocess,sys,threading; "
                      f"thread=threading.Thread(target=lambda:subprocess.run([sys.executable,'-c',{child!r}])); "
                      "thread.start(); thread.join()")
            measured = measure([sys.executable, "-c", parent], directory / "tree", sample_tree=True)
            self.assertEqual(measured["returncode"], 0)
            self.assertGreater(measured["sampled_tree_rss_kib"], 48 * 1024)
        finally:
            shutil.rmtree(directory)

    def test_ratio_summary_keeps_direction_and_uncertainty(self):
        self.assertAlmostEqual(geometric([0.5, 2]), 1)
        for bound in interval([0.9, 0.9]):
            self.assertAlmostEqual(bound, 0.9)
        low, high = interval([0.8, 1.2])
        self.assertLess(low, 1)
        self.assertGreater(high, 1)

    def test_summary_retains_matched_pairs_instead_of_pooling_iterations(self):
        scratch = ROOT / "target/consumer-tuning/tests"
        scratch.mkdir(parents=True, exist_ok=True)
        directory = scratch / uuid.uuid4().hex
        directory.mkdir()
        try:
            (directory / "fixture-manifest.json").write_text(json.dumps({
                "fixtures": [{"id": "test", "group": "generated-1024"}]}))
            (directory / "builds.jsonl").write_text("")
            rows = []
            for backend in ["current", "release022", "hayro-scalar"]:
                for tuned in ["cpu", "thinlto", "cgu1", "combined"]:
                    for pair in range(2):
                        baseline = 50 if backend == "hayro-scalar" else 100
                        baseline *= 10 ** pair
                        for config in ["generic", tuned]:
                            rows.append({
                                "backend": backend, "tuned": tuned, "config": config,
                                "fixture": "test", "pair": pair,
                                "decode_ns": [baseline if config == "generic" else baseline * 0.9] * 5,
                                "metrics": {"max_process_rss_kib": 100},
                            })
            (directory / "samples.jsonl").write_text("\n".join(map(json.dumps, rows)) + "\n")
            with contextlib.redirect_stdout(io.StringIO()):
                result = summarize(directory)
            for cohort in result["cohort"]:
                self.assertEqual(cohort["pairs"], 2)
                self.assertAlmostEqual(cohort["decode_reduction_percent"], 10)
            for comparison in result["comparator"]:
                self.assertAlmostEqual(comparison["current_over_hayro_scalar_geomean"], 2)
            for row in rows:
                if row["backend"] == "hayro-scalar" and row["config"] == "cpu" and row["pair"] == 0:
                    row["matches_backend_generic"] = False
            (directory / "samples.jsonl").write_text("\n".join(map(json.dumps, rows)) + "\n")
            with contextlib.redirect_stdout(io.StringIO()):
                changed = summarize(directory)
            cpu = next(row for row in changed["cohort"]
                       if row["backend"] == "hayro-scalar" and row["config"] == "cpu")
            self.assertFalse(cpu["output_invariant_qualified"])
            self.assertIsNone(cpu["decode_reduction_percent"])
            self.assertAlmostEqual(cpu["raw_decode_time_change_percent"], 10)
            comparator = next(row for row in changed["comparator"] if row["config"] == "cpu")
            self.assertIsNone(comparator["current_over_hayro_scalar_geomean"])
            self.assertEqual(comparator["unqualified_fixtures"], ["test"])
        finally:
            shutil.rmtree(directory)


if __name__ == "__main__":
    unittest.main()
