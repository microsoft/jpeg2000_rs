import copy
import json
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import framework
import hayro_comparison as comparison
import numerical


class HayroComparisonTests(unittest.TestCase):
    def setUp(self):
        root = framework.RESULTS_DIR / "test-work"
        root.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(dir=root)
        self.addCleanup(self.directory.cleanup)
        self.work = Path(self.directory.name)
        self.layout = {"width": 2, "height": 1, "components": [{
            "width": 2, "height": 1, "precision": 8, "signed": False,
        }]}
        self.values = [0, 255]
        self.samples = self.work / "output.i64le"
        self.samples.write_bytes(struct.pack("<2q", *self.values))
        self.observation = {
            "schema_version": 1, "engine": "ours", "hayro_version": "0.4.1",
            "hayro_features": "published-defaults", "lifecycle": "test fresh context",
            "status": "decoded", "decoder_accepted": True, "unsupported": False,
            "layout": self.layout, "sample_count": 2,
            "output_sha256": comparison.canonical_digest(self.layout, self.values),
            "timings": [{"decode_ns": 100, "common_output_ns": 200}], "error": None,
        }
        self.expected = {"accepted": True, "image": {"width": 2, "height": 1, "components": [{
            **self.layout["components"][0], "sample_kind": "unsigned", "samples": self.values,
        }]}}

    def test_canonical_observation_binds_real_samples_and_layout(self):
        actual = comparison.read_observation(self.observation, self.samples, 1)
        self.assertEqual(actual, self.expected)
        for invalid in (struct.pack("<q", 0), struct.pack("<2q", 0, 254)):
            self.samples.write_bytes(invalid)
            with self.assertRaises(ValueError):
                comparison.read_observation(self.observation, self.samples, 1)

    def test_unmeasured_wrong_version_or_inconsistent_observations_fail(self):
        for change in ("version", "accepted", "hash", "sample-count", "time", "time-order", "layout"):
            value = copy.deepcopy(self.observation)
            if change == "version":
                value["hayro_version"] = "0.4.0"
            elif change == "accepted":
                value["decoder_accepted"] = False
            elif change == "hash":
                value["output_sha256"] = None
            elif change == "sample-count":
                value["sample_count"] = 3
            elif change == "time":
                value["timings"] = []
            elif change == "time-order":
                value["timings"][0]["decode_ns"] = 300
            else:
                value["layout"]["width"] = True
            with self.subTest(change=change), self.assertRaises(ValueError):
                comparison.read_observation(value, self.samples, 1)
        with self.assertRaises(ValueError):
            comparison.read_observation(self.observation, self.samples, 2)

    def test_rejections_are_not_decodes_and_schema_requires_the_error(self):
        rejected = dict(self.observation, status="rejected", decoder_accepted=False,
                        unsupported=True, layout=None, sample_count=0, output_sha256=None,
                        timings=[], error="unsupported marker")
        comparison.validate_observation(rejected)
        with self.assertRaises(ValueError):
            comparison.read_observation(rejected, self.samples, 1)
        rejected["error"] = None
        with self.assertRaises(ValueError):
            comparison.validate_observation(rejected)

    def test_only_qualified_outputs_can_enter_performance_measurements(self):
        def process(command, *args):
            Path(command[4]).write_text("4\n")
            Path(command[-2]).write_bytes(self.samples.read_bytes())
            return subprocess.CompletedProcess(command, 0, json.dumps(self.observation).encode(), b""), 2.0, False

        build = {"path": "/test/build-default/release/comparison", "sha256": "0" * 64,
                 "hayro_features": "published-defaults"}
        case = numerical.NumericalCase("fixture", width=2, height=1)
        with mock.patch.object(framework, "_run_process_bounded", side_effect=process):
            result = comparison._run_adapter(build, "ours", "raw", self.samples, self.work,
                                              1, self.expected, case, "time")
            self.assertEqual(result["status"], "qualified")
            self.assertEqual(result["peak_rss_bytes"], 4096)
            wrong = copy.deepcopy(self.expected)
            wrong["image"]["components"][0]["samples"][1] = 254
            result = comparison._run_adapter(build, "ours", "raw", self.samples, self.work,
                                              1, wrong, case, "time")
            self.assertEqual(result["status"], "numerical-disagreement")
            self.assertEqual(result["reference_metrics"]["maximum_error"], 1)
            self.observation["engine"] = "hayro"
            with self.assertRaisesRegex(ValueError, "wrong engine"):
                comparison._run_adapter(build, "ours", "raw", self.samples, self.work,
                                        1, self.expected, case, "time")
            self.observation["engine"] = "ours"
            self.observation["hayro_features"] = "std-only"
            with self.assertRaisesRegex(ValueError, "build features"):
                comparison._run_adapter(build, "ours", "raw", self.samples, self.work,
                                        1, self.expected, case, "time")

    def test_default_missing_tools_block_without_build_and_configured_missing_fails(self):
        with mock.patch.object(shutil, "which", return_value=None), \
                mock.patch.object(comparison, "build_adapters") as build, \
                mock.patch.dict(comparison.os.environ, {
                    "OPENJPEG_ENCODER": "", "OPENJPEG_DECODER": "",
                    "OPENJPH_ENCODER": "", "OPENJPH_DECODER": "", "JPEG2000_TIME": "",
                }):
            result = comparison.run_comparison(self.work)
            self.assertEqual(result["status"], "blocked")
            self.assertFalse(result["baseline_passed"])
            summary = (self.work / "hayro-comparison.md").read_text()
            self.assertIn("**blocked**", summary)
            self.assertIn("## Blockers", summary)
            self.assertNotIn("## Performance", summary)
            invalid = dict(result, status="completed", baseline_passed=True, blockers=[])
            with self.assertRaisesRegex(ValueError, "summary"):
                framework.validate_schema(comparison.SCHEMA, invalid)
            build.assert_not_called()
            with mock.patch.dict(comparison.os.environ, {"JPEG2000_TIME": "missing-time-tool"}):
                with self.assertRaises(FileNotFoundError):
                    comparison.run_comparison(self.work)

    def test_summary_keeps_ratios_disagreements_and_unqualified_cases_distinct(self):
        result = {
            "status": "completed", "baseline_passed": True,
            "provenance": {"git_commit": "1" * 40, "git_dirty": False},
            "environment": {"system": "test host", "cpu_model": "test CPU", "rustc": "rustc test"},
            "reference": {"checksum": comparison.HAYRO_CHECKSUM},
            "repetitions": 3, "iterations": 5, "blockers": [], "errors": [],
            "performance": [{
                "id": "qualified-lossy", "performance": {
                    "ours": {"common_output_median_ms": 10, "peak_rss_bytes": 2**20},
                    "hayro-default": {"common_output_median_ms": 5, "peak_rss_bytes": 2**19,
                                      "ours_over_hayro_time_ratio": 2, "exact_output_match": False},
                },
            }, {"id": "unsupported-ht", "performance": {
                "ours": {"common_output_median_ms": 8, "peak_rss_bytes": 2**20},
            }}],
            "summary": {"corpus_cases": 17, "capability_cases": 53, "ours_qualified": 53,
                        "hayro_default_qualified": 23, "hayro_default_unsupported": 30,
                        "hayro_scalar_qualified": 23},
            "corpus": [{"id": "policy-difference", "expected": "reject", "engines": {
                "ours": {"status": "rejected"},
                "hayro-default": {"status": "accepted-without-reference"},
            }}],
        }
        destination = self.work / "summary.md"
        comparison.write_summary(destination, result)
        text = destination.read_text()
        self.assertIn("| qualified-lossy | 10.00 | 5.00 | N/A | 2.00 | 1.00 | 0.50 | False |", text)
        self.assertIn("| unsupported-ht | 8.00 | N/A | N/A | N/A | 1.00 | N/A | not comparable |", text)
        self.assertIn("Default acceptance-policy difference: `policy-difference`", text)
        self.assertIn("not an unbiased feature-support percentage", text)
        result["status"] = "failed"
        result["baseline_passed"] = False
        result["errors"] = ["our baseline changed"]
        result["performance"][0]["performance"]["hayro-default"] = {"runs": []}
        comparison.write_summary(destination, result)
        text = destination.read_text()
        self.assertIn("## Errors\n\n- our baseline changed", text)
        self.assertIn("| qualified-lossy | 10.00 | N/A | N/A | N/A |", text)

    def test_invalid_iteration_counts_fail_before_execution(self):
        for iterations, repetitions in ((0, 1), (101, 1), (True, 1), (1, 0), (1, 11), (1, True)):
            with self.subTest(iterations=iterations, repetitions=repetitions), self.assertRaises(ValueError):
                comparison.run_comparison(self.work, iterations, repetitions)
