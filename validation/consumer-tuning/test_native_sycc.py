import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import native_sycc as sycc


CHILD = """
import sys
operation, fixture, iterations, discard, *roi = sys.argv[1:]
if operation.endswith('-dump'):
    print(':'.join((operation, iterations, discard, *roi)))
elif iterations != '32':
    raise SystemExit('incorrect fixed work')
"""


class RequestedSyccTests(unittest.TestCase):
    def setUp(self):
        parent = sycc.native.ROOT / "target"
        parent.mkdir(exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix="test-sycc-", dir=parent)
        self.addCleanup(temp.cleanup)
        self.evidence = Path(temp.name)
        self.cohort = sycc.fixtures(self.evidence)

    def controls(self):
        # Exercise a generic conversion (not a native-off control), an eligible
        # conversion, and both matching native controls, through a real child.
        ids = {"444:requested-sycc", "444:native-off", "crg-crop-reduce1:requested-sycc",
               "crg-crop-reduce1:native-off"}
        return [case for case in self.cohort if case["id"] in ids]

    def fake_children(self, cohort, *, wrong=None):
        for case in cohort:
            op = "color-dump" if case["mode"] == "requested-sycc" else "native-dump"
            expected = ":".join([op, "1", str(case["discard"]), *map(str, case["roi"] or [])]) + "\n"
            if case["id"] == wrong:
                expected = expected.replace("color-dump", "native-dump")
            case["expected"] = {"bytes": len(expected), "sha256": sycc.native.sha(expected.encode())}
        return {side: sys.executable for side in sycc.native.BACKENDS}

    def test_actual_child_dispatches_generic_and_planned_conversion_separately_from_native(self):
        cases = self.controls()
        binaries = self.fake_children(cases)
        got = self.qualify(binaries, cases)
        routes = {row["case"]: row["expected_route"] for row in got}
        self.assertEqual(routes, {
            "444:requested-sycc": "generic-fallback", "444:native-off": "native-off",
            "crg-crop-reduce1:requested-sycc": "row-plan", "crg-crop-reduce1:native-off": "native-off",
        })
        base = self.evidence / "qualification"
        self.assertEqual((base / "crg-crop-reduce1/requested-sycc/baseline.stdout").read_text(),
                         "color-dump:1:1:15:21:99:65\n")
        self.assertEqual((base / "crg-crop-reduce1/native-off/candidate.stdout").read_text(),
                         "native-dump:1:1:15:21:99:65\n")

    def prepare_command(self, pinned, binary, case, evidence, *, dump):
        argv = self.real_command(pinned, binary, case, evidence, dump=dump)
        return [argv[0], "-c", CHILD, *argv[1:]]

    def qualify(self, binaries, cases):
        self.real_command = sycc.command
        with patch.object(sycc, "command", side_effect=self.prepare_command):
            return sycc.qualify(binaries, cases, self.evidence, [], None)

    def test_non_oracle_output_is_rejected_even_if_both_binaries_agree(self):
        cases = self.controls()
        binaries = self.fake_children(cases, wrong="444:requested-sycc")
        with self.assertRaisesRegex(ValueError, "frozen oracle mismatch: 444:requested-sycc"):
            self.qualify(binaries, cases)
        self.assertFalse((self.evidence / "samples.jsonl").exists())

    def test_runs_balanced_fixed_work_and_pairs_exact_case_keys(self):
        cases = self.controls()
        binaries = self.fake_children(cases)
        qualified = self.qualify(binaries, cases)

        def controlled(argv, prefix, *, env, seconds):
            prefix.parent.mkdir(parents=True, exist_ok=True)
            # Test the real timing traversal, not the host clock.
            with prefix.with_suffix(".stdout").open("xb") as stdout, \
                    prefix.with_suffix(".stderr").open("xb") as stderr:
                subprocess.run(argv, stdout=stdout, stderr=stderr, env=env, timeout=seconds, check=True)
            self.assertEqual(argv[5], "32")
            self.assertTrue(argv[3].endswith("-run"))
            wall = 640 if prefix.name == "baseline" else 320
            return {"wall_ns": wall, "user_s": 0.1, "system_s": 0.0, "max_process_rss_kib": 42,
                    "voluntary_context_switches": 2, "involuntary_context_switches": 3, "command": argv}

        with patch.object(sycc, "command", side_effect=self.prepare_command), \
                patch.object(sycc.native, "checked", side_effect=controlled) as launch:
            with self.assertRaisesRegex(ValueError, "preflights"):
                sycc.pair(binaries, cases, qualified[:-1], self.evidence, [], None, 2)
            launch.assert_not_called()
            rows = sycc.pair(binaries, cases, qualified, self.evidence, [], None, 2)
        self.assertEqual(len(rows), 16)
        persisted = [json.loads(line) for line in (self.evidence / "samples.jsonl").read_text().splitlines()]
        self.assertEqual(rows, persisted)
        for case in cases:
            matching = [row for row in rows if row["case"] == case["id"]]
            self.assertEqual([(r["pair"], r["backend"], r["position"]) for r in matching],
                             [(0, "baseline", 0), (0, "candidate", 1),
                              (1, "candidate", 0), (1, "baseline", 1)])
        for result in sycc.summaries(rows, cases, 2):
            self.assertEqual(result["baseline_over_candidate"], 2)
            self.assertEqual(result["per_backend"]["candidate"]["p99_process_mean_ns"], 10)
            self.assertEqual(result["per_backend"]["baseline"]["median_voluntary_context_switches"], 2)

    def test_preflight_and_timing_emit_upload_portable_paths_with_original_case_ids(self):
        cases = self.controls()
        binaries = self.fake_children(cases)
        qualified = self.qualify(binaries, cases)
        with patch.object(sycc, "command", side_effect=self.prepare_command):
            sycc.pair(binaries, cases, qualified, self.evidence, [], None, 2)

        rejected = set('":<>|*?\r\n')
        for path in self.evidence.rglob("*"):
            relative = path.relative_to(self.evidence)
            self.assertTrue(all(not rejected.intersection(part) for part in relative.parts), relative)

        preflights = [json.loads(line) for line in
                      (self.evidence / "qualification.jsonl").read_text().splitlines()]
        samples = [json.loads(line) for line in
                   (self.evidence / "samples.jsonl").read_text().splitlines()]
        self.assertEqual({row["case"]: (row["mode"], row["expected_route"]) for row in preflights}, {
            "444:requested-sycc": ("requested-sycc", "generic-fallback"),
            "444:native-off": ("native-off", "native-off"),
            "crg-crop-reduce1:requested-sycc": ("requested-sycc", "row-plan"),
            "crg-crop-reduce1:native-off": ("native-off", "native-off"),
        })
        self.assertEqual(
            {(row["case"], row["mode"], row["pair"], row["backend"]) for row in samples},
            {(case["id"], case["mode"], index, label) for case in cases
             for index in range(2) for label in sycc.native.BACKENDS},
        )
        self.assertEqual(len(list((self.evidence / "processes").rglob("*.metrics.json"))), len(samples))

    def check_integrated_pair_binding(self):
        baseline = "f4b2b7b29d38fa31bd74263913462bb67d6e5e4e"
        candidate = "590ca79a111f701308665038a83915434d551e80"
        options = SimpleNamespace(
            baseline=baseline, candidate=candidate, pairs=8, arch=sycc.native.platform.machine(),
            output=self.evidence / "integrated", qualify_only=True,
        )
        tool = {"command": [sys.executable], "returncode": 0}
        with patch.object(sycc.native, "reject_cargo_configs"), \
                patch.object(sycc.native, "clean_source"), \
                patch.object(sycc.native, "checked"), \
                patch.object(sycc.native, "text", return_value=sycc.native.UPSTREAM), \
                patch.object(sycc.native, "pinned_tool", return_value=tool), \
                patch.object(sycc.native, "native_affinity", return_value=([0], [])), \
                patch.object(sycc, "capture", return_value={}), \
                patch.object(sycc.native, "sources") as sources, \
                patch.object(sycc.native, "build", side_effect=lambda label, *a, **k: label), \
                patch.object(sycc, "qualify") as qualify:
            sycc.run(options)
        evidence = options.output / "evidence"
        sources.assert_called_once_with(
            {"baseline": baseline, "candidate": candidate}, options.output, evidence,
        )
        self.assertEqual(json.loads((evidence / "metadata.json").read_text())["revisions"],
                         {"baseline": baseline, "candidate": candidate})
        self.assertEqual(len(qualify.call_args.args[1]), 28)
        options.candidate = "1" * 40
        options.output = self.evidence / "unlisted"
        with patch.object(sycc.native, "sources") as sources, \
                self.assertRaisesRegex(ValueError, "frozen #480"):
            sycc.run(options)
        sources.assert_not_called()
        self.assertFalse(options.output.exists())

    def test_run_binds_integrated_pair_and_rejects_unlisted_pair_before_sources(self):
        self.check_integrated_pair_binding()

    def test_integrated_pair_binding_on_other_native_architecture(self):
        arch = next(name for name in sycc.native.ARCH if name != sycc.native.platform.machine())
        with patch.object(sycc.native.platform, "machine", return_value=arch), \
                patch.dict(os.environ, {"RUNNER_ARCH": sycc.native.ARCH[arch][1]}):
            self.check_integrated_pair_binding()
