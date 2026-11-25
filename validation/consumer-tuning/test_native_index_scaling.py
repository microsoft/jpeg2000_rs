import json
import os
from pathlib import Path
import random
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import native_index_scaling as scaling


CHILD = """
import sys
from pathlib import Path
from native_index_scaling import expected
side, operation, mode, path, pgm = sys.argv[1:]
if operation == 'preflight':
    out = expected(mode)
    if side == 'wrong':
        out = out.replace(b'Unsigned([64,', b'Unsigned([65,')
    if side == 'cdef':
        out = out.replace(b'channel_definitions: []', b'channel_definitions: [wrong]')
    sys.stdout.buffer.write(out)
elif operation == 'bench-fixed':
    k = int(Path(path).stem.split('-')[0][1:])
    scale = k * (2 if side == 'baseline' else 1)
    print('CONFIG\\t3\\t1\\t7')
    for value in (scale * 100, scale * 200, scale * 300):
        print(f'SAMPLE\\t{value}')
    print(f'LIFECYCLE\\t6\\t{2 if side == "short" else 3}')
else:
    sys.exit('unexpected operation')
"""


class IndexScalingTests(unittest.TestCase):
    def setUp(self):
        target = scaling.native.ROOT / "target"
        target.mkdir(exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix="test-native-index-scaling-", dir=target)
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.evidence = self.root / "evidence"
        self.evidence.mkdir()
        self.fixtures = scaling.stage_inputs(self.evidence)
        self.command = scaling.command
        self.env = {"PYTHONPATH": str(scaling.native.HERE), "PYTHONDONTWRITEBYTECODE": "1"}
        self.binaries = dict(zip(scaling.native.BACKENDS, scaling.native.BACKENDS, strict=True))

    def child_argv(self, pinned, binary, operation, case, evidence, fixtures):
        args = self.command(pinned, binary, operation, case, evidence, fixtures)
        return [sys.executable, "-c", CHILD, *args]

    def test_exact_nonconstant_inputs_actual_parts_and_per_tile_order(self):
        self.assertEqual(len(self.fixtures), 12)
        pgm = (self.evidence / "fixtures/seeded32.pgm").read_bytes()
        self.assertEqual(pgm, b"P5\n32 32\n255\n" + bytes(scaling.source_pixels()))
        self.assertEqual(len(set(pgm[13:])), 249)
        for k in scaling.GRID:
            facts = []
            for order in scaling.ORDERS:
                row = self.fixtures[f"k{k:04d}-{order}"]
                data = (self.evidence / "fixtures" / row["path"]).read_bytes()
                prefix, sequence, groups = scaling.part_groups(data, k)
                self.assertEqual(len(sequence), row["P"])
                self.assertTrue(all(len(parts) == 3 for parts in groups.values()))
                self.assertEqual(sequence[:3], ([(0, 0), (0, 1), (0, 2)] if order == "grouped"
                                               else [(t % k, t // k) for t in range(3)]))
                facts.append((prefix, groups))
            self.assertEqual(*facts)
        self.assertIn(f"Unsigned({scaling.source_pixels()[-1:]})".encode(), scaling.expected("roi"))
        self.assertIn(b"x_origin: 31, y_origin: 31", scaling.expected("roi"))

    def test_real_children_qualify26_before_timing_and_preserve_process_order(self):
        with patch.object(scaling, "command", side_effect=self.child_argv):
            passed = scaling.qualify(self.binaries, self.fixtures, self.evidence, [], self.env)
            self.assertEqual(len(passed), 26)
            self.assertEqual(passed, [(case["id"], side) for case in scaling.CASES
                                      for side in scaling.native.BACKENDS])
            with self.assertRaisesRegex(ValueError, "all 26"):
                scaling.pair(self.binaries, self.fixtures, passed[:-1], self.evidence, [], self.env, 2)
            self.assertFalse((self.evidence / "processes").exists())
            rows = scaling.pair(self.binaries, self.fixtures, passed, self.evidence, [], self.env, 2)
        self.assertEqual(len(rows), 52)
        self.assertEqual(rows, [json.loads(line) for line in
                                (self.evidence / "samples.jsonl").read_text().splitlines()])
        for index in range(2):
            shuffled = list(scaling.CASES)
            random.Random(48132 + index).shuffle(shuffled)
            self.assertEqual([r["fixture"] for r in rows if r["pair"] == index][::2],
                             [case["id"] for case in shuffled])
        for case in scaling.CASES:
            selected = [r for r in rows if r["fixture"] == case["id"]]
            self.assertEqual([(r["pair"], r["backend"], r["position"]) for r in selected],
                             [(0, "baseline", 0), (0, "candidate", 1),
                              (1, "candidate", 0), (1, "baseline", 1)])
            for row in selected:
                self.assertEqual((row["complete_api_calls"], row["timed_api_calls"]), (6, 3))
                self.assertEqual(len(row["decode_ns"]), 3)
                self.assertIn("minor_faults", row["metrics"])
        for row in scaling.native.summarize(rows, list(scaling.CASES), 2):
            self.assertEqual(row["candidate_over_baseline"], .5)
        for path in self.evidence.rglob("*"):
            for part in path.relative_to(self.evidence).parts:
                self.assertNotRegex(part, r'[":<>|*?\r\n]', str(path))

    def test_eight_pairs_dispatch208_six_call_children_without_changed_work(self):
        passed = [(case["id"], side) for case in scaling.CASES for side in scaling.native.BACKENDS]
        argv = []

        def checked(command, prefix, **kwargs):
            argv.append(command)
            prefix.parent.mkdir(parents=True, exist_ok=True)
            prefix.with_suffix(".stdout").write_bytes(
                b"CONFIG\t3\t1\t0\nSAMPLE\t10\nSAMPLE\t20\nSAMPLE\t30\nLIFECYCLE\t6\t3\n")
            prefix.with_suffix(".stderr").write_bytes(b"")
            return {"returncode": 0, "exit": 0, "command": command}

        with patch.object(scaling.native, "checked", side_effect=checked):
            rows = scaling.pair(self.binaries, self.fixtures, passed, self.evidence, [], self.env, 8)
        self.assertEqual(len(argv), 208)
        self.assertEqual(sum(r["complete_api_calls"] for r in rows), 1248)
        self.assertTrue(all(command[1:3] in (["bench-fixed", "full"], ["bench-fixed", "roi"])
                            for command in argv))

    def test_independent_full_sample_cdef_oracle_and_bad_six_call_output_reject(self):
        for wrong in ("wrong", "cdef"):
            evidence = self.root / wrong
            evidence.mkdir()
            fixtures = scaling.stage_inputs(evidence)
            with patch.object(scaling, "command", side_effect=self.child_argv), \
                    self.assertRaisesRegex(ValueError, "full literal oracle mismatch.*k0001-grouped/baseline"):
                scaling.qualify(dict.fromkeys(scaling.native.BACKENDS, wrong), fixtures,
                                evidence, [], self.env)
            self.assertFalse((evidence / "processes").exists())
        valid = b"CONFIG\t3\t1\t7\nSAMPLE\t10\nSAMPLE\t20\nSAMPLE\t30\nLIFECYCLE\t6\t3\n"
        self.assertEqual(scaling.timings(valid), (7, [10, 20, 30]))
        for bad in (valid.replace(b"6\t3", b"5\t3"), valid.replace(b"3\t1\t7", b"3\t2\t7"),
                    valid.replace(b"20", b"0"), valid.replace(b"SAMPLE\t20\n", b""),
                    valid + b"SAMPLE\t40\n", b"BATCH\t512\t2\t99\n"):
            with self.subTest(output=bad), self.assertRaisesRegex(ValueError, "six-call/three-clock"):
                scaling.timings(bad)

    def test_corrupt_probe_manifest_or_staged_input_refused(self):
        bad = self.root / "bad.rs"
        bad.write_bytes(b"")
        evidence = self.root / "bad-probe"
        evidence.mkdir()
        with patch.object(scaling, "PROBE", bad), self.assertRaisesRegex(ValueError, "cohort/probe hash"):
            scaling.stage_inputs(evidence)
        changed = self.root / "changed-cohort.json"
        changed.write_bytes(scaling.COHORT.read_bytes() + b" ")
        with patch.object(scaling, "COHORT", changed), self.assertRaisesRegex(ValueError, "cohort/probe hash"):
            scaling.stage_inputs(evidence)
        staged = self.evidence / "fixtures/k0256-interleaved.j2k"
        staged.write_bytes(staged.read_bytes()[:-1] + b"\x00")
        case = next(c for c in scaling.CASES if c["id"] == "k0256-interleaved")
        with self.assertRaisesRegex(ValueError, "staged scaling input hash"):
            scaling.command([], "probe", "preflight", case, self.evidence, self.fixtures)

    def check_run_binding(self, arch):
        output = self.root / f"native-{arch}"
        options = SimpleNamespace(
            baseline=scaling.BASELINE, candidate=scaling.CANDIDATE, pairs=8, arch=arch,
            output=output, qualify_only=True,
        )
        tool = {"command": [sys.executable], "returncode": 0}

        def build(label, work, evidence, selected_arch, *args, **kwargs):
            self.assertEqual(selected_arch, arch)
            path = work / f"{label}-mock-elf"
            path.write_bytes(b"\x7fELF\x02\x01" + bytes([scaling.native.ARCH[arch][0]]))
            folder = evidence / label
            folder.mkdir()
            (folder / "binary.json").write_text(json.dumps({
                "harness_sha256": scaling.PROBE_SHA, "decoder_argv": ['feature="default"'],
                "argv": [], "sha256": scaling.native.file_sha(path),
                "elf_machine": scaling.native.ARCH[arch][0],
            }))
            self.assertEqual(kwargs["probe_source"], evidence / scaling.PROBE.name)
            self.assertNotIn("default-features = false", kwargs["manifest"])
            return path

        with patch.object(scaling.native, "reject_cargo_configs"), \
                patch.object(scaling.native, "clean_source"), \
                patch.object(scaling.native, "checked"), \
                patch.object(scaling.native, "text", return_value=scaling.native.UPSTREAM), \
                patch.object(scaling.native, "pinned_tool", return_value=tool), \
                patch.object(scaling.native, "native_affinity", return_value=([0], [])), \
                patch.object(scaling, "capture", return_value={}), \
                patch.object(scaling.native, "sources") as sources, \
                patch.object(scaling.native, "build", side_effect=build), \
                patch.object(scaling, "qualify"):
            scaling.run(options)
        sources.assert_called_once_with(
            {"baseline": scaling.BASELINE, "candidate": scaling.CANDIDATE}, output, output / "evidence")
        metadata = json.loads((output / "evidence/metadata.json").read_text())
        self.assertEqual(metadata["timed_children"], 208)
        self.assertEqual(metadata["literal_preflights_before_timing"], 26)
        for side in scaling.native.BACKENDS:
            receipt = json.loads((output / f"evidence/{side}/recorded-binary.json").read_text())
            self.assertEqual(receipt["elf_machine"], scaling.native.ARCH[arch][0])
            self.assertEqual(receipt["path"], f"{side}/recorded-native-probe")

    def test_exact_source_pair_and_recorded_artifacts_on_native_and_opposite_host(self):
        for arch in scaling.native.ARCH:
            with self.subTest(arch=arch), \
                    patch.object(scaling.native.platform, "machine", return_value=arch), \
                    patch.dict(os.environ, {"RUNNER_ARCH": scaling.native.ARCH[arch][1]}):
                self.check_run_binding(arch)

    def test_unlisted_pair_work_and_opposite_host_refused_before_sources_or_output(self):
        for baseline, candidate, pairs in (
            (scaling.BASELINE, "1" * 40, 8), ("9279e2bad720511c2187a3602eda361ebf037287", scaling.CANDIDATE, 8),
            (scaling.BASELINE, scaling.CANDIDATE, 24),
        ):
            options = SimpleNamespace(
                baseline=baseline, candidate=candidate, pairs=pairs, arch=scaling.native.platform.machine(),
                output=self.root / "unlisted", qualify_only=True,
            )
            with patch.object(scaling.native, "sources") as sources, \
                    patch.object(scaling.native, "pinned_tool") as pinned, \
                    self.assertRaisesRegex(ValueError, "exact approved"):
                scaling.run(options)
            sources.assert_not_called()
            pinned.assert_not_called()
            self.assertFalse(options.output.exists())
        arch = next(name for name in scaling.native.ARCH if name != scaling.native.platform.machine())
        options.arch, options.baseline, options.candidate, options.pairs = (
            arch, scaling.BASELINE, scaling.CANDIDATE, 8)
        with patch.object(scaling.native, "sources") as sources, \
                self.assertRaisesRegex(ValueError, "requires the selected native"):
            scaling.run(options)
        sources.assert_not_called()
