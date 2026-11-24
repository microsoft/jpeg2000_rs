import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import native_selected_parts as selected


CHILD = """
import sys
from pathlib import Path
from native_selected_parts import expected
side, operation, *args = sys.argv[1:]
if operation == 'self-check':
    print('SELF-CHECK\\tPASS')
else:
    mode, fixture = args
    name = Path(fixture).stem
    if operation == 'preflight':
        out = expected(mode)
        if side == 'wrong' and mode == 'roi':
            out = out.replace(b'Unsigned([128])', b'Unsigned([129])')
        sys.stdout.buffer.write(out)
    elif operation == 'bench-fixed':
        counts = {('grouped', 'full'): 5120, ('interleaved', 'full'): 10240,
                  ('interleaved', 'roi'): 15360}
        batch = counts[name, mode] * (2 if side == 'baseline' else 1)
        print(f'BATCH\\t{511 if side == "short" else 512}\\t2\\t{batch}')
    else:
        sys.exit('unexpected operation')
"""


class SelectedPartsTests(unittest.TestCase):
    def setUp(self):
        target = selected.native.ROOT / "target"
        target.mkdir(exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix="test-selected-parts-", dir=target)
        self.addCleanup(temp.cleanup)
        self.evidence = Path(temp.name)
        selected.stage_inputs(self.evidence)
        self.env = {"PYTHONPATH": str(selected.native.HERE), "PYTHONDONTWRITEBYTECODE": "1"}
        self.command = selected.command
        self.binaries = dict(zip(selected.native.BACKENDS, selected.native.BACKENDS, strict=True))

    def child_argv(self, pinned, binary, operation, case, evidence):
        argv = self.command(pinned, binary, operation, case, evidence)
        return [sys.executable, "-c", CHILD, *argv]

    def test_real_children_cover_preflight_and_both_timed_dispatches(self):
        with patch.object(selected, "command", side_effect=self.child_argv):
            passed = selected.qualify(self.binaries, self.evidence, [], self.env)
            self.assertEqual(len(passed), 10)
            with self.assertRaisesRegex(ValueError, "all selected literal preflights"):
                selected.pair(self.binaries, passed[:-1], self.evidence, [], self.env, 2)
            self.assertFalse((self.evidence / "processes").exists())
            rows = selected.pair(self.binaries, passed, self.evidence, [], self.env, 2)
        self.assertEqual(len(rows), 12)
        self.assertEqual(rows, [json.loads(line) for line in
                                (self.evidence / "samples.jsonl").read_text().splitlines()])
        for case, mode in (("grouped-full", "full"), ("interleaved-full", "full"),
                           ("interleaved-roi", "roi")):
            matching = [row for row in rows if row["case"] == case]
            self.assertEqual([(r["pair"], r["backend"], r["position"]) for r in matching],
                             [(0, "baseline", 0), (0, "candidate", 1),
                              (1, "candidate", 0), (1, "baseline", 1)])
            for pair, backend, _ in [(r["pair"], r["backend"], r["position"]) for r in matching]:
                stem = self.evidence / "processes" / f"pair-{pair:02d}" / case / backend
                metrics = json.loads(stem.with_suffix(".metrics.json").read_text())
                self.assertEqual(metrics["command"][4:6], ["bench-fixed", mode])
                self.assertIn("minor_faults", metrics)
                self.assertTrue(stem.with_suffix(".stdout").read_bytes().startswith(b"BATCH\t512\t2\t"))
        for row, ns in zip(selected.summaries(rows, 2), (10, 20, 30), strict=True):
            self.assertEqual(row["baseline_over_candidate"], 2)
            self.assertEqual(row["per_backend"]["candidate"]["p99_batch_mean_ns"], ns)
        # Inspect the paths actually written by preflight and paired children.
        paths = [path.relative_to(self.evidence) for path in self.evidence.rglob("*")]
        self.assertIn(Path("qualification/self-check/baseline.stdout"), paths)
        self.assertIn(Path("processes/pair-01/interleaved-roi/candidate.metrics.json"), paths)
        for path in paths:
            for component in path.parts:
                self.assertNotRegex(component, r'[":<>|*?\r\n]', str(path))

    def test_rejects_matching_but_wrong_pixels_and_wrong_fixed_count(self):
        with patch.object(selected, "command", side_effect=self.child_argv):
            with self.assertRaisesRegex(ValueError, "oracle mismatch.*grouped-roi/baseline"):
                selected.qualify(dict.fromkeys(selected.native.BACKENDS, "wrong"),
                                 self.evidence, [], self.env)
            self.assertFalse((self.evidence / "processes").exists())
        fresh = self.evidence / "fresh"
        fresh.mkdir()
        selected.stage_inputs(fresh)
        with patch.object(selected, "command", side_effect=self.child_argv):
            passed = selected.qualify(self.binaries, fresh, [], self.env)
            self.binaries["baseline"] = "short"
            with self.assertRaisesRegex(ValueError, "invalid fixed batch"):
                selected.pair(self.binaries, passed, fresh, [], self.env, 2)
        self.assertFalse((fresh / "samples.jsonl").exists())
        self.assertEqual(len(list((fresh / "processes").glob("**/*.stdout"))), 1)

    def test_rejects_probe_and_staged_fixture_changes(self):
        bad = self.evidence / "wrong.rs"
        bad.write_text("")
        new = self.evidence / "new"
        new.mkdir()
        with patch.object(selected, "PROBE", bad), self.assertRaisesRegex(ValueError, "probe hash"):
            selected.stage_inputs(new)
        staged = self.evidence / "fixtures/grouped.j2k"
        staged.write_bytes(staged.read_bytes()[:-1] + b"\x00")
        with self.assertRaisesRegex(ValueError, "fixture hash"):
            selected.command([], "probe", "preflight", ("grouped", "full"), self.evidence)
