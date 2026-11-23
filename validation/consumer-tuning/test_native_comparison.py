import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import native_comparison as driver


class NativeComparisonTests(unittest.TestCase):
    def setUp(self):
        scratch = driver.ROOT / "target"
        scratch.mkdir(exist_ok=True)
        directory = tempfile.TemporaryDirectory(dir=scratch)
        self.addCleanup(directory.cleanup)
        self.scratch = Path(directory.name)

    def test_bad_dispatch_inputs_fail_before_git(self):
        command = [sys.executable, str(driver.HERE / "native_comparison.py"),
                   "--output", str(self.scratch / "run")]
        a, b = "a" * 40, "b" * 40
        for baseline, candidate, pairs in (("main", b, "8"), (a.upper(), b, "8"),
                                            (a, a, "8"), (a, b, "7"), (a, b, "26")):
            with self.subTest(baseline=baseline, candidate=candidate, pairs=pairs):
                result = subprocess.run([*command, "--baseline", baseline, "--candidate", candidate,
                                         "--pairs", pairs, "--validate-inputs"], capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse((self.scratch / "run").exists())
        with patch.object(driver.platform, "system", return_value="Linux"), \
                patch.object(driver.platform, "machine", return_value="aarch64"), \
                patch.dict(os.environ, {"RUNNER_ARCH": "X64"}):
            with self.assertRaisesRegex(ValueError, "runner architecture mismatch"):
                driver.validate_options(a, b, 8, "aarch64")

    def test_commit_must_be_reachable_from_branch(self):
        repo = self.scratch / "git"
        subprocess.run(["git", "init", "-q", "--initial-branch=main", str(repo)], check=True)
        git = ["git", "-C", str(repo), "-c", "user.name=Test", "-c", "user.email=test@example.com"]
        subprocess.run([*git, "commit", "-qm", "root", "--allow-empty"], check=True)
        parent = subprocess.check_output([*git, "rev-parse", "HEAD"], text=True).strip()
        tree = subprocess.check_output([*git, "rev-parse", "HEAD^{tree}"], text=True).strip()
        orphan = subprocess.check_output([*git, "commit-tree", tree, "-m", "unadvertised"], text=True).strip()
        driver.require_upstream_commit(repo / ".git", parent, self.scratch / "valid")
        with self.assertRaisesRegex(ValueError, "not reachable"):
            driver.require_upstream_commit(repo / ".git", orphan, self.scratch / "orphan")
        with self.assertRaisesRegex(ValueError, "not a commit"):
            driver.require_upstream_commit(repo / ".git", tree, self.scratch / "tree")
        (repo / "untracked").touch()
        with self.assertRaisesRegex(ValueError, "dirty source"):
            driver.clean_source(repo, self.scratch / "status")

    def test_fixture_provenance_and_corrupt_input(self):
        cohort = driver.fixtures(self.scratch)
        manifest = json.loads((self.scratch / "fixture-manifest.json").read_text())
        self.assertEqual([row["group"] for row in cohort].count("ht-target"), 3)
        self.assertEqual([row["group"] for row in cohort].count("legacy-control"), 2)
        self.assertEqual(manifest["fixtures"], cohort)
        self.assertEqual(manifest["ht_manifest_sha256"], driver.sha(driver.COHORT.read_bytes()))
        self.assertIn("MIT", manifest["ht_provenance"]["license"])
        for row in cohort:
            payload = (self.scratch / row["path"]).read_bytes()
            self.assertEqual(driver.checked_bytes(payload, row), payload)
            with self.assertRaisesRegex(ValueError, "corrupt or changed input"):
                driver.checked_bytes(payload[:-1] + bytes([payload[-1] ^ 1]), row)

    def test_native_output_full_bits_and_shape(self):
        fixture = dict(id="lossy", width=2, height=1, channels=1, lossless=False)
        words = [1, 2, 1, 0, 0, 1, 2, 1, 8, 0, 1, 1, 0, 0, 16, 2, 2000, 65536]
        dump = struct.pack("<18Q", *words)
        qualified = driver.qualify(dict(baseline=dump, candidate=dump), fixture)
        self.assertEqual(qualified["native_sha256"], driver.sha(dump))
        for index, value, message in ((3, 5, "header"), (9, 1, "component"),
                                      (14, 0, "component"), (16, 65536, "blank"),
                                      (17, 65537, "output differs")):
            with self.subTest(index=index), self.assertRaisesRegex(ValueError, message):
                changed = struct.pack("<18Q", *words[:index], value, *words[index+1:])
                driver.qualify(dict(baseline=dump, candidate=changed), fixture)
        white = struct.pack("<18Q", *words[:16], 127 << 16, 128 << 16)
        with self.assertRaisesRegex(ValueError, "all-white"):
            driver.native_signature(white, fixture)
        lossless = dict(fixture, lossless=True, source_samples_sha256=driver.sha(b"\0\xff"))
        centered = struct.pack("<16Q2q", *words[:14], 0, 2, -128, 127)
        self.assertEqual(driver.native_signature(centered, lossless)["native_sha256"], driver.sha(centered))
        overflow = struct.pack("<16Q2q", *words[:14], 0, 2, -129, 127)
        with self.assertRaisesRegex(ValueError, "centered 8-bit range"):
            driver.native_signature(overflow, lossless)

    def test_samples_and_matched_summary(self):
        signature = {"fingerprint": "1234"}
        valid = "ACCEPTED\t1234\nSAMPLE\t10\nSAMPLE\t20\nSAMPLE\t90\n"
        self.assertEqual(driver.timings(valid, signature), [10, 20, 90])
        for invalid in ("refused", valid.replace("10", "0"), valid.replace("1234", "0000"), valid * 2):
            with self.assertRaisesRegex(ValueError, "malformed samples"):
                driver.timings(invalid, signature)
        fixture = {"id": "test", "group": "control"}
        rows = [dict(fixture="test", pair=pair, backend=backend, decode_ns=[value] * 3)
                for pair, backend, value in ((1, "candidate", 15), (0, "baseline", 10),
                                              (1, "baseline", 30), (0, "candidate", 20))]
        result, = driver.summarize(rows, [fixture], 2)
        self.assertEqual(result["absolute"]["baseline"],
                         {"process_median_ns": 20, "pooled_p95_ns": 30, "pooled_p99_ns": 30})
        self.assertEqual(result["pair_ratios"], [2, .5])
        self.assertEqual(result["candidate_over_baseline"], 1.)
        self.assertEqual(result["matched_pair_bootstrap95"], [.5, 2.])
        with self.assertRaisesRegex(ValueError, "missing or duplicate"):
            driver.summarize(rows[:-1], [fixture], 2)

    def test_resolved_compiler_profile(self):
        argv = ["rustc", "-C", "opt-level=3", "-C", "lto=thin", "-C", "codegen-units=1",
                "-Ctarget-cpu=native", "-C", "overflow-checks=off"]
        self.assertTrue(driver.native_profile(argv))
        for invalid in (["-Ctarget-cpu=generic"], ["-C", "debug-assertions=yes"],
                        ["--target=aarch64-unknown-linux-gnu"]):
            self.assertFalse(driver.native_profile(argv + invalid))

    def test_subprocess_failure_preserves_raw_output(self):
        prefix = self.scratch / "refused"
        argv = [sys.executable, "-c",
                "import os; os.write(1, b'\\xff'); os.write(2, b'refused'); raise SystemExit(7)"]
        with self.assertRaisesRegex(RuntimeError, r"command failed \(7\)"):
            driver.checked(argv, prefix)
        self.assertEqual(prefix.with_suffix(".stdout").read_bytes(), b"\xff")
        self.assertEqual(prefix.with_suffix(".stderr").read_bytes(), b"refused")
        metrics = json.loads(prefix.with_suffix(".metrics.json").read_text())
        self.assertEqual(metrics["returncode"], 7)
        self.assertEqual(metrics["command"], argv)
        self.assertIn("minor_faults", metrics)
        self.assertIn("involuntary_context_switches", metrics)
