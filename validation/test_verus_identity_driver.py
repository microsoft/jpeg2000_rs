#!/usr/bin/env python3
"""Real pinned-compiler controls for the optional identity observation driver."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


CONTROL = """
use vstd::prelude::*;
verus! {
pub struct A {}
pub struct B {}
impl A { pub fn value(&self) -> (r: u8) ensures r == 7, { 7 } }
impl B { pub fn value(&self) -> (r: u8) ensures r == 9, { 9 } }
fn private_value() -> (r: u8) ensures r == 11, { 11 }
fn main() {
    let a = A {}; let b = B {};
    let av = a.value(); let bv = b.value(); let pv = private_value();
    assert(av == 7); assert(bv == 9); assert(pv == 11);
}
}
"""


def compiler_json(output: str) -> dict:
    start = output.index("\n{") + 1 if "\n{" in output else output.index("{")
    return json.JSONDecoder().raw_decode(output[start:])[0]


class DriverControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="verus-identity-control-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "control.rs"
        self.source.write_text(CONTROL)
        self.output = self.root / "identities.json"

    def run_driver(self, root: Path | None = None) -> subprocess.CompletedProcess:
        env = {
            **os.environ,
            "VERUS_ROOT": str(root or OPTIONS.verus_root),
            "JPEG2000_NAMES_OUTPUT": str(self.output),
            "LD_LIBRARY_PATH": str(OPTIONS.sdk_lib),
            "RUSTUP_TOOLCHAIN": "1.98.1-x86_64-unknown-linux-gnu",
        }
        env.pop("__VERUS_DRIVER_VIA_CARGO__", None)
        return subprocess.run(
            [str(OPTIONS.driver), str(self.source), "--crate-name", "identity_control",
             "--no-lifetime"],
            env=env, capture_output=True, text=True, timeout=120,
        )

    def test_actual_identities_and_result_details_match_the_pinned_binary(self):
        captured = self.run_driver()
        self.assertEqual(captured.returncode, 0, captured.stdout + captured.stderr)
        report = json.loads(self.output.read_text())
        ordinary = subprocess.run(
            [str(OPTIONS.verus_root / "verus"), str(self.source), "--crate-name",
             "identity_control", "--no-lifetime", "--output-json"],
            env={**os.environ, "RUSTUP_TOOLCHAIN": "1.98.1-x86_64-unknown-linux-gnu"},
            capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(ordinary.returncode, 0, ordinary.stdout + ordinary.stderr)
        proof = compiler_json(ordinary.stdout)
        self.assertTrue(report["entire_crate"])
        self.assertEqual(report["verified"], proof["verification-results"]["verified"])
        self.assertEqual(report["errors"], 0)
        self.assertEqual(report["source_function_coverage"], "not-measured")
        details = {row["compiler_result_label"]: row["result_details"]
                   for row in report["result_identities"]}
        self.assertEqual(details, proof["func-details"])
        self.assertEqual(len(report["result_identities"]), len(details))
        self.assertTrue(all(row["reported_label_disposition"] == "unique-reported-label"
                            for row in report["result_identities"]))
        project = [row for row in report["functions"]
                   if row["canonical"]["path"]["krate"] not in ("Core", "Alloc", "Vstd", "Internal")
                   and row["canonical"]["path"]["krate"]["Id"][0] == "identity_control"]
        self.assertEqual({row["compiler_result_label"] for row in project}, {
            "identity_control::A::value", "identity_control::B::value",
            "identity_control::private_value", "identity_control::main",
        })
        implementations = [row for row in project if row["compiler_result_label"].endswith("::value")]
        self.assertNotEqual(implementations[0]["canonical"], implementations[1]["canonical"])
        self.assertTrue(all(row["mode"] == "Exec" for row in project))

    def test_failed_verification_produces_no_success_capture(self):
        self.source.write_text(CONTROL.replace("ensures r == 11", "ensures r == 12"))
        result = self.run_driver()
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.output.exists())
        self.assertIn("verification failed", result.stderr)

    def test_trait_and_inherent_methods_keep_distinct_shared_label_identities(self):
        self.source.write_text(CONTROL.replace(
            "fn main() {",
            "trait T { fn value(&self) -> (r: u8) ensures r == 13; }\n"
            "impl T for A { fn value(&self) -> (r: u8) { 13 } }\n"
            "fn main() {",
        ))
        captured = self.run_driver()
        self.assertEqual(captured.returncode, 0, captured.stdout + captured.stderr)
        report = json.loads(self.output.read_text())
        shared = [row for row in report["result_identities"]
                  if row["compiler_result_label"] == "identity_control::A::value"]
        self.assertEqual(len(shared), 2)
        self.assertNotEqual(shared[0]["canonical"], shared[1]["canonical"])
        self.assertTrue(all(row["reported_label_canonical_count"] == 2
                            and row["reported_label_disposition"] == "shared-reported-label"
                            for row in shared))

    def test_actual_cargo_capture_matches_the_pinned_cargo_profile(self):
        manifest = self.root / "Cargo.toml"
        manifest.write_text(
            '[package]\nname="identity-control"\nversion="0.0.0"\nedition="2021"\n'
            'publish=false\n[workspace]\n[lib]\npath="control.rs"\n'
            '[dependencies]\nvstd="=0.0.0-2026-10-04-0306"\n'
            '[package.metadata.verus]\nverify=true\n'
        )
        env = {
            **os.environ,
            "VERUS_ROOT": str(OPTIONS.verus_root),
            "JPEG2000_NAMES_OUTPUT": str(self.output),
            "JPEG2000_NAMES_CRATE": "identity_control",
            "LD_LIBRARY_PATH": str(OPTIONS.sdk_lib),
            "RUSTUP_TOOLCHAIN": "1.98.1-x86_64-unknown-linux-gnu",
        }
        common = [
            "verus", "verify", "--manifest-path", str(manifest),
            "--fwd-verus-args-to", "roots",
        ]
        captured = subprocess.run(
            [str(OPTIONS.cargo_sdk / "cargo-verus"), *common,
             "--target-dir", str(self.root / "capture-build"),
             "--lib", "--", "--no-lifetime", "--output-json"],
            env=env, capture_output=True, text=True, timeout=180,
        )
        self.assertEqual(captured.returncode, 0, captured.stdout + captured.stderr)
        report = json.loads(self.output.read_text())
        ordinary = subprocess.run(
            [str(OPTIONS.verus_root / "cargo-verus"), *common,
             "--target-dir", str(self.root / "pinned-build"),
             "--lib", "--", "--no-lifetime", "--output-json"],
            env=env, capture_output=True, text=True, timeout=180,
        )
        self.assertEqual(ordinary.returncode, 0, ordinary.stdout + ordinary.stderr)
        proof = compiler_json(ordinary.stdout)
        self.assertTrue(report["cargo_mode"])
        self.assertTrue(report["entire_crate"])
        self.assertEqual(report["verified"], proof["verification-results"]["verified"])
        self.assertEqual(
            {row["compiler_result_label"]: row["result_details"]
             for row in report["result_identities"]},
            proof["func-details"],
        )

    def test_existing_capture_is_not_overwritten(self):
        self.output.write_bytes(b"retained old capture")
        digest = hashlib.sha256(self.output.read_bytes()).hexdigest()
        self.assertNotEqual(self.run_driver().returncode, 0)
        self.assertEqual(hashlib.sha256(self.output.read_bytes()).hexdigest(), digest)

    def test_mismatching_compiler_pin_is_rejected_before_capture(self):
        root = self.root / "different-compiler"
        root.mkdir()
        (root / "version.json").write_text(json.dumps({"verus": {"commit": "wrong"}}))
        result = self.run_driver(root)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.output.exists())
        self.assertIn("unqualified Verus compiler commit", result.stderr)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--driver", type=Path, required=True)
    parser.add_argument("--verus-root", type=Path, required=True)
    parser.add_argument("--sdk-lib", type=Path, required=True)
    parser.add_argument("--cargo-sdk", type=Path, required=True)
    OPTIONS, arguments = parser.parse_known_args()
    unittest.main(argv=[__file__, *arguments])
