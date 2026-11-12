import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import uuid


class DriverTests(unittest.TestCase):
    driver: Path
    rustc: Path

    @classmethod
    def setUpClass(cls):
        version = subprocess.run(
            [str(cls.rustc), "-vV"], check=True, text=True, capture_output=True,
        ).stdout
        if "commit-hash: 11177f2235f0c842b00f82c558ad9480c0c3a895" not in version:
            raise RuntimeError("unqualified diagnostic compiler")
        cls.sysroot = subprocess.run(
            [str(cls.rustc), "--print", "sysroot"], check=True, text=True, capture_output=True,
        ).stdout.strip()

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="native-inventory-control-")
        self.addCleanup(temporary.cleanup)
        self.work = Path(temporary.name)

    def invoke(self, output, capture_id, flags=()):
        environment = os.environ.copy()
        environment.update({
            "JPEG2000_INVENTORY_CRATE": "inventory_control",
            "JPEG2000_INVENTORY_OUTPUT": str(output),
        })
        if capture_id is None:
            environment.pop("JPEG2000_INVENTORY_CAPTURE_ID", None)
        else:
            environment["JPEG2000_INVENTORY_CAPTURE_ID"] = capture_id
        return subprocess.run(
            [
                str(self.driver), str(self.rustc), str(Path(__file__).with_name("control.rs")),
                "--crate-name", "inventory_control", "--crate-type", "lib",
                "--edition", "2024", "--emit=metadata", "--out-dir", str(self.work),
                "--sysroot", self.sysroot, *flags,
            ],
            env=environment, text=True, capture_output=True, timeout=60,
        )

    def capture(self, flags=()):
        output = self.work / f"{uuid.uuid4().hex}.json"
        capture_id = uuid.uuid4().hex
        result = self.invoke(output, capture_id, flags)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(report["capture_id"], capture_id)
        self.assertEqual(report["compiler_commit"], "11177f2235f0c842b00f82c558ad9480c0c3a895")
        self.assertEqual(report["crate"], "inventory_control")
        identifiers = [item["def_id"] for item in report["functions"]]
        self.assertEqual(len(identifiers), len(set(identifiers)))
        return report, output

    def function(self, report, name):
        matches = [item for item in report["functions"] if item["def_path"] == name]
        self.assertEqual(len(matches), 1, name)
        return matches[0]

    def test_nested_macro_derived_and_cfg_observations(self):
        report, _ = self.capture()
        self.assertTrue(self.function(report, "outer::nested")["mir_observed"])
        self.assertTrue(self.function(report, "expanded")["from_expansion"])
        self.assertTrue(self.function(report, "<Record as std::clone::Clone>::clone")["from_expansion"])
        self.assertTrue(any(
            call.get("def_path") == "outer::nested"
            for call in self.function(report, "outer")["calls"]
        ))
        names = {item["def_path"] for item in report["functions"]}
        self.assertNotIn("disabled", names)
        self.assertNotIn("test_only", names)
        test_report, _ = self.capture(("--cfg", "test"))
        self.assertTrue(self.function(test_report, "test_only")["body_owner"])
        self.assertNotIn("disabled", {item["def_path"] for item in test_report["functions"]})

    def test_abstract_const_and_runtime_constructors_are_not_conflated(self):
        report, _ = self.capture()
        self.assertFalse(self.function(report, "Abstract::declaration")["mir_available"])
        self.assertTrue(self.function(report, "Tuple")["mir_observed"])
        self.assertFalse(self.function(report, "Tuple")["body_owner"])
        self.assertTrue(self.function(report, "Choice::Value")["runtime_callable"])
        self.assertFalse(self.function(report, "Choice::Empty")["runtime_callable"])
        self.assertTrue(self.function(report, "const_callable")["mir_observed"])
        self.assertEqual(
            {item["def_path"] for item in report["other_body_owners"]},
            {"CONSTANT", "STATIC"},
        )

    def test_dispatch_and_drop_uncertainty_remain_explicit(self):
        report, _ = self.capture()
        direct = self.function(report, "direct_trait")["calls"][0]
        self.assertEqual(direct["resolution"]["dispatch"], "item")
        self.assertEqual(direct["resolution"]["def_path"], "<Record as Abstract>::declaration")
        self.assertEqual(self.function(report, "generic_trait")["calls"][0]["resolution"]["dispatch"],
                         "unresolved-generic")
        self.assertEqual(self.function(report, "dynamic")["calls"][0]["resolution"]["dispatch"], "virtual")
        self.assertEqual(self.function(report, "indirect")["calls"][0]["kind"], "indirect-function-pointer")
        self.assertTrue(any(
            item["kind"] == "Closure" and item["mir_observed"] for item in report["functions"]
        ))
        for call in self.function(report, "with_drop")["calls"]:
            self.assertIsNotNone(call["block"])
            self.assertIsNotNone(call["source"])
            self.assertIsNotNone(call["begin"])
        self.assertTrue(any(
            call["kind"] == "drop-terminator"
            and call["resolution"]["dispatch"] == "unresolved-destructor"
            for call in self.function(report, "with_drop")["calls"]
        ))

    def test_existing_capture_is_refused_without_overwriting_its_origin(self):
        report, output = self.capture()
        before = hashlib.sha256(output.read_bytes()).hexdigest()
        result = self.invoke(output, uuid.uuid4().hex)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("native inventory output must be new", result.stderr)
        self.assertEqual(hashlib.sha256(output.read_bytes()).hexdigest(), before)
        self.assertEqual(json.loads(output.read_text(encoding="utf-8"))["capture_id"], report["capture_id"])

    def test_capture_identity_is_required_before_any_output(self):
        output = self.work / "must-not-exist.json"
        for capture_id in (None, "", " \t"):
            with self.subTest(capture_id=capture_id):
                result = self.invoke(output, capture_id)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("JPEG2000_INVENTORY_CAPTURE_ID", result.stderr)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Execute real compiler inventory controls; no mocked compiler.")
    parser.add_argument("--driver", type=Path, required=True)
    parser.add_argument("--rustc", type=Path, required=True)
    arguments = parser.parse_args()
    DriverTests.driver = arguments.driver.resolve(strict=True)
    DriverTests.rustc = arguments.rustc.resolve(strict=True)
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(DriverTests)
    )
    raise SystemExit(0 if result.wasSuccessful() else 1)
