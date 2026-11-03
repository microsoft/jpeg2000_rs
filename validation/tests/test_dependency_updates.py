import fnmatch
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class DependencyUpdateTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((ROOT / ".github/dependabot.yml").read_text(encoding="utf-8"))
        self.updates = {item["package-ecosystem"]: item for item in self.data["updates"]}

    def test_exact_ecosystems_and_committed_manifest_directories(self):
        self.assertEqual(self.data["version"], 2)
        self.assertEqual(len(self.data["updates"]), 3)
        self.assertEqual(set(self.updates), {"cargo", "pip", "github-actions"})
        self.assertEqual(self.updates["cargo"]["directories"], ["/", "/fuzz"])
        self.assertEqual(self.updates["pip"]["directory"], "/validation")
        self.assertEqual(self.updates["github-actions"]["directory"], "/")
        for path in ("Cargo.toml", "fuzz/Cargo.toml", "validation/requirements.in",
                     "validation/requirements.txt"):
            self.assertTrue((ROOT / path).is_file(), path)

    def test_weekly_bounded_proposals_without_privileged_update_options(self):
        for ecosystem, item in self.updates.items():
            with self.subTest(ecosystem=ecosystem):
                self.assertEqual(item["schedule"], {"interval": "weekly"})
                self.assertEqual(item["open-pull-requests-limit"], 1)
                self.assertEqual(len(item["groups"]), 1)
                self.assertEqual(next(iter(item["groups"].values())), {"patterns": ["*"]})
                self.assertEqual(set(item), {
                    "package-ecosystem", "directories" if ecosystem == "cargo" else "directory",
                    "schedule", "open-pull-requests-limit", "groups",
                } | ({"ignore"} if ecosystem == "cargo" else set()))

    def test_verifier_dependency_closure_is_not_automatically_updated(self):
        ignored = self.updates["cargo"]["ignore"]
        self.assertEqual(ignored, [{"dependency-name": "vstd"}, {"dependency-name": "verus_*"}])
        for dependency in ("vstd", "verus_builtin", "verus_builtin_macros",
                           "verus_state_machines_macros"):
            self.assertTrue(any(fnmatch.fnmatchcase(dependency, item["dependency-name"])
                                for item in ignored), dependency)

    def test_generated_package_consumer_is_not_silently_redirected(self):
        self.assertNotIn("/validation/image-consumer-probe",
                         self.updates["cargo"]["directories"])
        manifest = (ROOT / "validation/image-consumer-probe/Cargo.toml").read_text(encoding="utf-8")
        self.assertIn('path = "../../target/package/jpeg2000-decoder-0.1.0"', manifest)


if __name__ == "__main__":
    unittest.main()
