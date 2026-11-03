import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "validation/review_policy.py"
spec = importlib.util.spec_from_file_location("review_policy", SCRIPT)
review_policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review_policy)


class ReviewPolicyTests(unittest.TestCase):
    def policy(self):
        return {
            "id": 25421374, "enforcement": "active", "bypass_actors": [],
            "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}},
            "rules": [
                {"type": "deletion"}, {"type": "non_fast_forward"},
                {"type": "pull_request", "parameters": {
                    "required_approving_review_count": 1,
                    "dismiss_stale_reviews_on_push": True,
                    "require_last_push_approval": True,
                    "required_review_thread_resolution": True,
                    "require_code_owner_review": False,
                }},
                {"type": "required_status_checks", "parameters": {
                    "strict_required_status_checks_policy": True,
                    "required_status_checks": [
                        {"context": name, "integration_id": identity}
                        for name, identity in review_policy.REQUIRED_CHECKS.items()
                    ],
                }},
            ],
        }

    def test_native_review_policy_passes_without_invented_codeowners(self):
        result = review_policy.validate_ruleset(self.policy())
        self.assertEqual(result["required_approvals"], 1)
        self.assertEqual(result["technical_checks"], 12)
        self.assertFalse(result["code_owner_review_required"])

    def test_zero_bool_and_missing_review_counts_are_rejected(self):
        for value in (0, False, None, "1"):
            with self.subTest(value=value):
                data = self.policy()
                data["rules"][2]["parameters"]["required_approving_review_count"] = value
                with self.assertRaisesRegex(ValueError, "independent approving review"):
                    review_policy.validate_ruleset(data)

    def test_stale_last_push_and_thread_resolution_cannot_be_disabled(self):
        for setting in ("dismiss_stale_reviews_on_push", "require_last_push_approval",
                        "required_review_thread_resolution"):
            with self.subTest(setting=setting):
                data = self.policy()
                data["rules"][2]["parameters"][setting] = False
                with self.assertRaisesRegex(ValueError, setting):
                    review_policy.validate_ruleset(data)

    def test_each_missing_or_wrong_origin_technical_check_is_rejected(self):
        for index in range(12):
            for kind in ("missing", "origin"):
                with self.subTest(index=index, kind=kind):
                    data = self.policy()
                    checks = data["rules"][3]["parameters"]["required_status_checks"]
                    if kind == "missing":
                        checks.pop(index)
                    else:
                        checks[index]["integration_id"] = 1
                    with self.assertRaisesRegex(ValueError, "twelve technical checks"):
                        review_policy.validate_ruleset(data)

    def test_legacy_hold_extra_duplicate_and_nonstrict_checks_are_rejected(self):
        for kind in ("legacy", "duplicate", "strict"):
            with self.subTest(kind=kind):
                data = self.policy()
                status = data["rules"][3]["parameters"]
                if kind == "legacy":
                    status["required_status_checks"].append({
                        "context": "Model-review hold", "integration_id": 15368,
                    })
                elif kind == "duplicate":
                    status["required_status_checks"].append(copy.deepcopy(
                        status["required_status_checks"][0]))
                else:
                    status["strict_required_status_checks_policy"] = False
                with self.assertRaises(ValueError):
                    review_policy.validate_ruleset(data)

    def test_disabled_ruleset_bypass_and_other_ref_scope_are_rejected(self):
        for kind in ("disabled", "bypass", "release"):
            with self.subTest(kind=kind):
                data = self.policy()
                if kind == "disabled":
                    data["enforcement"] = "disabled"
                elif kind == "bypass":
                    data["bypass_actors"] = [{"actor_id": 1}]
                else:
                    data["conditions"]["ref_name"]["include"].append("refs/heads/release/0.1")
                with self.assertRaises(ValueError):
                    review_policy.validate_ruleset(data)

    def test_deleted_duplicated_or_malformed_rules_are_rejected(self):
        for kind in ("delete", "non_fast_forward", "duplicate", "malformed"):
            with self.subTest(kind=kind):
                data = self.policy()
                if kind in ("delete", "non_fast_forward"):
                    data["rules"] = [x for x in data["rules"]
                                     if x["type"] != ("deletion" if kind == "delete" else kind)]
                elif kind == "duplicate":
                    data["rules"].append(copy.deepcopy(data["rules"][0]))
                else:
                    data["rules"] = None
                with self.assertRaises(ValueError):
                    review_policy.validate_ruleset(data)

    def run_audit(self, content):
        with tempfile.TemporaryDirectory(prefix="jpeg2000-review-policy-") as directory:
            snapshot = Path(directory) / "ruleset.json"
            snapshot.write_text(content, encoding="utf-8")
            result = subprocess.run(
                [sys.executable, "-I", "-B", str(SCRIPT), str(snapshot)],
                capture_output=True, text=True,
            )
            self.assertEqual(snapshot.read_text(encoding="utf-8"), content)
            return result

    def test_cli_is_read_only_and_reports_configuration_not_approval(self):
        result = self.run_audit(json.dumps(self.policy()))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("not reviewer qualification", json.loads(result.stdout)["scope"])

    def test_cli_invalid_json_and_policy_fail_explicitly(self):
        for content in ("{", "null", json.dumps({"enforcement": "active"})):
            with self.subTest(content=content):
                result = self.run_audit(content)
                self.assertEqual(result.returncode, 2)
                self.assertIn("review policy error:", result.stderr)
                self.assertEqual(result.stdout, "")

    def test_legacy_failure_workflow_is_retired_not_made_successful(self):
        self.assertFalse((ROOT / ".github/workflows/model-review-hold.yml").exists())


if __name__ == "__main__":
    unittest.main()
