import argparse
import json
import sys
from pathlib import Path


REQUIRED_CHECKS = {
    "Test (ubuntu-latest)": 15368,
    "Test (macos-latest)": 15368,
    "Test (windows-latest)": 15368,
    "Minimum supported Rust (1.88.0)": 15368,
    "Quality and package audit": 15368,
    "Native numerical (ubuntu-latest)": 15368,
    "Native numerical (macos-latest)": 15368,
    "Native numerical (windows-latest)": 15368,
    "Generated decoder validation": 15368,
    "verify": 15368,
    "license/cla": 95686,
    "CodeQL": 57789,
}


def _object(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict) or any(not isinstance(key, str) for key in value):
        raise ValueError(f"{label} must be an object with string keys")
    return dict(value)


def _array(value: object, label: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{label} must be an array")
    return list(value)


def validate_ruleset(value: object) -> dict[str, object]:
    """Audit a supplied API snapshot; never configure policy or approve a PR."""
    data = _object(value, "ruleset")
    if data.get("id") != 25421374 or data.get("enforcement") != "active":
        raise ValueError("the main ruleset 25421374 must be active")
    if data.get("bypass_actors") != []:
        raise ValueError("main must have no bypass actors")
    conditions = _object(data.get("conditions"), "conditions")
    scope = _object(conditions.get("ref_name"), "ref_name")
    if (set(conditions) != {"ref_name"} or scope.get("include") != ["~DEFAULT_BRANCH"]
            or scope.get("exclude") != []):
        raise ValueError("the migration must target only the default branch")
    rules = {}
    for item in _array(data.get("rules"), "rules"):
        rule = _object(item, "rule")
        kind = rule.get("type")
        if not isinstance(kind, str) or kind in rules:
            raise ValueError("rule types must be strings and unique")
        rules[kind] = rule
    if not {"deletion", "non_fast_forward", "pull_request",
            "required_status_checks"}.issubset(rules):
        raise ValueError("deletion, non-fast-forward, review and status protections are required")
    review = _object(rules["pull_request"].get("parameters"), "review parameters")
    approvals = review.get("required_approving_review_count")
    if type(approvals) is not int or approvals != 0:
        raise ValueError("solo owner review requires zero native approving reviews")
    for setting in ("require_last_push_approval", "require_code_owner_review"):
        if review.get(setting) is not False:
            raise ValueError(f"{setting} must be disabled for solo owner review")
    if review.get("required_review_thread_resolution") is not True:
        raise ValueError("required_review_thread_resolution must remain enabled")
    if type(review.get("dismiss_stale_reviews_on_push")) is not bool:
        raise ValueError("dismiss_stale_reviews_on_push configuration must be explicit")
    status = _object(rules["required_status_checks"].get("parameters"), "status parameters")
    if status.get("strict_required_status_checks_policy") is not True:
        raise ValueError("strict required status checks must remain enabled")
    checks = {}
    for item in _array(status.get("required_status_checks"), "required checks"):
        check = _object(item, "required check")
        context = check.get("context")
        if not isinstance(context, str) or context in checks:
            raise ValueError("required check contexts must be strings and unique")
        checks[context] = check.get("integration_id")
    if checks != REQUIRED_CHECKS:
        raise ValueError("all twelve technical checks and their app identities must be preserved")
    return {
        "ruleset_id": data["id"],
        "required_approvals": approvals,
        "technical_checks": len(checks),
        "code_owner_review_required": review["require_code_owner_review"],
        "review_mode": "solo-owner-managed",
        "owner_comment_automatically_enforced": False,
        "scope": "read-only snapshot audit; not independent review or normative adjudication",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Read-only audit of solo-owner main protections.")
    parser.add_argument("snapshot", type=Path, help="fresh GitHub ruleset API JSON snapshot")
    arguments = parser.parse_args()
    try:
        result = validate_ruleset(json.loads(arguments.snapshot.read_text(encoding="utf-8")))
    except (OSError, ValueError) as error:
        print(f"review policy error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
