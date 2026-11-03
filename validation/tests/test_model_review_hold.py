import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


VALIDATION = Path(__file__).resolve().parents[1]
CONTROLLER = VALIDATION / "check-model-review-hold.py"
spec = importlib.util.spec_from_file_location("model_review_hold", CONTROLLER)
model_review_hold = importlib.util.module_from_spec(spec)
spec.loader.exec_module(model_review_hold)


class ModelReviewHoldTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="jpeg2000-model-hold-")
        self.addCleanup(directory.cleanup)
        self.repository = Path(directory.name)
        self.git("init", "--initial-branch=main")
        self.git("config", "user.name", "Model hold test")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("config", "core.autocrlf", "false")
        self.write("src/lib.rs", "pub fn example() {}\n")
        self.write("specs/README.md", "# Guide\n")
        self.base = self.commit()

    def git(self, *arguments):
        return subprocess.run(
            ["git", "-C", str(self.repository), *arguments],
            check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout.decode("utf-8").strip()

    def write(self, name, content):
        path = self.repository / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def commit(self):
        self.git("add", "--all")
        self.git("commit", "--message", "Fixture")
        return self.git("rev-parse", "HEAD")

    def run_controller(self, base, head):
        return subprocess.run(
            [sys.executable, str(CONTROLLER), "--repository", str(self.repository), "--", base, head],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )

    def test_surface_includes_targets_dependencies_and_controller(self):
        for path in (
            "src/lib.rs", "src/table.bin", "specs/new.rs", "specs/table.json",
            "proofs/shared/view.rs", "examples/decoder.rs", "other/model.rs",
            ".github/workflows/model-review-hold.yml", ".github/new-workflow.yml",
            ".cargo/config.toml", "Cargo.toml", "Cargo.lock", "fuzz/Cargo.toml",
            "rust-toolchain.toml", "rust-toolchain", "validation/framework.py",
            ".gitattributes", ".gitmodules",
            "validation/check-model-review-hold.py", "validation/normative-coverage.json",
            "validation/tests/test_model_review_hold.py",
        ):
            with self.subTest(path=path):
                self.assertTrue(model_review_hold.held_path(path))
        for path in ("README.md", "PROOFS.md", "specs/README.md", "specs/AUDIT_REFERENCE.md",
                     "validation/VALIDATION.md", "proofs/README.md"):
            with self.subTest(path=path):
                self.assertFalse(model_review_hold.held_path(path))

    def test_documentation_change_passes(self):
        self.write("specs/README.md", "# Improved guide\n")
        self.write("specs/AUDIT_REFERENCE.md", "# Existing detail\n")
        result = self.run_controller(self.base, self.commit())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("PASS: no unapproved changes", result.stdout)

    def test_source_change_is_held(self):
        self.write("src/lib.rs", "pub fn changed() {}\n")
        result = self.run_controller(self.base, self.commit())
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("'src/lib.rs'", result.stdout)

    def test_new_target_is_held(self):
        self.write("specs/new.rs", "pub spec fn weakened() -> bool { true }\n")
        self.assertEqual(
            model_review_hold.held_changes(self.repository, self.base, self.commit()),
            ["specs/new.rs"],
        )

    def test_source_deletion_is_held(self):
        (self.repository / "src/lib.rs").unlink()
        self.assertEqual(
            model_review_hold.held_changes(self.repository, self.base, self.commit()),
            ["src/lib.rs"],
        )

    def test_rename_to_documentation_does_not_hide_source_removal(self):
        self.git("mv", "src/lib.rs", "source.md")
        self.assertEqual(
            model_review_hold.held_changes(self.repository, self.base, self.commit()),
            ["src/lib.rs"],
        )

    def test_candidate_controller_cannot_approve_its_own_model_change(self):
        self.write("validation/check-model-review-hold.py", "raise SystemExit(0)\n")
        self.write("src/lib.rs", "pub fn changed() {}\n")
        result = self.run_controller(self.base, self.commit())
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("'src/lib.rs'", result.stdout)
        self.assertIn("'validation/check-model-review-hold.py'", result.stdout)

    def test_workflow_only_change_is_held(self):
        self.write(".github/workflows/model-review-hold.yml", "jobs: {}\n")
        result = self.run_controller(self.base, self.commit())
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("'.github/workflows/model-review-hold.yml'", result.stdout)

    def test_unrelated_base_progress_is_not_a_proposed_change(self):
        self.write("specs/README.md", "# Improved guide\n")
        head = self.commit()
        self.git("checkout", "-b", "target-progress", self.base)
        self.write("src/lib.rs", "pub fn unrelated_base_change() {}\n")
        base = self.commit()
        result = self.run_controller(base, head)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_uncommitted_files_do_not_replace_committed_evidence(self):
        self.write("src/lib.rs", "pub fn changed() {}\n")
        head = self.commit()
        self.write("src/lib.rs", "pub fn example() {}\n")
        result = self.run_controller(self.base, head)
        self.assertEqual(result.returncode, 1, result.stderr)

    def test_empty_change_passes(self):
        result = self.run_controller(self.base, self.base)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_incomplete_or_option_shaped_commit_ids_are_errors(self):
        for value in (self.base[:8], "--no-index", "0" * 39, "z" * 40):
            with self.subTest(value=value):
                result = self.run_controller(value, self.base)
                self.assertEqual(result.returncode, 2)
                self.assertIn("expected a full SHA-1 commit ID", result.stderr)

    def test_missing_history_is_an_error_not_an_allowed_change(self):
        result = self.run_controller(self.base, "0" * 40)
        self.assertEqual(result.returncode, 2)
        self.assertIn("could not read", result.stderr)

    def test_unrelated_histories_are_an_error_not_an_allowed_change(self):
        self.git("checkout", "--orphan", "unrelated")
        self.write("specs/README.md", "# Unrelated root commit\n")
        head = self.commit()
        result = self.run_controller(self.base, head)
        self.assertEqual(result.returncode, 2)
        self.assertIn("could not read", result.stderr)

    def test_multiple_merge_bases_are_an_error(self):
        tree = self.git("rev-parse", self.base + "^{tree}")
        left = self.git("commit-tree", tree, "-p", self.base, "-m", "Left")
        right = self.git("commit-tree", tree, "-p", self.base, "-m", "Right")
        base = self.git("commit-tree", tree, "-p", left, "-p", right, "-m", "Left merge")
        head = self.git("commit-tree", tree, "-p", right, "-p", left, "-m", "Right merge")
        result = self.run_controller(base, head)
        self.assertEqual(result.returncode, 2)
        self.assertIn("exactly one merge base", result.stderr)

    def test_git_paths_are_nul_delimited_not_line_delimited(self):
        name = "specs/name\npart.rs"
        with patch.object(model_review_hold, "git", side_effect=[
            self.base.encode("ascii") + b"\n",
            name.encode("utf-8") + b"\0specs/README.md\0",
        ]):
            self.assertEqual(
                model_review_hold.held_changes(self.repository, self.base, self.base),
                [name],
            )


    def registry(self, entries):
        directory = tempfile.TemporaryDirectory(prefix="jpeg2000-trusted-registry-")
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "registry.md"
        path.write_text(
            "# Trusted fixture\n\n```json\n"
            + json.dumps({"schema_version": 1, "amendments": entries})
            + "\n```\n", encoding="utf-8",
        )
        return path

    def consumer_fixture(self):
        workflow = ".github/workflows/ci.yml"
        self.write(workflow, "jobs: original\n")
        base = self.commit()
        for path in model_review_hold.AMENDMENT_PROFILES["image-consumer-probe"]:
            self.write(path, "checked consumer fixture\n")
        head = self.commit()
        entry = {
            "id": "consumer-fixture",
            "profile": "image-consumer-probe",
            "source_pr": 164, "source_head": head, "ci_run": 1, "verus_run": 2,
            "rationale": "Bounded standalone consumer, not a normative amendment.",
            "paths": {
                path: {
                    "before": self.git("rev-parse", f"{base}:{path}") if path == workflow else None,
                    "after": self.git("rev-parse", f"{head}:{path}"),
                }
                for path in model_review_hold.AMENDMENT_PROFILES["image-consumer-probe"]
            },
        }
        return base, head, entry

    def test_repository_registry_is_valid(self):
        self.assertIsInstance(
            model_review_hold.read_reviewed_amendments(CONTROLLER.parent / "reviewed-amendments.md"),
            list,
        )

    def test_exact_trusted_record_passes(self):
        base, head, entry = self.consumer_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_candidate_record_cannot_authorize_its_source(self):
        base, _, entry = self.consumer_fixture()
        self.write("validation/reviewed-amendments.md",
                   "```json\n" + json.dumps({"schema_version": 1, "amendments": [entry]}) + "\n```\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(
                set(model_review_hold.held_changes(self.repository, base, self.commit())),
                set(entry["paths"]),
            )

    def test_registry_only_proposal_can_pass_before_review(self):
        self.write("validation/reviewed-amendments.md", "proposed policy data\n")
        self.assertEqual(model_review_hold.held_changes(self.repository, self.base, self.commit()), [])

    def test_documentation_can_repair_invalid_trusted_registry(self):
        path = self.registry([])
        path.write_text("invalid trusted data\n", encoding="utf-8")
        self.write("validation/reviewed-amendments.md", "repaired proposed data\n")
        with patch.object(model_review_hold, "REGISTRY", path):
            self.assertEqual(model_review_hold.held_changes(self.repository, self.base, self.commit()), [])

    def test_extra_model_is_held_despite_trusted_consumer_record(self):
        base, _, entry = self.consumer_fixture()
        self.write("specs/new.rs", "pub spec fn weakened() -> bool { true }\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertIn("specs/new.rs",
                          model_review_hold.held_changes(self.repository, base, self.commit()))

    def test_changed_consumer_source_is_held(self):
        base, _, entry = self.consumer_fixture()
        path = "validation/image-consumer-probe/src/decoder.rs"
        self.write(path, "changed consumer\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertIn(path, model_review_hold.held_changes(self.repository, base, self.commit()))

    def test_changed_workflow_is_held(self):
        base, _, entry = self.consumer_fixture()
        self.write(".github/workflows/ci.yml", "changed workflow\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertIn(".github/workflows/ci.yml",
                          model_review_hold.held_changes(self.repository, base, self.commit()))

    def test_missing_consumer_file_is_held(self):
        base, _, entry = self.consumer_fixture()
        (self.repository / "validation/image-consumer-probe/Cargo.lock").unlink()
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertTrue(model_review_hold.held_changes(self.repository, base, self.commit()))

    def test_wrong_original_blob_is_held(self):
        base, head, entry = self.consumer_fixture()
        entry["paths"][".github/workflows/ci.yml"]["before"] = "0" * 40
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertTrue(model_review_hold.held_changes(self.repository, base, head))

    def test_original_absence_is_required(self):
        base, head, entry = self.consumer_fixture()
        self.git("checkout", "-b", "different-original", base)
        self.write("validation/image-consumer-probe/Cargo.toml", "preexisting\n")
        other_base = self.commit()
        for path in entry["paths"]:
            self.write(path, self.git("show", f"{head}:{path}") + "\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertTrue(model_review_hold.held_changes(self.repository, other_base, self.commit()))

    def test_executable_mode_is_held(self):
        base, _, entry = self.consumer_fixture()
        path = "validation/image-consumer-probe/src/decoder.rs"
        self.git("update-index", "--chmod=+x", path)
        self.git("commit", "--message", "Change mode")
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertIn(path, model_review_hold.held_changes(
                self.repository, base, self.git("rev-parse", "HEAD")))

    def test_controller_cannot_be_combined_with_authorized_source(self):
        base, _, entry = self.consumer_fixture()
        self.write("validation/check-model-review-hold.py", "raise SystemExit(0)\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertIn("validation/check-model-review-hold.py",
                          model_review_hold.held_changes(self.repository, base, self.commit()))

    def test_separate_records_do_not_authorize_combined_changes(self):
        base, _, consumer = self.consumer_fixture()
        paths = model_review_hold.AMENDMENT_PROFILES["source-complete-package"]
        for path in paths:
            self.write(path, "package fixture\n")
        head = self.commit()
        package = dict(consumer, id="package-fixture", profile="source-complete-package",
                       source_head=head, paths={
                           path: {"before": None, "after": self.git("rev-parse", f"{head}:{path}")}
                           for path in paths
                       })
        with patch.object(model_review_hold, "REGISTRY", self.registry([consumer, package])):
            self.assertTrue(model_review_hold.held_changes(self.repository, base, head))

    def test_malformed_missing_multiple_or_duplicate_json_is_rejected(self):
        for text in (
            "no JSON\n", "```json\n{\n```\n",
            '```json\n{"schema_version":1,"schema_version":1,"amendments":[]}\n```\n',
            '```json\n{"schema_version":1,"amendments":[]}\n```\n' * 2,
        ):
            with self.subTest(text=text):
                path = self.registry([])
                path.write_text(text, encoding="utf-8")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(path)

    def test_record_schema_rejects_flags_unknown_profiles_and_normative_paths(self):
        _, _, original = self.consumer_fixture()
        for change in (
            lambda entry: entry.update(approved=True),
            lambda entry: entry.pop("ci_run"),
            lambda entry: entry.update(profile="normative-model"),
            lambda entry: entry["paths"].update({"specs/new.rs": {"before": None, "after": "a" * 40}}),
            lambda entry: entry["paths"].update({"validation/check-model-review-hold.py": {"before": None, "after": "a" * 40}}),
            lambda entry: entry.update(source_pr=True),
            lambda entry: entry.update(verus_run=0),
            lambda entry: entry.update(source_head="short"),
            lambda entry: entry.update(rationale=" "),
        ):
            entry = copy.deepcopy(original)
            change(entry)
            with self.assertRaises(ValueError):
                model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_invalid_or_unchanged_blob_identities_are_rejected(self):
        _, _, original = self.consumer_fixture()
        path = ".github/workflows/ci.yml"
        for identities in (
            {"before": "short", "after": "a" * 40},
            {"before": None, "after": None},
            {"before": "a" * 40, "after": "a" * 40},
            {"before": None, "after": "z" * 40},
            {"before": None, "after": "a" * 40, "approved": True},
        ):
            entry = copy.deepcopy(original)
            entry["paths"][path] = identities
            with self.assertRaises(ValueError):
                model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_invalid_envelopes_and_duplicate_record_ids_are_rejected(self):
        _, _, entry = self.consumer_fixture()
        with self.assertRaises(ValueError):
            model_review_hold.read_reviewed_amendments(self.registry([entry, entry]))
        for data in (
            [], {"schema_version": True, "amendments": []},
            {"schema_version": 2, "amendments": []},
            {"schema_version": 1, "amendments": {}},
            {"schema_version": 1, "amendments": [], "approved": True},
        ):
            path = self.registry([])
            path.write_text("```json\n" + json.dumps(data) + "\n```\n", encoding="utf-8")
            with self.assertRaises(ValueError):
                model_review_hold.read_reviewed_amendments(path)

    def test_missing_or_symlink_registry_is_rejected(self):
        path = self.registry([])
        missing = path.with_name("missing.md")
        with self.assertRaises(ValueError):
            model_review_hold.read_reviewed_amendments(missing)
        link = path.with_name("linked.md")
        link.symlink_to(path)
        with self.assertRaises(ValueError):
            model_review_hold.read_reviewed_amendments(link)

    def proof_support_fixture(self):
        originals = {
            "src/decode.rs": "fn decode() {}\n#[cfg(verus_keep_ghost)]\nverus! { pub proof fn helper() {} }\n",
            "validation/expected-package-files.txt": "src/decode.rs\n",
            "validation/normative-coverage.json": '{"proof_refs":[{"path":"src/decode.rs","symbol":"helper"}]}\n',
        }
        proposed = {
            "src/decode.rs": 'fn decode() {}\n#[cfg(verus_keep_ghost)]\ninclude!("decode/proof_support.rs");\n',
            "src/decode/proof_support.rs": "verus! { pub proof fn helper() {} }\n",
            "validation/expected-package-files.txt": "src/decode/proof_support.rs\nsrc/decode.rs\n",
            "validation/normative-coverage.json": '{"proof_refs":[{"path":"src/decode/proof_support.rs","symbol":"helper"}]}\n',
        }
        return self.layout_fixture(
            originals, proposed, "decode-proof-support",
            "Exact support layout, not normative model approval.",
        )

    def layout_fixture(self, originals, proposed, profile, rationale):
        for path, content in originals.items():
            self.write(path, content)
        base = self.commit()
        for path, content in proposed.items():
            self.write(path, content)
        head = self.commit()
        entry = {
            "id": f"{profile}-fixture", "profile": profile,
            "source_pr": 1, "source_head": head, "ci_run": 1, "verus_run": 2,
            "rationale": rationale,
            "paths": {
                path: {
                    "before": self.git("rev-parse", f"{base}:{path}") if path in originals else None,
                    "after": self.git("rev-parse", f"{head}:{path}"),
                }
                for path in proposed
            },
        }
        return base, head, entry

    def test_exact_decode_support_profile_passes_only_after_trusted_adoption(self):
        base, head, entry = self.proof_support_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_decode_support_record_does_not_authorize_changed_runtime(self):
        base, _, entry = self.proof_support_fixture()
        self.write("src/decode.rs", "fn decode() { panic!() }\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertIn("src/decode.rs",
                          model_review_hold.held_changes(self.repository, base, self.commit()))

    def test_decode_support_record_does_not_authorize_changed_proof_or_model(self):
        base, head, original = self.proof_support_fixture()
        self.write("src/decode/proof_support.rs", "verus! { pub proof fn changed() {} }\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([original])):
            self.assertIn("src/decode/proof_support.rs",
                          model_review_hold.held_changes(self.repository, base, self.commit()))
        self.git("checkout", "-b", "extra-model", head)
        self.write("specs/new.rs", "pub spec fn weakened() -> bool { true }\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([original])):
            self.assertIn("specs/new.rs",
                          model_review_hold.held_changes(self.repository, base, self.commit()))

    def test_decode_support_profile_cannot_name_another_module_or_controller(self):
        _, _, original = self.proof_support_fixture()
        for replacement in ("src/tier1.rs", "validation/check-model-review-hold.py"):
            entry = copy.deepcopy(original)
            entry["paths"][replacement] = entry["paths"].pop("src/decode.rs")
            with self.assertRaises(ValueError):
                model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def tier1_test_fixture(self):
        originals = {
            "src/tier1.rs": "fn decode() {}\n#[cfg(test)]\nmod tests { #[test] fn exact() {} }\n",
            "validation/expected-package-files.txt": "src/tier1.rs\n",
            "validation/normative-coverage.json": '{"test_refs":[{"path":"src/tier1.rs","symbol":"exact"}]}\n',
            "validation/tests/test_framework.py": "original binding regression\n",
        }
        proposed = {
            "src/tier1.rs": "fn decode() {}\n#[cfg(test)]\nmod tests;\n",
            "src/tier1/tests.rs": "use super::*;\n#[test]\nfn exact() {}\n",
            "validation/expected-package-files.txt": "src/tier1/tests.rs\nsrc/tier1.rs\n",
            "validation/normative-coverage.json": '{"test_refs":[{"path":"src/tier1/tests.rs","symbol":"exact"}]}\n',
            "validation/tests/test_framework.py": "relocated binding regression\n",
        }
        return self.layout_fixture(
            originals, proposed, "tier1-test-extraction",
            "Exact private-test relocation with unchanged runtime/proof prefix.",
        )

    def test_exact_tier1_test_record_passes_only_after_trusted_adoption(self):
        base, head, entry = self.tier1_test_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_tier1_test_record_rejects_changed_runtime_tests_inventory_or_bindings(self):
        base, head, entry = self.tier1_test_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-tier1-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_tier1_test_record_does_not_authorize_models_other_modules_or_controller(self):
        base, head, entry = self.tier1_test_fixture()
        for index, path in enumerate((
            "specs/new.rs", "src/decode/proof_support.rs", "validation/check-model-review-hold.py",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-tier1-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_tier1_test_profile_cannot_name_another_module_or_controller(self):
        _, _, original = self.tier1_test_fixture()
        for replacement in ("src/decode.rs", "specs/new.rs", "validation/check-model-review-hold.py"):
            with self.subTest(path=replacement):
                entry = copy.deepcopy(original)
                entry["paths"][replacement] = entry["paths"].pop("src/tier1.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def crate_rename_fixture(self):
        paths = model_review_hold.AMENDMENT_PROFILES["crate-publication-rename"]
        originals = {path: f"original {path}\n" for path in paths}
        proposed = {path: f"renamed {path}\n" for path in paths}
        return self.layout_fixture(
            originals, proposed, "crate-publication-rename",
            "Exact owner-requested package/import/collector rename, not a normative amendment.",
        )

    def test_exact_crate_rename_record_requires_trusted_adoption(self):
        base, head, entry = self.crate_rename_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_crate_rename_record_rejects_any_changed_protected_identity(self):
        base, head, entry = self.crate_rename_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-rename-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_crate_rename_record_cannot_authorize_codec_models_or_controller(self):
        base, head, entry = self.crate_rename_fixture()
        for index, path in enumerate((
            "src/lib.rs", "src/tier1.rs", "specs/new.rs", "proofs/new.rs",
            "validation/check-model-review-hold.py",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-rename-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_crate_rename_profile_cannot_expand_to_codec_or_controller_paths(self):
        _, _, original = self.crate_rename_fixture()
        for path in ("src/lib.rs", "specs/new.rs", "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("Cargo.toml")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def decode_domain_fixture(self):
        paths = model_review_hold.AMENDMENT_PROFILES["decode-domain-layout"]
        existing = {
            "src/decode.rs", "src/decode/proof_support.rs",
            "validation/expected-package-files.txt", "validation/framework.py",
            "validation/normative-coverage.json", "validation/tests/test_framework.py",
        }
        return self.layout_fixture(
            {path: f"original {path}\n" for path in existing},
            {path: f"relocated {path}\n" for path in paths},
            "decode-domain-layout",
            "Exact decoder responsibility split with unchanged executing contracts and bodies.",
        )

    def test_exact_decode_domain_record_requires_trusted_adoption(self):
        base, head, entry = self.decode_domain_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_decode_domain_record_rejects_each_changed_source_or_evidence_identity(self):
        base, head, entry = self.decode_domain_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-domain-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_decode_domain_record_does_not_authorize_models_other_modules_or_controller(self):
        base, head, entry = self.decode_domain_fixture()
        for index, path in enumerate((
            "specs/new.rs", "proofs/new.rs", "src/codestream.rs", "src/lib.rs",
            "validation/check-model-review-hold.py",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-domain-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_decode_domain_profile_cannot_expand_to_unknown_modules_or_models(self):
        _, _, original = self.decode_domain_fixture()
        for path in ("src/decode/unknown.rs", "src/codestream.rs", "specs/new.rs",
                     "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("src/decode/selection.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def remaining_domain_fixture(self):
        paths = model_review_hold.AMENDMENT_PROFILES["remaining-runtime-domain-layout"]
        self.assertEqual(len(paths), 124)
        existing = {
            "src/codestream.rs", "src/color.rs", "src/image.rs", "src/jp2.rs",
            "src/jpip.rs", "src/jpx.rs", "src/packet.rs", "src/refinement.rs",
            "src/tier1.rs", "src/transform.rs", "validation/expected-package-files.txt",
            "validation/framework.py", "validation/normative-coverage.json",
            "validation/tests/test_framework.py",
        }
        return self.layout_fixture(
            {path: f"original {path}\n" for path in existing},
            {path: f"relocated {path}\n" for path in paths},
            "remaining-runtime-domain-layout",
            "Exact remaining responsibility modules; unchanged native bodies and contracts.",
        )

    def test_exact_remaining_domain_record_requires_trusted_adoption(self):
        base, head, entry = self.remaining_domain_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_remaining_domain_record_rejects_each_changed_source_or_evidence_identity(self):
        base, head, entry = self.remaining_domain_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-remaining-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_remaining_domain_record_does_not_authorize_models_other_modules_or_controller(self):
        base, head, entry = self.remaining_domain_fixture()
        for index, path in enumerate((
            "specs/new.rs", "proofs/new.rs", "src/decode.rs", "src/decode/api.rs",
            "src/lib.rs", "src/limits.rs", "Cargo.toml",
            "validation/check-model-review-hold.py", ".github/workflows/verus.yml",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-remaining-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_remaining_domain_profile_cannot_expand_to_unknown_modules_or_models(self):
        _, _, original = self.remaining_domain_fixture()
        for path in ("src/tier1/unknown.rs", "src/decode.rs", "specs/new.rs",
                     "proofs/new.rs", "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("src/tier1/raw.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def packet_metadata_fixture(self):
        paths = {
            "src/error.rs",
            "src/codestream/packet_headers.rs", "src/codestream/proof_support.rs",
            "src/codestream/tests.rs", "specs/packet_input.rs",
            "validation/framework.py", "validation/normative-coverage.json",
            "validation/tests/test_framework.py",
        }
        self.assertEqual(model_review_hold.AMENDMENT_PROFILES["packet-metadata-finalization"],
                         paths)
        return self.layout_fixture(
            {path: f"original {path}\n" for path in paths},
            {path: f"source-derived result contract {path}\n" for path in paths},
            "packet-metadata-finalization",
            "Exact source-derived raw packet finalizers, not normative correspondence approval.",
        )

    def test_packet_metadata_record_requires_exact_trusted_adoption(self):
        base, head, entry = self.packet_metadata_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_packet_metadata_record_rejects_each_changed_source_model_or_evidence(self):
        base, head, entry = self.packet_metadata_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-packet-metadata-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_packet_metadata_record_does_not_authorize_other_models_or_controls(self):
        base, head, entry = self.packet_metadata_fixture()
        for index, path in enumerate((
            "specs/packet.rs", "specs/new.rs", "proofs/new.rs", "src/codestream/tiles.rs",
            "src/decode/api.rs", "src/lib.rs", "src/limits.rs", "Cargo.toml",
            "rust-toolchain.toml", "validation/generate-proof-coverage.py",
            "validation/check-model-review-hold.py", ".github/workflows/verus.yml",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-packet-metadata-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_packet_metadata_profile_rejects_expansion_and_incomplete_records(self):
        _, _, original = self.packet_metadata_fixture()
        for path in ("specs/new.rs", "proofs/new.rs", "src/codestream.rs",
                     "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("specs/packet_input.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))
        for path in original["paths"]:
            with self.subTest(missing=path):
                entry = copy.deepcopy(original)
                del entry["paths"][path]
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_candidate_packet_metadata_record_cannot_authorize_itself(self):
        base, _, entry = self.packet_metadata_fixture()
        self.write("validation/reviewed-amendments.md",
                   "```json\n" + json.dumps({"schema_version": 1, "amendments": [entry]})
                   + "\n```\n")
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(
                self.repository, base, self.commit())), set(entry["paths"]))

    def tile_component_style_cache_fixture(self):
        paths = {
            "src/codestream/layout.rs", "src/codestream/tiles.rs",
            "src/codestream/tests.rs",
        }
        self.assertEqual(model_review_hold.AMENDMENT_PROFILES["tile-component-style-cache"],
                         paths)
        return self.layout_fixture(
            {path: f"original {path}\n" for path in paths},
            {path: f"latest-owner index cache {path}\n" for path in paths},
            "tile-component-style-cache",
            "Exact allocation reduction with proved latest-owner indices, not changed resource policy.",
        )

    def test_tile_component_style_cache_requires_exact_trusted_adoption(self):
        base, head, entry = self.tile_component_style_cache_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_tile_component_style_cache_rejects_each_changed_source_or_proof(self):
        base, head, entry = self.tile_component_style_cache_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-tile-cache-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_tile_component_style_cache_does_not_authorize_models_limits_or_controls(self):
        base, head, entry = self.tile_component_style_cache_fixture()
        for index, path in enumerate((
            "src/codestream.rs", "src/decode.rs", "src/error.rs",
            "src/codestream/packet_headers.rs", "specs/new.rs", "proofs/new.rs",
            "validation/resource_benchmarks.py", "validation/framework.py",
            "validation/generate-proof-coverage.py", "validation/check-model-review-hold.py",
            "Cargo.toml", ".github/workflows/ci.yml",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-tile-cache-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_tile_component_style_cache_rejects_expansion_or_missing_paths(self):
        _, _, original = self.tile_component_style_cache_fixture()
        for path in ("src/error.rs", "specs/new.rs", "validation/resource_benchmarks.py",
                     "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("src/codestream/layout.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))
        for path in original["paths"]:
            with self.subTest(missing=path):
                entry = copy.deepcopy(original)
                del entry["paths"][path]
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def tile_packet_admission_fixture(self):
        paths = {
            "src/codestream/tiles.rs", "src/codestream/packet_headers.rs",
            "src/codestream/tests.rs", "specs/packet_input.rs",
            "validation/framework.py", "validation/normative-coverage.json",
            "validation/tests/test_framework.py",
        }
        self.assertEqual(model_review_hold.AMENDMENT_PROFILES["tile-packet-admission"],
                         paths)
        return self.layout_fixture(
            {path: f"original {path}\n" for path in paths},
            {path: f"source-derived tile packet admission {path}\n" for path in paths},
            "tile-packet-admission",
            "Exact actual PLT/PPT producer extraction and complete state contracts.",
        )

    def test_tile_packet_admission_requires_exact_trusted_adoption(self):
        base, head, entry = self.tile_packet_admission_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_tile_packet_admission_rejects_each_changed_source_model_or_binding(self):
        base, head, entry = self.tile_packet_admission_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-tile-admission-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_tile_packet_admission_does_not_authorize_other_models_or_controls(self):
        base, head, entry = self.tile_packet_admission_fixture()
        for index, path in enumerate((
            "src/codestream/layout.rs", "src/error.rs", "src/decode.rs",
            "specs/new.rs", "proofs/new.rs", "validation/resource_benchmarks.py",
            "validation/generate-proof-coverage.py", "validation/check-model-review-hold.py",
            "Cargo.toml", ".github/workflows/verus.yml",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-tile-admission-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_tile_packet_admission_rejects_expansion_and_incomplete_records(self):
        _, _, original = self.tile_packet_admission_fixture()
        for path in ("src/error.rs", "src/codestream/layout.rs", "specs/new.rs",
                     "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("specs/packet_input.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))
        for path in original["paths"]:
            with self.subTest(missing=path):
                entry = copy.deepcopy(original)
                del entry["paths"][path]
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_cache_and_packet_records_do_not_authorize_combined_source(self):
        cache_paths = model_review_hold.AMENDMENT_PROFILES["tile-component-style-cache"]
        packet_paths = model_review_hold.AMENDMENT_PROFILES["tile-packet-admission"]
        base, _, cache = self.layout_fixture(
            {path: f"original {path}\n" for path in cache_paths | packet_paths},
            {path: f"cache change {path}\n" for path in cache_paths},
            "tile-component-style-cache", "Bounded cache fixture.",
        )
        for path in packet_paths:
            self.write(path, f"packet change {path}\n")
        head = self.commit()
        packet = dict(cache, id="packet-admission-combined-fixture",
                      profile="tile-packet-admission", source_head=head, paths={
                          path: {"before": self.git("rev-parse", f"{base}:{path}"),
                                 "after": self.git("rev-parse", f"{head}:{path}")}
                          for path in packet_paths
                      })
        with patch.object(model_review_hold, "REGISTRY", self.registry([cache, packet])):
            self.assertTrue(model_review_hold.held_changes(self.repository, base, head))

    def component_depth_registration_fixture(self):
        paths = {
            "src/codestream/layout.rs", "src/codestream/image_header.rs",
            "src/codestream/tests.rs", "specs/mod.rs",
            "validation/framework.py", "validation/normative-coverage.json",
            "validation/tests/test_framework.py",
        }
        self.assertEqual(model_review_hold.AMENDMENT_PROFILES["component-depth-registration"],
                         paths)
        return self.layout_fixture(
            {path: f"original {path}\n" for path in paths},
            {path: f"component application {path}\n" for path in paths},
            "component-depth-registration",
            "Exact actual CBD/CRG application and physical uniformity with complete frames.",
        )

    def test_component_application_requires_exact_trusted_adoption(self):
        base, head, entry = self.component_depth_registration_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_component_application_rejects_each_changed_source_model_or_binding(self):
        base, head, entry = self.component_depth_registration_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-component-application-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_component_application_does_not_authorize_other_models_or_controls(self):
        base, head, entry = self.component_depth_registration_fixture()
        for index, path in enumerate((
            "src/codestream.rs", "src/codestream/tiles.rs",
            "src/codestream/decomposition.rs", "src/codestream/coding_style.rs",
            "src/codestream/packet_headers.rs", "src/error.rs", "specs/packet_input.rs",
            "specs/new.rs", "proofs/new.rs", "validation/resource_benchmarks.py",
            "validation/generate-proof-coverage.py", "validation/check-model-review-hold.py",
            "Cargo.toml", "Cargo.lock", "rust-toolchain.toml", ".github/workflows/verus.yml",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-component-application-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_component_application_rejects_expansion_and_incomplete_records(self):
        _, _, original = self.component_depth_registration_fixture()
        for path in ("src/error.rs", "src/codestream/tiles.rs", "specs/new.rs",
                     "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("specs/mod.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))
        for path in original["paths"]:
            with self.subTest(missing=path):
                entry = copy.deepcopy(original)
                del entry["paths"][path]
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_component_and_tile_records_reject_even_exact_combined_source(self):
        profile = "component-depth-registration"
        component_paths = model_review_hold.AMENDMENT_PROFILES[profile]
        for other_profile in ("tile-component-style-cache", "tile-packet-admission"):
            with self.subTest(profile=other_profile):
                other_paths = model_review_hold.AMENDMENT_PROFILES[other_profile]
                base, head, component = self.layout_fixture(
                    {path: f"original {path}\n" for path in component_paths | other_paths},
                    {path: f"combined source {path}\n" for path in component_paths | other_paths},
                    profile, "Exact combined source must remain held.",
                )
                entries = []
                for name, paths in ((profile, component_paths), (other_profile, other_paths)):
                    entries.append(dict(
                        component, id=f"combined-{name}", profile=name, source_head=head,
                        paths={
                            path: {"before": self.git("rev-parse", f"{base}:{path}"),
                                   "after": self.git("rev-parse", f"{head}:{path}")}
                            for path in paths
                        },
                    ))
                registry = self.registry(entries)
                self.assertEqual(len(model_review_hold.read_reviewed_amendments(registry)), 2)
                with patch.object(model_review_hold, "REGISTRY", registry):
                    self.assertTrue(model_review_hold.held_changes(self.repository, base, head))

    def decomposition_resolution_fixture(self):
        paths = {
            "src/codestream/decomposition.rs", "src/codestream/extensions.rs",
            "src/codestream/coding_style.rs", "src/codestream/proof_support.rs",
            "src/codestream/tests.rs", "specs/mod.rs", "validation/framework.py",
            "validation/normative-coverage.json", "validation/tests/test_framework.py",
        }
        self.assertEqual(model_review_hold.AMENDMENT_PROFILES["decomposition-resolution"],
                         paths)
        return self.layout_fixture(
            {path: f"original {path}\n" for path in paths},
            {path: f"decomposition resolution {path}\n" for path in paths},
            "decomposition-resolution",
            "Exact first-match DFS/ADS, style setter and actual resolution contracts.",
        )

    def test_decomposition_resolution_requires_exact_trusted_adoption(self):
        base, head, entry = self.decomposition_resolution_fixture()
        with patch.object(model_review_hold, "REGISTRY", self.registry([])):
            self.assertEqual(set(model_review_hold.held_changes(self.repository, base, head)),
                             set(entry["paths"]))
        with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
            self.assertEqual(model_review_hold.held_changes(self.repository, base, head), [])

    def test_decomposition_resolution_rejects_each_changed_source_model_or_binding(self):
        base, head, entry = self.decomposition_resolution_fixture()
        for index, path in enumerate(entry["paths"]):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"changed-decomposition-{index}", head)
                self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_decomposition_resolution_does_not_authorize_other_models_or_controls(self):
        base, head, entry = self.decomposition_resolution_fixture()
        for index, path in enumerate((
            "src/codestream.rs", "src/codestream/tiles.rs", "src/codestream/layout.rs",
            "src/codestream/image_header.rs", "src/codestream/packet_headers.rs",
            "src/error.rs", "specs/packet_input.rs", "specs/new.rs", "proofs/new.rs",
            "validation/resource_benchmarks.py", "validation/generate-proof-coverage.py",
            "validation/check-model-review-hold.py", "Cargo.toml", "Cargo.lock",
            "rust-toolchain.toml", ".github/workflows/verus.yml",
        )):
            with self.subTest(path=path):
                self.git("checkout", "-b", f"extra-decomposition-{index}", head)
                self.write(path, "unapproved extra change\n")
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertIn(path, model_review_hold.held_changes(
                        self.repository, base, self.commit()))

    def test_decomposition_resolution_rejects_expansion_and_incomplete_records(self):
        _, _, original = self.decomposition_resolution_fixture()
        for path in ("src/error.rs", "src/codestream/tiles.rs", "specs/new.rs",
                     "validation/check-model-review-hold.py"):
            with self.subTest(path=path):
                entry = copy.deepcopy(original)
                entry["paths"][path] = entry["paths"].pop("specs/mod.rs")
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))
        for path in original["paths"]:
            with self.subTest(missing=path):
                entry = copy.deepcopy(original)
                del entry["paths"][path]
                with self.assertRaises(ValueError):
                    model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_decomposition_records_reject_even_exact_combined_source(self):
        profile = "decomposition-resolution"
        resolution_paths = model_review_hold.AMENDMENT_PROFILES[profile]
        for other_profile in ("component-depth-registration", "tile-component-style-cache",
                              "tile-packet-admission"):
            with self.subTest(profile=other_profile):
                other_paths = model_review_hold.AMENDMENT_PROFILES[other_profile]
                base, head, resolution = self.layout_fixture(
                    {path: f"original {path}\n" for path in resolution_paths | other_paths},
                    {path: f"combined source {path}\n" for path in resolution_paths | other_paths},
                    profile, "Exact combined source must remain held.",
                )
                entries = []
                for name, paths in ((profile, resolution_paths), (other_profile, other_paths)):
                    entries.append(dict(
                        resolution, id=f"combined-{name}", profile=name, source_head=head,
                        paths={
                            path: {"before": self.git("rev-parse", f"{base}:{path}"),
                                   "after": self.git("rev-parse", f"{head}:{path}")}
                            for path in paths
                        },
                    ))
                registry = self.registry(entries)
                self.assertEqual(len(model_review_hold.read_reviewed_amendments(registry)), 2)
                with patch.object(model_review_hold, "REGISTRY", registry):
                    self.assertTrue(model_review_hold.held_changes(self.repository, base, head))

    def main_and_sot_profiles(self):
        return {
            "main-component-finalization": {
                "src/codestream/layout.rs", "src/codestream/coding_style.rs",
                "src/codestream/quantization.rs", "src/codestream/proof_support.rs",
                "src/codestream/tests.rs", "specs/mod.rs", "validation/framework.py",
                "validation/normative-coverage.json", "validation/tests/test_framework.py",
            },
            "sot-reader-marker": {
                "src/codestream/tiles.rs", "src/codestream/reader.rs",
                "src/codestream/proof_support.rs", "src/codestream/tests.rs", "specs/mod.rs",
                "validation/framework.py", "validation/normative-coverage.json",
                "validation/tests/test_framework.py",
            },
        }

    def main_or_sot_fixture(self, profile):
        paths = self.main_and_sot_profiles()[profile]
        self.assertEqual(model_review_hold.AMENDMENT_PROFILES[profile], paths)
        return self.layout_fixture(
            {path: f"original {path}\n" for path in paths},
            {path: f"producer result {path}\n" for path in paths},
            profile, "Exact source-derived main finalization or SOT reader contracts.",
        )

    def test_main_and_sot_profiles_require_exact_trusted_adoption(self):
        for profile in self.main_and_sot_profiles():
            with self.subTest(profile=profile):
                base, head, entry = self.main_or_sot_fixture(profile)
                with patch.object(model_review_hold, "REGISTRY", self.registry([])):
                    self.assertEqual(set(model_review_hold.held_changes(
                        self.repository, base, head)), set(entry["paths"]))
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertEqual(model_review_hold.held_changes(
                        self.repository, base, head), [])

    def test_main_and_sot_profiles_reject_each_changed_identity(self):
        for profile in self.main_and_sot_profiles():
            base, head, entry = self.main_or_sot_fixture(profile)
            for index, path in enumerate(entry["paths"]):
                with self.subTest(profile=profile, path=path):
                    self.git("checkout", "-b", f"changed-{profile}-{index}", head)
                    self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                    with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                        self.assertIn(path, model_review_hold.held_changes(
                            self.repository, base, self.commit()))

    def test_main_and_sot_profiles_reject_other_sources_and_controls(self):
        extras = (
            "src/codestream.rs", "src/error.rs", "src/codestream/layout.rs",
            "src/codestream/quantization.rs", "src/codestream/tiles.rs",
            "src/codestream/reader.rs", "src/codestream/extensions.rs",
            "specs/packet_input.rs", "specs/new.rs", "proofs/new.rs",
            "validation/resource_benchmarks.py", "validation/generate-proof-coverage.py",
            "validation/check-model-review-hold.py", "Cargo.toml", "Cargo.lock",
            "rust-toolchain.toml", ".github/workflows/verus.yml",
        )
        for profile in self.main_and_sot_profiles():
            base, head, entry = self.main_or_sot_fixture(profile)
            for index, path in enumerate(extras):
                if path in entry["paths"]:
                    continue
                with self.subTest(profile=profile, path=path):
                    self.git("checkout", "-b", f"extra-{profile}-{index}", head)
                    self.write(path, f"unapproved extra change {profile}\n")
                    with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                        self.assertIn(path, model_review_hold.held_changes(
                            self.repository, base, self.commit()))

    def test_main_and_sot_profiles_reject_incomplete_or_expanded_records(self):
        for profile in self.main_and_sot_profiles():
            _, _, original = self.main_or_sot_fixture(profile)
            for path in original["paths"]:
                with self.subTest(profile=profile, missing=path):
                    entry = copy.deepcopy(original)
                    del entry["paths"][path]
                    with self.assertRaises(ValueError):
                        model_review_hold.read_reviewed_amendments(self.registry([entry]))
            for path in ("src/error.rs", "specs/new.rs", "validation/check-model-review-hold.py"):
                with self.subTest(profile=profile, expanded=path):
                    entry = copy.deepcopy(original)
                    entry["paths"][path] = copy.deepcopy(entry["paths"]["specs/mod.rs"])
                    with self.assertRaises(ValueError):
                        model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_main_and_sot_profiles_reject_exactly_bound_combined_sources(self):
        profiles = self.main_and_sot_profiles()
        for profile, paths in profiles.items():
            others = set(profiles) | {"component-depth-registration", "decomposition-resolution",
                                      "tile-component-style-cache", "tile-packet-admission"}
            for other in others - {profile}:
                with self.subTest(profile=profile, other=other):
                    other_paths = model_review_hold.AMENDMENT_PROFILES[other]
                    base, head, template = self.layout_fixture(
                        {path: f"original {path}\n" for path in paths | other_paths},
                        {path: f"combined {path}\n" for path in paths | other_paths},
                        profile, "Two individually exact records must not admit combined source.",
                    )
                    entries = [
                        dict(template, id=f"combined-{name}", profile=name, source_head=head,
                             paths={
                                 path: {"before": self.git("rev-parse", f"{base}:{path}"),
                                        "after": self.git("rev-parse", f"{head}:{path}")}
                                 for path in scope
                             })
                        for name, scope in ((profile, paths), (other, other_paths))
                    ]
                    registry = self.registry(entries)
                    self.assertEqual(len(model_review_hold.read_reviewed_amendments(registry)), 2)
                    with patch.object(model_review_hold, "REGISTRY", registry):
                        self.assertTrue(model_review_hold.held_changes(self.repository, base, head))

    def input_producer_profiles(self):
        return {
            "tile-data-window": {
                "src/codestream/tiles.rs", "src/codestream/proof_support.rs",
                "src/codestream/tests.rs", "specs/packet_input.rs", "validation/framework.py",
                "validation/normative-coverage.json", "validation/tests/test_framework.py",
            },
            "layout-prologue": {
                "src/codestream/layout.rs", "src/codestream/proof_support.rs",
                "src/codestream/tests.rs", "specs/layout_input.rs", "specs/mod.rs",
                "validation/framework.py", "validation/normative-coverage.json",
                "validation/tests/test_framework.py", "validation/expected-package-files.txt",
            },
        }

    def input_producer_fixture(self, profile):
        paths = self.input_producer_profiles()[profile]
        self.assertEqual(model_review_hold.AMENDMENT_PROFILES[profile], paths)
        originals = {path: f"original {path}\n" for path in paths
                     if path != "specs/layout_input.rs"}
        return self.layout_fixture(
            originals, {path: f"producer result {path}\n" for path in paths},
            profile, "Exact source-derived tile window or layout prologue contracts.",
        )

    def test_input_producer_profiles_require_exact_trusted_adoption(self):
        for profile in self.input_producer_profiles():
            with self.subTest(profile=profile):
                base, head, entry = self.input_producer_fixture(profile)
                if profile == "layout-prologue":
                    self.assertIsNone(entry["paths"]["specs/layout_input.rs"]["before"])
                with patch.object(model_review_hold, "REGISTRY", self.registry([])):
                    self.assertEqual(set(model_review_hold.held_changes(
                        self.repository, base, head)), set(entry["paths"]))
                with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                    self.assertEqual(model_review_hold.held_changes(
                        self.repository, base, head), [])

    def test_input_producer_profiles_reject_each_changed_identity(self):
        for profile in self.input_producer_profiles():
            base, head, entry = self.input_producer_fixture(profile)
            for index, path in enumerate(entry["paths"]):
                with self.subTest(profile=profile, path=path):
                    self.git("checkout", "-b", f"changed-{profile}-{index}", head)
                    self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                    with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                        self.assertIn(path, model_review_hold.held_changes(
                            self.repository, base, self.commit()))

    def test_input_producer_profiles_reject_other_sources_and_controls(self):
        extras = (
            "src/codestream.rs", "src/error.rs", "src/codestream/layout.rs",
            "src/codestream/image_header.rs", "src/codestream/quantization.rs",
            "src/codestream/tiles.rs", "src/codestream/reader.rs",
            "src/codestream/extensions.rs", "specs/mod.rs", "specs/packet_input.rs",
            "specs/layout_input.rs", "specs/new.rs", "proofs/new.rs",
            "validation/resource_benchmarks.py", "validation/generate-proof-coverage.py",
            "validation/check-model-review-hold.py", "Cargo.toml", "Cargo.lock",
            "rust-toolchain.toml", ".github/workflows/verus.yml",
        )
        for profile in self.input_producer_profiles():
            base, head, entry = self.input_producer_fixture(profile)
            for index, path in enumerate(extras):
                if path in entry["paths"]:
                    continue
                with self.subTest(profile=profile, path=path):
                    self.git("checkout", "-b", f"extra-{profile}-{index}", head)
                    self.write(path, f"unapproved extra change {profile}\n")
                    with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                        self.assertIn(path, model_review_hold.held_changes(
                            self.repository, base, self.commit()))

    def test_input_producer_profiles_reject_incomplete_or_expanded_records(self):
        for profile in self.input_producer_profiles():
            _, _, original = self.input_producer_fixture(profile)
            for path in original["paths"]:
                with self.subTest(profile=profile, missing=path):
                    entry = copy.deepcopy(original)
                    del entry["paths"][path]
                    with self.assertRaises(ValueError):
                        model_review_hold.read_reviewed_amendments(self.registry([entry]))
            for path in ("src/error.rs", "specs/new.rs", "validation/check-model-review-hold.py"):
                with self.subTest(profile=profile, expanded=path):
                    entry = copy.deepcopy(original)
                    entry["paths"][path] = copy.deepcopy(entry["paths"]["validation/framework.py"])
                    with self.assertRaises(ValueError):
                        model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_input_producer_profiles_reject_exactly_bound_combined_sources(self):
        for profile, paths in self.input_producer_profiles().items():
            for other, other_paths in model_review_hold.AMENDMENT_PROFILES.items():
                if other == profile:
                    continue
                with self.subTest(profile=profile, other=other):
                    base, head, template = self.layout_fixture(
                        {path: f"original {path}\n" for path in paths | other_paths},
                        {path: f"combined {path}\n" for path in paths | other_paths},
                        profile, "Two individually exact records must not admit combined source.",
                    )
                    entries = [
                        dict(template, id=f"combined-{name}", profile=name, source_head=head,
                             paths={
                                 path: {"before": self.git("rev-parse", f"{base}:{path}"),
                                        "after": self.git("rev-parse", f"{head}:{path}")}
                                 for path in scope
                             })
                        for name, scope in ((profile, paths), (other, other_paths))
                    ]
                    registry = self.registry(entries)
                    self.assertEqual(len(model_review_hold.read_reviewed_amendments(registry)), 2)
                    with patch.object(model_review_hold, "REGISTRY", registry):
                        self.assertTrue(model_review_hold.held_changes(self.repository, base, head))

    @staticmethod
    def execution_profiles():
        return {
            "jpip-effective-progression": {
                "src/jpip/precinct.rs", "src/jpip/tests.rs",
            },
            "validation-python-hash-lock": {
                ".github/workflows/ci.yml", ".github/workflows/copilot-setup-steps.yml",
                ".github/workflows/verus.yml", "validation/requirements.in",
                "validation/requirements.txt",
            },
            "source-observation-inventory": {
                "validation/source_inventory.py", "validation/source-inventory.schema.json",
                "validation/tests/test_source_inventory.py",
            },
        }

    def execution_profile_fixture(self, profile, new_files=False):
        paths = self.execution_profiles()[profile]
        if new_files:
            for path in paths:
                target = self.repository / path
                if target.exists():
                    target.unlink()
        originals = ({"specs/README.md": f"# Original {profile}\n"} if new_files else
                     {path: f"original {path}\n" for path in paths})
        return self.layout_fixture(
            originals, {path: f"proposed {path}\n" for path in paths},
            profile, "Exact execution profile fixture; no real source adoption.",
        )

    def test_execution_profiles_require_exact_scopes_and_trusted_adoption(self):
        expected = self.execution_profiles()
        self.assertEqual(
            {name: model_review_hold.AMENDMENT_PROFILES.get(name) for name in expected},
            expected,
        )
        for profile in expected:
            for new_files in (False, True):
                with self.subTest(profile=profile, new_files=new_files):
                    base, head, entry = self.execution_profile_fixture(profile, new_files)
                    if new_files:
                        self.assertTrue(all(
                            identity["before"] is None for identity in entry["paths"].values()
                        ))
                    with patch.object(model_review_hold, "REGISTRY", self.registry([])):
                        self.assertEqual(set(model_review_hold.held_changes(
                            self.repository, base, head)), set(entry["paths"]))
                    with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                        self.assertEqual(model_review_hold.held_changes(
                            self.repository, base, head), [])

    def test_execution_profiles_reject_missing_or_expanded_records(self):
        for profile in self.execution_profiles():
            _, _, original = self.execution_profile_fixture(profile)
            for path in original["paths"]:
                with self.subTest(profile=profile, missing=path):
                    entry = copy.deepcopy(original)
                    del entry["paths"][path]
                    with self.assertRaises(ValueError):
                        model_review_hold.read_reviewed_amendments(self.registry([entry]))
            for path in ("src/error.rs", "specs/new.rs",
                         "validation/check-model-review-hold.py"):
                with self.subTest(profile=profile, extra=path):
                    entry = copy.deepcopy(original)
                    entry["paths"][path] = copy.deepcopy(next(iter(entry["paths"].values())))
                    with self.assertRaises(ValueError):
                        model_review_hold.read_reviewed_amendments(self.registry([entry]))

    def test_execution_profiles_reject_each_changed_blob_and_executable_mode(self):
        self.git("config", "core.filemode", "false")
        for profile in self.execution_profiles():
            base, head, original = self.execution_profile_fixture(profile)
            for index, path in enumerate(original["paths"]):
                with self.subTest(profile=profile, path=path, kind="before"):
                    entry = copy.deepcopy(original)
                    entry["paths"][path]["before"] = "0" * 40
                    with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                        self.assertEqual(set(model_review_hold.held_changes(
                            self.repository, base, head)), set(original["paths"]))
                for kind in ("after", "mode"):
                    with self.subTest(profile=profile, path=path, kind=kind):
                        self.git("checkout", "-b", f"{profile}-{index}-{kind}", head)
                        if kind == "after":
                            self.write(path, self.git("show", f"{head}:{path}") + "changed\n")
                            changed = self.commit()
                        else:
                            self.git("update-index", "--chmod=+x", path)
                            self.git("commit", "--message", "Executable mode")
                            changed = self.git("rev-parse", "HEAD")
                        with patch.object(model_review_hold, "REGISTRY", self.registry([original])):
                            self.assertEqual(set(model_review_hold.held_changes(
                                self.repository, base, changed)), set(original["paths"]))

    def test_execution_profiles_reject_additional_sources_and_controls(self):
        extras = (
            "src/error.rs", "specs/new.rs", "proofs/new.rs", "Cargo.toml", "Cargo.lock",
            "rust-toolchain.toml", ".github/workflows/model-review-hold.yml",
            "validation/check-model-review-hold.py", "validation/tests/test_model_review_hold.py",
            "validation/resource_benchmarks.py", "validation/generate-proof-coverage.py",
        )
        for profile in self.execution_profiles():
            base, head, entry = self.execution_profile_fixture(profile)
            for index, path in enumerate(extras):
                with self.subTest(profile=profile, path=path):
                    self.git("checkout", "-b", f"{profile}-extra-{index}", head)
                    self.write(path, f"unapproved {profile} {path}\n")
                    with patch.object(model_review_hold, "REGISTRY", self.registry([entry])):
                        self.assertIn(path, model_review_hold.held_changes(
                            self.repository, base, self.commit()))

    def test_execution_profiles_reject_incomparable_combined_records(self):
        for profile, paths in self.execution_profiles().items():
            for other, other_paths in model_review_hold.AMENDMENT_PROFILES.items():
                combined = paths | other_paths
                if combined == paths or combined == other_paths:
                    continue
                with self.subTest(profile=profile, other=other):
                    base, head, template = self.layout_fixture(
                        {path: f"original {path}\n" for path in combined},
                        {path: f"combined {path}\n" for path in combined},
                        profile, "Two exact subset records cannot authorize their union.",
                    )
                    entries = [
                        dict(template, id=f"union-{name}", profile=name, paths={
                            path: {"before": self.git("rev-parse", f"{base}:{path}"),
                                   "after": self.git("rev-parse", f"{head}:{path}")}
                            for path in scope
                        })
                        for name, scope in ((profile, paths), (other, other_paths))
                    ]
                    registry = self.registry(entries)
                    self.assertEqual(len(model_review_hold.read_reviewed_amendments(registry)), 2)
                    with patch.object(model_review_hold, "REGISTRY", registry):
                        self.assertEqual(set(model_review_hold.held_changes(
                            self.repository, base, head)), combined)

    def test_execution_profiles_cannot_use_candidate_written_registry(self):
        for profile in self.execution_profiles():
            base, _, entry = self.execution_profile_fixture(profile)
            self.write("validation/reviewed-amendments.md",
                       "```json\n" + json.dumps({
                           "schema_version": 1, "amendments": [entry],
                       }) + "\n```\n")
            with patch.object(model_review_hold, "REGISTRY", self.registry([])):
                self.assertEqual(set(model_review_hold.held_changes(
                    self.repository, base, self.commit())), set(entry["paths"]))

    def test_invalid_trusted_registry_causes_explicit_cli_failure(self):
        self.write("src/lib.rs", "pub fn changed() {}\n")
        head = self.commit()
        with tempfile.TemporaryDirectory(prefix="jpeg2000-controller-cli-") as directory:
            controller = Path(directory) / "validation/check-model-review-hold.py"
            controller.parent.mkdir()
            controller.write_text(CONTROLLER.read_text(), encoding="utf-8")
            result = subprocess.run(
                [sys.executable, str(controller), "--repository", str(self.repository),
                 self.base, head], capture_output=True, text=True,
            )
        self.assertEqual(result.returncode, 2)
        self.assertIn("trusted amendment registry must be a regular file", result.stderr)


if __name__ == "__main__":
    unittest.main()
