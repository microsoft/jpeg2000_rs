import copy
import hashlib
import importlib.util
import io
import json
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from urllib.error import HTTPError


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("release_check", ROOT / "validation/check-release.py")
release = None
if sys.version_info >= (3, 11):
    release = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(release)


@unittest.skipIf(release is None, "publication tooling requires Python 3.11+")
class ReleaseTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="jpeg2000-release-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "--initial-branch=release/0.1")
        self.git("config", "user.name", "Release fixture")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("config", "core.autocrlf", "false")
        self.manifest = (
            '[package]\nname="jpeg2000-decoder"\nversion="0.1.1"\n'
            'rust-version="1.88.0"\npublish=["crates-io"]\n'
        ).encode()
        self.files = {
            ".gitignore": b"target/\n",
            "Cargo.toml": self.manifest,
            "src/lib.rs": b"pub fn fixture() {}\n",
            "specs/mod.rs": b"// selected model fixture\n",
            "proofs/mod.rs": b"// selected proof fixture\n",
        }
        for name, data in self.files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.git("add", "--all")
        self.git("commit", "-m", "Qualified fixture")
        self.commit = self.git("rev-parse", "HEAD")
        self.tree = self.git("rev-parse", "HEAD^{tree}")
        self.git("tag", "v0.1.1")
        self.head = "b" * 40
        self.checks = {}
        self.runs = {}
        for index, (commit, event) in enumerate(((self.head, "pull_request"), (self.commit, "push"))):
            entries = []
            for number, (name, workflow) in enumerate(release.REQUIRED_CHECKS.items()):
                if event == "push" and workflow is None:
                    continue
                run_id = 100 + index * 10 + (1 if workflow == "verus" else 0)
                entries.append({
                    "id": index * 1000 + number, "name": name, "head_sha": commit,
                    "status": "completed", "conclusion": "success",
                    "app": {"id": 15368 if workflow else 95686,
                            "slug": "github-actions" if workflow else "microsoft-github-policy-service"},
                    "details_url": f"https://github.com/{release.REPOSITORY}/actions/runs/{run_id}/job/50",
                    "check_suite": {"id": run_id},
                })
                if workflow:
                    self.runs[str(run_id)] = {
                        "id": run_id, "repository": {"full_name": release.REPOSITORY},
                        "head_sha": commit, "path": f".github/workflows/{workflow}.yml",
                        "head_branch": "release/0.1" if event == "push" else "release-preparation",
                        "event": event, "check_suite_id": run_id,
                        "status": "completed", "conclusion": "success",
                    }
            self.checks[commit] = entries

    def git(self, *arguments):
        return subprocess.check_output(
            ["git", "-C", str(self.root), *arguments], text=True, stderr=subprocess.PIPE,
        ).strip()

    def api(self, endpoint):
        if "/check-runs?" in endpoint:
            commit = endpoint.split("/commits/")[1].split("/")[0]
            return {"check_runs": copy.deepcopy(self.checks[commit])}
        if "/actions/runs?head_sha=" in endpoint:
            commit = endpoint.split("head_sha=")[1].split("&")[0]
            return {"workflow_runs": [copy.deepcopy(r) for r in self.runs.values()
                                     if r["head_sha"] == commit]}
        if "/actions/runs/" in endpoint:
            return copy.deepcopy(self.runs[endpoint.rsplit("/", 1)[1]])
        if endpoint.endswith("/pulls/7"):
            return {"number": 7, "merged": True, "merge_commit_sha": self.commit,
                    "head": {"sha": self.head, "ref": "release-preparation"}}
        if "/git/commits/" in endpoint:
            return {"sha": self.head, "tree": {"sha": self.tree}}
        if "/pulls?" in endpoint:
            return [{"number": 7, "merged_at": "2026-11-15T00:00:00Z",
                     "merge_commit_sha": self.commit,
                     "base": {"ref": "release/0.1", "repo": {"full_name": release.REPOSITORY}}}]
        raise AssertionError(endpoint)

    def test_only_matching_manual_release_branch_requests_are_admitted(self):
        args = [release.REPOSITORY, "workflow_dispatch", "refs/heads/release/0.1",
                "v0.1.1", "dry-run", "", ""]
        self.assertEqual(release.validate_request(*args), "release/0.1")
        for index, value in [(0, "telecos/jpeg2000_rs"), (1, "push"), (1, "release"),
                             (2, "refs/heads/main"), (2, "refs/tags/release/0.1"),
                             (2, "refs/heads/release/0.2"), (3, "v0.1.1\n"),
                             (3, "v00.1.1"), (3, "v0.1.1;echo bad")]:
            with self.subTest(value=value):
                bad = args.copy()
                bad[index] = value
                with self.assertRaises(ValueError):
                    release.validate_request(*bad)
        args[4] = "publish"
        with self.assertRaisesRegex(ValueError, "owner-approved"):
            release.validate_request(*args)
        args[5:] = [self.commit, "a" * 64]
        self.assertEqual(release.validate_request(*args), "release/0.1")

    def test_main_cli_rejects_before_network_or_packaging_and_removes_stale_receipt(self):
        output = self.root / "receipt.json"
        output.write_text('{"stale":true}')
        result = subprocess.run([
            sys.executable, str(ROOT / "validation/check-release.py"), "source",
            "--repository", release.REPOSITORY, "--event", "workflow_dispatch",
            "--ref", "refs/heads/main", "--tag", "v0.1.1", "--output", str(output),
        ], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("never main or a tag", result.stderr)
        self.assertFalse(output.exists())

    def test_false_or_unrestricted_publication_manifests_are_rejected(self):
        for publish in (False, True, None, [], ["other-registry"], ["crates-io", "other"]):
            with self.subTest(publish=publish), self.assertRaises(ValueError):
                release.check_manifest({"package": {"name": release.PACKAGE, "version": "0.1.1",
                                                    "rust-version": "1.88.0",
                                                    "publish": publish}}, "0.1.1")

    def test_tag_requires_merged_reviewed_tree_and_both_exact_source_qualifications(self):
        with patch.object(release, "remote_tag", return_value=self.commit):
            result = release.validate_source(self.root, "release/0.1", self.commit,
                                             "v0.1.1", self.commit, api=self.api)
            self.assertEqual(result["commit"], self.commit)
            self.assertEqual(result["verus_run_id"], 111)
            with self.assertRaisesRegex(ValueError, "one merged PR"):
                release.validate_source(self.root, "release/0.2", self.commit,
                                        "v0.1.1", api=self.api)
            with self.assertRaisesRegex(ValueError, "approved immutable"):
                release.validate_source(self.root, "release/0.1", self.commit,
                                        "v0.1.1", "c" * 40, api=self.api)
            with self.assertRaisesRegex(ValueError, "selected release-branch commit"):
                release.validate_source(self.root, "release/0.1", "c" * 40,
                                        "v0.1.1", api=self.api)
            self.tree = "d" * 40
            with self.assertRaisesRegex(ValueError, "reviewed PR tree"):
                release.validate_source(self.root, "release/0.1", self.commit,
                                        "v0.1.1", api=self.api)
        with patch.object(release, "remote_tag", return_value="e" * 40):
            with self.assertRaisesRegex(ValueError, "absent or moved"):
                release.validate_source(self.root, "release/0.1", self.commit,
                                        "v0.1.1", api=self.api)

    def test_failed_pending_and_missing_checks_are_distinct(self):
        check = self.checks[self.commit][0]
        check["status"], check["conclusion"] = "in_progress", None
        with self.assertRaises(release.ChecksPending):
            release.validate_checks(self.commit, "integrated", "release/0.1", self.api)
        check["status"], check["conclusion"] = "completed", "failure"
        with self.assertRaisesRegex(ValueError, "did not succeed"):
            release.validate_checks(self.commit, "integrated", "release/0.1", self.api)
        self.checks[self.commit].pop(0)
        with self.assertRaisesRegex(ValueError, "missing required"):
            release.validate_checks(self.commit, "integrated", "release/0.1", self.api)

    def test_wrong_issuer_event_source_run_and_suite_cannot_satisfy_qualification(self):
        for field, value in [("event", "workflow_dispatch"), ("head_sha", "c" * 40),
                             ("head_branch", "main"),
                             ("path", ".github/workflows/fake.yml"), ("check_suite_id", 999)]:
            with self.subTest(field=field):
                original = self.runs["110"][field]
                self.runs["110"][field] = value
                with self.assertRaisesRegex(ValueError, "qualification producer"):
                    release.validate_checks(self.commit, "integrated", "release/0.1", self.api)
                self.runs["110"][field] = original
        self.checks[self.commit][0]["app"]["id"] = 1
        with self.assertRaisesRegex(ValueError, "issuer"):
            release.validate_checks(self.commit, "integrated", "release/0.1", self.api)

    def test_actual_archive_binding_and_approved_hash_are_required(self):
        package = self.root / "target/package/jpeg2000-decoder-0.1.1"
        package.mkdir(parents=True)
        archive = package.parent / (package.name + ".crate")
        members = {k: v for k, v in self.files.items() if k != ".gitignore"}
        members.update({
            "Cargo.toml.orig": self.manifest,
            ".cargo_vcs_info.json": json.dumps({"git": {"sha1": self.commit},
                                              "path_in_vcs": ""}).encode(),
        })
        with tarfile.open(archive, "w:gz") as packed:
            for name, data in members.items():
                path = package / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                info = tarfile.TarInfo(package.name + "/" + name)
                info.size = len(data)
                packed.addfile(info, io.BytesIO(data))
        checker = release.archive_checker()
        checksum = hashlib.sha256(archive.read_bytes()).hexdigest()
        with patch.object(release, "remote_tag", return_value=self.commit), \
                patch.object(release, "archive_checker", return_value=checker), \
                patch.object(checker, "package_paths", return_value=(package, archive)):
            self.assertEqual(release.verify_archive(self.root, "v0.1.1", self.commit,
                                                    checksum)[0], checksum)
            with self.assertRaisesRegex(ValueError, "SHA256"):
                release.verify_archive(self.root, "v0.1.1", self.commit, "0" * 64)
            (package / "src/lib.rs").write_text("pub fn changed() {}\n")
            with self.assertRaisesRegex(ValueError, "differs from its archive"):
                release.verify_archive(self.root, "v0.1.1", self.commit, checksum)

    def test_only_registry_404_means_absent_and_existing_versions_must_match(self):
        checksum = "a" * 64
        with patch.object(release, "request", side_effect=HTTPError("test", 404, "", {}, None)):
            self.assertTrue(release.registry_state("0.1.1", checksum)["publish_needed"])
        with patch.object(release, "request", side_effect=HTTPError("test", 403, "", {}, None)):
            with self.assertRaises(HTTPError):
                release.registry_state("0.1.1", checksum)
        entry = {"crate": release.PACKAGE, "num": "0.1.1", "checksum": checksum, "yanked": False}
        with patch.object(release, "request", side_effect=lambda url: json.dumps({"version": entry}).encode()):
            result = release.registry_state("0.1.1", checksum)
            self.assertEqual(result["registry_status"], "verified_existing_identical")
            self.assertFalse(result["publish_needed"])
            entry["yanked"] = True
            with self.assertRaisesRegex(ValueError, "differs"):
                release.registry_state("0.1.1", checksum)

    def test_qualified_ci_artifact_must_match_both_source_and_archive(self):
        data = b"qualified archive bytes"
        checksum = hashlib.sha256(data).hexdigest()

        def download(*args, **kwargs):
            destination = self.root / "target/release-validation/qualification"
            destination.mkdir(parents=True)
            (destination / "jpeg2000-decoder-0.1.1.crate").write_bytes(data)
            (destination / "packaged-source-inputs.json").write_text(json.dumps({
                "source_commit": self.commit, "archive_sha256": checksum,
            }))

        with patch.object(release.subprocess, "run", side_effect=download):
            release.verify_qualification(self.root, self.commit, "0.1.1", 111, checksum)
        with self.assertRaisesRegex(ValueError, "fresh"):
            release.verify_qualification(self.root, self.commit, "0.1.1", 111, checksum)

    def test_artifact_from_another_source_is_not_qualification(self):
        data = b"qualified archive bytes"
        checksum = hashlib.sha256(data).hexdigest()

        def download(*args, **kwargs):
            destination = self.root / "target/release-validation/qualification"
            destination.mkdir(parents=True)
            (destination / "jpeg2000-decoder-0.1.1.crate").write_bytes(data)
            (destination / "packaged-source-inputs.json").write_text(json.dumps({
                "source_commit": "c" * 40, "archive_sha256": checksum,
            }))

        with patch.object(release.subprocess, "run", side_effect=download):
            with self.assertRaisesRegex(ValueError, "actual CI-qualified archive"):
                release.verify_qualification(self.root, self.commit, "0.1.1", 111, checksum)


if __name__ == "__main__":
    unittest.main()
