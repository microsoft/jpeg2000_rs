"""Python 3.11+ release-branch provenance and archive checks; never uploads."""

import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen


REPOSITORY = "microsoft/jpeg2000_rs"
PACKAGE = "jpeg2000-decoder"
SHA = re.compile(r"[0-9a-f]{40}")
DIGEST = re.compile(r"[0-9a-f]{64}")
TAG = re.compile(r"v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)")
REQUIRED_CHECKS = {
    **{f"Test ({platform})": "ci" for platform in
       ("ubuntu-latest", "macos-latest", "windows-latest")},
    **{f"Native numerical ({platform})": "ci" for platform in
       ("ubuntu-latest", "macos-latest", "windows-latest")},
    "Minimum supported Rust (1.88.0)": "ci",
    "Quality and package audit": "ci",
    "Generated decoder validation": "ci",
    "verify": "verus",
    "license/cla": None,
}


def git(root, *arguments):
    return subprocess.check_output(["git", "-C", str(root), *arguments], text=True).strip()


def github(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint], text=True))


def pages(endpoint, field=None, api=github):
    entries = []
    for page in range(1, 11):
        response = api(f"{endpoint}?per_page=100&page={page}")
        batch = response[field] if field else response
        if not isinstance(batch, list):
            raise ValueError("invalid GitHub pagination response")
        entries.extend(batch)
        if len(batch) < 100:
            return entries
    raise ValueError("release metadata exceeds bounded pagination")


def validate_request(repository, event, ref, tag, mode, approved_commit, approved_sha256):
    match = TAG.fullmatch(tag)
    if repository != REPOSITORY or event != "workflow_dispatch":
        raise ValueError("only a manual upstream-repository request is allowed")
    if match is None or ref != f"refs/heads/release/{match[1]}.{match[2]}":
        raise ValueError("select the matching release/MAJOR.MINOR branch, never main or a tag")
    if mode not in ("dry-run", "publish"):
        raise ValueError("unknown release mode")
    if approved_commit and not SHA.fullmatch(approved_commit):
        raise ValueError("approved commit must be a full lowercase SHA")
    if approved_sha256 and not DIGEST.fullmatch(approved_sha256):
        raise ValueError("approved archive must be a SHA256 digest")
    if mode == "publish" and not (approved_commit and approved_sha256):
        raise ValueError("publication requires the owner-approved commit and archive SHA256")
    return ref.removeprefix("refs/heads/")


def check_manifest(document, version):
    package = document["package"]
    if (package["name"] != PACKAGE or package["version"] != version
            or package.get("rust-version") != "1.88.0"
            or package.get("publish") != ["crates-io"]):
        raise ValueError("expected matching version, MSRV and explicit crates.io-only publication")


class ChecksPending(ValueError):
    pass


def validate_checks(commit, phase, expected_branch, api=github):
    expected = set(REQUIRED_CHECKS)
    if phase == "integrated":
        expected.remove("license/cla")
    elif phase != "pull_request":
        raise ValueError("unknown qualification phase")
    checks = {}
    for check in pages(f"repos/{REPOSITORY}/commits/{commit}/check-runs", "check_runs", api):
        name = check["name"]
        if name in expected and (name not in checks or check["id"] > checks[name]["id"]):
            checks[name] = check
    event = "push" if phase == "integrated" else "pull_request"
    runs = {}
    pending = []
    for name in sorted(expected & checks.keys()):
        check = checks[name]
        if (check["head_sha"] != commit
                or check["status"] not in ("queued", "in_progress", "completed")
                or (check["status"] == "completed" and check["conclusion"] != "success")):
            raise ValueError(f"{phase}: check did not succeed: {name}")
        workflow = REQUIRED_CHECKS[name]
        app = check["app"]
        if workflow is None:
            if app["id"] != 95686 or app["slug"] != "microsoft-github-policy-service":
                raise ValueError("unexpected CLA issuer")
        else:
            if app["id"] != 15368 or app["slug"] != "github-actions":
                raise ValueError(f"unexpected check issuer: {name}")
            match = re.fullmatch(
                rf"https://github\.com/{REPOSITORY}/actions/runs/([0-9]+)/job/[0-9]+",
                check["details_url"],
            )
            if match is None:
                raise ValueError("unexpected qualification run URL")
            run_id = match[1]
            if run_id not in runs:
                runs[run_id] = api(f"repos/{REPOSITORY}/actions/runs/{run_id}")
            run = runs[run_id]
            if (run["repository"]["full_name"] != REPOSITORY or run["head_sha"] != commit
                    or run["head_branch"] != expected_branch
                    or run["path"] != f".github/workflows/{workflow}.yml"
                    or run["event"] != event or run["check_suite_id"] != check["check_suite"]["id"]
                    or run["status"] not in ("queued", "in_progress", "completed")
                    or (run["status"] == "completed" and run["conclusion"] != "success")):
                raise ValueError(f"wrong or unsuccessful qualification producer: {name}")
            if run["status"] != "completed":
                pending.append(f"workflow {workflow}")
        if check["status"] != "completed":
            pending.append(name)
    missing = expected - checks.keys()
    if missing:
        producers = api(
            f"repos/{REPOSITORY}/actions/runs?head_sha={commit}&event={event}&per_page=100"
        )["workflow_runs"]
        for name in missing:
            workflow = REQUIRED_CHECKS[name]
            matches = [run for run in producers if workflow is not None
                       and run["repository"]["full_name"] == REPOSITORY
                       and run["head_sha"] == commit and run["event"] == event
                       and run["head_branch"] == expected_branch
                       and run["path"] == f".github/workflows/{workflow}.yml"]
            if not matches or max(matches, key=lambda run: run["id"])["status"] not in (
                    "queued", "in_progress"):
                raise ValueError(f"{phase}: missing required check/producer: {name}")
            pending.append(name)
    if pending:
        raise ChecksPending(f"{phase}: pending qualification: {sorted(set(pending))}")
    return {
        "commit": commit,
        "check_ids": [checks[name]["id"] for name in sorted(expected)],
        "verus_run_id": int(re.search(r"/runs/([0-9]+)/", checks["verify"]["details_url"])[1]),
    }


def await_checks(commit, phase, expected_branch, deadline, api=github):
    while True:
        try:
            return validate_checks(commit, phase, expected_branch, api)
        except ChecksPending as error:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise ValueError(f"qualification wait deadline reached: {error}") from error
            print(str(error), file=sys.stderr, flush=True)
            time.sleep(min(60, remaining))


def remote_tag(root, tag):
    refs = dict(line.split()[::-1] for line in git(
        root, "ls-remote", "--tags", f"https://github.com/{REPOSITORY}.git",
        f"refs/tags/{tag}", f"refs/tags/{tag}^{{}}",
    ).splitlines())
    return refs.get(f"refs/tags/{tag}^{{}}", refs.get(f"refs/tags/{tag}"))


def validate_source(root, branch, branch_commit, tag, approved_commit="", wait=False, api=github):
    if not SHA.fullmatch(branch_commit):
        raise ValueError("dispatch branch commit must be an immutable SHA")
    commit = git(root, "rev-parse", "--verify", f"refs/tags/{tag}^{{commit}}")
    if not SHA.fullmatch(commit) or (approved_commit and commit != approved_commit):
        raise ValueError("tag differs from the approved immutable candidate")
    if commit != branch_commit or git(root, "rev-parse", "HEAD") != branch_commit:
        raise ValueError("tag must equal the selected release-branch commit")
    if remote_tag(root, tag) != commit:
        raise ValueError("remote release tag is absent or moved")
    check_manifest(tomllib.loads(git(root, "show", f"{commit}:Cargo.toml")), tag[1:])
    associated = pages(f"repos/{REPOSITORY}/commits/{commit}/pulls", api=api)
    matches = [pr for pr in associated if pr["merge_commit_sha"] == commit and pr["merged_at"]
               and pr["base"]["ref"] == branch
               and pr["base"]["repo"]["full_name"] == REPOSITORY]
    if len(matches) != 1:
        raise ValueError("tag must identify one merged PR integration into the selected release branch")
    pr = api(f"repos/{REPOSITORY}/pulls/{matches[0]['number']}")
    if not pr["merged"] or pr["merge_commit_sha"] != commit:
        raise ValueError("release PR identity changed")
    head = pr["head"]["sha"]
    if not SHA.fullmatch(head):
        raise ValueError("invalid reviewed PR head")
    reviewed = api(f"repos/{REPOSITORY}/git/commits/{head}")
    if (reviewed["sha"] != head
            or reviewed["tree"]["sha"] != git(root, "rev-parse", f"{commit}^{{tree}}")):
        raise ValueError("integrated source differs from the reviewed PR tree")
    deadline = time.monotonic() + (105 * 60 if wait else 0)
    pull_checks = await_checks(head, "pull_request", pr["head"]["ref"], deadline, api)
    integrated = await_checks(commit, "integrated", branch, deadline, api)
    return {"tag": tag, "version": tag[1:], "commit": commit, "release_branch": branch,
            "pull_request": pr["number"], "pull_request_checks": pull_checks,
            "integrated_checks": integrated, "verus_run_id": integrated["verus_run_id"]}


def archive_checker():
    path = Path(__file__).with_name("check-packaged-source.py")
    spec = importlib.util.spec_from_file_location("release_packaged_source", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify_archive(root, tag, commit, expected=""):
    if not SHA.fullmatch(commit) or (expected and not DIGEST.fullmatch(expected)):
        raise ValueError("invalid candidate/checksum")
    if git(root, "rev-parse", "HEAD") != commit or remote_tag(root, tag) != commit:
        raise ValueError("checkout or remote tag differs from the approved source")
    check_manifest(tomllib.loads((root / "Cargo.toml").read_text()), tag[1:])
    checker = archive_checker()
    package, archive = checker.package_paths(root)
    if archive.stat().st_size > 32 * 1024 * 1024:
        raise ValueError("release archive exceeds the compressed size limit")
    with tarfile.open(archive, "r:gz") as packed:
        entries = packed.getmembers()
        if len(entries) > 4096 or sum(entry.size for entry in entries) > 64 * 1024 * 1024:
            raise ValueError("release archive exceeds bounded inventory limits")
    binding = checker.snapshot(root, package, archive)
    if expected and binding["archive_sha256"] != expected:
        raise ValueError("archive differs from the approved/qualified SHA256")
    return binding["archive_sha256"], archive


def verify_qualification(root, commit, version, run_id, checksum):
    destination = root / "target/release-validation/qualification"
    if destination.exists():
        raise ValueError("qualification download directory must be fresh")
    subprocess.run(["gh", "run", "download", str(run_id), "--repo", REPOSITORY,
                    "--name", "packaged-verus-validation", "--dir", str(destination)], check=True)
    archives = list(destination.rglob(f"{PACKAGE}-{version}.crate"))
    bindings = list(destination.rglob("packaged-source-inputs.json"))
    if len(archives) != 1 or len(bindings) != 1:
        raise ValueError("expected one exact archive and input binding from the qualified Verus run")
    binding = json.loads(bindings[0].read_text())
    if (binding["source_commit"] != commit or binding["archive_sha256"] != checksum
            or hashlib.sha256(archives[0].read_bytes()).hexdigest() != checksum):
        raise ValueError("publication archive differs from the actual CI-qualified archive")


def request(url, limit=2 * 1024 * 1024):
    with urlopen(Request(url, headers={"User-Agent": f"{PACKAGE}-release-check"}), timeout=30) as reply:
        data = reply.read(limit + 1)
        if len(data) > limit:
            raise ValueError("registry response exceeds bounded size")
        return data


def registry_state(version, checksum, require=False):
    if not TAG.fullmatch("v" + version) or not DIGEST.fullmatch(checksum):
        raise ValueError("invalid registry version/checksum")
    deadline = time.monotonic() + 90
    while True:
        try:
            entry = json.loads(request(f"https://crates.io/api/v1/crates/{PACKAGE}/{version}"))["version"]
            break
        except HTTPError as error:
            if error.code != 404:
                raise
            if not require:
                return {"registry_status": "not_published", "publish_needed": True}
            if time.monotonic() >= deadline:
                raise ValueError("published version not visible before deadline") from error
            time.sleep(3)
    if (entry["crate"] != PACKAGE or entry["num"] != version
            or entry["checksum"] != checksum or entry["yanked"] is not False):
        raise ValueError("registry version differs from the approved archive or is yanked")
    return {"registry_status": "verified_existing_identical", "publish_needed": False}


def verify_registry_consumer(root, version, checksum):
    with tempfile.TemporaryDirectory(prefix="jpeg2000-registry-consumer-") as directory:
        consumer = Path(directory)
        (consumer / "src").mkdir()
        (consumer / "Cargo.toml").write_text(
            '[package]\nname="registry-consumer"\nversion="0.0.0"\nedition="2021"\n'
            f'[workspace]\n[dependencies]\n{PACKAGE}={{version="={version}",default-features=false}}\n'
        )
        (consumer / "src/gray.jp2").write_bytes(
            (root / "validation/image-consumer-probe/tests/fixtures/gray.jp2").read_bytes()
        )
        (consumer / "src/main.rs").write_text(
            'use jpeg2000_decoder::{DecodeOptions,decode_jp2_color};\n'
            'fn main(){let i=decode_jp2_color(include_bytes!("gray.jp2"),'
            '&DecodeOptions::default()).unwrap();assert_eq!((i.width(),i.height()),(1,1));'
            'assert_eq!(i.channels()[0].samples(),&[32896]);}\n'
        )
        environment = {key: value for key, value in os.environ.items()
                       if key not in {"CARGO_REGISTRY_TOKEN", "CARGO_REGISTRIES_CRATES_IO_TOKEN",
                                      "GH_TOKEN", "GITHUB_TOKEN", "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
                                      "ACTIONS_ID_TOKEN_REQUEST_URL"}}
        environment.update(CARGO_HOME=str(consumer / "cargo-home"),
                           CARGO_TARGET_DIR=str(consumer / "target"),
                           CARGO_NET_OFFLINE="false",
                           CARGO_REGISTRIES_CRATES_IO_INDEX="sparse+https://index.crates.io/")
        for arguments in (["generate-lockfile"], ["fetch", "--locked"]):
            subprocess.run(["cargo", "+1.98.1", *arguments], cwd=consumer, env=environment, check=True)
        locked = tomllib.loads((consumer / "Cargo.lock").read_text())
        decoder = [entry for entry in locked["package"] if entry["name"] == PACKAGE]
        if (len(decoder) != 1 or decoder[0]["version"] != version
                or decoder[0]["checksum"] != checksum
                or decoder[0]["source"] != "registry+https://github.com/rust-lang/crates.io-index"):
            raise ValueError("fresh consumer did not resolve the exact published registry archive")
        subprocess.run(["cargo", "+1.98.1", "run", "--offline", "--locked"],
                       cwd=consumer, env=environment, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("source", "archive"))
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--tag", required=True)
    parser.add_argument("--ref", default=os.environ.get("GITHUB_REF", ""))
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", ""))
    parser.add_argument("--event", default=os.environ.get("GITHUB_EVENT_NAME", ""))
    parser.add_argument("--branch-commit", default=os.environ.get("GITHUB_SHA", ""))
    parser.add_argument("--mode", choices=("dry-run", "publish"), default="dry-run")
    parser.add_argument("--approved-commit", default="")
    parser.add_argument("--approved-sha256", default="")
    parser.add_argument("--commit")
    parser.add_argument("--wait-for-checks", action="store_true")
    parser.add_argument("--qualified-run", type=int)
    parser.add_argument("--verify-published", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--github-output", type=Path)
    args = parser.parse_args()
    try:
        args.output.unlink(missing_ok=True)
        branch = validate_request(args.repository, args.event, args.ref, args.tag, args.mode,
                                  args.approved_commit, args.approved_sha256)
        if args.phase == "source":
            if args.commit or args.qualified_run or args.verify_published:
                raise ValueError("archive options cannot be used for source validation")
            report = validate_source(args.root, branch, args.branch_commit, args.tag,
                                     args.approved_commit, args.wait_for_checks)
        else:
            if args.wait_for_checks or not args.commit:
                raise ValueError("archive phase requires an immutable commit, without waiting")
            if args.approved_commit and args.commit != args.approved_commit:
                raise ValueError("candidate differs from owner-approved commit")
            checksum, archive = verify_archive(args.root, args.tag, args.commit, args.approved_sha256)
            if args.qualified_run:
                verify_qualification(args.root, args.commit, args.tag[1:], args.qualified_run, checksum)
            report = {"tag": args.tag, "version": args.tag[1:], "commit": args.commit,
                      "archive_sha256": checksum,
                      **registry_state(args.tag[1:], checksum, args.verify_published)}
            if args.verify_published:
                downloaded = request(f"https://static.crates.io/crates/{PACKAGE}/"
                                     f"{PACKAGE}-{args.tag[1:]}.crate", 32 * 1024 * 1024)
                if hashlib.sha256(downloaded).hexdigest() != checksum:
                    raise ValueError("downloaded registry archive checksum mismatch")
                verify_registry_consumer(args.root, args.tag[1:], checksum)
                report["fresh_registry_consumer"] = "passed"
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        if args.github_output:
            with args.github_output.open("a") as output:
                for key in ("commit", "version", "verus_run_id", "archive_sha256", "publish_needed"):
                    if key in report:
                        value = report[key]
                        output.write(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n")
        print(json.dumps(report, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError,
            subprocess.SubprocessError) as error:
        print(f"release validation failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
