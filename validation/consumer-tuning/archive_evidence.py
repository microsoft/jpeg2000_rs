#!/usr/bin/env python3
"""Persist all raw textual observations, excluding hashed native executables."""

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile


def archive(source, destination):
    source = source.resolve()
    if not (source / "COMPLETE").is_file():
        raise ValueError("refusing to archive an incomplete benchmark as final evidence")
    metadata = json.loads((source / "metadata.json").read_text())
    fixtures = json.loads((source / "fixture-manifest.json").read_text())["fixtures"]
    expected_samples = metadata["pairs"] * 4 * 3 * len(fixtures) * 2
    records = [json.loads(line) for line in (source / "samples.jsonl").read_text().splitlines()]
    if len(records) != expected_samples or any(record["metrics"]["returncode"] for record in records):
        raise ValueError("missing or failed process observations")
    identities = [(row["pair"], row["tuned"], row["backend"], row["fixture"], row["position"])
                  for row in records]
    if len(set(identities)) != len(identities):
        raise ValueError("duplicated process identity")
    builds = [json.loads(line) for line in (source / "builds.jsonl").read_text().splitlines()]
    if len(builds) != metadata["build_rounds"] * 5 * 3:
        raise ValueError("missing build observations")
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        raise FileExistsError(destination)
    index = {}
    binaries = []

    def add_bytes(tar, name, data):
        entry = tarfile.TarInfo(name)
        entry.size = len(data)
        entry.mode = 0o644
        tar.addfile(entry, io.BytesIO(data))

    with destination.open("wb") as stream, \
            gzip.GzipFile(filename="", mode="wb", fileobj=stream, mtime=0) as compressed, \
            tarfile.open(fileobj=compressed, mode="w") as tar:
        for path in sorted(source.rglob("*")):
            if not path.is_file():
                continue
            relative = str(path.relative_to(source))
            if relative.startswith("binaries/"):
                continue
            data = path.read_bytes()
            index[relative] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
            add_bytes(tar, relative, data)
        for row in builds:
            path = source / f"build-{row['round']}-{row['config']}-{row['backend']}/binary.json"
            binary = json.loads(path.read_text())
            binaries.append({"round": row["round"], "config": row["config"],
                             "backend": row["backend"], "sha256": binary["sha256"],
                             "bytes": binary["bytes"]})
        add_bytes(tar, "ARCHIVE_CONTENTS.json", (json.dumps({
            "schema": 1, "raw_text_files": index, "omitted_executables": binaries,
            "note": "All raw build/compiler/link/process text, metadata and outcomes are retained. "
                    "Native executables remain in the full hosted artifact and are hashed here.",
        }, indent=2) + "\n").encode())
    checksum = hashlib.sha256(destination.read_bytes()).hexdigest()
    Path(str(destination) + ".sha256").write_text(f"{checksum}  {destination.name}\n")
    print(f"{checksum}  {destination} ({destination.stat().st_size} bytes)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    options = parser.parse_args()
    archive(options.source, options.destination)
