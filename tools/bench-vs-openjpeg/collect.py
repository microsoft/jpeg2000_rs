#!/usr/bin/env python3
"""Collect portable raw observations and immutable inputs, excluding build caches."""

import argparse
import json
import os
from pathlib import Path
import shutil

from run import sha, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    work, output = options.work.resolve(), options.output.resolve()
    if not work.is_dir():
        parser.error("measured work tree does not exist")
    if output.is_relative_to(work):
        parser.error("collection output must be outside the measured work tree")
    output.mkdir(parents=True, exist_ok=False)
    entries = []
    for directory, dirs, files in os.walk(work):
        parent = Path(directory)
        dirs[:] = [d for d in dirs if not (
            d == ".git" or (parent / d / ".git").exists()
            or (parent / d / "CMakeCache.txt").is_file()
            or (parent / d / ".rustc_info.json").is_file()
            or (parent / d / "release/.fingerprint").is_dir()
            or (parent / d / "conformance/COPYRIGHT").is_file())]
        for name in files:
            path = Path(directory) / name
            if path.is_symlink() or name.endswith("-dump.stdout"):
                continue
            if name in {"rust.stdout", "openjpeg.stdout"}:
                metrics = path.with_suffix(".json")
                if not metrics.is_file():
                    raise ValueError(f"cannot distinguish pixels from process text: {path}")
                if "dump" in json.loads(metrics.read_text())["command"]:
                    continue
            if path.suffix not in {".csv", ".json", ".stdout", ".stderr", ".log",
                                   ".md", ".txt", ".j2k", ".s", ".asm", ".out"}:
                continue
            relative = path.relative_to(work)
            target = output / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
            entries.append(dict(path=str(relative), bytes=target.stat().st_size,
                                sha256=sha(target.read_bytes())))
    complete = work / "COMPLETE.json"
    if not complete.exists():
        complete = work / "timings" / "COMPLETE.json"
    if complete.exists():
        retained = {item["path"] for item in entries}
        matrix = complete.parent
        for pattern in ["*.csv", "*.json", "*/build*.json", "*/*/correctness.json",
                        "*/*/*-r*.json", "*/*/*-r*.stdout", "*/*/*-r*.stderr"]:
            for path in matrix.glob(pattern):
                if str(path.relative_to(work)) not in retained:
                    raise ValueError(f"collection omitted matrix evidence: {path.relative_to(work)}")
        for path in (work / "instructions").rglob("*"):
            if path.is_file() and path.suffix in {".json", ".stdout", ".stderr", ".out"} \
                    and str(path.relative_to(work)) not in retained:
                raise ValueError(f"collection omitted instruction evidence: {path.relative_to(work)}")
    write_json(output / "INDEX.json", dict(
        scope="Measured observations and canonical encoded inputs; not a full A-G conformance claim",
        timing_matrix_complete=complete.exists(), entries=entries,
        omitted="Build caches, full pixel dumps, PNM intermediates and downloaded JPEG originals"))
    print(f"Collected {len(entries)} files; timing matrix complete: {complete.exists()}")


if __name__ == "__main__":
    main()
