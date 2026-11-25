#!/usr/bin/env python3
"""Collect portable raw observations and immutable inputs, excluding build caches."""

import argparse
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
        dirs[:] = [d for d in dirs if d not in {
            "cargo", "openjpeg", "openjpeg-source", "consumer", "sources", "assets", "input", "__pycache__"}]
        for name in files:
            path = Path(directory) / name
            if path.is_symlink() or name.endswith("-dump.stdout") or name in {"rust.stdout", "openjpeg.stdout"}:
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
    complete = work / "timings" / "COMPLETE.json"
    write_json(output / "INDEX.json", dict(
        scope="Measured observations and canonical encoded inputs; not a full A-G conformance claim",
        timing_matrix_complete=complete.exists(), entries=entries,
        omitted="Build caches, full pixel dumps, PNM intermediates and downloaded JPEG originals"))
    print(f"Collected {len(entries)} files; timing matrix complete: {complete.exists()}")


if __name__ == "__main__":
    main()
