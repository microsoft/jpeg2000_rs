#!/usr/bin/env python3
"""Broader acceptance of unchanged actual-consumer artifacts on a fixed public corpus."""

import argparse
import csv
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess

from run import capture
from zune_integration import native_cpu

PIN = "4989f9c680beeb7bad4fbfd441a93aa373d2ba4f"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def corpus(directory):
    directory.mkdir(parents=True, exist_ok=False)
    subprocess.run(["git", "-C", str(ROOT), "fetch", "--depth", "1", "origin", PIN], check=True)
    paths = subprocess.check_output(["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only", PIN],
                                    text=True).splitlines()
    rows = []
    for path in paths:
        if Path(path).suffix.lower() not in {".jp2", ".j2k", ".jph", ".jpx"}:
            continue
        data = subprocess.check_output(["git", "-C", str(ROOT), "show", PIN + ":" + path])
        name = path.replace("/", "__")
        (directory / name).write_bytes(data)
        rows.append({"source": path, "file": name, "sha256": hashlib.sha256(data).hexdigest(),
                     "bytes": len(data)})
    if len(rows) < 16:
        raise ValueError("fixed public corpus unexpectedly incomplete")
    return rows


def outcomes(text, pixels, names):
    rows = list(csv.DictReader(text.splitlines(), delimiter="\t"))
    if [r["file"] for r in rows] != names:
        raise ValueError("acceptance process omitted or reordered corpus files")
    result = {}
    for row in rows:
        status = row["status"]
        if status != "ok":
            result[row["file"]] = {"status": status}
            continue
        data = (pixels / (row["file"] + ".bin")).read_bytes()
        result[row["file"]] = {"status": "ok", "width": int(row["width"]),
                               "height": int(row["height"]), "color": row["color"],
                               "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
    return result


def run(options):
    artifacts, output = options.artifacts.resolve(), options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    metadata = json.loads((artifacts / "results/metadata.json").read_text())
    if metadata["machine"] != platform.machine():
        raise ValueError("artifact architecture differs from native acceptance host")
    cpu, _ = native_cpu()
    sources = corpus(output / "inputs")
    names = sorted(r["file"] for r in sources)
    (output / "corpus.json").write_text(json.dumps({
        "pin": PIN, "files": sources,
        "scope": "fixed public decoder fixtures; supplied example Hayro pin did not resolve",
    }, indent=2) + "\n")
    expected, records = {}, []
    for config in ("generic", "cpu", "thinlto", "cgu1", "combined"):
        for backend in ("hayro", "rust"):
            if config in {"cpu", "combined"} and cpu != metadata["native_cpu"]:
                records.append({"config": config, "backend": backend,
                                "supported": False, "reason": "tuned artifact host CPU differs"})
                continue
            binary = artifacts / f"results/binaries/build-1-{config}-{backend}"
            binary.chmod(0o755)
            for mode in ("strict", "lenient"):
                label = f"{config}-{backend}-{mode}"
                values = {}
                for name in names:
                    single = output / "single-inputs" / name
                    single.mkdir(parents=True, exist_ok=True)
                    if not (single / name).exists():
                        shutil.copyfile(output / "inputs" / name, single / name)
                    pixels = output / (label + "-pixels") / name
                    prefix = output / label / name
                    prefix.parent.mkdir(exist_ok=True)
                    command = ["bash", "-c", 'ulimit -v 2097152 && exec "$@"', "bash",
                               str(binary), mode, str(single), str(pixels)]
                    try:
                        process = subprocess.run(command, capture_output=True, timeout=300)
                    except subprocess.TimeoutExpired as error:
                        Path(str(prefix) + ".stdout").write_bytes(error.stdout or b"")
                        Path(str(prefix) + ".stderr").write_bytes(error.stderr or b"")
                        values[name] = {"status": "process-timeout", "timeout_seconds": 300}
                        continue
                    Path(str(prefix) + ".stdout").write_bytes(process.stdout)
                    Path(str(prefix) + ".stderr").write_bytes(process.stderr)
                    if process.returncode:
                        values[name] = {"status": "process-failure", "returncode": process.returncode}
                    else:
                        values.update(outcomes(process.stdout.decode(), pixels, [name]))
                key = (backend, mode)
                expected.setdefault(key, values)
                changes = [name for name in names if values[name] != expected[key][name]]
                records.append({"config": config, "backend": backend, "mode": mode,
                                "supported": True, "outcomes": values,
                                "matches_backend_generic": not changes, "changed_files": changes})
    (output / "summary.json").write_text(json.dumps({
        "artifact_build_host": metadata["native_cpu"], "native_acceptance_host": cpu,
        "corpus_pin": PIN, "cases": len(names), "records": records,
        "resource_scope": "identical2GiB address-space cap and300s process timeout; no timing claim",
        "cpu": capture(["lscpu", "--json"]),
    }, indent=2) + "\n")
    (output / "COMPLETE").write_text("fixed-corpus native acceptance outcomes preserved, not universal support\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args())
