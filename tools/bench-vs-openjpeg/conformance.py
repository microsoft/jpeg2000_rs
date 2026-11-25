#!/usr/bin/env python3
"""Inventory pinned JPEG-2000 conformance vectors; do not time or redistribute them."""

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from run import capture, compare_dumps, sha, write_json

TREE = "39524bd3a601d90ed8e0177559400d23945f96a9"
REPOSITORY = "uclouvain/openjpeg-data"


def decode_blob(document, expected):
    if document["encoding"] != "base64" or document["sha"] != expected["sha"]:
        raise ValueError("unexpected GitHub blob encoding or identity")
    data = base64.b64decode(document["content"])
    identity = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if identity != expected["sha"] or len(data) != expected["size"]:
        raise ValueError("downloaded bytes differ from the pinned Git object")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--openjpeg", type=Path, required=True)
    parser.add_argument("--gh", default="gh")
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--maximum-address-space", type=int, default=8 * 1024**3)
    options = parser.parse_args()
    if options.cpu not in os.sched_getaffinity(0) or options.maximum_address_space < 0:
        parser.error("invalid CPU or address-space cap")
    binaries = {"rust": options.rust.resolve(), "openjpeg": options.openjpeg.resolve()}
    binary_hashes = {backend: sha(binary.read_bytes()) for backend, binary in binaries.items()}
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)

    def api(endpoint):
        return json.loads(subprocess.check_output(
            [options.gh, "api", f"repos/{REPOSITORY}/{endpoint}"], text=True))

    tree = api(f"git/trees/{TREE}?recursive=1")
    if tree["sha"] != TREE or tree.get("truncated"):
        raise ValueError("requires complete pinned source tree")
    write_json(output / "source-tree.json", tree)
    entries = [item for item in tree["tree"]
               if item["type"] == "blob" and item["path"].startswith("input/conformance/")]
    if len(entries) != 59:
        raise ValueError("pinned conformance inventory differs")
    entries.sort(key=lambda item: (Path(item["path"]).name != "COPYRIGHT", item["path"]))
    inventory = []
    for item in entries:
        relative = Path(item["path"])
        if ".." in relative.parts or relative.is_absolute():
            raise ValueError("invalid pinned input path")
        destination = output / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(decode_blob(api(f"git/blobs/{item['sha']}"), item))
        inventory.append(dict(path=item["path"], git_blob=item["sha"], bytes=item["size"],
                              sha256=sha(destination.read_bytes())))
        write_json(output / "inputs.json", inventory)
    if not (output / "input/conformance/COPYRIGHT").is_file():
        raise ValueError("required conformance-use copyright notice is missing")

    env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1")
    records = []
    for item in inventory:
        path = output / item["path"]
        if path.suffix not in {".jp2", ".j2k", ".j2c"}:
            continue
        record = dict(input=item, processes={})
        dumps = {}
        for backend, binary in binaries.items():
            data, metrics = capture(
                ["taskset", "-c", options.cpu, binary, path, "dump", "0", "-", "1", "0", "0"],
                output / "observations" / path.stem / (backend + "-dump"), env,
                maximum_address_space=options.maximum_address_space)
            record["processes"][backend] = metrics
            if metrics["returncode"] == 0:
                dumps[backend] = data
        if len(dumps) != 2:
            record["status"] = "decoder-refusal-or-failure"
        else:
            try:
                record["comparison"] = compare_dumps(dumps["rust"], dumps["openjpeg"])
                record["status"] = ("identical" if record["comparison"]["differing_samples"] == 0
                                    else "decoded-with-differences")
            except ValueError as error:
                record.update(status="output-validation-failed", error=str(error))
        records.append(record)
        write_json(output / "inventory.json", dict(
            scope="Conformance-use diagnostic inventory, not normative qualification or approved numerical tolerance",
            repository=REPOSITORY, tree=TREE, records=records,
            binary_sha256=binary_hashes,
            maximum_address_space=options.maximum_address_space,
            runner_sha256=sha(Path(__file__).read_bytes()),
            licensing="Retain input/conformance/COPYRIGHT; JPEG-2000 conformance use only; no vector redistribution"))
        print(path.name, record["status"], flush=True)
    if len(records) != 57:
        raise ValueError("expected every pinned encoded conformance vector")
    return 0 if all(row["status"] == "identical" for row in records) else 1


if __name__ == "__main__":
    sys.exit(main())
