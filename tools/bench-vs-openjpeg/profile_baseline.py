#!/usr/bin/env python3
"""Separate sampled stage attribution and whole-process counters from timing."""

import argparse
import csv
import json
import os
from pathlib import Path
import re

from run import execute, write_json


def stage(symbol):
    if any(key in symbol for key in ["malloc", "calloc", "realloc", "memcpy", "memset",
                                      "memmove", "__libc_free", "free@plt", "cfree", "raw_vec",
                                      "__rdl_", "allocation::"]):
        return "allocation/copy/zero"
    if "mq::" in symbol or "2mq" in symbol or "opj_mqc" in symbol:
        return "MQ"
    if (("tier1" in symbol and "ht_" in symbol) or "opj_ht" in symbol
            or "opj_t1_ht" in symbol or "frwd_fetch" in symbol or "rev_fetch" in symbol):
        return "Tier1 HT"
    if "tier1" in symbol or "opj_t1_" in symbol:
        return "Tier1 shared/legacy"
    if ("::transform::" in symbol or "9transform" in symbol or "opj_dwt" in symbol
            or "opj_idwt" in symbol or "opj_v8dwt" in symbol):
        return "DWT"
    if "component_transform" in symbol or "image::mct" in symbol or "opj_mct" in symbol:
        return "MCT"
    if "reconstruction::fused" in symbol or "quantization::" in symbol:
        return "dequant/placement"
    if "image::assembly" in symbol:
        return "assembly"
    if any(key in symbol for key in ["decode::output", "image::samples", "image::arithmetic",
                                      "color::", "opj_tcd_dc_level"]):
        return "typed/output/color"
    if any(key in symbol for key in ["packet::", "codestream::", "decode::planning",
                                      "opj_t2_", "opj_j2k", "opj_pi_"]):
        return "parsing/Tier2/planning"
    if "reconstruction::" in symbol:
        return "reconstruction other"
    if "opj_tcd_decode_tile" in symbol:
        return "TCD reconstruction unresolved"
    return "other"


def parse_report(raw):
    grouped = {}
    for line in raw.splitlines():
        match = re.match(r"^\s*([0-9.]+)%?\s*;\s*([^;]+)", line)
        if match:
            name = stage(match[2])
            grouped[name] = grouped.get(name, 0) + float(match[1])
    return grouped


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--perf", default="perf")
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--case", default=".")
    options = parser.parse_args()
    baseline = options.baseline.resolve()
    if not (baseline / "COMPLETE.json").exists():
        parser.error("baseline incomplete")
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cases = [c for c in json.loads((baseline / "corpus.json").read_text())["cases"]
             if re.search(options.case, c["id"])]
    if not cases:
        parser.error("no matching cases")
    env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1", LC_ALL="C")
    rows = []
    for case in cases:
        for backend, binary in [
            ("rust", baseline / "generic/cargo/release/bench-vs-openjpeg"),
            ("openjpeg", baseline / "generic/bench-openjpeg"),
        ]:
            work = output / case["id"] / backend
            work.mkdir(parents=True)
            base = ["taskset", "-c", options.cpu, binary, case["path"], "typed", "0", "-"]
            execute([options.perf, "record", "-e", "cycles:u", "-c", "5000000",
                     "--call-graph", "dwarf", "-o", work / "profile.data", "--",
                     *base, "15", "2000", "0"], work / "record", env)
            raw = execute([options.perf, "report", "-i", work / "profile.data",
                           "--stdio", "--no-children", "--sort", "symbol",
                           "--field-separator", ";", "-F", "overhead,symbol",
                           "--percent-limit", "0", "--no-call-graph"],
                          work / "report", env).decode()
            grouped = parse_report(raw)
            if not grouped:
                raise ValueError(f"no stage samples parsed: {work}")
            write_json(work / "stages.json", grouped)
            for name, percent in grouped.items():
                rows.append(dict(case=case["id"], **{"class": case["corpus_class"]},
                                 backend=backend, stage=name, sampled_self_percent=percent))
            for repeat in range(3):
                execute([options.perf, "stat", "-x", ";", "-o", work / f"counters-{repeat}.csv",
                         "-e", "cycles:u,instructions:u,branches:u,branch-misses:u,"
                         "L1-dcache-load-misses:u,LLC-load-misses:u",
                         "--", *base, "1", "0", "0"], work / f"count-{repeat}", env)
    with (output / "stages.csv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    write_json(output / "COMPLETE.json", {
        "scope": "generic baseline, sampled leaf/self attribution; not isolated stage timers",
        "counter_scope": "whole process including startup/input; unsupported events remain explicit",
        "rows": len(rows),
    })


if __name__ == "__main__":
    main()
