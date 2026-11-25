#!/usr/bin/env python3
"""Verify the full timing protocol and extract source-separated comparison tables."""

import argparse
from collections import defaultdict
import csv
import itertools
import json
import math
from pathlib import Path
import statistics

from run import sha, write_json


def validate_samples(values):
    if len(values) < 15 or sum(values) < 2_000_000_000 or min(values) <= 0:
        raise ValueError("requires at least 15 positive samples AND two seconds per process")


def write_csv(path, rows):
    with path.open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    matrix, output = options.matrix.resolve(), options.output.resolve()
    complete = json.loads((matrix / "COMPLETE.json").read_text())
    corpus = json.loads((matrix / "corpus.json").read_text())
    environment = json.loads((matrix / "environment.json").read_text())
    cases = {case["id"]: case for case in corpus["cases"]}
    configs = complete["configurations"]
    if len(cases) != complete["cases"] or len(configs) != len(set(configs)):
        raise ValueError("completion shape differs from selected corpus/configurations")
    samples = defaultdict(list)
    total = 0
    with (matrix / "raw.csv").open() as stream:
        for row in csv.DictReader(stream):
            key = (row["config"], row["case"], row["backend"], row["mode"], int(row["round"]))
            if row["class"] != cases[row["case"]]["corpus_class"] or int(row["sample"]) != len(samples[key]):
                raise ValueError("sample numbering or corpus class differs")
            samples[key].append(int(row["ns"]))
            total += 1
    expected = {(config, case, backend, mode, round_index)
                for config, case, (backend, mode), round_index in itertools.product(
                    configs, cases, [("rust", "typed"), ("openjpeg", "typed"), ("openjpeg", "native")],
                    range(2))}
    if set(samples) != expected or total != complete["records"]:
        raise ValueError("missing, extra or incomplete process groups")
    resources = []
    for (config, case, backend, mode, round_index), values in samples.items():
        validate_samples(values)
        metrics = json.loads((matrix / config / case / f"{backend}-{mode}-r{round_index}.json").read_text())
        if metrics["returncode"] != 0 or metrics["command"][-3:] != ["15", "2000", "3"]:
            raise ValueError("process did not use the full recorded protocol")
        if metrics["thread_environment"] != {"OPJ_NUM_THREADS": "0", "BENCH_OPENJPEG_THREADS": "1"}:
            raise ValueError("decoder worker lifecycle differs")
        if metrics["maximum_address_space"] != environment["maximum_address_space"]:
            raise ValueError("decoder address-space cap differs")
        resources.append(dict(config=config, case=case, backend=backend, mode=mode,
                              round=round_index, max_rss_kib=metrics["max_rss_kib"],
                              minor_faults=metrics["minor_faults"], major_faults=metrics["major_faults"]))
    with (matrix / "summary.csv").open() as stream:
        summaries = list(csv.DictReader(stream))
    if len(summaries) != len(expected) // 2:
        raise ValueError("aggregate summary shape differs")
    medians = {}
    for row in summaries:
        key = (row["config"], row["case"], row["backend"], row["mode"])
        values = samples[key + (0,)] + samples[key + (1,)]
        quartiles = statistics.quantiles(values, n=4, method="inclusive")
        median = statistics.median(values) / 1e6
        iqr = (quartiles[2] - quartiles[0]) / 1e6
        if int(row["n"]) != len(values) or float(row["median_ms"]) != median or float(row["iqr_ms"]) != iqr:
            raise ValueError("summary median/IQR/count does not reproduce from raw samples")
        if key in medians:
            raise ValueError("duplicate summary key")
        medians[key] = median
    correctness, builds = [], {}
    for config in configs:
        build = matrix / config / "build.json"
        metadata = (json.loads(build.read_text()) if build.exists()
                    else json.loads((matrix / config / "build-reference.json").read_text())["metadata"])
        if metadata["decoder_src_tree"] != environment["decoder_src_tree"] or "-ffp-contract=off" not in metadata["cflags"]:
            raise ValueError("decoder source or reference arithmetic flags differ")
        builds[config] = metadata
        for case in cases.values():
            comparison = json.loads((matrix / config / case["id"] / "correctness.json").read_text())
            if case["lossless"] and comparison["differing_samples"] != 0:
                raise ValueError("reversible output mismatch")
            correctness.append(dict(config=config, case=case["id"], lossless=case["lossless"], **comparison))
    ratios = []
    groups = defaultdict(list)
    for config, case in itertools.product(configs, cases.values()):
        rust = medians[(config, case["id"], "rust", "typed")]
        reference = medians[(config, case["id"], "openjpeg", "typed")]
        native = medians[(config, case["id"], "openjpeg", "native")]
        ratio = rust / reference
        comparison = next(row for row in correctness if row["config"] == config and row["case"] == case["id"])
        pixels, remainder = divmod(comparison["samples"], case["channels"])
        if remainder or (corpus["request"] == {"reduce": 0, "window": "-"}
                         and pixels != case["width"] * case["height"]):
            raise ValueError("throughput requires the declared unit-sampled source geometry")
        groups[(config, case["corpus_class"])].append(ratio)
        ratios.append(dict(config=config, case=case["id"], corpus_class=case["corpus_class"],
                           rust_ms=rust, openjpeg_typed_ms=reference, openjpeg_native_ms=native,
                           decoded_pixels=pixels, rust_mpixel_s=pixels / (rust * 1000),
                           openjpeg_typed_mpixel_s=pixels / (reference * 1000),
                           typed_ratio=ratio, native_ratio=rust / native))
    cross = []
    for case, backend in itertools.product(cases, ["rust", "openjpeg"]):
        hashes = {row[backend + "_sha256"] for row in correctness if row["case"] == case}
        if len(hashes) != 1:
            cross.append(dict(case=case, backend=backend))
    output.mkdir(parents=True, exist_ok=False)
    write_csv(output / "summary.csv", summaries)
    write_csv(output / "ratios.csv", ratios)
    write_csv(output / "resources.csv", resources)
    write_csv(output / "correctness.csv", correctness)
    write_json(output / "analysis.json", dict(
        scope="This selected corpus and source only; shared-host wall times are indicative",
        records=total, processes=len(samples), cases=len(cases), builds=builds,
        environment=environment, request=corpus["request"],
        raw_sha256=sha((matrix / "raw.csv").read_bytes()),
        summary_sha256=sha((matrix / "summary.csv").read_bytes()),
        analyzer_sha256=sha(Path(__file__).read_bytes()),
        cross_configuration_differences=cross,
        class_geomeans=[dict(config=config, corpus_class=group, cases=len(values),
                             typed_ratio=math.exp(statistics.mean(map(math.log, values))))
                        for (config, group), values in sorted(groups.items())]))
    print(f"Verified {total} samples, {len(samples)} full-protocol processes, {len(cases)} cases.")
    for (config, group), values in sorted(groups.items()):
        print(config, group, len(values), f"{math.exp(statistics.mean(map(math.log, values))):.4f}")
    print("Cross-configuration output differences:", cross)


if __name__ == "__main__":
    main()
