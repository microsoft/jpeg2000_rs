#!/usr/bin/env python3
"""Reproduce the three first-party HT codestreams; never used during timing."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from generate_fixtures import sha

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from numerical import (NumericalCase, _main_header_segments, source_extension,
                       source_image, validate_image_headers)


def generate(encoder, output):
    output.mkdir(parents=True, exist_ok=False)
    records = []
    for name, size, channels, lossless in (
        ("ht-gray8-lossless", 512, 1, True),
        ("ht-large-rgb", 768, 3, True),
        ("ht-rgb8-lossy", 512, 3, False),
    ):
        options = ("-colour_trans", str(channels == 3).lower())
        case = NumericalCase(name, channels=channels, width=size, height=size,
                             decomposition_levels=5, lossless=lossless, options=options)
        pnm = source_image(case)
        source = output / f"{name}.{source_extension(case)}"
        source.write_bytes(pnm)
        encoded = output / f"{name}.j2k"
        flags = ["-num_decomps", "5", "-reversible", str(lossless).lower(),
                 "-tile_size", f"{{{size},{size}}}"]
        if not lossless:
            flags += ["-qstep", "0.01"]
        command = [str(encoder), *flags, "-i", str(source), "-o", str(encoded), *options]
        with (output / f"{name}.stdout").open("wb") as out, \
                (output / f"{name}.stderr").open("wb") as err:
            subprocess.run(command, stdout=out, stderr=err, timeout=120, check=True)
        data = encoded.read_bytes()
        validate_image_headers(case, data)
        headers = dict(_main_header_segments(data))
        if not (int.from_bytes(headers[0xff50][:4], "big") & 0x20000
                and headers[0xff52][8] & 0x40):
            raise ValueError(f"{name}: encoder did not produce HT")
        records.append(dict(id=name, width=size, height=size, channels=channels,
                            lossless=lossless, bytes=len(data), sha256=sha(data),
                            pnm_sha256=sha(pnm),
                            source_samples_sha256=sha(pnm.split(b"\n", 3)[3]),
                            encoder_flags=flags + list(options)))
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("encoder", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    generate(args.encoder.resolve(strict=True), args.output)
