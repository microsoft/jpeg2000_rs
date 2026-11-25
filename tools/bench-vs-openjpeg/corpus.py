#!/usr/bin/env python3
"""Prepare hash-bound photographic, precision, coding-mode, structure and 8K inputs."""

import argparse
from array import array
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import urllib.request

from run import OPENJPEG, execute, sha, write_json

PHOTOS = [
    dict(id="day", file="ISS066-E-2729.jpg",
         url="https://upload.wikimedia.org/wikipedia/commons/7/7a/ISS066-E-2729_-_View_of_Earth.jpg",
         page="https://commons.wikimedia.org/wiki/File:ISS066-E-2729_-_View_of_Earth.jpg",
         sha256="02a5b21f74555643fd027fe0ad94397bc0a7a32734e0554d20a06c7816463bbc"),
    dict(id="night", file="ISS066-E-47096.jpg",
         url="https://upload.wikimedia.org/wikipedia/commons/b/b6/ISS066-E-47096_-_View_of_Earth.jpg",
         page="https://commons.wikimedia.org/wiki/File:ISS066-E-47096_-_View_of_Earth.jpg",
         sha256="d805ffca520ff935716a8918f34bdc21c21ef7905d65aad3344f97ada3b202ad"),
]
CREDIT = "NASA Johnson Space Center, Earth Science and Remote Sensing Unit"
LICENSE = "PD-USGov-NASA; public domain in the United States; no NASA endorsement"
POLICY = "https://www.nasa.gov/nasa-brand-center/images-and-media/"
PROGRESSIONS = ("LRCP", "RLCP", "RPCL", "PCRL", "CPRL")


def precision_payload(gray, precision):
    if precision not in (12, 16):
        raise ValueError("expected derived 12/16-bit source")
    extra = precision - 8
    values = array("H", ((value << extra) | ((index * 17 + index // 31) & ((1 << extra) - 1))
                         for index, value in enumerate(gray)))
    if sys.byteorder == "big":
        values.byteswap()
    little = values.tobytes()
    values.byteswap()
    return values.tobytes(), little


def coding_header(raw):
    if raw[:2] != b"\xff\x4f":
        raise ValueError("not a raw codestream")
    offset, result = 2, {}
    while offset + 4 <= len(raw):
        marker = raw[offset:offset + 2]
        if marker == b"\xff\x90":
            break
        length = int.from_bytes(raw[offset + 2:offset + 4], "big")
        end = offset + length + 2
        if length < 2 or end > len(raw):
            raise ValueError("invalid main-header marker")
        payload = raw[offset + 4:end]
        if marker == b"\xff\x51":
            if len(payload) < 39:
                raise ValueError("short SIZ")
            channels = int.from_bytes(payload[34:36], "big")
            if len(payload) != 36 + 3 * channels or any(
                    payload[36 + 3 * c:39 + 3 * c] != payload[36:39]
                    for c in range(channels)):
                raise ValueError("expected uniform component descriptors")
            if payload[36] & 128 or payload[37:39] != b"\x01\x01":
                raise ValueError("expected unsigned unit-sampling source")
            fields = struct.unpack_from(">8I", payload, 2)
            result.update(width=fields[0] - fields[2], height=fields[1] - fields[3],
                          origin=[fields[2], fields[3]],
                          tile=[fields[4], fields[5]],
                          channels=channels,
                          precision=(payload[36] & 127) + 1)
        elif marker == b"\xff\x52":
            if len(payload) < 10 or payload[1] >= len(PROGRESSIONS) or payload[9] not in (0, 1):
                raise ValueError("invalid or unsupported COD")
            result.update(resolutions=payload[5] + 1, mct=payload[4],
                          block=[1 << (payload[6] + 2), 1 << (payload[7] + 2)],
                          mode=payload[8], wavelet="5/3" if payload[9] == 1 else "9/7",
                          progression=PROGRESSIONS[payload[1]],
                          layers=int.from_bytes(payload[2:4], "big"),
                          precincts=list(payload[10:]) if payload[0] & 1 else [])
        offset = end
    if not {"width", "wavelet"} <= result.keys():
        raise ValueError("SIZ/COD missing")
    return result


def source(output, name, width, height, channels, precision, payload, provenance,
           *, canonical=None):
    size = width * height * channels * ((precision + 7) // 8)
    if len(payload) != size:
        raise ValueError("source payload length differs")
    path = output / "sources" / (name + (".pgm" if channels == 1 else ".ppm"))
    path.parent.mkdir(exist_ok=True)
    header = f"P{5 if channels == 1 else 6}\n{width} {height}\n{(1 << precision) - 1}\n".encode()
    path.write_bytes(header + payload)
    return dict(id=name, path=str(path.relative_to(output)), width=width, height=height,
                channels=channels, precision=precision,
                source_samples_sha256=sha(payload if canonical is None else canonical),
                source_sha256=sha(header + payload),
                source_layout="unsigned interleaved little-endian samples; PNM file uses big-endian for >8 bits",
                origin=provenance, license=LICENSE, credit=CREDIT)


def prepare(options):
    from PIL import Image, __version__ as pillow_version

    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    options.assets.mkdir(parents=True, exist_ok=True)
    images, origins = {}, []
    for photo in PHOTOS:
        path = options.assets / photo["file"]
        if not path.exists():
            urllib.request.urlretrieve(photo["url"], path)
        if sha(path.read_bytes()) != photo["sha256"]:
            raise ValueError(f"photograph hash differs: {path}")
        with Image.open(path) as image:
            if image.size != (5568, 3712):
                raise ValueError("original photograph dimensions differ")
            images[photo["id"]] = image.convert("RGB")
        origins.append(dict(photo, license=LICENSE, credit=CREDIT, policy=POLICY))
    sources, variants = [], {}

    def save(name, image, note):
        channels = 1 if image.mode == "L" else 3
        item = source(output, name, *image.size, channels, 8, image.tobytes(), note)
        sources.append(item)
        variants[name] = item
        return item

    for name, image in images.items():
        small = image.resize((1536, 1024), Image.Resampling.LANCZOS)
        save(name + "-small-rgb", small, f"{name} NASA photograph; Pillow 12.0.0 Lanczos resize")
        save(name + "-small-gray", small.convert("L"), f"{name} photograph; resized RGB converted to L")
    day = images["day"]
    if set(options.groups) & {"A", "B"}:
        save("day-large-rgb", day, "Original 5568x3712 NASA daytime photograph decoded to RGB")
        save("day-large-gray", day.convert("L"), "Original NASA daytime photograph converted to L")
        gray = day.resize((1536, 1024), Image.Resampling.LANCZOS).convert("L").tobytes()
        for precision in (12, 16):
            payload, canonical = precision_payload(gray, precision)
            name = f"day-small-gray{precision}"
            item = source(output, name, 1536, 1024, 1, precision, payload,
                          "NASA gray image with explicitly synthetic deterministic low bits; not a native sensor-precision claim",
                          canonical=canonical)
            sources.append(item)
            variants[name] = item
    small_rgb = day.resize((1536, 1024), Image.Resampling.LANCZOS)
    if "C" in options.groups:
        save("style-gray256", small_rgb.convert("L").crop((640, 384, 896, 640)),
             "Center 256x256 crop of resized NASA daytime grayscale")
    if "D" in options.groups:
        for size in (32, 64, 96, 128):
            for mode in ("L", "RGB"):
                save(f"thumb-{size}-{'gray' if mode == 'L' else 'rgb'}",
                     day.resize((size, size), Image.Resampling.LANCZOS).convert(mode),
                     "NASA daytime thumbnail; deliberate square resampling")
    if "F" in options.groups:
        save("day-gray8k", day.convert("L").resize((8192, 8192), Image.Resampling.LANCZOS),
             "NASA photograph resampled to an 8192x8192 test raster, not native 8K capture")
    (output / "streams").mkdir()
    cases = []
    encoder = options.encoder.resolve()
    help_result = subprocess.run([encoder, "-h"], capture_output=True, text=True)
    if "v2.5.4" not in help_result.stdout + help_result.stderr:
        raise ValueError("OpenJPEG 2.5.4 encoder required")

    def encode(item, name, group, flags=(), *, lossless=True, expected=None):
        path = output / "streams" / (name + ".j2k")
        levels = min(6, min(item["width"], item["height"]).bit_length())
        command = [encoder, "-i", output / item["path"], "-o", path, "-n", str(levels),
                   "-mct", str(int(item["channels"] == 3)), *flags]
        execute(command, output / "encoding" / name, dict(os.environ, OPJ_NUM_THREADS="0"))
        raw = path.read_bytes()
        coding = coding_header(raw)
        for key in ("width", "height", "channels", "precision"):
            if coding[key] != item[key]:
                raise ValueError(f"encoded {key} differs: {name}")
        for key, value in (expected or {}).items():
            if coding[key] != value:
                raise ValueError(f"requested coding property not encoded: {name}/{key}")
        cases.append(dict(item, id=name, path=str(path.relative_to(output)), sha256=sha(raw),
                          bytes=len(raw), corpus_class=group, lossless=lossless,
                          source_id=item["id"], source_path=item["path"],
                          encoding_command=list(map(str, command)), coding=coding))

    if set(options.groups) & {"A", "B"}:
        for name, item in variants.items():
            if not (name.startswith("day-") or name.startswith("night-")) or name == "day-gray8k":
                continue
            if "A" in options.groups:
                encode(item, name + "-lossless", "A", expected={"wavelet": "5/3"})
            if "B" in options.groups:
                for ratio in (10, 40, 100):
                    encode(item, name + f"-lossy-r{ratio}", "B",
                           ["-I", "-r", str(ratio)], lossless=False, expected={"wavelet": "9/7"})
    if "C" in options.groups:
        for block in (32, 64):
            for mode in (0, 1, 2, 4, 8, 16, 32):
                encode(variants["style-gray256"], f"style-b{block}-m{mode}", "C",
                       ["-b", f"{block},{block}", "-M", str(mode)],
                       expected={"block": [block, block], "mode": mode})
    if "D" in options.groups:
        item = variants["day-small-rgb"]
        encode(item, "structure-untiled", "D")
        for tile in (256, 512, 1024):
            encode(item, f"structure-tile{tile}", "D", ["-t", f"{tile},{tile}"],
                   expected={"tile": [tile, tile]})
        for order in PROGRESSIONS:
            encode(item, "structure-" + order.lower(), "D", ["-p", order],
                   expected={"progression": order})
        encode(item, "structure-precinct128", "D",
               ["-c", ",".join(["[128,128]"] * 6)], expected={"precincts": [0x77] * 6})
        encode(item, "structure-layers3", "D", ["-r", "80,20,1"], expected={"layers": 3})
        for name, item in variants.items():
            if name.startswith("thumb-"):
                encode(item, name, "D")
    if "F" in options.groups:
        item = variants["day-gray8k"]
        encode(item, "roi8k-untiled53", "F", expected={"wavelet": "5/3"})
        encode(item, "roi8k-tiled53", "F", ["-t", "256,256"],
               expected={"tile": [256, 256], "wavelet": "5/3"})
        encode(item, "roi8k-untiled97", "F", ["-I", "-r", "40"],
               lossless=False, expected={"wavelet": "9/7"})
    write_json(output / "manifest.json", dict(
        schema=1, scope="Expanded A/B photographic, C mode, D structure and F 8K inputs; not official conformance",
        license=LICENSE, credit=CREDIT, photographs=origins, sources=sources,
        preparation={"pillow": pillow_version, "encoder": str(encoder),
                     "encoder_sha256": sha(encoder.read_bytes()), "openjpeg_revision": OPENJPEG,
                     "high_precision_low_bits": "(gray8 << extra) | ((index*17 + index//31) & ((1<<extra)-1))"},
        cases=cases))
    print(f"Prepared {len(cases)} encoded cases in {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--assets", type=Path, required=True)
    parser.add_argument("--encoder", type=Path, required=True)
    parser.add_argument("--groups", default="ABCDF")
    options = parser.parse_args()
    if not options.groups or not set(options.groups) <= set("ABCDF"):
        parser.error("groups must be selected from ABCDF")
    prepare(options)
