#!/usr/bin/env python3
"""Generate the public, integer-only #446--#449 shared cohort."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OPENJPEG_REVISION = "a5891555eb49ed7cc26b2901ea680acda136d811"
TRACKED = [
    "validation/image-consumer-probe/tests/fixtures/gray.jp2",
    "validation/image-consumer-probe/tests/fixtures/rgb.jp2",
    "validation/generated/corpus/raw-minimal.j2k",
    "validation/generated/corpus/raw-invalid-soc.j2k",
    "validation/generated/corpus/jp2-invalid-signature.jp2",
    "validation/fixtures/hayro-mixed-progression/packets_mixed_levels_rpcl.j2k",
    "validation/fixtures/hayro-empty-axes/codestream_single_row_odd_offset.j2k",
    "validation/fixtures/hayro-sized-eoc/tile_parts_missing_eoc.j2k",
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def samples(channels, noisy, size=1024):
    """Interleaved u8, raster y/x/channel order; all arithmetic explicitly integer."""
    data = bytearray(size * size * channels)
    state = 0x6D2B79F5
    i = 0
    for y in range(size):
        for x in range(size):
            for c in range(channels):
                if noisy:
                    state ^= (state << 13) & 0xFFFFFFFF
                    state ^= state >> 17
                    state ^= (state << 5) & 0xFFFFFFFF
                    value = state >> 24
                else:
                    value = ((3 * x + 5 * y + 97 * c) // 16) & 255
                data[i] = value
                i += 1
    return bytes(data)


def jp2_parts(data):
    offset = 0
    boxes = []
    codestream = None
    metadata = bytearray()
    while offset < len(data):
        length, kind = struct.unpack_from(">I4s", data, offset)
        if length < 8 or offset + length > len(data):
            raise ValueError("unexpected JP2 box length")
        box = data[offset:offset + length]
        boxes.append({"type": kind.decode("ascii"), "bytes": length, "sha256": sha(box)})
        if kind == b"jp2c":
            if codestream is not None:
                raise ValueError("multiple codestreams")
            codestream = box[8:]
        else:
            metadata.extend(box)
        offset += length
    if codestream is None:
        raise ValueError("no codestream")
    return codestream, boxes, sha(metadata)


def coding_metadata(raw):
    offset = 2
    found = {}
    while offset < len(raw):
        marker = raw[offset:offset + 2]
        if marker == b"\xff\x90":
            break
        length = int.from_bytes(raw[offset + 2:offset + 4], "big")
        if length < 2:
            raise ValueError("invalid marker")
        payload = raw[offset + 4:offset + 2 + length]
        if marker == b"\xff\x52":
            found = {"resolutions": payload[5] + 1, "mct": payload[4],
                     "wavelet": "5/3" if payload[9] == 1 else "9/7"}
        offset += length + 2
    if not found:
        raise ValueError("no COD")
    return found


def generate(encoder, output):
    output.mkdir(parents=True, exist_ok=True)
    help_text = subprocess.run([str(encoder), "-h"], capture_output=True, text=True).stdout
    if "v2.5.4" not in help_text:
        raise ValueError("OpenJPEG 2.5.4 required")
    fixtures = []
    sources = []
    for channels, color in [(1, "gray"), (3, "rgb")]:
        for noisy, pattern in [(False, "smooth"), (True, "noisy")]:
            payload = samples(channels, noisy)
            source_name = f"{pattern}-{color}." + ("pgm" if channels == 1 else "ppm")
            header = f"P{5 if channels == 1 else 6}\n1024 1024\n255\n".encode()
            (output / source_name).write_bytes(header + payload)
            sources.append({"path": source_name, "sha256": sha(header + payload),
                            "samples_sha256": sha(payload), "channels": channels,
                            "width": 1024, "height": 1024, "pattern": pattern})
            for lossy in [False, True]:
                name = f"{pattern}-{color}-{'lossy' if lossy else 'lossless'}"
                args = ["-n", "6", "-mct", str(int(channels == 3))]
                if lossy:
                    args += ["-I", "-r", "12"]
                command = [str(encoder), "-i", str(output / source_name),
                           "-o", str(output / (name + ".jp2")), *args]
                result = subprocess.run(command, capture_output=True, text=True, check=True)
                (output / (name + ".encoder.log")).write_text(result.stdout + result.stderr)
                jp2 = (output / (name + ".jp2")).read_bytes()
                raw, boxes, metadata_hash = jp2_parts(jp2)
                (output / (name + ".j2k")).write_bytes(raw)
                coding = coding_metadata(raw)
                assert coding == {"resolutions": 6, "mct": int(channels == 3),
                                  "wavelet": "9/7" if lossy else "5/3"}, coding
                for suffix, encoded in [("jp2", jp2), ("j2k", raw)]:
                    fixtures.append({
                        "id": name + "-" + suffix, "path": name + "." + suffix,
                        "group": "generated-1024", "format": suffix,
                        "sha256": sha(encoded), "bytes": len(encoded),
                        "width": 1024, "height": 1024, "channels": channels,
                        "source": source_name, "source_samples_sha256": sha(payload),
                        "expected_lossless_samples_sha256": None if lossy else sha(payload),
                        "coding": coding, "encoder_arguments": args,
                        "codestream_sha256": sha(raw), "jp2_boxes": boxes if suffix == "jp2" else [],
                        "container_metadata_sha256": metadata_hash if suffix == "jp2" else sha(b""),
                    })
    for source in TRACKED:
        path = ROOT / source
        subprocess.run(["git", "-C", str(ROOT), "ls-files", "--error-unmatch", source],
                       check=True, stdout=subprocess.DEVNULL)
        relative = "tracked/" + source
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        fixtures.append({"id": "tracked-" + path.stem, "path": relative,
                         "group": "tracked-validation", "format": path.suffix[1:],
                         "sha256": sha(path.read_bytes()), "bytes": path.stat().st_size,
                         "origin": source, "license": "MIT; repository LICENSE or adjacent LICENSE-MIT"})
        license_file = path.parent / "LICENSE-MIT"
        if license_file.exists():
            shutil.copyfile(license_file, target.parent / "LICENSE-MIT")
    manifest = {
        "schema": 1, "cohort": "consumer-tuning-449-v1",
        "decoder_main_control": "97d5162b3f43fb14942c46bbea73752d26fb24b4",
        "encoder": {"project": "OpenJPEG", "version": "2.5.4",
                    "revision": OPENJPEG_REVISION},
        "sample_layout": "unsigned 8-bit, interleaved y/x/channel order; SHA256 excludes PNM header",
        "patterns": {
            "smooth": "((3*x + 5*y + 97*c) // 16) & 255",
            "noisy": "xorshift32 state=0x6d2b79f5 reset per source; for each y,x,c: "
                     "s^=(s<<13)&0xffffffff; s^=s>>17; s^=(s<<5)&0xffffffff; byte=s>>24",
        },
        "sources": sources, "fixtures": fixtures,
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (output / "encoder-provenance.json").write_text(json.dumps({
        "executable": str(encoder), "executable_sha256": sha(encoder.read_bytes()),
        "help": help_text,
    }, indent=2) + "\n")
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--encoder", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT / "target/consumer-tuning/fixtures")
    options = parser.parse_args()
    generate(options.encoder.resolve(), options.output.resolve())
