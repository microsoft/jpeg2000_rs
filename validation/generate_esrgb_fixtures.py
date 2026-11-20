"""Reproduce the self-authored PIMA encoded-value fixtures with OpenJPEG.

OpenJPEG only encodes the supplied lossless component values; it does not
perform or certify the PIMA conversion. Expected color values are derived
independently in test_esrgb_classification.py.
"""

import argparse
import struct
import subprocess
import tempfile
from pathlib import Path


def vectors(precision):
    offset = 3 * 2 ** (precision - 3)
    step = 2 ** (precision - 9)
    white = offset + 255 * step
    extended = [
        0, offset - 1, offset, offset + 1, offset + step // 2,
        offset + step - 1, offset + step, offset + 127 * step,
        offset + 127 * step + step // 2 - 1,
        offset + 127 * step + step // 2,
        offset + 127 * step + step // 2 + 1,
        offset + 128 * step, white - step, white - 1,
        white, white + 1, 2**precision - 2, 2**precision - 1,
    ]
    values = extended + [offset + code * step for code in range(256)]
    return [
        values,
        values[37:] + values[:37],
        list(reversed(values)),
    ]


def box(kind, payload):
    return struct.pack(">I4s", 8 + len(payload), kind) + payload


def generate(encoder, output):
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="jpeg2000-pima-") as directory:
        work = Path(directory)
        for precision in (10, 12, 16):
            channels = vectors(precision)
            ppm = work / f"pima-{precision}.ppm"
            raw = work / f"pima-{precision}.j2k"
            ppm.write_bytes(
                f"P6\n137 2\n{2**precision - 1}\n".encode("ascii")
                + b"".join(struct.pack(">H", value)
                           for pixel in zip(*channels) for value in pixel)
            )
            subprocess.run(
                [encoder, "-i", str(ppm), "-o", str(raw), "-n", "1",
                 "-mct", "0", "-r", "1"],
                check=True, capture_output=True,
            )
            header = box(b"ihdr", struct.pack(">IIH4B", 2, 137, 3, precision - 1, 7, 0, 0))
            header += box(b"colr", struct.pack(">3BI", 1, 0, 0, 20))
            # JPX minor version 1; the carrier claims no JP2 compatibility.
            file_type = box(b"ftyp", b"jpx " + struct.pack(">I", 1) + b"jpx ")
            # One-byte masks; no additional standard/vendor reader requirements.
            requirements = box(b"rreq", b"\x01\x00\x00\x00\x00\x00\x00")
            container = (
                box(b"jP  ", b"\r\n\x87\n") + file_type + requirements
                + box(b"jp2h", header) + box(b"jp2c", raw.read_bytes())
            )
            (output / f"pima-{precision}.jpx").write_bytes(container)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--encoder", default="opj_compress")
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).parent / "fixtures" / "pima-esrgb",
    )
    arguments = parser.parse_args()
    generate(arguments.encoder, arguments.output)
