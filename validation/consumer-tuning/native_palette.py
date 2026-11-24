"""Generate the first-party #479 targets and a decoder-independent typed-plane oracle."""

from array import array
import struct
import sys

from generate_fixtures import jp2_parts, samples, sha

SOURCE = "smooth-gray-lossless-jp2"
MASK64 = (1 << 64) - 1
CASES = (
    ("palette-gray-alpha", ((8, False), (8, False)), (((0, 1),), ((1, 0),)),
     lambda i: (i, 255 - i), "4bc55f48e87389701336095827f7de020f29918b98e0865553474b0cc9be9457"),
    ("palette-mixed38", ((38, True), (38, False), (5, False)), ((), (), ()),
     lambda i: ((i << 29) - (1 << 37), i << 30, i % 32),
     "3e8444bbeaf24e8d122f496443c05895b2a7e82f4a43a3d69394b4c0b9a04874"),
)


def box(kind, payload):
    return struct.pack(">I4s", 8 + len(payload), kind) + payload


def typed_oracle(width, height, indices, columns, definitions, table):
    """Serialize expected components from the authored source indices, not a decode."""
    output = bytearray(struct.pack("<6Q", 2, width, height, 0, 0, len(columns)))
    for column, ((precision, signed), defs) in enumerate(zip(columns, definitions, strict=True)):
        output += struct.pack("<11Q", width, height, precision, signed, 1, 1, 0, 0,
                              signed, len(indices), len(defs))
        for kind, association in defs:
            output += struct.pack("<2Q", kind, association)
        values = [row[column] & MASK64 for row in table]
        plane = array("Q", (values[index] for index in indices))
        if sys.byteorder != "little":
            plane.byteswap()
        output += plane.tobytes()
    return {"native_sha256": sha(output), "native_bytes": len(output)}


def generate(source, fixture):
    width, height = fixture["width"], fixture["height"]
    indices = samples(1, False, size=width)
    raw, boxes, _ = jp2_parts(source)
    if (width != height or len(indices) != width * height or set(indices) != set(range(256))
            or sha(indices) != fixture["source_samples_sha256"]
            or sha(source) != fixture["sha256"] or sha(raw) != fixture["codestream_sha256"]
            or [row["type"] for row in boxes] != ["jP  ", "ftyp", "jp2h", "jp2c"]):
        raise ValueError("unexpected frozen palette index source")
    start = boxes[0]["bytes"] + boxes[1]["bytes"]
    end = start + boxes[2]["bytes"]
    for name, columns, definitions, row, expected in CASES:
        table = [row(index) for index in range(256)]
        descriptors = bytes(precision - 1 | (int(signed) << 7) for precision, signed in columns)
        entries = b"".join(
            (value % (1 << precision)).to_bytes((precision + 7) // 8, "big")
            for values in table for (precision, _), value in zip(columns, values, strict=True))
        mappings = [(0, 1, column) for column in range(len(columns))]
        cdef = [(column, *definition) for column, defs in enumerate(definitions) for definition in defs]
        additions = (box(b"pclr", struct.pack(">HB", len(table), len(columns)) + descriptors + entries)
                     + box(b"cmap", b"".join(struct.pack(">HBB", *mapping) for mapping in mappings)))
        if cdef:
            additions += box(b"cdef", struct.pack(">H", len(cdef))
                             + b"".join(struct.pack(">3H", *definition) for definition in cdef))
        data = source[:start] + box(b"jp2h", source[start + 8:end] + additions) + source[end:]
        if sha(data) != expected:
            raise ValueError(f"{name}: regenerated JP2 differs from the frozen #479 hash")
        yield ({
            "id": name, "group": "palette-target", "format": "jp2", "api": "decode_jp2",
            "bytes": len(data), "sha256": expected, "width": width, "height": height,
            "channels": len(columns), "license": "MIT; repository LICENSE",
            "origin": "First-party #479 table over frozen smooth-gray-lossless.jp2",
            "index_fixture": SOURCE, "index_jp2_sha256": sha(source),
            "index_codestream_sha256": sha(raw), "index_samples_sha256": sha(indices),
            "palette_entries": len(table), "palette_columns": list(descriptors),
            "component_mapping": [list(mapping) for mapping in mappings],
            "channel_definitions": [list(definition) for definition in cdef],
            "expected_native": typed_oracle(width, height, indices, columns, definitions, table),
        }, data)
