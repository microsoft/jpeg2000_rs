"""Authored and tracked public entry-path fixtures; no external downloads."""

from pathlib import Path
import struct

from generate_fixtures import jp2_parts, sha
from native_comparison import checked_bytes
from native_palette import box

ROOT = Path(__file__).resolve().parents[2]
PSOT = "validation/fixtures/hayro-sized-eoc/tile_parts_missing_eoc.j2k"
PSOT_HASH = "31ca91d8ad893468b21e5452f93fd46973a3e370829e255d33ed8d4e8f1b7c44"
PSOT_ZERO = "ed81f4211b84a5b0ce9b9ea0782202fb7e0a999d70877866824e1bbcf27da2f8"
TINY = {
    1: "df1abe6330374120f7bb5507009f82943f35d132ae0904314e38b3afeb534924",
    3: "573c379f461926d0d99a2e5beb059a1c666ce256a0b2fb8dc0f1b9032f51651b",
}


def boxed(raw, w, h, count, color):
    return (box(b"jP  ", bytes.fromhex("0d0a870a"))
            + box(b"ftyp", b"jp2 \0\0\0\0jp2 ")
            + box(b"jp2h", box(b"ihdr", struct.pack(">IIH4B", h, w, count, 7, 7, 0, 0))
                  + box(b"colr", struct.pack(">3BI", 1, 0, 0, color)))
            + box(b"jp2c", raw))


def tiny(count):
    """#483's exact 1x1 JP2 with authored empty packets (level-shifted 128)."""
    def segment(marker, payload):
        return struct.pack(">HH", marker, len(payload) + 2) + payload

    siz = struct.pack(">H8IH", 0, 1, 1, 0, 0, 1, 1, 0, 0, count)
    siz += b"".join(bytes((7, i + 1, 1)) for i in range(count))
    raw = (b"\xff\x4f" + segment(0xff51, siz)
           + segment(0xff52, bytes((0, 0, 0, 1, 0, 0, 0, 0, 0, 1)))
           + segment(0xff5c, b"\0\x40")
           + segment(0xff90, struct.pack(">HIBB", 0, 14 + count, 0, 1))
           + b"\xff\x93" + bytes(count) + b"\xff\xd9")
    return boxed(raw, 1, 1, count, 17 if count == 1 else 16)


def tiles(raw):
    if raw[:4] != b"\xff\x4f\xff\x51":
        raise ValueError("missing first SIZ")
    xs, ys, xo, yo, tw, th, tx, ty = struct.unpack_from(">8I", raw, 8)
    if not tw or not th or tx > xo or ty > yo:
        raise ValueError("unexpected fixture tile grid")
    return ((xs - tx + tw - 1) // tw) * ((ys - ty + th - 1) // th)


def fixtures(output):
    rows = []

    def add(name, payload, w, h, count, *, mode, origin, expected=None, fmt="jp2",
            header=False, blocked=None, refusal=False, precision_steps=None, tile_count=None,
            iterations=16, pinned=None, license="MIT; repository LICENSE", color=None):
        row = dict(id=name, path=f"{name}.{fmt}", format=fmt, bytes=len(payload), sha256=sha(payload),
                   width=w, height=h, channels=count, mode=mode, origin=origin, license=license,
                   lossless=expected is not None, source_samples_sha256=sha(expected) if expected else None,
                   cpp_block_reason=blocked, header_phase=header, expect_refusal=refusal,
                   iterations=iterations, tiny_dx=precision_steps, tiles=tile_count, color=color)
        if pinned is not None and row["sha256"] != pinned:
            raise ValueError(f"{name}: source differs from pinned receipt")
        (output / row["path"]).write_bytes(payload)
        rows.append(row)

    for count, color in ((1, 2), (3, 1)):
        for mode in ("strict", "compatible"):
            add(f"component-{count}-{mode}", tiny(count), 1, 1, count, mode=mode,
                origin="#483 authored tiny_box", header=True, expected=bytes([128]) * count,
                precision_steps=list(range(1, count + 1)), pinned=TINY[count], color=color,
                iterations=512, blocked="Root-only #483 phase probe; no OpenJPEG header-prefix equivalence asserted.")

    source = checked_bytes((ROOT / PSOT).read_bytes(),
                           dict(bytes=7587, sha256=PSOT_HASH, id=PSOT))
    if source[119:121] != b"\xff\x90" or len(source) != 119 + int.from_bytes(source[125:129], "big"):
        raise ValueError("unexpected #483 terminal tile-part extent")
    psot0 = source[:125] + bytes(4) + source[129:]
    for mode in ("strict", "compatible"):
        add(f"psot-zero-missing-eoc-{mode}", psot0, 128, 96, 1, mode=mode, fmt="j2k",
            origin=PSOT + " (#483 changes only Psot to zero)", pinned=PSOT_ZERO,
            license="MIT; validation/fixtures/hayro-sized-eoc/LICENSE-MIT",
            header=mode == "compatible", refusal=mode == "strict",
            blocked="Truncation recovery control; no cross-decoder recovery equivalence asserted.")

    for source_name, count, digest in (
        ("rgb8", 1, "dba2e08f48e96e832e72c5f8da823e1700ee1444be58187e28e7669f0b130adb"),
        ("rgb-tiled8", 4, "1b2f0de069efec0a30043db31412a247c00e02a6856702c71ae4d1e223dc778d"),
    ):
        path = f"adapters/image/tests/fixtures/{source_name}.jp2"
        payload = (ROOT / path).read_bytes()
        raw, _, _ = jp2_parts(payload)
        if sha(payload) != digest or tiles(raw) != count:
            raise ValueError(f"{path}: changed source or tile grid")
        expected = bytes((x * 29 + y * 47 + c * 71) % 256
                         for y in range(7) for x in range(9) for c in range(3))
        name = "pdf-single-tile" if count == 1 else "pdf-multi-tile"
        add(name, payload + b"\r\n", 9, 7, 3, mode="compatible", tile_count=count,
            origin=path + " + PDF CRLF; oracle: adapters/image/tests/fixtures/generate.py",
            expected=expected, color=1, iterations=128,
            blocked="Root PDF CRLF recovery path; exact authored samples qualify only Root ratios.")
        if count == 1:
            add(name + "-strict-refusal", payload + b"\r\n", 9, 7, 3, mode="strict",
                tile_count=count, origin=path + " + PDF CRLF", refusal=True,
                blocked="Negative control: strict Root must not enter PDF CRLF recovery.")

    if tiles(source) != 1:
        raise ValueError("unexpected MIT missing-EOC regression tile grid")
    add("pdf-mit-sized-eoc", boxed(source, 128, 96, 1, 17), 128, 96, 1, mode="compatible",
        origin=PSOT + " in authored JP2 envelope (source codestream unchanged)", tile_count=1,
        license="MIT; validation/fixtures/hayro-sized-eoc/LICENSE-MIT",
        blocked="Tracked MIT sized missing-EOC regression, no independent cross-decoder recovery oracle.")
    return rows
