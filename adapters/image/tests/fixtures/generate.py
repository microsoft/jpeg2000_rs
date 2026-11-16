"""Reproduce synthetic lossless fixtures using Pillow's independent OpenJPEG codec."""

import struct
from pathlib import Path

from PIL import Image, features

ROOT = Path(__file__).parent
SIZE = (9, 7)
SAVE = dict(format="JPEG2000", irreversible=False, num_resolutions=2, mct=0)


def save(name, image, *, raw=False, **settings):
    path = ROOT / f"{name}.{'j2k' if raw else 'jp2'}"
    image.save(path, no_jp2=raw, **SAVE, **settings)
    with Image.open(path) as decoded:
        assert decoded.size == image.size
        assert list(decoded.get_flattened_data()) == list(image.get_flattened_data()), name
    values = list(image.get_flattened_data())
    samples = [v for pixel in values for v in (pixel if isinstance(pixel, tuple) else (pixel,))]
    if image.mode != "I;16":
        samples = [value * 257 for value in samples]
    (ROOT / f"{name}.u16le").write_bytes(struct.pack(f"<{len(samples)}H", *samples))


def box(kind, payload):
    return struct.pack(">I", len(payload) + 8) + kind + payload


def boxes(data):
    offset = 0
    while offset < len(data):
        length, kind = struct.unpack_from(">I4s", data, offset)
        assert length >= 8 and offset + length <= len(data)
        yield kind, data[offset + 8:offset + length]
        offset += length


def remap(name, source, expected, color, extra, *, reference_pixels=None):
    result = []
    for kind, payload in boxes(source):
        if kind == b"jp2h":
            children = [
                box(child, b"\x01\x00\x00" + struct.pack(">I", color)
                    if child == b"colr" else content)
                for child, content in boxes(payload)
            ]
            payload = b"".join(children) + extra
        result.append(box(kind, payload))
    path = ROOT / f"{name}.jp2"
    path.write_bytes(b"".join(result))
    with Image.open(path) as decoded:
        assert list(decoded.convert("RGB").get_flattened_data()) == (
            expected if reference_pixels is None else reference_pixels
        ), name
    samples = [v * 257 for pixel in expected for v in pixel]
    (ROOT / f"{name}.u16le").write_bytes(struct.pack(f"<{len(samples)}H", *samples))


def shifted_origin(source, expected):
    result = []
    for kind, payload in boxes(source):
        if kind == b"jp2c":
            payload = bytearray(payload)
            siz = payload.index(b"\xff\x51")
            # A two-pixel translation preserves the one-level DWT phase.
            for field in [6, 10, 14, 18, 30, 34]:
                value = struct.unpack_from(">I", payload, siz + field)[0]
                struct.pack_into(">I", payload, siz + field, value + 2)
        result.append(box(kind, payload))
    path = ROOT / "rgb-origin8.jp2"
    path.write_bytes(b"".join(result))
    with Image.open(path) as decoded:
        assert decoded.size == SIZE
        assert list(decoded.get_flattened_data()) == expected
    (ROOT / "rgb-origin8.u16le").write_bytes((ROOT / "rgb8.u16le").read_bytes())


def pixels(channels):
    return [
        tuple((x * 29 + y * 47 + c * 71) % 256 for c in range(channels))
        for y in range(SIZE[1])
        for x in range(SIZE[0])
    ]


if __name__ == "__main__":
    print("Pillow", Image.__version__, "OpenJPEG", features.version("jpg_2000"))
    assert features.check("jpg_2000")
    gray = Image.new("L", SIZE)
    gray.putdata([p[0] for p in pixels(1)])
    rgb = Image.new("RGB", SIZE)
    rgb.putdata(pixels(3))
    rgba = Image.new("RGBA", SIZE)
    rgba.putdata(pixels(4))
    la = Image.new("LA", SIZE)
    la.putdata(pixels(2))
    words = [0, 1, 255, 256, 4095, 32767, 32768, 65534, 65535] * SIZE[1]
    gray16 = Image.frombytes("I;16", SIZE, struct.pack(f"<{len(words)}H", *words))
    for name, image in [("gray8", gray), ("rgb8", rgb), ("rgba8", rgba), ("gray-alpha8", la),
                        ("gray16", gray16)]:
        save(name, image)
    save("raw-rgb8", rgb, raw=True)
    save("raw-gray8", gray, raw=True)
    shifted_origin((ROOT / "rgb8.jp2").read_bytes(), pixels(3))
    save("rgb-tiled8", rgb, tile_size=(5, 4))

    palette = [(255, 0, 0), (0, 255, 0), (0, 0, 255)]
    indices = Image.new("L", SIZE)
    indices.putdata([i % 3 for i in range(SIZE[0] * SIZE[1])])
    encoded = ROOT / "palette-index-source.jp2"
    indices.save(encoded, **SAVE)
    pclr = box(b"pclr", struct.pack(">HB", 3, 3) + b"\x07" * 3 +
               bytes(v for pixel in palette for v in pixel))
    cmap = box(b"cmap", b"".join(struct.pack(">HBB", 0, 1, column) for column in range(3)))
    remap("palette8", encoded.read_bytes(),
          [palette[i % 3] for i in range(SIZE[0] * SIZE[1])], 16, pclr + cmap)
    encoded.unlink()

    cdef = box(b"cdef", struct.pack(">H", 3) +
               b"".join(struct.pack(">HHH", channel, 0, 3 - channel) for channel in range(3)))
    remap("reordered8", (ROOT / "rgb8.jp2").read_bytes(),
          [tuple(reversed(pixel)) for pixel in pixels(3)], 16, cdef,
          # Pillow leaves cdef association-only permutations in physical order.
          reference_pixels=pixels(3))

    neutral = Image.new("RGB", SIZE, (128, 128, 128))
    encoded = ROOT / "sycc-source.jp2"
    neutral.save(encoded, **SAVE)
    remap("sycc8", encoded.read_bytes(), [(128, 128, 128)] * (SIZE[0] * SIZE[1]), 18, b"")
    encoded.unlink()
