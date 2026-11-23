#include <openjpeg.h>
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifdef NDEBUG
#error "These regression tests require assertions"
#endif

struct Bytes {
    uint8_t data[4096];
    size_t size;
};

struct Reader {
    const struct Bytes *input;
    size_t offset;
};

struct Decoder {
    struct Reader reader;
    opj_stream_t *stream;
    opj_codec_t *codec;
    opj_image_t *image;
    unsigned errors;
};

static void byte(struct Bytes *b, uint8_t value) {
    assert(b->size < sizeof(b->data));
    b->data[b->size++] = value;
}

static void u16(struct Bytes *b, uint16_t value) {
    byte(b, (uint8_t)(value >> 8));
    byte(b, (uint8_t)value);
}

static void u32(struct Bytes *b, uint32_t value) {
    u16(b, (uint16_t)(value >> 16));
    u16(b, (uint16_t)value);
}

static void append(struct Bytes *b, const void *data, size_t size) {
    assert(size <= sizeof(b->data) - b->size);
    memcpy(b->data + b->size, data, size);
    b->size += size;
}

static void box(struct Bytes *b, const char kind[4], const struct Bytes *body) {
    u32(b, (uint32_t)body->size + 8);
    append(b, kind, 4);
    append(b, body->data, body->size);
}

static void marker(struct Bytes *b, uint16_t kind, const struct Bytes *body) {
    u16(b, kind);
    u16(b, (uint16_t)body->size + 2);
    append(b, body->data, body->size);
}

static struct Bytes codestream(uint32_t x0, uint32_t y0, uint32_t width,
                               uint32_t height, uint8_t sampling,
                               uint16_t components, uint8_t levels) {
    struct Bytes result = {0}, siz = {0}, cod = {0}, qcd = {0}, sot = {0};
    u16(&result, 0xff4f);
    u16(&siz, 0);
    u32(&siz, x0 + width);
    u32(&siz, y0 + height);
    u32(&siz, x0);
    u32(&siz, y0);
    u32(&siz, x0 + width);
    u32(&siz, y0 + height);
    u32(&siz, 0);
    u32(&siz, 0);
    u16(&siz, components);
    for (uint16_t i = 0; i < components; ++i) {
        byte(&siz, 7);
        byte(&siz, sampling);
        byte(&siz, sampling);
    }
    marker(&result, 0xff51, &siz);
    append(&cod, (uint8_t[]){0, 0, 0, 1, 0, levels, 0, 0, 0, 1}, 10);
    marker(&result, 0xff52, &cod);
    byte(&qcd, 0);
    for (unsigned i = 0; i < 1u + 3u * levels; ++i)
        byte(&qcd, 0x40);
    marker(&result, 0xff5c, &qcd);
    unsigned packets = components * (levels + 1u);
    u16(&sot, 0);
    u32(&sot, 14 + packets);
    byte(&sot, 0);
    byte(&sot, 1);
    marker(&result, 0xff90, &sot);
    u16(&result, 0xff93);
    for (unsigned i = 0; i < packets; ++i)
        byte(&result, 0);
    u16(&result, 0xffd9);
    return result;
}

static struct Bytes jp2(const struct Bytes *stream, uint16_t components,
                         uint32_t color, unsigned palette_bits) {
    struct Bytes result = {0}, header = {0}, image = {0}, colr = {0};
    struct Bytes signature = {{0x0d, 0x0a, 0x87, 0x0a}, 4};
    struct Bytes type = {{'j', 'p', '2', ' ', 0, 0, 0, 0, 'j', 'p', '2', ' '}, 12};
    box(&result, "jP  ", &signature);
    box(&result, "ftyp", &type);
    u32(&image, 1);
    u32(&image, 1);
    u16(&image, components);
    append(&image, (uint8_t[]){7, 7, 0, 0}, 4);
    box(&header, "ihdr", &image);
    byte(&colr, color ? 1 : 2);
    byte(&colr, 0);
    byte(&colr, 0);
    if (color)
        u32(&colr, color);
    else
        byte(&colr, 0);
    box(&header, "colr", &colr);
    if (palette_bits) {
        struct Bytes palette = {0}, mapping = {0}, definitions = {0};
        u16(&palette, 256);
        byte(&palette, 2);
        byte(&palette, 7);
        byte(&palette, palette_bits == 5 ? 0x84 : 31);
        for (unsigned i = 0; i < 256; ++i) {
            byte(&palette, i == 128 ? 42 : 0);
            if (palette_bits == 5)
                byte(&palette, i == 128 ? 0x1d : 0);
            else
                u32(&palette, i == 128 ? UINT32_MAX : 0);
        }
        box(&header, "pclr", &palette);
        append(&mapping, (uint8_t[]){0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0}, 12);
        box(&header, "cmap", &mapping);
        u16(&definitions, 3);
        append(&definitions, (uint8_t[]){
            0, 0, 0, 0, 0, 1,
            0, 1, 0, 1, 0, 1,
            0, 2, 0xff, 0xff, 0xff, 0xff
        }, 18);
        box(&header, "cdef", &definitions);
    }
    box(&result, "jp2h", &header);
    box(&result, "jp2c", stream);
    return result;
}

static OPJ_SIZE_T read_bytes(void *dest, OPJ_SIZE_T requested, void *user) {
    struct Reader *reader = user;
    size_t remaining = reader->input->size - reader->offset;
    size_t count = requested < remaining ? requested : remaining;
    memcpy(dest, reader->input->data + reader->offset, count);
    reader->offset += count;
    return count ? count : (OPJ_SIZE_T)-1;
}

static void error_callback(const char *message, void *user) {
    struct Decoder *decoder = user;
    assert(message && *message);
    ++decoder->errors;
}

static void open_stream(struct Decoder *d, const struct Bytes *input) {
    d->reader = (struct Reader){input, 0};
    d->stream = opj_stream_create(4096, OPJ_TRUE);
    assert(d->stream);
    opj_stream_set_user_data(d->stream, &d->reader, NULL);
    opj_stream_set_user_data_length(d->stream, input->size);
    opj_stream_set_read_function(d->stream, read_bytes);
}

static void open_decoder(struct Decoder *d, const struct Bytes *input,
                          int boxed, int indexed, int lenient, unsigned reduce) {
    memset(d, 0, sizeof(*d));
    open_stream(d, input);
    d->codec = opj_create_decompress(boxed ? OPJ_CODEC_JP2 : OPJ_CODEC_J2K);
    assert(d->codec);
    assert(opj_set_error_handler(d->codec, error_callback, d));
    opj_dparameters_t parameters;
    opj_set_default_decoder_parameters(&parameters);
    parameters.cp_reduce = reduce;
    if (indexed)
        parameters.flags |= OPJ_DPARAMETERS_IGNORE_PCLR_CMAP_CDEF_FLAG;
    assert(opj_setup_decoder(d->codec, &parameters));
    if (lenient)
        assert(opj_decoder_set_strict_mode(d->codec, OPJ_FALSE));
    assert(opj_read_header(d->stream, d->codec, &d->image));
    for (uint32_t i = 0; i < d->image->numcomps; ++i)
        assert(d->image->comps[i].data == NULL);
}

static void close_decoder(struct Decoder *d) {
    opj_image_destroy(d->image);
    opj_destroy_codec(d->codec);
    opj_stream_destroy(d->stream);
}

static void test_origin(unsigned sampling, unsigned reduce) {
    struct Bytes input = codestream(3, 5, 5, 3, (uint8_t)sampling, 1,
                                    (uint8_t)reduce);
    struct Decoder d;
    open_decoder(&d, &input, 0, 0, 0, reduce);
    assert(d.image->x0 == 3 && d.image->y0 == 5);
    assert(d.image->x1 == 8 && d.image->y1 == 8);
    unsigned full_width = (8 + sampling - 1) / sampling -
                          (3 + sampling - 1) / sampling;
    unsigned full_height = (8 + sampling - 1) / sampling -
                           (5 + sampling - 1) / sampling;
    unsigned reduction = 1u << reduce;
    assert(d.image->comps[0].w == (full_width + reduction - 1) / reduction);
    assert(d.image->comps[0].h == (full_height + reduction - 1) / reduction);
    opj_image_comp_t *original = d.image->comps;
    assert(opj_set_decode_area(d.codec, d.image, 3, 5, 8, 8));
    unsigned scale = sampling << reduce;
    assert(d.image->comps[0].w == (8 + scale - 1) / scale -
                                 (3 + scale - 1) / scale);
    assert(d.image->comps[0].h == (8 + scale - 1) / scale -
                                 (5 + scale - 1) / scale);
    assert(opj_decode(d.codec, d.stream, d.image));
    assert(d.image->comps == original);
    assert(opj_end_decompress(d.codec, d.stream));
    opj_image_comp_t *c = &d.image->comps[0];
    assert(c->x0 == (3 + sampling - 1) / sampling);
    assert(c->y0 == (5 + sampling - 1) / sampling);
    assert(c->w == (8 + scale - 1) / scale - (3 + scale - 1) / scale);
    assert(c->h == (8 + scale - 1) / scale - (5 + scale - 1) / scale);
    assert(c->factor == reduce);
    for (size_t i = 0; i < (size_t)c->w * c->h; ++i)
        assert(c->data[i] == 128);
    assert(d.errors == 0);
    close_decoder(&d);
}

static void test_palette(int indexed, int lenient) {
    struct Bytes stream = codestream(0, 0, 1, 1, 1, 1, 0);
    struct Bytes input = jp2(&stream, 1, 17, 5);
    if (lenient)
        byte(&input, '\n');
    struct Decoder d;
    open_decoder(&d, &input, 1, indexed, lenient, 0);
    assert(d.image->numcomps == 1);
    opj_image_comp_t *original = d.image->comps;
    assert(opj_decode(d.codec, d.stream, d.image));
    assert(d.image->numcomps == (indexed ? 1u : 3u));
    if (indexed) {
        assert(d.image->comps == original);
        assert(d.image->comps[0].prec == 8);
        assert(d.image->comps[0].data[0] == 128);
        assert(d.image->comps[0].alpha == 0);
    } else {
        assert(d.image->comps[0].prec == 8);
        assert(d.image->comps[0].data[0] == 42);
        assert(d.image->comps[1].prec == 5 && d.image->comps[1].sgnd == 1);
        assert(d.image->comps[1].data[0] == -3);
        assert(d.image->comps[1].alpha == 1);
        assert(d.image->comps[2].data[0] == 128);
    }
    assert(d.errors == 0);
    close_decoder(&d);
}

static void test_unhandled_color(uint32_t color) {
    struct Bytes stream = codestream(0, 0, 1, 1, 1, 3, 0);
    struct Bytes input = jp2(&stream, 3, color, 0);
    struct Decoder d;
    open_decoder(&d, &input, 1, 0, 0, 0);
    assert(d.image->color_space == OPJ_CLRSPC_UNSPECIFIED);
    assert(opj_decode(d.codec, d.stream, d.image));
    assert(d.image->numcomps == 3);
    for (unsigned i = 0; i < 3; ++i)
        assert(d.image->comps[i].data[0] == 128);
    assert(d.errors == 0);
    close_decoder(&d);
}

static void test_output_failure_preserves_header(void) {
    struct Bytes stream = codestream(0, 0, 1, 1, 1, 1, 0);
    struct Bytes valid = jp2(&stream, 1, 17, 5);
    struct Bytes input = jp2(&stream, 1, 17, 32);
    struct Decoder d;
    open_decoder(&d, &valid, 1, 0, 0, 0);
    assert(opj_decode(d.codec, d.stream, d.image));
    assert(opj_end_decompress(d.codec, d.stream));
    opj_image_destroy(d.image);
    opj_stream_destroy(d.stream);
    open_stream(&d, &input);
    assert(opj_read_header(d.stream, d.codec, &d.image));
    opj_image_comp_t *original = d.image->comps;
    assert(!opj_decode(d.codec, d.stream, d.image));
    assert(!opj_end_decompress(d.codec, d.stream));
    assert(d.image->numcomps == 1 && d.image->comps == original);
    assert(d.image->comps[0].data == NULL);
    assert(d.errors == 1);
    close_decoder(&d);
}

static void test_lenient_ht(int boxed, int indexed) {
    static const uint8_t raw[] = {
        0xff, 0x4f, 0xff, 0x51, 0x00, 0x29, 0x40, 0x00,
        0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 1, 7, 1, 1,
        0xff, 0x50, 0, 8, 0, 2, 0, 0, 0, 8,
        0xff, 0x52, 0, 12, 0, 0, 0, 1, 0, 0, 0, 0, 0x40, 1,
        0xff, 0x5c, 0, 4, 0, 0x40,
        0xff, 0x90, 0, 10, 0, 0, 0, 0, 0, 15, 0, 1,
        0xff, 0x93, 0, 0xff, 0xd9
    };
    struct Bytes stream = {0};
    append(&stream, raw, sizeof(raw));
    struct Bytes input = boxed ? jp2(&stream, 1, 17, 0) : stream;
    if (boxed == 2) {
        memcpy(input.data + 20, "jph ", 4);
        memcpy(input.data + 28, "jph ", 4);
    }
    struct Decoder d;
    open_decoder(&d, &input, boxed != 0, indexed, 1, 0);
    assert(opj_decode(d.codec, d.stream, d.image));
    assert(d.image->numcomps == 1 && d.image->comps[0].data[0] == 128);
    assert(opj_end_decompress(d.codec, d.stream));
    assert(d.errors == 0);
    close_decoder(&d);
}

static void test_lenient_jpx(int baseline, int indexed) {
    struct Bytes stream = codestream(0, 0, 1, 1, 1, 1, 0);
    struct Bytes input = jp2(&stream, 1, 17, 0);
    const char *brand = baseline ? "jpxb" : "jpx ";
    memcpy(input.data + 20, brand, 4);
    memcpy(input.data + 28, brand, 4);
    struct Decoder d;
    open_decoder(&d, &input, 1, indexed, 1, 0);
    assert(opj_decode(d.codec, d.stream, d.image));
    assert(d.image->numcomps == 1 && d.image->comps[0].data[0] == 128);
    assert(opj_end_decompress(d.codec, d.stream));
    assert(d.errors == 0);
    close_decoder(&d);
}

int main(void) {
    test_origin(1, 0);
    test_origin(2, 0);
    test_origin(1, 1);
    for (int indexed = 0; indexed <= 1; ++indexed)
        for (int lenient = 0; lenient <= 1; ++lenient)
            test_palette(indexed, lenient);
    test_unhandled_color(14);
    test_unhandled_color(0);
    test_output_failure_preserves_header();
    for (int boxed = 0; boxed <= 2; ++boxed)
        for (int indexed = 0; indexed <= 1; ++indexed)
            test_lenient_ht(boxed, indexed);
    for (int baseline = 0; baseline <= 1; ++baseline)
        for (int indexed = 0; indexed <= 1; ++indexed)
            test_lenient_jpx(baseline, indexed);
    puts("20 OpenJPEG adapter regression cases passed");
    return 0;
}
