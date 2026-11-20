#include <openjpeg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct Header { uint32_t x0, y0, x1, y1, count; int32_t color; };
struct Plane { uint32_t width, height, precision, signedness, dx, dy, alpha; };
extern bool jpeg2000_compat_inspect_v2(const uint8_t *, size_t, bool, bool, uint32_t,
                          struct Header *, struct Plane *);
extern void *jpeg2000_compat_decode_v2(const uint8_t *, size_t, bool, bool, bool, uint8_t);
extern size_t jpeg2000_compat_component_count_v2(const void *);
extern bool jpeg2000_compat_plane_v2(const void *, uint32_t, struct Plane *);
extern bool jpeg2000_compat_copy_plane_v2(const void *, uint32_t, int32_t *, size_t,
                             const struct Plane *);
extern void jpeg2000_compat_destroy_v2(void *);

struct Codec {
    bool boxed, configured, indexed, strict, decoded;
    uint8_t reduce;
    opj_msg_callback error;
    void *error_user;
};
struct Stream {
    uint8_t *bytes;
    size_t size;
    uint64_t length;
    opj_stream_read_fn read;
    opj_stream_seek_fn seek;
    opj_stream_skip_fn skip;
    opj_stream_free_user_data_fn release;
    void *user;
};

static OPJ_BOOL fail(struct Codec *codec, const char *reason) {
    if (codec && codec->error)
        codec->error(reason, codec->error_user);
    return OPJ_FALSE;
}

OPJ_BOOL opj_set_error_handler(opj_codec_t *handle, opj_msg_callback callback, void *user) {
    struct Codec *codec = (struct Codec *)handle;
    if (!codec)
        return OPJ_FALSE;
    codec->error = callback;
    codec->error_user = user;
    return OPJ_TRUE;
}

OPJ_BOOL opj_set_info_handler(opj_codec_t *handle, opj_msg_callback callback, void *user) {
    (void)callback;
    (void)user;
    return handle != NULL;
}

OPJ_BOOL opj_set_warning_handler(opj_codec_t *handle, opj_msg_callback callback, void *user) {
    return opj_set_info_handler(handle, callback, user);
}

opj_codec_t *opj_create_decompress(OPJ_CODEC_FORMAT format) {
    if (format != OPJ_CODEC_J2K && format != OPJ_CODEC_JP2)
        return NULL;
    struct Codec *codec = calloc(1, sizeof(*codec));
    if (codec) {
        codec->boxed = format == OPJ_CODEC_JP2;
        codec->strict = true;
    }
    return (opj_codec_t *)codec;
}

void opj_destroy_codec(opj_codec_t *codec) { free(codec); }

void opj_set_default_decoder_parameters(opj_dparameters_t *params) {
    memset(params, 0, sizeof(*params));
    params->decod_format = -1;
    params->cod_format = -1;
}

OPJ_BOOL opj_setup_decoder(opj_codec_t *handle, opj_dparameters_t *params) {
    struct Codec *codec = (struct Codec *)handle;
    if (!codec || !params || params->cp_reduce > 31 || params->cp_layer ||
        (params->flags & ~OPJ_DPARAMETERS_IGNORE_PCLR_CMAP_CDEF_FLAG))
        return fail(codec, "Unsupported decoder parameters");
    codec->reduce = (uint8_t)params->cp_reduce;
    codec->indexed = (params->flags & OPJ_DPARAMETERS_IGNORE_PCLR_CMAP_CDEF_FLAG) != 0;
    codec->configured = true;
    return OPJ_TRUE;
}

OPJ_BOOL opj_decoder_set_strict_mode(opj_codec_t *handle, OPJ_BOOL strict) {
    struct Codec *codec = (struct Codec *)handle;
    if (!codec)
        return OPJ_FALSE;
    codec->strict = strict != OPJ_FALSE;
    return OPJ_TRUE;
}

opj_stream_t *opj_stream_create(OPJ_SIZE_T buffer_size, OPJ_BOOL read) {
    return buffer_size && read ? (opj_stream_t *)calloc(1, sizeof(struct Stream)) : NULL;
}

void opj_stream_set_read_function(opj_stream_t *handle, opj_stream_read_fn read) {
    ((struct Stream *)handle)->read = read;
}

void opj_stream_set_seek_function(opj_stream_t *handle, opj_stream_seek_fn seek) {
    ((struct Stream *)handle)->seek = seek;
}

void opj_stream_set_skip_function(opj_stream_t *handle, opj_stream_skip_fn skip) {
    ((struct Stream *)handle)->skip = skip;
}

void opj_stream_set_user_data(opj_stream_t *handle, void *user,
                              opj_stream_free_user_data_fn release) {
    struct Stream *stream = (struct Stream *)handle;
    stream->user = user;
    stream->release = release;
}

void opj_stream_set_user_data_length(opj_stream_t *handle, OPJ_UINT64 length) {
    ((struct Stream *)handle)->length = length;
}

void opj_stream_destroy(opj_stream_t *handle) {
    struct Stream *stream = (struct Stream *)handle;
    if (!stream)
        return;
    if (stream->release)
        stream->release(stream->user);
    free(stream->bytes);
    free(stream);
}

void opj_image_destroy(opj_image_t *image) {
    if (!image)
        return;
    for (uint32_t i = 0; i < image->numcomps; ++i)
        free(image->comps[i].data);
    free(image->comps);
    free(image->icc_profile_buf);
    free(image);
}

void *opj_image_data_alloc(OPJ_SIZE_T size) { return malloc(size); }
void opj_image_data_free(void *data) { free(data); }

static uint32_t component_offset(uint32_t origin, uint32_t sampling) {
    return (uint32_t)(((uint64_t)origin + sampling - 1) / sampling);
}

static uint32_t component_length(uint32_t start, uint32_t end,
                                 uint32_t sampling, uint8_t reduce) {
    uint64_t scale = (uint64_t)sampling << reduce;
    return (uint32_t)(((uint64_t)end + scale - 1) / scale -
                      ((uint64_t)start + scale - 1) / scale);
}

OPJ_BOOL opj_set_decode_area(opj_codec_t *handle, opj_image_t *image,
                             OPJ_INT32 x0, OPJ_INT32 y0, OPJ_INT32 x1, OPJ_INT32 y1) {
    if (handle && image && x0 >= 0 && y0 >= 0 &&
        ((x0 == 0 && y0 == 0) ||
         ((uint32_t)x0 == image->x0 && (uint32_t)y0 == image->y0)) &&
        ((x1 == 0 && y1 == 0) || (x1 > 0 && y1 > 0 &&
            (uint32_t)x1 == image->x1 && (uint32_t)y1 == image->y1))) {
        struct Codec *codec = (struct Codec *)handle;
        if (!image->comps)
            return fail(codec, "Invalid JPEG 2000 components");
        for (uint32_t i = 0; i < image->numcomps; ++i) {
            if (image->comps[i].data)
                return OPJ_TRUE;
            if (!image->comps[i].dx || !image->comps[i].dy)
                return fail(codec, "Invalid JPEG 2000 component sampling");
        }
        for (uint32_t i = 0; i < image->numcomps; ++i) {
            opj_image_comp_t *c = &image->comps[i];
            c->w = component_length(image->x0, image->x1, c->dx, codec->reduce);
            c->h = component_length(image->y0, image->y1, c->dy, codec->reduce);
        }
        return OPJ_TRUE;
    }
    return fail((struct Codec *)handle, "Only full-image decode is supported");
}

OPJ_BOOL opj_get_decoded_tile(opj_codec_t *handle, opj_stream_t *stream,
                              opj_image_t *image, OPJ_UINT32 index) {
    (void)stream;
    (void)image;
    (void)index;
    return fail((struct Codec *)handle, "Individual tile decode is not supported");
}

OPJ_BOOL opj_end_decompress(opj_codec_t *handle, opj_stream_t *stream) {
    struct Codec *codec = (struct Codec *)handle;
    return stream && codec && codec->decoded;
}

OPJ_BOOL opj_read_header(opj_stream_t *stream_handle, opj_codec_t *codec_handle,
                         opj_image_t **out) {
    struct Stream *stream = (struct Stream *)stream_handle;
    struct Codec *codec = (struct Codec *)codec_handle;
    if (!out)
        return OPJ_FALSE;
    *out = NULL;
    if (!codec || !codec->configured || !stream || !stream->read || stream->bytes ||
        !stream->length || stream->length > 16 * 1024 * 1024)
        return OPJ_FALSE;
    stream->bytes = malloc((size_t)stream->length);
    if (!stream->bytes)
        return OPJ_FALSE;
    while (stream->size < stream->length) {
        size_t remaining = (size_t)stream->length - stream->size;
        size_t n = stream->read(stream->bytes + stream->size, remaining, stream->user);
        if (!n || n > remaining)
            return OPJ_FALSE;
        stream->size += n;
    }

    struct Header header;
    struct Plane plane;
    if (!jpeg2000_compat_inspect_v2(stream->bytes, stream->size, codec->boxed,
                                codec->strict, 0, &header, &plane))
        return fail(codec, "Unsupported or invalid JPEG 2000 header");
    opj_image_t *image = calloc(1, sizeof(*image));
    if (!image)
        return OPJ_FALSE;
    image->comps = calloc(header.count, sizeof(*image->comps));
    if (!image->comps) {
        free(image);
        return OPJ_FALSE;
    }
    image->numcomps = header.count;
    image->x0 = header.x0;
    image->y0 = header.y0;
    image->x1 = header.x1;
    image->y1 = header.y1;
    image->color_space = (OPJ_COLOR_SPACE)header.color;
    for (uint32_t i = 0; i < image->numcomps; ++i) {
        if (i && !jpeg2000_compat_inspect_v2(stream->bytes, stream->size, codec->boxed,
                                         codec->strict, i, &header, &plane)) {
            opj_image_destroy(image);
            return OPJ_FALSE;
        }
        if (!plane.dx || !plane.dy) {
            opj_image_destroy(image);
            return fail(codec, "Invalid JPEG 2000 component sampling");
        }
        image->comps[i] = (opj_image_comp_t){
            .dx = plane.dx, .dy = plane.dy,
            .x0 = component_offset(header.x0, plane.dx),
            .y0 = component_offset(header.y0, plane.dy),
            .w = component_length(0, plane.width, 1, codec->reduce),
            .h = component_length(0, plane.height, 1, codec->reduce),
            .prec = plane.precision, .sgnd = plane.signedness, .factor = codec->reduce,
        };
    }
    codec->decoded = false;
    *out = image;
    return OPJ_TRUE;
}

OPJ_BOOL opj_decode(opj_codec_t *codec_handle, opj_stream_t *stream_handle,
                    opj_image_t *image) {
    struct Codec *codec = (struct Codec *)codec_handle;
    struct Stream *stream = (struct Stream *)stream_handle;
    if (!codec || !codec->configured || !stream || !stream->bytes || !image)
        return OPJ_FALSE;
    for (uint32_t i = 0; i < image->numcomps; ++i)
        if (image->comps[i].data)
            return OPJ_FALSE;
    codec->decoded = false;
    void *decoded = jpeg2000_compat_decode_v2(stream->bytes, stream->size, codec->boxed,
                                          codec->indexed, codec->strict, codec->reduce);
    if (!decoded)
        return fail(codec, "JPEG 2000 decode failed");
    size_t count = jpeg2000_compat_component_count_v2(decoded);
    if (!count || count > UINT32_MAX || count > SIZE_MAX / sizeof(*image->comps)) {
        jpeg2000_compat_destroy_v2(decoded);
        return fail(codec, "Invalid JPEG 2000 output component count");
    }
    opj_image_comp_t *components = calloc(count, sizeof(*components));
    if (!components) {
        jpeg2000_compat_destroy_v2(decoded);
        return fail(codec, "Cannot allocate JPEG 2000 output components");
    }
    bool ok = true;
    uint64_t remaining = 32000000;
    for (size_t i = 0; i < count; ++i) {
        opj_image_comp_t *c = &components[i];
        struct Plane plane;
        if (!jpeg2000_compat_plane_v2(decoded, (uint32_t)i, &plane)) {
            ok = false;
            break;
        }
        uint64_t samples = (uint64_t)plane.width * plane.height;
        if (!plane.dx || !plane.dy || !plane.precision || plane.precision > 31 ||
            !samples || samples > remaining ||
            !(c->data = opj_image_data_alloc((size_t)samples * sizeof(*c->data))) ||
            !jpeg2000_compat_copy_plane_v2(decoded, (uint32_t)i, c->data, (size_t)samples, &plane)) {
            ok = false;
            break;
        }
        c->w = plane.width;
        c->h = plane.height;
        c->prec = plane.precision;
        c->sgnd = plane.signedness;
        c->dx = plane.dx;
        c->dy = plane.dy;
        c->x0 = component_offset(image->x0, plane.dx);
        c->y0 = component_offset(image->y0, plane.dy);
        c->factor = codec->reduce;
        c->alpha = (OPJ_UINT16)plane.alpha;
        remaining -= samples;
    }
    jpeg2000_compat_destroy_v2(decoded);
    if (!ok) {
        for (size_t i = 0; i < count; ++i)
            free(components[i].data);
        free(components);
        return fail(codec, "Unsupported JPEG 2000 output plane");
    }
    if (image->numcomps == count) {
        memcpy(image->comps, components, count * sizeof(*components));
        free(components);
    } else {
        free(image->comps);
        image->comps = components;
    }
    image->numcomps = (OPJ_UINT32)count;
    codec->decoded = true;
    return OPJ_TRUE;
}
