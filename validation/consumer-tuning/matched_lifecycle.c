/* Memory-stream derivative of adapters/openjpeg-capi/probe.c. Public API only. */
#define _POSIX_C_SOURCE 200809L
#include <openjpeg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

struct trial {
    const unsigned char *data;
    size_t size, offset;
    unsigned reads, skips, seeks, bytes, errors, warnings, infos, phase;
    FILE *dump;
};

static OPJ_SIZE_T read_memory(void *buffer, OPJ_SIZE_T size, void *user) {
    struct trial *t = user;
    size_t n = t->size - t->offset;
    if (n > size) n = size;
    memcpy(buffer, t->data + t->offset, n);
    t->offset += n;
    t->reads++;
    t->bytes += n;
    return n ? n : (OPJ_SIZE_T)-1;
}

static OPJ_BOOL seek_memory(OPJ_OFF_T offset, void *user) {
    struct trial *t = user;
    t->seeks++;
    if (offset < 0 || (uint64_t)offset > t->size) return OPJ_FALSE;
    t->offset = (size_t)offset;
    return OPJ_TRUE;
}

static OPJ_OFF_T skip_memory(OPJ_OFF_T amount, void *user) {
    struct trial *t = user;
    t->skips++;
    if (amount < -(OPJ_OFF_T)t->offset || amount > (OPJ_OFF_T)(t->size - t->offset))
        return -1;
    t->offset = (size_t)((OPJ_OFF_T)t->offset + amount);
    return amount;
}

static void message(struct trial *t, char kind, const char *text) {
    if (t->dump && fprintf(stderr, "%u %c %zu:", t->phase, kind, strlen(text)) < 0) abort();
    if (t->dump && fputs(text, stderr) == EOF) abort();
}

static void error(const char *text, void *user) {
    struct trial *t = user;
    t->errors++;
    message(t, 'E', text);
}

static void warning(const char *text, void *user) {
    struct trial *t = user;
    t->warnings++;
    message(t, 'W', text);
}

static void info(const char *text, void *user) {
    struct trial *t = user;
    t->infos++;
    message(t, 'I', text);
}

static void write_all(FILE *out, const void *data, size_t width, size_t count) {
    if (count && fwrite(data, width, count, out) != count) abort();
}

static void snapshot(FILE *out, const opj_image_t *image) {
    const uint32_t present = image != NULL;
    write_all(out, &present, sizeof(present), 1);
    if (!image) return;
    const uint32_t fields[] = {
        image->x0, image->y0, image->x1, image->y1, image->numcomps,
        (uint32_t)image->color_space, image->icc_profile_len, image->icc_profile_buf != NULL
    };
    write_all(out, fields, sizeof(*fields), sizeof(fields) / sizeof(*fields));
    if (image->icc_profile_buf)
        write_all(out, image->icc_profile_buf, 1, image->icc_profile_len);
    if (!image->comps || image->numcomps > 256) abort();
    for (uint32_t i = 0; i < image->numcomps; ++i) {
        const opj_image_comp_t *c = &image->comps[i];
        const uint32_t plane[] = {
            c->w, c->h, c->x0, c->y0, c->dx, c->dy, c->prec, c->sgnd,
            c->factor, c->alpha, c->resno_decoded, c->data != NULL
        };
        write_all(out, plane, sizeof(*plane), sizeof(plane) / sizeof(*plane));
        if (c->data) {
            const uint64_t count = (uint64_t)c->w * c->h;
            if (count > 32000000) abort();
            write_all(out, c->data, sizeof(*c->data), (size_t)count);
        }
    }
}

static uint64_t now(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) abort();
    return (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
}

int main(int argc, char **argv) {
    _Static_assert(sizeof(OPJ_INT32) == 4, "S32 output required");
    if (argc != 4 && argc != 5) return 2;
    FILE *file = fopen(argv[2], "rb");
    if (!file || fseek(file, 0, SEEK_END)) return 2;
    long length = ftell(file);
    if (length <= 0 || length > 16 * 1024 * 1024 || fseek(file, 0, SEEK_SET)) return 2;
    unsigned char *data = malloc((size_t)length);
    if (!data || fread(data, 1, (size_t)length, file) != (size_t)length || fclose(file)) return 2;
    FILE *dump = argc == 5 ? fopen(argv[4], "wb") : NULL;
    if (argc == 5 && !dump) return 2;
    unsigned iterations = (unsigned)strtoul(argv[3], NULL, 10);
    if ((dump && iterations) || (!dump && !iterations) || iterations > 1024) return 2;
    const unsigned warmups = dump ? 0 : 2;
    for (unsigned i = 0; i < (dump ? 1 : warmups + iterations); ++i) {
        struct trial t = {.data = data, .size = (size_t)length, .dump = dump};
        opj_image_t *image = NULL;
        opj_dparameters_t parameters;
        uint64_t start = dump ? 0 : now();
        opj_stream_t *stream = opj_stream_create(4096, OPJ_TRUE);
        opj_codec_t *codec = opj_create_decompress(!strcmp(argv[1], "jp2") ? OPJ_CODEC_JP2 : OPJ_CODEC_J2K);
        opj_set_default_decoder_parameters(&parameters);
        if (!stream || !codec || !opj_set_error_handler(codec, error, &t) ||
            !opj_set_warning_handler(codec, warning, &t) || !opj_set_info_handler(codec, info, &t) ||
            !opj_setup_decoder(codec, &parameters) || !opj_decoder_set_strict_mode(codec, OPJ_TRUE))
            return 2;
        opj_stream_set_user_data(stream, &t, NULL);
        opj_stream_set_user_data_length(stream, t.size);
        opj_stream_set_read_function(stream, read_memory);
        opj_stream_set_skip_function(stream, skip_memory);
        opj_stream_set_seek_function(stream, seek_memory);
        t.phase = 1;
        unsigned header = !!opj_read_header(stream, codec, &image);
        if (dump) snapshot(dump, image);
        t.phase = 2;
        unsigned decoded = header && image && opj_decode(codec, stream, image);
        t.phase = 3;
        unsigned ended = decoded && opj_end_decompress(codec, stream);
        if (dump) snapshot(dump, image);
        /* Escape the same planes in all builds, without a timed pixel scan. */
        if (decoded) {
            for (uint32_t c = 0; c < image->numcomps; ++c) {
                if (!image->comps[c].data) return 2;
                __asm__ volatile("" : : "g"(image->comps[c].data) : "memory");
            }
        }
        t.phase = 4;
        if (image) opj_image_destroy(image);
        opj_destroy_codec(codec);
        opj_stream_destroy(stream);
        uint64_t elapsed = dump ? 0 : now() - start;
        printf("status %u %u %u %u %u %u %u %u %u %u\n", header, decoded, ended,
               t.errors, t.warnings, t.infos, t.reads, t.skips, t.seeks, t.bytes);
        if (i >= warmups && !dump) printf("sample %llu\n", (unsigned long long)elapsed);
    }
    free(data);
    if (dump && fclose(dump)) return 2;
    return ferror(stdout) || ferror(stderr) ? 2 : 0;
}
