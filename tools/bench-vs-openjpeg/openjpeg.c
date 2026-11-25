#define _POSIX_C_SOURCE 200809L
#include <openjpeg.h>
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct {
    const unsigned char *data;
    size_t size, position;
    OPJ_CODEC_FORMAT format;
} Input;

typedef struct {
    opj_image_t *image;
    uint64_t **planes;
} Output;

static void fail(const char *message) {
    fprintf(stderr, "benchmark failed: %s\n", message);
    exit(1);
}

static void error_message(const char *message, void *unused) {
    (void)unused;
    fprintf(stderr, "OpenJPEG: %s", message);
}

static OPJ_SIZE_T read_memory(void *buffer, OPJ_SIZE_T count, void *user) {
    Input *input = user;
    size_t left = input->size - input->position;
    if (!left) return (OPJ_SIZE_T)-1;
    if (count > left) count = left;
    memcpy(buffer, input->data + input->position, count);
    input->position += count;
    return count;
}

static OPJ_OFF_T skip_memory(OPJ_OFF_T count, void *user) {
    Input *input = user;
    if (count < 0 || (uint64_t)count > input->size - input->position)
        return -1;
    input->position += (size_t)count;
    return count;
}

static OPJ_BOOL seek_memory(OPJ_OFF_T offset, void *user) {
    Input *input = user;
    if (offset < 0 || (uint64_t)offset > input->size) return OPJ_FALSE;
    input->position = (size_t)offset;
    return OPJ_TRUE;
}

static uint64_t number(const char *text) {
    char *end;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno || text[0] == '-' || !*text || *end) fail("invalid integer");
    return value;
}

static void window_values(const char *text, int *window) {
    for (unsigned i = 0; i < 4; ++i) {
        const char *start = text;
        uint64_t value = 0;
        while (*text >= '0' && *text <= '9') {
            value = value * 10 + (unsigned)(*text++ - '0');
            if (value > INT32_MAX) fail("invalid window");
        }
        if (text == start || (i < 3 ? *text != ',' : *text != '\0'))
            fail("invalid window");
        window[i] = (int)value;
        if (i < 3) ++text;
    }
    if (window[2] <= 0 || window[3] <= 0 ||
        (int64_t)window[0] + window[2] > INT32_MAX ||
        (int64_t)window[1] + window[3] > INT32_MAX)
        fail("invalid window");
}

static uint64_t now(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value)) fail("clock_gettime");
    return (uint64_t)value.tv_sec * UINT64_C(1000000000) + (uint64_t)value.tv_nsec;
}

static Output decode(Input input, unsigned reduce, const int *window, int typed,
                     int threads) {
    input.position = 0;
    Output output = {0};
    opj_dparameters_t parameters;
    opj_set_default_decoder_parameters(&parameters);
    opj_codec_t *codec = opj_create_decompress(input.format);
    opj_stream_t *stream = opj_stream_create(65536, OPJ_TRUE);
    if (!codec || !stream) fail("codec/stream allocation");
    opj_set_error_handler(codec, error_message, NULL);
    opj_set_warning_handler(codec, error_message, NULL);
    opj_stream_set_user_data(stream, &input, NULL);
    opj_stream_set_user_data_length(stream, input.size);
    opj_stream_set_read_function(stream, read_memory);
    opj_stream_set_skip_function(stream, skip_memory);
    opj_stream_set_seek_function(stream, seek_memory);
    if (!opj_setup_decoder(codec, &parameters) ||
        !opj_codec_set_threads(codec, threads) ||
        !opj_read_header(stream, codec, &output.image) ||
        !opj_set_decoded_resolution_factor(codec, reduce))
        fail("decoder setup/header/resolution");
    if (window && !opj_set_decode_area(codec, output.image,
            window[0], window[1], window[0] + window[2], window[1] + window[3]))
        fail("decode area");
    if (!opj_decode(codec, stream, output.image) || !opj_end_decompress(codec, stream))
        fail("decode/end_decompress");
    if (typed) {
        output.planes = calloc(output.image->numcomps, sizeof(*output.planes));
        if (!output.planes) fail("plane pointer allocation");
        for (OPJ_UINT32 c = 0; c < output.image->numcomps; ++c) {
            const opj_image_comp_t *plane = &output.image->comps[c];
            uint64_t count = (uint64_t)plane->w * plane->h;
            if (count > SIZE_MAX / sizeof(uint64_t)) fail("output size overflow");
            output.planes[c] = malloc((size_t)count * sizeof(uint64_t));
            if (!output.planes[c] && count) fail("typed output allocation");
            for (uint64_t i = 0; i < count; ++i)
                output.planes[c][i] = (uint64_t)(int64_t)plane->data[i];
        }
    }
    opj_destroy_codec(codec);
    opj_stream_destroy(stream);
    return output;
}

static void destroy(Output output) {
    if (output.planes) {
        for (OPJ_UINT32 c = 0; c < output.image->numcomps; ++c)
            free(output.planes[c]);
        free(output.planes);
    }
    opj_image_destroy(output.image);
}

static void retain(Output output) {
    /* Make all output stores observable before stopping the timer. */
    __asm__ __volatile__("" : : "g"(output.image), "g"(output.planes) : "memory");
}

static void word(uint64_t value) {
    unsigned char bytes[8];
    for (unsigned i = 0; i < 8; ++i) bytes[i] = (unsigned char)(value >> (8 * i));
    if (fwrite(bytes, 1, 8, stdout) != 8) fail("output write");
}

static void dump(Output output, unsigned reduce, const int *window) {
    uint64_t x0 = output.image->x0, y0 = output.image->y0;
    uint64_t x1 = output.image->x1, y1 = output.image->y1;
    uint64_t scale = UINT64_C(1) << reduce;
    if (window) {
        if (x0 < (uint64_t)window[0]) x0 = (uint64_t)window[0];
        if (y0 < (uint64_t)window[1]) y0 = (uint64_t)window[1];
        if (x1 > (uint64_t)window[0] + (uint64_t)window[2])
            x1 = (uint64_t)window[0] + (uint64_t)window[2];
        if (y1 > (uint64_t)window[1] + (uint64_t)window[3])
            y1 = (uint64_t)window[1] + (uint64_t)window[3];
    }
    if (x1 <= x0 || y1 <= y0) fail("empty output canvas");
    word((x1 + scale - 1) / scale - (x0 + scale - 1) / scale);
    word((y1 + scale - 1) / scale - (y0 + scale - 1) / scale);
    word(output.image->numcomps);
    for (OPJ_UINT32 c = 0; c < output.image->numcomps; ++c) {
        const opj_image_comp_t *plane = &output.image->comps[c];
        word(plane->w);
        word(plane->h);
        word(plane->prec);
        word(plane->sgnd);
        for (uint64_t i = 0; i < (uint64_t)plane->w * plane->h; ++i)
            word(output.planes[c][i]);
    }
}

int main(int argc, char **argv) {
    if (argc != 8) fail("usage: bench-openjpeg INPUT typed|native|dump REDUCE x,y,w,h|- ITERATIONS MINIMUM_MS WARMUPS");
    if (strcmp(opj_version(), "2.5.4")) fail("OpenJPEG 2.5.4 required");
    int native = !strcmp(argv[2], "native"), dumping = !strcmp(argv[2], "dump");
    if (!native && !dumping && strcmp(argv[2], "typed")) fail("unknown output mode");
    uint64_t reduce = number(argv[3]), iterations = number(argv[5]);
    uint64_t minimum_ms = number(argv[6]), warmups = number(argv[7]);
    if (reduce > 32 || !iterations || minimum_ms > UINT64_MAX / 1000000)
        fail("invalid reduction/iteration/duration");
    int window[4], *area = NULL;
    if (strcmp(argv[4], "-")) {
        window_values(argv[4], window);
        area = window;
    }
    int threads = 1;
    if (getenv("BENCH_OPENJPEG_THREADS")) {
        uint64_t count = number(getenv("BENCH_OPENJPEG_THREADS"));
        if (!count || count > 256) fail("invalid thread count");
        threads = (int)count;
    }
    FILE *file = fopen(argv[1], "rb");
    if (!file || fseek(file, 0, SEEK_END)) fail("input open/seek");
    long length = ftell(file);
    if (length <= 0 || fseek(file, 0, SEEK_SET)) fail("input length/seek");
    unsigned char *bytes = malloc((size_t)length);
    if (!bytes || fread(bytes, 1, (size_t)length, file) != (size_t)length)
        fail("input allocation/read");
    if (fclose(file)) fail("input close");
    static const unsigned char jp2_signature[] = {0, 0, 0, 12, 'j', 'P', ' ', ' ', 13, 10, 135, 10};
    OPJ_CODEC_FORMAT format = (size_t)length >= sizeof(jp2_signature) &&
        !memcmp(bytes, jp2_signature, sizeof(jp2_signature)) ? OPJ_CODEC_JP2 : OPJ_CODEC_J2K;
    Input input = {bytes, (size_t)length, 0, format};
    if (dumping) {
        Output output = decode(input, (unsigned)reduce, area, 1, threads);
        dump(output, (unsigned)reduce, area);
        destroy(output);
    } else {
        for (uint64_t i = 0; i < warmups; ++i) {
            Output output = decode(input, (unsigned)reduce, area, !native, threads);
            retain(output);
            destroy(output);
        }
        uint64_t count = 0, total = 0, capacity = 64;
        uint64_t *times = malloc(capacity * sizeof(*times));
        if (!times) fail("timing allocation");
        while (count < iterations || total < minimum_ms * UINT64_C(1000000)) {
            if (count == capacity) {
                if (capacity > SIZE_MAX / (2 * sizeof(*times))) fail("timing size");
                capacity *= 2;
                uint64_t *grown = realloc(times, capacity * sizeof(*times));
                if (!grown) fail("timing growth");
                times = grown;
            }
            uint64_t start = now();
            Output output = decode(input, (unsigned)reduce, area, !native, threads);
            retain(output);
            uint64_t elapsed = now() - start;
            destroy(output);
            total += elapsed;
            times[count++] = elapsed;
        }
        for (uint64_t i = 0; i < count; ++i)
            printf("SAMPLE\t%" PRIu64 "\n", times[i]);
        free(times);
    }
    free(bytes);
    if (fflush(stdout)) fail("output flush");
    return 0;
}
