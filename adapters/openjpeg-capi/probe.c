#include <openjpeg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static OPJ_SIZE_T read_file(void *buffer, OPJ_SIZE_T size, void *user) {
    size_t read = fread(buffer, 1, size, user);
    return read ? read : (OPJ_SIZE_T)-1;
}

static void close_file(void *user) { fclose(user); }

int main(int argc, char **argv) {
    if (argc != 3)
        return 2;
    FILE *file = fopen(argv[2], "rb");
    if (!file)
        return 2;
    if (fseek(file, 0, SEEK_END) != 0) {
        fclose(file);
        return 2;
    }
    long length = ftell(file);
    if (length <= 0 || fseek(file, 0, SEEK_SET) != 0) {
        fclose(file);
        return 2;
    }
    opj_stream_t *stream = opj_stream_create(4096, OPJ_TRUE);
    if (!stream) {
        fclose(file);
        return 2;
    }
    opj_stream_set_user_data(stream, file, close_file);
    opj_stream_set_user_data_length(stream, (OPJ_UINT64)length);
    opj_stream_set_read_function(stream, read_file);
    opj_codec_t *codec = opj_create_decompress(argv[1][0] == 'b' ?
        OPJ_CODEC_JP2 : OPJ_CODEC_J2K);
    opj_dparameters_t parameters;
    opj_set_default_decoder_parameters(&parameters);
    opj_image_t *image = NULL;
    int status = 1;
    if (!codec || !opj_setup_decoder(codec, &parameters) ||
        !opj_read_header(stream, codec, &image))
        goto cleanup;

    printf("header %u %u %u %u %u\n", image->x0, image->y0, image->x1, image->y1,
           image->numcomps);
    for (uint32_t i = 0; i < image->numcomps; ++i) {
        const opj_image_comp_t *c = &image->comps[i];
        if (c->data)
            goto cleanup;
        printf("plane %u %u %u %u %u %u\n", c->w, c->h, c->dx, c->dy, c->prec, c->sgnd);
    }
    if (!opj_decode(codec, stream, image))
        goto cleanup;
    printf("color %d\n", (int)image->color_space);
    for (uint32_t i = 0; i < image->numcomps; ++i) {
        const opj_image_comp_t *c = &image->comps[i];
        if (!c->data)
            goto cleanup;
        for (uint64_t j = 0; j < (uint64_t)c->w * c->h; ++j)
            printf("%d\n", c->data[j]);
    }
    status = 0;
cleanup:
    if (image)
        opj_image_destroy(image);
    if (codec)
        opj_destroy_codec(codec);
    opj_stream_destroy(stream);
    return status;
}
