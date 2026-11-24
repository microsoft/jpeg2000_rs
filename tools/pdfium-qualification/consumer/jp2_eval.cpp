#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

#include "core/fxcodec/jpx/cjpx_decoder.h"
#include "public/fpdfview.h"

namespace {

struct Result {
  std::string status;
  uint32_t width = 0;
  uint32_t height = 0;
  uint32_t channels = 0;
  int color = 0;
  std::vector<uint8_t> pixels;
};

Result Image(const std::vector<uint8_t>& input,
             bool strict,
             uint8_t reduce,
             bool indexed) {
  auto decoder = CJPX_Decoder::Create(
      input, indexed ? CJPX_Decoder::ColorSpaceOption::kIndexed
                     : CJPX_Decoder::ColorSpaceOption::kNormal,
      reduce, strict);
  if (!decoder) {
    return {"header_error"};
  }
  if (!decoder->StartDecode()) {
    return {"decode_error"};
  }
  auto info = decoder->GetInfo();
  Result result{"output_limit", info.width, info.height, info.channels,
                static_cast<int>(info.colorspace)};
  uint64_t row = static_cast<uint64_t>(info.width) * info.channels;
  uint64_t pitch = (row + 3) & ~uint64_t{3};
  if (!info.width || !info.height || !info.channels || info.channels > 16 ||
      pitch > UINT32_MAX || pitch * info.height > 512 * 1024 * 1024) {
    return result;
  }
  std::vector<uint8_t> padded(pitch * info.height);
  if (!decoder->Decode(padded, static_cast<uint32_t>(pitch), false,
                       info.channels)) {
    result.status = "pack_error";
    return result;
  }
  result.pixels.reserve(row * info.height);
  for (uint32_t y = 0; y < info.height; ++y) {
    auto begin = padded.begin() + y * pitch;
    result.pixels.insert(result.pixels.end(), begin, begin + row);
  }
  result.status = "ok";
  return result;
}

Result Pdf(const std::vector<uint8_t>& input) {
  FPDF_DOCUMENT doc = FPDF_LoadMemDocument64(input.data(), input.size(), nullptr);
  if (!doc) {
    return {"document_error"};
  }
  Result result{"ok"};
  int count = FPDF_GetPageCount(doc);
  for (int i = 0; i < count; ++i) {
    FPDF_PAGE page = FPDF_LoadPage(doc, i);
    if (!page) {
      result.status = "page_error";
      break;
    }
    int w = static_cast<int>(FPDF_GetPageWidthF(page) + 0.5f);
    int h = static_cast<int>(FPDF_GetPageHeightF(page) + 0.5f);
    if (w <= 0 || h <= 0 || static_cast<uint64_t>(w) * h > 32000000) {
      FPDF_ClosePage(page);
      result.status = "output_limit";
      break;
    }
    FPDF_BITMAP bitmap = FPDFBitmap_Create(w, h, 1);
    if (!bitmap) {
      FPDF_ClosePage(page);
      result.status = "bitmap_error";
      break;
    }
    FPDFBitmap_FillRect(bitmap, 0, 0, w, h, 0xffffffff);
    FPDF_RenderPageBitmap(bitmap, page, 0, 0, w, h, 0, FPDF_ANNOT);
    auto* data = static_cast<uint8_t*>(FPDFBitmap_GetBuffer(bitmap));
    int stride = FPDFBitmap_GetStride(bitmap);
    for (int y = 0; y < h; ++y) {
      result.pixels.insert(result.pixels.end(), data + y * stride,
                           data + y * stride + w * 4);
    }
    result.width = static_cast<uint32_t>(w);
    result.height += static_cast<uint32_t>(h);
    result.channels = 4;
    result.color = count;
    FPDFBitmap_Destroy(bitmap);
    FPDF_ClosePage(page);
  }
  FPDF_CloseDocument(doc);
  return result;
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 8) {
    std::fprintf(stderr, "mode input output strict reduce indexed repetitions\n");
    return 2;
  }
  std::ifstream file(argv[2], std::ios::binary);
  if (!file) {
    std::perror(argv[2]);
    return 2;
  }
  std::vector<uint8_t> input((std::istreambuf_iterator<char>(file)), {});
  bool pdf = std::string(argv[1]) == "pdf";
  if (pdf) {
    FPDF_LIBRARY_CONFIG config{};
    config.version = 2;
    FPDF_InitLibraryWithConfig(&config);
  }
  bool strict = std::atoi(argv[4]) != 0;
  uint8_t reduce = static_cast<uint8_t>(std::atoi(argv[5]));
  bool indexed = std::atoi(argv[6]) != 0;
  int runs = std::atoi(argv[7]);
  auto decode = [&]() {
    return pdf ? Pdf(input) : Image(input, strict, reduce, indexed);
  };
  Result result = decode();
  std::vector<double> times;
  if (result.status == "ok") {
    std::ofstream output(argv[3], std::ios::binary);
    output.write(reinterpret_cast<const char*>(result.pixels.data()),
                 result.pixels.size());
    if (!output) {
      std::fprintf(stderr, "Cannot write pixels\n");
      return 2;
    }
    for (int i = 0; runs && i < 3; ++i) {
      if (decode().status != "ok") {
        std::fprintf(stderr, "Warmup failed\n");
        return 2;
      }
    }
    for (int i = 0; i < runs; ++i) {
      auto start = std::chrono::steady_clock::now();
      auto repeated = decode();
      double us = std::chrono::duration<double, std::micro>(
                      std::chrono::steady_clock::now() - start).count();
      if (repeated.status != "ok" || repeated.pixels != result.pixels) {
        std::fprintf(stderr, "Non-repeatable decode\n");
        return 2;
      }
      times.push_back(us);
    }
  }
  std::sort(times.begin(), times.end());
  double p50 = times.empty() ? 0 : times[times.size() / 2];
  double p90 = times.empty() ? 0 : times[times.size() * 9 / 10];
  std::printf("%s\t%u\t%u\t%u\t%d\t%.3f\t%.3f\t%zu\n",
              result.status.c_str(), result.width, result.height,
              result.channels, result.color, p50, p90, times.size());
  if (pdf) {
    FPDF_DestroyLibrary();
  }
  return 0;
}
