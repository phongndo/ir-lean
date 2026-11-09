#pragma once

#include "llama.h"

#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

// Correctness instrumentation for a private copy of the stock completion driver.
class exact_capture {
  std::string prefix;
  std::ofstream logits;
  std::ofstream tokens;
  std::ofstream positions;
  int32_t n_vocab;
  size_t prompt_count = 0;
  size_t steps = 0;
  bool pending = false;

  static std::ofstream open(const std::string &path) {
    std::ofstream out;
    out.exceptions(std::ios::failbit | std::ios::badbit);
    out.open(path, std::ios::binary | std::ios::trunc);
    return out;
  }

  static std::string output_prefix() {
    const char *value = std::getenv("LLAMA_EXACT_OUTPUT_PREFIX");
    if (!value || !*value)
      throw std::runtime_error("set LLAMA_EXACT_OUTPUT_PREFIX to a new output filename prefix");
    for (const char *suffix : {".logits.f32", ".tokens.i32", ".positions.i32", ".prompt.i32", ".json"}) {
      if (std::filesystem::exists(std::string(value) + suffix))
        throw std::runtime_error("capture output exists: " + std::string(value) + suffix);
    }
    return value;
  }

public:
  explicit exact_capture(const llama_vocab *vocab)
      : prefix(output_prefix()), logits(open(prefix + ".logits.f32")), tokens(open(prefix + ".tokens.i32")),
        positions(open(prefix + ".positions.i32")), n_vocab(llama_vocab_n_tokens(vocab)) {
    static_assert(sizeof(float) == 4 && std::numeric_limits<float>::is_iec559, "requires IEEE754 binary32");
    static_assert(sizeof(llama_token) == 4, "requires 32-bit token IDs");
    const uint32_t endian = 1;
    if (*reinterpret_cast<const unsigned char *>(&endian) != 1 || n_vocab <= 0)
      throw std::runtime_error("requires little-endian host and positive vocabulary size");
  }

  void prompt(const std::vector<llama_token> &values) {
    auto out = open(prefix + ".prompt.i32");
    out.write(reinterpret_cast<const char *>(values.data()), values.size() * sizeof(llama_token));
    out.close();
    prompt_count = values.size();
  }

  void before_sample(llama_context *ctx, int32_t n_past) {
    if (pending)
      throw std::runtime_error("previous logits have no sampled token");
    const float *values = llama_get_logits_ith(ctx, -1);
    if (!values)
      throw std::runtime_error("no logits before sampling");
    logits.write(reinterpret_cast<const char *>(values), size_t(n_vocab) * sizeof(float));
    positions.write(reinterpret_cast<const char *>(&n_past), sizeof(n_past));
    pending = true;
  }

  void sampled(llama_token token) {
    if (!pending || token < 0 || token >= n_vocab)
      throw std::runtime_error("invalid sampled token or missing logits");
    tokens.write(reinterpret_cast<const char *>(&token), sizeof(token));
    pending = false;
    ++steps;
  }

  void finish() {
    if (pending || steps == 0 || prompt_count == 0)
      throw std::runtime_error("capture is incomplete or empty");
    logits.close();
    tokens.close();
    positions.close();
    auto metadata = open(prefix + ".json");
    metadata << "{\"format\":\"llama-completion-exact-v1\",\"endianness\":\"little\","
             << "\"n_vocab\":" << n_vocab << ",\"prompt_tokens\":" << prompt_count
             << ",\"sampled_tokens\":" << steps << ",\"logit_rows\":" << steps
             << ",\"logits_bytes\":" << steps * size_t(n_vocab) * sizeof(float) << "}\n";
    metadata.close();
  }
};
