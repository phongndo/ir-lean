#include <cstdio>
#include <exception>

int llama_completion(int argc, char **argv);

int main(int argc, char **argv) {
  try {
    return llama_completion(argc, argv);
  } catch (const std::exception &error) {
    std::fprintf(stderr, "exact capture failed: %s\n", error.what());
    return 2;
  }
}
