# The llama.cpp release tests/llama.py proves a rewrite of, and tests/llama_bench.py measures. It's 185 MB, which
# GitHub has to send each time, as no binary cache has it, so only `nix develop .#llama` has it, and not the
# default shell every CI job and `nix develop` start.
{ fetchFromGitHub }:
fetchFromGitHub {
  owner = "ggml-org";
  repo = "llama.cpp";
  rev = "b12189";
  hash = "sha256-Y57pW8G1grsd6QD+mIQ7F7b2S5bwWdSlH39eRRYr0b0=";
}
