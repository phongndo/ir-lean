#!/bin/sh
# Prints a proved result, and exits as if it failed. The two disagree, so neither can be trusted.
cat "$(dirname "$0")/../fixtures/control_result.json"
exit 1
