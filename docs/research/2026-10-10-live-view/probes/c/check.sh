#!/bin/sh
# Build scene_test with strict warnings and two sanitizers, and run it on the patch files that
# `sh ../run.sh PatchFiles` writes into ../out.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
cc -std=c11 -D_POSIX_C_SOURCE=200809L -Wall -Wextra -Werror -O1 -g \
  -fsanitize=address,undefined -o "$here/scene_test" "$here/scene_test.c"
"$here/scene_test" "$here/../out/pFork" "$here/../out/pScope" "$here/../out/chain6"
