#!/bin/sh
# build.sh: build `draw`, the replay of a stream of device calls (draw.c over paint.h).
# Nothing is downloaded: cairo and pango are the system's, found by pkg-config.
#
#   tools/view/build.sh          build tools/view/draw when a source is newer
#   OUT=dir tools/view/build.sh  build into another folder
#
# Every warning is an error. The headers of pango, cairo and glib are system headers here, so
# their own warnings do not count.
set -eu
cd "$(dirname "$0")"
OUT=${OUT:-.}
CC=${CC:-cc}
if [ -x "$OUT/draw" ] && [ "$OUT/draw" -nt draw.c ] && [ "$OUT/draw" -nt paint.h ]; then exit 0; fi
WARN="-std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Werror"
INC=$(pkg-config --cflags pangocairo | sed 's/-I/-isystem /g')
LIBS="$(pkg-config --libs pangocairo) -lm"
# shellcheck disable=SC2086
$CC $WARN -O2 $INC draw.c $LIBS -o "$OUT/draw"
