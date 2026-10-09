#!/bin/sh
# build.sh: build the two programs of the view, each when a source is newer.
#   draw   the replay of one stream of device calls: to PNG, or the key under a pixel
#   play   a window over a folder of frames, which plays the motion between them (SDL2)
# Nothing is downloaded: cairo, pango and SDL2 are the system's, found by pkg-config.
#
#   tools/view/build.sh          build into tools/view
#   OUT=dir tools/view/build.sh  build into another folder
#
# Every warning is an error. The headers of pango, cairo, glib and SDL2 are system headers here,
# so their own warnings do not count.
set -eu
cd "$(dirname "$0")"
OUT=${OUT:-.}
CC=${CC:-cc}
WARN="-std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Werror"
stale() { [ ! -x "$OUT/$1" ] || [ "$1.c" -nt "$OUT/$1" ] || [ paint.h -nt "$OUT/$1" ] || [ replay.h -nt "$OUT/$1" ]; }
if stale draw; then
  # shellcheck disable=SC2046
  $CC $WARN -O2 $(pkg-config --cflags pangocairo | sed 's/-I/-isystem /g') draw.c \
    $(pkg-config --libs pangocairo) -lm -o "$OUT/draw"
fi
if stale play; then
  # shellcheck disable=SC2046
  $CC $WARN -O2 $(pkg-config --cflags pangocairo sdl2 | sed 's/-I/-isystem /g') play.c \
    $(pkg-config --libs pangocairo sdl2) -lm -o "$OUT/play"
fi
