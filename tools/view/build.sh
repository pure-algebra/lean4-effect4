#!/bin/sh
# build.sh: build the programs of the view, each when a source is newer.
#   draw        the replay of one stream of device calls: to PNG, or the key under a pixel
#   play        a window over a folder of frames, which plays the motion between them, or over a
#               live session's patches (SDL3, vendored)
#   scene_test  the check of the retained store (scene.h) against Lean's whole streams, built with
#               the address and undefined-behaviour sanitizers
# cairo and pango are the system's, found by pkg-config. SDL3 is vendored by pin: its first build
# fetches and verifies the tarball (vendor/SDL3-3.4.16/fetch.sh) and builds it static.
#
#   tools/view/build.sh              build draw and play into tools/view
#   tools/view/build.sh scene_test   build the named programs only
#   OUT=dir tools/view/build.sh      build into another folder
#
# Every warning is an error. The headers of pango, cairo, glib and SDL3 are system headers here,
# so their own warnings do not count.
set -eu
cd "$(dirname "$0")"
OUT=${OUT:-.}
CC=${CC:-cc}
WARN="-std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Werror"
stale() { [ ! -x "$OUT/$1" ] || [ "$1.c" -nt "$OUT/$1" ] || [ paint.h -nt "$OUT/$1" ] || [ replay.h -nt "$OUT/$1" ] || [ scene.h -nt "$OUT/$1" ]; }
for target in ${*:-draw play}; do
  case $target in
  draw)
    if stale draw; then
      # shellcheck disable=SC2046
      $CC $WARN -O2 $(pkg-config --cflags pangocairo | sed 's/-I/-isystem /g') draw.c \
        $(pkg-config --libs pangocairo) -lm -o "$OUT/draw"
    fi ;;
  play)
    # play links SDL3, built static from its pin into tools/view/sdl3 the first time
    if [ ! -f sdl3/lib/libSDL3.a ]; then ../../vendor/SDL3-3.4.16/build.sh sdl3 > /dev/null; fi
    if stale play || [ sdl3/lib/libSDL3.a -nt "$OUT/play" ]; then
      SDL3=$(PKG_CONFIG_PATH=sdl3/lib/pkgconfig pkg-config --static --cflags --libs sdl3 | sed 's/-I/-isystem /g')
      # shellcheck disable=SC2046,SC2086
      $CC $WARN -O2 $(pkg-config --cflags pangocairo | sed 's/-I/-isystem /g') play.c \
        $(pkg-config --libs pangocairo) $SDL3 -o "$OUT/play"
    fi ;;
  scene_test)
    if stale scene_test; then
      $CC $WARN -D_POSIX_C_SOURCE=200809L -O1 -g -fsanitize=address,undefined scene_test.c -o "$OUT/scene_test"
    fi ;;
  *) echo "build.sh: no program $target; the programs are draw, play and scene_test" >&2; exit 2 ;;
  esac
done
