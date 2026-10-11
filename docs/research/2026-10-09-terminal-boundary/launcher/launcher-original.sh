#!/bin/sh
# v: the frames of a program built by edits, in a window, a console or PNG files
# (docs/research/2026-10-09-visual-pipeline.md).
#
#   v NAME           build a corpus program top-down and play its frames in a window
#   v -r NAME        run a corpus program step by step: the program and its graph of fibers
#   v -g             the graph specimen: a graph built one edge at a time, cycles included
#   v -F             the program graph's specimen: fork and join, cross edges, regions, loops
#   v -f FILE        the frames of a session request file (tools/Drivers/Session.lean's input)
#   v -t NAME        the frames in this console, as characters
#   v -p NAME        write a PNG of every frame and every picture of motion
#   v -m N ...       N pictures of motion between two frames (default 20; 1 draws none)
#   v -P ...         no marks: the plain page (the marks wait for the owner's ruling)
#   v -l LOOK ...    in a look: a name of tools/view/looks (paper, hue, sans, ...) or a token file
#   v -L             every look side by side: tools/view/out/looks/index.html and a PNG of each
#
# NAME is a program of the wire corpus: p42 pBind pFork pAwait pGen pLoop pCatch pScope.
# The frames go to tools/view/out/NAME. In the window: Right or Space plays to the next frame,
# Left steps back, Home and End, Q quits.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
# lake comes from elan; a shell whose profile does not add it still finds it here
command -v lake > /dev/null 2>&1 || PATH="$HOME/.elan/bin:$PATH"
root=$(cd "$here/../.." && pwd)
mode=window; motion=20; file=""; plain=""; look=""; cmd=build
while [ $# -gt 0 ]; do
  case "$1" in
    -t) mode=text ;;
    -p) mode=png ;;
    -f) shift; file=$1 ;;
    -m) shift; motion=$1 ;;
    -P) plain=--plain ;;
    -l) shift; look=$1 ;;
    -L) cmd=looks ;;
    -r) cmd=run ;;
    -g) cmd=specimen ;;
    -F) cmd=flows ;;
    -h|--help) sed -n 2,19p "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) break ;;
  esac
  shift
done
if [ "$cmd" = looks ]; then
  out="$here/out/looks"
  rm -rf "$out"
  (cd "$root" && LEAN_NUM_THREADS=3 lake env lean --run tools/Drivers/View.lean looks tools/view/looks "$out")
  "$here/build.sh"
  for f in "$out"/*/*.draw; do "$here/draw" "$f" --png "${f%.draw}.png"; done
  echo "$out/index.html"
  exit 0
fi
case $look in
  ''|*/*) ;;
  *) [ -f "$here/looks/$look.tokens.json" ] || [ "$look" = dark ] || { echo "v: no look $look in $here/looks" >&2; exit 2; } ;;
esac
case $look in
  */*) look=$(cd "$(dirname "$look")" && pwd)/$(basename "$look") ;;
esac
if [ "$cmd" = specimen ] || [ "$cmd" = flows ]; then
  name=$cmd; out="$here/out/$cmd"
  set -- "$cmd" "$out"
elif [ -n "$file" ]; then
  name=$(basename "$file" .jsonl); out="$here/out/$name"
  file=$(cd "$(dirname "$file")" && pwd)/$(basename "$file")
  set -- session "$file" "$out"
else
  name=${1:?usage: v [-t | -p] [-r] [-m N] (NAME | -f FILE)}; out="$here/out/$name-$cmd"
  set -- "$cmd" "$name" "$out"
fi
rm -rf "$out"
if [ -n "$look" ]; then set -- --look "$look" "$@"; fi
(cd "$root" && LEAN_NUM_THREADS=3 lake env lean --run tools/Drivers/View.lean --motion "$motion" $plain "$@")
"$here/build.sh"
case $mode in
  text) cat "$out/frames.txt" ;;
  png) for f in "$out"/*.draw; do "$here/draw" "$f" --png "${f%.draw}.png"; done; echo "$out" ;;
  window) exec "$here/play" "$out" ;;
esac
