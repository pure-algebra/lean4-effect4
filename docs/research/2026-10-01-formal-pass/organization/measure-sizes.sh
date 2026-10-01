#!/bin/bash
# Seat ORGANIZATION: module counts and line sizes by area (tracked files only).
# Usage: bash measure-sizes.sh   (reads git ls-files at the working tree; writes nothing)
cd /Users/pooks/Dev/lean4-effect4 || exit 1
echo "HEAD $(git rev-parse --short HEAD)"
area() { # $1 = label, $2.. = git pathspecs
  local label=$1; shift
  local files; files=$(git ls-files "$@")
  local n; n=$(printf '%s\n' "$files" | grep -c . )
  local l=0; if [ "$n" -gt 0 ]; then l=$(printf '%s\n' "$files" | xargs cat | wc -l | tr -d ' '); fi
  printf '%-40s %4s files %7s lines\n' "$label" "$n" "$l"
}
area "src/Effect4 (all .lean)" 'src/Effect4/**.lean' 'src/Effect4.lean'
area "src/Effect4/Laws" 'src/Effect4/Laws/**.lean' 'src/Effect4/Laws.lean'
area "src/Effect4 core (non-Laws)" ':(glob)src/Effect4/**/*.lean' ':(exclude,glob)src/Effect4/Laws/**' ':(exclude)src/Effect4/Laws.lean'
for d in Program Machine Store Codegen Schema Api Data Ingest; do area "core $d" "src/Effect4/$d/**.lean" "src/Effect4/$d.lean"; done
for d in Program Machine Codegen Auto Api Store Schema Effects; do area "Laws/$d" "src/Effect4/Laws/$d/**.lean" "src/Effect4/Laws/$d.lean"; done
for d in Guard Typed Intro Folds Simulation Typing Handles Authoring Agreement; do area "Laws/Program/$d" "src/Effect4/Laws/Program/$d/**.lean"; done
area "Laws/Program top-level files" ':(glob)src/Effect4/Laws/Program/*.lean'
area "Test (all .lean)" 'Test/**.lean'
area "tools (all .lean)" 'tools/**.lean'
area "generated/" 'generated/**'
area "src/OCaml5" 'src/OCaml5/**.lean'
