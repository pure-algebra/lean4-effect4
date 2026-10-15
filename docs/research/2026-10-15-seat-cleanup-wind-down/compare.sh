#!/bin/bash
# Seat CLEANUP, S3 (2026-10-15): every moved byte of a regenerated OCaml file is layout.
# For each file named, the committed version (at a revision) and the working copy are parsed by
# ocamlc (-stop-after parsing). The parse trees (-dparsetree) are compared with every source
# location removed, so the comparison is exact on the tree and blind to layout only. The
# parser drops comments, so the comments of both versions are compared as ordered lists,
# whitespace collapsed.
#   compare.sh <path>...              a revision against the working copy, per path; the
#                                     revision is $COMPARE_BASE (default HEAD), e.g. 68765c384
#   compare.sh --pair <old> <new>     two files (the controls)
set -u
root=$(git rev-parse --show-toplevel)
out=${COMPARE_OUT:-$root/scratch/s3/compare}
rev=${COMPARE_BASE:-HEAD}
rm -rf "$out" && mkdir -p "$out"
status=0
n=0

side() {  # side <file> <dir>: the file's parse tree without locations, and its comments
  local file=$1 dir=$2 base
  base=$(basename "$file")
  mkdir -p "$dir" && cp "$file" "$dir/$base"
  (cd "$dir" && opam exec --switch=effect4 -- ocamlfind ocamlc -stop-after parsing -dparsetree -c "$base" \
    2> "$base.parsetree.raw" > "$base.stdout")
  python3 - "$dir/$base" > "$dir/$base.comments" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
for c in re.findall(r'\(\*(.*?)\*\)', text, re.S):
    print(' '.join(c.split()))
EOF
  python3 - "$dir/$base.parsetree.raw" > "$dir/$base.parsetree" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
if 'structure_item' not in text:
    sys.exit(0)
print(re.sub(r' ?\([^()\n]*\[\d+,\d+\+\d+\]\.\.\[\d+,\d+\+\d+\]\)( ghost)?', '', text))
EOF
}

pair() {  # pair <old> <new> <label> <moved>
  local old=$1 new=$2 label=$3 moved=$4 base tree notes items
  n=$((n + 1))
  base=$(basename "$new")
  side "$old" "$out/$n/old"
  side "$new" "$out/$n/new"
  local a=$out/$n/old/$(basename "$old") b=$out/$n/new/$base
  if [ ! -s "$a.parsetree" ] || [ ! -s "$b.parsetree" ]; then tree="NO PARSE TREE"; status=1
  elif cmp -s "$a.parsetree" "$b.parsetree"; then tree="same parse tree"; else tree="PARSE TREE DIFFERS"; status=1; fi
  if cmp -s "$a.comments" "$b.comments"; then notes="same comments"; else notes="COMMENTS DIFFER"; status=1; fi
  items=$(grep -c '^  structure_item' "$b.parsetree.raw")
  echo "$label: $tree ($items structure items); $notes; lines $moved"
}

if [ "${1:-}" = "--pair" ]; then
  pair "$2" "$3" "$2 / $3" "-"
else
  for path in "$@"; do
    mkdir -p "$out/head"
    git -C "$root" show "$rev:$path" > "$out/head/$(basename "$path")"
    pair "$out/head/$(basename "$path")" "$root/$path" "$path" \
      "$(git -C "$root" diff --numstat "$rev" -- "$path" | awk '{print "+" $1 " -" $2}')"
  done
fi
exit $status
