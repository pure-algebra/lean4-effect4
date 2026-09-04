#!/usr/bin/env bash
# Seat F3: the Deep-file drift gate. The avatar is a port of `Effect4/Deep/*.lean` at one
# revision; `deep-pins.tsv` records the SHA-256 of every Lean file it was re-diffed against.
#
#   pin-deep.sh            # check: exit 1 naming every file whose digest moved
#   pin-deep.sh --write    # record the working tree's digests (after a re-diff)
#
# Rationale (docs/research/2026-09-04-seat-f3-ocaml-platform-critique.md §5.1): the count
# gate of `run-witnesses.sh` catches a theorem added or removed; it does not catch an arm
# re-spelled under the same name (R2-10 was one word). Gates stamp on content hashes.
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
pins="$here/deep-pins.tsv"
files=$(grep -v '^#' "$pins" | cut -f1)
if [ "${1:-}" = "--write" ]; then
  header=$(grep '^#' "$pins")
  { echo "$header"; (cd "$repo" && shasum -a 256 $files | awk '{print $2"\t"$1}'); } > "$pins.tmp" \
    && mv "$pins.tmp" "$pins"
  echo "deep-pins.tsv: RECORDED $(echo "$files" | wc -l | tr -d ' ') digests"
  exit 0
fi
status=0
while IFS=$'\t' read -r file want; do
  case "$file" in \#*|"") continue ;; esac
  have=$(cd "$repo" && shasum -a 256 "$file" | cut -d' ' -f1)
  if [ "$have" != "$want" ]; then
    echo "deep-pins: $file CHANGED since the avatar was re-diffed (pinned ${want:0:12}, tree ${have:0:12})"
    status=1
  fi
done < "$pins"
if [ $status = 0 ]; then echo "deep-pins: every pinned Deep file is at the re-diffed revision"; fi
exit $status
