#!/usr/bin/env bash
# Internal-citation gate: no line-numbered citation into a mutable authored
# document of this repository.
#
# A line citation into a pinned host source is stable. Those files are
# third-party bytes identified by digest, they are never edited here, and the
# census and field gates already refuse off-pin bytes. A line citation into one
# of this repository's own authored rulings is not stable. Those rulings are
# edited continuously, so a document name plus a line number silently
# retargets whenever a section above it grows or shrinks, and the citing
# sentence keeps asserting a claim the target no longer makes. That has already
# happened here: a proof-graph reallocation in `docs/SCHEMA-CUTOVER.md` moved
# the five `SC-WIRE-*` obligation rows, and citations elsewhere in the tree were
# left pointing at unrelated prose without any file being edited.
#
# This gate extracts every `<path>.<ext>:<line>` and `<path>.<ext>:<line>-<line>`
# citation token under the scanned trees and rejects the ones whose target is
# one of six protected authored documents:
#
#   docs/SCHEMA-CUTOVER.md    PLAN.md    AGENTS.md
#   docs/ARCHITECTURE.md      PORT-MANIFEST.md    docs/AGENT-ROUTING.md
#
# WHAT A PASS MEANS: in the scanned trees, no citation names one of those six
# documents together with a line number. Cite a section heading, an obligation
# ID such as `SC-WIRE-01`, a proof-graph node such as `SCHEMA-PG-WIRE`, or a
# short quoted phrase from the target instead.
#
# WHAT A PASS DOES NOT MEAN: nothing about whether a replacement anchor exists,
# whether the target still says what the citing sentence claims, or whether any
# other citation in the tree is correct. Line citations into the pinned host
# sources, into `vendor/foldlab/` evidence, and into `.lean` sources are
# examined and deliberately accepted; this gate makes no claim about them. It is
# a lexical scan, not a resolver, and it assigns no cutover status. Three
# further limits are named rather than glossed:
#
#   * a bare continuation citation such as `:123`, which inherits its document
#     from an earlier sentence, carries no document name and is invisible to
#     this scan;
#   * the five targets are matched exactly, after stripping one leading `./`,
#     so a different file with the same basename under another directory is a
#     different target and is not flagged; and
#   * `vendor/` is skipped wherever it appears, because that tree is read-only
#     pinned evidence whose internal citations belong to its own repository.
set -euo pipefail

protected_docs="docs/SCHEMA-CUTOVER.md SCHEMA-CUTOVER.md PLAN.md AGENTS.md docs/ARCHITECTURE.md ARCHITECTURE.md PORT-MANIFEST.md docs/AGENT-ROUTING.md AGENT-ROUTING.md"
scanned_trees="Effect4 Effect4Test docs test scripts harness"

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
root="$repo_root"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --root)
      shift
      [[ $# -gt 0 ]] || { printf 'FAIL --root needs a directory argument\n' >&2; exit 1; }
      root="$1"
      ;;
    -h|--help)
      cat <<'USAGE'
usage: check-internal-citations.sh [--root <dir>]

Scans Effect4/, Effect4Test/, docs/, test/, scripts/, and harness/ under <dir>
and rejects any citation that names one of the six protected authored
documents together with a line number.

--root defaults to this repository. Any other root reports a result about the
supplied tree only and closes nothing about this repository; it exists so the
reaction test in scripts/test-internal-citations-gate.sh can exercise this
detector hermetically.
USAGE
      exit 0
      ;;
    -*) printf 'FAIL unknown option: %s\n' "$1" >&2; exit 1 ;;
    *)  printf 'FAIL unexpected argument: %s\n' "$1" >&2; exit 1 ;;
  esac
  shift
done

[[ -d "$root" ]] || { printf 'FAIL root is not a directory: %s\n' "$root" >&2; exit 1; }
root="$(cd -- "$root" && pwd -P)"

scan_dirs=()
for tree in $scanned_trees; do
  [[ -d "$root/$tree" ]] && scan_dirs+=("$root/$tree")
done

if [[ "${#scan_dirs[@]}" -eq 0 ]]; then
  printf 'FAIL none of the scanned trees (%s) exist under %s\n' "$scanned_trees" "$root" >&2
  exit 1
fi

files=()
while IFS= read -r candidate; do
  case "$candidate" in
    */vendor/*) continue ;;
  esac
  grep -Iq . -- "$candidate" 2>/dev/null || continue
  files+=("$candidate")
done < <(find "${scan_dirs[@]}" -type f -print | LC_ALL=C sort)

if [[ "${#files[@]}" -eq 0 ]]; then
  printf 'FAIL no readable text file was found under the scanned trees of %s\n' "$root" >&2
  exit 1
fi

report="$(
  awk -v protected="$protected_docs" -v prefix="$root/" '
    BEGIN {
      n = split(protected, names, " ")
      for (i = 1; i <= n; i++) prot[names[i]] = 1
      token = "[A-Za-z0-9._/-]+\\.[A-Za-z0-9]+:[0-9]+(-[0-9]+)?"
      candidates = 0
    }
    {
      rest = $0
      while (match(rest, token)) {
        tok = substr(rest, RSTART, RLENGTH)
        rest = substr(rest, RSTART + RLENGTH)
        candidates++
        colon = index(tok, ":")
        doc = substr(tok, 1, colon - 1)
        sub(/^\.\//, "", doc)
        if (doc in prot) {
          shown = FILENAME
          if (index(shown, prefix) == 1) shown = substr(shown, length(prefix) + 1)
          printf "VIOLATION\t%s\t%d\t%s\n", shown, FNR, tok
        }
      }
    }
    END { printf "CANDIDATES\t%d\n", candidates }
  ' "${files[@]}"
)"

candidates="$(printf '%s\n' "$report" | awk -F'\t' '$1 == "CANDIDATES" { print $2 }')"
violations="$(printf '%s\n' "$report" | awk -F'\t' '$1 == "VIOLATION"')"
violation_count="$(printf '%s' "$violations" | grep -c . || true)"

if [[ "${candidates:-0}" -eq 0 ]]; then
  printf 'FAIL extracted no citation tokens at all; the extraction pattern no longer matches\n' >&2
  exit 1
fi

if [[ "$violation_count" -gt 0 ]]; then
  printf 'FAIL %d line-numbered citation(s) into a mutable authored document\n' "$violation_count" >&2
  printf '%s\n' "$violations" | while IFS=$'\t' read -r _ file line token; do
    printf 'FAIL %s line %s cites `%s`; cite a section heading, obligation ID, proof-graph node, or quoted phrase instead\n' \
      "$file" "$line" "$token" >&2
  done
  exit 1
fi

printf 'PASS no line-numbered citation into the 6 protected authored documents\n'
printf 'PASS %s citation tokens examined in %s files across %s scanned tree(s)\n' \
  "$candidates" "${#files[@]}" "${#scan_dirs[@]}"
if [[ "$root" == "$repo_root" ]]; then
  printf 'NOTE lexical scan only; host-source, vendor/, and .lean line citations are accepted unchecked\n'
else
  printf 'INFO scanned root is not this repository: %s\n' "$root"
  printf 'INFO the result is about the supplied tree only and closes nothing here\n'
fi
