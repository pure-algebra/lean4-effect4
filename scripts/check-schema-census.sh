#!/usr/bin/env bash
# Drift gate for the Schema tag census (`SC-REP-CENSUS-PIN`).
#
# Lexically compares the persisted tag spellings in an Effect
# `SchemaRepresentation.ts` against the spelling set exposed by the `tagName`
# definitions in `src/Effect4/Schema/Representation.lean`.
#
# Two independent extractions are taken from the source and must agree:
#
#   union route  the closed `export type Representation = | A | B | ...` and
#                `export type Check = A | B` declarations. These are single
#                site in the pinned source, so a 23rd member cannot be added
#                to the type surface without appearing here. Blank lines and
#                `//` / `/* */` comments inside the union are skipped rather
#                than treated as terminators: treating a comment as the end of
#                the union silently truncated the extraction and let a 23rd
#                member hide behind one doc comment.
#   codec route  the `Schema.tag(...)` and `makeKeywordSchema(...)` call sites
#                that build the persisted codec, in either quote style. Check
#                tags are scoped to the `FilterSchema`..`CheckUnion` block;
#                the remaining literal call sites are representation tags.
#
# The union route is authoritative for the source spelling set. The codec
# route is a cross-check: if the two disagree, the file's type surface and its
# codec surface have diverged and the gate refuses to report agreement. This
# is a textual source-shape gate. It does not parse TypeScript, inspect payload
# fields, run the codec, or establish denotational or host faithfulness.
#
# The pinned authority is effect@4.0.0-rc.112, whose `SchemaRepresentation.ts`
# has SHA-256 a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc.
# Only that file can produce pin-matched evidence. Any other bytes are a dry
# run and are reported as closing nothing, however well they agree. Cutover
# status is assigned by the generated proof-closure join, never by this script.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
pinned_digest="a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc"
lean_source="$repo_root/src/Effect4/Schema/Representation.lean"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    printf 'FAIL neither sha256sum nor shasum is available\n' >&2
    return 1
  fi
}

dry_run=0
source_file=""
lean_override=""
expect_lean_override=0
for argument in "$@"; do
  if [[ "$expect_lean_override" -eq 1 ]]; then
    lean_override="$argument"; expect_lean_override=0; continue
  fi
  case "$argument" in
    --dry-run) dry_run=1 ;;
    --lean-source) expect_lean_override=1 ;;
    -*) printf 'FAIL unknown option: %s\n' "$argument" >&2; exit 2 ;;
    *)
      if [[ -n "$source_file" ]]; then
        printf 'FAIL more than one source supplied: %s and %s\n' \
          "$source_file" "$argument" >&2
        exit 2
      fi
      source_file="$argument"
      ;;
  esac
done

usage() {
  cat >&2 <<'USAGE'
usage: check-schema-census.sh [--dry-run] [--lean-source <file>] <path/to/SchemaRepresentation.ts>

Without --dry-run the file must be the pinned rc.112 bytes.
With --dry-run any Effect source is accepted, and the result closes nothing.

--lean-source <file> replaces src/Effect4/Schema/Representation.lean as the Lean
side of the comparison. It exists only so the reaction test can attack the
Lean scrape, it requires --dry-run, and it closes nothing.
USAGE
}

if [[ "$expect_lean_override" -eq 1 ]]; then
  printf 'FAIL --lean-source needs a file argument\n' >&2
  exit 2
fi

if [[ -n "$lean_override" ]]; then
  if [[ "$dry_run" -ne 1 ]]; then
    printf 'FAIL --lean-source requires --dry-run; the Lean side is not overridable on-pin\n' >&2
    exit 2
  fi
  [[ -f "$lean_override" ]] || {
    printf 'FAIL --lean-source file is absent: %s\n' "$lean_override" >&2; exit 2; }
  lean_source="$lean_override"
fi

if [[ -z "$source_file" ]]; then
  printf 'FAIL no SchemaRepresentation.ts supplied\n' >&2
  printf 'FAIL SC-REP-CENSUS-PIN cannot be confirmed without the pinned rc.112 bytes\n' >&2
  usage
  exit 1
fi

[[ -f "$source_file" ]] || { printf 'FAIL not a file: %s\n' "$source_file" >&2; exit 1; }

actual_digest="$(sha256_file "$source_file")"
if [[ "$actual_digest" == "$pinned_digest" ]]; then
  on_pin=1
  printf 'PASS pinned rc.112 SchemaRepresentation.ts (%s)\n' "$actual_digest"
else
  on_pin=0
  printf 'INFO off-pin source: %s\n' "$actual_digest"
  printf 'INFO expected rc.112: %s\n' "$pinned_digest"
  if [[ "$dry_run" -eq 0 ]]; then
    printf 'FAIL refusing to compare off-pin bytes without --dry-run\n' >&2
    exit 1
  fi
fi

# --- source, union route (authoritative, exhaustive) --------------------
extract_union() {
  local declaration="$1"
  awk -v decl="$declaration" '
    BEGIN { collecting = 0; inblock = 0 }
    {
      if (collecting == 0) {
        if ($0 ~ "^export type " decl " =") {
          collecting = 1
          line = $0
          sub("^export type " decl " =", "", line)
        } else {
          next
        }
      } else {
        t = $0
        sub(/^[ \t]+/, "", t)
        # A comment or a blank line inside the union is not a terminator.
        # Treating it as one silently truncated the extraction and let a
        # 23rd member hide behind a doc comment.
        if (inblock) { if (t ~ /\*\//) inblock = 0; next }
        if (t == "") next
        if (t ~ /^\/\//) next
        if (t ~ /^\/\*/) { if (t !~ /\*\//) inblock = 1; next }
        if (t ~ /^\*/) next
        # Only a real declaration line ends the union.
        if (t !~ /^\|/) { exit }
        line = $0
      }
      sub(/\/\/.*$/, "", line)
      n = split(line, parts, /\|/)
      for (i = 1; i <= n; i++) {
        gsub(/[ \t\r]/, "", parts[i])
        if (parts[i] != "") print parts[i]
      }
    }
  ' "$source_file"
}

representation_union="$(extract_union "Representation" | LC_ALL=C sort -u)"
check_union="$(extract_union "Check" | LC_ALL=C sort -u)"

[[ -n "$representation_union" ]] || {
  printf 'FAIL extracted no Representation union members from %s; the `export type Representation =` shape no longer matches\n' \
    "$source_file" >&2; exit 1; }
[[ -n "$check_union" ]] || {
  printf 'FAIL extracted no Check union members from %s; the `export type Check =` shape no longer matches\n' \
    "$source_file" >&2; exit 1; }

# The two nominal families must remain disjoint. Comparing only their merged
# set would miss a tag copied into or moved between the wrong family.
source_union_overlap="$(comm -12 \
  <(printf '%s\n' "$representation_union") \
  <(printf '%s\n' "$check_union"))"
[[ -z "$source_union_overlap" ]] || {
  printf 'FAIL source union families overlap; Representation and Check are nominally distinct\n' >&2
  printf '%s\n' "$source_union_overlap" >&2
  exit 1
}

# --- source, codec route (cross-check by family) ------------------------
codec_tags_in() {
  # Accepts both quote styles. A single-quoted Schema.tag('X') previously
  # evaded the double-quote-only pattern and went uncounted.
  awk '
    {
      s = $0
      while (match(s, /(Schema\.tag|makeKeywordSchema)\([\047"][^\047"]+[\047"]\)/)) {
        st = RSTART; ln = RLENGTH
        tok = substr(s, st, ln)
        if (match(tok, /[\047"][^\047"]+[\047"]/)) print substr(tok, RSTART + 1, RLENGTH - 2)
        s = substr(s, st + ln)
      }
    }
  '
}

all_codec_tags="$( codec_tags_in <"$source_file" | LC_ALL=C sort -u )"

check_codec="$(
  sed -n '/^const FilterSchema =/,/^const CheckUnion =/p' "$source_file" \
    | codec_tags_in \
    | LC_ALL=C sort -u \
    || true
)"

representation_codec="$(comm -23 \
  <(printf '%s\n' "$all_codec_tags") \
  <(printf '%s\n' "$check_codec"))"

# --- Lean side ----------------------------------------------------------
# Scoped to the bodies of the `tagName` functions only, so unrelated
# string-returning declarations added later cannot contaminate the census.
extract_lean_tags() {
  local namespace_name="$1"
  awk -v namespace_name="$namespace_name" '
    # Strip a Lean line comment, but only when it starts before any string
    # literal, so a tag spelling containing "--" survives while a comment
    # carrying the pinned spelling cannot be mistaken for the value.
    function decomment(x,   qi, ci) {
      qi = index(x, "\"")
      ci = index(x, "--")
      if (ci > 0 && (qi == 0 || ci < qi)) sub(/--.*$/, "", x)
      return x
    }
    $0 == "namespace " namespace_name { in_namespace = 1; next }
    in_namespace && $0 == "end " namespace_name {
      in_namespace = 0; inside = 0; pending = 0; next
    }
    in_namespace && /^def tagName/ { inside = 1; next }
    in_namespace && inside {
      t = decomment($0)
      if ($0 ~ /^[ \t]*\|/) {
        if (match(t, /"[^"]*"/)) { print substr(t, RSTART + 1, RLENGTH - 2); pending = 0 }
        else { pending = 1 }
        next
      }
      if ($0 ~ /^[ \t]*$/) next
      if (pending) {
        if (match(t, /"[^"]*"/)) { print substr(t, RSTART + 1, RLENGTH - 2); pending = 0; next }
      }
      inside = 0
    }
  ' "$lean_source" | LC_ALL=C sort -u
}

lean_representation_tags="$(extract_lean_tags "RepresentationTag")"
lean_check_tags="$(extract_lean_tags "CheckTag")"

count_of() { printf '%s\n' "$1" | grep -c . || true; }

[[ -n "$all_codec_tags" ]] || {
  printf 'FAIL extracted no codec tags from %s; the call-site shape no longer matches\n' \
    "$source_file" >&2; exit 1; }
[[ -n "$representation_codec" ]] || {
  printf 'FAIL extracted no Representation codec tags from %s\n' "$source_file" >&2; exit 1; }
[[ -n "$check_codec" ]] || {
  printf 'FAIL extracted no Check codec tags from %s; the `FilterSchema`..`CheckUnion` shape no longer matches\n' \
    "$source_file" >&2; exit 1; }
[[ -n "$lean_representation_tags" ]] || {
  printf 'FAIL extracted no RepresentationTag spellings from %s\n' \
    "$lean_source" >&2; exit 1; }
[[ -n "$lean_check_tags" ]] || {
  printf 'FAIL extracted no CheckTag spellings from %s\n' \
    "$lean_source" >&2; exit 1; }

lean_overlap="$(comm -12 \
  <(printf '%s\n' "$lean_representation_tags") \
  <(printf '%s\n' "$lean_check_tags"))"
[[ -z "$lean_overlap" ]] || {
  printf 'FAIL Lean tag families overlap; RepresentationTag and CheckTag are nominally distinct\n' >&2
  printf '%s\n' "$lean_overlap" >&2
  exit 1
}

compare_source_routes() {
  local family="$1" union_set="$2" codec_set="$3"
  if diff -u <(printf '%s\n' "$union_set") <(printf '%s\n' "$codec_set") >/dev/null; then
    return
  fi
  printf 'FAIL the type union and the codec disagree for %s\n' "$family" >&2
  printf '  -union  +codec\n' >&2
  diff -u <(printf '%s\n' "$union_set") <(printf '%s\n' "$codec_set") \
    | tail -n +4 >&2 || true
  exit 1
}

compare_lean_source() {
  local family="$1" lean_set="$2" source_set="$3"
  if diff -u <(printf '%s\n' "$lean_set") <(printf '%s\n' "$source_set") >/dev/null; then
    return
  fi
  printf 'FAIL tag census drift between Lean and source for %s\n' "$family" >&2
  printf '  -lean  +source\n' >&2
  diff -u <(printf '%s\n' "$lean_set") <(printf '%s\n' "$source_set") \
    | tail -n +4 >&2 || true
  exit 1
}

compare_source_routes "Representation" "$representation_union" "$representation_codec"
compare_source_routes "Check" "$check_union" "$check_codec"
compare_lean_source "RepresentationTag" "$lean_representation_tags" "$representation_union"
compare_lean_source "CheckTag" "$lean_check_tags" "$check_union"

representation_count="$(count_of "$representation_union")"
check_count="$(count_of "$check_union")"
total="$(( representation_count + check_count ))"

printf 'PASS both lexical source routes agree by family: %d spellings (%d representation, %d check)\n' \
  "$total" "$representation_count" "$check_count"

[[ "$representation_count" -eq 22 ]] || {
  printf 'FAIL expected 22 representation tags, found %d\n' "$representation_count" >&2; exit 1; }
[[ "$check_count" -eq 2 ]] || {
  printf 'FAIL expected 2 check tags, found %d\n' "$check_count" >&2; exit 1; }

if [[ "$on_pin" -eq 1 ]]; then
  printf 'PASS SC-REP-CENSUS-PIN has exact extracted spelling-set agreement at the pinned rc.112 bytes\n'
  printf 'INFO this is lexical source evidence, not payload or semantic faithfulness\n'
else
  printf 'INFO dry run only: SC-REP-CENSUS-PIN remains OPEN\n'
  printf 'INFO agreement with off-pin bytes is a signal, not evidence\n'
fi
