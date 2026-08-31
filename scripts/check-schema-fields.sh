#!/usr/bin/env bash
# Drift gate for persisted Schema FIELD spellings (`SC-REP-FIELD-PIN`).
#
# `scripts/check-schema-census.sh` pins the 22 `_tag` spellings. Nothing pinned
# the field names those tagged nodes carry, which is the drift the payload
# carrier is exposed to: a renamed or added persisted field changes the wire
# without changing any tag.
#
# This gate extracts every persisted structural field route in the pinned
# `SchemaRepresentation.ts` and compares it to the table frozen below.  The
# routes include named `Schema.Struct` declarations, the shared
# `KeywordFields` fragment, and the two helper-created structs used for keyword
# nodes and scalar value envelopes.
#
# WHAT A PASS MEANS: at the pinned rc.112 bytes, the codec structs carry
# exactly the recorded field spellings, in the recorded order.
#
# WHAT A PASS DOES NOT MEAN: nothing about semantics, payload types,
# optionality, required-versus-optional divergence between the TypeScript
# interface and the codec, or agreement with any Lean declaration. There is no
# Lean-side field carrier yet, so this gate has ONE route, not the two-route
# cross-check the census gate uses. It is an extraction, not a proof about the
# runtime.
set -euo pipefail

pinned_digest="a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    printf 'FAIL neither sha256sum nor shasum is available\n' >&2
    exit 1
  fi
}

dry_run=0
expect_file=""
source_file=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dry-run) dry_run=1 ;;
    --expect)
      shift
      [[ $# -gt 0 ]] || { printf 'FAIL --expect needs a file argument\n' >&2; exit 1; }
      expect_file="$1"
      ;;
    -h|--help)
      cat <<'USAGE'
usage: check-schema-fields.sh [--dry-run] <path/to/SchemaRepresentation.ts>

Without --dry-run the file must be the pinned rc.112 bytes.
With --dry-run any Effect source is accepted, and the result closes nothing.

--expect <file> replaces the frozen table with one read from <file>. It exists
only so the reaction test in scripts/test-schema-fields-gate.sh can exercise
this detector hermetically, it requires --dry-run, and it closes nothing.
USAGE
      exit 0
      ;;
    -*) printf 'FAIL unknown option: %s\n' "$1" >&2; exit 1 ;;
    *)
      [[ -z "$source_file" ]] || { printf 'FAIL more than one source supplied\n' >&2; exit 1; }
      source_file="$1"
      ;;
  esac
  shift
done

if [[ -n "$expect_file" && "$dry_run" -ne 1 ]]; then
  printf 'FAIL --expect requires --dry-run; the frozen table is not overridable on-pin\n' >&2
  exit 1
fi

if [[ -z "$source_file" ]]; then
  printf 'FAIL SC-REP-FIELD-PIN cannot be confirmed without a source file\n' >&2
  exit 1
fi
[[ -f "$source_file" ]] || { printf 'FAIL source file is absent: %s\n' "$source_file" >&2; exit 1; }

actual_digest="$(sha256_file "$source_file")"
if [[ "$actual_digest" == "$pinned_digest" ]]; then
  on_pin=1
  printf 'PASS pinned rc.112 SchemaRepresentation.ts (%s)\n' "$actual_digest"
else
  on_pin=0
  printf 'INFO off-pin source: %s\n' "$actual_digest"
  printf 'INFO expected rc.112: %s\n' "$pinned_digest"
  if [[ "$dry_run" -ne 1 ]]; then
    printf 'FAIL refusing to compare off-pin bytes without --dry-run\n' >&2
    exit 1
  fi
fi

extract_fields() {
  awk '
    function start(n, i, c) { name=n; ind=i; closer=c; depth=1; printf "%s:", name }
    function finish() { if (depth) { printf "\n"; depth=0 } }
    function emit_field(rest, q, tail, close_at, token) {
      if (rest ~ /^[A-Za-z_$][A-Za-z0-9_$]*:/) {
        match(rest, /^[A-Za-z_$][A-Za-z0-9_$]*:/)
        printf " %s", substr(rest, RSTART, RLENGTH-1)
        return 1
      }
      q=substr(rest, 1, 1)
      if (q == "\"" || q == sprintf("%c", 39)) {
        tail=substr(rest, 2)
        close_at=index(tail, q)
        if (close_at > 0 && substr(rest, close_at+2, 1) == ":") {
          token=substr(rest, 2, close_at-1)
          if (index(token, "\\") == 0) {
            printf " %s", token
            return 1
          }
        }
      }
      return 0
    }
    function emit_inline_struct(line, body, count, parts, i, part) {
      body=line
      sub(/^.*Schema\.Struct\(\{[ ]*/, "", body)
      sub(/[ ]*\}\),[ ]*\{.*$/, "", body)
      count=split(body, parts, ",")
      for (i=1; i<=count; i++) {
        part=parts[i]
        sub(/^[[:space:]]+/, "", part)
        sub(/[[:space:]]+$/, "", part)
        if (part ~ /^[A-Za-z_$][A-Za-z0-9_$]*$/) {
          printf " %s", part
        } else if (!emit_field(part)) {
          printf " <unsupported-inline-field>"
        }
      }
    }
    /^function makeKeywordSchema/ { keyword_helper=1; next }
    keyword_helper && /^  return Schema\.Struct\(\{$/ {
      finish(); start("makeKeywordSchema", 4, "  })"); keyword_helper=0; next
    }
    /^function makeValueSchema/ { value_helper=1; next }
    value_helper && /Schema\.encodeTo\(Schema\.Struct\(\{/ {
      finish(); printf "makeValueSchema:"; emit_inline_struct($0); printf "\n"
      value_helper=0; next
    }
    /^const [A-Za-z0-9_]+ = Schema\.Struct\(\{$/ { finish(); start($2, 2, "})"); next }
    /^const [A-Za-z0-9_]+ = \{$/                 { finish(); start($2, 2, "}");  next }
    /^const [A-Za-z0-9_]+: Schema\.Codec<.*= Schema\.toCodecJson\($/ {
      pend=$2; sub(/:$/, "", pend); next
    }
    pend != "" && /^  Schema\.Struct\(\{$/ {
      finish()
      start(pend, 4, "  })"); pend=""; next
    }
    depth>0 {
      if ($0 == closer) { depth=0; printf "\n"; next }
      pad=substr($0, 1, ind)
      rest=substr($0, ind+1)
      gsub(/ /, "", pad)
      if (pad != "") next
      if (rest ~ /^\.\.\.[A-Za-z0-9_.]+/) {
        match(rest, /^\.\.\.[A-Za-z0-9_.]+/); printf " %s", substr(rest, RSTART, RLENGTH); next
      }
      if (emit_field(rest)) next
    }
    END { if (depth) printf "\n" }
  ' "$1" | LC_ALL=C sort
}

expected_table() {
  cat <<'TABLE' | LC_ALL=C sort
ArraysSchema: _tag ...KeywordFields elements rest
CheckRepresentationAnnotationSchema: ...RepresentationAnnotationSchema.fields schemas
DeclarationSchema: _tag representation annotations typeParameters checks
DocumentFromJson: representation references
ElementSchema: isOptional type annotations
EnumSchema: _tag ...KeywordFields enums
FilterGroupSchema: _tag representation annotations checks
FilterSchema: _tag representation annotations aborted
IndexSignatureSchema: parameter type
KeywordFields: annotations checks
LiteralSchema: _tag ...KeywordFields literal
MultiDocumentFromJson: representations references
ObjectsSchema: _tag ...KeywordFields propertySignatures indexSignatures
PropertySignatureSchema: name type isOptional isMutable annotations
ReferenceSchema: _tag $ref
RepresentationAnnotationSchema: id payload
SuspendSchema: _tag annotations checks thunk
TemplateLiteralSchema: _tag ...KeywordFields parts
UnionSchema: _tag ...KeywordFields types mode
UniqueSymbolSchema: _tag ...KeywordFields symbol
makeKeywordSchema: _tag ...KeywordFields
makeValueSchema: type value
TABLE
}

actual="$(extract_fields "$source_file")"
if [[ -n "$expect_file" ]]; then
  [[ -f "$expect_file" ]] || { printf 'FAIL --expect file is absent: %s\n' "$expect_file" >&2; exit 1; }
  expected="$(LC_ALL=C sort "$expect_file")"
else
  expected="$(expected_table)"
fi

actual_count="$(printf '%s\n' "$actual" | grep -c ':' || true)"
if [[ "$actual_count" -eq 0 ]]; then
  printf 'FAIL extracted no codec structs; the extraction pattern no longer matches\n' >&2
  exit 1
fi

if [[ "$actual" != "$expected" ]]; then
  printf 'FAIL persisted field spelling drift\n' >&2
  diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual") >&2 || true
  exit 1
fi

printf 'PASS %s structural field routes carry the recorded persisted field spellings\n' "$actual_count"
if [[ "$on_pin" -eq 1 ]]; then
  printf 'PASS SC-REP-FIELD-PIN has exact extracted field-spelling agreement at the pinned rc.112 bytes\n'
  printf 'NOTE single-route lexical extraction; no Lean-side field carrier exists yet to cross-check against\n'
else
  printf 'INFO dry run only: SC-REP-FIELD-PIN remains OPEN\n'
fi
