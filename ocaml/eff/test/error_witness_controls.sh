#!/usr/bin/env bash
# DI-62 compile controls: closed error witnesses accept the represented types and
# reject Boolean introductions. Positive compilation proves the interface is loaded.
set -euo pipefail
compiler="${1:?expected ocamlc}"
library_dir="$(cd "${2:?expected compiled interface directory}" && pwd)"
controls="$(cd "$(dirname "${BASH_SOURCE[0]}")/error_witness_controls" && pwd)"
scratch="$(mktemp -d "${TMPDIR:-/tmp}/effect4-error-witness.XXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT

"$compiler" -I "$library_dir" -c "$controls/positive.ml" -o "$scratch/positive.cmo"
for name in unsupported_bool fail_mismatch yield_mismatch cause_mismatch; do
  if "$compiler" -I "$library_dir" -c "$controls/$name.ml" -o "$scratch/$name.cmo" >"$scratch/$name.log" 2>&1; then
    printf 'FAIL: %s unexpectedly compiled\n' "$name" >&2
    exit 1
  fi
  diagnostic="$(cat "$scratch/$name.log")"
  case "$name:$diagnostic" in
    unsupported_bool:*"Unbound constructor Error_bool"*|unsupported_bool:*"There is no constructor Error_bool"*) ;;
    *_mismatch:*"bool"*"string"*|*_mismatch:*"string"*"bool"*) ;;
    *)
      printf 'FAIL: %s failed for an unexpected reason\n%s\n' "$name" "$diagnostic" >&2
      exit 1
      ;;
  esac
  printf 'PASS: %s rejected by the OCaml type checker\n' "$name"
done
printf 'PASS: represented error witnesses compile; four unsupported introductions are rejected\n'
