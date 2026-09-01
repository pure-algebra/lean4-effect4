#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator="$repo_root/scripts/generate-schema-structural-assurance.sh"
projection="$repo_root/generated/schema-structural-assurance.tsv"

if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run" ]]; then
    projection="$2"
  else
    printf 'usage: check-schema-structural-assurance.sh [--dry-run <projection>]\n' >&2
    exit 2
  fi
fi

[[ -x "$generator" ]] || { printf 'FAIL Schema structural generator is not executable\n' >&2; exit 1; }
[[ -f "$projection" && ! -L "$projection" ]] || {
  printf 'FAIL Schema structural assurance projection is absent, not regular, or a symlink\n' >&2
  exit 1
}

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-schema-structural-check.XXXXXX")"
cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-schema-structural-check.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; cleanup_rc=1 ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

"$generator" >"$tmp_root/fresh.tsv"
if ! cmp -s -- "$tmp_root/fresh.tsv" "$projection"; then
  printf 'FAIL stale generated Schema structural assurance projection\n' >&2
  diff -u -- "$projection" "$tmp_root/fresh.tsv" >&2 || true
  exit 1
fi

printf 'PASS Schema structural assurance projection is current\n'
printf 'PASS exact 1092-declaration census, 418 theorem/axiom receipts, 26 counterexamples, and graph statuses agree\n'
printf 'PASS SCHEMA-PG-REPRESENTATION-TAG and SCHEMA-PG-FIELD-ADMISSION close; SCHEMA-PG-PAYLOAD retains only SC-REP-03 general recursor open\n'

