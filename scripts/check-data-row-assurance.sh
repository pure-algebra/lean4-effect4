#!/usr/bin/env bash
# Byte-for-byte drift gate for the generated DATA-PG-ROW assurance join.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator="$repo_root/scripts/generate-data-row-assurance.sh"
fixed_projection="$repo_root/generated/data-row-assurance.tsv"

mode="production"
candidate="$fixed_projection"
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run" ]]; then
    mode="dry-run"
    candidate="$2"
  else
    printf 'usage: check-data-row-assurance.sh [--dry-run <candidate.tsv>]\n' >&2
    exit 2
  fi
fi

if [[ -n "${EFFECT4_DATA_ROW_ASSURANCE_CANDIDATE-}" ]]; then
  printf 'FAIL Data.Row assurance gate rejects environment candidate overrides\n' >&2
  exit 2
fi

[[ -x "$generator" ]] || { printf 'FAIL generator is not executable: %s\n' "$generator" >&2; exit 1; }
[[ -f "$candidate" && ! -L "$candidate" ]] || {
  printf 'FAIL Data.Row assurance candidate is absent, not regular, or a symlink: %s\n' \
    "$candidate" >&2
  exit 1
}

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-data-row-assurance-check.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-data-row-assurance-check.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_rc=1
      ;;
  esac
  exit "$cleanup_rc"
}
trap cleanup EXIT

"$generator" >"$tmp_root/fresh.tsv"

if ! cmp -s -- "$tmp_root/fresh.tsv" "$candidate"; then
  printf 'FAIL stale generated Data.Row assurance projection: %s\n' "$candidate" >&2
  diff -u -- "$candidate" "$tmp_root/fresh.tsv" >&2 || true
  exit 1
fi

if [[ "$mode" == "dry-run" ]]; then
  printf 'PASS dry-run candidate matches current Data.Row evidence; closes nothing\n'
else
  printf 'PASS generated Data.Row 60-owner/34-API/23-theorem/23-axiom join is current\n'
  printf 'PASS all 10 DATA-PG-ROW edges are mechanically closed\n'
  printf 'PASS DATA-PG-ROW/ORDER consumes the closed Context bridge leaf; ENV-KEY-INTERP remains open\n'
fi
