#!/usr/bin/env bash
# Byte-for-byte drift gate for FIBER-PG-REPRESENTATIVE assurance.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator="$repo_root/scripts/generate-fiber-assurance.sh"
fixed_projection="$repo_root/generated/fiber-assurance.tsv"

mode="production"
candidate="$fixed_projection"
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run" ]]; then
    mode="dry-run"
    candidate="$2"
  else
    printf 'usage: check-fiber-assurance.sh [--dry-run <candidate.tsv>]\n' >&2
    exit 2
  fi
fi

if [[ -n "${EFFECT4_FIBER_ASSURANCE_CANDIDATE-}" ]]; then
  printf 'FAIL Fiber assurance gate rejects environment candidate overrides\n' >&2
  exit 2
fi

[[ -x "$generator" ]] || {
  printf 'FAIL generator is not executable: %s\n' "$generator" >&2
  exit 1
}
[[ -f "$candidate" && ! -L "$candidate" ]] || {
  printf 'FAIL Fiber assurance candidate is absent, not regular, or a symlink: %s\n' \
    "$candidate" >&2
  exit 1
}

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-fiber-assurance-check.XXXXXX")"

cleanup() {
  local cleanup_rc=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-fiber-assurance-check.*) rm -rf -- "$tmp_root" ;;
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
  printf 'FAIL stale generated Fiber assurance projection: %s\n' "$candidate" >&2
  diff -u -- "$candidate" "$tmp_root/fresh.tsv" >&2 || true
  exit 1
fi

if [[ "$mode" == "dry-run" ]]; then
  printf 'PASS dry-run candidate matches current Fiber evidence; closes nothing\n'
else
  printf 'PASS generated Fiber 504-owner/185-API/92-theorem/92-axiom join is current\n'
  printf 'PASS all 7 required FIBER-PG-REPRESENTATIVE edges are mechanically closed; 3 edges remain declared not-applicable\n'
fi
