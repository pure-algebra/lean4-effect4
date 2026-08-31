#!/usr/bin/env bash
# Byte-for-byte drift gate for the generated Context Key assurance projection.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
generator="$repo_root/scripts/generate-environment-context-key-evidence.sh"
fixed_projection="$repo_root/generated/environment-context-key-assurance.tsv"

mode="production"
candidate="$fixed_projection"
if [[ $# -gt 0 ]]; then
  if [[ $# -eq 2 && "$1" == "--dry-run" ]]; then
    mode="dry-run"
    candidate="$2"
  else
    printf 'usage: check-environment-context-key-evidence.sh [--dry-run <candidate.tsv>]\n' >&2
    exit 2
  fi
fi

if [[ -n "${EFFECT4_CONTEXT_KEY_EVIDENCE_CANDIDATE-}" ]]; then
  printf 'FAIL context-key evidence gate rejects environment candidate overrides\n' >&2
  exit 2
fi

[[ -x "$generator" ]] || { printf 'FAIL generator is not executable: %s\n' "$generator" >&2; exit 1; }
[[ -f "$candidate" && ! -L "$candidate" ]] || {
  printf 'FAIL context-key evidence candidate is absent, not regular, or a symlink: %s\n' \
    "$candidate" >&2
  exit 1
}

tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-context-key-check.XXXXXX")"

cleanup() {
  local cleanup_status=$?
  set +e
  case "$tmp_root" in
    "$tmp_parent"/effect4-context-key-check.*) rm -rf -- "$tmp_root" ;;
    *)
      printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2
      cleanup_status=1
      ;;
  esac
  exit "$cleanup_status"
}
trap cleanup EXIT

"$generator" >"$tmp_root/fresh.tsv"

if ! cmp -s -- "$tmp_root/fresh.tsv" "$candidate"; then
  printf 'FAIL stale generated context-key assurance projection: %s\n' "$candidate" >&2
  diff -u -- "$candidate" "$tmp_root/fresh.tsv" >&2 || true
  exit 1
fi

if [[ "$mode" == "dry-run" ]]; then
  printf 'PASS dry-run candidate matches the current Context Key evidence; closes nothing\n'
else
  printf 'PASS generated Context Key owned-declaration/API/owner/theorem/axiom join is current\n'
  printf 'PASS ENV-LEAF-KEY-IDENTITY and local ENV-LEAF-KEY-ORDER-BRIDGE receipts are closed\n'
  printf 'PASS ENV-PG-CONTEXT/ENV-KEY-INTERP and DATA-PG-ROW/ORDER attachments remain open\n'
fi
