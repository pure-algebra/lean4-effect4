#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
checker="$repo_root/scripts/check-vendor-foldlab.sh"

"$checker"
echo "PASS baseline vendor"

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-test-foldlab.XXXXXX")"
cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

make_fixture() {
  local fixture_root="$1"
  mkdir -p "$fixture_root/vendor"
  cp -R "$repo_root/vendor/foldlab" "$fixture_root/vendor/foldlab"
}

expect_rejection() {
  local fixture_root="$1"
  local expected_pattern="$2"
  local label="$3"
  local log_file="$fixture_root/check.log"
  if "$checker" "$fixture_root" > "$log_file" 2>&1; then
    echo "self-test unexpectedly accepted $label" >&2
    exit 1
  fi
  if ! grep -Eq "$expected_pattern" "$log_file"; then
    echo "self-test rejected $label for an unexpected reason" >&2
    sed -n '1,120p' "$log_file" >&2
    exit 1
  fi
  echo "PASS planted $label rejected"
}

omission_root="$tmp_root/omission"
make_fixture "$omission_root"
omitted_path="$(sed -n '2p' "$omission_root/vendor/foldlab/PINNED-MANIFEST.tsv" | cut -f1)"
rm -- "$omission_root/vendor/foldlab/pinned/tree/$omitted_path"
expect_rejection "$omission_root" 'file-set mismatch' 'omission'

extra_root="$tmp_root/extra"
make_fixture "$extra_root"
printf 'planted extra file\n' > "$extra_root/vendor/foldlab/pinned/tree/__planted_extra__"
expect_rejection "$extra_root" 'file-set mismatch' 'extra file'

mutation_root="$tmp_root/mutation"
make_fixture "$mutation_root"
mutated_path="$(sed -n '2p' "$mutation_root/vendor/foldlab/LATE-MANIFEST.tsv" | cut -f1)"
printf '\nplanted mutation\n' >> "$mutation_root/vendor/foldlab/late/tree/$mutated_path"
expect_rejection "$mutation_root" 'byte-size mismatch|SHA-256 mismatch|Git-blob mismatch' 'mutation'

"$checker" >/dev/null
echo "PASS source vendor unchanged after disposable attacks"
