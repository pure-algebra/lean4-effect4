#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
checker="$repo_root/scripts/check-corpus-sources.sh"

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/effect4-test-corpus-sources.XXXXXX")"
cleanup() {
  rm -rf -- "$tmp_root"
}
trap cleanup EXIT

make_repo() {
  local corpus_root="$1"
  local name="$2"
  local repo="$corpus_root/$name"
  mkdir -p "$repo"
  git -C "$repo" init -q
  git -C "$repo" config user.name 'Effect4 corpus gate'
  git -C "$repo" config user.email 'effect4-corpus@example.invalid'
  printf '%s\n' "$name" > "$repo/source.txt"
  git -C "$repo" add source.txt
  git -C "$repo" commit -q -m "add $name"
  git -C "$repo" remote add origin "https://example.invalid/$name"
}

write_manifest() {
  local corpus_root="$1"
  local manifest="$2"
  printf 'checkout\thead_commit\troot_tree\tsource_url\trole\tdisposition\n' > "$manifest"
  local repo name head tree
  for repo in "$corpus_root"/*; do
    name="${repo##*/}"
    head="$(git -C "$repo" rev-parse HEAD)"
    tree="$(git -C "$repo" rev-parse 'HEAD^{tree}')"
    printf '%s\t%s\t%s\thttps://example.invalid/%s\texternal-source-checkout\tinventory-only-unclassified\n' \
      "$name" "$head" "$tree" "$name" >> "$manifest"
  done
}

baseline="$tmp_root/baseline"
mkdir -p "$baseline/corpus"
number=1
while [[ "$number" -le 34 ]]; do
  printf -v checkout_number '%02d' "$number"
  make_repo "$baseline/corpus" "source-$checkout_number"
  number=$((number + 1))
done
write_manifest "$baseline/corpus" "$baseline/SOURCES.tsv"

"$checker" --corpus-root "$baseline/corpus" --manifest "$baseline/SOURCES.tsv" >/dev/null
echo "PASS synthetic baseline accepted"

make_case() {
  local label="$1"
  local case_root="$tmp_root/$label"
  mkdir -p "$case_root"
  cp -R "$baseline/corpus" "$case_root/corpus"
  cp "$baseline/SOURCES.tsv" "$case_root/SOURCES.tsv"
  printf '%s\n' "$case_root"
}

expect_rejection() {
  local case_root="$1"
  local expected_pattern="$2"
  local label="$3"
  local log_file="$case_root/check.log"
  if "$checker" --corpus-root "$case_root/corpus" --manifest "$case_root/SOURCES.tsv" > "$log_file" 2>&1; then
    echo "corpus gate unexpectedly accepted planted $label" >&2
    exit 1
  fi
  if ! grep -Eq "$expected_pattern" "$log_file"; then
    echo "corpus gate rejected planted $label for an unexpected reason" >&2
    sed -n '1,100p' "$log_file" >&2
    exit 1
  fi
  echo "PASS planted $label rejected"
}

omission_root="$(make_case omission)"
rm -rf -- "$omission_root/corpus/source-01"
expect_rejection "$omission_root" 'checkout set mismatch' 'checkout omission'

extra_row_root="$(make_case extra-row)"
printf 'zz-ghost\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\thttps://example.invalid/zz-ghost\texternal-source-checkout\tinventory-only-unclassified\n' >> "$extra_row_root/SOURCES.tsv"
expect_rejection "$extra_row_root" 'manifest has 35 source rows' 'extra manifest row'

blank_pin_root="$(make_case blank-pin)"
awk -F '\t' 'BEGIN { OFS = FS } NR == 2 { $2 = "" } { print }' "$blank_pin_root/SOURCES.tsv" > "$blank_pin_root/SOURCES.next"
mv "$blank_pin_root/SOURCES.next" "$blank_pin_root/SOURCES.tsv"
expect_rejection "$blank_pin_root" 'blank HEAD pin' 'blank pin'

duplicate_source_root="$(make_case duplicate-source)"
first_url="$(sed -n '2p' "$duplicate_source_root/SOURCES.tsv" | cut -f4)"
awk -F '\t' -v url="$first_url" 'BEGIN { OFS = FS } NR == 3 { $4 = url } { print }' "$duplicate_source_root/SOURCES.tsv" > "$duplicate_source_root/SOURCES.next"
mv "$duplicate_source_root/SOURCES.next" "$duplicate_source_root/SOURCES.tsv"
expect_rejection "$duplicate_source_root" 'duplicate source URL' 'duplicate source'

duplicate_pin_root="$(make_case duplicate-pin)"
first_head="$(sed -n '2p' "$duplicate_pin_root/SOURCES.tsv" | cut -f2)"
first_tree="$(sed -n '2p' "$duplicate_pin_root/SOURCES.tsv" | cut -f3)"
awk -F '\t' -v head="$first_head" -v tree="$first_tree" 'BEGIN { OFS = FS } NR == 3 { $2 = head; $3 = tree } { print }' "$duplicate_pin_root/SOURCES.tsv" > "$duplicate_pin_root/SOURCES.next"
mv "$duplicate_pin_root/SOURCES.next" "$duplicate_pin_root/SOURCES.tsv"
expect_rejection "$duplicate_pin_root" 'duplicate commit/tree pin' 'duplicate pin'

wrong_head_root="$(make_case wrong-head)"
awk -F '\t' 'BEGIN { OFS = FS } NR == 2 { $2 = "1111111111111111111111111111111111111111" } { print }' "$wrong_head_root/SOURCES.tsv" > "$wrong_head_root/SOURCES.next"
mv "$wrong_head_root/SOURCES.next" "$wrong_head_root/SOURCES.tsv"
expect_rejection "$wrong_head_root" 'HEAD pin mismatch' 'wrong HEAD pin'

wrong_tree_root="$(make_case wrong-tree)"
awk -F '\t' 'BEGIN { OFS = FS } NR == 2 { $3 = "2222222222222222222222222222222222222222" } { print }' "$wrong_tree_root/SOURCES.tsv" > "$wrong_tree_root/SOURCES.next"
mv "$wrong_tree_root/SOURCES.next" "$wrong_tree_root/SOURCES.tsv"
expect_rejection "$wrong_tree_root" 'root-tree pin mismatch' 'wrong root-tree pin'

unrecorded_root="$(make_case unrecorded-checkout)"
make_repo "$unrecorded_root/corpus" 'source-35'
expect_rejection "$unrecorded_root" 'checkout set mismatch' 'unrecorded checkout'

dirty_root="$(make_case dirty-tracked)"
printf 'planted dirty change\n' >> "$dirty_root/corpus/source-01/source.txt"
expect_rejection "$dirty_root" 'tracked files are dirty' 'dirty tracked file'

escape_root="$(make_case path-escape)"
awk -F '\t' 'BEGIN { OFS = FS } NR == 2 { $1 = "../escape" } { print }' "$escape_root/SOURCES.tsv" > "$escape_root/SOURCES.next"
mv "$escape_root/SOURCES.next" "$escape_root/SOURCES.tsv"
expect_rejection "$escape_root" 'not sorted|unsafe checkout name' 'path escape'

symlink_root="$(make_case checkout-symlink)"
rm -rf -- "$symlink_root/corpus/source-01"
ln -s "$baseline/corpus/source-01" "$symlink_root/corpus/source-01"
expect_rejection "$symlink_root" 'checkout is a symlink|Git metadata is not a local directory' 'checkout symlink'

"$checker" --corpus-root "$baseline/corpus" --manifest "$baseline/SOURCES.tsv" >/dev/null
echo "PASS synthetic source inventory unchanged after disposable attacks"
