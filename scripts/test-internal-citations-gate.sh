#!/usr/bin/env bash
# Exercises whether `scripts/check-internal-citations.sh` reacts.
#
# This exercises the DETECTOR, not the repository. Every case runs against a
# synthetic tree built under $TMPDIR from `Test/fixtures/internal-citations/`,
# never against the live tree, so a pass here says nothing about whether this
# repository's real citations are correct — only that the eleven named violations
# and invocation defects cannot return a vacuous success, and that the six
# named legitimate citation classes are not rejected.
#
# The violating citations are assembled from shell variables rather than
# spelled literally, because `scripts/` is itself one of the trees the gate
# scans. A literal violation written here would make the real gate fail on this
# file.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
gate="$repo_root/scripts/check-internal-citations.sh"
fixture="$repo_root/Test/fixtures/internal-citations/tree"
tmp_parent="${TMPDIR:-/tmp}"
tmp_parent="${tmp_parent%/}"
tmp_root="$(mktemp -d "$tmp_parent/effect4-citations-gate.XXXXXX")"
fixture_before="$tmp_root/fixture.before"

cleanup() {
  local status=$?
  set +e
  if [[ -f "$fixture_before" ]]; then
    find "$fixture" -type f -print0 | LC_ALL=C sort -z | xargs -0 cksum \
      >"$tmp_root/fixture.after" 2>/dev/null
    if ! cmp -s -- "$fixture_before" "$tmp_root/fixture.after"; then
      printf 'FAIL fixture changed while the gate tests ran\n' >&2
      status=1
    fi
  fi
  case "$tmp_root" in
    "$tmp_parent"/effect4-citations-gate.*) rm -rf -- "$tmp_root" ;;
    *) printf 'FAIL refusing to remove unexpected path: %s\n' "$tmp_root" >&2; status=1 ;;
  esac
  exit "$status"
}
trap cleanup EXIT

[[ -x "$gate" ]] || { printf 'FAIL gate is not executable: %s\n' "$gate" >&2; exit 1; }
[[ -d "$fixture" ]] || { printf 'FAIL fixture tree is missing: %s\n' "$fixture" >&2; exit 1; }
find "$fixture" -type f -print0 | LC_ALL=C sort -z | xargs -0 cksum >"$fixture_before"

# The five protected documents, held as data so this file carries no literal
# line-numbered citation into any of them.
cutover='docs/SCHEMA-CUTOVER.md'
cutover_bare='SCHEMA-CUTOVER.md'
plan='PLAN.md'
agents='AGENTS.md'
arch='docs/ARCHITECTURE.md'
routing='docs/AGENT-ROUTING.md'

rejected=0
accepted=0

empty_tree() {
  local name="$1"
  local dir="$tmp_root/$name"
  rm -rf -- "$dir"
  mkdir -p "$dir/docs" "$dir/src/Effect4" "$dir/Test" "$dir/Test/contracts" "$dir/scripts" "$dir/harness"
  printf '%s' "$dir"
}

full_tree() {
  local name="$1"
  local dir="$tmp_root/$name"
  rm -rf -- "$dir"
  mkdir -p "$dir"
  cp -R -- "$fixture/." "$dir/"
  printf '%s' "$dir"
}

expect_reject() {
  local name="$1" dir="$2" signal="$3"
  local log="$tmp_root/reject-$rejected.log"
  if "$gate" --root "$dir" >"$log" 2>&1; then
    printf 'FAIL gate accepted a tree it must reject: %s\n' "$name" >&2
    cat "$log" >&2
    exit 1
  fi
  if ! grep -Fq -- "$signal" "$log"; then
    printf 'FAIL %s was rejected, but the expected signal was absent: %s\n' "$name" "$signal" >&2
    cat "$log" >&2
    exit 1
  fi
  rejected=$((rejected + 1))
  printf 'PASS rejected: %s\n' "$name"
}

expect_accept() {
  local name="$1" dir="$2"
  local log="$tmp_root/accept-$accepted.log"
  if ! "$gate" --root "$dir" >"$log" 2>&1; then
    printf 'FAIL gate rejected a legitimate tree: %s\n' "$name" >&2
    cat "$log" >&2
    exit 1
  fi
  if ! grep -Fq 'citation tokens examined' "$log"; then
    printf 'FAIL %s passed without reporting how many tokens it examined\n' "$name" >&2
    cat "$log" >&2
    exit 1
  fi
  accepted=$((accepted + 1))
  printf 'PASS accepted: %s\n' "$name"
}

# ---------------------------------------------------------------- acceptances

# A1. the unmutated fixture tree, and it must state that it closes nothing here
dir="$(full_tree baseline)"
expect_accept "baseline fixture tree" "$dir"
grep -Fq 'closes nothing here' "$tmp_root/accept-0.log" || {
  printf 'FAIL a non-repository root must state that it closes nothing here\n' >&2
  exit 1
}

# A2. pinned host-source line citations
dir="$(empty_tree accept-host)"
cp -- "$fixture/docs/host-citations.md" "$dir/docs/"
expect_accept "pinned host-source line citations" "$dir"

# A3. vendor/foldlab read-only evidence line citations
dir="$(empty_tree accept-vendor)"
cp -- "$fixture/docs/vendor-evidence.md" "$dir/docs/"
expect_accept "vendor/foldlab line citations" "$dir"

# A4. .lean source line citations
dir="$(empty_tree accept-lean)"
cp -- "$fixture/src/Effect4/Sample.lean" "$dir/src/Effect4/"
cp -- "$fixture/Test/SampleContract.lean" "$dir/Test/"
expect_accept ".lean source line citations" "$dir"

# A5. near-miss basenames are different files and must not be flagged
dir="$(empty_tree accept-near-miss)"
{
  printf '# near-miss basenames\n\n'
  printf -- '- `vendor/foldlab/pinned/tree/library/cas/CORE-ABSTRACTIONS-%s:127-131`\n' "$plan"
  printf -- '- `harness/%s:12`\n' "$agents"
  printf -- '- `src/Effect4/Schema/Check.lean:7`\n'
} >"$dir/docs/near-miss.md"
expect_accept "near-miss basenames under other paths" "$dir"

# A6. the required anchored spelling for all five protected documents
dir="$(empty_tree accept-anchored)"
cp -- "$fixture/docs/anchored-citations.md" "$dir/docs/"
cp -- "$fixture/docs/host-citations.md" "$dir/docs/"
expect_accept "section, obligation-ID, node, and quoted-phrase anchors" "$dir"

# ---------------------------------------------------------------- rejections

# R1. a range citation into the Schema cutover ruling, in docs/
dir="$(full_tree reject-cutover-range)"
printf 'The five wire rows are at `%s:588-592`.\n' "$cutover" >"$dir/docs/stale.md"
expect_reject "range citation into the Schema cutover ruling" "$dir" "$cutover:588-592"

# R2. the same document cited by bare basename and a single line, in src/Effect4/
dir="$(full_tree reject-cutover-bare)"
printf '/-- see `%s:524` -/\n' "$cutover_bare" >"$dir/src/Effect4/Stale.lean"
expect_reject "bare-basename single-line citation into the cutover ruling" "$dir" "$cutover_bare:524"

# R3. a citation into the plan, in Test/
dir="$(full_tree reject-plan)"
printf '/-- gate conditions at `%s:299` -/\n' "$plan" >"$dir/Test/StaleContract.lean"
expect_reject "citation into the plan" "$dir" "$plan:299"

# R4. a citation into the agent router, in Test/contracts/
dir="$(full_tree reject-agents)"
printf 'ownership repair rule at `%s:20`\n' "$agents" >"$dir/Test/contracts/stale.contract.md"
expect_reject "citation into the agent router" "$dir" "$agents:20"

# R5. a citation into the architecture ruling, in the host harness
dir="$(full_tree reject-architecture)"
mkdir -p "$dir/harness"
printf '# dependency order at `%s:41-48`\n' "$arch" >"$dir/harness/stale-gate.md"
expect_reject "citation into the architecture ruling" "$dir" "$arch:41-48"

# R6. a `./`-prefixed citation into the architecture ruling
dir="$(full_tree reject-dot-slash)"
printf 'the gates table is at `./%s:553`\n' "$arch" >"$dir/docs/stale-dot-slash.md"
expect_reject "dot-slash-prefixed citation into the architecture ruling" "$dir" "$arch:553"

# R7. the target decides, not the host file type: a protected citation in .lean
dir="$(full_tree reject-lean-host)"
printf '/-- `%s:117-118` forbids a leaf from owning a host edge -/\n' "$cutover" \
  >"$dir/src/Effect4/StaleHost.lean"
expect_reject "protected citation carried by a .lean file" "$dir" "$cutover:117-118"

# R7b. the routing threshold document is mutable and authored too
dir="$(full_tree reject-routing)"
printf 'The leaf conditions at `%s:136` decide the route.\n' "$routing" \
  >"$dir/docs/StaleRouting.md"
expect_reject "citation into the agent routing threshold" "$dir" "$routing:136"

# R8. total extraction failure must not read as a clean tree
dir="$(full_tree reject-no-tokens)"
while IFS= read -r f; do
  sed 's/:[0-9][0-9]*//g' "$f" >"$f.stripped" && mv -- "$f.stripped" "$f"
done < <(find "$dir" -type f -print)
expect_reject "total extraction failure" "$dir" 'extracted no citation tokens'

# R9. a root with none of the scanned trees must be refused, not passed
dir="$tmp_root/reject-no-trees"
rm -rf -- "$dir"
mkdir -p "$dir/generated"
printf 'nothing to scan here\n' >"$dir/generated/README.md"
expect_reject "root with no scanned tree" "$dir" 'none of the scanned trees'

# R10. a stray positional argument must be refused, not silently ignored
log="$tmp_root/stray.log"
if "$gate" "$fixture" >"$log" 2>&1; then
  printf 'FAIL gate accepted a stray positional argument\n' >&2
  exit 1
fi
grep -Fq 'unexpected argument' "$log" || {
  printf 'FAIL stray-argument refusal did not name its reason\n' >&2
  exit 1
}
rejected=$((rejected + 1))
printf 'PASS rejected: stray positional argument\n'

# ---------------------------------------------------------------------- totals

[[ "$rejected" -eq 11 ]] || {
  printf 'FAIL expected 11 rejections, counted %d\n' "$rejected" >&2
  exit 1
}
[[ "$accepted" -eq 6 ]] || {
  printf 'FAIL expected 6 acceptances, counted %d\n' "$accepted" >&2
  exit 1
}

printf 'PASS internal-citation gate rejects %d/11 specified violations and invocation defects\n' "$rejected"
printf 'PASS internal-citation gate accepts %d/6 specified legitimate citation classes\n' "$accepted"
printf 'PASS internal-citation gate reacts to %d/17 specified cases\n' "$((rejected + accepted))"
printf 'NOTE detector receipt only; says nothing about whether any real citation resolves to the claim that cites it\n'
