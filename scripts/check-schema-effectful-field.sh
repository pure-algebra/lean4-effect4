#!/usr/bin/env bash
# usage: EFFECT4_EFFECT_NODE_MODULES=<pinned node_modules> ./scripts/check-schema-effectful-field.sh
#
# Target host gate for `test/contracts/schema-effectful-field-typescript.contract.md`.
# It pins the host profile, then runs `harness/schema-effectful-field/check.sh`
# end to end: the hand-written positive file, the three named language-service
# mutants, and the Lean-generated module under direct TypeScript, effect-tsgo,
# and the Effect runtime. Host evidence about one exact profile only.
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
harness_dir="$project_root/harness/schema-effectful-field"
node_modules="${EFFECT4_EFFECT_NODE_MODULES:-$project_root/../foldlab/library/effects/node_modules}"

if [[ ! -d "$node_modules/effect" ]]; then
  echo "schema effectful-field harness: set EFFECT4_EFFECT_NODE_MODULES to the exact pinned node_modules directory" >&2
  exit 1
fi

node_bin="$(command -v node)"
effect_version="$($node_bin -p 'require(process.argv[1]).version' "$node_modules/effect/package.json")"
typescript_version="$($node_bin -p 'require(process.argv[1]).version' "$node_modules/typescript/package.json")"
tsgo_version="$($node_bin -p 'require(process.argv[1]).version' "$node_modules/@effect/tsgo/package.json")"

[[ "$effect_version" == "4.0.0-rc.112" ]]
[[ "$typescript_version" == "7.0.2" ]]
[[ "$tsgo_version" == "0.38.0" ]]

host_compiler="$(find "$node_modules" -path '*/@typescript/typescript-*/lib/tsc.original' -type f -print -quit)"
if [[ -z "$host_compiler" ]]; then
  echo "schema effectful-field harness: unpatched TypeScript compiler not found" >&2
  exit 1
fi

if [[ ! -x "$harness_dir/check.sh" ]]; then
  echo "schema effectful-field harness: harness driver is absent or not executable" >&2
  exit 1
fi

temporary_dir="$(mktemp -d)"
trap 'rm -rf "$temporary_dir"' EXIT

harness_log="$temporary_dir/check.log"
cd "$project_root"
if ! EFFECT4_EFFECT_NODE_MODULES="$node_modules" "$harness_dir/check.sh" \
    >"$harness_log" 2>&1; then
  cat "$harness_log" >&2
  echo "schema effectful-field harness: host oracle rejected the field API" >&2
  exit 1
fi

# A silent driver is not a pass. Every receipt the harness owes must be present.
required_receipts=(
  "schema effectful field: TypeScript $typescript_version passed"
  "schema effectful field: Effect $effect_version runtime passed"
  "schema effectful field: effect-tsgo $tsgo_version diagnostics passed"
  "schema effectful field: Lean-generated target passed"
)
for receipt in "${required_receipts[@]}"; do
  if ! grep -Fq -- "$receipt" "$harness_log"; then
    cat "$harness_log" >&2
    echo "schema effectful-field harness: missing receipt: $receipt" >&2
    exit 1
  fi
done

echo "schema effectful-field harness: positive field API typechecked and ran read-before-write"
echo "schema effectful-field harness: floatingEffect, missingEffectError, missingEffectContext each reported exactly once"
echo "schema effectful-field harness: Lean-generated module matched the hand-written profile"
echo "schema effectful-field harness: direct compiler $typescript_version passed"
echo "schema effectful-field harness: effect $effect_version ran the generated field API"
echo "schema effectful-field harness: language service $tsgo_version passed"
