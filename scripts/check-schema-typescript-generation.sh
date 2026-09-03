#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
harness_dir="$project_root/harness/schema-generation"
node_modules="${EFFECT4_EFFECT_NODE_MODULES:-$project_root/../foldlab/library/effects/node_modules}"

if [[ ! -d "$node_modules/effect" ]]; then
  echo "schema TypeScript harness: set EFFECT4_EFFECT_NODE_MODULES to the exact pinned node_modules directory" >&2
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
  echo "schema TypeScript harness: unpatched TypeScript compiler not found" >&2
  exit 1
fi

temporary_dir="$(mktemp -d)"
trap 'rm -rf "$temporary_dir"' EXIT

cd "$project_root"
lake env lean "$harness_dir/EmitFixture.lean" > "$temporary_dir/Person.generated.ts"
cmp "$harness_dir/Person.generated.ts" "$temporary_dir/Person.generated.ts"
lake env lean "$harness_dir/EmitCoverageFixture.lean" > \
  "$temporary_dir/AllRepresentations.generated.ts"
cmp "$harness_dir/AllRepresentations.generated.ts" \
  "$temporary_dir/AllRepresentations.generated.ts"
lake env lean "$harness_dir/EmitMultiFixture.lean" > \
  "$temporary_dir/TwoRoots.generated.ts"
cmp "$harness_dir/TwoRoots.generated.ts" "$temporary_dir/TwoRoots.generated.ts"

cp "$harness_dir/tsconfig.json" "$temporary_dir/tsconfig.json"
cp "$harness_dir/runtime-check.ts" "$temporary_dir/runtime-check.ts"
cp "$harness_dir/coverage-runtime-check.ts" \
  "$temporary_dir/coverage-runtime-check.ts"
cp "$harness_dir/multi-runtime-check.ts" "$temporary_dir/multi-runtime-check.ts"
ln -s "$node_modules" "$temporary_dir/node_modules"

compiler_output="$("$host_compiler" -p "$temporary_dir/tsconfig.json" --pretty false 2>&1)"
if [[ -n "$compiler_output" ]]; then
  printf '%s\n' "$compiler_output" >&2
  echo "schema TypeScript harness: direct compiler emitted diagnostics" >&2
  exit 1
fi

diagnostics="$temporary_dir/effect-language-service.json"
(
  cd "$temporary_dir"
  "$node_modules/.bin/effect-tsgo" diagnostics \
    --project tsconfig.json --format json --strict --list-files > "$diagnostics"
)

if ! "$node_bin" -e '
  const fs = require("node:fs")
  const report = JSON.parse(fs.readFileSync(process.argv[1], "utf8"))
  const clean = report.summary?.errors === 0 && report.summary?.warnings === 0 &&
    report.summary?.filesChecked === 6 && report.files?.length === 6 &&
    report.files.every((file) =>
      file.detectedEffect === "v4" && file.supportedEffect === "v4")
  if (!clean) process.exit(1)
' "$diagnostics"; then
  echo "schema TypeScript harness: language service did not report 6 clean v4 files" >&2
  exit 1
fi

# A runtime check that stopped asserting is not evidence. Pin how many
# assertions each receipt owes, and require the receipt line it prints.
runtime_assertions="$(grep -c 'throw new Error(' "$harness_dir/runtime-check.ts")"
if [[ "$runtime_assertions" != 6 ]]; then
  echo "schema TypeScript harness: runtime-check.ts must keep exactly 6 assertions, found $runtime_assertions" >&2
  exit 1
fi
coverage_assertions="$(grep -c 'throw new Error(' \
  "$harness_dir/coverage-runtime-check.ts")"
if [[ "$coverage_assertions" != 2 ]]; then
  echo "schema TypeScript harness: coverage-runtime-check.ts must keep exactly 2 assertions, found $coverage_assertions" >&2
  exit 1
fi
multi_assertions="$(grep -c 'throw new Error(' "$harness_dir/multi-runtime-check.ts")"
if [[ "$multi_assertions" != 4 ]]; then
  echo "schema TypeScript harness: multi-runtime-check.ts must keep exactly 4 assertions, found $multi_assertions" >&2
  exit 1
fi

runtime_output="$(NODE_NO_WARNINGS=1 "$node_bin" --experimental-strip-types \
  "$temporary_dir/runtime-check.ts")"
if [[ "$runtime_output" != "schema-generation-runtime: ok" ]]; then
  printf '%s\n' "$runtime_output" >&2
  echo "schema TypeScript harness: document runtime receipt is absent" >&2
  exit 1
fi
printf '%s\n' "$runtime_output"

coverage_output="$(NODE_NO_WARNINGS=1 "$node_bin" --experimental-strip-types \
  "$temporary_dir/coverage-runtime-check.ts")"
if [[ "$coverage_output" != "schema-generation-coverage: 22 representations, 2 checks" ]]; then
  printf '%s\n' "$coverage_output" >&2
  echo "schema TypeScript harness: corpus runtime receipt is absent" >&2
  exit 1
fi
printf '%s\n' "$coverage_output"

multi_output="$(NODE_NO_WARNINGS=1 "$node_bin" --experimental-strip-types \
  "$temporary_dir/multi-runtime-check.ts")"
if [[ "$multi_output" != "schema-generation-multi: 2 roots, 1 shared reference" ]]; then
  printf '%s\n' "$multi_output" >&2
  echo "schema TypeScript harness: multi-document runtime receipt is absent" >&2
  exit 1
fi
printf '%s\n' "$multi_output"

echo "schema TypeScript harness: fixture bytes match Lean generation"
echo "schema TypeScript harness: 22-constructor corpus bytes match Lean generation"
echo "schema TypeScript harness: two-root multi-document bytes match Lean generation"
echo "schema TypeScript harness: direct compiler $typescript_version passed"
echo "schema TypeScript harness: effect $effect_version revived the document and the two-root multi-document"
echo "schema TypeScript harness: language service $tsgo_version passed"
