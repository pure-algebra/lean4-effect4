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

cp "$harness_dir/tsconfig.json" "$temporary_dir/tsconfig.json"
cp "$harness_dir/runtime-check.ts" "$temporary_dir/runtime-check.ts"
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

"$node_bin" -e '
  const fs = require("node:fs")
  const report = JSON.parse(fs.readFileSync(process.argv[1], "utf8"))
  const clean = report.summary?.errors === 0 && report.summary?.warnings === 0 &&
    report.summary?.filesChecked === 2 && report.files?.length === 2 &&
    report.files.every((file) =>
      file.detectedEffect === "v4" && file.supportedEffect === "v4")
  if (!clean) process.exit(1)
' "$diagnostics"

NODE_NO_WARNINGS=1 "$node_bin" --experimental-strip-types \
  "$temporary_dir/runtime-check.ts"

echo "schema TypeScript harness: fixture bytes match Lean generation"
echo "schema TypeScript harness: direct compiler $typescript_version passed"
echo "schema TypeScript harness: effect $effect_version revived the document"
echo "schema TypeScript harness: language service $tsgo_version passed"
