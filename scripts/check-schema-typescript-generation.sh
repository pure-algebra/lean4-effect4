#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
harness_dir="$project_root/harness/schema-generation"
node_modules="${EFFECT4_EFFECT_NODE_MODULES:-$project_root/harness/schema-host/node_modules}"

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

# the trailing slash follows a linked `node_modules` (a worktree links the main checkout's)
host_compiler="$(find "$node_modules/" -path '*/@typescript/typescript-*/lib/tsc.original' -type f -print -quit)"
if [[ -z "$host_compiler" ]]; then
  echo "schema TypeScript harness: unpatched TypeScript compiler not found" >&2
  exit 1
fi

temporary_dir="$(mktemp -d)"
trap 'rm -rf "$temporary_dir"' EXIT

cd "$project_root"
emit_and_compare() {
  if ! lake env lean -M4096 "$harness_dir/$1" > "$temporary_dir/$2"; then
    cat "$temporary_dir/$2" >&2
    return 1
  fi
  cmp -- "$harness_dir/$2" "$temporary_dir/$2"
}
emit_and_compare EmitFixture.lean Person.generated.ts
emit_and_compare EmitCoverageFixture.lean AllRepresentations.generated.ts
emit_and_compare EmitMultiFixture.lean TwoRoots.generated.ts

cp "$harness_dir/tsconfig.json" "$temporary_dir/tsconfig.json"
cp "$harness_dir/runtime-check.ts" "$temporary_dir/runtime-check.ts"
cp "$harness_dir/coverage-runtime-check.ts" \
  "$temporary_dir/coverage-runtime-check.ts"
cp "$harness_dir/multi-runtime-check.ts" "$temporary_dir/multi-runtime-check.ts"
# The language-service launcher chmods its bundled compiler on every invocation.
# Keep the selected installation read-only, including a shared Foldlab install.
cp -RL "$node_modules" "$temporary_dir/node_modules"
node_modules="$temporary_dir/node_modules"

if ! compiler_output="$("$host_compiler" -p "$temporary_dir/tsconfig.json" --pretty false 2>&1)"; then
  printf '%s\n' "$compiler_output" >&2
  echo "schema TypeScript harness: direct compiler failed" >&2
  exit 1
fi
if [[ -n "$compiler_output" ]]; then
  printf '%s\n' "$compiler_output" >&2
  echo "schema TypeScript harness: direct compiler emitted diagnostics" >&2
  exit 1
fi

diagnostics="$temporary_dir/effect-language-service.json"
if ! (
  cd "$temporary_dir"
  "$node_modules/.bin/effect-tsgo" diagnostics \
    --project tsconfig.json --format json --strict --list-files > "$diagnostics"
); then
  cat "$diagnostics" >&2
  echo "schema TypeScript harness: language service command failed" >&2
  exit 1
fi

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

# rc.112 writes its own RPC documents; Lean reads every one (slice A1, the persisted boundary).
documents_fixture="$project_root/Test/fixtures/schema-documents/effect-rpc-rc112.json"
cp "$harness_dir/export-rpc.ts" "$temporary_dir/export-rpc.ts"
if ! NODE_NO_WARNINGS=1 "$node_bin" --experimental-strip-types \
  "$temporary_dir/export-rpc.ts" > "$temporary_dir/effect-rpc-rc112.json"; then
  echo "schema TypeScript harness: rc.112 did not write its RPC documents" >&2
  exit 1
fi
if ! cmp -- "$documents_fixture" "$temporary_dir/effect-rpc-rc112.json"; then
  echo "schema TypeScript harness: rc.112's RPC documents differ from the fixture" >&2
  exit 1
fi
if ! lake env lean -M4096 "$project_root/Test/Schema/DocumentJson.lean" \
  > "$temporary_dir/document-json.log" 2>&1; then
  cat "$temporary_dir/document-json.log" >&2
  echo "schema TypeScript harness: Lean's reading of rc.112's documents failed" >&2
  exit 1
fi

echo "schema TypeScript harness: fixture bytes match Lean generation"
echo "schema TypeScript harness: 22-constructor corpus bytes match Lean generation"
echo "schema TypeScript harness: two-root multi-document bytes match Lean generation"
echo "schema TypeScript harness: direct compiler $typescript_version passed"
echo "schema TypeScript harness: effect $effect_version revived the document and the two-root multi-document"
echo "schema TypeScript harness: language service $tsgo_version passed"
echo "schema TypeScript harness: effect $effect_version rewrote its RPC documents byte for byte; Lean read every one"
