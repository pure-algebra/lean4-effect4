#!/usr/bin/env bash
# Finite observations of the pinned host; no Lean simulation claim.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
harness_dir="$repo_root/harness/fiber-supervision"
node_modules="${EFFECT4_EFFECT_NODE_MODULES:-$repo_root/../foldlab/library/effects/node_modules}"
node_bin="$(command -v node)"

"$node_bin" --input-type=module - "$node_modules" "$harness_dir/host-pin.json" \
  "$repo_root/vendor/effect-4.0.0-rc.112/src/internal/effect.ts" <<'JS'
import assert from "node:assert/strict"
import { createHash } from "node:crypto"
import fs from "node:fs"
import path from "node:path"
const [modules, pinFile, vendored] = process.argv.slice(2)
const pin = JSON.parse(fs.readFileSync(pinFile, "utf8"))
const root = path.join(modules, "effect")
const version = name => JSON.parse(fs.readFileSync(path.join(modules, name, "package.json"), "utf8")).version
assert.equal(version("effect"), pin.effectVersion)
assert.equal(version("typescript"), pin.typescriptVersion)
assert.equal(version("@effect/tsgo"), pin.diagnosticVersion)
assert.deepEqual(fs.readFileSync(path.join(root, "src/internal/effect.ts")), fs.readFileSync(vendored))
const files = []
function walk(relative = "") {
  for (const entry of fs.readdirSync(path.join(root, relative), { withFileTypes: true })) {
    const child = path.join(relative, entry.name)
    assert(!entry.isSymbolicLink(), `unexpected package symlink: ${child}`)
    if (entry.isDirectory()) walk(child)
    else if (entry.isFile()) files.push(child.split(path.sep).join("/"))
  }
}
walk()
const sha = bytes => createHash("sha256").update(bytes).digest("hex")
const records = files.sort().map(file => `${file}\0${sha(fs.readFileSync(path.join(root, file)))}\n`).join("")
assert.equal(files.length, pin.effectFileCount)
assert.equal(sha(records), pin.effectTreeSha256)
console.log(`PASS exact Effect ${pin.effectVersion} package tree and vendored runtime source`)
console.log(`HOST ${process.version} ${process.platform}/${process.arch}; TypeScript ${pin.typescriptVersion}; diagnostics ${pin.diagnosticVersion}`)
JS

host_compiler="$(find "$node_modules" -path '*/@typescript/typescript-*/lib/tsc.original' -type f -print -quit)"
[[ -n "$host_compiler" && -x "$host_compiler" ]] || {
  printf 'FAIL pinned unpatched TypeScript compiler is unavailable\n' >&2
  exit 1
}

temporary_dir="$(mktemp -d "${TMPDIR:-/tmp}/effect4-supervision-host.XXXXXX")"
temporary_dir="$(cd -- "$temporary_dir" && pwd -P)"
trap 'rm -rf -- "$temporary_dir"' EXIT
cp "$harness_dir/runtime-check.ts" "$harness_dir/tsconfig.json" "$temporary_dir/"
ln -s "$node_modules" "$temporary_dir/node_modules"

"$host_compiler" -p "$temporary_dir/tsconfig.json" --pretty false
"$host_compiler" -p "$temporary_dir/tsconfig.json" --listFilesOnly \
  > "$temporary_dir/analyzed-files.txt"
grep -Fxq "$temporary_dir/runtime-check.ts" "$temporary_dir/analyzed-files.txt"

# A buildable control first; this deliberately wrong assignment must reach
# the compiler and fail for its type error, not a missing file or executable.
printf '\nconst supervisionTypeErrorControl: number = "wrong"\n' \
  >> "$temporary_dir/runtime-check.ts"
if "$host_compiler" -p "$temporary_dir/tsconfig.json" --pretty false \
  > "$temporary_dir/type-control.log" 2>&1; then
  printf 'FAIL TypeScript accepted the deliberately wrong assignment\n' >&2
  exit 1
fi
grep -Eq 'runtime-check\.ts.*error TS2322:' "$temporary_dir/type-control.log"
cp "$harness_dir/runtime-check.ts" "$temporary_dir/runtime-check.ts"
"$host_compiler" -p "$temporary_dir/tsconfig.json" --pretty false
printf 'PASS direct compiler accepted, rejected the type-error control, and accepted restoration\n'

if ! (
  cd "$temporary_dir"
  "$node_modules/.bin/effect-tsgo" diagnostics \
    --project tsconfig.json --format json --strict --list-files > diagnostics.json
); then
  cat "$temporary_dir/diagnostics.json" >&2
  exit 1
fi
"$node_bin" --input-type=module - "$temporary_dir/diagnostics.json" <<'JS'
import assert from "node:assert/strict"
import fs from "node:fs"
const report = JSON.parse(fs.readFileSync(process.argv[2], "utf8"))
assert.equal(report.summary?.errors, 0)
assert.equal(report.summary?.warnings, 0)
assert.equal(report.summary?.filesChecked, 1)
assert.equal(report.files?.length, 1)
assert(report.files.every(file => file.detectedEffect === "v4" && file.supportedEffect === "v4"))
console.log("PASS Effect diagnostics examined the one complete harness file")
JS

cmp "$harness_dir/runtime-check.ts" "$temporary_dir/runtime-check.ts"
NODE_NO_WARNINGS=1 "$node_bin" --experimental-strip-types "$temporary_dir/runtime-check.ts"
