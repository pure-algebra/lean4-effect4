#!/bin/bash
# Probe MODS-4: run each printed client on the pinned host, over our Latch (`-lib`) and over
# Effect's own Latch (`-pin`), and print the two exits side by side.
# Run from the repository root: bash docs/research/2026-10-08-seat-MODULES/pin/run.sh
set -euo pipefail
root=$(pwd)
here="$root/docs/research/2026-10-08-seat-MODULES/pin"
work=$(mktemp -d)
ln -s "$root/harness/truth/node_modules" "$work/node_modules"
imports=$(sed -n 3,4p "$root/harness/truth/generated/pDefsOdd.ts" |
  sed "s|\"../prelude.ts\"|\"$root/harness/truth/prelude.ts\"|; s|import { Cause,|import { Latch, Cause,|")
footer='const exit = await Effect.runPromiseExit(main)
console.log(JSON.stringify(exit._tag === "Success" ? exit.value : String(exit.cause)))'
for client in d1 d2 d3; do
  for side in lib pin; do
    printf '%s\n%s\n%s\n' "$imports" "$(cat "$here/$client-$side.ts")" "$footer" > "$work/$client-$side.ts"
  done
  echo "$client ours: $(bun run "$work/$client-lib.ts")   Effect's: $(bun run "$work/$client-pin.ts")"
done
grep '"version"' "$work/node_modules/effect/package.json"
bun --version
rm -rf "$work"
