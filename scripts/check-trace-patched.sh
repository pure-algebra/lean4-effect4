#!/usr/bin/env bash
# Phase-2 host instrumentation (P-T11): build the patched rc.112 copy, run every
# flow golden against it (dispatch form), and require the service-level traces
# to agree under every mask exactly as with the unpatched copy: the hunks are
# observation-only. Then check the frame-level facts the patched rows expose:
# scope finalizers run latest-first with the closing exit, and every run pops
# frames. Receipts under harness/trace/receipts/patched/ carry the manifest
# digest; the copy itself is never committed.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools="${EFFECT4_TOOLS:-$repo_root/../effect4-tools}"
here="$repo_root/harness/trace"
cd "$repo_root"
lake build Effect4 >/dev/null
node "$here/patched/apply.mjs"
patched="$(node "$here/patched/apply.mjs" --print)"
export EFFECT4_EFFECT_NODE_MODULES="$patched"
export EFFECT4_PATCHED="$here/patched/patch-manifest.json"
mkdir -p "$here/receipts/patched"
# A resource-boundary golden carries `budget default <n>`; the patched copy adds
# no primitives (its hunks only observe), so the same budget lands the frontier.
budget_row() { awk -F'\t' -v want="$2" '$1=="budget" && $2==want {print $3}' "$1"; }
for golden in "$repo_root"/generated/traces/flow/*.tsv; do
  default_budget="$(budget_row "$golden" default)"
  base="$(basename "$golden" .tsv)"; program="${base%%.*}"
  EFFECT4_PROGRAM="$program" EFFECT4_BUDGET="${default_budget:-100000}" \
    node "$tools/packages/harness/trace.mjs" "$here" \
    --golden "$golden" --masks "$repo_root/generated/traces/masks.tsv" --tail flow-tail.ts \
    --receipt "$here/receipts/patched/$base.json" | sed 's/^trace/trace(patched)/' | grep -v "mask outcome"
done
echo "PASS patched copy: service-level traces agree with every flow golden under every mask"
# --- frame-level facts from the patched rows -----------------------------------
python3 - "$here/receipts/patched" <<'PY'
import json, os, sys
d = sys.argv[1]
def rows(name): return json.load(open(os.path.join(d, name + ".json")))["patchedFrames"]
def fail(m): print("FAIL " + m, file=sys.stderr); sys.exit(1)
two = [r for r in rows("regionTwoFail.empty") if r["row"] == "scope.close-lifo"]
if [r["index"] for r in two] != [1, 0] or any(r["exit"] != "Failure" for r in two):
    fail(f"regionTwoFail: expected two sequential finalizers latest-first with the failure, got {two}")
print("PASS scope.close-lifo: regionTwoFail runs its two releases latest-first, each with the closing Failure")
# rc.112 keeps a single registered finalizer inline (the reified ScopeState.openInline)
# and closes it without the finalizer loop: no scope.close-lifo row, one inline row.
one = rows("regionBothSucceed.empty")
if [r for r in one if r["row"] == "scope.close-lifo"]:
    fail("regionBothSucceed: a single release must not enter the finalizer loop")
if [(r["exit"]) for r in one if r["row"] == "scope.close-inline"] != ["Success"]:
    fail(f"regionBothSucceed: expected one inline close with Success, got {one}")
print("PASS scope.close-inline: regionBothSucceed closes its single release inline with the closing Success")
nested = [r for r in rows("regionNested.empty") if r["row"] in ("scope.close-inline", "scope.close-lifo", "scope.close-single")]
if [(r["row"], r["exit"]) for r in nested] != [("scope.close-inline", "Failure"), ("scope.close-inline", "Failure")]:
    fail(f"regionNested: expected the inner then the outer single release inline with the failure, got {nested}")
print("PASS scope.close-inline: regionNested closes both single-release scopes inline with the failure, inner first")
for name in ["incr.empty", "swap.once", "regionNested.empty"]:
    pops = [r for r in rows(name) if r["row"] == "frame.pop"]
    if not pops: fail(f"{name}: no frame.pop rows")
print("PASS frame.pop: every run records its continuation pops")
PY
echo "PASS patched host facts hold (receipts under harness/trace/receipts/patched/)"
