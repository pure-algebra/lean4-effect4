#!/usr/bin/env bash
# Phase-2 host instrumentation (P-T11): build the patched rc.112 copy, run every
# flow golden against it (dispatch form), and require the service-level traces
# to agree under every mask exactly as with the unpatched copy: the hunks are
# observation-only. Then check the frame-level facts the patched rows expose:
# scope finalizers run latest-first with the closing exit, and every run pops
# frames. Receipts under harness/trace/receipts/patched/ carry the manifest
# digest; the copy itself is never committed.
#
# ## Stamp (rule 9)
#
# What it reads: the patch machinery -- `patched/apply.mjs`, which builds the
# copy, and `patched/patch-manifest.json`, whose digest every receipt carries;
# the harness TypeScript and tsconfig, since `flow-tail.ts` and `tracer.ts`
# drive the runs; the flow goldens and the mask table under `generated/traces/`;
# the effect4-tools trace runner; and the identity of the unpatched
# installation the copy is made from. `patched/_copy/` is an output of
# `apply.mjs`, not an input, and the receipts under `receipts/patched/` are
# written by this gate and read back by it in the same run.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
. "$repo_root/scripts/lib/stamp.sh"
tools="${EFFECT4_TOOLS:-$repo_root/../effect4-tools}"
here="$repo_root/harness/trace"
for argument in "$@"; do
  case "$argument" in
    --force) export EFFECT4_FORCE=1 ;;
    *) echo "unknown argument $argument" >&2; exit 2 ;;
  esac
done
cd "$repo_root"
lake build Effect4 >/dev/null
inputs=(
  "$repo_root/scripts/check-trace-patched.sh"
  "$repo_root/scripts/lib/portable.sh"
  "$repo_root/scripts/lib/stamp.sh"
  "$here/patched/apply.mjs"
  "$here/patched/patch-manifest.json"
  "$here/patched/trace-host-pin.json"
  "$here/tsconfig.json"
  "$repo_root/generated/traces"
  "$stamp_build_lib/Effect4.trace"
  "$repo_root/lakefile.toml"
  "$repo_root/lake-manifest.json"
  "$repo_root/lean-toolchain"
)
for module in "$here"/*.ts; do inputs+=("$module"); done
while IFS= read -r input; do inputs+=("$input"); done < <(
  stamp_tools_inputs trace.mjs copy.mjs
  stamp_host_inputs
)
key="$(stamp_key "${inputs[@]}")"
if stamp_hit trace-patched "$key"; then
  stamp_report trace-patched "$key"
  exit 0
fi
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
stamp_write trace-patched "$key" "$(printf \
  'the patched copy agrees with %s flow goldens under every mask; scope close order and frame.pop hold' \
  "$(find "$repo_root/generated/traces/flow" -maxdepth 1 -name '*.tsv' | wc -l | tr -d ' ')")"
