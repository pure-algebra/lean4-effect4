#!/usr/bin/env bash
# Joins the frozen coverage rows (Effect4Test/Target/TypeScript/LoweringCoverage.lean)
# with the evidence on disk and prints generated/lowering-coverage.tsv to stdout.
# It refuses, before printing a byte: a rule tag without a row or a row without
# a tag; a claimed golden that is missing or does not list the rule; a host
# claim without an all-ok receipt at the current pin; a property or type
# claim without its batch or receipt file.
#   --sources <dir>   tag scan root instead of Effect4/Target/TypeScript   (self-test only)
#   --traces <dir>    goldens instead of generated/traces                  (self-test only)
#   --receipts <dir>  host receipts instead of harness/trace/receipts      (self-test only)
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "$repo_root/scripts/lib/portable.sh"
cd "$repo_root"
sources="Effect4/Target/TypeScript"; traces="generated/traces"; receipts="harness/trace/receipts"
while [ $# -gt 0 ]; do
  case "$1" in
    --sources) sources="$2"; shift 2 ;;
    --traces) traces="$2"; shift 2 ;;
    --receipts) receipts="$2"; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
for variable in EFFECT4_LOWERING_COVERAGE_SOURCE EFFECT4_LOWERING_COVERAGE_CANDIDATE; do
  [ -z "${!variable:-}" ] || { echo "FAIL $variable is not an admitted override" >&2; exit 2; }
done
tmp="$(mktemp -d "${TMPDIR:-/tmp}/effect4-lowering.XXXXXX")"; trap 'rm -rf -- "$tmp"' EXIT
lake build Effect4 >/dev/null
# --- the numerator -----------------------------------------------------------
( unset LEAN_PATH LEAN_SRC_PATH; lake env lean Effect4Test/Target/TypeScript/LoweringCoverage.lean ) > "$tmp/driver.log" 2>&1 \
  || { echo "FAIL lowering coverage numerator did not elaborate" >&2; cat "$tmp/driver.log" >&2; exit 1; }
grep $'^E4LOWCOV\t' "$tmp/driver.log" | sed $'s/^E4LOWCOV\t//' > "$tmp/rows.tsv"
# --- rule tags in the sources, both directions -------------------------------
grep -rho 'lowering: rule\.[a-z][a-z-]*' "$sources" | sed 's/lowering: rule\.//' | LC_ALL=C sort -u > "$tmp/tags.txt"
cut -f1 "$tmp/rows.tsv" | LC_ALL=C sort -u > "$tmp/ruled.txt"
if ! cmp -s "$tmp/tags.txt" "$tmp/ruled.txt"; then
  echo "FAIL lowering rule census: tags in $sources and Rule.all disagree" >&2
  diff "$tmp/tags.txt" "$tmp/ruled.txt" >&2 || true; exit 1
fi
# --- evidence joins ----------------------------------------------------------
pin_file="harness/trace/host-pin.json"
python3 - "$tmp/rows.tsv" "$traces" "$receipts" "$pin_file" > "$tmp/joined.tsv" <<'PY'
import json, sys, os, hashlib
rows_path, traces, receipts, pin_path = sys.argv[1:5]
pin = json.load(open(pin_path))
def sha(p): return hashlib.sha256(open(p,'rb').read()).hexdigest()
def fail(msg): print("FAIL " + msg, file=sys.stderr); sys.exit(1)
for line in open(rows_path):
    rule, state, goldens, host, prop, types, proof = line.rstrip("\n").split("\t")
    names = [g for g in goldens.split(",") if g]
    pinned = []
    for g in names:
        path = os.path.join(traces, g + ".tsv")
        if not os.path.exists(path): fail(f"missing golden evidence: {rule} claims {g} but {path} is absent")
        rules_row = [l for l in open(path) if l.startswith("rules\t")]
        listed = rules_row[0].rstrip("\n").split("\t")[1].split(",") if rules_row else []
        if rule not in listed: fail(f"undeclared golden evidence: {g} does not exercise {rule}")
        pinned.append(f"{g}:sha256={sha(path)}")
        if host == "1":
            rpath = os.path.join(receipts, g + ".json")
            if not os.path.exists(rpath): fail(f"host receipt missing: {rule} claims host evidence but {rpath} is absent")
            r = json.load(open(rpath))
            if any(v != "ok" for v in r.get("results", {}).values()): fail(f"host receipt not ok: {rpath}")
            rp = r.get("host", {}).get("pin") or {}
            for key in ("effectVersion", "effectUpstreamCommit", "effectTreeSha256", "typescriptVersion", "diagnosticVersion"):
                if rp.get(key) != pin.get(key): fail(f"host receipt pin differs from {pin_path}: {rpath} ({key})")
    if prop == "1" and not os.path.exists("generated/lowering-property.tsv"): fail(f"property batch missing for {rule}")
    if types == "1":
        for g in names:
            if not os.path.exists(os.path.join("harness/trace/types", g + ".receipt")): fail(f"type receipt missing for {g}")
    print("\t".join(["rule", rule, state, ",".join(pinned), host, prop, types, proof]))
PY
# --- print --------------------------------------------------------------------
effects_rev="$(python3 -c "import json;m=json.load(open('lake-manifest.json'));print(next(p['rev'] for p in m['packages'] if p['name']=='effects'))")"
# An abbreviated revision is not a durable identifier, and the provenance width
# once changed mid-corpus (survey finding H10). Refuse before a byte is printed.
[[ "$effects_rev" =~ ^[0-9a-f]{40}$ ]] || {
  echo "FAIL lake-manifest.json gives the effects rev as '$effects_rev'; a pin row must be 40 hex characters" >&2
  echo "  put the full sha in lakefile.toml and re-resolve the manifest" >&2
  exit 1
}
printf 'format\teffect4-lowering-coverage-v1\n'
printf 'generator\tscripts/generate-lowering-coverage.sh\tsha256=%s\n' "$(sha256 scripts/generate-lowering-coverage.sh)"
printf 'regenerate\t./scripts/generate-lowering-coverage.sh > generated/lowering-coverage.tsv\n'
for input in Effect4Test/Target/TypeScript/LoweringCoverage.lean Effect4/Target/TypeScript/Lower.lean Effect4/Target/TypeScript/EffectV4.lean docs/LOWERING-COVERAGE.md; do
  printf 'input\t%s\tsha256=%s\n' "$input" "$(sha256 "$input")"
done
printf 'pin\teffects\t%s\n' "$effects_rev"
printf 'columns\trule\tid\tstate\tgoldens\thost\tproperty\ttypeReceipt\tproof\n'
cat "$tmp/joined.tsv"
awk -F'\t' '{ n[$3]++ } END { for (s in n) printf "count\t%s\t%d\n", s, n[s] }' "$tmp/joined.tsv" | LC_ALL=C sort
