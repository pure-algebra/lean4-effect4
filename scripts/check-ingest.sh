#!/usr/bin/env bash
# Host acceptance: exact printer/foreign oracles, reachability, metamorphic tests,
# runtime reproducibility, original wire decoded independently by OCaml.
# The stamp covers tool traces, all package sources/fixtures/pins and OCaml inputs.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$repo_root"
. scripts/lib/portable.sh
. scripts/lib/stamp.sh
export LEAN_NUM_THREADS=3
lock="$repo_root/.lake/LANE.lock"
owned=0
if mkdir "$lock" 2>/dev/null; then
  owned=1
  export EFFECT4_LANE_OWNER="ingest-$$-$RANDOM"
  printf '%s\n' "$EFFECT4_LANE_OWNER" > "$lock/owner"
elif [[ -z "${EFFECT4_LANE_OWNER:-}" || ! -f "$lock/owner" ]] || [[ "$(cat "$lock/owner")" != "$EFFECT4_LANE_OWNER" ]]; then
  echo 'FAIL ingest: Lean lane is held by another run' >&2; exit 1
fi
work="$(mktemp -d "${TMPDIR:-/tmp}/effect4-ingest.XXXXXX")"
cleanup() {
  rm -rf -- "$work"
  if [[ "$owned" = 1 ]]; then rm -f "$lock/owner"; rmdir "$lock"; fi
}
trap cleanup EXIT
command -v bun >/dev/null
command -v node >/dev/null
command -v opam >/dev/null
before_lock="$(sha256 ts/eff/bun.lock)"
(cd ts/eff && bun install --frozen-lockfile)
[[ "$(sha256 ts/eff/bun.lock)" = "$before_lock" ]] || { echo 'FAIL ingest: lockfile drift' >&2; exit 1; }
bun ts/eff/ingest/cli.ts --help >/dev/null
lake build Tools.Corpus
key="$(stamp_key "$0" scripts/lib ts/eff/*.ts ts/eff/ingest ts/eff/test ts/eff/package.json ts/eff/bun.lock ts/eff/tsconfig.json tools/Tools/Corpus.lean tools/Tools/ForeignCorpus.lean tools/Tools/Styles.lean \
  harness/truth/IngestPrint.lean harness/truth/run-truth.ts harness/truth/prelude.ts \
  "$stamp_build_lib/Tools/Corpus.trace" ocaml/eff lean-toolchain \
  "$(stamp_fact bun "$(bun --version)")" "$(stamp_fact node "$(node --version)")")"
if stamp_hit ingest "$key"; then stamp_report ingest "$key"; exit 0; fi
lean_run tools/Tools/Corpus.lean "$work/printed" 400 4
lean_run tools/Tools/Corpus.lean --foreign "$work/foreign" 400 4
bun ts/eff/ingest/check-coverage.ts "$work/foreign"
bun ts/eff/ingest/cli.ts gate --printed "$work/printed" --foreign "$work/foreign"
# DI-37: the printed image against the foreign contract over the same printed corpus, up to the
# service-key renumbering the two contracts differ on. A printed module the foreign contract
# admits must lift to the printed oracle's program; the modules it refuses are reported with
# their codes, because the two contracts differ on the admitted language by design.
bun ts/eff/ingest/check-corpus.ts inclusion "$work/printed"
for mode in printed foreign; do bun ts/eff/ingest/check-metamorphic.ts "$mode" "$work/$mode"; done
bun ts/eff/ingest/check-metamorphic.ts negative ts/eff/ingest/fixtures/refusals
bun ts/eff/ingest/check-metamorphic.ts negative ts/eff/ingest/fixtures/witnesses
(cd ts/eff && bun run typecheck && bun test)
bun ts/eff/ingest/render-readme.ts --check
opam exec --switch=effect4 -- dune build --root ocaml eff/effect4_eff.cma
# Build outside the source tree, so OCaml's side products are temporary too.
cp ts/eff/ingest/check-wire.ml "$work/check-wire.ml"
opam exec --switch=effect4 -- ocamlc -I "$repo_root/ocaml/_build/default/eff/.effect4_eff.objs/byte" \
  "$repo_root/ocaml/_build/default/eff/effect4_eff.cma" "$work/check-wire.ml" -o "$work/check-wire"
"$work/check-wire" "$work/printed" "$work/foreign"
[[ "$(sha256 ts/eff/bun.lock)" = "$before_lock" ]] || { echo 'FAIL ingest: lockfile drift' >&2; exit 1; }
bun ts/eff/ingest/check-fidelity.ts
summary='original JSON/wire/key oracles, printed-in-foreign inclusion up to key renumbering, source-edit invariance, refusal reachability, pinned runtime reproducibility, OCaml exact decoding and original/reprinted fidelity probes'
printf 'PASS ingest: %s\n' "$summary"
stamp_write ingest "$key" "$summary"
