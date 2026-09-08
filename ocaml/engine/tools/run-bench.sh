#!/usr/bin/env bash
# ocaml/engine/tools/run-bench.sh — lane B: ONE script that reproduces the whole bench
# receipt (docs/research/2026-09-08-engine-bench.md).
#
# It builds every bench binary of `ocaml/engine/test` and `ocaml/engine/cas/test` plus this
# lane's `e4_engine_bench`, runs them all, and writes one Markdown document to stdout (and,
# with -o, to a file).  Nothing here measures anything itself: every number is printed by
# the binary its own lane wrote, so a lane that changes its floor changes this receipt by
# rebuilding, not by editing prose.
#
#   bash ocaml/engine/tools/run-bench.sh [-o OUT.md] [-d BENCHDIR] [-q] [-r REPS] [SECTION...]
#
#     -o OUT     also write the collected Markdown to OUT
#     -d DIR     the DISK directory the CAS cells use.  Default $HOME/effect4-bench.
#                It MUST be on the Linux filesystem: A2-OQ1 measured /mnt/c at 72-146x
#                slower, and every fsync number is meaningless there.  The script refuses
#                a directory under /mnt/.
#     -q         quick: fewer reps and a small cap, for a smoke run (not a receipt)
#     -r REPS    best-of-REPS for e4_engine_bench (default 5)
#     SECTION... any of: engine cas route1 all   (default: all)
#
# Environment it sets for the children:
#   E4_BENCH_REPS / E4_BENCH_CAP / E4_BENCH_TARGET  — e4_engine_bench's method knobs
#   E4_PACK_TMP / E4_CAS_TMP / E4_INDEX_TMP / E4_CACHE_TMP / E4_CHECKPOINT_TMP — the disk dir
#
# WSL2 CAVEAT, stated once and repeated in the receipt: this host is WSL2.  $HOME is ext4 on
# a virtual disk (`/dev/sdd`); /mnt/c is a 9p mount of the Windows filesystem.  `fsync`
# semantics on both differ from bare metal — lane P1 measured 9p's fsync FASTER than ext4's,
# twice, which is a fact about the 9p server's durability and not about the code.  Every
# durability cell below is therefore an upper bound on this host, not a portable number.
set -uo pipefail

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ocaml_dir=$(CDPATH= cd -- "$here/../.." && pwd)   # .../ocaml
repo=$(CDPATH= cd -- "$ocaml_dir/.." && pwd)

out=""
benchdir="${HOME}/effect4-bench"
reps=5
cap=25
target=0.030
sections=""

while [ $# -gt 0 ]; do
  case "$1" in
    -o) out="$2"; shift 2 ;;
    -d) benchdir="$2"; shift 2 ;;
    -r) reps="$2"; shift 2 ;;
    -q) reps=1; cap=3; target=0.005; shift ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) sections="$sections $1"; shift ;;
  esac
done
[ -n "$sections" ] || sections="all"

want () {
  case " $sections " in
    *" all "*) return 0 ;;
    *" $1 "*) return 0 ;;
    *) return 1 ;;
  esac
}

case "$benchdir" in
  /mnt/*) echo "refusing $benchdir: the CAS cells must run on the Linux filesystem (A2-OQ1)" >&2
          exit 2 ;;
esac
mkdir -p "$benchdir"

export E4_BENCH_REPS="$reps" E4_BENCH_CAP="$cap" E4_BENCH_TARGET="$target"
export E4_PACK_TMP="$benchdir" E4_CAS_TMP="$benchdir" E4_INDEX_TMP="$benchdir"
export E4_CACHE_TMP="$benchdir" E4_CHECKPOINT_TMP="$benchdir"

log=$(mktemp)
trap 'rm -f "$log"' EXIT
emit () { printf '%s\n' "$*" >> "$log"; printf '%s\n' "$*"; }
run () {  # run <label> <command...>
  local label="$1"; shift
  emit ""
  emit "<!-- ============================================================ -->"
  emit "## $label"
  emit ""
  emit '```'
  local t0 t1 rc
  t0=$(date +%s)
  "$@" 2>&1 | tee -a "$log"
  rc=${PIPESTATUS[0]}
  t1=$(date +%s)
  [ "$rc" = 0 ] || emit "(exit $rc — recorded, not fatal)"
  emit '```'
  emit ""
  emit "_command: \`$*\` — $((t1 - t0)) s_"
}

# ------------------------------------------------------------------ the build, with retry
build_targets="engine"
build_ok=0
build_note="first attempt"
attempt=0
cd "$ocaml_dir" || exit 2
while [ $attempt -lt 15 ]; do
  attempt=$((attempt + 1))
  if berr=$(dune build $build_targets 2>&1); then
    build_ok=1
    [ $attempt -gt 1 ] && build_note="green on attempt $attempt (other lanes were mid-edit)"
    break
  fi
  echo "--- dune build failed on attempt $attempt; other lanes may be mid-edit. Retrying in 60 s." >&2
  echo "$berr" | head -5 >&2
  build_note="attempt $attempt failed: $(echo "$berr" | head -3 | tr '\n' ' ')"
  sleep 60
done

# ------------------------------------------------------------------ the header
{
  echo "# engine bench — collected run"
  echo
  echo "| what | value |"
  echo "| --- | --- |"
  echo "| date | $(date -Is) |"
  echo "| host | $(uname -srm) |"
  echo "| nproc | $(nproc) |"
  echo "| OCaml | $(ocamlfind ocamlopt -version 2>/dev/null || ocamlopt -version) |"
  echo "| dune | $(dune --version) |"
  echo "| switch | ${OPAM_SWITCH_PREFIX:-<none>} |"
  echo "| repo | $repo |"
  echo "| HEAD | $(git -C "$repo" rev-parse --short HEAD 2>/dev/null) |"
  echo "| bench dir (disk cells) | $benchdir ($(df -T "$benchdir" | tail -1 | awk '{print $2, $1}')) |"
  echo "| build | $([ $build_ok = 1 ] && echo green || echo FAILED) — $build_note |"
  echo "| method | best of $reps, median beside; cap ${cap}s; Gc.compact between reps |"
  echo
  echo "WSL2 caveat: \$HOME is ext4 on a virtual disk and /mnt/c is a 9p mount; fsync"
  echo "semantics on both differ from bare metal, so every durability cell is an upper"
  echo "bound on this host rather than a portable number (lane P1 measured 9p's fsync"
  echo "FASTER than ext4's, twice)."
} > "$log"
cat "$log"

if [ $build_ok = 0 ]; then
  emit ""
  emit "**The build never went green in 15 attempts (~15 min). Nothing below was re-run.**"
  [ -n "$out" ] && cp "$log" "$out"
  exit 1
fi

B=_build/default

# ------------------------------------------------------------------ the engine's own cells
if want engine; then
  run "W1–W4, the domain sweep and the acceptance table (lane B, \`e4_engine_bench\`)" \
      ./$B/engine/test/e4_engine_bench.exe
  run "C1–C6 carriers and the small-size crossover (lane C, \`bench_carriers\`)" \
      ./$B/engine/test/bench_carriers.exe
  run "B-Q2a–d timers (lane Q2, \`bench_timers\`)" \
      ./$B/engine/test/bench_timers.exe
  run "B-Q3a–c, B-Q5a–c log/index/query (lane Q3, \`bench_query\`)" \
      ./$B/engine/test/bench_query.exe
  run "the trace over E4_log.Vec (lane W, \`bench_trace\`)" \
      ./$B/engine/test/bench_trace.exe
  run "B-Q1a/B-Q1b dispatcher + the 100 000-op differential (lane Q1, \`test_buckets\`)" \
      ./$B/engine/test/test_buckets.exe
  run "B-Q4a mailbox contention (lane Q4, \`test_host\`)" \
      ./$B/engine/test/test_host.exe
  run "B-Q4b wake latency (lane Q5, \`test_sched\`)" \
      ./$B/engine/test/test_sched.exe
fi

# ------------------------------------------------------------------ the CAS disk cells
# Each binary is given its OWN subdirectory so the cells do not share a page cache or a
# pack; `bench_cache` and `bench_bycid` create children of the directory they are given and
# do NOT create it themselves, so it must exist first (measured: `Unix.ENOENT, "mkdir"`).
if want cas; then
  mkdir -p "$benchdir/pack" "$benchdir/wal" "$benchdir/cas" "$benchdir/index" \
           "$benchdir/cache" "$benchdir/ckpt" "$benchdir/bycid"
  run "B1/B6 pack append + fsync (lane P1, \`bench_pack\`)" \
      ./$B/engine/cas/test/bench_pack.exe "$benchdir/pack"
  run "B8/B9 WAL append + replay (lane P5, \`bench_wal\`)" \
      ./$B/engine/cas/test/bench_wal.exe "$benchdir/wal"
  run "B1/B2/B3 store put/get + the SHA-256 ceiling (lane P4, \`bench_cas\`)" \
      ./$B/engine/cas/test/bench_cas.exe "$benchdir/cas"
  run "B4/B5 index lookups, memory and rebuild (lane P2, \`bench_index\`)" \
      ./$B/engine/cas/test/bench_index.exe "$benchdir/index"
  run "B10 cache hit ratio, subterm and dependents (lane P7, \`bench_cache\`)" \
      ./$B/engine/cas/test/bench_cache.exe "$benchdir/cache"
  run "B7 checkpoint sharing and the chunker (lane P6, \`bench_checkpoint\`)" \
      ./$B/engine/cas/test/bench_checkpoint.exe "$benchdir/ckpt"
  run "by_cid / pin_all (lane W item 4, \`bench_bycid\`)" \
      ./$B/engine/cas/test/bench_bycid.exe "$benchdir/bycid"
fi

# ------------------------------------------------------------------ route 1, the floor
if want route1; then
  r1=$repo/ocaml/link/_build/default/e4_bench.exe
  if [ -x "$r1" ]; then
    run "ROUTE 1 (Lean compiled to C, linked): the published floor, RE-MEASURED today" \
        "$r1" 200 3 20000
    run "ROUTE 1: 2 000 machines" "$r1" 2000 3 200
  else
    emit ""
    emit "## ROUTE 1"
    emit ""
    emit "\`$r1\` is not built and \`link/tools/build.sh\` needs a Lean compile of"
    emit "\`Bridge.lean\` (\`ocaml/link/tools/compile-bridge.sh\`), which this lane may not run."
    emit "Quote \`ocaml/link/REPORT.md\` §7 instead."
  fi
fi

emit ""
emit "== run-bench done =="
[ -n "$out" ] && { cp "$log" "$out"; echo "written: $out" >&2; }
exit 0
