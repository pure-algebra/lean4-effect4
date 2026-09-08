#!/usr/bin/env bash
# gen-check.sh — the gate on the engine seam (build lane G).
#
# What it is: the four checks that say `ocaml/engine/api_engine.ml` is the file the extern
# table describes and that nothing it depends on has moved.  Run it in WSL from anywhere:
#
#   wsl -e bash -lc 'eval $(opam env --switch=effect4 --set-switch) && \
#     bash /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml/engine/tools/gen-check.sh'
#
# What it does NOT do: regenerate.  Lean runs on the Windows side under `.lake/LANE.lock`
# (one Lean process per machine, docs/research/2026-09-08-engine-brief.md §4), and the exact
# command is printed by --regen-command below and carried in api_engine.ml's own header.
#
# Checks:
#   C1  Risk R1 (engine-a1 §7): nothing removes a fiber from `RunMachine.fibers`.  The
#       carrier substitution is licensed by "every write is an append and no fiber is ever
#       removed"; a `filter`/`erase`/`removeAll`/`dropWhile` on that field would break it.
#   C2  The oracle is green and untouched: `dune build gen && dune build @gen/runtest`.
#       `ocaml/gen/api_gen.ml` is the in-process oracle and lane G never edits it.
#   C3  The seam compiles: `dune build engine`, and — the real statement — `api_engine.ml`
#       type-checks ON ITS OWN, with no carrier instance.  A functor body that type-checks
#       is the proof that the extern table is closed (engine-a1 §1.3).
#   C4  The checked-in generated file carries the CURRENT prelude, verbatim: an edit to
#       ocaml/engine/tools/api_engine_prelude.ml without a regeneration is caught here.
set -u

REPO=/mnt/c/Users/kokok/Dev/lean4-effect4
ENGINE="$REPO/ocaml/engine"
GEN="$ENGINE/api_engine.ml"
PRELUDE="$ENGINE/tools/api_engine_prelude.ml"
fail=0
note() { printf '%-4s %s\n' "$1" "$2"; }

if [ "${1:-}" = "--regen-command" ]; then
  sed -n '2p' "$GEN"
  exit 0
fi

# ---- C1  no fiber is ever removed --------------------------------------------------------
# `\b` keeps `m.fibers.filterMap` out: `completedExits` (Fibers.lean:1543) is a READ.
hits=$(grep -rEn 'fibers\.(filter|erase|removeAll|dropWhile|eraseP|removeIf)\b' "$REPO/src/Effect4/" || true)
if [ -n "$hits" ]; then
  note FAIL "C1 a fiber is removed from the fiber table — the ordering argument is dead:"
  printf '%s\n' "$hits"
  fail=1
else
  note ok "C1 no filter/erase/removeAll/dropWhile on RunMachine.fibers in src/Effect4/"
fi

# ---- C2  the oracle -----------------------------------------------------------------------
if (cd "$REPO/ocaml" && dune build gen && dune build @gen/runtest) >/tmp/geng-c2.log 2>&1; then
  note ok "C2 ocaml/gen builds and @gen/runtest passes (api_gen.ml is the oracle)"
else
  note FAIL "C2 ocaml/gen is not green:"; cat /tmp/geng-c2.log; fail=1
fi

# ---- C3  the seam -------------------------------------------------------------------------
if (cd "$REPO/ocaml" && dune build engine) >/tmp/geng-c3a.log 2>&1; then
  note ok "C3a dune build engine"
else
  note FAIL "C3a dune build engine:"; cat /tmp/geng-c3a.log; fail=1
fi

iso=$(mktemp -d)
cp "$GEN" "$iso/"
if (cd "$iso" && ocamlfind ocamlopt -c -w +a-4-9-40-41-42-44-45-70 api_engine.ml) >/tmp/geng-c3b.log 2>&1; then
  note ok "C3b api_engine.ml type-checks alone: the functor body needs no instance, so the"
  note ""  "     extern table is closed (every unconverted carrier site would be a type error)"
else
  note FAIL "C3b api_engine.ml does not type-check on its own — the extern table has a hole:"
  cat /tmp/geng-c3b.log; fail=1
fi
rm -rf "$iso"

# ---- C4  the prelude in the generated file is the current one ------------------------------
a=$(sed -n '/PRELUDE-BEGIN/,/PRELUDE-END/p' "$PRELUDE" | sed 's/^[[:space:]]*//')
b=$(sed -n '/PRELUDE-BEGIN/,/PRELUDE-END/p' "$GEN"     | sed 's/^[[:space:]]*//')
if [ -z "$b" ]; then
  note FAIL "C4 api_engine.ml carries no prelude block"; fail=1
elif [ "$a" = "$b" ]; then
  note ok "C4 the generated file carries the current prelude"
else
  note FAIL "C4 the prelude has changed since api_engine.ml was generated — regenerate:"
  printf '   %s\n' "$(sed -n '2p' "$GEN")"
  fail=1
fi

echo
if [ "$fail" = 0 ]; then echo "gen-check: PASS"; else echo "gen-check: FAIL"; fi
exit "$fail"
