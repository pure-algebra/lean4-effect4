import OCaml5.Eff.Goldens
import Effect4.Store.Domain.ProgramWire
import Effect4.Api

/-! Measurement for seat T3b's design note (phase 1), at `5949fe4b`, after seat T3a's
`GoldenMoves.lean`. The OCaml golden programs (`OCaml5.Eff.Corpus.corpus`, the source of
`ocaml/eff/goldens/` and `ocaml/goldens/eff/`) and the wire corpus (`Wire.Corpus.all`): which
perform one of the eight read-modify-write rows, whose bytes the retirement at tags 5 to 12 moves,
and with which function names; and whether each prints. Replay from the worktree root under the
shared lock: `lake env lean -M8192 docs/research/2026-10-04-seat-T3b/GoldenMoves.lean`
(`lake build OCaml5.Eff.Goldens` first). -/

open Effect4 Effect4.Program

def G.rows : List Lean.Name :=
  [``NativeOp.refUpdate, ``NativeOp.refGetAndUpdate, ``NativeOp.refUpdateAndGet,
   ``NativeOp.refUpdateSome, ``NativeOp.refGetAndUpdateSome, ``NativeOp.refUpdateSomeAndGet,
   ``NativeOp.refModify, ``NativeOp.refModifySome]

def G.rmw (p : Eff NativeOp) : List Lean.Name :=
  ((OCaml5.Eff.effV p).names.filter fun n => G.rows.contains n)

#eval show IO Unit from do
  IO.println "## OCaml golden programs"
  for (name, p) in OCaml5.Eff.Corpus.corpus do
    let uses := G.rmw p
    unless uses.isEmpty do
      IO.println s!"{name}\trows {uses.eraseDups}\tprints {(Api.print p).isOk}\twellTyped {Api.wellTyped p}"
  IO.println "## The wire corpus"
  for (name, p) in Wire.Corpus.all do
    let uses := G.rmw p
    unless uses.isEmpty do
      IO.println s!"{name}\trows {uses.eraseDups}\tprints {(Api.print p).isOk}\twellTyped {Api.wellTyped p}"
