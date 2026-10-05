import OCaml5.Eff.Goldens
import Effect4.Api

/-! Measurement for seat T3a's design note (phase 1): the OCaml golden programs
(`OCaml5.Eff.Corpus.corpus`, the source of `ocaml/eff/goldens/`). The same two questions as
`CorpusMoves.lean`: which programs are refused at a row T3a templates, with a request the template
accepts; which programs name a native handle spelling in an annotation or their checked type; and
which perform `Deferred.make`, whose bytes a retirement moves. Replay:
`lake env lean docs/research/2026-10-04-seat-T3a/GoldenMoves.lean` under the shared lock. -/

open Effect4 Effect4.Program

def G.spellings : List String := ["Ref.Ref<number>", "Deferred.Deferred<number, number>"]

def G.mentions (t : Ty) : Bool :=
  (Formation.nodes t).any fun
    | .handle target | .app target _ => G.spellings.contains target
    | _ => false

/-- Whether a program performs `Deferred.make`, read off its canonical bytes' operations. -/
def G.makesDeferred (p : Eff NativeOp) : Bool :=
  (OCaml5.Eff.effV p).names.contains ``NativeOp.deferredMake

#eval show IO Unit from do
  for (name, p) in OCaml5.Eff.Corpus.corpus do
    let refusal := match Api.explain p with
      | some ⟨_, .requestNotSubtype row request _⟩ => s!"requestNotSubtype {row} at {request.render}"
      | some r => s!"{r.reason.head}"
      | none => "-"
    let typed := match Api.typeOf p [] with
      | some t => G.mentions t.answer || G.mentions t.error
      | none => false
    let annotated := (Formation.programAnnotations p).any fun (_, t) => G.mentions t
    if typed || annotated || G.makesDeferred p || refusal.startsWith "requestNotSubtype" then
      IO.println s!"{name}\ttype names a spelling {typed}\tannotation {annotated}\tDeferred.make {G.makesDeferred p}\trefusal {refusal}"
