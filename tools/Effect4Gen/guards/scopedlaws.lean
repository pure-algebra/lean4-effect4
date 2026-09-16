/-! ## Acceptance guards for the generated scope-preservation lemmas

Appended verbatim by `--append tools/Effect4Gen/guards/scopedlaws.lean` into
`src/Effect4/Laws/Program/Authoring/Lifts.lean`. One program of each binding shape, its
scope discharged by `authoring_scoped` (the goal's head names the lemma), so a lemma that
went missing or changed shape fails here. -/

namespace Effect4.Program.AuthoringScopedGuards

open Effect4.Program Effect4.Program.Authoring

example : Src.Scoped (Op := Unit) (bind "r" (succeed (nat 0)) (succeed (var "r"))) := by
  authoring_scoped

example : Src.Scoped (Op := Unit)
    (acquireRelease "a" "x" (succeed (nat 0)) (succeed (app "pair" [var "a", var "x"]))) := by
  authoring_scoped

example : Src.Scoped (Op := Unit)
    (whileLoop "i" "a" (nat 0) (app "lt" [var "i", nat 3]) (var "a") (succeed (var "i"))) := by
  authoring_scoped

example : Src.Scoped (Op := Unit)
    (catchIf "e" (app "eq" [var "e", str "boom"]) (fail (str "boom")) (succeed (var "e"))) := by
  authoring_scoped

example : Src.Scoped (Op := Unit)
    (provideLayer (Layer.effectDiscard (succeed (nat 1))) false (succeed (nat 1))) := by
  authoring_scoped

example : Src.Scoped (Op := Unit) (withFiber (Action.raceAll [succeed (nat 1), succeed (nat 2)])) := by
  authoring_scoped

example : Src.Scoped (Op := Unit) (withFiber (Action.interruptAll (nat 0) (some (nat 1)))) := by
  authoring_scoped

example : Src.Scoped (Op := Unit)
    (failCause (Authoring.Cause.both (Authoring.Cause.fail (nat 1)) (Authoring.Cause.interrupt none))) := by
  authoring_scoped

example : LayerSrc.Scoped (Op := Unit) (Layer.mergeAll [Layer.effectDiscard (succeed (nat 1)), Layer.ref "Db"]) := by
  authoring_scoped

end Effect4.Program.AuthoringScopedGuards
