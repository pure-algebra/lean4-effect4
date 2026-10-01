import Effect4.Program.Authoring.Loops

/-! Seat J, step 2: the red side of the four B-9 controls, at the definitions as they stood at
the base `6b3f2c92` (copied verbatim under `old` names). Each guard is the history guard that
`Test/Program/AuthorContract.lean` now keeps under `#guard_msgs (error)`; here it must hold.
Run: `lake env lean -DwarningAsError=true docs/research/2026-10-01-landing/seat-J/probes/OldMintedSpellings.lean`. -/

namespace SeatJ.OldMintedSpellings

open Effect4 Effect4.Program Effect4.Program.Authoring

/-- `Sugar.bindWith` at the base. -/
def oldBindWith {Op : Type} (first : Src Op) (rest : TermSrc → Src Op) : Src Op := fun env p =>
  let x := "_" ++ toString env.names.length
  bind x first (rest (var x)) env p

/-- `Sugar.andThen` at the base. -/
def oldAndThen {Op : Type} (first rest : Src Op) : Src Op := bind "_" first rest

/-- `Loops.iterateWith` at the base. -/
def oldIterateWith {Op : Type} (initial : TermSrc) (spec : LoopSpec Op) : Src Op := fun env p =>
  let c := "_c" ++ toString env.names.length
  let a := "_a" ++ toString env.names.length
  iterate c a spec.cursorTy initial (spec.while_ (var c)) (spec.step (var c) (var a))
    (spec.result (var c)) (spec.body (var c)) env p

/-- `Forms.tapContinuation` at the base (generated). -/
def oldTapContinuation (answer : String) (effect : Src NativeOp) (continuation : Src NativeOp) :
    Src NativeOp :=
  Authoring.bind answer (effect) (Authoring.bind "_answer1" (continuation) (Authoring.succeed (Authoring.var answer)))

#guard elaborate (oldTapContinuation "_answer1" (succeed (nat 1)) (succeed (nat 2)))
  = .ok (.bind (.succeed (.lit (.nat 1))) (.bind (.succeed (.lit (.nat 2))) (.succeed (.var 1))))

#guard elaborate (bind "_" (succeed (nat 1)) (oldAndThen (succeed (nat 2)) (succeed (var "_")))
    : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 1))) (.bind (.succeed (.lit (.nat 2))) (.succeed (.var 1))))

#guard elaborate (bind "_1" (succeed (nat 1)) (oldBindWith (succeed (nat 2)) fun _ => succeed (var "_1"))
    : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 1))) (.bind (.succeed (.lit (.nat 2))) (.succeed (.var 1))))

#guard elaborate
    (bind "_c1" (succeed (bool false)) <|
      oldIterateWith (nat 0) { while_ := fun _ => var "_c1", body := fun _ => succeed unit,
                               step := fun c _ => c } : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.bool false)))
      (.iterate none (.lit (.nat 0)) (.var 1) (.var 1) (.var 1) (.succeed (.lit .unit))))

end SeatJ.OldMintedSpellings
