import Effect4.Api
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Loops

/-!
# Loop sugar contract — the authored loops elaborate, type and run

`src/Effect4/Program/Authoring/Loops.lean` authors `iterate` four ways. This battery pins, for
each, the positional tree it elaborates to (one, in full, so the minted binders are visible), that
the tree types under the native signature with no annotation (DI-91), what the machine answers,
and the printed image of the plain counting loop. The universal statement is
`Laws/Program/Authoring/Loops.lean`: each form preserves `Src.Scoped`.
-/

set_option autoImplicit false

namespace Test.Program.LoopSugarContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

def answerOf (src : Src NativeOp) : Option ExitV :=
  match elaborate src with
  | .ok e => (Api.run e 400).exit
  | .error _ => none

def typed (src : Src NativeOp) : Bool :=
  match elaborate src with
  | .ok e => (Api.typeOf e).isSome
  | .error _ => false

/-! ## `iterateWith`: the cursor is the answer by default, and carries no annotation -/

def count3 : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, nat 3], body := fun _ => succeed unit,
      step := fun i _ => app "succ" [i] }

#guard elaborate count3
  = .ok (.iterate none (.lit (.nat 0))
          (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
          (.app "succ" (.cons (.var 0) .nil))
          (.var 0)
          (.succeed (.lit .unit)))
#guard typed count3
#guard answerOf count3 = some (Exit.success (Store.Val.nat 3))

-- a stated, wider cursor is the author's to give
#guard elaborate (iterateWith (nat 0)
    { while_ := fun _ => bool false, body := fun _ => succeed unit, step := fun i _ => i,
      cursorTy := some (.union .nat .string) } : Src NativeOp)
  = .ok (.iterate (some (.union .nat .string)) (.lit (.nat 0)) (.lit (.bool false)) (.var 0)
          (.var 0) (.succeed (.lit .unit)))

-- the one printed loop shape, with no annotation
#guard (match elaborate count3 with
    | .ok e => (Api.print e).toOption.map (TypeScript.Render.expr TypeScript.house0 0)
    | .error _ => none)
  = some ("Effect.suspend(() => {\n  let a0 = 0\n  return Effect.map(Effect.whileLoop({\n"
      ++ "    while: () => lt(a0, 3),\n    body: () => Effect.succeed(undefined),\n"
      ++ "    step: (a1) => {\n      a0 = succ(a0)\n    },\n  }), () => a0)\n})")

/-! ## `forRange`: a `Ref` bumped five times -/

def bump5 : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun r =>
    andThen (forRange (nat 0) (nat 5) fun _ => Ref.update .incr r) (Ref.get r)

#guard typed bump5
#guard answerOf bump5 = some (Exit.success (Store.Val.nat 5))

/-! ## `foldRange`: the sum of 0..4, with a pair cursor the author never sees -/

def sum5 : Src NativeOp :=
  foldRange (nat 0) (nat 5) (nat 0) fun i acc => succeed (app "add" [i, acc])

#guard typed sum5
#guard answerOf sum5 = some (Exit.success (Store.Val.nat 10))
-- an empty range answers the start
#guard answerOf (foldRange (nat 4) (nat 4) (nat 7) fun i acc => succeed (app "add" [i, acc]))
  = some (Exit.success (Store.Val.nat 7))

/-! ## `repeatWhile`: the condition is an effect -/

def untilThree : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun r =>
    andThen
      (repeatWhile (bindWith (Ref.get r) fun v => succeed (app "lt" [v, nat 3]))
        (Ref.update .incr r))
      (Ref.get r)

#guard typed untilThree
#guard answerOf untilThree = some (Exit.success (Store.Val.nat 3))
-- a condition false at once runs the body no times
#guard answerOf (bindWith (Ref.make (nat 9)) fun r =>
    andThen (repeatWhile (succeed (bool false)) (Ref.update .incr r)) (Ref.get r))
  = some (Exit.success (Store.Val.nat 9))

/-! ## Scope: by the laws, not by running -/

theorem count3_closed {e : Eff NativeOp} (h : elaborate count3 = .ok e) :
    Eff.scopedAt 0 e = true :=
  elaborate_scoped
    (iterateWith_scoped (nat_scoped 0)
      (fun _ hc => app_scoped "lt"
        (TermSrc.Scoped_cons hc (TermSrc.Scoped_cons (nat_scoped 3) TermSrc.Scoped_nil)))
      (fun _ _ => succeed_scoped unit_scoped)
      (fun _ _ hc _ => app_scoped "succ" (TermSrc.Scoped_cons hc TermSrc.Scoped_nil))
      (fun _ hc => hc)) h

#print axioms iterateWith_scoped
#print axioms forRange_scoped
#print axioms foldRange_scoped
#print axioms repeatWhile_scoped
#print axioms count3_closed

end Test.Program.LoopSugarContract
