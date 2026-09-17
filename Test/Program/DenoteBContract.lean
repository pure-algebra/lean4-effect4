import Effect4.Laws.Program.DenoteB
import Effect4.Api
import Test.Program.CompileContract

/-!
# DenoteB contract: the budgeted meaning of loops against the machine, pinned

The `select` and `iterate` packet §2.3. For the loop programs of
`Test/Program/CompileContract.lean`, `meaningB k p [] Stores.empty` at a budget that suffices
is what `Api.run p fuel` answers: the same exit and the same stores. Below that budget it is
`none`, with the stores written so far kept. These guards are the executable oracle of the
agreement the packet states existentially; they are one program at a time.

Every pin is a `#guard` over first-order values.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.DenoteBContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Test.Syntax.CompileContract (fuel pSucceed pBindSync pIterateCount pIterateAnswer
  pIterateRef pIterateBadResult pWhileLoop)

/-- The oracle: the machine finishes with the budgeted meaning's exit and stores. -/
def agreesAt (k : Nat) (p : NativeEff) : Bool :=
  let r := Api.run p fuel
  let m := meaningB k p [] Stores.empty
  r.outcome == Api.Outcome.finished && r.exit == m.1 && r.stores == m.2

/-! ## The budget: counting to three is three rounds and the round that fails the test -/

#guard (meaningB 0 pIterateCount [] Stores.empty).1 = none
#guard (meaningB 3 pIterateCount [] Stores.empty).1 = none
#guard (meaningB 4 pIterateCount [] Stores.empty).1 = some (Exit.success (Val.nat 3))
#guard (meaningB 5 pIterateCount [] Stores.empty).1 = some (Exit.success (Val.nat 3))
#guard (meaningB 40 pIterateCount [] Stores.empty).1 = some (Exit.success (Val.nat 3))

/-! ## Agreement with the machine at a sufficient budget -/

#guard agreesAt 4 pIterateCount
#guard agreesAt 2 pIterateAnswer
#guard agreesAt 8 pIterateRef
#guard agreesAt 1 pIterateBadResult

/-! ## An unfinished loop keeps the stores it wrote

`pIterateRef` makes a ref and increments it once a round. At budget 2 the loop has run two
rounds and is unfinished; the ref holds 2, not 0 and not 3. -/

#guard (meaningB 2 pIterateRef [] Stores.empty).1 = none
#guard (meaningB 2 pIterateRef [] Stores.empty).2.refs = [Val.nat 2]
#guard (meaningB 8 pIterateRef [] Stores.empty).2.refs = [Val.nat 3]

/-! ## A loop under every composite form of the fragment

The budgeted meaning descends through a decision, a handler, a reified exit, a finalizer and
another loop's body; at a sufficient budget each agrees with the machine, and an unfinished
inner loop leaves the whole unfinished. -/

/-- A loop in the arm a decision chooses. -/
def pLoopUnderSelect : NativeEff :=
  .select (.lit (.bool true)) .bool pIterateCount (.succeed (.lit (.nat 9)))

/-- A loop whose body fails on the third round, caught: the handler answers 5. -/
def pLoopCaught : NativeEff :=
  .catchCause
    (.iterate none (.lit (.nat 0)) (.lit (.bool true)) (.app "succ" (.cons (.var 0) .nil)) (.var 0)
      (.select (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 2)) .nil))) .bool
        (.succeed (.lit .unit)) (.fail (.lit (.nat 4)))))
    (.succeed (.lit (.nat 5)))

/-- A loop as the body of a finalizer's scope, and a loop in the finalizer. A raw program: the
finalizer's loop reads `var 0`, which under `onExit` is the reified exit, so it is ill-typed and
both sides go wrong alike (`Test/Program/LoopSoundContract.lean` pins that; the typed form is
`pLoopFinalizer` there). Agreement is stated on raw programs, so the guard stays. -/
def pLoopOnExit : NativeEff := .onExit pIterateCount pIterateAnswer

/-- A loop's exit as a value. -/
def pLoopExit : NativeEff := .exit pIterateCount

/-- Two rounds of an outer loop, each running the three-round inner loop. -/
def pLoopNested : NativeEff :=
  .iterate none (.lit (.nat 0)) (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 2)) .nil)))
    (.app "succ" (.cons (.var 0) .nil)) (.var 0)
    (.iterate none (.lit (.nat 0)) (.app "lt" (.cons (.var 1) (.cons (.lit (.nat 3)) .nil)))
      (.app "succ" (.cons (.var 1) .nil)) (.var 1) (.succeed (.lit .unit)))

#guard [pLoopUnderSelect, pLoopCaught, pLoopOnExit, pLoopExit, pLoopNested].all Looped
-- `CompileContract`'s loop was a `whileLoop`, outside the fragment; since that retired into
-- `iterate` it is the same program inside it.
#guard Looped pWhileLoop

#guard agreesAt 4 pLoopUnderSelect
#guard agreesAt 3 pLoopCaught
#guard agreesAt 4 pLoopOnExit
#guard agreesAt 4 pLoopExit
#guard agreesAt 4 pLoopNested
#guard (meaningB 3 pLoopCaught [] Stores.empty).1 = some (Exit.success (Val.nat 5))
#guard (meaningB 4 pLoopNested [] Stores.empty).1 = some (Exit.success (Val.nat 2))
-- One budget bounds every loop: the inner loop needs four rounds, so three leave the whole
-- unfinished although the outer loop needs only three.
#guard (meaningB 3 pLoopNested [] Stores.empty).1 = none
#guard (meaningB 3 pLoopUnderSelect [] Stores.empty).1 = none
#guard (meaningB 3 pLoopOnExit [] Stores.empty).1 = none

/-! ## The straight fragment is `denote`, at every budget -/

#guard (meaningB 0 pSucceed [] Stores.empty).1 = some (meaning pSucceed [] Stores.empty).1
#guard (meaningB 0 pBindSync [] Stores.empty) =
  ((some (meaning pBindSync [] Stores.empty).1), (meaning pBindSync [] Stores.empty).2)
#guard agreesAt 9 pWhileLoop

/-! ## The ceilings -/

/-- info: 'Effect4.Program.Denote.iter_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms iter_uniform
/-- info: 'Effect4.Program.Denote.denoteB_bind_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms denoteB_bind_none
/-- info: 'Effect4.Program.Denote.denoteB_straight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms denoteB_straight
/-- info: 'Effect4.Program.Denote.denoteB_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms denoteB_mono
/-- info: 'Effect4.Program.Denote.meaningB_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meaningB_unique

end Test.Program.DenoteBContract
