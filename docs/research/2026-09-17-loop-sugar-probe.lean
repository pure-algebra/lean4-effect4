import Effect4.Api
import Effect4.Program.Authoring.Sugar

/-! Probe: loop sugar over `iterate`, authoring only (no constructor, no atom).

`iterate` is one engine: a cursor, a pure test, an effectful body, a pure step, a pure result.
Everything here is a Lean function that authors an `iterate`. -/

set_option autoImplicit false

namespace LoopSugar
open Effect4 Effect4.Program Effect4.Program.Authoring

/-! ## 1. `iterateWith`: binders as Lean functions, Effect's key order, defaults -/

/-- The parts of a loop over a cursor, in rc.112's `{ while, body, step }` order, with the
result last. `result` defaults to the cursor; `cursorTy` to none (the initial value's type). -/
structure LoopSpec (Op : Type) where
  while_ : TermSrc → TermSrc
  body : TermSrc → Src Op
  step : TermSrc → TermSrc → TermSrc
  result : TermSrc → TermSrc := id
  cursorTy : Option Ty := none

/-- `iterateWith initial spec`: names are minted from the scope's length, as `bindWith` does. -/
def iterateWith {Op : Type} (initial : TermSrc) (spec : LoopSpec Op) : Src Op := fun env p =>
  let c := "_c" ++ toString env.names.length
  let a := "_a" ++ toString env.names.length
  iterate c a spec.cursorTy initial (spec.while_ (var c)) (spec.step (var c) (var a))
    (spec.result (var c)) (spec.body (var c)) env p

/-! ## 2. Counting: `forRange`, the loop most authors mean -/

/-- `forRange lo hi body`: `body i` for `lo ≤ i < hi`; answers `hi`'s final cursor. -/
def forRange {Op : Type} (lo hi : TermSrc) (body : TermSrc → Src Op) : Src Op :=
  iterateWith lo
    { while_ := fun i => app "lt" [i, hi], body := body, step := fun i _ => app "succ" [i] }

/-! ## 3. A while loop whose condition is an EFFECT

`iterate`'s test is a pure term over the cursor. An effectful condition (read a `Ref`, poll a
queue) is the cursor itself: evaluate it once before the loop, and again at the end of each
round. The cursor is the last answer of the condition. -/
def whileEff {Op : Type} (cond body : Src Op) : Src Op :=
  bindWith cond fun first =>
    iterateWith first
      { while_ := id, body := fun _ => andThen body cond, step := fun _ again => again,
        result := fun _ => unit }

/-! ## 4. An accumulator beside the cursor: a pair cursor, destructured for the author -/

/-- `foldRange lo hi zero f`: the cursor is `(i, acc)`; `f i acc` is an effect answering the
next accumulator. Answers the final accumulator. A fold over a range, by one `iterate`. -/
def foldRange {Op : Type} (lo hi zero : TermSrc) (f : TermSrc → TermSrc → Src Op) : Src Op :=
  iterateWith (app "pair" [lo, zero])
    { while_ := fun c => app "lt" [app "fst" [c], hi]
      body := fun c => f (app "fst" [c]) (app "snd" [c])
      step := fun c acc => app "pair" [app "succ" [app "fst" [c]], acc]
      result := fun c => app "snd" [c] }

/-! ## 5. A fold over a LIST, with nothing added to the language

A cons list as tagged pairs (`tagged "cons" (pair head tail)`, `tagged "nil" unit`) is taken
apart by the tag decision and `tagIs`. The cursor is `(acc, rest)`. This is the catamorphism
written with the one loop engine: `out` is the tag decision, the recursion is `iterate`. -/
def reduceT {Op : Type} (xs zero : TermSrc) (f : TermSrc → TermSrc → Src Op) : Src Op :=
  iterateWith (app "pair" [zero, xs])
    { while_ := fun c => app "tagIs" [str "cons", app "snd" [c]]
      body := fun c => fun env p =>
        let cell := "_cell" ++ toString env.names.length
        let rest := "_rest" ++ toString env.names.length
        selectTag cell rest (app "snd" [c]) "cons"
          (bindWith (f (app "fst" [c]) (app "fst" [var cell])) fun acc =>
            succeed (app "pair" [acc, app "snd" [var cell]]))
          (succeed c) env p
      step := fun _ next => next
      result := fun c => app "fst" [c] }

/-! ## Receipts -/

def run? (src : Src NativeOp) : Option Effect4.Machine.ExitV :=
  match elaborate src with
  | .ok e => (Api.run e 400).exit
  | .error _ => none

def typed? (src : Src NativeOp) : Bool :=
  match elaborate src with
  | .ok e => (Api.typeOf e).isSome
  | .error _ => false

-- count to 3: the cursor is the answer
def count3 : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, nat 3], body := fun _ => succeed unit,
      step := fun i _ => app "succ" [i] }
#eval typed? count3
#eval ("count3 answers 3:", decide (run? count3 = some (Exit.success (Effect4.Store.Val.nat 3))))

-- forRange bumping a Ref five times, then reading it
def bump5 : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun r =>
    andThen (forRange (nat 0) (nat 5) fun _ => Ref.update .incr r) (Ref.get r)
#eval typed? bump5
#eval ("bump5 answers 5:", decide (run? bump5 = some (Exit.success (Effect4.Store.Val.nat 5))))

-- sum of 0..4 with a pair cursor: 10
def sum5 : Src NativeOp :=
  foldRange (nat 0) (nat 5) (nat 0) fun i acc => succeed (app "add" [i, acc])
#eval typed? sum5
#eval ("sum5 answers 10:", decide (run? sum5 = some (Exit.success (Effect4.Store.Val.nat 10))))

-- an effectful condition: loop while the Ref is below 3, bumping it; then read it: 3
def untilThree : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun r =>
    andThen
      (whileEff (bindWith (Ref.get r) fun v => succeed (app "lt" [v, nat 3])) (Ref.update .incr r))
      (Ref.get r)
#eval typed? untilThree
#eval ("untilThree answers 3:", decide (run? untilThree = some (Exit.success (Effect4.Store.Val.nat 3))))

-- a fold over a tagged cons list [1, 2, 3], authored as a literal: 6
def tcons (h t : TermSrc) : TermSrc := app "pair" [str "cons", app "pair" [h, t]]
def tnil : TermSrc := app "pair" [str "nil", unit]
def sumList : Src NativeOp :=
  reduceT (tcons (nat 1) (tcons (nat 2) (tcons (nat 3) tnil))) (nat 0)
    fun acc x => succeed (app "add" [acc, x])
#eval typed? sumList
#eval ("sumList answers 6:", decide (run? sumList = some (Exit.success (Effect4.Store.Val.nat 6))))

-- what the counting loop prints as
#eval match elaborate count3 with
  | .ok e => (Api.print e).toOption.map (TypeScript.Render.expr TypeScript.house0 0)
  | .error _ => none

end LoopSugar
