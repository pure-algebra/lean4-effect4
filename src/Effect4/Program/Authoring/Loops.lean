import Effect4.Program.Authoring.Sugar

/-!
# Program.Authoring.Loops — loops an author writes, over the one loop

`iterate` is the language's only recursion: a cursor, a pure test, an effectful body, a pure
step over the cursor and the body's answer, a pure result. Every definition here is a Lean
function that authors one `iterate` through the generated lift. None adds a constructor, an atom,
a wire tag or a printed shape, so there is one owner of what a loop means and prints
(`docs/research/2026-09-17-loop-sugar-and-list-elimination.md`; the compiled probe beside it).

Binders are Lean functions over names minted from the scope's length, as `bindWith` does. The
cursor carries no annotation unless the author states one (DI-91): its type is its initial
value's.
-/

namespace Effect4.Program.Authoring

open Effect4.Program

/-- The parts of a loop over a cursor, in the order rc.112's `Effect.whileLoop` names them
(`{ while, body, step }`, `vendor/effect-4.0.0-rc.112/src/Effect.ts:1282`), then the result.
`result` defaults to the cursor. `cursorTy` is stated only for a cursor wider than its initial
value (an accumulator that starts empty). -/
structure LoopSpec (Op : Type) where
  while_ : TermSrc → TermSrc
  body : TermSrc → Src Op
  step : TermSrc → TermSrc → TermSrc
  result : TermSrc → TermSrc := id
  cursorTy : Option Ty := none

/-- `iterateWith initial spec`: `iterate` with its two binders as Lean functions. -/
def iterateWith {Op : Type} (initial : TermSrc) (spec : LoopSpec Op) : Src Op := fun env p =>
  let c := "_c" ++ toString env.names.length
  let a := "_a" ++ toString env.names.length
  iterate c a spec.cursorTy initial (spec.while_ (var c)) (spec.step (var c) (var a))
    (spec.result (var c)) (spec.body (var c)) env p

/-- `forRange lo hi body`: `body i` for `lo ≤ i < hi`, in order. Answers the final counter. -/
def forRange {Op : Type} (lo hi : TermSrc) (body : TermSrc → Src Op) : Src Op :=
  iterateWith lo
    { while_ := fun i => app "lt" [i, hi], body := body, step := fun i _ => app "succ" [i] }

/-- `foldRange lo hi zero f`: a fold over `lo ≤ i < hi`. The cursor is the pair of the counter
and the accumulator, taken apart for the author; `f i acc` answers the next accumulator. Answers
the final accumulator. -/
def foldRange {Op : Type} (lo hi zero : TermSrc) (f : TermSrc → TermSrc → Src Op) : Src Op :=
  iterateWith (app "pair" [lo, zero])
    { while_ := fun c => app "lt" [app "fst" [c], hi]
      body := fun c => f (app "fst" [c]) (app "snd" [c])
      step := fun c acc => app "pair" [app "succ" [app "fst" [c]], acc]
      result := fun c => app "snd" [c] }

/-- `repeatWhile cond body`: a loop whose condition is an effect (read a `Ref`, poll a queue).
`iterate`'s test is a pure term over the cursor, so the cursor is the condition's last answer:
`cond` runs once before the loop and again at the end of every round. Answers `unit`. -/
def repeatWhile {Op : Type} (cond body : Src Op) : Src Op :=
  bindWith cond fun first =>
    iterateWith first
      { while_ := id, body := fun _ => andThen body cond, step := fun _ again => again,
        result := fun _ => unit }

end Effect4.Program.Authoring
