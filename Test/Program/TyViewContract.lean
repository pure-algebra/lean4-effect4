import Effect4.Laws.Program.TyView

/-! # The relational view's red control (tooling plan 1.4)

`src/Effect4/Laws/Program/TyView.lean` is generated from `Ty`'s constructors and the variance
table `tools/Effect4Gen/variances.json`, which `tools/Tools/Variances.lean` reads off rc.112.
Three things could go wrong and each has a control:

1. **A head with no declared variance, a variance list of the wrong length, or a head that is no
   constructor** — the generator refuses, by name, before emitting a line. Exercised by running
   `tools/Effect4Gen/View.lean --variances <a mutated copy>`; the three messages are in the
   seat's receipt. Not reproducible as a `#guard`, because the refusal is a generator exit.
2. **A variance that disagrees with `sub`'s arm** — the emitted file carries one probe pair per
   position per head, and the arm lemma's own proof fails. Also a generator-run control.
3. **An arm that compares its arguments OUT OF ORDER** — this is the one a probe could miss, so
   the fixture below shows it does not. Two relations over the same fixture carrier: one
   positional, one with the two arguments crossed. They agree on every probe that uses the same
   atom at both positions, and the **crossing probe** — distinct atoms at every position — tells
   them apart. That is why the generator emits a crossing probe for every head of arity two or
   more, and this module is what says the probe has teeth.

The view's own laws are exercised by the acceptance guards appended into the generated file
(`tools/Effect4Gen/guards/tyview.lean`).
-/

namespace Test.Program.TyViewContract

open Effect4.Program

/-! ## The out-of-order fixture

A two-atom carrier with one binary head. `lo` is below `hi` and nothing else is related, which
is the fixture's stand-in for `lit "a" ≤ string`. -/

private inductive Fix where
  | lo
  | hi
  | pair (left right : Fix)
deriving DecidableEq, Repr

/-- The atoms, as `sub` relates `lit "a"` and `string`. -/
private def atom : Fix → Fix → Bool
  | .lo, .hi => true
  | a, b => a == b

/-- The arm as the generator assumes it: argument 0 against argument 0, argument 1 against
argument 1. -/
private def positional : Fix → Fix → Bool
  | .pair a1 a2, .pair b1 b2 => positional a1 b1 && positional a2 b2
  | a, b => atom a b

/-- The same arm with the two arguments **crossed**: argument 0 against argument 1. A generator
that emitted `args = [(.co, left), (.co, right)]` for this relation would be lying, and the
`sub_eq_args` law it emitted would be false. -/
private def crossed : Fix → Fix → Bool
  | .pair a1 a2, .pair b1 b2 => crossed a1 b2 && crossed a2 b1
  | a, b => atom a b

/-! ### The variance probe alone does NOT tell them apart

The probe puts the interesting pair at one position and the SAME atom at every other position,
so a crossed arm still compares that atom with itself and answers the same. -/

#guard positional (.pair .lo .lo) (.pair .hi .lo) = crossed (.pair .lo .lo) (.pair .hi .lo)
#guard positional (.pair .hi .lo) (.pair .lo .lo) = crossed (.pair .hi .lo) (.pair .lo .lo)
#guard positional (.pair .lo .lo) (.pair .lo .hi) = crossed (.pair .lo .lo) (.pair .lo .hi)

/-! ### The crossing probe does

Distinct atoms at every position: positional compares `lo` with `hi` and `hi` with `lo`, so it
answers `false`; crossed compares `lo` with `lo` and `hi` with `hi`, so it answers `true`. This
is exactly the shape the generator emits — `#guard !Ty.sub (.prod .nat .bool) (.prod .bool .unit)`
— for every head of arity two or more. -/

#guard !positional (.pair .lo .hi) (.pair .hi .lo)
#guard crossed (.pair .lo .hi) (.pair .hi .lo)
#guard positional (.pair .lo .hi) (.pair .hi .lo) != crossed (.pair .lo .hi) (.pair .hi .lo)

/-! ## The real thing, at the same shape

The crossing probes the generator emitted into `TyView.lean` for `Ty`'s binary heads, restated
here so this module fails if the emitted ones are ever weakened. Each is `false` because `sub`
compares position 0 with position 0. -/

#guard !Ty.sub (.prod .nat .bool) (.prod .bool .unit)
#guard !Ty.sub (.except .nat .bool) (.except .bool .unit)
#guard !Ty.sub (.exitOf .nat .bool) (.exitOf .bool .unit)
#guard !Ty.sub (.fiberOf .nat .bool) (.fiberOf .bool .unit)
#guard !Ty.sub (.deferredOf .nat .bool) (.deferredOf .bool .unit)

/-! ## The law, and the vocabulary it gives the proofs -/

#check @Ty.sub_eq_args
#check @Ty.sub_eq_argsBelow_of_sameHead
#check @Ty.sub_eq_false_of_not_sameHead
#check @Ty.sameHead_refl
#check @Ty.sameHead_symm
#check @Ty.sameHead_trans
#check @Ty.args_congr
#check @Ty.sizeOf_args
#check @Ty.eq_of_sameHead
#check @Ty.argsBelow_refl
#check @Ty.Variance.holds_trans
#check @Ty.Variance.holds_antisymm
#check @AdmitsSub

/-- The law as a proof obligation, so this module fails if its statement moves. -/
example (a b : Ty) (ha : Ty.isMember a = true) (hb : Ty.isMember b = true)
    (hlit : Ty.litRule a b = false) (htop : Ty.topRule a b = false) :
    Ty.sub a b = (Ty.sameHead a b && Ty.argsBelow Ty.sub a b) :=
  Ty.sub_eq_args a b ha hb hlit htop

end Test.Program.TyViewContract
