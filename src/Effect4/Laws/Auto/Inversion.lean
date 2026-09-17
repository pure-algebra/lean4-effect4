import Aesop

/-!
# Laws.Auto.Inversion — what a successful computation says of its parts

Aesop (`https://github.com/leanprover-community/aesop`) is the proof search of the law graph,
used as its README describes: lemmas are registered as rules in its DEFAULT rule set, and a
proof says `aesop`, adding per call what belongs to that proof alone (`aesop (add safe forward
[ih1, ih2])` for induction hypotheses, which the README asks to be introduced by hand; a rule
that creates metavariables, such as a transitivity, per call only, as it advises).

This module registers the facts a proof about a reader or a checker begins with: what a
SUCCESSFUL `Except` or `Option` computation says of its parts. They are stated generically
(nothing here mentions a type of the project) and added as normalisation simp rules
(`@[aesop norm simp]`), so they act inside Aesop and leave every existing `simp` call alone.

The axiom ceiling is kept by the axiom gate, as for every other proof: a search that reaches past
`[propext, Quot.sound]` fails the gate like a hand proof would. Only modules under
`src/Effect4/Laws/**` and the batteries import Aesop; the core root does not.
-/

set_option autoImplicit false

namespace Effect4.Laws.Auto

variable {ε ε' α β : Type}

theorem bind_eq_ok {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp only [bind, Except.bind, reduceCtorEq, false_and, exists_false]
  | ok a => simp only [bind, Except.bind, Except.ok.injEq, exists_eq_left']

theorem map_eq_ok {m : Except ε α} {f : α → β} {b : β} :
    m.map f = .ok b ↔ ∃ a, m = .ok a ∧ f a = b := by
  cases m with
  | error e => simp only [Except.map, reduceCtorEq, false_and, exists_false]
  | ok a => simp only [Except.map, Except.ok.injEq, exists_eq_left']

theorem mapError_eq_ok {f : ε → ε'} {m : Except ε α} {a : α} :
    m.mapError f = .ok a ↔ m = .ok a := by
  cases m with
  | error e => simp only [Except.mapError, reduceCtorEq]
  | ok b =>
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl

theorem toOption_eq_some {m : Except ε α} {a : α} : m.toOption = some a ↔ m = .ok a := by
  cases m with
  | error e => simp only [Except.toOption, reduceCtorEq]
  | ok b => simp only [Except.toOption, Option.some.injEq, Except.ok.injEq]

theorem getD_error_eq_ok {o : Option (Except ε α)} {err : ε} {a : α} :
    o.getD (.error err) = .ok a ↔ o = some (.ok a) := by
  cases o with
  | none => simp only [Option.getD_none, reduceCtorEq]
  | some r => simp only [Option.getD_some, Option.some.injEq]

/-! A refusal is not a success, and nothing is not something: what closes a branch that the
computation did not take. -/

theorem error_ne_ok {e : ε} {a : α} : (Except.error e : Except ε α) = .ok a ↔ False := by
  simp only [reduceCtorEq]

theorem ok_ne_error {e : ε} {a : α} : (Except.ok a : Except ε α) = .error e ↔ False := by
  simp only [reduceCtorEq]

theorem none_ne_some {a : α} : (none : Option α) = some a ↔ False := by
  simp only [reduceCtorEq]

theorem some_ne_none {a : α} : some a = (none : Option α) ↔ False := by
  simp only [reduceCtorEq]

attribute [aesop norm simp]
  error_ne_ok ok_ne_error none_ne_some some_ne_none
  bind_eq_ok map_eq_ok mapError_eq_ok toOption_eq_some getD_error_eq_ok
  Option.map_eq_some_iff Option.bind_eq_some_iff
  Option.some.injEq Except.ok.injEq Prod.mk.injEq

end Effect4.Laws.Auto
