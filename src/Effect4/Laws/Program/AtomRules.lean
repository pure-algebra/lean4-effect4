import Effect4.Laws.Program.Typed
import Effect4.Laws.Auto.RuleSets

/-!
# `Effect4.Atoms` — the bank an atom's soundness proof asks for by name (tooling plan 2.2)

Six lemmas, every one of them an *inversion*: what an environment fitting a list of types must
be, and what a value of a scalar type must be. The twenty blocks of `nativeAtom_typed` applied
them by hand, over and over, and the twelve atoms L3 adds would have applied them twelve times
more. Registered here in the named bank `Effect4.Atoms`
(`Laws/Auto/RuleSets.lean`), they are asked for by a proof that wants them —
`aesop (rule_sets := [Effect4.Atoms])` — and paid for by no proof that does not.

`destruct` for the five that consume their hypothesis: once `Fits vs [a, b]` has told you
`vs = [x, y]`, the original fit says nothing further, and keeping it would let aesop re-derive
the same pair for ever. `forward` for `Fits.all_sub_string`, whose conclusion is a universal
statement about the members and whose hypothesis stays useful.

The bank's own control is `pair_inv_closes` below: it closes with the clause and, in the
negative fixture `Test/Program/AtomRulesRed.lean`, fails without it. The fixture omits the
clause rather than writing `-Effect4.Atoms`, which errors at the clause ("not active") instead
of at the goal and would therefore prove nothing about the bank.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

attribute [aesop safe destruct (rule_sets := [Effect4.Atoms])]
  Fits.singleton_inv
  Fits.pair_inv
  Val.hasTy_nat_inv
  Val.hasTy_bool_inv
  Val.hasTy_string_inv

attribute [aesop safe forward (rule_sets := [Effect4.Atoms])]
  Fits.all_sub_string

/-- The bank's control: two values fitting two `nat`s are two `Val.nat`s. Every step of it is
one of the six rules — `Fits.pair_inv` and twice `Val.hasTy_nat_inv` — and the same goal is
not closed by `aesop` without the clause (`Test/Program/AtomRulesRed.lean`). -/
theorem pair_inv_closes {vs : List Val} (h : Fits vs [Ty.nat, Ty.nat]) :
    ∃ m n : Nat, vs = [Val.nat m, Val.nat n] := by
  aesop (rule_sets := [Effect4.Atoms])

end Effect4.Program
