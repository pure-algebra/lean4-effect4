import Effect4.Api

/-!
# `E4-RUN-CE-047`: exact reference multiplication and repaired target refusal

Row 321 marks every growing natural operation with `Profile.grow`, so that a face can refuse a
result above the profile's bound (DI-56): `succ`, `add`, `plus` and `minus`
(`src/Effect4/Machine/Integers.lean`). The original atom `mul` lacked that mark. Lean's evaluator answers the
exact product (`NativeAtom.eval`, `src/Effect4/Machine/Term.lean`), and the original two faces answered
otherwise, with no refusal:

- the TypeScript prelude is `(a: number, b: number): number => a * b`, which rounds above 2^53:
  under bun 1.4.2, `(2^27 + 1) * (2^27 + 1)` is `18014398777917440` (2026-10-11, this session);
- the OCaml route lowers it to `lcnf_nat_mul`, which saturates at `max_int` above 2^62
  (`ocaml/gen/api_gen.ml`).

Row 309 says that no multiplication enters, yet the name resolves, and
`Test/Dogfood/P1HttpCache.lean` uses it. The repair marks `mul` with `Profile.scale`; both targets refuse products outside the profile.
`docs/research/2026-10-11-machine-models/codex/type-profile/TargetReceipt.md` records the finite checks.
The exact reference answer remains unchanged.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Machine.Semantics.MulOutsideProfile

open Effect4 Effect4.Program

def a : Nat := 2 ^ 27 + 1

-- The name resolves to the atom.
#guard NativeAtom.ofName? "mul" = some .mul

-- The attack: both arguments are inside the profile, and Lean answers the exact product above it.
#guard a ≤ rc112.natBound
#guard NativeAtom.eval .mul [.nat a, .nat a] = some (.nat 18014398777917441)
#guard rc112.natBound < 18014398777917441

-- The repaired prelude checks its result before exposing it.
#guard (NativeAtom.row .mul).prelude = "(a: number, b: number): number => inProfile(a * b)"
#guard NativeAtom.eval .mul [.nat a, .nat a] = some (.nat (Profile.scale a a))

-- Control: `add` goes through the profile's mark, so its faces can refuse.
#guard NativeAtom.eval .add [.nat a, .nat a] = some (.nat (Profile.grow a a))

end Test.Counterexamples.Machine.Semantics.MulOutsideProfile
