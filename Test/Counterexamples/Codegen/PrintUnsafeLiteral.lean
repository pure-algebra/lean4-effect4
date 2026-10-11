import Effect4.Api

/-!
# `E4-PRINT-CE-002`: a natural literal outside the profile prints as another number (seeded)

The checker types a natural literal at `nat` whatever its size, and the term printer writes it in
decimal (`printLit`, `src/Effect4/Codegen/PrintLeaf.lean`). JavaScript reads a decimal integer
literal as the nearest binary64. Above `Number.MAX_SAFE_INTEGER` that is another number: under bun
1.4.2, `9007199254740993` reads as `9007199254740992` (2026-10-11, this session). So the printed
program computes with a value the model does not hold, and nothing refuses it.

DI-56 rules that a face refuses outside its profile, and the profile's bound is `2^53 - 1`
(`rc112.natBound`, `src/Effect4/Program/Profile.lean`). Lean's own round trip holds
(`readLiteral_print`): Lean reads the decimal exactly. The defect is the target's reading.

The forced repair: the module printer refuses a natural literal above the profile's bound, with a
refusal that names the literal.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Codegen.PrintUnsafeLiteral

open Effect4 Effect4.Program

/-- The least natural that JavaScript cannot read back. -/
def beyond : Nat := 2 ^ 53 + 1

/-- A program that answers it. -/
def answersUnsafe : Eff NativeOp := .succeed (.lit (.nat beyond))

-- The checker admits the program at `nat`.
#guard (Api.typeOf answersUnsafe []).map (·.answer) = some .nat

-- The attack: the literal is outside the profile, and the printer writes its decimal anyway.
#guard rc112.natBound < beyond
#guard match printLit (.nat beyond) with
  | .int value => value == 9007199254740993
  | _ => false

-- Control: the bound itself is inside the profile and prints the same way; JavaScript reads it
-- exactly.
#guard match printLit (.nat rc112.natBound) with
  | .int value => value == 9007199254740991
  | _ => false

end Test.Counterexamples.Codegen.PrintUnsafeLiteral
