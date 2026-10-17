import Effect4.Api.Codegen

/-!
# `E4-PRINT-CE-002`: a natural literal outside the profile prints as another number (repaired)

The checker types a natural literal at `nat` whatever its size, and the term printer writes it in
decimal (`printLit`, `src/Effect4/Codegen/PrintLeaf.lean`). JavaScript reads a decimal integer
literal as the nearest binary64. Above `Number.MAX_SAFE_INTEGER` that is another number: under bun
1.4.2, `9007199254740993` reads as `9007199254740992` (2026-10-11, this session). So the printed
program computes with a value the model does not hold, and nothing refuses it.

DI-56 rules that a face refuses outside its profile, and the profile's bound is `2^53 - 1`
(`rc112.natBound`, `src/Effect4/Program/Profile.lean`). Lean's own round trip holds
(`readLiteral_print`): Lean reads the decimal exactly. The defect is the target's reading.

The repair (2026-10-11): the module emission refuses a natural literal above the profile's bound
before it prints, with `EmissionRefusal.outsideProfile` naming the literal, and its certificate
records the bound (`ModuleEmission.inProfile`, `src/Effect4/Codegen/Checked.lean`). The term
printer stays total, so its round trip is unchanged. The reading boundary refuses the same
literal (`SurfaceRefusal.outsideProfile`, `ModuleReading.inProfile`, `src/Effect4/Codegen/Admit.lean`).
-/

set_option autoImplicit false

namespace Test.Counterexamples.Codegen.PrintUnsafeLiteral

open Effect4 Effect4.Program

/-- The least natural that JavaScript cannot read back. -/
def beyond : Nat := 2 ^ 53 + 1

/-- A program that answers it. -/
def answersUnsafe : Eff NativeOp := .succeed (.lit (.nat beyond))

-- The checker admits the program at `nat`.
#guard (Api.typeOf answersUnsafe).map (·.answer) = some .nat

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

-- The repair: the emission refuses the program, naming the literal.
#guard match Codegen.emitModule "answersUnsafe" answersUnsafe with
  | .error (.outsideProfile value) => value == beyond
  | _ => false

-- Control: the bound itself emits.
#guard match Codegen.emitModule "answersBound" (.succeed (.lit (.nat rc112.natBound))) with
  | .ok _ => true
  | .error _ => false

-- The reading boundary refuses the same program's text, written by the raw printer, which
-- checks no profile.
#guard match Api.typeOf answersUnsafe with
  | none => false
  | some ty => match printEntry [] (nativeSignature []) "main" ty answersUnsafe with
    | .error _ => false
    | .ok decls =>
      match Codegen.admitModule "main" { header := [], imports := [], decls := decls.map .const }
          [] Codegen.effectOrigins [.named ["Effect"] "effect"] with
      | .error (.outsideProfile value) => value == beyond
      | _ => false

-- Control: the bound's text is admitted.
#guard match Codegen.emitModule "main" (.succeed (.lit (.nat rc112.natBound))) with
  | .error _ => false
  | .ok e => match Codegen.admitModule "main" e.module [] Codegen.effectOrigins
      [.named ["Effect"] "effect"] with
    | .ok _ => true
    | .error _ => false

end Test.Counterexamples.Codegen.PrintUnsafeLiteral
