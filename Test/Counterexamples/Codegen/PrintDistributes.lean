import Effect4.Api.Codegen

/-!
# `E4-PRINT-CE-001`: the printer spells a pair of a union as a union of pairs (seeded)

The checker's order distributes a product over every union (`Ty.normalize`, DI-15), and the type
printer spells a type from its normal form (`Codegen.Types.ofTy`, `src/Effect4/Codegen/Types.lean`).
TypeScript distributes only at a literal discriminant. So the printed annotation of a checked
pair whose first item is `nat | string` is a union of two tuples, and tsgo 7.0.0-dev.20260629.1
refuses the value `readonly [string | number, boolean]` there (TS2375). The end-to-end run is the
topology note's probe (`docs/research/2026-10-11-topology-graphs/probes/EmitProbe.lean`, output
`probes/emit/tsgo.out`): the module emitted for `pairOf` below fails tsgo.

The witness here is the Lean half: the checker keeps the pair of a union as the answer type, and
the printer spells it exactly as it spells the union of pairs. The forced repair is the note's
repair A: distribute a product only at a literal or discriminant position, for every product-like
head (`docs/research/2026-10-11-topology-graphs/README.md`, §3.6).
-/

set_option autoImplicit false

namespace Test.Counterexamples.Codegen.PrintDistributes

open Effect4 Effect4.Program

def n (i : Nat) : Term := .lit (.nat i)
def tt : Term := .lit (.bool true)

/-- A value at `nat | string`, paired with `true`. -/
def pairOf : Eff NativeOp :=
  .bind (.select tt .bool (.succeed (n 1)) (.succeed (.lit (.str "s"))))
    (.succeed (.app "pair" (.cons (.var 0) (.cons tt .nil))))

def pairOfUnion : Ty := .prod (.union .nat .string) .bool
def unionOfPairs : Ty := .union (.prod .nat .bool) (.prod .string .bool)

-- The checker's answer is the pair of a union.
#guard (Api.typeOf pairOf []).map (·.answer) = some pairOfUnion

-- The attack: its normal form is the union of pairs, and the printer spells the two alike.
#guard pairOfUnion.normalize = unionOfPairs
#guard Codegen.Types.ofTy pairOfUnion = Codegen.Types.ofTy unionOfPairs

-- Control: the two types differ before normalization.
#guard pairOfUnion != unionOfPairs

end Test.Counterexamples.Codegen.PrintDistributes
