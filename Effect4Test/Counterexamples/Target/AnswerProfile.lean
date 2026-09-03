/-
Executable witnesses for `E4-TARGET-CE-022` and `E4-TARGET-CE-023`
(`test/counterexamples/REGISTER.md`, `test/counterexamples/target/ATTACKS.md`).
Contract packet: `test/contracts/answer-profile.contract.md`.

Doc comments cannot precede `effect_signature`, `effect_atoms` or `#guard`, so
the receipts carry line comments.
-/

import Effect4.Meta.Derive
import Effect4.Target.TypeScript.Trace
import Effect4.Target.TypeScript.ScriptFlow

namespace Effect4Test.Counterexamples.Target.AnswerProfile

open Effects Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val ToVal)
open Effect4.Target.TypeScript.Trace (val rows)

/-! ## `E4-TARGET-CE-022`: a depth-three answer read by shape, not by spelling

The attack: the host encoder decides a value's wire form from the value. Above
depth two that is not enough information. A pair and a list are both JavaScript
arrays, so the single host value `[[1, 2]]` has two readings in the alphabet,
and they render to different bytes in a different order. Whichever one an
untyped encoder picks, it is right for one declared answer type and wrong for
the other, and the golden comparison is a byte comparison. -/

-- The list-of-pairs reading: a pair is `[a, b]`, a list is right-nested pairs
-- closed by unit. This is what Lean renders for
-- `ReadonlyArray<readonly [number, number]>`.
#guard val (ToVal.toVal ([(1, 2)] : List (Nat × Nat))) = "[[1, 2], []]"

-- The list-of-lists reading of the same host array. This is what an encoder
-- that reads every JavaScript array as a list produces.
#guard val (ToVal.toVal ([[1, 2]] : List (List Nat))) = "[[1, [2, []]], []]"

-- The two readings are different bytes, so the golden comparison separates
-- them; and they are different events, so `m2` agreement separates them too.
#guard val (ToVal.toVal ([(1, 2)] : List (Nat × Nat))) !=
  val (ToVal.toVal ([[1, 2]] : List (List Nat)))
#guard !Effect4.Trace.agree Effects.Trace.Mask.m2
  [.answer "lookup" (ToVal.toVal ([(1, 2)] : List (Nat × Nat)))]
  [.answer "lookup" (ToVal.toVal ([[1, 2]] : List (List Nat)))]

-- The same separation one constructor down, where the ambiguity is between an
-- `Option` of a pair and a two-element list of options.
#guard val (ToVal.toVal (Option.some (1, 2) : Option (Nat × Nat))) = "{\"some\":[1, 2]}"
#guard val (ToVal.toVal ([Option.some 1, Option.some 2] : List (Option Nat))) =
  "[{\"some\":1}, [{\"some\":2}, []]]"

-- The retained fix: the spelling is carried in the row, so the host has the
-- information the value does not carry. Both readings have a spelling in the
-- profile, and the spellings differ.
#guard (Spelling.list (.prod .nat .nat)).render = "ReadonlyArray<readonly [number, number]>"
#guard (Spelling.list (.list .nat)).render = "ReadonlyArray<ReadonlyArray<number>>"
#guard (Spelling.list (.prod .nat .nat)).render != (Spelling.list (.list .nat)).render

-- The rendered row a golden carries, for the depth-three answer the corpus
-- pins (`generated/traces/probe.empty.tsv`).
#guard rows [.answer "lookup" (ToVal.toVal (Option.some (Except.ok 44) : Option (Except String Nat)))] =
  "answer\tlookup\t{\"some\":[true, 44]}\n"

/-! ## `E4-TARGET-CE-023`: an atom declared in one face only

The attack: an atom is a Lean function, a row in the flow embedding's table,
and a `const` in `atoms.ts`, and before this packet those three were three
independent declarations. A name present in one and absent in another is a
host `ReferenceError` or a silently refused embedding, neither of which any
Lean receipt sees. -/

effect_atoms ProbeAtoms where
  | bump (n : Nat) : Nat ⟪ "n + 1" ⟫ := n + 1

effect_signature Store where
  | get : Nat ⟪ "read the store" ⟫

-- The three faces are projections of one row list, so their name sets are
-- equal by construction, not by agreement.
#guard ProbeAtoms.table.map (·.1) = ProbeAtoms.rows.map (·.name)
#guard ProbeAtoms.source = atomsModule ProbeAtoms.rows
#guard ProbeAtoms.rows.map (·.name) = ["bump"]
#guard ProbeAtoms.eval "bump" (.nat 4) = .nat 5

-- The failure the packet removes: a script calling an atom the table does not
-- carry. The embedding refuses it, and that refusal is the only signal a
-- hand-written table gives.
def ghostScript : Script :=
  { family := "Store", name := "ghost", param := ("n", "number"), result := "number",
    steps := [.perform (some "x") "get" [], .ret (.app "ghost" [.var "x"])] }

#guard (Script.toFlow Store.rows ProbeAtoms.table ghostScript).isNone
#guard (Script.toFlow Store.rows (ProbeAtoms.table ++ [("ghost", "number", "number")])
  ghostScript).isSome

-- An atom absent from the rows has no host body, so the generated module
-- cannot name it: the source is exactly the rows.
#guard Spelling.mentions "export const bump" (atomsModule ProbeAtoms.rows)
#guard !Spelling.mentions "export const ghost" (atomsModule ProbeAtoms.rows)

end Effect4Test.Counterexamples.Target.AnswerProfile
