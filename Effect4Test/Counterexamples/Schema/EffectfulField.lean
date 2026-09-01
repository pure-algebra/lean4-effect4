/-
Retained attacks for `test/contracts/schema-effectful-field.contract.md`.
-/

import Effect4.Schema.EffectfulField

namespace Effect4Test.Counterexamples.Schema.EffectfulField

open Effect4

private def spec : EffectfulFieldSpec where
  alphabet := { value := 7 }
  readOperation := { value := 11 }
  writeOperation := { value := 12 }

private def valid : AnnotationEntry :=
  EffectfulFieldSpec.annotationKey.entry spec

/-! `E4-SCHEMA-CE-049`: typed filtering must not hide duplicate or malformed
raw occurrences. -/

example : EffectfulFieldSpec.check (some [valid, valid]) = none := by
  rfl

example : EffectfulFieldSpec.check
    (some
      [ { key := EffectfulFieldSpec.annotationKey.name, payload := Json.null }
      , valid
      ]) = none := by
  rfl

/-! A tiny closed signature for the generated-program attacks. -/

private inductive Op where
  | read
  | write (value : Nat)
deriving DecidableEq

private def Sig : Signature where
  Op := Op
  Answer
    | .read => Nat
    | .write _ => Unit

private def operationId : Op -> OperationId
  | .read => { value := 11 }
  | .write _ => { value := 12 }

private def operations : FieldEffectOps Sig (Nat × Bool) Nat where
  alphabet := { value := 7 }
  readOperation := { value := 11 }
  writeOperation := { value := 12 }
  operationId := operationId
  read _ := .read
  read_answer _ := rfl
  write _ value := .write value
  read_operation _ := rfl
  write_operation _ _ := rfl

private def otherAlphabet : FieldEffectOps Sig (Nat × Bool) Nat :=
  { operations with alphabet := { value := 8 } }

/-! `E4-SCHEMA-CE-050`: matching local operation numbers do not erase the
alphabet identity. -/

example : spec.Matches operations := by
  decide

example : not (spec.Matches otherAlphabet) := by
  decide

private def fstLens : Lens (Nat × Bool) Nat where
  get := Prod.fst
  replace value source := (value, source.2)

private def field : EffectfulField Sig (Nat × Bool) Nat :=
  { optic := fstLens, operations := operations }

private def rootOperation : Program Sig A -> Option Op
  | .pure _ => none
  | .vis operation _ => some operation

/-! `E4-SCHEMA-CE-051`: modify starts with the effectful read. It cannot use
the stale `Lens.get source` value to choose the write. -/

example : rootOperation (field.modify (fun value => value + 1) (10, true)) =
    some .read := by
  rfl

private def staleModify (source : Nat × Bool) : Program Sig (Nat × Bool) :=
  Program.perform (operations.write source (fstLens.get source + 1)) >>= fun _ =>
    Program.pure (fstLens.replace (fstLens.get source + 1) source)

example : rootOperation (staleModify (10, true)) = some (.write 11) := by
  rfl

/-! `E4-SCHEMA-CE-052`: set starts with the write program rather than erasing
the effect into a pure lens update. -/

example : rootOperation (field.set 13 (10, true)) = some (.write 13) := by
  rfl

example : rootOperation (Program.pure (fstLens.replace 13 (10, true)) :
    Program Sig (Nat × Bool)) = none := by
  rfl

end Effect4Test.Counterexamples.Schema.EffectfulField
