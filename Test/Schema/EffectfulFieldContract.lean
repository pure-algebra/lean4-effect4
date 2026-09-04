/-
Contract packet: `test/contracts/schema-effectful-field.contract.md`.

Breaker-owned red battery for `SCHEMA-PG-EFFECTFUL-FIELD`. The builder makes
this file green without editing it.
-/

import Effect4.Schema.EffectfulField

namespace Test.Schema.EffectfulFieldContract

open Effect4 Effects

universe uOp uAns v

variable {signature : Signature.{uOp, uAns}}
variable {S A : Type uAns}

/-! ## F0 — portable data reuses existing identities and annotation carrier -/

#check (@EffectfulFieldSpec : Type)
#check (@EffectfulFieldSpec.mk :
  AlphabetId -> OperationId -> OperationId -> EffectfulFieldSpec)
#check (@EffectfulFieldSpec.alphabet : EffectfulFieldSpec -> AlphabetId)
#check (@EffectfulFieldSpec.readOperation : EffectfulFieldSpec -> OperationId)
#check (@EffectfulFieldSpec.writeOperation : EffectfulFieldSpec -> OperationId)
#synth DecidableEq EffectfulFieldSpec
#synth Repr EffectfulFieldSpec

#check (EffectfulFieldSpec.annotationKey : AnnotationKey EffectfulFieldSpec)
#check (EffectfulFieldSpec.annotationKey_lawful :
  EffectfulFieldSpec.annotationKey.Lawful)

example : EffectfulFieldSpec.annotationKey.name = "effect4/effectful-field" := by
  rfl

/-! ## F1 — admission sees exact raw same-name occurrences -/

#check (@EffectfulFieldSpec.rawOccurrences : Annotations -> List Json)
#check (@EffectfulFieldSpec.RawAdmissible : Annotations -> Prop)
#check (@EffectfulFieldSpec.check : Annotations -> Option EffectfulFieldSpec)

#check (@EffectfulFieldSpec.check_eq_some_iff :
  forall {annotations : Annotations} {spec : EffectfulFieldSpec},
    EffectfulFieldSpec.check annotations = some spec <->
      EffectfulFieldSpec.rawOccurrences annotations =
        [EffectfulFieldSpec.annotationKey.encode spec])

#check (@EffectfulFieldSpec.rawAdmissible_iff_exists_check :
  forall {annotations : Annotations},
    EffectfulFieldSpec.RawAdmissible annotations <->
      exists spec, EffectfulFieldSpec.check annotations = some spec)

example (annotations : Annotations) :
    EffectfulFieldSpec.rawOccurrences annotations =
      (Annotations.payloadsAt EffectfulFieldSpec.annotationKey.name).collect annotations := by
  rfl

/-! ## F2 — resolved bridge reuses Signature and Program -/

#check (@FieldEffectOps.{uOp, uAns} :
  (signature : Signature.{uOp, uAns}) -> Type uAns -> Type uAns ->
    Type (max uOp uAns))
#check (@FieldEffectOps.mk.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  (alphabet : AlphabetId) ->
  (readOperation writeOperation : OperationId) ->
  (operationId : signature.Op -> OperationId) ->
  (read : S -> signature.Op) ->
  (read_answer : forall source, signature.Answer (read source) = A) ->
  (write : S -> A -> signature.Op) ->
  (read_operation : forall source,
    operationId (read source) = readOperation) ->
  (write_operation : forall source value,
    operationId (write source value) = writeOperation) ->
  FieldEffectOps signature S A)

#check (@EffectfulFieldSpec.Matches.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  EffectfulFieldSpec -> FieldEffectOps signature S A -> Prop)

#check (@EffectfulField.{uOp, uAns} :
  (signature : Signature.{uOp, uAns}) -> Type uAns -> Type uAns ->
    Type (max uOp uAns))
#check (@EffectfulField.mk.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  Lens S A -> FieldEffectOps signature S A ->
    EffectfulField signature S A)

#check (@EffectfulField.Resolvable.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  Annotations -> FieldEffectOps signature S A -> Prop)

#check (@EffectfulField.resolve.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  Lens S A -> FieldEffectOps signature S A -> Annotations ->
    Option (EffectfulField signature S A))

#check (@EffectfulField.resolvable_iff_resolve_isSome.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  {optic : Lens S A} -> {operations : FieldEffectOps signature S A} ->
  {annotations : Annotations} ->
  EffectfulField.Resolvable annotations operations <->
    (EffectfulField.resolve optic operations annotations).isSome = true)

/-! ## F3 — generated programs have exact ordered equations -/

#check (@EffectfulField.get.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  EffectfulField signature S A -> S -> Program signature A)
#check (@EffectfulField.set.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  EffectfulField signature S A -> A -> S -> Program signature S)
#check (@EffectfulField.modify.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  EffectfulField signature S A -> (A -> A) -> S -> Program signature S)

#check (@EffectfulField.get_eq.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  (field : EffectfulField signature S A) -> (source : S) ->
  field.get source =
    Program.perform (field.operations.read source) >>= fun answer =>
      Program.pure ((field.operations.read_answer source).mp answer))

#check (@EffectfulField.set_eq.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  (field : EffectfulField signature S A) -> (value : A) -> (source : S) ->
  field.set value source =
    Program.perform (field.operations.write source value) >>= fun _ =>
      Program.pure (field.optic.replace value source))

#check (@EffectfulField.modify_eq.{uOp, uAns} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  (field : EffectfulField signature S A) -> (f : A -> A) -> (source : S) ->
  field.modify f source =
    field.get source >>= fun current => field.set (f current) source)

/-! ## F4 — interpretation preserves the generated order -/

#check (@EffectfulField.interpret_set.{uOp, uAns, v} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  {M : Type uAns -> Type v} -> [Monad M] -> [LawfulMonad M] ->
  (handler : Handler signature M) ->
  (field : EffectfulField signature S A) -> (value : A) -> (source : S) ->
  interpret handler (field.set value source) =
    handler.handle (field.operations.write source value) >>= fun _ =>
      pure (field.optic.replace value source))

#check (@EffectfulField.interpret_modify.{uOp, uAns, v} :
  {signature : Signature.{uOp, uAns}} -> {S A : Type uAns} ->
  {M : Type uAns -> Type v} -> [Monad M] -> [LawfulMonad M] ->
  (handler : Handler signature M) ->
  (field : EffectfulField signature S A) -> (f : A -> A) -> (source : S) ->
  interpret handler (field.modify f source) =
    handler.handle (field.operations.read source) >>= fun answer =>
      let current := (field.operations.read_answer source).mp answer
      handler.handle (field.operations.write source (f current)) >>= fun _ =>
        pure (field.optic.replace (f current) source))

end Test.Schema.EffectfulFieldContract
