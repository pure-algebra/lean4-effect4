# Schema effectful-field interface contract

Status: **Pass-B FROZEN; implementation REQUIRED-BLOCKED**.

Production fence: `src/Effect4/Schema/EffectfulField.lean`, plus its import in
`Effect4.lean`. Breaker battery:
`Test/Schema/EffectfulFieldContract.lean`. Retained attacks:
`Test/Counterexamples/Schema/EffectfulField.lean` and
`E4-SCHEMA-CE-049` through `E4-SCHEMA-CE-052`.

This is the first additive consumer of the Schema annotation data plane. It
derives effectful `get`, `set`, and `modify` programs for a field selected by
an existing pure `Lens`. It does not make the optic carrier monadic and does
not add a second Schema, effect, program, operation identity, or alphabet
carrier.

## Existing-type disposition

The implementation reuses these declarations exactly:

- `Lens S A` selects and locally replaces the field;
- `AnnotationKey A`, `AnnotationEntry`, `Annotations`, and
  `Annotations.payloadsAt` own persisted metadata and raw occurrence order;
- `Signature` and `Program` own the effect algebra and generated program;
- `AlphabetId` and `OperationId` own portable effect identity.

`EffectfulFieldSpec` is new because it is the portable annotation payload.
`FieldEffectOps` is new because it is the resolved, non-persisted bridge from
those identities to operations in an existing `Signature`. `EffectfulField` is a
small derived interface pairing the existing lens with that bridge. None is a
replacement carrier.

No service key, environment requirement, refusal, cause, runtime, handler, or
TypeScript type appears in this packet. A later layer may resolve the same
portable identities through services, but it may not alter this admission
relation or store host functions in Schema data.

## Portable annotation

```lean
structure Effect4.EffectfulFieldSpec where
  alphabet : AlphabetId
  readOperation : OperationId
  writeOperation : OperationId
deriving DecidableEq, Repr

EffectfulFieldSpec.annotationKey : AnnotationKey EffectfulFieldSpec
EffectfulFieldSpec.annotationKey_lawful :
  EffectfulFieldSpec.annotationKey.Lawful
```

The annotation name is exactly `"effect4/effectful-field"`. Its payload is a
JSON object with exactly these ordered entries:

```text
alphabet       canonical decimal string for AlphabetId.value
readOperation  canonical decimal string for OperationId.value
writeOperation canonical decimal string for OperationId.value
```

Decode accepts no other shape, order, key multiplicity, extra field, or
non-canonical decimal spelling. This exact format makes
`annotationKey_lawful.encode_decode` true over retained raw JSON rather than
silently normalizing it.

## Exact raw-occurrence admission

```lean
EffectfulFieldSpec.rawOccurrences : Annotations -> List Json
EffectfulFieldSpec.RawAdmissible : Annotations -> Prop
EffectfulFieldSpec.check : Annotations -> Option EffectfulFieldSpec

EffectfulFieldSpec.check_eq_some_iff :
  EffectfulFieldSpec.check annotations = some spec <->
    EffectfulFieldSpec.rawOccurrences annotations =
      [EffectfulFieldSpec.annotationKey.encode spec]

EffectfulFieldSpec.rawAdmissible_iff_exists_check :
  EffectfulFieldSpec.RawAdmissible annotations <->
    exists spec, EffectfulFieldSpec.check annotations = some spec
```

`rawOccurrences` is definitionally the `collect` projection of
`Annotations.payloadsAt EffectfulFieldSpec.annotationKey.name`; no second bag
walk is permitted. `RawAdmissible` means that this raw list is exactly one
canonically encoded spec. `check` returns that spec exactly when admitted.

Consequently missing, malformed, or multiple same-name occurrences all return
`none`. Unrelated annotations are preserved and ignored. In particular,
`AnnotationKey.getAll` is forbidden as the admission input: it filters
malformed entries and would accept one valid occurrence beside malformed raw
evidence.

## Resolved programs and derived interface

All program result types in this first packet live in the signature answer
universe.

```lean
structure Effect4.FieldEffectOps
    (signature : Signature.{uOp, uAns}) (S A : Type uAns) where
  alphabet : AlphabetId
  readOperation : OperationId
  writeOperation : OperationId
  operationId : signature.Op -> OperationId
  read : S -> signature.Op
  read_answer : forall source, signature.Answer (read source) = A
  write : S -> A -> signature.Op
  read_operation : forall source, operationId (read source) = readOperation
  write_operation : forall source value,
    operationId (write source value) = writeOperation

EffectfulFieldSpec.Matches :
  EffectfulFieldSpec -> FieldEffectOps signature S A -> Prop

structure Effect4.EffectfulField
  (signature : Signature.{uOp, uAns})
    (S A : Type uAns) where
  optic : Lens S A
  operations : FieldEffectOps signature S A
```

`Matches` is equality of the alphabet, read-operation, and write-operation
identities, in that order. It assigns no meaning beyond exact identity
agreement.

```lean
EffectfulField.Resolvable :
  Annotations -> FieldEffectOps signature S A -> Prop

EffectfulField.resolve :
  Lens S A -> FieldEffectOps signature S A -> Annotations ->
    Option (EffectfulField signature S A)

EffectfulField.resolvable_iff_resolve_isSome :
  EffectfulField.Resolvable annotations operations <->
    (EffectfulField.resolve optic operations annotations).isSome = true
```

`Resolvable` requires one checked spec and `spec.Matches operations`.
`resolve` returns exactly `some { optic, operations }` under that condition
and `none` otherwise. It does not look up a service or reinterpret operation
identity.

The generated API is:

```lean
EffectfulField.get :
  EffectfulField signature S A -> S -> Program signature A
EffectfulField.set :
  EffectfulField signature S A -> A -> S -> Program signature S
EffectfulField.modify :
  EffectfulField signature S A -> (A -> A) -> S -> Program signature S
```

Its exact equations are:

```lean
field.get source =
  Program.perform (field.operations.read source) >>= fun answer =>
    Program.pure ((field.operations.read_answer source).mp answer)

field.set value source =
  Program.perform (field.operations.write source value) >>= fun _ =>
    Program.pure (field.optic.replace value source)

field.modify f source =
  field.get source >>= fun current => field.set (f current) source
```

The read equality is the only answer-type equality in this bridge. The write
answer is discarded polymorphically, so there is deliberately no
`write_answer` field. `modify` transforms the
value produced by the read, not the stale value projected from `source`.
`set` performs the write before returning the locally updated source.

For every lawful target monad and handler, `interpret_set` and
`interpret_modify` expose those same ordered binds after interpretation.
They are the semantic bridge: no fixed-fuel runner law is stated.

## Counterexamples

- `E4-SCHEMA-CE-049`: filtering through typed values accepts one valid entry
  beside malformed or duplicate raw evidence.
- `E4-SCHEMA-CE-050`: operation IDs can coincide under different alphabets;
  the alphabet comparison cannot be omitted.
- `E4-SCHEMA-CE-051`: using `Lens.get source` in `modify` skips the effectful
  read and can transform a stale value.
- `E4-SCHEMA-CE-052`: returning only `Program.pure (optic.replace ...)` from
  `set` erases the write effect.

## Proof burden

`SCHEMA-PG-EFFECTFUL-FIELD` is required because this packet owns admission,
generated-program equations, and interpreter preservation. Its edges are:

1. `EFF-FIELD-01-CODEC`: both `AnnotationKey.Lawful` directions for the exact
   payload spelling;
2. `EFF-FIELD-02-ADMISSION`: `check_eq_some_iff` and
   `rawAdmissible_iff_exists_check`, including every raw occurrence;
3. `EFF-FIELD-03-RESOLUTION`: resolvability is exactly checked annotation plus
   three identity equalities, and the operation bridge ties both operation
   constructors to their retained `OperationId`s;
4. `EFF-FIELD-04-GENERATION`: exact `get`, `set`, and `modify` equations;
5. `EFF-FIELD-05-INTERPRETATION`: `interpret_set` and `interpret_modify`
   preserve program order through `interpret_bind`.

Record projections, the ground key-name equation, and the four finite
counterexamples are leaf receipts, not separate proof graphs. Acceptance
requires both Lean batteries to elaborate, all exported law theorems to have
no axioms, and the default package build to pass without editing this packet
or either breaker battery.

## Breaker receipt

At freeze time production declares none of the names above. The breaker runs:

```text
lake env lean -DmaxErrors=10000 Test/Schema/EffectfulFieldContract.lean
lake env lean -DmaxErrors=10000 Test/Counterexamples/Schema/EffectfulField.lean
```

Both must be clean red because of the missing production surface, not because
of an absent import or unrelated build failure.
