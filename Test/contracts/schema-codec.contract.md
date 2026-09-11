# S-3 type-directed JSON boundary

Owner-approved contract, 2026-09-11. The owner selected exact value admission and
layout-compatible subtype agreement after E4-SCHEMA-CE-056 through 059, and selected
the pinned rc.112 Schema JSON formats over the original proposal's Result/Cause shapes.

Implementation: `src/Effect4/Schema/Codec.lean`.
Laws: `src/Effect4/Laws/Schema/Codec.lean`.
Battery: `Test/Codegen/SchemaGenerationContract.lean`.
Retained falsifiers: `Test/Counterexamples/Schema/Codec.lean`.

## Boundary

`Ty.encode : Ty → Store.Val → Option Json` and
`Ty.decode : Ty → Json → Option Store.Val` reuse the existing type and value carriers.
They add no constructor, ordinal, CAS key, or stored binary encoding.

The encoder checks original type membership, computes a candidate JSON image, and
accepts only if the layout decoder recovers the exact input value. `Ty.isCodecValue`
is the executable admission check for this domain. `Ty.isCodecSupported` describes
the absence of opaque/unsupported components; it does not guarantee that every
inhabitant has a JSON image. `never` is a supported empty column and admits no
standalone value; `int`, handles and fibers refuse.

The decoder checks the original type after reading the structural layout, including
literal refinements and cause error membership. Object field order is immaterial;
duplicates, missing fields and extra fields refuse. The decoder's strict field set
is narrower than Effect's default excess-property stripping.

Natural numbers encode through `Arch.Json.ofNat`; only exact recoveries are accepted.
Exactly representable integers above 2^53 are allowed. Fractions, negative numbers,
negative zero, NaNs and infinities refuse. Ordinary lists use arrays; fiber snapshots
are not flattened to lists. Cause annotations omitted by the host format cannot cross
the exact boundary. Unions retain branch order: a value refuses when its chosen JSON
image decodes to a different branch's machine representation.

## Wire profile

The reference is `vendor/effect-4.0.0-rc.112/src/Schema.ts`, specifically the
`Schema.toCodecJson` projection of Option, Result, Exit, Cause and Defect.
Unit uses null; booleans and strings are scalar JSON; products and lists use arrays.
Option uses `None` or `Some/value`. Result uses `Failure/failure` or
`Success/success`. Exit uses `Success/value` or `Failure/cause`.
Cause is an ordered array of `Fail/error`, `Die/defect`, and `Interrupt/fiberId`
objects; an absent interruptor uses JSON null.

Closed machine defect payloads retain the JSON data in `harness/truth/Truth.lean`.
Arbitrary host exceptions and runtime objects have no promised inverse into the closed
machine alphabet. The host check compares representative JSON images, not a general
semantic equivalence between host objects and machine values.

## Required laws

- `encode_of_hasTy`: membership and `Ty.isCodecValue t v = true` imply encoding succeeds.
- `decode_encode`: on the same domain, `(encode t v).bind (decode t) = some v`.
  This avoids inventing a default JSON inhabitant for `Option.get!`.
- `hasTy_decode`: `decode t j = some v` implies original type membership, without
  any extra support or admission premise.
- `encode_sub`: `Ty.sub s t = true`, membership at `s`, and `Codec.Compatible s t`
  imply `encode t v = encode s v`.

`Codec.Compatible` is equality of the structural layouts interpreted by the codec.
Layout erases literal refinements outside unions and recurses through composites;
it keeps each whole union because original branch constraints select an interpretation.
This admits literal widening through composites and identical unions. It is a
conservative executable sufficient condition, not a complete decision procedure for
all semantically equivalent JSON encoders.

All declarations remain within `[propext, Quot.sound]`. The build checks root separation,
module closure and the axiom ceiling. `scripts/check-schema-codec.sh` typechecks the host
comparison and freshly compares public Lean outputs with rc.112, including round trips
and the rejected legacy shapes. Its finite examples do not replace the universal laws.
