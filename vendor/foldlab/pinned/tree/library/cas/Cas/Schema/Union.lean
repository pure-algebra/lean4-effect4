/-!
# The union modes — the two semantics, as first-order data

Effect's union carries a MODE: `anyOf` (try each member, first success
wins) or `oneOf` (assert exactly one member matches, and report the
successes when more than one does) — `SchemaRepresentation.ts:395-398`,
`SchemaIssue.ts:698/757`. The mode is part of a union's identity, so it
is content, not a function and not a default.

The table is the house registry idiom (`Cas/Schema/Declarations.lean`,
`Cas/Lift/Taxonomy.lean`): a closed inductive of admitted rows, their
wire spellings verbatim, a completeness theorem, a `Nodup` guard on the
wire, and the wire read back exactly. Two rows is a small table, but a
small table is still a table — the alternative, a `Bool`, would make
the wire spelling live in a projection function and would read wrong
from every seat (S5).

**The mode is always spelled.** Effect defaults an omitted mode to
`anyOf` (`Schema.ts:4912`) and its own code generator elides `anyOf`
again (`toCodeDocument.ts:570`). The estate does neither: the
revision-1 projection always emits `"mode"`, and the lowering always
passes it. That is D4 — deterministic elisions only — and it is what
keeps one code, one spelling, one address.
-/

namespace Cas.Schema

/-- LAW SM-6: both modes are carried and admitted, and a union's
member order is its identity.

A union's semantics. Row order is Effect's own declaration order
(`Schema.Literals(["anyOf", "oneOf"])`, `SchemaRepresentation.ts:1064`). -/
inductive UnionMode where
  /-- Try the members in order; the first success is the result. Effect's
  default, and the mode a plain `Schema.Union([..])` builds. -/
  | anyOf
  /-- Require exactly one member to match; more than one is a failure
  that reports the successes. -/
  | oneOf
  deriving DecidableEq, Repr

/-- The persistence identity, verbatim (`representation.mode`). -/
def UnionMode.wire : UnionMode → String
  | .anyOf => "anyOf"
  | .oneOf => "oneOf"

/-- The wire spelling read back — the admission test the decoder
applies to a foreign `mode`. Anything else is not a mode at all. -/
def UnionMode.ofWire : String → Option UnionMode
  | "anyOf" => some .anyOf
  | "oneOf" => some .oneOf
  | _ => none

/-- Every mode, in registry order. -/
def UnionMode.all : List UnionMode := [.anyOf, .oneOf]

/-- The table is complete: every mode is listed. -/
theorem UnionMode.all_complete (m : UnionMode) : m ∈ UnionMode.all := by
  cases m <;> decide

-- Wire spellings collide with nothing: injectivity of the wire on the
-- table, checked at elaboration time.
#guard decide ((UnionMode.all.map UnionMode.wire).Nodup)

/-- The wire is read back exactly. -/
theorem UnionMode.ofWire_wire (m : UnionMode) :
    UnionMode.ofWire m.wire = some m := by
  cases m <;> rfl

end Cas.Schema
