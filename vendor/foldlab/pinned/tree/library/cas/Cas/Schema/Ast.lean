import Cas.Core.Node
import Cas.Values.Json
import Cas.Schema.Declarations
import Cas.Schema.Union

/-!
# The codes — the canonical schema, Lean side

The root schema language as data. Identity is structural everywhere:
no code's meaning lives in a function (the carrier-adequacy law), so
every code is comparable, encodable, and — through the node envelope —
content-addressable.

This is increment 1 of the universe: the closed, non-recursive
fragment mirroring the TypeScript v0 constructor set exactly
(`Null/Boolean/Integer/String/Literal/Array/Struct/Ref`). Increment 2
adds recursion as NAMED definition environments (the shape tree-sitter
grammars and JSON Schema `$defs` actually have), with conformance as
an inductive predicate and a fueled sound-and-complete checker — the
admission pattern, applied to schemas.

`WF` is the canonical-fields discipline (no duplicate field names —
what makes the encode/decode round trip total on the encode side);
strict sortedness, which byte-level canonicality adds on top, arrives
with the rendering theorem.
-/

namespace Cas.Schema

/-- The safe-integer bound: the one number range whose decimal
rendering is language-neutral (CAS-004). -/
def maxSafeNat : Nat := 9007199254740991

/-- A safe integer. -/
abbrev SafeInt := { i : Int // i.natAbs ≤ maxSafeNat }

/-- A literal a schema can pin. -/
inductive LitVal where
  | null
  | bool (b : Bool)
  | int (i : SafeInt)
  | str (s : String)
  deriving DecidableEq

/-- LAW SM-15: the number row is bounded because the value plane has
no float term.

An enum member's VALUE. Effect's `Enum` admits exactly two value
types and no others — `Schema.Union([StringValueCodec, NumberValueCodec])`
(`SchemaRepresentation.ts:1015-1022`) — so the carrier is those two rows
and nothing else. It is deliberately NOT `LitVal`: a null or boolean
enum member is not a spelling Effect can persist, and reusing `LitVal`
would put two unspellable rows under the code and make the decoder
carry a shape gate the type can carry instead.

The number row is `SafeInt`, the same bound every other number in this
plane obeys (CAS-004) — Effect's own field is `Schema.Number`, whose
float range the value plane has no term for (the float ceiling,
ruling 15). -/
inductive EnumValue where
  | str (s : String)
  | int (i : SafeInt)
  deriving DecidableEq

/-- The codes. A struct field is `(name, optional, code)`. -/
inductive Ast where
  | null
  | bool
  | int
  | str
  | lit (v : LitVal)
  | arr (item : Ast)
  | struct (fields : List (String × Bool × Ast))
  | ref (tag : UInt8)
  /-- The general declaration code (increment C-decl): Effect's opaque
  `Declaration` as content — a registry id, a first-order payload, and
  the type parameters, exactly the persisted shape
  (`SchemaRepresentation.ts:144-153`).

  `id` ranges over `DeclarationId.General`, so an unadmitted
  declaration has no spelling here at all: admission is by
  construction, and the door names what it refuses. Row zero of the
  registry, `foldlab/cas/ref`, is NOT general — it keeps its dedicated
  code `.ref`, which is what keeps the revision-1 projection injective.
  Whether `.ref` should later become sugar for this code is an operator
  ruling, recorded and not taken. -/
  | decl (id : DeclarationId.General) (payload : DeclPayload)
      (typeParameters : List Ast)
  /-- The union code (increment C1): Effect's `Union` as content — an
  ORDERED list of member codes and the mode, exactly the persisted
  shape (`SchemaRepresentation.ts:395-398`).

  **Order is identity** (operator-ratified 2026-08-29). Members are
  never sorted, never flattened, never deduplicated, so
  `union [a, b] ≠ union [b, a]` and `union [a, union [b, c]] ≠
  union [a, b, c]`: the ordered tree IS the identity, and two reordered
  unions are two codes at two addresses. This is the estate's own
  TypeScript normalizer read into the carrier ("union, tuple, check,
  and reference order remain semantic and are never rearranged"), and
  it is the contrast case to `.struct`, whose fields DO sort.

  The mode is always spelled — `UnionMode` is a constructor argument,
  not an option with a default. -/
  | union (members : List Ast) (mode : UnionMode)
  /-- The enum code (increment C4): Effect's `Enum` as content — an
  ORDERED list of `(name, value)` members, exactly the persisted shape
  (`SchemaRepresentation.ts:1015-1022`).

  **Order is identity**, for the same reason it is on `.union`, and with
  a second reason of its own. Effect builds the member list as
  `Object.keys(enums).filter(…).map(key => [key, enums[key]])`
  (`Schema.ts:3021-3030`): `Object.keys` order, which for a TypeScript
  enum is SOURCE order. Nothing in Effect's constructor, its
  representation codec, or the estate's normalizer rearranges it, and
  the array in the wire is positional, not a keyed record — so the
  written order is the order stored, read back, and re-emitted, and
  `enum [("A", …), ("B", …)] ≠ enum [("B", …), ("A", …)]`.

  What `WF` asks is nonemptiness and pairwise-distinct NAMES. The name
  is the member's identity (`E.A` is how a member is written), so two
  members cannot share one. VALUES are deliberately unconstrained:
  TypeScript admits alias members (`enum E { A = 1, B = 1 }`), Effect
  persists both rows, and refusing them here would retire content the
  source language spells. That freedom is exactly why the denotation is
  parked — see `Cas/Schema/El.lean`, obligation `enumEl`. -/
  | enum (members : List (String × EnumValue))
  /-- The tuple code (increment C2, the Arrays completion): Effect's
  `Arrays` node in its POSITIONAL form — per-element type and
  optionality, with an optional rest type — exactly the persisted shape
  `{"_tag":"Arrays","checks":[],"elements":[{isOptional,type},…],
  "rest":[…]}` (`SchemaRepresentation.ts:1028-1038`).

  **Why a new constructor and not a wider `.arr`** (the additive-vs-arity
  call, recorded): growing `.arr` from `(item : Ast)` to
  `(elements) (rest)` is an ARITY change to a landed code — every
  pattern match, every `Described` instance, and the deriving handler
  break, and the code that is today `Ast.arr a` acquires a second
  spelling. A new constructor is additive: `.arr` keeps its meaning and
  its bytes, and nothing already written moves.

  **Why the elements are nonempty BY CONSTRUCTION** (`first`, then the
  rest of them): `{elements:[], rest:[t]}` is already `Ast.arr t`'s
  representation. A tuple code able to spell an empty element list would
  therefore be a SECOND two-to-one map from codes to representations,
  and `toRepresentationJson_inj` — which holds unconditionally, up to
  the one literal-null collapse of register R13 — would become false as
  stated. Making the collision unspellable is cheaper and more honest
  than growing the normal form to absorb it.

  What this leaves out, deliberately: `Schema.Tuple([])`, the EMPTY
  tuple (`{elements:[], rest:[]}`), has no spelling here. It has none
  today either — the `.arr` decoder demands exactly one rest element —
  so nothing is retired; admitting it is a constructor change owed to a
  consumer, not to this increment.

  The rest is an `Option`, so "at most one rest type" is true by
  construction rather than by a well-formedness clause: a `rest` array of
  length two or more has no spelling at all and dies in the decoder. The
  trailing-rest semantics the admission map defers stay deferred, and
  the refusal is structural. -/
  | tuple (first : Bool × Ast) (more : List (Bool × Ast)) (rest : Option Ast)
  /-- The reference code (increment C6): Effect's `Reference` as content
  — a NAME into the document's references table, exactly the persisted
  shape `{"$ref":"…","_tag":"Reference"}`
  (`SchemaRepresentation.ts:171-174`, `:1066-1069`).

  **Two constructors, not one** (operator-ruled 2026-08-30, amending
  CORE-ABSTRACTIONS-PLAN.md:127-131). Effect spells recursion with two
  different nodes and a real recursive document carries both: this one
  is the EDGE — it names a table entry — and `.susp` is the GUARD. The
  one-constructor design the plan first carried cannot decode what
  Effect writes, and it makes the guardedness law a tautology: if the
  only node naming a table entry is also the guard, then every cycle
  passes through a guard for free and the door refuses nothing. The
  probe that pinned the spellings is
  `library/effects/test/SchemaReferencesPin.test.ts`; the ruling and the
  break are recorded in `contracts/PDD-3.contract.md`.

  `WF` asks NONEMPTINESS of the name and nothing else — the same
  constraint Effect puts on the field itself (`$ref` is
  `Schema.NonEmptyString`, so an empty name is not a spelling Effect can
  persist). The ADDRESS discipline — "the name is the target's content
  address, or an annotated name" — is deliberately NOT here: it is the
  door's and the materializer's question, per the ruling's own text, and
  a `WF` clause about it would put a store fact inside a structural
  predicate. RESOLVABILITY is likewise not asked: a name with no table
  entry is admitted, exactly as Effect's own codec admits it (pinned by
  the probe), and it can lie on no cycle because it has no outgoing
  edge. -/
  | reference (name : String)
  /-- The suspend code (increment C6): Effect's `Suspend` as content — a
  lazily resolved INLINE representation, exactly the persisted shape
  `{"_tag":"Suspend","checks":[],"thunk":<representation>}`
  (`SchemaRepresentation.ts:158-163`, `:984-989`).

  The thunk is a nested CODE, not a name — which is what makes this a
  different constructor from `.reference` rather than a spelling of it.
  Effect's `checks` field here is `Schema.Tuple([])`, the EMPTY tuple, so
  a `Suspend` can never carry a check and the carrier needs no term for
  one; Effect's own decoder refuses a `Suspend` that carries one, which
  the probe pins.

  **This is the GUARD the guardedness law is about.** `Ast.bareRefs`
  stops dead at this constructor, so a cycle in the references table
  that passes through a `.susp` contributes no edge to the relation the
  door checks — which is exactly "every cycle passes through a `susp`",
  stated as acyclicity of the non-suspend relation
  (`Cas/Schema/Guarded.lean`).

  `WF` asks only that the thunk is a code: a `Suspend` imposes no
  discipline of its own. -/
  | susp (thunk : Ast)

mutual

/-- Canonical-fields well-formedness: every struct's fields are in
STRICT sorted name order — so the only admissible spelling of a struct
is the canonical one, and the Lean identity agrees with the sorted
canonical-JSON identity on the TypeScript side by construction. Strict
order subsumes no-duplicates, which is what the round trip needs.

On a declaration this is the registry's own discipline read off the
row: the payload is one the id admits and the type parameters are as
many as the id takes. WHICH ids exist is not asked here — that is
settled by the carrier (`DeclarationId.General`); this clause asks only
whether the row's contract is honoured.

On a union it is NONEMPTINESS and nothing else about the shape of the
list: every member well-formed, in whatever order they were written.
The empty union is refused — that is `Never`'s job, and `Never` is not
admitted — and order is deliberately not constrained, because order is
the identity (ratified).

On a tuple it is the elements and the rest type being codes and nothing
more: the element list is nonempty by construction, the rest is at most
one type by construction, and neither the positions nor the optionality
bits are constrained here.

On an enum it is nonemptiness and pairwise-distinct member NAMES. The
empty enum is refused for the same reason the empty union is: it admits
nothing, which is `Never`, which is not admitted. Names are distinct
because the name IS the member's identity. Order is again not
constrained — it is the identity — and neither are the VALUES, which
TypeScript is free to alias.

On a reference it is NONEMPTINESS of the name, and nothing else. The
address discipline and resolvability are both deliberately outside this
predicate — see the constructor. On a suspend it is the thunk being a
code, and nothing else. GUARDEDNESS is not asked here either, and could
not be: it is a property of a DOCUMENT — the table plus its root — not
of a code in isolation, so it lives on `Document.WF`
(`Cas/Schema/Guarded.lean`). -/
def Ast.WF : Ast → Prop
  | .arr a => a.WF
  | .struct fs => List.Pairwise (fun a b => a.1 < b.1) fs ∧ WFFields fs
  | .decl id p ps => id.PayloadWF p ∧ ps.length = id.arity ∧ WFParams ps
  | .union ms _ => ms ≠ [] ∧ WFMembers ms
  | .enum ms =>
    ms ≠ [] ∧ List.Pairwise (fun a b : String × EnumValue => a.1 ≠ b.1) ms
  | .tuple e es r => WFElement e ∧ WFElements es ∧ WFRest r
  | .reference n => n ≠ ""
  | .susp a => a.WF
  | _ => True

def WFFields : List (String × Bool × Ast) → Prop
  | [] => True
  | (_, _, a) :: fs => a.WF ∧ WFFields fs

/-- A declaration's type parameters are codes, each well-formed. -/
def WFParams : List Ast → Prop
  | [] => True
  | a :: as => a.WF ∧ WFParams as

/-- A union's members are codes, each well-formed. Nothing is asked
about the ORDER — order is the identity, so there is no canonical
arrangement to demand. -/
def WFMembers : List Ast → Prop
  | [] => True
  | a :: as => a.WF ∧ WFMembers as

/-- One tuple element is well-formed when its TYPE is. Nothing is asked
of the OPTIONALITY bit — see the note on `El` for why the
trailing-optional discipline is a denotation precondition rather than an
admission one, exactly as discrimination is for unions.

The element families are split head-from-tail like this throughout the
increment, and not out of taste: the tuple carries its first element as
a constructor field rather than inside the list (so that an empty
element list is unspellable), and a clause written over `e :: es` would
build a list Lean's structural recursion cannot see through. -/
def WFElement : Bool × Ast → Prop
  | (_, a) => a.WF

/-- A tuple's remaining elements are codes, each well-formed. Their
POSITION is their identity, so there is nothing to demand about the
arrangement. -/
def WFElements : List (Bool × Ast) → Prop
  | [] => True
  | e :: es => WFElement e ∧ WFElements es

/-- A tuple's rest type, when it has one, is a well-formed code. -/
def WFRest : Option Ast → Prop
  | none => True
  | some a => a.WF

end

/-- The empty union is refused at `WF`: it is `Never`, and `Never` is
not an admitted code. Stated once so the refusal is a theorem and not
just a clause. -/
theorem union_nil_not_wf (m : UnionMode) : ¬ (Ast.union [] m).WF :=
  fun h => h.1 rfl

/-- The empty enum is refused at `WF` for the same reason: an enum with
no members admits no value, which is `Never`, which is not admitted. -/
theorem enum_nil_not_wf : ¬ (Ast.enum []).WF :=
  fun h => h.1 rfl

/-- The empty reference name is refused at `WF`. Effect refuses it too —
`$ref` is `Schema.NonEmptyString` — so the two doors agree on this
spelling by construction rather than by coincidence. -/
theorem reference_empty_not_wf : ¬ (Ast.reference "").WF :=
  fun h => h rfl

/-- A suspend is well-formed exactly when its thunk is: the constructor
adds no discipline of its own, stated once so the fact is citable rather
than read off the clause. -/
theorem susp_wf_iff_thunk {a : Ast} : (Ast.susp a).WF ↔ a.WF := Iff.rfl

/-- Distinct member names never repeat — the `Nodup` reading of the
enum's own clause, stated once so the discipline is citable. -/
theorem enum_names_nodup {ms : List (String × EnumValue)}
    (h : List.Pairwise (fun a b : String × EnumValue => a.1 ≠ b.1) ms) :
    (ms.map (·.1)).Nodup :=
  List.pairwise_map.mpr h

/-- Strictly sorted field names never repeat. -/
theorem sorted_names_nodup {fs : List (String × Bool × Ast)}
    (h : List.Pairwise (fun a b => a.1 < b.1) fs) :
    (fs.map (fun f => f.1)).Nodup := by
  induction h with
  | nil => simp
  | cons hhead _ ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨f, hf, heq⟩
    have hlt := hhead f hf
    rw [heq] at hlt
    exact absurd hlt (String.lt_irrefl _)

end Cas.Schema
