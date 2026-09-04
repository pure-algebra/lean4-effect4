import Effect4.Schema.Authoring

/-!
# Surface.Kind: the typed embedding

Implements `docs/research/2026-09-04-surface-library-plan.md` §3.

The TyXML idea transposed onto Effect Schema: the slot discipline of a surface
becomes a *kind* on the representation that fills the slot, checked by the
kernel at construction, so an ill-kinded slot is unrepresentable rather than
caught at run time. `Sch refs k` is the subtype; `kindCheck` is its decision
procedure; the containment `text ⊆ struct ⊆ json` is two theorems and `void`
is disjoint from all three.

| | |
| --- | --- |
| Carrier | `Kind` (4 nullary constructors), `Sch refs k` (a representation with a proof of one Bool equation) |
| Operations | `kindCheck`, `Sch.mk`/`Sch.of?`, `Sch.widen`, `jsonRepresentable` |
| Laws | `kindCheck_text_struct`, `kindCheck_struct_json`, `kindCheck_text_json`, `kindCheck_void_iff`, `kindCheck_void_not_json`, `kindCheck_widens` |
| Structure | a chain of three subsets plus one disjoint singleton; the embedding is a subtype |
| Payoff | deletes the construction-time throws of `HttpApiEndpoint.ts:1134-1306` as a class, and answers the `JsonRepresentable` question once for every emitter |
| Anti-vacuity | one admitted and one refused `#guard` per kind, at the end of this module |
| Generation | none: kinds are hand-authored; the emitters read them |

## Why the containment theorems are cheap

`kindCheck` is deliberately *layered*, not four independent walks: `struct` is
`json` conjoined with a shape clause, and `text` is `struct` conjoined with a
property clause. The two containment theorems are then projections of a
conjunction and hold at every fuel, not only at 64. A four-way case analysis
would have made them inductions over the representation for no gain.

## The refusals, by name

`kindCheck` refuses, for every kind, exactly what `Effect4.Arch.Accepts`
refuses on the encoded side: the keywords with no JSON inhabitant
(`undefined`, `void`, `bigint`, `symbol`, `uniqueSymbol`, a bigint literal),
`declaration`, `templateLiteral`, and an object with a repeated property key or
a non-string property key. Two decisions this module makes that the plan's
prose leaves open, recorded here rather than in a comment:

* `void` is refused by `Kind.json` so that `Kind.void` is *disjoint* from the
  other three, which is what the plan's §3 asks for; `kindCheck_void_not_json`
  is the theorem.
* `never` is admitted by `Kind.json`. It has no inhabitant, but it has a JSON
  Schema (`{"not": {}}`) and rc.112 compiles it; emptiness of a payload type is
  not a well-formedness failure of the surface that declares it.

Fuel bounds the two non-structural steps, `reference` through `refs` and
`suspend` through its thunk, exactly as `Arch.Accepts.acceptsShape` does. A
recursive entity therefore exhausts fuel and is refused, which is the v1
refusal row for `suspend`.

## The owed row

The plan's §3 also asks for "`kindCheck` monotone in fuel". It is **not**
proved here and is not claimed: it is an induction over the representation with
the fuel as the measure, and no declaration in this wave rests on it, because
every `Sch` is built at the single fuel 64 and every law above is stated at a
fixed fuel. `jsonOk_mono` is the name it will take.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema

/-! ## The kinds -/

/--
The classification a schema must have to occupy a slot of a surface.

`json` is any JSON-representable representation (bodies, tool results);
`struct` is an `objects` node with string keys and no index signatures
(entities, tool parameters); `text` is a `struct` whose every property is
decodable from URL or header text (path parameters, query, headers); `void` is
the no-content marker for a 201/202/204 success.
-/
inductive Kind where
  /-- Any JSON-representable representation. -/
  | json
  /-- An object with string property keys and no index signatures. -/
  | struct
  /-- A `struct` whose every property type is decodable from text. -/
  | text
  /-- The no-content marker: exactly `Representation.void`. -/
  | void
deriving DecidableEq, Repr, Inhabited

namespace Kind

/-- The kind's spelling in a rule id, a view and a report. -/
def name : Kind → String
  | .json => "json"
  | .struct => "struct"
  | .text => "text"
  | .void => "void"

/-- The closed kind alphabet. -/
def census : List Kind := [.json, .struct, .text, .void]

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 4 := by decide

/-- The census repeats no kind. -/
theorem census_nodup : census.Nodup := by decide

/-- The census covers the alphabet. -/
theorem mem_census (kind : Kind) : kind ∈ census := by
  cases kind <;> decide

/-- Recognise a kind's spelling; nothing else is a kind. -/
def ofName? : String → Option Kind
  | "json" => some .json
  | "struct" => some .struct
  | "text" => some .text
  | "void" => some .void
  | _ => none

/-- Every spelling is recognised, and recognised as its own kind. -/
theorem ofName?_name (kind : Kind) : ofName? kind.name = some kind := by
  cases kind <;> decide

/-- Spellings are distinct, so a report can be read back. Derived from
`ofName?_name` rather than by comparing the sixteen pairs: a `simp` over string
disequalities reaches `Classical.choice` on this toolchain, which this tree's
axiom gate refuses. -/
theorem name_injective {first second : Kind} (h : first.name = second.name) :
    first = second := by
  have recovered := ofName?_name first
  rw [h, ofName?_name second] at recovered
  exact (Option.some.inj recovered).symm

end Kind

/-! ## Property keys -/

/-- The name of a property signature, when its key is a string. A number or a
global-symbol key has no name here and is refused by every kind. -/
def propertyName? : PropertyKey → Option String
  | .string key => some key
  | _ => none

/-- The string names of a property list, in declaration order. -/
def propertyNames (properties : List PropertySignature) : List String :=
  properties.filterMap fun property => propertyName? property.name

/-- No name twice. A repeated key is refused outright: rc.112 parses the
persisted object into a map where the earlier binding vanishes
(`E4-SCHEMA-CE-012`), so nothing about it is shape-decidable. -/
def namesUnique : List String → Bool
  | [] => true
  | first :: rest => !rest.contains first && namesUnique rest

/-! ## The four checks

Each is fuel-bounded through `reference` (resolved in `refs`) and `suspend`
(through its thunk). The callback idiom, a lambda closing over the function at
the smaller fuel, is `Arch.Accepts.acceptsShape`'s, so everything below
reduces under `decide` and `#guard`.
-/

/-- JSON representability: the encoded side of this representation is JSON. -/
def jsonOk (refs : List ReferenceEntry) : Nat → Representation → Bool
  | 0, _ => false
  | fuel + 1, representation =>
    match representation with
    | .declaration _ _ _ _ => false
    | .reference key =>
      match refs.find? (·.key == key.value) with
      | some entry => jsonOk refs fuel entry.representation
      | none => false
    | .suspend _ _ thunk => jsonOk refs fuel thunk
    | .null _ _ => true
    | .undefined _ _ => false
    | .void _ _ => false
    | .never _ _ => true
    | .unknown _ _ => true
    | .any _ _ => true
    | .string _ _ => true
    | .number _ _ => true
    | .boolean _ _ => true
    | .bigint _ _ => false
    | .symbol _ _ => false
    | .literal _ _ (.bigint _) => false
    | .literal _ _ _ => true
    | .uniqueSymbol _ _ _ => false
    | .objectKeyword _ _ => true
    | .enum _ _ _ => true
    | .templateLiteral _ _ _ => false
    | .arrays _ _ elements rest =>
      elements.all (fun element => jsonOk refs fuel element.type) &&
        rest.all (fun item => jsonOk refs fuel item)
    | .objects _ _ properties indexes =>
      properties.all (fun property =>
        (propertyName? property.name).isSome && jsonOk refs fuel property.type) &&
        namesUnique (propertyNames properties) &&
        indexes.all (fun index =>
          jsonOk refs fuel index.parameter && jsonOk refs fuel index.type)
    | .union _ _ types _ => types.all (fun member => jsonOk refs fuel member)

/-- The extra shape clause of `Kind.struct`: an `objects` node with string
property keys and no index signatures. Everything else the kind demands is
already `jsonOk`'s. -/
def structOk (refs : List ReferenceEntry) : Nat → Representation → Bool
  | 0, _ => false
  | fuel + 1, representation =>
    match representation with
    | .objects _ _ properties indexes =>
      indexes.isEmpty &&
        properties.all (fun property => (propertyName? property.name).isSome)
    | .reference key =>
      match refs.find? (·.key == key.value) with
      | some entry => structOk refs fuel entry.representation
      | none => false
    | .suspend _ _ thunk => structOk refs fuel thunk
    | _ => false

/-- A property type decodable from URL or header text: a string, a number, a
boolean, a string or number literal, an enum of those, or a non-empty union of
those. Optionality of the property is not constrained; an optional text
property is admitted. -/
def textual (refs : List ReferenceEntry) : Nat → Representation → Bool
  | 0, _ => false
  | fuel + 1, representation =>
    match representation with
    | .string _ _ => true
    | .number _ _ => true
    | .boolean _ _ => true
    | .literal _ _ (.string _) => true
    | .literal _ _ (.number _) => true
    | .literal _ _ _ => false
    | .enum _ _ _ => true
    | .union _ _ types _ =>
      !types.isEmpty && types.all (fun member => textual refs fuel member)
    | .reference key =>
      match refs.find? (·.key == key.value) with
      | some entry => textual refs fuel entry.representation
      | none => false
    | .suspend _ _ thunk => textual refs fuel thunk
    | _ => false

/-- The extra property clause of `Kind.text`. -/
def textOk (refs : List ReferenceEntry) : Nat → Representation → Bool
  | 0, _ => false
  | fuel + 1, representation =>
    match representation with
    | .objects _ _ properties _ =>
      properties.all (fun property => textual refs fuel property.type)
    | .reference key =>
      match refs.find? (·.key == key.value) with
      | some entry => textOk refs fuel entry.representation
      | none => false
    | .suspend _ _ thunk => textOk refs fuel thunk
    | _ => false

/-- The no-content marker, recognised by its tag alone: no fuel, no reference
resolution, no `suspend`. -/
def voidOk : Representation → Bool
  | .void _ _ => true
  | _ => false

/-! ## The kind check -/

/--
Decide that a representation has a kind, under a document's references table.

Layered on purpose: `struct` is `json` and one shape clause, `text` is `struct`
and one property clause. `void` ignores the fuel because it is a tag test.
-/
def kindCheck (refs : List ReferenceEntry) : Nat → Kind → Representation → Bool
  | fuel, .json, representation => jsonOk refs fuel representation
  | fuel, .struct, representation =>
    jsonOk refs fuel representation && structOk refs fuel representation
  | fuel, .text, representation =>
    jsonOk refs fuel representation &&
      (structOk refs fuel representation && textOk refs fuel representation)
  | _, .void, representation => voidOk representation

/-! ## The laws -/

/-- `text ⊆ struct` as sets of representations, at every fuel. -/
theorem kindCheck_text_struct (refs : List ReferenceEntry) (fuel : Nat)
    (representation : Representation)
    (h : kindCheck refs fuel .text representation = true) :
    kindCheck refs fuel .struct representation = true := by
  simp only [kindCheck, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, h.2.1⟩

/-- `struct ⊆ json` as sets of representations, at every fuel. -/
theorem kindCheck_struct_json (refs : List ReferenceEntry) (fuel : Nat)
    (representation : Representation)
    (h : kindCheck refs fuel .struct representation = true) :
    kindCheck refs fuel .json representation = true := by
  simp only [kindCheck, Bool.and_eq_true] at h
  exact h.1

/-- `text ⊆ json`, the composite. -/
theorem kindCheck_text_json (refs : List ReferenceEntry) (fuel : Nat)
    (representation : Representation)
    (h : kindCheck refs fuel .text representation = true) :
    kindCheck refs fuel .json representation = true :=
  kindCheck_struct_json refs fuel representation
    (kindCheck_text_struct refs fuel representation h)

/-- `void` admits exactly the `Void` tag, at every fuel and under every table. -/
theorem kindCheck_void_iff (refs : List ReferenceEntry) (fuel : Nat)
    (representation : Representation) :
    kindCheck refs fuel .void representation = true ↔
      representation.tag = RepresentationTag.void := by
  cases representation <;> simp [kindCheck, voidOk, Representation.tag]

/-- `void` is disjoint from `json`, and therefore from `struct` and `text`. -/
theorem kindCheck_void_not_json (refs : List ReferenceEntry) (fuel : Nat)
    (representation : Representation)
    (h : kindCheck refs fuel .void representation = true) :
    kindCheck refs fuel .json representation = false := by
  cases representation <;> simp_all [kindCheck, voidOk]
  cases fuel <;> simp [jsonOk]

/-- The containment order `Sch.widen` moves along: `text ≤ struct ≤ json`, and
`void` only with itself. Kinds are not a lattice here and this is not a meet or
a join; it is exactly the reflexive transitive closure of the two containment
theorems above. -/
def Kind.widens : Kind → Kind → Bool
  | .text, .text => true
  | .text, .struct => true
  | .text, .json => true
  | .struct, .struct => true
  | .struct, .json => true
  | .json, .json => true
  | .void, .void => true
  | _, _ => false

/-- Widening preserves the check, at every fuel. -/
theorem kindCheck_widens (refs : List ReferenceEntry) (fuel : Nat)
    (narrow wide : Kind) (h : narrow.widens wide = true)
    (representation : Representation)
    (ok : kindCheck refs fuel narrow representation = true) :
    kindCheck refs fuel wide representation = true := by
  cases narrow <;> cases wide <;>
    simp_all [Kind.widens, kindCheck, Bool.and_eq_true]

/-! ## The typed embedding -/

/--
A representation with a kernel-checked kind, under a fixed references table.

No `DecidableEq` and no `Repr`: the second field is a proof, so the carrier
that is stored, addressed and compared is `rep` itself. `Sch` is the
*construction* boundary, not a stored row.
-/
structure Sch (refs : List ReferenceEntry) (k : Kind) where
  /-- The representation filling the slot. -/
  rep : Representation
  /-- Its kind, checked by the kernel at fuel 64. -/
  ok : kindCheck refs 64 k rep = true

namespace Sch

variable {refs : List ReferenceEntry} {k : Kind}

/-- Construct a kinded schema, or refuse. The only entry point a surface author
needs; `Sch.mk` is available but asks for the proof term. -/
def of? (rep : Representation) : Option (Sch refs k) :=
  if h : kindCheck refs 64 k rep = true then some ⟨rep, h⟩ else none

/-- A successful construction answers the representation it was given. -/
theorem of?_rep (rep : Representation) (value : Sch refs k)
    (h : (Sch.of? (refs := refs) (k := k) rep) = some value) : value.rep = rep := by
  unfold of? at h
  split at h
  · exact (Option.some.inj h).symm ▸ rfl
  · exact absurd h (by simp)

/-- Move a schema along the containment order. -/
def widen (wide : Kind) (h : k.widens wide = true) (value : Sch refs k) :
    Sch refs wide :=
  ⟨value.rep, kindCheck_widens refs 64 k wide h value.rep value.ok⟩

/-- Widening keeps the representation. -/
@[simp] theorem widen_rep (wide : Kind) (h : k.widens wide = true) (value : Sch refs k) :
    (value.widen wide h).rep = value.rep := rfl

end Sch

/-! ## The wire question every emitter asks -/

/-- The survey's missing static check for every wire consumer: is this
representation's encoded side JSON, under this table, at the working fuel? -/
def jsonRepresentable (refs : List ReferenceEntry) (rep : Representation) : Bool :=
  kindCheck refs 64 .json rep

/-- The proposition form, so `decide` and `#guard` both work. -/
def JsonRepresentable (refs : List ReferenceEntry) (rep : Representation) : Prop :=
  jsonRepresentable refs rep = true

instance (refs : List ReferenceEntry) (rep : Representation) :
    Decidable (JsonRepresentable refs rep) := by
  unfold JsonRepresentable; infer_instance

/-- The two faces agree by definition. -/
theorem jsonRepresentable_iff (refs : List ReferenceEntry) (rep : Representation) :
    jsonRepresentable refs rep = true ↔ JsonRepresentable refs rep := Iff.rfl

/-- Every kinded JSON schema is JSON-representable. -/
theorem jsonRepresentable_of_sch {refs : List ReferenceEntry}
    (value : Sch refs .json) : JsonRepresentable refs value.rep := value.ok

/-! ## Anti-vacuity: one admitted and one refused representative per kind -/

private def idStruct : Representation :=
  Schema.struct [Schema.property "id" Schema.string]

private def tagStruct : Representation :=
  Schema.struct [Schema.property "tags" (Schema.array Schema.string)]

private def dupStruct : Representation :=
  Schema.struct [Schema.property "id" Schema.string, Schema.property "id" Schema.number]

-- json
#guard kindCheck [] 64 .json Schema.string = true
#guard kindCheck [] 64 .json Schema.bigint = false

-- struct
#guard kindCheck [] 64 .struct idStruct = true
#guard kindCheck [] 64 .struct Schema.string = false

-- text
#guard kindCheck [] 64 .text idStruct = true
#guard kindCheck [] 64 .text tagStruct = false

-- void
#guard kindCheck [] 64 .void Schema.void = true
#guard kindCheck [] 64 .void Schema.string = false

-- the shared refusals
#guard kindCheck [] 64 .json Schema.undefined = false
#guard kindCheck [] 64 .json Schema.symbol = false
#guard kindCheck [] 64 .json (Schema.literal (.bigint 1)) = false
#guard kindCheck [] 64 .json (Schema.globalSymbol "k") = false
#guard kindCheck [] 64 .json (.templateLiteral none [] []) = false
#guard kindCheck [] 64 .json (.declaration ⟨"d", .null⟩ none [] []) = false
#guard kindCheck [] 64 .json dupStruct = false
#guard kindCheck [] 64 .struct dupStruct = false

-- references resolve in the table, and only there
#guard kindCheck [⟨"User", idStruct⟩] 64 .struct (Schema.reference "User") = true
#guard kindCheck [] 64 .struct (Schema.reference "User") = false

-- a recursive entity exhausts the fuel: the v1 `suspend` refusal row
#guard kindCheck [⟨"Loop", Schema.reference "Loop"⟩] 64 .json (Schema.reference "Loop") = false

end Effect4.Surface
