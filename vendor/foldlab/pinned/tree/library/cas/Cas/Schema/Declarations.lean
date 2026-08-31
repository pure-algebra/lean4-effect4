import Cas.Values.Json

/-!
# The declaration registry — the allowlist, as first-order data

Effect's third extension point reduced to content: a `Declaration`
persists as `{_tag, representation: {id, payload}, typeParameters,
checks}` and is revived per id (`SchemaRepresentation.ts:144-153,
502-510`). The id is the whole identity — nothing about a declaration's
meaning lives in a function — so the estate's side of the contract is a
TABLE, in the shape the lift taxonomy already uses for refusal codes
(`Cas/Lift/Taxonomy.lean`): a closed inductive of admitted rows, their
wire spellings, a completeness theorem, and a Nodup guard on the wire.

This is the allowlist the census verdict requires (PLAN P4: an
allowlist is the only safe admission rule for an open annotation bag).
Admission lives HERE and nowhere else: a declaration id that is not a
row of this table has no `Ast` spelling at all, so the carrier cannot
represent an unadmitted declaration and the door
(`Cas.Schema.ingest`) refuses one by name
(`IngestRefusal.unknownDeclaration`).

## Two types, one table

`DeclarationId` is THE registry — every admitted id, row zero first.
`DeclarationId.General` is the subset the GENERAL declaration code
(`Ast.decl`) spells: the registry minus the rows that already have a
dedicated code. Row zero, `foldlab/cas/ref`, is dedicated — it is
`Ast.ref` — and keeping it out of the general code is what keeps the
revision-1 projection injective: one representation, one code, no new
collapse. `General.row_not_dedicated` and `General.row_surjective` are
the completeness guards that make the two types agree; adding a
registry row without dispositioning it is a build error.

Whether `Ast.ref` should LATER become sugar for `Ast.decl` at row zero
is an operator ruling, recorded and not taken here.
-/

namespace Cas.Schema

/-! ## The payload -/

/-- A declaration's payload: Effect's `payload: Json` restricted to the
scalars.

The restriction is the deep-API choice (stipulation S1): scalars are
CANONICAL BY CONSTRUCTION, so the revision-1 representation of a
declaration keeps the unconditional canonicality the rest of the
projection has (`toRepresentationJson_canonical` takes no
well-formedness premise) instead of trading it for a
`Json.Value.Canonical` side condition threaded through every law. Every
admitted row's payload is a scalar today — `foldlab/cas/ref` carries a
kind tag, the three Effect rows carry `null` — so nothing is lost;
a structured payload arrives with the row that needs one, as its own
increment. -/
inductive DeclPayload where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | int (i : Int)
  | str (s : String)
  deriving DecidableEq, Repr

/-- The payload as a JSON value — what `representation.payload`
carries. -/
def DeclPayload.toJson : DeclPayload → Json.Value
  | .null => .null
  | .bool b => .bool b
  | .nat n => .nat n
  | .int i => .int i
  | .str s => .str s

/-- The strict payload decoder: exactly the scalars, nothing
structured. -/
def DeclPayload.ofJson : Json.Value → Option DeclPayload
  | .null => some .null
  | .bool b => some (.bool b)
  | .nat n => some (.nat n)
  | .int i => some (.int i)
  | .str s => some (.str s)
  | _ => none

/-- Payloads are canonically spelled by construction — the point of the
scalar restriction. -/
theorem DeclPayload.toJson_canonical (p : DeclPayload) : p.toJson.Canonical := by
  cases p <;> trivial

/-- The payload round trip. -/
theorem DeclPayload.ofJson_toJson (p : DeclPayload) :
    DeclPayload.ofJson p.toJson = some p := by
  cases p <;> rfl

/-- One payload per JSON value. -/
theorem DeclPayload.toJson_inj {p q : DeclPayload} (h : p.toJson = q.toJson) :
    p = q := by
  have hp := DeclPayload.ofJson_toJson p
  rw [h, DeclPayload.ofJson_toJson q] at hp
  injection hp with hp
  exact hp.symm

/-! ## The registry -/

/-- LAW SM-7: the adopted Effect rows are taken verbatim and mint no
estate identity.

THE declaration registry: every declaration id the store admits,
row zero first. The set grows only by adding a row here — that is what
stipulation S3's "full control" buys, and what an unadmitted id runs
into at the door.

Each row's contract, mirroring the pinned Effect 4 source
(`effect@4.0.0-rc.111`):

| row | wire | arity | payload |
|---|---|---|---|
| `casRef` | `foldlab/cas/ref` | 0 | kind tag, `nat < 256` |
| `effectDate` | `effect/schema/Date` | 0 | `null` |
| `effectUrl` | `effect/schema/URL` | 0 | `null` |
| `effectOption` | `effect/schema/Option` | 1 | `null` |

The three Effect rows are ADOPTED, not minted: each is a built-in that
already ships the full `{id, reviver, toCode, toArbitrary}` contract
(PLAN P3/P4 — a construct speaking Effect's own id inherits Effect's
revival and code generation for free), so admitting them costs the
estate no new identity. Their VALUES have no Lean carrier yet (`El` of
a general declaration is `Empty`); what is admitted here is the
declaration AS CONTENT — a schema the store can hold, address,
re-emit, and hand back to Effect. -/
inductive DeclarationId where
  /-- Row zero — `foldlab/cas/ref`: a typed store reference, payload =
  the expected kind tag. Carried by the dedicated code `Ast.ref`. -/
  | casRef
  /-- `effect/schema/Date` (`Schema.ts:12149`). -/
  | effectDate
  /-- `effect/schema/URL` (`Schema.ts:12021`). -/
  | effectUrl
  /-- `effect/schema/Option` (`Schema.ts:9637`) — the one arity-1 row:
  its single type parameter is the element schema. -/
  | effectOption
  deriving DecidableEq, Repr

/-- The persistence identity, verbatim (`representation.id`). -/
def DeclarationId.wire : DeclarationId → String
  | .casRef => "foldlab/cas/ref"
  | .effectDate => "effect/schema/Date"
  | .effectUrl => "effect/schema/URL"
  | .effectOption => "effect/schema/Option"

/-- The wire spelling read back — the admission test the door applies
to a foreign `representation.id`. -/
def DeclarationId.ofWire : String → Option DeclarationId
  | "foldlab/cas/ref" => some .casRef
  | "effect/schema/Date" => some .effectDate
  | "effect/schema/URL" => some .effectUrl
  | "effect/schema/Option" => some .effectOption
  | _ => none

/-- How many type parameters the row takes. -/
def DeclarationId.arity : DeclarationId → Nat
  | .casRef => 0
  | .effectDate => 0
  | .effectUrl => 0
  | .effectOption => 1

/-- Boolean twin of `PayloadWF` — the row's payload discipline as the
runtime gate. -/
def DeclarationId.payloadWf : DeclarationId → DeclPayload → Bool
  | .casRef, .nat t => decide (t < 256)
  | .effectDate, .null => true
  | .effectUrl, .null => true
  | .effectOption, .null => true
  | _, _ => false

/-- The row's payload discipline: which payloads that id admits. This
is the Lean face of Effect's per-reviver `payloadSchema`. -/
def DeclarationId.PayloadWF : DeclarationId → DeclPayload → Prop
  | .casRef, .nat t => t < 256
  | .effectDate, .null => True
  | .effectUrl, .null => True
  | .effectOption, .null => True
  | _, _ => False

/-- The gate decides exactly the row's payload discipline. -/
theorem DeclarationId.payloadWf_iff (d : DeclarationId) (p : DeclPayload) :
    d.payloadWf p = true ↔ d.PayloadWF p := by
  cases d <;> cases p <;>
    simp [DeclarationId.payloadWf, DeclarationId.PayloadWF]

/-- Whether the row already has a dedicated code in `Ast`. Row zero
does (`Ast.ref`); nothing else does. -/
def DeclarationId.dedicated : DeclarationId → Bool
  | .casRef => true
  | .effectDate => false
  | .effectUrl => false
  | .effectOption => false

/-- Every row, in registry order. -/
def DeclarationId.all : List DeclarationId :=
  [.casRef, .effectDate, .effectUrl, .effectOption]

/-- The table is complete: every row is listed. -/
theorem DeclarationId.all_complete (d : DeclarationId) : d ∈ DeclarationId.all := by
  cases d <;> decide

-- Wire spellings collide with nothing: injectivity of the wire on the
-- registry, checked at elaboration time.
#guard decide ((DeclarationId.all.map DeclarationId.wire).Nodup)

/-- The wire is read back exactly. -/
theorem DeclarationId.ofWire_wire (d : DeclarationId) :
    DeclarationId.ofWire d.wire = some d := by
  cases d <;> rfl

/-! ## The general rows — what `Ast.decl` spells -/

namespace DeclarationId

/-- The registry rows the GENERAL declaration code (`Ast.decl`) spells:
every admitted id except the ones that already have a dedicated code.

Row zero is deliberately absent. `foldlab/cas/ref` is `Ast.ref`, and if
the general code could also spell it, one revision-1 representation
would have two codes — the projection would stop being injective and
`Ast.repNorm` would owe a second collapse. Keeping the dedicated rows
out is what lets the general code land with every revision-1 law
unchanged and NO new collapse. -/
inductive General where
  /-- `effect/schema/Date`. -/
  | date
  /-- `effect/schema/URL`. -/
  | url
  /-- `effect/schema/Option`. -/
  | option
  deriving DecidableEq, Repr

/-- The registry row a general id names. -/
def General.row : General → DeclarationId
  | .date => .effectDate
  | .url => .effectUrl
  | .option => .effectOption

/-- The general id's persistence identity. -/
def General.wire (g : General) : String := g.row.wire

/-- The general id's type-parameter count. -/
def General.arity (g : General) : Nat := g.row.arity

/-- The general id's payload gate. -/
def General.payloadWf (g : General) (p : DeclPayload) : Bool := g.row.payloadWf p

/-- The general id's payload discipline. -/
def General.PayloadWF (g : General) (p : DeclPayload) : Prop := g.row.PayloadWF p

/-- The gate decides exactly the discipline, for general rows too. -/
theorem General.payloadWf_iff (g : General) (p : DeclPayload) :
    g.payloadWf p = true ↔ g.PayloadWF p :=
  DeclarationId.payloadWf_iff g.row p

/-- The general wire spellings read back — the decoder's admission
test. A dedicated row's wire (row zero's) answers `none` here: it is
admitted, but not through this code. -/
def General.ofWire : String → Option General
  | "effect/schema/Date" => some .date
  | "effect/schema/URL" => some .url
  | "effect/schema/Option" => some .option
  | _ => none

/-- The general wire is read back exactly. -/
theorem General.ofWire_wire (g : General) : General.ofWire g.wire = some g := by
  cases g <;> rfl

/-- Every general row, in registry order. -/
def General.all : List General := [.date, .url, .option]

/-- The general table is complete. -/
theorem General.all_complete (g : General) : g ∈ General.all := by
  cases g <;> decide

/-- Guard one: nothing dedicated leaks into the general code, so the
general code never shadows a dedicated one. -/
theorem General.row_not_dedicated (g : General) : g.row.dedicated = false := by
  cases g <;> rfl

/-- Guard two: nothing non-dedicated is left out — every registry row
without a dedicated code is spelled by a general id. Together with
guard one this pins `General` as exactly the non-dedicated part of the
registry, so a new row that forgets its disposition fails to build. -/
theorem General.row_surjective {d : DeclarationId} (h : d.dedicated = false) :
    ∃ g : General, g.row = d := by
  cases d with
  | casRef => exact absurd h (by decide)
  | effectDate => exact ⟨.date, rfl⟩
  | effectUrl => exact ⟨.url, rfl⟩
  | effectOption => exact ⟨.option, rfl⟩

/-- One general id per registry row. -/
theorem General.row_inj {g h : General} (e : g.row = h.row) : g = h := by
  cases g <;> cases h <;> first | rfl | (exact absurd e (by decide))

end DeclarationId

end Cas.Schema
