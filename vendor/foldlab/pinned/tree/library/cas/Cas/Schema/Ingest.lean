import Cas.Schema.SelfCodec
import Cas.Schema.PayloadInj
import Cas.Schema.Guarded
import Cas.Core.Canonicalize.Json

/-!
# The ingestion door — foreign spelling in, canonical code out

The acquisition loop applied to the schema plane: a foreign JSON value
(a hoovered carrier, a model-minted schema — any spelling) is
NORMALIZED by the key-sorting method (`canonValue`), strictly DECODED,
and GATED by the runtime well-formedness check (`Ast.wf`, the boolean
twin of `Ast.WF`). The door is total and every refusal is named; the
foreign spelling dies at the boundary and only substance survives.

The door speaks REVISION 1 — Effect's native persistent
`SchemaRepresentation` document, wrapped in the schema-node envelope.
That is the form the live plane emits (`Ast.envelope`,
`CanonicalSchema.payloadOf`), so `ingest` can ingest what the plane
actually writes. `ingestLegacy` keeps the retired revision-0 tagged
spelling readable for already-addressed nodes; it is a
read-compatibility arm, not the door.

Population through this door is coordination-free by construction:
`ingest` is pure, the answered code is canonical, and admission is
content-addressed — the same code from any spelling lands at the same
address, and duplicates are inert.

What is proved:

- `Ast.wf_iff` — the boolean gate decides exactly `Ast.WF`;
- `ingest_wf` — the door answers only well-formed codes;
- `ingest_envelope` — the canonical image is fixed: a well-formed
  code's own revision-1 envelope ingests to exactly that code's
  revision-1 normal form, and to the code itself when the code is
  `RepNormal` (`ingest_envelope'`). The normalizer is a no-op on the
  envelope because `envelope_canonical` says it is already canonically
  spelled — the exactness law needs no canonicality hypothesis;
- `ingestLegacy_wf` / `ingestLegacy_toJson` — the same two laws for
  the revision-0 arm, unchanged in substance;
- `ingestBytes_wf` / `ingestBytes_payload` — the same two laws for the
  BYTES door (below), which is `Cas.Json.parse` composed with this one.

The declaration allowlist (increment C-decl) is enforced here and
nowhere else on the failure path: `Ast.ofEnvelope` refuses a
`Declaration` whose id is no row of `Cas.Schema.DeclarationId`, and
`refusalOf` names that refusal `unknownDeclaration` instead of letting
it read as a shape failure. The gate `Ast.wf` grew the row's own
discipline with it — payload shape and type-parameter count, read off
the registry — so `ingest_wf` and `ingest_envelope` hold over the grown
carrier with their statements unchanged.

The union code (increment C1) is gated the same way and needs no new
refusal. Its ONE discipline is nonemptiness — the empty union is
`Never`, which is not admitted — so an empty `types` array decodes as a
shape and is refused `illFormed` by the gate, exactly as an unsorted
struct is. A `mode` outside the table is not a union spelling at all
and dies in the decoder as `notASchema`. Member ORDER is never tested,
because order is the identity: there is no canonical arrangement to
demand and nothing on this path sorts.

The enum code (increment C4) is gated the same way and needs no new
refusal either. Its discipline is nonemptiness and pairwise-distinct
member NAMES, both `illFormed` at the gate; a member value outside the
two rows Effect can persist — string and number — is not an enum
spelling at all and dies in the decoder as `notASchema`. Member VALUES
are deliberately unconstrained, because TypeScript aliases are content
the source language spells, and order is again never tested.

The tuple code (increment C2) adds no refusal either, and adds no `wf`
clause worth the name: its elements are nonempty by construction and its
rest is at most one type by construction, so the two disciplines the
admission map asks for are STRUCTURAL. A `rest` of length two or more,
and the empty tuple, therefore die in the decoder as `notASchema` — they
are shapes the carrier cannot spell, which is the same reading `Never`
gets.
-/

namespace Cas.Schema

open Cas.Json

/-- LAW SM-14: these five names are the refusal taxonomy, so an empty
union refuses `illFormed` and an unknown mode `notASchema`.

Why an ingested value was refused. -/
inductive IngestRefusal where
  /-- The normalized value is not a spelling of any code. -/
  | notASchema
  /-- A code, but it breaks the canonical-fields discipline. -/
  | illFormed
  /-- A schema-node envelope, but not revision 1. -/
  | wrongRevision
  /-- A revision-1 document carrying a non-empty `references` table,
  refused by the BARE-CODE arm.

  NARROWED by increment C6 (operator ruling 2026-08-30). It used to mean
  "the admitted subset does not reach the table" — true when the carrier
  had no `Reference` and no `Suspend`. The carrier has both now, and
  `ingestDocument` reads the table; what this name refuses is asking
  `ingest`, which answers ONE CODE, for a document that carries a table.
  The two are different questions and the door names them differently
  rather than answering the narrower one silently. -/
  | nonEmptyReferences
  /-- A revision-1 document whose references table has an UNGUARDED
  CYCLE: a cycle of the reference relation with no `susp` anywhere on
  it. Such a table cannot be BUILT — revival walks the code eagerly, so
  unfolding `A` gives `A` back and no node is ever reached — and the
  table is refused rather than carried.

  This is the refusal `references_guarded_decidable` decides
  (`Cas/Schema/Guarded.lean`), and it is the estate's alone to make:
  Effect's own codec reads an unguarded cycle back without complaint,
  which the spelling probe pins. A cycle that DOES pass through a `susp`
  is admitted — that is ordinary recursion, and it is what Effect emits
  for a recursive schema.

  NARROWED by the break pass (2026-08-30, finding F2). This name used to
  say "resolving one never terminates", which claims more than the door
  decides: `susp` is a DELAY and not a constructor, so a `susp`-guarded
  self-reference is admitted and FORCING it may still diverge —
  `{"A": susp (reference "A")}` runs Effect's validator forever. What is
  refused here is a cycle that closes through constructors alone. See
  `Cas/Schema/Guarded.lean`, "What this does NOT decide". -/
  | unguardedCycle
  /-- A `Declaration` whose `representation.id` is no row of the
  declaration registry (`Cas.Schema.DeclarationId`). The allowlist is
  the only safe admission rule for Effect's open extension point
  (PLAN P4), so an unknown id is refused BY NAME rather than carried as
  opaque content — the carrier has no spelling for it. Admitting one is
  a registry change, not a decoder change. -/
  | unknownDeclaration
  deriving DecidableEq, Repr

/-- Boolean twin of the strict-order clause: every later field name is
above this one — the `Pairwise` shape verbatim, so the agreement proof
needs no transitivity. -/
def pairwiseNames : List (String × Bool × Ast) → Bool
  | [] => true
  | f :: fs => fs.all (fun g => decide (f.1 < g.1)) && pairwiseNames fs

/-- Boolean twin of the enum's distinct-names clause — the `Pairwise`
shape verbatim, like `pairwiseNames`. It asks for DISTINCTNESS and not
for order: an enum's members are never sorted, because their order is
their identity. -/
def distinctEnumNames : List (String × EnumValue) → Bool
  | [] => true
  | m :: ms => ms.all (fun n => decide (m.1 ≠ n.1)) && distinctEnumNames ms

mutual

/-- Boolean twin of `Ast.WF` — the runtime gate of the ingestion
door. -/
def Ast.wf : Ast → Bool
  | .arr a => a.wf
  | .struct fs => pairwiseNames fs && wfFields fs
  | .decl id p ps =>
    id.payloadWf p && decide (ps.length = id.arity) && wfParams ps
  | .union ms _ => !ms.isEmpty && wfMembers ms
  | .enum ms => !ms.isEmpty && distinctEnumNames ms
  | .tuple e es r => wfElement e && wfElements es && wfRest r
  | .reference n => n != ""
  | .susp a => a.wf
  | _ => true

def wfFields : List (String × Bool × Ast) → Bool
  | [] => true
  | (_, _, a) :: fs => a.wf && wfFields fs

/-- Boolean twin of `WFParams`. -/
def wfParams : List Ast → Bool
  | [] => true
  | a :: as => a.wf && wfParams as

/-- Boolean twin of `WFMembers`. Order is not tested — there is
nothing to test, order is the identity. -/
def wfMembers : List Ast → Bool
  | [] => true
  | a :: as => a.wf && wfMembers as

/-- Boolean twin of `WFElement`. The optionality bit is not tested —
there is nothing to test, it is carried. -/
def wfElement : Bool × Ast → Bool
  | (_, a) => a.wf

/-- Boolean twin of `WFElements`. -/
def wfElements : List (Bool × Ast) → Bool
  | [] => true
  | e :: es => wfElement e && wfElements es

/-- Boolean twin of `WFRest`. -/
def wfRest : Option Ast → Bool
  | none => true
  | some a => a.wf

end

theorem pairwiseNames_iff : ∀ fs, pairwiseNames fs = true ↔
    List.Pairwise (fun a b : String × Bool × Ast => a.1 < b.1) fs
  | [] => by simp [pairwiseNames]
  | f :: fs => by
    simp [pairwiseNames, List.pairwise_cons, List.all_eq_true,
      pairwiseNames_iff fs]

theorem distinctEnumNames_iff : ∀ ms, distinctEnumNames ms = true ↔
    List.Pairwise (fun a b : String × EnumValue => a.1 ≠ b.1) ms
  | [] => by simp [distinctEnumNames]
  | m :: ms => by
    simp [distinctEnumNames, List.pairwise_cons, List.all_eq_true,
      distinctEnumNames_iff ms]

mutual

/-- The gate decides exactly the canonical-fields discipline. -/
theorem Ast.wf_iff : ∀ (a : Ast), a.wf = true ↔ a.WF
  | .null => by simp [Ast.wf, Ast.WF]
  | .bool => by simp [Ast.wf, Ast.WF]
  | .int => by simp [Ast.wf, Ast.WF]
  | .str => by simp [Ast.wf, Ast.WF]
  | .lit _ => by simp [Ast.wf, Ast.WF]
  | .ref _ => by simp [Ast.wf, Ast.WF]
  | .arr a => by simp [Ast.wf, Ast.WF, Ast.wf_iff a]
  | .struct fs => by
    simp [Ast.wf, Ast.WF, pairwiseNames_iff fs, wfFields_iff fs]
  | .decl id p ps => by
    simp [Ast.wf, Ast.WF, DeclarationId.General.payloadWf_iff id p,
      wfParams_iff ps, and_assoc]
  | .union ms _ => by
    simp [Ast.wf, Ast.WF, wfMembers_iff ms]
  | .enum ms => by
    simp [Ast.wf, Ast.WF, distinctEnumNames_iff ms]
  | .tuple e es r => by
    simp [Ast.wf, Ast.WF, wfElement_iff e, wfElements_iff es, wfRest_iff r,
      and_assoc]
  | .reference _ => by simp [Ast.wf, Ast.WF]
  | .susp a => by simp [Ast.wf, Ast.WF, Ast.wf_iff a]

theorem wfMembers_iff : ∀ ms, wfMembers ms = true ↔ WFMembers ms
  | [] => by simp [wfMembers, WFMembers]
  | a :: as => by
    simp [wfMembers, WFMembers, Ast.wf_iff a, wfMembers_iff as]

theorem wfElement_iff : ∀ e, wfElement e = true ↔ WFElement e
  | (_, a) => by simp [wfElement, WFElement, Ast.wf_iff a]

theorem wfElements_iff : ∀ es, wfElements es = true ↔ WFElements es
  | [] => by simp [wfElements, WFElements]
  | e :: es => by
    simp [wfElements, WFElements, wfElement_iff e, wfElements_iff es]

theorem wfRest_iff : ∀ r, wfRest r = true ↔ WFRest r
  | none => by simp [wfRest, WFRest]
  | some a => by simp [wfRest, WFRest, Ast.wf_iff a]

theorem wfFields_iff : ∀ fs, wfFields fs = true ↔ WFFields fs
  | [] => by simp [wfFields, WFFields]
  | (_, _, a) :: fs => by
    simp [wfFields, WFFields, Ast.wf_iff a, wfFields_iff fs]

theorem wfParams_iff : ∀ ps, wfParams ps = true ↔ WFParams ps
  | [] => by simp [wfParams, WFParams]
  | a :: as => by
    simp [wfParams, WFParams, Ast.wf_iff a, wfParams_iff as]

end

/-! ## The door — revision 1 -/

/-- One `Declaration` node, tested against the registry: is its
`representation.id` no row at all? -/
private def unknownDeclarationHere : List (String × Json.Value) → Bool
  | [("_tag", .str "Declaration"), ("checks", _),
     ("representation", .obj [("id", .str w), ("payload", _)]),
     ("typeParameters", _)] => (DeclarationId.ofWire w).isNone
  | _ => false

mutual

/-- Does the representation carry a declaration the registry does not
admit? A structural search over the normalized value — it decides
nothing (`Ast.ofEnvelope` alone decides admission); it only tells the
refusal apart from a shape failure. -/
private def unknownDeclarationIn : Json.Value → Bool
  | .obj fields => unknownDeclarationHere fields || unknownDeclarationFields fields
  | .arr xs => unknownDeclarationItems xs
  | _ => false

private def unknownDeclarationFields : List (String × Json.Value) → Bool
  | [] => false
  | (_, v) :: rest => unknownDeclarationIn v || unknownDeclarationFields rest

private def unknownDeclarationItems : List Json.Value → Bool
  | [] => false
  | v :: rest => unknownDeclarationIn v || unknownDeclarationItems rest

end

/-- The refusal namer: a pure diagnostic on the failure path, walking
the envelope's shell and — for the declaration allowlist — the
representation AND the references table it wraps. It never decides
admission; that is the decoder's job alone, so there is exactly one
decoder behind the door and the refusal name cannot disagree with it.

This is the BARE-CODE arm's namer and it is unchanged by C6: that arm
answers one code, so a table is still a refusal for it and still
`nonEmptyReferences`. The DOCUMENT door has its own namer below, which
does not carry that branch — it reads the table. -/
private def refusalOf : Json.Value → IngestRefusal
  | .obj [("revision", .nat r), ("value", d)] =>
    if r = schemaRevision then
      match d with
      | .obj [("references", .obj refs), ("representation", rep)] =>
        if !refs.isEmpty then .nonEmptyReferences
        else if unknownDeclarationIn rep then .unknownDeclaration
        else .notASchema
      | _ => .notASchema
    else .wrongRevision
  | _ => .notASchema

/-- The DOCUMENT door's namer. Same walk, minus the table branch — a
document that carries a table is this door's business, not a shape
failure — and the allowlist search now covers the table's codes too. -/
private def documentRefusalOf : Json.Value → IngestRefusal
  | .obj [("revision", .nat r), ("value", d)] =>
    if r = schemaRevision then
      match d with
      | .obj [("references", .obj refs), ("representation", rep)] =>
        if unknownDeclarationIn rep || unknownDeclarationFields refs then
          .unknownDeclaration
        else .notASchema
      | _ => .notASchema
    else .wrongRevision
  | _ => .notASchema

/-! ## The document door — revision 1, table and all

`ingestDocument` is the door the TypeScript gate mirrors: it reads the
whole document, gates every code on the canonical-fields discipline, and
gates the TABLE on guardedness. `ingest` below is the BARE-CODE arm of
it, kept at its own name and its own type so that every law already
proved about it stands unchanged. -/

/-- Every table entry's code is well-formed. -/
def WFReferences : List (String × Ast) → Prop
  | [] => True
  | (_, a) :: rest => a.WF ∧ WFReferences rest

/-- Well-formedness of a document: the codes' own discipline, the
table's canonical-key discipline, and GUARDEDNESS.

The strict name order is asked for exactly the reason `.struct` asks it
of fields — it is what makes the canonical spelling unique — and
nonemptiness of a name for the reason `.reference` asks it of a pointer:
`$ref` is `Schema.NonEmptyString`, so a name no pointer can spell is
dead weight the table should not carry. -/
def Document.WF (d : Document) : Prop :=
  List.Pairwise (fun a b : String × Ast => a.1 < b.1) d.references
    ∧ (∀ e ∈ d.references, e.1 ≠ "")
    ∧ WFReferences d.references
    ∧ d.representation.WF
    ∧ d.Guarded

/-- Boolean twin of `WFReferences`. -/
def wfReferences : List (String × Ast) → Bool
  | [] => true
  | (_, a) :: rest => a.wf && wfReferences rest

/-- Boolean twin of the strict-name-order clause. -/
def pairwiseRefNames : List (String × Ast) → Bool
  | [] => true
  | e :: rest => rest.all (fun f => decide (e.1 < f.1)) && pairwiseRefNames rest

theorem wfReferences_iff : ∀ rs, wfReferences rs = true ↔ WFReferences rs
  | [] => by simp [wfReferences, WFReferences]
  | (_, a) :: rest => by
    simp [wfReferences, WFReferences, Ast.wf_iff a, wfReferences_iff rest]

theorem pairwiseRefNames_iff : ∀ rs, pairwiseRefNames rs = true ↔
    List.Pairwise (fun a b : String × Ast => a.1 < b.1) rs
  | [] => by simp [pairwiseRefNames]
  | e :: rest => by
    simp [pairwiseRefNames, List.pairwise_cons, List.all_eq_true,
      pairwiseRefNames_iff rest]

/-- Boolean twin of `Document.WF` — the runtime gate of the document
door. The guardedness conjunct is `Document.guardedMemo`, the walk that
settles each name once, and `references_guarded_decidable_memo` is what
says it decides the real property rather than approximating it. -/
def Document.wf (d : Document) : Bool :=
  pairwiseRefNames d.references
    && d.references.all (fun e => e.1 != "")
    && wfReferences d.references
    && d.representation.wf
    && d.guardedMemo

/-- The gate decides exactly the discipline. -/
theorem Document.wf_iff (d : Document) : d.wf = true ↔ d.WF := by
  simp only [Document.wf, Document.WF, Bool.and_eq_true, List.all_eq_true,
    pairwiseRefNames_iff, wfReferences_iff, Ast.wf_iff,
    references_guarded_decidable_memo, and_assoc]
  constructor
  · rintro ⟨hp, hne, hwr, hrep, hg⟩
    exact ⟨hp, fun e he => by simpa using hne e he, hwr, hrep, hg⟩
  · rintro ⟨hp, hne, hwr, hrep, hg⟩
    exact ⟨hp, fun e he => by simpa using hne e he, hwr, hrep, hg⟩

/-- Which refusal a decoded-but-rejected document earns. Guardedness is
named separately from the canonical-fields discipline because the two
are different defects and the door's A-grade prose has to say which.

The ORDER is this door's, and the TypeScript gate mirrors it rather
than choosing its own (R10): a document with two defects is named for
the cycle. -/
private def documentRefusal (d : Document) : IngestRefusal :=
  if d.guardedMemo then .illFormed else .unguardedCycle

/-- A key list with a repeat in it. -/
def hasRepeatedKey : List String → Bool
  | [] => false
  | k :: ks => ks.contains k || hasRepeatedKey ks

/-- Does the envelope's references table carry one name TWICE?

Asked BEFORE the document is decoded, and answered from the spelling
rather than from either reader's habits. A duplicate key is where the
two hosts stop reading the same document out of one byte string:
`Cas.Json.parse` keeps both pairs and `Document.lookup` takes the
FIRST; `JSON.parse` keeps the LAST. So
`{"A":{"$ref":"A",…},"A":{"_tag":"String",…}}` is a cycle to Lean and
an ordinary table to TypeScript, and swapping the two pairs swaps which
door sees it — the break pass exhibited both directions (PDD-3 finding
F1, `contracts/attacks/PDD-3/Attack.lean` §7).

Neither reading is more right, so the door refuses the spelling instead
of picking a winner. It costs nothing real: a canonical spelling has
its keys in strict ascending order, so it has no duplicate to lose.

ASSUMED RULING, flagged for operator override in the packet. Scoped to
the references table on purpose — a duplicate key elsewhere (a repeated
`_tag` on a node) splits the same way, predates this increment, and the
two doors have not been reconciled on it. -/
def duplicateReferenceKey : Json.Value → Bool
  | .obj [("revision", _),
      ("value", .obj [("references", .obj refs), ("representation", _)])] =>
    hasRepeatedKey (refs.map (·.1))
  | _ => false

/-- The door, on an ALREADY canonical value — so the normalizer runs
once and the refusal order is readable in one place: the spelling
first, then the decoder, then the disciplines. -/
private def ingestDocumentCanonical (c : Json.Value) :
    Except IngestRefusal Document :=
  if duplicateReferenceKey c then .error .illFormed
  else
    match Document.ofEnvelope c with
    | some d => if d.wf then .ok d else .error (documentRefusal d)
    | none => .error (documentRefusalOf c)

/-- THE DOCUMENT DOOR: normalize the spelling, refuse a table that
names one entry twice, strictly decode the revision-1 envelope with its
table, gate every code and the table's guardedness. -/
def ingestDocument (v : Json.Value) : Except IngestRefusal Document :=
  ingestDocumentCanonical (canonValue v)

/-- Soundness of the document door. -/
theorem ingestDocument_wf {v : Json.Value} {d : Document}
    (h : ingestDocument v = .ok d) : d.WF := by
  unfold ingestDocument ingestDocumentCanonical at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        next hw => exact (Document.wf_iff _).mp hw
      · cases h
    · cases h

/-- The door answers only GUARDED tables — the half of soundness the
C6 theorem carries, stated on its own so the claim is citable without
unfolding `Document.WF`. -/
theorem ingestDocument_guarded {v : Json.Value} {d : Document}
    (h : ingestDocument v = .ok d) : d.Guarded :=
  (ingestDocument_wf h).2.2.2.2

/-- THE door, BARE-CODE arm: unchanged by C6, in definition and in
every law below.

It answers ONE CODE, so it keeps refusing a document that carries a
table, by the same name as before. `ingestDocument` above is the arm
that reads one. The two agree wherever both apply — `ingestDocument_nil`
below is that agreement — and they are kept as two definitions rather
than one because routing this arm through the document door would move
statements that are frozen. -/
def ingest (v : Json.Value) : Except IngestRefusal Ast :=
  match Ast.ofEnvelope (canonValue v) with
  | some a => if a.wf then .ok a else .error .illFormed
  | none => .error (refusalOf (canonValue v))

/-- Soundness: the door answers only well-formed codes. -/
theorem ingest_wf {v : Json.Value} {a : Ast}
    (h : ingest v = .ok a) : a.WF := by
  unfold ingest at h
  split at h
  · split at h
    · cases h
      next hw => exact (Ast.wf_iff _).mp hw
    · cases h
  · cases h

/-- Exactness on the canonical image: a well-formed code's own
revision-1 envelope ingests to that code's revision-1 normal form. The
normalizer is a no-op here — `envelope_canonical` says the envelope is
already canonically spelled — so no canonicality hypothesis is
needed. -/
theorem ingest_envelope {a : Ast} (ha : a.WF) :
    ingest a.envelope = .ok a.repNorm := by
  unfold ingest
  rw [canonValue_of_canonical _ (envelope_canonical a), ofEnvelope_envelope a]
  simp [(Ast.wf_iff _).mpr (Ast.repNorm_wf a ha)]

/-- THE TWO DOORS AGREE where both apply: a bare code's own envelope
goes through the document door to the same code, carried in a document
with an empty table.

This is what makes the pair honest rather than a fork. The document
door's extra clauses are all vacuous on an empty table — there are no
names to order, none to be nonempty, no entry to be well formed, and no
edge to cycle — so the only surviving condition is the code's own, which
is the bare arm's condition exactly. -/
theorem ingestDocument_nil {a : Ast} (ha : a.WF) :
    ingestDocument a.envelope = .ok (Document.mk [] a.repNorm) := by
  unfold ingestDocument ingestDocumentCanonical
  rw [canonValue_of_canonical _ (envelope_canonical a),
    show a.envelope = (Document.mk [] a).envelope from rfl,
    if_neg (by simp [duplicateReferenceKey, Document.envelope,
      Document.representationDocument, referencesToJson, hasRepeatedKey]),
    Document.ofEnvelope_envelope (Document.mk [] a)]
  simp only [Document.repNorm, List.map_nil]
  rw [if_pos]
  simp only [Document.wf, pairwiseRefNames, wfReferences, Document.guardedMemo,
    Document.settleAll, Document.names, List.map_nil, List.all_nil,
    Bool.and_true, Option.isSome_some,
    (Ast.wf_iff _).mpr (Ast.repNorm_wf a ha)]

/-- Exactness on the nose, for the codes the revision-1 projection
distinguishes: the door is the identity on the canonical image, so the
quotient it computes agrees with the projection's round trip. -/
theorem ingest_envelope' {a : Ast} (ha : a.WF) (hn : a.RepNormal) :
    ingest a.envelope = .ok a := by
  rw [ingest_envelope ha, hn]

/-! ## The legacy arm — revision 0

The retired tagged projection (`Ast.toJson`), kept readable so
already-addressed revision-0 schema nodes can still be decoded. It is
NOT the door: it takes the bare tagged value, has no envelope, and
mints nothing new. -/

/-- The revision-0 read-compatibility arm: normalize the spelling,
decode the retired tagged projection, gate on the same discipline. -/
def ingestLegacy (v : Json.Value) : Except IngestRefusal Ast :=
  match Ast.ofJson (canonValue v) with
  | none => .error .notASchema
  | some a => if a.wf then .ok a else .error .illFormed

/-- Soundness of the legacy arm: it too answers only well-formed
codes. -/
theorem ingestLegacy_wf {v : Json.Value} {a : Ast}
    (h : ingestLegacy v = .ok a) : a.WF := by
  unfold ingestLegacy at h
  split at h
  · cases h
  · split at h
    · cases h
      next hw => exact (Ast.wf_iff _).mp hw
    · cases h

/-- The legacy arm's canonical image is fixed: a well-formed code's own
revision-0 spelling ingests to exactly itself. Revision 0 keeps a null
literal as a literal, so no normal form intervenes. -/
theorem ingestLegacy_toJson {a : Ast} (ha : a.WF) :
    ingestLegacy a.toJson = .ok a := by
  unfold ingestLegacy
  rw [canonValue_of_canonical _ (toJson_canonical a ha), ofJson_toJson]
  simp [(Ast.wf_iff a).mpr ha]

/-! ## The declaration allowlist at the door — worked, at elaboration

The two facts the theorems above state in general, run on the general
declaration code so the door's behaviour is visible in the source:
an admitted declaration goes in and comes back with the same payload
bytes, and an id outside the registry is refused BY NAME. -/

/-- `Schema.Option(Schema.String)` as a code — an admitted arity-1
declaration over an admitted element. -/
private def optionOfString : Ast := .decl .option .null [.str]

-- An admitted declaration ingests to itself: same canonical bytes out.
#guard (match ingest optionOfString.envelope with
        | .ok a => a.payload == optionOfString.payload
        | .error _ => false)

-- An id outside the registry is refused by name, not silently carried.
#guard (match ingest (.obj [("revision", .nat schemaRevision),
          ("value", .obj [("references", .obj []),
            ("representation", .obj [
              ("_tag", .str "Declaration"), ("checks", .arr []),
              ("representation", .obj [
                ("id", .str "vendor/x/Widget"), ("payload", .null)]),
              ("typeParameters", .arr [])])])]) with
        | .error .unknownDeclaration => true
        | _ => false)

-- An admitted id with a payload its row does not admit is a different
-- refusal: the allowlist passed, the row's own discipline did not.
#guard (match ingest (Ast.decl .date (.str "not a null payload") []).envelope with
        | .error .illFormed => true
        | _ => false)

/-! ## Order is identity at the door — worked, at elaboration

The ratified identity calls for the union code (C1), run through the
door so the carrier's behaviour is visible in the source rather than
only stated in a docstring. -/

/-- Two unions over the same members in different orders. -/
private def zebraFirst : Ast :=
  .union [.lit (.str "zebra"), .lit (.str "alpha")] .oneOf

private def alphaFirst : Ast :=
  .union [.lit (.str "alpha"), .lit (.str "zebra")] .oneOf

-- ORDER IS IDENTITY: reordering the members is a DIFFERENT code with
-- DIFFERENT payload bytes. Nothing sorts on the way in or out.
#guard zebraFirst.payload != alphaFirst.payload

-- Both survive the door as themselves, in the order they were written.
#guard (match ingest zebraFirst.envelope, ingest alphaFirst.envelope with
        | .ok a, .ok b => a.payload == zebraFirst.payload &&
            b.payload == alphaFirst.payload
        | _, _ => false)

-- THE MODE IS DATA: the same members under the two modes are two
-- codes, and both are admitted immediately (open ruling 2, resolved as
-- proposed — carriage is faithful, validation semantics are staged).
#guard (Ast.union [.str, .bool] .anyOf).payload !=
  (Ast.union [.str, .bool] .oneOf).payload

#guard (match ingest (Ast.union [.str, .bool] .anyOf).envelope,
              ingest (Ast.union [.str, .bool] .oneOf).envelope with
        | .ok _, .ok _ => true
        | _, _ => false)

-- NO FLATTENING: a nested union is not its flattening.
#guard (Ast.union [.str, .union [.bool, .int] .anyOf] .anyOf).payload !=
  (Ast.union [.str, .bool, .int] .anyOf).payload

-- THE EMPTY UNION IS REFUSED at the gate — it is `Never`, and `Never`
-- is not admitted. The decoder reads its shape; the discipline is what
-- turns it away.
#guard (match ingest (Ast.union [] .anyOf).envelope with
        | .error .illFormed => true
        | _ => false)

-- A mode that is no row of the table is not a union at all: the
-- spelling dies in the decoder, so the value is not a schema.
#guard (match ingest (.obj [("revision", .nat schemaRevision),
          ("value", .obj [("references", .obj []),
            ("representation", .obj [
              ("_tag", .str "Union"), ("checks", .arr []),
              ("mode", .str "allOf"),
              ("types", .arr [(Ast.str).toRepresentationJson])])])]) with
        | .error .notASchema => true
        | _ => false)

/-! ## The enum at the door — worked, at elaboration

The C4 calls, run through the door so the carrier's behaviour is in the
source and not only in a docstring. -/

private def direction : Ast :=
  .enum [("Up", .str "Up"), ("Down", .str "Down")]

private def directionReversed : Ast :=
  .enum [("Down", .str "Down"), ("Up", .str "Up")]

-- ORDER IS IDENTITY: reordering the members is a DIFFERENT code with
-- DIFFERENT payload bytes. Effect reads `Object.keys` order, which is
-- source order, and nothing on this path sorts.
#guard direction.payload != directionReversed.payload

-- Both survive the door as themselves, in the order they were written.
#guard (match ingest direction.envelope, ingest directionReversed.envelope with
        | .ok a, .ok b => a.payload == direction.payload &&
            b.payload == directionReversed.payload
        | _, _ => false)

-- A numeric enum, including the alias TypeScript admits: two members at
-- one value, which `WF` deliberately does NOT refuse — the name is the
-- identity, the value is not.
#guard (match ingest (Ast.enum [("A", .int ⟨1, by decide⟩),
          ("B", .int ⟨1, by decide⟩)]).envelope with
        | .ok _ => true
        | .error _ => false)

-- THE EMPTY ENUM IS REFUSED at the gate — like the empty union, it
-- admits nothing, which is `Never`, which is not admitted.
#guard (match ingest (Ast.enum []).envelope with
        | .error .illFormed => true
        | _ => false)

-- REPEATED NAMES are refused: the name is the member's identity, so two
-- members cannot share one.
#guard (match ingest (Ast.enum [("A", .str "x"), ("A", .str "y")]).envelope with
        | .error .illFormed => true
        | _ => false)

-- A member value outside the two admitted rows — a BOOLEAN, which
-- Effect's `Enum` cannot persist — is not an enum spelling at all and
-- dies in the decoder.
#guard (match ingest (.obj [("revision", .nat schemaRevision),
          ("value", .obj [("references", .obj []),
            ("representation", .obj [
              ("_tag", .str "Enum"), ("checks", .arr []),
              ("enums", .arr [.arr [.str "A",
                .obj [("type", .str "boolean"), ("value", .bool true)]]])])])]) with
        | .error .notASchema => true
        | _ => false)

/-! ## The tuple at the door — worked, at elaboration

The C2 calls, run through the door. The two that matter are the ones the
carrier makes structural rather than clausal: a tuple cannot spell the
plain array's representation, and a `rest` of length two has no spelling
at all. -/

private def pair : Ast := .tuple (false, .str) [(false, .int)] none

private def pairSwapped : Ast := .tuple (false, .int) [(false, .str)] none

private def headAndTail : Ast := .tuple (false, .str) [] (some .int)

-- POSITION IS IDENTITY: swapping two elements is a DIFFERENT code with
-- DIFFERENT payload bytes.
#guard pair.payload != pairSwapped.payload

-- Both survive the door as themselves, positions intact.
#guard (match ingest pair.envelope, ingest pairSwapped.envelope with
        | .ok a, .ok b => a.payload == pair.payload &&
            b.payload == pairSwapped.payload
        | _, _ => false)

-- The OPTIONALITY BIT IS DATA: the same element types under different
-- optionality are two codes, and both are admitted.
#guard (Ast.tuple (false, .str) [(false, .int)] none).payload !=
  (Ast.tuple (false, .str) [(true, .int)] none).payload

#guard (match ingest (Ast.tuple (false, .str) [(true, .int)] none).envelope with
        | .ok _ => true
        | .error _ => false)

-- A tuple with a rest type — `Schema.TupleWithRest` — round-trips too.
#guard (match ingest headAndTail.envelope with
        | .ok a => a.payload == headAndTail.payload
        | .error _ => false)

-- THE PLAIN ARRAY KEEPS ITS OWN SPELLING. `.arr` is `{elements:[],
-- rest:[t]}`, and no tuple code can spell that, because `Ast.tuple`
-- takes a first element. So there is no second collapse to normalize
-- away, and the array's bytes are unchanged by this increment.
#guard (match ingest (Ast.arr .str).envelope with
        | .ok a => a.payload == (Ast.arr .str).payload
        | .error _ => false)

-- A `rest` OF LENGTH TWO has no spelling on this side — the carrier
-- holds an `Option` — so the deferred trailing-rest semantics are
-- refused in the DECODER, by shape, and not by a clause that could
-- drift.
#guard (match ingest (.obj [("revision", .nat schemaRevision),
          ("value", .obj [("references", .obj []),
            ("representation", .obj [
              ("_tag", .str "Arrays"), ("checks", .arr []),
              ("elements", .arr [.obj [("isOptional", .bool false),
                ("type", (Ast.str).toRepresentationJson)]]),
              ("rest", .arr [(Ast.int).toRepresentationJson,
                (Ast.bool).toRepresentationJson])])])]) with
        | .error .notASchema => true
        | _ => false)

-- THE EMPTY TUPLE — `{elements:[], rest:[]}` — is still not admitted.
-- It was not admitted before this increment either; nothing is retired.
#guard (match ingest (.obj [("revision", .nat schemaRevision),
          ("value", .obj [("references", .obj []),
            ("representation", .obj [
              ("_tag", .str "Arrays"), ("checks", .arr []),
              ("elements", .arr []), ("rest", .arr [])])])]) with
        | .error .notASchema => true
        | _ => false)

/-! ## The C6 codes at the door — worked, at elaboration

The round-trip witnesses the ticket asks for, one per new case, run
through the door so the carrier's behaviour is in the source. The
GUARDEDNESS calls are not here — they are document-level and live with
the document door (`Cas/Schema/Guarded.lean`). -/

private def nodeRef : Ast := .reference "Node"

/-- THE admitted check spelling, read off the `Number` node's own
projection rather than retyped — the same move `Admission.lean` makes. -/
private def theIntCheck : Json.Value :=
  match (Ast.int).toRepresentationJson with
  | .obj [_, ("checks", .arr [c])] => c
  | _ => .null

private def suspendedList : Ast :=
  .susp (.struct [("next", true, .reference "Node"), ("value", false, .str)])

-- A reference survives the door as itself: same canonical bytes out.
#guard (match ingest nodeRef.envelope with
        | .ok a => a.payload == nodeRef.payload
        | .error _ => false)

-- A suspend round-trips with its thunk intact, nested code and all.
#guard (match ingest suspendedList.envelope with
        | .ok a => a.payload == suspendedList.payload
        | .error _ => false)

-- THE TWO ARE DIFFERENT CODES, and that is the whole point of the
-- ruling: a name is not a thunk, so `reference "x"` and a suspend over
-- anything are two codes at two addresses.
#guard nodeRef.payload != (Ast.susp .str).payload

-- The EMPTY reference name is refused at the gate — Effect refuses it
-- too (`$ref` is `Schema.NonEmptyString`), so the two doors agree here
-- by construction.
#guard (match ingest (Ast.reference "").envelope with
        | .error .illFormed => true
        | _ => false)

-- A `Reference` carrying a `checks` key is not a reference spelling at
-- all: Effect's own node has exactly two keys, and the decoder is exact.
#guard (match ingest (.obj [("revision", .nat schemaRevision),
          ("value", .obj [("references", .obj []),
            ("representation", .obj [("$ref", .str "Node"),
              ("_tag", .str "Reference"), ("checks", .arr [])])])]) with
        | .error .notASchema => true
        | _ => false)

-- A `Suspend` carrying a check dies the same way. Effect's own field is
-- the EMPTY tuple, so a non-empty one is not a Suspend at either door.
#guard (match ingest (.obj [("revision", .nat schemaRevision),
          ("value", .obj [("references", .obj []),
            ("representation", .obj [("_tag", .str "Suspend"),
              ("checks", .arr [theIntCheck]),
              ("thunk", (Ast.str).toRepresentationJson)])])]) with
        | .error .notASchema => true
        | _ => false)

/-! ## Guardedness at the door — worked, at elaboration

The C6 witnesses. These are the falsifier the ticket names: an
unguarded cycle the door must refuse, and — its necessary partner,
without which "refuse everything" would pass — a guarded cycle the door
must ADMIT. -/

/-- The linked list, exactly as Effect emits it for a recursive schema:
the root is a reference into the table, and the recursive knot is a
`susp` whose thunk reaches the entry again. Taken from the spelling
probe's own output. -/
def guardedList : Document :=
  { references := [("Node",
      .struct [("next", false, .susp (.union [.reference "Node", .null] .anyOf)),
        ("value", false, .str)])],
    representation := .reference "Node" }

/-- An ALIAS cycle: `A` is `B` and `B` is `A`, with no guard anywhere.
Resolving it never reaches a node. Effect's own codec reads it back
without complaint — the probe pins that — so this door is the only one
that refuses it. -/
def aliasCycle : Document :=
  { references := [("A", .reference "B"), ("B", .reference "A")],
    representation := .reference "A" }

/-- A STRUCTURAL cycle with no guard: `A = {next: A}` spelled with a
bare reference where Effect would have written a `susp`. Effect's
generator never emits this shape; the representation can spell it, so
the door has to answer it. -/
def bareStructCycle : Document :=
  { references := [("A", .struct [("next", false, .reference "A")])],
    representation := .reference "A" }

-- THE GUARD IS WHAT DOES IT. The linked list's table has a cycle —
-- `Node` reaches `Node` — and it passes through the `susp`, so the
-- non-suspend relation has no edge at all and the door admits it.
#guard guardedList.guarded
#guard (match guardedList.references with
        | [(_, a)] => a.bareRefs == []
        | _ => false)

-- Both unguarded cycles are refused, and refused BY NAME: the door
-- says which discipline failed, not merely that something did.
#guard !aliasCycle.guarded
#guard !bareStructCycle.guarded

-- The walk the door RUNS answers the same, on all three. A name on a
-- cycle never enters the memo, because a name is memoized on the way
-- back out and the walk never gets there.
#guard guardedList.guardedMemo
#guard !aliasCycle.guardedMemo
#guard !bareStructCycle.guardedMemo

/-- The alias table really does have a cycle, and the proof EXHIBITS
it rather than deciding it: `A` steps to `B`, `B` edges back to `A`.
Stated so the witness is a derivation the reader can check, not an
appeal to the same procedure the theorem is about. -/
theorem aliasCycle_cyclic : aliasCycle.Cyclic := by
  refine ⟨"A", .step (m := "B") ?_ (.edge ?_)⟩
  · show "B" ∈ aliasCycle.out "A"
    decide
  · show "A" ∈ aliasCycle.out "B"
    decide

/-- The structural cycle likewise — one self-edge, straight through a
struct field with no guard on it. -/
theorem bareStructCycle_cyclic : bareStructCycle.Cyclic := by
  refine ⟨"A", .edge ?_⟩
  show "A" ∈ bareStructCycle.out "A"
  decide

/-- THE FALSIFIER, discharged. Both unguarded tables are refused, and by
the C6 theorem that refusal is not an artefact of the procedure: they
are genuinely cyclic, so no correct door may admit them. -/
theorem unguarded_alias_cycle_refused : ¬ aliasCycle.Guarded :=
  fun h => h aliasCycle_cyclic

theorem unguarded_struct_cycle_refused : ¬ bareStructCycle.Guarded :=
  fun h => h bareStructCycle_cyclic

/-- THE PARTNER FALSIFIER, without which "refuse everything" would pass:
a GUARDED cycle — ordinary recursion, and exactly what Effect emits for
a recursive schema — is admitted. The proof runs through
`references_guarded_decidable`, which is what makes the check's answer
mean the absence of a cycle. -/
theorem guarded_list_admitted : guardedList.Guarded :=
  (references_guarded_decidable guardedList).mp (by decide)

-- The door answers accordingly, by name. `#guard` and not `rfl`: the
-- door runs `canonValue`, whose key ordering is `String.lt`, and that
-- does not reduce in the kernel — the same reason every other refusal
-- call in this file is a `#guard`.
#guard (match ingestDocument aliasCycle.envelope with
        | .error .unguardedCycle => true
        | _ => false)

#guard (match ingestDocument bareStructCycle.envelope with
        | .error .unguardedCycle => true
        | _ => false)

#guard (match ingestDocument guardedList.envelope with
        | .ok d => d.payload == guardedList.payload
        | .error _ => false)

-- The bare-code arm refuses the lot by its own name: they carry tables,
-- and that arm answers one code.
#guard (match ingest guardedList.envelope with
        | .error .nonEmptyReferences => true
        | _ => false)

/-! ### A table with EDGES on it, admitted

The break pass's F4. Both admitted C6 witnesses above have an EMPTY
bare-edge relation — `guardedList`'s only reference sits under the
`susp`, and a table of plain strings has no references at all — so a
door with fuel ZERO, one that never follows an edge, agreed with this
one on all 71 corpus rows. These two are the missing witnesses: acyclic
tables the door admits after actually walking them. -/

/-- One acyclic edge: `A` names `B`, and `B` is a code. -/
def refChain : Document :=
  { references := [("A", .reference "B"), ("B", .str)],
    representation := .reference "A" }

/-- Two edges, so the search recurses more than once. -/
def refChainTwo : Document :=
  { references := [("A", .reference "B"), ("B", .reference "C"), ("C", .str)],
    representation := .reference "A" }

-- The relations are NON-EMPTY, which is the whole point of the pair.
#guard refChain.out "A" == ["B"]
#guard refChainTwo.out "A" == ["B"]
#guard refChainTwo.out "B" == ["C"]

#guard refChain.guardedMemo
#guard refChainTwo.guardedMemo

theorem refChain_guarded : refChain.Guarded :=
  (references_guarded_decidable refChain).mp (by decide)

theorem refChainTwo_guarded : refChainTwo.Guarded :=
  (references_guarded_decidable refChainTwo).mp (by decide)

#guard (match ingestDocument refChain.envelope with
        | .ok d => d.payload == refChain.payload
        | .error _ => false)

#guard (match ingestDocument refChainTwo.envelope with
        | .ok d => d.payload == refChainTwo.payload
        | .error _ => false)

/-! ### Two defects at once — the door names the CYCLE

The break pass's F5. `documentRefusal` tests guardedness first, so a
document that is both cyclic and ill formed is named for the cycle. The
TypeScript gate used to run its per-entry admission before its
guardedness filter and named the other defect; it mirrors this order
now, because the reference handler's order IS the order (R10). -/

/-- A table entry that is BOTH on a bare cycle and out of field order
(`b` before `a`). Its control is the same entry with the cycle removed,
which both doors name `illFormed`. -/
def unsortedAndCyclic : Document :=
  { references := [("A", .struct [("b", false, .reference "A"),
                                  ("a", false, .str)])],
    representation := .reference "A" }

def unsortedOnly : Document :=
  { references := [("A", .struct [("b", false, .str), ("a", false, .str)])],
    representation := .reference "A" }

#guard (match ingestDocument unsortedAndCyclic.envelope with
        | .error .unguardedCycle => true
        | _ => false)

#guard (match ingestDocument unsortedOnly.envelope with
        | .error .illFormed => true
        | _ => false)

/-! ### The duplicate table key — refused for its SPELLING

The break pass's BREAK (F1), under the assumed ruling recorded in the
packet. One byte string, two documents: with the reference FIRST the
table cycles for a reader that keeps the first pair and not for one
that keeps the last, and swapping the pairs swaps which reader sees it.
The door refuses the spelling rather than picking a winner, and it does
so BEFORE the decoder runs, so the answer does not depend on what else
is wrong with the document. -/

/-- The duplicate, reference first. -/
def dupKeyRefFirst : Json.Value :=
  .obj [("revision", .nat schemaRevision),
    ("value", .obj [
      ("references", .obj [("A", (Ast.reference "A").toRepresentationJson),
        ("A", Ast.str.toRepresentationJson)]),
      ("representation", Ast.str.toRepresentationJson)])]

/-- The duplicate, reference last — the other direction of the split. -/
def dupKeyRefLast : Json.Value :=
  .obj [("revision", .nat schemaRevision),
    ("value", .obj [
      ("references", .obj [("A", Ast.str.toRepresentationJson),
        ("A", (Ast.reference "A").toRepresentationJson)]),
      ("representation", Ast.str.toRepresentationJson)])]

-- ONE NAME, BOTH DIRECTIONS. Before this gate the first earned
-- `unguardedCycle` and the second `illFormed`, which is a door
-- answering for the parser it happens to be written in.
#guard (match ingestDocument dupKeyRefFirst with
        | .error .illFormed => true
        | _ => false)

#guard (match ingestDocument dupKeyRefLast with
        | .error .illFormed => true
        | _ => false)

-- THE PARTNER, without which refusing every table would pass: the same
-- two entries under two different names is an ordinary table.
#guard (match ingestDocument (.obj [("revision", .nat schemaRevision),
          ("value", .obj [
            ("references", .obj [("A", (Ast.reference "B").toRepresentationJson),
              ("B", Ast.str.toRepresentationJson)]),
            ("representation", Ast.str.toRepresentationJson)])]) with
        | .ok _ => true
        | .error _ => false)

/-! ### The recursion witnesses the corpus was still missing — PDD-13

`contracts/PDD-13.contract.md`, slice 5. The C6 rows in service divide
cleanly: a cycle with an EMPTY bare relation (`guardedList`), and a
non-empty bare relation with NO cycle (`refChain`). Nothing yet asked
the two questions at once, and two doors that pass every row above
still disagree here.

Each witness below names the door it kills. -/

/-- A GUARDED cycle whose bare relation is not empty: `A` names `B`
BARE, and `B` reaches `A` again under a `susp`. So the search has to
follow a real edge AND stop at the guard — the first row that needs
both. `guardedList` needs only the stop, `refChain` only the follow. -/
def guardedChain : Document :=
  { references := [("A", .reference "B"),
      ("B", .struct [("a", false, .susp (.reference "A"))])],
    representation := .reference "A" }

/-- The same pair of names joined BOTH ways: `A` reaches `B` bare and
again under a guard, and `B` reaches `A`. The guarded path does not
excuse the bare one — "some path is guarded" is not the predicate, and
a door that reads it that way admits a table whose resolution never
finishes. -/
def partlyGuardedCycle : Document :=
  { references := [("A", .union [.reference "B", .susp (.reference "B")] .anyOf),
      ("B", .reference "A")],
    representation := .reference "A" }

/-- An unguarded cycle among entries the ROOT NEVER REACHES. Guardedness
is a property of the TABLE, not of the part of it the representation
uses, so this is refused — and a door that walks from the root inward
admits it. It is also the boundary of "a dead entry is admitted": a dead
WELL-FORMED entry is, a dead cyclic one is not. -/
def deadUnguardedEntry : Document :=
  { references := [("A", .str), ("B", .reference "C"), ("C", .reference "B")],
    representation := .reference "A" }

-- The bare relations, so each row's claim about itself is checked and
-- not merely written down.
#guard guardedChain.out "A" == ["B"]
#guard guardedChain.out "B" == []
#guard partlyGuardedCycle.out "A" == ["B"]
#guard partlyGuardedCycle.out "B" == ["A"]
#guard deadUnguardedEntry.out "B" == ["C"]
#guard deadUnguardedEntry.out "C" == ["B"]

#guard guardedChain.guardedMemo
#guard !partlyGuardedCycle.guardedMemo
#guard !deadUnguardedEntry.guardedMemo

theorem guardedChain_guarded : guardedChain.Guarded :=
  (references_guarded_decidable guardedChain).mp (by decide)

#guard (match ingestDocument guardedChain.envelope with
        | .ok d => d.payload == guardedChain.payload
        | .error _ => false)

#guard (match ingestDocument partlyGuardedCycle.envelope with
        | .error .unguardedCycle => true
        | _ => false)

#guard (match ingestDocument deadUnguardedEntry.envelope with
        | .error .unguardedCycle => true
        | _ => false)

/-! ## The bytes-in door

`ingest` takes a VALUE. Everything that arrives from outside — a stored
payload, a hoovered carrier, a model's answer — arrives as BYTES, and
until the parser slice there was no first step: the loop's read half
started one stage in. `ingestBytes` is that step, and it is the whole
of it: parse, un-collapse, ingest.

## Why the collapse has to be undone here

`Cas.Json.parse` answers a NUMBER-NORMAL value — every nonnegative
number spelled `Value.nat`, because that is the only reading a decimal
run has (`Json.parse_sound`). The revision-1 representation spells one
of its numbers `Value.int`: the literal under the key `"value"`. So the
parsed value is not the representation's own spelling, and the strict
decoder would refuse it.

`deNumNorm` (`Cas.Schema.PayloadInj`) is exactly that reading, already
proved to invert the collapse on the representation image of a
well-formed code (`deNumNorm_numNorm_envelope`). It is a SCHEMA-plane
fact — the key decides the constructor — which is why it belongs on
this side of the door and not in the parser.

## The refusal

Bytes that are no canonical rendering at all are refused `notASchema`:
the value plane could not spell them, so they are not a spelling of any
code. The taxonomy is closed and mirrored on the TypeScript side
(`CanonicalSchema.ts`); this door adds no name to it. -/

/-- THE BYTES-IN DOOR: the canonical payload bytes of a revision-1
schema node, read back to the code. Parse strictly, undo the number
collapse the way the representation spells numbers, then run the
existing door. -/
def ingestBytes (s : String) : Except IngestRefusal Ast :=
  match Json.parse s with
  | some v => ingest (deNumNorm v)
  | none => .error .notASchema

/-- Soundness: the bytes door, like the value door, answers only
well-formed codes. -/
theorem ingestBytes_wf {s : String} {a : Ast} (h : ingestBytes s = .ok a) : a.WF := by
  unfold ingestBytes at h
  split at h
  · exact ingest_wf h
  · cases h

/-- EXACTNESS on the canonical image, end to end: a well-formed code's
own payload BYTES ingest to exactly that code's revision-1 normal form.
The R15 read loop, closed at its first step. -/
theorem ingestBytes_payload {a : Ast} (ha : a.WF) :
    ingestBytes a.payload = .ok a.repNorm := by
  unfold ingestBytes Ast.payload
  rw [Json.parse_render (envelope_canonical a)]
  show ingest (deNumNorm (Json.Value.numNorm a.envelope)) = _
  rw [deNumNorm_numNorm_envelope ha]
  exact ingest_envelope ha

/-- Exactness on the nose, for the codes the revision-1 projection
distinguishes. -/
theorem ingestBytes_payload' {a : Ast} (ha : a.WF) (hn : a.RepNormal) :
    ingestBytes a.payload = .ok a := by
  rw [ingestBytes_payload ha, hn]

/-! ### The bytes door, worked at elaboration -/

-- The loop: a code's payload bytes go out and the code comes back.
#guard (match ingestBytes optionOfString.payload with
        | .ok a => a.payload == optionOfString.payload
        | .error _ => false)

#guard (match ingestBytes (Ast.lit (.int ⟨-7, by decide⟩)).payload with
        | .ok a => a.payload == (Ast.lit (.int ⟨-7, by decide⟩)).payload
        | .error _ => false)

-- A NONNEGATIVE number literal is the arm the collapse would break:
-- the parser answers `Value.nat 7` where the representation spells
-- `Value.int 7`, and `deNumNorm` is what puts it back.
#guard (match ingestBytes (Ast.lit (.int ⟨7, by decide⟩)).payload with
        | .ok a => a.payload == (Ast.lit (.int ⟨7, by decide⟩)).payload
        | .error _ => false)

-- The enum through the BYTES door, including the number member the
-- collapse would otherwise break.
#guard (match ingestBytes (Ast.enum [("A", .int ⟨1, by decide⟩),
          ("B", .str "b")]).payload with
        | .ok a => a.payload ==
            (Ast.enum [("A", .int ⟨1, by decide⟩), ("B", .str "b")]).payload
        | .error _ => false)

-- Bytes that are no canonical rendering die at the parser, by name.
#guard (match ingestBytes "{\"revision\": 1}" with
        | .error .notASchema => true
        | _ => false)

#guard (match ingestBytes "not json at all" with
        | .error .notASchema => true
        | _ => false)

-- A canonical rendering that is not a schema node is refused by the
-- door proper, not by the parser — same name, different reader.
#guard (match ingestBytes "[]" with
        | .error .notASchema => true
        | _ => false)

-- The two C6 codes through the BYTES door. A reference's payload is a
-- STRING, so the number collapse never touches it; a suspend's thunk
-- goes through whatever its own code needs.
#guard (match ingestBytes nodeRef.payload with
        | .ok a => a.payload == nodeRef.payload
        | .error _ => false)

#guard (match ingestBytes suspendedList.payload with
        | .ok a => a.payload == suspendedList.payload
        | .error _ => false)

end Cas.Schema
