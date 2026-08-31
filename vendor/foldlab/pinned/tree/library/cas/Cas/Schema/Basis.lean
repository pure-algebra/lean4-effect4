import Cas.Schema.Ingest
import Cas.Schema.Discriminated

/-!
# Basis theorems for the schema plane's API surface

Per capability family: the fewest shapes that generate it, proved.

A BASIS result has three parts, and this module states all three for
every family it claims:

- **GENERATION** — every public operation of the family, proved equal
  to a composition over a small declared core. Where the definition IS
  the composition the proof is `rfl` and the theorem is still worth
  stating: it pins the factoring as law, so a later edit that changes
  the factoring breaks a theorem rather than drifting silently.
- **INDEPENDENCE** — the core cannot shrink. For each core element, a
  separating witness: an input on which the composition of the others
  cannot agree.
- **NAMED REDUNDANCY** — every deliberate duplicate stated as a
  collapse, in the house idiom (a named function, an idempotence law,
  and an invisibility law at the observation), never left implicit.

Nothing here defines a new operation. The theorems ARE the interface;
the core elements are spelled inline in the statements so the surface
grows by proof only.

## BLOAT-LEDGER

### F1 — the projection family: BASIS FOUND

| | |
|---|---|
| surface | 5 (`toRepresentationJson`, `representationDocument`, `envelope`, `payload`, `payloadBytes`) |
| core | 5 (`toRepresentationJson`, document-wrap, envelope-wrap, `renderPlain`, `toUTF8`) |
| generation | 4 (`representationDocument_generated`, `envelope_generated`, `payload_generated`, `payloadBytes_generated`) |
| independence | 2 byte witnesses (`#guard`), 2 stages separated by type |
| named collapses | 1 — `renderCompact` collapses to `renderPlain` on this family's image |

The surface is a CHAIN, not a fan: each member is the next stage
applied to the one before, so five operations sit over five core
shapes and the count cannot come down. Three of the four generation
equations are `rfl`; `payload_generated` is a real theorem, because
`payload` is defined with `renderCompact` (which sorts) and the core
uses `renderPlain` (which does not) — they agree here only because
`envelope_canonical` says the envelope is already sorted.

### F2 — the door family: BASIS FOUND, and the declared core was SHORT

| | |
|---|---|
| surface | 3 (`ingest`, `ingestLegacy`, `ingestBytes`) |
| core | 6 — `parse`, `canonValue`, `deNumNorm`, `ofEnvelope`, `ofJson`, `wf` |
| generation | 3 (`ingest_generated`, `ingestLegacy_generated`, `ingestBytes_generated`) |
| independence | `canonValue_widens_door`, `wf_is_independent`, plus 3 `#guard` witnesses |
| named collapses | 1 — `canonValue` collapses to the identity on the projection's image |

`deNumNorm` is a SIXTH core element, not a stage of the other five: it
is the only thing on the read path that manufactures a `Value.int`, and
without it the bytes door refuses every nonnegative number literal
(`deNumNorm_is_independent`). Counting it is a correction to the
family's declared core, not a new operation.

**The interesting question, answered: `canonValue` is NOT redundant on
the rev-1 path.** It is redundant on the projection's IMAGE
(`canonValue_redundant_on_image` — the envelope is already canonically
spelled, so the normalizer is a no-op there) and irredundant on the
DOMAIN (`canonValue_widens_door` — an envelope written with its two
keys in the other order is refused outright by `Ast.ofEnvelope` and
admitted by `ingest`). Both halves are proved, neither is a `#guard`.
The door is therefore genuinely wider than its decoder, and the
widening is exactly one quotient: `ingest_absorbs_canonValue` says
`ingest` is constant on `canonValue`'s classes.

### F3 — the normalizer family: BASIS FOUND, minimal set is ONE

| | |
|---|---|
| surface | 4 (`repNorm`, `numNorm`, `canonValue`, `deNumNorm`) |
| core, emit path | 1 (`repNorm`) |
| core, read path | 3 (`canonValue`, `deNumNorm`, and `numNorm` as the parser's image) |
| generation | `payload_eq_iff_repNorm`, `payloadBytes_eq_iff_repNorm` |
| independence | `normalizers_are_independent` (three rfl separations) |
| named collapses | 4 idempotence laws, one newly landed (`deNumNorm_idem`) |

The composition algebra: `canonValue` and `numNorm` COMMUTE
(`canonValue_numNorm_comm`) — the key-sorting method and the number
collapse never see each other, because sorting compares keys only and
the collapse preserves them. `canonValue` and `deNumNorm` commute for
the same reason (`canonValue_deNumNorm_comm`), which is why the bytes
door may un-collapse before it normalizes or after, indifferently.
`repNorm` is absorbed by the projection (`toRepresentationJson_repNorm`,
landed in `SelfCodec`).

**"One code, one address" is EXACT, not merely sound.** For well-formed
codes the address identifies exactly `repNorm`'s classes and nothing
finer or coarser (`payload_eq_iff_repNorm`). The forward half was
already law (`payload_inj`); the converse half is what makes the
normalizer set MINIMAL — a second normalizer on the emit path would
have to identify something the address does not.

### F4 — the carrier's redundancy census: CARRIER BLOAT = 1

| | |
|---|---|
| carrier | 12 constructors |
| identifications the projection makes | exactly 1 |
| the collapse | `.lit .null ↔ .null`, named, normalized by `repNorm` |
| census theorem | `toRepresentationJson_eq_iff_repNorm` (no `WF` premise) |

The census is an IFF, and it needs no well-formedness hypothesis: two
codes have the same representation exactly when they have the same
normal form. Combined with `repNorm_the_one_collapse`,
`repNorm_fixes_every_other_leaf`, and `repNorm_is_a_congruence` —
which together say `repNorm` is the identity everywhere except at the
single leaf rewrite and its congruence closure — "carrier bloat = 1,
deliberate, named" is a theorem, not a vibe.

**`.int`'s position, honestly.** `.int` is SUGAR IN THE REPRESENTATION
(Effect spells it `Number` plus an `isInt` filter check, not a keyword)
and a PRIMITIVE IN THE CARRIER. The hypothesised analogue of the
declaration-payload collision does NOT exist: no second code spells
`.int`'s representation, and the proof needs no `WF` premise
(`int_no_second_spelling`). The contrast with `payload_inj_needs_wf`
is real and is a LEVEL distinction, not an exception —
`.decl .date (.nat 5)` and `.decl .date (.int 5)` have DIFFERENT
representation values and identical payload BYTES, so their collision
lives below the representation, in the rendering's number collapse, and
`WF` is what evacuates it. `.int` carries no number at all, so it
cannot participate.

### F5 — the twins: 12 capabilities, 24 spellings

`twins_inventory` — every boolean gate in the schema plane paired with
its `Prop`, each pair one capability by proof. Twelve `_iff` theorems
already existed; this restates them as one inventory so the count is
lemma-backed rather than counted by hand.

### Deliberate lab multiplicity — NOT in any core, NOT collapsed

Counted, not condemned. These are duplicates the estate keeps on
purpose, and each is a live obligation rather than a defect:

1. **`Ast.toJson` / `Ast.ofJson` — the whole revision-0 projection**
   (2 operations + `legacyEnvelope`). Retired as a door, retained as a
   decoder pin for already-addressed nodes. It is a SECOND, independent
   projection of the same carrier with its own canonicality and round
   trip, and it is genuinely more injective than revision 1 (it keeps
   `.lit .null` a literal, so `ingestLegacy_toJson` needs no normal
   form). Not collapsible while revision-0 addresses exist.
2. **`Ast.ofRepresentationJson`'s `RepNormal` image** — the named open
   obligation of `SelfCodec`. Until it is proved, `RepNormal` is a
   hypothesis on the exactness laws rather than a characterization.
3. **`renderCompact` vs `renderPlain`** — two printers, collapsed on
   canonical values (`renderCompact_eq_renderPlain`) and NOT collapsed
   in general. Kept because `renderCompact` is total and
   defensive; `renderPlain` is what the proofs induct on.
4. **`ingestBytes` vs `ingest`** — not redundancy: a strictly longer
   composition (F2's generation equations show it). Counted here only
   because the surface reads like three doors when it is one door and
   two adapters.

Total deliberate multiplicity outside the cores: 4 items, 5 operations.
-/

namespace Cas.Schema

open Cas.Json

/-! ## F1 — the projection family

Core: `toRepresentationJson`, then two fixed key-frames, then
`renderPlain`, then `toUTF8`. The wraps are spelled inline rather than
named, so this module adds no operation to the surface. -/

/-- GENERATION 1/4: the document is the representation under the
single-root key frame. `rfl` — the factoring is the definition, and
this theorem is what pins it. -/
theorem representationDocument_generated (a : Ast) :
    a.representationDocument =
      .obj [("references", .obj []), ("representation", a.toRepresentationJson)] :=
  rfl

/-- GENERATION 2/4: the envelope is the document under the revision key
frame. `rfl`, for the same reason. -/
theorem envelope_generated (a : Ast) :
    a.envelope =
      .obj [("revision", .nat schemaRevision),
        ("value", .obj [("references", .obj []),
          ("representation", a.toRepresentationJson)])] :=
  rfl

/-- GENERATION 3/4: the payload is the PLAIN rendering of the wrapped
representation. NOT `rfl`: `Ast.payload` is defined with
`renderCompact`, which sorts, and the core uses `renderPlain`, which
does not. They agree because `envelope_canonical` says there is nothing
left to sort — the named collapse of this family. -/
theorem payload_generated (a : Ast) :
    a.payload = Json.renderPlain
      (.obj [("revision", .nat schemaRevision),
        ("value", .obj [("references", .obj []),
          ("representation", a.toRepresentationJson)])]) :=
  payload_renderPlain a

/-- GENERATION 4/4: the whole chain, end to end — the address's bytes
are `toUTF8 ∘ renderPlain ∘ envelope-wrap ∘ document-wrap ∘
toRepresentationJson`, and nothing else. -/
theorem payloadBytes_generated (a : Ast) :
    a.payloadBytes = (Json.renderPlain
      (.obj [("revision", .nat schemaRevision),
        ("value", .obj [("references", .obj []),
          ("representation", a.toRepresentationJson)])])).toUTF8 := by
  show a.payload.toUTF8 = _
  rw [payload_generated]

/-- NAMED REDUNDANCY of F1: the two printers are one capability on this
family's image. `renderCompact` sorts and `renderPlain` does not; on
the envelope there is nothing to sort. -/
theorem renderCompact_collapses_on_envelope (a : Ast) :
    Json.renderCompact a.envelope = Json.renderPlain a.envelope :=
  Json.renderCompact_eq_renderPlain _ (envelope_canonical a)

/-! ### F1 independence, at the bytes

Each wrap is OBSERVABLE: dropping either stage changes the address.
The remaining two stages (`renderPlain`, `toUTF8`) are separated by
type — `Json.Value → String` and `String → ByteArray` — so no witness
is available or needed. -/

-- The document wrap is observable: the representation alone is not the
-- document.
#guard Json.renderCompact (Ast.null.toRepresentationJson) !=
  Json.renderCompact (Ast.null.representationDocument)

-- The envelope wrap is observable: the document alone is not the
-- payload.
#guard Json.renderCompact (Ast.null.representationDocument) != Ast.null.payload

-- And the collapse above is NOT a general fact: off the canonical
-- image the two printers disagree, which is why `renderPlain` and not
-- `renderCompact` is the core element.
#guard Json.renderCompact (.obj [("b", .null), ("a", .null)]) !=
  Json.renderPlain (.obj [("b", .null), ("a", .null)])

/-! ## F2 — the door family

Core: `Json.parse`, `canonValue`, `deNumNorm`, `Ast.ofEnvelope`,
`Ast.ofJson`, `Ast.wf`. The generation equations are stated on the
SUCCESS graph, which is the whole of the door's answer: the failure
path runs a private refusal-namer that decides nothing (`Ast.ofEnvelope`
alone decides admission), so it contributes no capability. -/

/-- GENERATION 1/3: the door's success graph is exactly
`wf ∘ ofEnvelope ∘ canonValue`. -/
theorem ingest_generated {v : Json.Value} {a : Ast} :
    ingest v = .ok a ↔
      Ast.ofEnvelope (canonValue v) = some a ∧ a.wf = true := by
  constructor
  · intro h
    unfold ingest at h
    split at h
    · next b hb =>
      split at h
      · next hw => cases h; exact ⟨hb, hw⟩
      · cases h
    · cases h
  · rintro ⟨h1, h2⟩
    unfold ingest
    rw [h1]
    simp [h2]

/-- GENERATION 2/3: the legacy arm is the same composition with the
other decoder. One capability, two decoders — which is what makes
`ofJson` and `ofEnvelope` two core elements and not one. -/
theorem ingestLegacy_generated {v : Json.Value} {a : Ast} :
    ingestLegacy v = .ok a ↔
      Ast.ofJson (canonValue v) = some a ∧ a.wf = true := by
  constructor
  · intro h
    unfold ingestLegacy at h
    split at h
    · cases h
    · next b hb =>
      split at h
      · next hw => cases h; exact ⟨hb, hw⟩
      · cases h
  · rintro ⟨h1, h2⟩
    unfold ingestLegacy
    rw [h1]
    simp [h2]

/-- GENERATION 3/3: the bytes door is the value door with two stages in
front. All six core elements appear in one equation. -/
theorem ingestBytes_generated {s : String} {a : Ast} :
    ingestBytes s = .ok a ↔ ∃ v, Json.parse s = some v ∧
      Ast.ofEnvelope (canonValue (deNumNorm v)) = some a ∧ a.wf = true := by
  constructor
  · intro h
    unfold ingestBytes at h
    split at h
    · next v hv => exact ⟨v, hv, ingest_generated.mp h⟩
    · cases h
  · rintro ⟨v, hv, hd, hw⟩
    unfold ingestBytes
    rw [hv]
    exact ingest_generated.mpr ⟨hd, hw⟩

/-! ### Is `canonValue` redundant on the rev-1 path?

Triaged before proving, and the answer is TWO-SIDED. On the image it is
a no-op; on the domain it is the whole widening. Both halves proved. -/

/-- NAMED REDUNDANCY of F2, the image half: on everything the
projection emits, `canonValue` is the identity. This is why
`ingest_envelope` needs no canonicality hypothesis. -/
theorem canonValue_redundant_on_image (a : Ast) :
    canonValue a.envelope = a.envelope :=
  canonValue_of_canonical _ (envelope_canonical a)

/-- The door is CONSTANT on the normalizer's classes: `ingest` factors
through `canonValue`. The quotient the door computes is exactly the
key-order quotient, and no finer one. -/
theorem ingest_absorbs_canonValue (v : Json.Value) :
    ingest (canonValue v) = ingest v := by
  unfold ingest
  rw [canonValue_idem]

/-- Two-element merge sort, computed. The general sort is well-founded
recursion and does not reduce in the kernel, so the separating witness
below needs this one equation to become a theorem rather than a
`#guard`. -/
private theorem mergeSort_pair {α : Type} (le : α → α → Bool) (a b : α) :
    [a, b].mergeSort le = if le a b then [a, b] else [b, a] := by
  rw [show [a, b].mergeSort le = ([a] : List α).merge [b] le from by
    simp [List.mergeSort]]
  rw [List.cons_merge_cons, List.nil_merge, List.merge_right]

/-- The separating witness: the null code's own envelope with its two
keys written in the other order. A foreign spelling, and the only thing
wrong with it is the order. -/
private def swappedEnvelope : Json.Value :=
  .obj [("value", Ast.null.representationDocument),
        ("revision", .nat schemaRevision)]

/-- The strict decoder refuses it outright — `Ast.ofEnvelope` matches
the key frame positionally. -/
private theorem ofEnvelope_swapped : Ast.ofEnvelope swappedEnvelope = none := rfl

/-- The normalizer puts it back. -/
private theorem canonValue_swapped :
    canonValue swappedEnvelope = Ast.null.envelope := by
  show Json.Value.obj _ = _
  simp only [canonFields, mergeSort_pair,
    if_neg (by decide : ¬ (decide ("value" ≤ "revision") = true)),
    canonValue_of_canonical _ (representationDocument_canonical Ast.null)]
  rfl

/-- INDEPENDENCE of `canonValue`: it is NOT redundant on the rev-1
path. `Ast.ofEnvelope` is strict about key order, and the door admits a
spelling the decoder refuses — so the normalizer genuinely widens the
door rather than decorating it. -/
theorem canonValue_widens_door :
    ∃ v : Json.Value, Ast.ofEnvelope v = none ∧ ingest v = .ok .null := by
  refine ⟨swappedEnvelope, ofEnvelope_swapped, ?_⟩
  unfold ingest
  rw [canonValue_swapped, ofEnvelope_envelope]
  rfl

/-- INDEPENDENCE of `wf`: the gate is not implied by the decoder. The
empty union decodes cleanly and is refused by the discipline alone —
`Never` is a shape the carrier spells and admission does not. -/
theorem wf_is_independent :
    Ast.ofEnvelope (Ast.union [] .anyOf).envelope = some (.union [] .anyOf) ∧
      (Ast.union [] .anyOf).wf = false :=
  ⟨by rw [ofEnvelope_envelope]; rfl, rfl⟩

/-! ### The remaining core elements, witnessed at the bytes

`ofJson` and `ofEnvelope` are two decoders and not one: each admits a
spelling the other refuses. `deNumNorm` is the sixth core element the
family's declared core was missing. -/

-- The rev-0 spelling is not a rev-1 envelope: `ingest` refuses what
-- `ingestLegacy` admits.
#guard (match ingest (Ast.str).toJson, ingestLegacy (Ast.str).toJson with
        | .error _, .ok _ => true
        | _, _ => false)

-- And the converse: `ingestLegacy` refuses what `ingest` admits.
#guard (match ingestLegacy (Ast.str).envelope, ingest (Ast.str).envelope with
        | .error _, .ok _ => true
        | _, _ => false)

-- INDEPENDENCE of `deNumNorm`: the parser answers a number-normal
-- value, and the rev-1 representation spells one of its numbers
-- `Value.int`. Without the un-collapse the bytes door refuses every
-- nonnegative number literal; with it, the same bytes come back as the
-- code. Nothing else in the core manufactures a `Value.int`.
#guard (match ingest (Ast.lit (.int ⟨7, by decide⟩)).envelope.numNorm,
              ingestBytes (Ast.lit (.int ⟨7, by decide⟩)).payload with
        | .error _, .ok _ => true
        | _, _ => false)

/-! ## F3 — the normalizer family

Four normalizers over two planes. The composition algebra below says
which of them ever meet. -/

/-! ### The commutation: `canonValue` and `numNorm` never see each other

Key-sorting compares keys; the number collapse preserves them. The
proof is the estate's own mutual-recursion shape plus core's
`List.map_mergeSort`, which is exactly the stability fact this needs. -/

private theorem numNormFields_eq_map (fs : List (String × Value)) :
    numNormFields fs = fs.map fun f => (f.1, f.2.numNorm) := by
  induction fs with
  | nil => rfl
  | cons f rest ih => cases f; simp [numNormFields, ih]

private theorem numNormFields_mergeSort (l : List (String × Value)) :
    numNormFields (l.mergeSort fun a b => decide (a.1 ≤ b.1)) =
      (numNormFields l).mergeSort fun a b => decide (a.1 ≤ b.1) := by
  rw [numNormFields_eq_map, numNormFields_eq_map]
  exact List.map_mergeSort (fun _ _ _ _ => rfl)

mutual

/-- The key-sorting method and the number collapse COMMUTE. Neither is
a stage of the other, and the read path may apply them in either
order. -/
theorem canonValue_numNorm_comm :
    ∀ v : Value, canonValue v.numNorm = (canonValue v).numNorm
  | .null | .bool _ | .nat _ | .str _ => rfl
  | .int i => by
    by_cases h : 0 ≤ i
    · simp only [Value.numNorm, canonValue, if_pos h]
    · simp only [Value.numNorm, canonValue, if_neg h]
  | .arr xs => by
    simp only [Value.numNorm, canonValue, canonItems_numNormItems xs]
  | .obj fs => by
    simp only [Value.numNorm, canonValue, canonFields_numNormFields fs,
      numNormFields_mergeSort]

/-- The array arm of the commutation: items carry no keys, so the two
methods pass through them position by position. -/
theorem canonItems_numNormItems :
    ∀ xs : List Value, canonItems (numNormItems xs) = numNormItems (canonItems xs)
  | [] => rfl
  | x :: xs => by
    simp only [numNormItems, canonItems, canonValue_numNorm_comm x,
      canonItems_numNormItems xs]

/-- The field arm of the commutation, BEFORE the sort: both methods
rewrite values under the keys they find and neither touches a key. The
sort itself is handled once, by `numNormFields_mergeSort`. -/
theorem canonFields_numNormFields :
    ∀ fs : List (String × Value),
      canonFields (numNormFields fs) = numNormFields (canonFields fs)
  | [] => rfl
  | (_, v) :: fs => by
    simp only [numNormFields, canonFields, canonValue_numNorm_comm v,
      canonFields_numNormFields fs]

end

/-! ### The same for `deNumNorm`, and its missing idempotence law

`deNumNorm` is the one house normalizer that landed WITHOUT the idiom's
idempotence law. It has it now. -/

private theorem reint_deNumNorm_reint {w : Json.Value} (hw : deNumNorm w = w) :
    reint (deNumNorm (reint w)) = reint w := by
  cases w <;> simp only [reint, deNumNorm, hw]

mutual

/-- The un-collapse is idempotent — the house idiom, completed. -/
theorem deNumNorm_idem : ∀ v : Json.Value, deNumNorm (deNumNorm v) = deNumNorm v
  | .null | .bool _ | .nat _ | .int _ | .str _ => rfl
  | .arr xs => by simp only [deNumNorm, deNumNormItems_idem xs]
  | .obj fs => by simp only [deNumNorm, deNumNormFields_idem fs]

/-- The array arm of the idempotence: an item sits under no key, so the
`"value"` reading never fires on it. -/
theorem deNumNormItems_idem :
    ∀ xs : List Json.Value, deNumNormItems (deNumNormItems xs) = deNumNormItems xs
  | [] => rfl
  | x :: xs => by
    simp only [deNumNormItems, deNumNorm_idem x, deNumNormItems_idem xs]

/-- The field arm of the idempotence, and the only one that does work:
under `"value"` a second pass finds a `Value.int` where the first found
a `Value.nat`, and `reint` is already the identity there. -/
theorem deNumNormFields_idem :
    ∀ fs : List (String × Json.Value),
      deNumNormFields (deNumNormFields fs) = deNumNormFields fs
  | [] => rfl
  | (k, v) :: fs => by
    simp only [deNumNormFields, deNumNormFields_idem fs]
    by_cases h : k = "value"
    · simp only [if_pos h, reint_deNumNorm_reint (deNumNorm_idem v)]
    · simp only [if_neg h, deNumNorm_idem v]

end

private theorem deNumNormFields_eq_map (fs : List (String × Json.Value)) :
    deNumNormFields fs =
      fs.map fun f => (f.1, if f.1 = "value" then reint (deNumNorm f.2)
        else deNumNorm f.2) := by
  induction fs with
  | nil => rfl
  | cons f rest ih => cases f; simp [deNumNormFields, ih]

/-- The `"value"` reading is blind to key order: it rewrites a bare
number and passes every structure through, and `canonValue` is the
identity on bare numbers. -/
private theorem canonValue_reint (w : Json.Value) :
    canonValue (reint w) = reint (canonValue w) := by
  cases w <;> rfl

private theorem deNumNormFields_mergeSort (l : List (String × Json.Value)) :
    deNumNormFields (l.mergeSort fun a b => decide (a.1 ≤ b.1)) =
      (deNumNormFields l).mergeSort fun a b => decide (a.1 ≤ b.1) := by
  rw [deNumNormFields_eq_map, deNumNormFields_eq_map]
  exact List.map_mergeSort (fun _ _ _ _ => rfl)

mutual

/-- The key-sorting method and the un-collapse COMMUTE too, for the
same reason: the un-collapse is keyed on the field NAME, and sorting
carries names with their values. This is why the bytes door may
normalize before or after undoing the collapse. -/
theorem canonValue_deNumNorm_comm :
    ∀ v : Json.Value, canonValue (deNumNorm v) = deNumNorm (canonValue v)
  | .null | .bool _ | .nat _ | .int _ | .str _ => rfl
  | .arr xs => by
    simp only [deNumNorm, canonValue, canonItems_deNumNormItems xs]
  | .obj fs => by
    simp only [deNumNorm, canonValue, canonFields_deNumNormFields fs,
      deNumNormFields_mergeSort]

/-- The array arm of the second commutation. -/
theorem canonItems_deNumNormItems :
    ∀ xs : List Json.Value,
      canonItems (deNumNormItems xs) = deNumNormItems (canonItems xs)
  | [] => rfl
  | x :: xs => by
    simp only [deNumNormItems, canonItems, canonValue_deNumNorm_comm x,
      canonItems_deNumNormItems xs]

/-- The field arm of the second commutation, BEFORE the sort. The
`"value"` branch is where the two methods could have collided — the
un-collapse reads the key and the sort moves the pair — and they do
not: sorting carries a key with its own value, so the reading fires on
the same pair either way. -/
theorem canonFields_deNumNormFields :
    ∀ fs : List (String × Json.Value),
      canonFields (deNumNormFields fs) = deNumNormFields (canonFields fs)
  | [] => rfl
  | (k, v) :: fs => by
    simp only [deNumNormFields, canonFields, canonFields_deNumNormFields fs]
    by_cases h : k = "value"
    · simp only [if_pos h, canonValue_reint, canonValue_deNumNorm_comm v]
    · simp only [if_neg h, canonValue_deNumNorm_comm v]

end

/-! ### The minimal normalizer set on the emit path

`repNorm` is invisible to the projection (`toRepresentationJson_repNorm`,
landed) and therefore invisible to the address. The converse — the
address identifies NOTHING beyond `repNorm`'s classes — is
`payload_inj`, landed. Putting the two together makes the normalizer
set MINIMAL and not merely sound. -/

/-- `repNorm` is invisible at the address. -/
theorem payload_repNorm (a : Ast) : a.repNorm.payload = a.payload := by
  show Json.renderCompact _ = Json.renderCompact _
  rw [Ast.envelope, Ast.envelope, Ast.representationDocument,
    Ast.representationDocument, toRepresentationJson_repNorm a]

/-- ONE CODE, ONE ADDRESS — exactly. For well-formed codes the address
identifies precisely `repNorm`'s classes: no coarser (that is
`payload_inj`) and no finer (that is `payload_repNorm`). A second
normalizer on the emit path would have to identify something the
address does not, so the emit-path normalizer set is `{repNorm}` and
cannot shrink or grow. -/
theorem payload_eq_iff_repNorm {a b : Ast} (ha : a.WF) (hb : b.WF) :
    a.payload = b.payload ↔ a.repNorm = b.repNorm := by
  constructor
  · exact payload_inj ha hb
  · intro h
    rw [← payload_repNorm a, ← payload_repNorm b, h]

/-- The same at the bytes the schema node actually carries. -/
theorem payloadBytes_eq_iff_repNorm {a b : Ast} (ha : a.WF) (hb : b.WF) :
    a.payloadBytes = b.payloadBytes ↔ a.repNorm = b.repNorm := by
  rw [← payload_eq_iff_repNorm ha hb]
  constructor
  · exact fun h => String.toByteArray_inj.mp h
  · exact fun h => congrArg String.toUTF8 h

/-- INDEPENDENCE of the normalizer family: no two of them do each
other's work, witnessed on scalars and on key order.

1. `canonValue` cannot collapse a number — it is the identity on every
   scalar.
2. `numNorm` cannot sort keys — it is the identity on the field list.
3. `deNumNorm` is the only one that manufactures a `Value.int`; the
   other two are the identity there. -/
theorem normalizers_are_independent :
    canonValue (.int 5) = .int 5 ∧
    Value.numNorm swappedEnvelope = swappedEnvelope ∧
    deNumNorm (.obj [("value", .nat 5)]) = .obj [("value", .int 5)] ∧
    canonValue (.obj [("value", .nat 5)]) = .obj [("value", .nat 5)] :=
  ⟨rfl, rfl, rfl, by
    show Json.Value.obj _ = _
    simp only [canonFields, List.mergeSort_singleton]
    rfl⟩

/-! ## F4 — the carrier's redundancy census

`Ast` has twelve constructors. How many does the revision-1 projection
identify? Exactly one pair, and the pair is named. -/

/-- THE CENSUS. Two codes have the same representation exactly when
they have the same normal form — an IFF, and with NO well-formedness
premise. The forward half is `toRepresentationJson_inj` (landed); the
converse is `toRepresentationJson_repNorm` (landed). Stated together,
they say the projection's fibres ARE `repNorm`'s classes: the carrier's
redundancy under the projection is entirely accounted for by the named
normal form, with no residue. -/
theorem toRepresentationJson_eq_iff_repNorm {a b : Ast} :
    a.toRepresentationJson = b.toRepresentationJson ↔ a.repNorm = b.repNorm := by
  constructor
  · exact toRepresentationJson_inj
  · intro h
    rw [← toRepresentationJson_repNorm a, ← toRepresentationJson_repNorm b, h]

/-- THE ONE COLLAPSE: `.lit .null` and `.null` are two codes with one
normal form, hence (by the census) one representation and one address.
Deliberate — Effect has no `Literal(null)` node, only `Null` — and
named. -/
theorem repNorm_the_one_collapse :
    Ast.repNorm (.lit .null) = Ast.repNorm .null ∧
      (Ast.lit .null : Ast) ≠ .null :=
  ⟨rfl, fun h => Ast.noConfusion h⟩

/-- The collapse, at the address. -/
theorem litNull_payload : (Ast.lit .null).payload = Ast.null.payload := rfl

/-- BLOAT = 1, first half: `repNorm` is the IDENTITY on every leaf
except `.lit .null`. Nine equations, all `rfl` — there is no second
leaf rewrite hiding anywhere. -/
theorem repNorm_fixes_every_other_leaf :
    Ast.repNorm .null = .null ∧
    Ast.repNorm .bool = .bool ∧
    Ast.repNorm .int = .int ∧
    Ast.repNorm .str = .str ∧
    (∀ t : UInt8, Ast.repNorm (.ref t) = .ref t) ∧
    (∀ b : Bool, Ast.repNorm (.lit (.bool b)) = .lit (.bool b)) ∧
    (∀ i : SafeInt, Ast.repNorm (.lit (.int i)) = .lit (.int i)) ∧
    (∀ s : String, Ast.repNorm (.lit (.str s)) = .lit (.str s)) ∧
    (∀ ms : List (String × EnumValue), Ast.repNorm (.enum ms) = .enum ms) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩

/-- BLOAT = 1, second half: on every COMPOUND code `repNorm` is the
congruence and adds no identification of its own — the head is kept,
the arity is kept, the order is kept, and the payload and mode and
optionality bits are carried verbatim. Together with
`repNorm_fixes_every_other_leaf` this says `repNorm` is generated by
the single leaf rewrite of `repNorm_the_one_collapse`, so the carrier's
bloat under the projection is exactly one, deliberate, and named. -/
theorem repNorm_is_a_congruence :
    (∀ a : Ast, Ast.repNorm (.arr a) = .arr a.repNorm) ∧
    (∀ fs, Ast.repNorm (.struct fs) = .struct (repNormFields fs)) ∧
    (∀ id p ps, Ast.repNorm (.decl id p ps) = .decl id p (repNormParams ps)) ∧
    (∀ ms m, Ast.repNorm (.union ms m) = .union (repNormMembers ms) m) ∧
    (∀ e es r, Ast.repNorm (.tuple e es r) =
      .tuple (repNormElement e) (repNormElements es) (repNormRest r)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- Nothing normalizes TO `.int` but `.int`. -/
private theorem repNorm_eq_int : ∀ {b : Ast}, b.repNorm = .int → b = .int
  | .null, h => absurd h (fun hh => Ast.noConfusion hh)
  | .bool, h => absurd h (fun hh => Ast.noConfusion hh)
  | .int, _ => rfl
  | .str, h => absurd h (fun hh => Ast.noConfusion hh)
  | .lit .null, h => absurd h (fun hh => Ast.noConfusion hh)
  | .lit (.bool _), h => absurd h (fun hh => Ast.noConfusion hh)
  | .lit (.int _), h => absurd h (fun hh => Ast.noConfusion hh)
  | .lit (.str _), h => absurd h (fun hh => Ast.noConfusion hh)
  | .arr _, h => absurd h (fun hh => Ast.noConfusion hh)
  | .struct _, h => absurd h (fun hh => Ast.noConfusion hh)
  | .ref _, h => absurd h (fun hh => Ast.noConfusion hh)
  | .decl _ _ _, h => absurd h (fun hh => Ast.noConfusion hh)
  | .union _ _, h => absurd h (fun hh => Ast.noConfusion hh)
  | .enum _, h => absurd h (fun hh => Ast.noConfusion hh)
  | .tuple _ _ _, h => absurd h (fun hh => Ast.noConfusion hh)

/-- `.int`'S POSITION, HONESTLY. `.int` is sugar in the REPRESENTATION —
Effect spells it `Number` plus an `isInt` filter check, not a keyword —
but it is a primitive in the CARRIER: no second code spells its
representation, and the proof needs no `WF` premise. The hypothesised
analogue of the declaration-payload collision (`payload_inj_needs_wf`)
does NOT exist, and the reason is a level distinction: that collision
lives BELOW the representation, in the rendering's number collapse,
between two codes whose representation VALUES already differ. `.int`
carries no number, so it cannot participate. -/
theorem int_no_second_spelling {b : Ast}
    (h : b.toRepresentationJson = Ast.int.toRepresentationJson) : b = .int :=
  repNorm_eq_int (toRepresentationJson_eq_iff_repNorm.mp h)

/-! ## F5 — the twins

Twelve boolean gates, twelve `Prop`s, twelve `_iff` theorems: twelve
capabilities in twenty-four spellings. The duplication is deliberate
(the `Prop` is what proofs induct on, the `Bool` is what the door runs)
and it is fully collapsed — no gate is missing its twin, and no twin is
missing its `_iff`. -/

/-- THE TWINS INVENTORY: every boolean/`Prop` pair in the schema plane,
each proved one capability. Counted by proof rather than by hand. -/
theorem twins_inventory :
    (∀ a : Ast, a.wf = true ↔ a.WF) ∧
    (∀ fs, wfFields fs = true ↔ WFFields fs) ∧
    (∀ ps, wfParams ps = true ↔ WFParams ps) ∧
    (∀ ms, wfMembers ms = true ↔ WFMembers ms) ∧
    (∀ e, wfElement e = true ↔ WFElement e) ∧
    (∀ es, wfElements es = true ↔ WFElements es) ∧
    (∀ r, wfRest r = true ↔ WFRest r) ∧
    (∀ fs, pairwiseNames fs = true ↔
      List.Pairwise (fun a b : String × Bool × Ast => a.1 < b.1) fs) ∧
    (∀ ms, distinctEnumNames ms = true ↔
      List.Pairwise (fun a b : String × EnumValue => a.1 ≠ b.1) ms) ∧
    (∀ ms, discriminatedB ms = true ↔ Discriminated ms) ∧
    (∀ (d : DeclarationId) (p : DeclPayload), d.payloadWf p = true ↔ d.PayloadWF p) ∧
    (∀ (g : DeclarationId.General) (p : DeclPayload),
      g.payloadWf p = true ↔ g.PayloadWF p) :=
  ⟨Ast.wf_iff, wfFields_iff, wfParams_iff, wfMembers_iff, wfElement_iff,
    wfElements_iff, wfRest_iff, pairwiseNames_iff, distinctEnumNames_iff,
    discriminatedB_iff, DeclarationId.payloadWf_iff,
    DeclarationId.General.payloadWf_iff⟩

end Cas.Schema
