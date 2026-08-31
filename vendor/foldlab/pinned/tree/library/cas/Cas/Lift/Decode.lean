import Cas.Values.JsonParse
import Cas.Codec.Hex
import Cas.Lang.Defun

/-!
# The lift decoder — the recognizer's document, read as a program

The Lean landing of the effect-lift lane. The recognition harness
(`experiments/lift-harness`) reads pinned Effect TypeScript and answers
a canonical `Lift` document (`src/contract.ts`); this module reads that
document back as a `PProg` — the defunctionalized table of
`Cas/Lang/Defun.lean` — and stops there.

## The direction law, enforced here

`AGENTS.md`: HOOVER is ingestion and never mints identity; EXECUTE (the
Lean reference handler) is the only way words are minted. This decoder
therefore delivers a `PProg` and NOTHING ELSE. A document carrying a
`word` field is not data with an extra key: it is a hoover-side artifact
claiming an execute-side result, and it is refused BY NAME
(`wordPresent`) rather than parsed and ignored. R8 dropped that field
from the recognizer's contract for exactly this reason; the refusal is
what keeps it dropped.

## THE DECODER'S DOMAIN — its contract, stated up front

The decoder's image is a strict SUB-LANGUAGE of `PProg`, and it is
declared, not discovered:

- **puts only.** The document has no `load` spelling, because the
  recognizer's `const-yield-load` rule is disabled in v0 (`load is not
  yet documented`, `Cas.Lift.manifestV0`). No `PLine.load` is ever
  answered.
- **answer references only.** A `Ref.source` is an INDEX (contract.ts:
  "names die at the boundary"), so every operand is `PIn.ans`. No
  `PIn.lit` is ever answered: the document has no literal-address
  operand, and a decoder that invented one would be minting an address
  the recognizer never saw.
- **dense, ordered, backward-resolving.** An instruction's `index` must
  BE its position in the table, and every reference must name a STRICTLY
  EARLIER instruction. Both are properties the recognizer establishes
  (rule `answer-ref` resolves against binders already bound), so
  requiring them here is not a new discipline: it is the door refusing
  to admit what the instrument cannot have produced.

Everything outside that domain is a named refusal, never a repair.

## Strict, like the lane it serves

`Cas.Schema.ingest` NORMALIZES its input (`canonValue`) before decoding,
because foreign schema spellings arrive from anywhere. This door does
not, and the difference is deliberate: the lift lane's own ruling is
that the input must BE canonical rather than be forgiven into it (R6/R7,
`contract.ts`: "Decoding validates; it never repairs"). The document is
the recognizer's canonical JSON — sorted keys at every level, integers
in decimal — so the decoder matches that spelling exactly and refuses
every other one. A re-ordered document is a different instrument's
output, and the gate that compares two engines byte for byte would have
no meaning if this door quietly sorted for them.

## What is proved

- `PLine.wf_iff` / `PIn.wf_iff` — the boolean gate decides exactly the
  line well-formedness `Defun` states as a `Prop`;
- `decodeLift_wf` — SOUNDNESS: the door answers only well-formed lines;
- `decodeLift_encodeLift` — the ROUND TRIP on the document side: the
  decoder inverts the document encoder wherever the encoder is defined.
  The encoder's domain is the decoder's domain, spelled once, so this is
  the round trip AND the domain statement in one theorem;
- `encodeLift_decodeLift` — EXACTNESS, the second half of the house
  codec discipline (`bytesOfHex_exact`'s shape): the door accepts
  nothing outside the encoder's image, so the two are mutual inverses
  with no third possibility in between;
- `decodeLift_inj` — INJECTIVITY, immediate from exactness: one
  program, one document. This is what makes the P3 byte comparison mean
  what it says;
- `decodeLiftBytes_encodeLiftBytes` — the same round trip at the BYTES,
  premise-free: `encodeLift_canonical` and `encodeLift_numNormal`
  discharge what the strict parser's law asks for, so no caller carries
  a spelling hypothesis.

Owed, and named rather than assumed:

- the door's answer is only shown WELL-FORMED, not shown to RUN. A
  decoded table's operands all name strictly earlier answers by
  construction of the `refNotEarlier` gate, which is what
  `resolveRefs` needs, but that consequence is not stated as a theorem
  here. `Defun`'s own sandwich (`runPFrom_puts_sound` and friends) is
  where it would land.
- P4, and it is structural rather than owed to this module: gate-green
  is NOT run-safe. Ledger row TG1 — a type-only import erases at
  compile time, both recognition engines agree, and the program still
  `ReferenceError`s at runtime. Nothing in this file, and nothing in
  the round trip it closes, is evidence that an emitted program runs.
-/

namespace Cas.Lang

/-! ## The boolean twin of line well-formedness

`PIn.WF`/`PLine.WF` (`Cas/Lang/Defun.lean`) are `Prop`s. A door needs a
decision, so it carries the boolean twin and the agreement — the shape
`Cas.Schema.Ast.wf` / `Ast.wf_iff` established for the schema door, kept
here for the same reason: the gate that runs and the property that is
stated must be one thing. -/

/-- Boolean twin of `PIn.WF`: an answer index fits the 32-bit wire
field. -/
def PIn.wf : PIn → Bool
  | .lit _ => true
  | .ans i => decide (i < 4294967296)

/-- Boolean twin of `PLine.WF`: byte-bound fields and well-formed
operands. -/
def PLine.wf : PLine → Bool
  | .put _ _ payload refs =>
      decide (payload.length < 4294967296) &&
      decide (refs.length < 4294967296) &&
      refs.all (fun r => PIn.wf r.2)
  | .load src => PIn.wf src

/-- The gate decides exactly the operand's wire bound. -/
theorem PIn.wf_iff : ∀ i : PIn, i.wf = true ↔ i.WF
  | .lit _ => by simp [PIn.wf, PIn.WF]
  | .ans _ => by simp [PIn.wf, PIn.WF]

/-- The gate decides exactly the line's well-formedness. -/
theorem PLine.wf_iff : ∀ l : PLine, l.wf = true ↔ l.WF
  | .put _ _ payload refs => by
    simp [PLine.wf, PLine.WF, List.all_eq_true, PIn.wf_iff, and_assoc]
  | .load src => by simp [PLine.wf, PLine.WF, PIn.wf_iff]

end Cas.Lang

namespace Cas.Lift

open Cas.Json Cas.Lang

/-! ## The document, as Lean data

The TypeScript mirror is `Lift` in `experiments/lift-harness/src/contract.ts`
(`kind`, `name`, `storeBinder`, `instructions`, `helperUnpinned`). The
instruction list is not carried as its own record type: the
correspondence `Instruction{version, tag, payloadHex, refs} = PLine.put`
is exact, so the document's instructions ARE a `PProg` once decoded, and
a second carrier for them would be a second place to drift. -/

/-- A recognized straight-line program, decoded: the declaration's name,
the store parameter's name, the program itself, and the recognizer's
honest admission that rule 7 (hex-helper pinning) is off in v0.

`helperUnpinned` is carried, not judged. It is instrument metadata about
the RECOGNITION, and refusing on it would refuse every v0 document; what
it must never do is be read as a claim that the program is run-safe (see
the P4 note below). -/
structure Lifted where
  name : String
  storeBinder : String
  prog : PProg
  helperUnpinned : Bool
  deriving DecidableEq

/-- Why a document was refused. Closed, and every arm names a document
property rather than a parser accident. -/
inductive LiftRefusal where
  /-- Not the closed five-field lift document at all. -/
  | notADocument
  /-- A verdict, but not a lift: a refusal document, or another `kind`.
  The recognizer's refusals are the instrument's own vocabulary
  (`Cas.Lift.RefusalCode`) and are not programs; they die here. -/
  | notLifted
  /-- THE DIRECTION LAW. The document carries a `word` field — a
  hoover-side artifact claiming an execute-side result. Words are minted
  by running the reference handler and by nothing else, so a document
  that brought one is refused rather than trusted or stripped. -/
  | wordPresent
  /-- An instruction is not the closed five-field shape. -/
  | instructionShape
  /-- A reference is not the closed two-field shape. -/
  | refShape
  /-- An instruction's `index` is not its position in the table. The
  recognizer emits a dense, ordered table (rule `body-partition`); a
  document whose indices disagree with their positions is not one. -/
  | indexNotPosition
  /-- `version`, `tag` or `expectedTag` does not fit the wire byte. -/
  | byteOutOfRange
  /-- `payloadHex` is outside the admissible hex domain (R7: lowercase,
  even length, empty admissible, no normalization). -/
  | payloadNotHex
  /-- A reference names its own instruction or a later one. Answers are
  resolved against binders already bound, so a forward reference is
  something the instrument cannot have produced. -/
  | refNotEarlier
  /-- The line's own byte bounds (`PLine.WF`) do not hold. -/
  | lineNotWellFormed
  deriving DecidableEq, Repr

/-! ## The refusal namer

A pure diagnostic on the failure path, in the shape `Cas.Schema.ingest`
uses: it decides nothing — the decoder's own arms decide admission — it
only tells one failure apart from another, so `wordPresent` reads as the
direction-law refusal it is instead of as a shape failure. -/

private def hasWord : List (String × Json.Value) → Bool
  | [] => false
  | (k, _) :: rest => k == "word" || hasWord rest

private def isLiftedKind : List (String × Json.Value) → Bool
  | [] => false
  | ("kind", .str "lifted") :: _ => true
  | _ :: rest => isLiftedKind rest

private def refusalOf : Json.Value → LiftRefusal
  | .obj fields =>
    if hasWord fields then .wordPresent
    else if isLiftedKind fields then .notADocument
    else .notLifted
  | _ => .notADocument

/-! ## The door

Every arm is a literal shape match on the canonical spelling — sorted
keys, `Value.nat` for every non-negative number (which is the only
reading `Cas.Json.parse` gives a decimal run). Nothing is normalized and
nothing is coerced. -/

/-- One reference: `{expectedTag, source}` against the index of the
instruction that carries it. `source` becomes `PIn.ans` — the only
operand form the document can spell. -/
def decodeRef (index : Nat) : Json.Value → Except LiftRefusal (UInt8 × PIn)
  | .obj [("expectedTag", .nat t), ("source", .nat s)] =>
    if t < 256 then
      if s < index then .ok (UInt8.ofNat t, .ans s)
      else .error .refNotEarlier
    else .error .byteOutOfRange
  | _ => .error .refShape

/-- A line's whole reference list, each entry against the same index. -/
def decodeRefs (index : Nat) :
    List Json.Value → Except LiftRefusal (List (UInt8 × PIn))
  | [] => .ok []
  | v :: vs =>
    match decodeRef index v with
    | .error e => .error e
    | .ok r =>
      match decodeRefs index vs with
      | .error e => .error e
      | .ok rs => .ok (r :: rs)

/-- One instruction at its position: the closed five-field shape, the
index-is-position discipline, the byte bounds, the hex domain, and the
line's own well-formedness gate. -/
def decodeLine (index : Nat) : Json.Value → Except LiftRefusal PLine
  | .obj [("index", .nat i), ("payloadHex", .str h), ("refs", .arr rs),
          ("tag", .nat t), ("version", .nat ver)] =>
    if i = index then
      if ver < 256 then
        if t < 256 then
          match bytesOfHexS h with
          | none => .error .payloadNotHex
          | some payload =>
            match decodeRefs index rs with
            | .error e => .error e
            | .ok refs =>
              if (PLine.put (UInt8.ofNat ver) (UInt8.ofNat t) payload refs).wf
              then .ok (PLine.put (UInt8.ofNat ver) (UInt8.ofNat t) payload refs)
              else .error .lineNotWellFormed
        else .error .byteOutOfRange
      else .error .byteOutOfRange
    else .error .indexNotPosition
  | _ => .error .instructionShape

/-- The instruction table from a given position. -/
def decodeProgFrom (index : Nat) :
    List Json.Value → Except LiftRefusal PProg
  | [] => .ok []
  | v :: vs =>
    match decodeLine index v with
    | .error e => .error e
    | .ok l =>
      match decodeProgFrom (index + 1) vs with
      | .error e => .error e
      | .ok rest => .ok (l :: rest)

/-- THE DOOR: a canonical lift document, read as a program. Total, and
every refusal is named. -/
def decodeLift : Json.Value → Except LiftRefusal Lifted
  | .obj [("helperUnpinned", .bool hu), ("instructions", .arr is),
          ("kind", .str "lifted"), ("name", .str nm),
          ("storeBinder", .str sb)] =>
    match decodeProgFrom 0 is with
    | .error e => .error e
    | .ok prog =>
      .ok { name := nm, storeBinder := sb, prog, helperUnpinned := hu }
  | v => .error (refusalOf v)

/-- THE BYTES-IN DOOR: the recognizer's canonical JSON, read as a
program. `Cas.Json.parse` answers a number-normal value — every
non-negative number spelled `Value.nat` — which is exactly the spelling
the document uses, so no un-collapse step is needed here (contrast
`Cas.Schema.ingestBytes`, whose representation spells one number
`Value.int`).

Bytes that are no canonical rendering at all are refused
`notADocument`: the value plane could not spell them, so they are no
document. -/
def decodeLiftBytes (s : String) : Except LiftRefusal Lifted :=
  match Json.parse s with
  | some v => decodeLift v
  | none => .error .notADocument

/-! ## The document encoder — the round trip's other half

The canonical lift document OF a program. This is not a second
recognizer and it mints nothing: it is the statement of what the
decoder's domain is, written as a partial function whose domain is
exactly the sub-language declared above. `encodeLift l = none` IS "`l`
is outside the decoder's domain", and `decodeLift_encodeLift` says the
door inverts it everywhere it is defined.

Key order is the canonical one (sorted at every level), so the rendered
bytes are `Cas.Json.renderCompact`'s and the harness's `canonJson`'s
alike — which is what lets the P3 gate compare them. -/

/-- One operand as a `{expectedTag, source}` reference. `none` on the two
forms the document cannot spell: a literal address, and an answer that is
not strictly earlier. -/
def encodeRef (index : Nat) (r : UInt8 × PIn) : Option Json.Value :=
  match r.2 with
  | .lit _ => none
  | .ans s =>
    if s < index then
      some (.obj [("expectedTag", .nat r.1.toNat), ("source", .nat s)])
    else none

/-- A line's whole reference list. -/
def encodeRefs (index : Nat) :
    List (UInt8 × PIn) → Option (List Json.Value)
  | [] => some []
  | r :: rs =>
    match encodeRef index r with
    | none => none
    | some v =>
      match encodeRefs index rs with
      | none => none
      | some vs => some (v :: vs)

/-- One code point as one instruction at its position. `none` on a `load`
line — the recognized surface has no spelling for it. -/
def encodeLine (index : Nat) : PLine → Option Json.Value
  | .load _ => none
  | .put ver t payload refs =>
    if (PLine.put ver t payload refs).wf then
      match encodeRefs index refs with
      | none => none
      | some rs =>
        some (.obj [("index", .nat index), ("payloadHex", .str (hexS payload)),
                    ("refs", .arr rs), ("tag", .nat t.toNat),
                    ("version", .nat ver.toNat)])
    else none

/-- The instruction table from a given position. -/
def encodeProgFrom (index : Nat) : PProg → Option (List Json.Value)
  | [] => some []
  | l :: rest =>
    match encodeLine index l with
    | none => none
    | some v =>
      match encodeProgFrom (index + 1) rest with
      | none => none
      | some vs => some (v :: vs)

/-- The canonical lift document of a lifted program, when the program is
in the decoder's domain. -/
def encodeLift (l : Lifted) : Option Json.Value :=
  match encodeProgFrom 0 l.prog with
  | none => none
  | some is =>
    some (.obj [("helperUnpinned", .bool l.helperUnpinned),
                ("instructions", .arr is), ("kind", .str "lifted"),
                ("name", .str l.name), ("storeBinder", .str l.storeBinder)])

/-- The document's BYTES: the canonical value encoding, which is the
spelling the recognizer's `canonJson` emits. -/
def encodeLiftBytes (l : Lifted) : Option String :=
  (encodeLift l).map Json.renderCompact

/-! ## Soundness — the door answers only well-formed programs -/

/-- The line the door answers came through the door's own `wf` gate —
so its byte bounds hold, on the nose. -/
theorem decodeLine_wf {index : Nat} {v : Json.Value} {l : PLine}
    (h : decodeLine index v = .ok l) : l.WF := by
  simp only [decodeLine] at h
  repeat' split at h
  all_goals
    first
      | (cases h; exact (PLine.wf_iff _).mp (by assumption))
      | cases h

theorem decodeProgFrom_wf : ∀ (index : Nat) (vs : List Json.Value) (p : PProg),
    decodeProgFrom index vs = .ok p → ∀ l ∈ p, l.WF
  | _, [], p, h => by cases h; simp
  | index, v :: vs, p, h => by
    simp only [decodeProgFrom] at h
    split at h
    · cases h
    · next l hl =>
      split at h
      · cases h
      · next rest hrest =>
        cases h
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst hx; exact decodeLine_wf hl
        · exact decodeProgFrom_wf (index + 1) vs rest hrest x hx

/-- SOUNDNESS: every line the door answers is well-formed — the byte
bounds `Defun`'s interpreter assumes are established at the boundary,
not hoped for downstream. -/
theorem decodeLift_wf {v : Json.Value} {l : Lifted}
    (h : decodeLift v = .ok l) : ∀ line ∈ l.prog, line.WF := by
  unfold decodeLift at h
  split at h
  · split at h
    · cases h
    · next p hp => cases h; exact decodeProgFrom_wf 0 _ p hp
  · cases h

/-! ## The round trip on the document side

The encoder's domain IS the decoder's domain, so one theorem states
both: wherever the document encoder is defined, the door inverts it. -/

theorem decodeRef_encodeRef {index : Nat} {r : UInt8 × PIn} {v : Json.Value}
    (h : encodeRef index r = some v) : decodeRef index v = .ok r := by
  obtain ⟨t, i⟩ := r
  cases i with
  | lit a => simp [encodeRef] at h
  | ans s =>
    simp only [encodeRef] at h
    split at h
    · next hs =>
      injection h with h
      subst h
      simp only [decodeRef, if_pos t.toNat_lt, if_pos hs, Except.ok.injEq,
        Prod.mk.injEq, and_true]
      exact UInt8.ofNat_toNat
    · exact absurd h (by simp)

theorem decodeRefs_encodeRefs : ∀ (index : Nat) (rs : List (UInt8 × PIn))
    (vs : List Json.Value), encodeRefs index rs = some vs →
    decodeRefs index vs = .ok rs
  | _, [], vs, h => by
    simp only [encodeRefs, Option.some.injEq] at h
    subst h; rfl
  | index, r :: rs, vs, h => by
    simp only [encodeRefs] at h
    split at h
    · exact absurd h (by simp)
    · next v hv =>
      split at h
      · exact absurd h (by simp)
      · next ws hws =>
        injection h with h
        subst h
        simp only [decodeRefs, decodeRef_encodeRef hv,
          decodeRefs_encodeRefs index rs ws hws]

theorem decodeLine_encodeLine {index : Nat} {l : PLine} {v : Json.Value}
    (h : encodeLine index l = some v) : decodeLine index v = .ok l := by
  cases l with
  | load _ => simp [encodeLine] at h
  | put ver t payload refs =>
    simp only [encodeLine] at h
    split at h
    · next hw =>
      split at h
      · exact absurd h (by simp)
      · next rs hrs =>
        injection h with h
        subst h
        simp only [decodeLine, if_pos ver.toNat_lt, if_pos t.toNat_lt,
          bytesOfHexS_hexS, decodeRefs_encodeRefs index refs rs hrs,
          UInt8.ofNat_toNat]
        simp [hw]
    · exact absurd h (by simp)

theorem decodeProgFrom_encodeProgFrom : ∀ (index : Nat) (p : PProg)
    (vs : List Json.Value), encodeProgFrom index p = some vs →
    decodeProgFrom index vs = .ok p
  | _, [], vs, h => by
    simp only [encodeProgFrom, Option.some.injEq] at h
    subst h; rfl
  | index, l :: rest, vs, h => by
    simp only [encodeProgFrom] at h
    split at h
    · exact absurd h (by simp)
    · next v hv =>
      split at h
      · exact absurd h (by simp)
      · next ws hws =>
        injection h with h
        subst h
        simp only [decodeProgFrom, decodeLine_encodeLine hv,
          decodeProgFrom_encodeProgFrom (index + 1) rest ws hws]

/-- THE ROUND TRIP: the door inverts the document encoder wherever the
encoder is defined — which is exactly on the decoder's declared domain
(puts only, answer refs only, dense and backward-resolving). Nothing is
lost across the document and nothing is invented. -/
theorem decodeLift_encodeLift {l : Lifted} {v : Json.Value}
    (h : encodeLift l = some v) : decodeLift v = .ok l := by
  simp only [encodeLift] at h
  split at h
  · exact absurd h (by simp)
  · next is his =>
    injection h with h
    subst h
    simp only [decodeLift, decodeProgFrom_encodeProgFrom 0 l.prog is his]

/-! ### Exactness — the door accepts nothing outside the encoder's image

The second half of the house codec discipline (`bytesOfHex_exact`'s
shape): whatever the door answers, the document it answered from is the
document that program encodes. Injectivity of `decodeLift` falls out of
it — two documents that decode to one program are one document — which
is what makes "the document determines the program" a fact rather than a
hope, and what makes the P3 byte comparison mean what it says. -/

theorem encodeRef_decodeRef {index : Nat} {v : Json.Value} {r : UInt8 × PIn}
    (h : decodeRef index v = .ok r) : encodeRef index r = some v := by
  unfold decodeRef at h
  split at h
  · next t s =>
    split at h
    · next ht =>
      split at h
      · next hs =>
        injection h with h
        subst h
        simp [encodeRef, hs, UInt8.toNat_ofNat', Nat.mod_eq_of_lt ht]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem encodeRefs_decodeRefs : ∀ (index : Nat) (vs : List Json.Value)
    (rs : List (UInt8 × PIn)), decodeRefs index vs = .ok rs →
    encodeRefs index rs = some vs
  | _, [], rs, h => by
    simp only [decodeRefs, Except.ok.injEq] at h
    subst h; rfl
  | index, v :: vs, rs, h => by
    simp only [decodeRefs] at h
    split at h
    · exact absurd h (by simp)
    · next r hr =>
      split at h
      · exact absurd h (by simp)
      · next ws hws =>
        injection h with h
        subst h
        simp only [encodeRefs, encodeRef_decodeRef hr,
          encodeRefs_decodeRefs index vs ws hws]

theorem encodeLine_decodeLine {index : Nat} {v : Json.Value} {l : PLine}
    (h : decodeLine index v = .ok l) : encodeLine index l = some v := by
  unfold decodeLine at h
  split at h
  · next i hx rs t ver =>
    split at h
    · next hi =>
      split at h
      · next hver =>
        split at h
        · next ht =>
          split at h
          · exact absurd h (by simp)
          · next payload hp =>
            split at h
            · exact absurd h (by simp)
            · next refs hrefs =>
              split at h
              · next hw =>
                injection h with h
                subst h
                simp [encodeLine, hw, encodeRefs_decodeRefs index rs refs hrefs,
                  ← bytesOfHexS_exact hp, hi, UInt8.toNat_ofNat',
                  Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hver]
              · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem encodeProgFrom_decodeProgFrom : ∀ (index : Nat) (vs : List Json.Value)
    (p : PProg), decodeProgFrom index vs = .ok p →
    encodeProgFrom index p = some vs
  | _, [], p, h => by
    simp only [decodeProgFrom, Except.ok.injEq] at h
    subst h; rfl
  | index, v :: vs, p, h => by
    simp only [decodeProgFrom] at h
    split at h
    · exact absurd h (by simp)
    · next l hl =>
      split at h
      · exact absurd h (by simp)
      · next rest hrest =>
        injection h with h
        subst h
        simp only [encodeProgFrom, encodeLine_decodeLine hl,
          encodeProgFrom_decodeProgFrom (index + 1) vs rest hrest]

/-- EXACTNESS: the door accepts nothing the document encoder does not
emit. With `decodeLift_encodeLift` this makes the two functions mutual
inverses on the declared domain, with no third possibility in between. -/
theorem encodeLift_decodeLift {v : Json.Value} {l : Lifted}
    (h : decodeLift v = .ok l) : encodeLift l = some v := by
  unfold decodeLift at h
  split at h
  · next hu is nm sb =>
    split at h
    · exact absurd h (by simp)
    · next p hp =>
      injection h with h
      subst h
      simp only [encodeLift, encodeProgFrom_decodeProgFrom 0 is p hp]
  · exact absurd h (by simp)

/-- INJECTIVITY on the door's domain: one program, one document. -/
theorem decodeLift_inj {v w : Json.Value} {l : Lifted}
    (hv : decodeLift v = .ok l) (hw : decodeLift w = .ok l) : v = w := by
  have := encodeLift_decodeLift hv
  rw [encodeLift_decodeLift hw] at this
  exact (Option.some.inj this).symm

/-! ### The document is canonically spelled by construction

The bytes law needs the encoder's image to be canonical (keys already in
strict order, so `renderCompact` sorts nothing) and number-normal (every
number spelled `Value.nat`, which is the only reading the parser gives a
decimal run). Both are facts about the encoder, not hypotheses a caller
should have to carry, so they are proved here and the bytes law takes no
premises. -/

private theorem encodeRef_wire {index : Nat} {r : UInt8 × PIn} {v : Json.Value}
    (h : encodeRef index r = some v) : v.Canonical ∧ v.numNorm = v := by
  obtain ⟨t, i⟩ := r
  cases i with
  | lit a => simp [encodeRef] at h
  | ans s =>
    simp only [encodeRef] at h
    split at h
    · injection h with h
      subst h
      exact ⟨⟨by simp, by simp [Json.CanonicalFields, Json.Value.Canonical]⟩, rfl⟩
    · exact absurd h (by simp)

private theorem encodeRefs_wire : ∀ (index : Nat) (rs : List (UInt8 × PIn))
    (vs : List Json.Value), encodeRefs index rs = some vs →
    Json.CanonicalItems vs ∧ Json.numNormItems vs = vs
  | _, [], vs, h => by
    simp only [encodeRefs, Option.some.injEq] at h
    subst h
    exact ⟨trivial, rfl⟩
  | index, r :: rs, vs, h => by
    simp only [encodeRefs] at h
    split at h
    · exact absurd h (by simp)
    · next v hv =>
      split at h
      · exact absurd h (by simp)
      · next ws hws =>
        injection h with h
        subst h
        obtain ⟨hc, hn⟩ := encodeRef_wire hv
        obtain ⟨hcs, hns⟩ := encodeRefs_wire index rs ws hws
        exact ⟨⟨hc, hcs⟩, by simp [Json.numNormItems, hn, hns]⟩

private theorem encodeLine_wire {index : Nat} {l : PLine} {v : Json.Value}
    (h : encodeLine index l = some v) : v.Canonical ∧ v.numNorm = v := by
  cases l with
  | load _ => simp [encodeLine] at h
  | put ver t payload refs =>
    simp only [encodeLine] at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · next rs hrs =>
        injection h with h
        subst h
        obtain ⟨hcs, hns⟩ := encodeRefs_wire index refs rs hrs
        refine ⟨⟨by simp, ?_⟩, ?_⟩
        · simp [Json.CanonicalFields, Json.Value.Canonical, hcs]
        · simp [Json.Value.numNorm, Json.numNormFields, hns]
    · exact absurd h (by simp)

private theorem encodeProgFrom_wire : ∀ (index : Nat) (p : PProg)
    (vs : List Json.Value), encodeProgFrom index p = some vs →
    Json.CanonicalItems vs ∧ Json.numNormItems vs = vs
  | _, [], vs, h => by
    simp only [encodeProgFrom, Option.some.injEq] at h
    subst h
    exact ⟨trivial, rfl⟩
  | index, l :: rest, vs, h => by
    simp only [encodeProgFrom] at h
    split at h
    · exact absurd h (by simp)
    · next v hv =>
      split at h
      · exact absurd h (by simp)
      · next ws hws =>
        injection h with h
        subst h
        obtain ⟨hc, hn⟩ := encodeLine_wire hv
        obtain ⟨hcs, hns⟩ := encodeProgFrom_wire (index + 1) rest ws hws
        exact ⟨⟨hc, hcs⟩, by simp [Json.numNormItems, hn, hns]⟩

/-- The encoder's image is canonically spelled: `renderCompact` sorts
nothing on it, so the document's bytes are the structural fold. -/
theorem encodeLift_canonical {l : Lifted} {v : Json.Value}
    (h : encodeLift l = some v) : v.Canonical := by
  simp only [encodeLift] at h
  split at h
  · exact absurd h (by simp)
  · next is his =>
    injection h with h
    subst h
    exact ⟨by simp, by
      simp [Json.CanonicalFields, Json.Value.Canonical,
        (encodeProgFrom_wire 0 l.prog is his).1]⟩

/-- The encoder's image is number-normal: every number is spelled
`Value.nat`, which is the only reading `Cas.Json.parse` gives. -/
theorem encodeLift_numNormal {l : Lifted} {v : Json.Value}
    (h : encodeLift l = some v) : v.NumNormal := by
  simp only [encodeLift] at h
  split at h
  · exact absurd h (by simp)
  · next is his =>
    injection h with h
    subst h
    show Json.Value.numNorm _ = _
    simp [Json.Value.numNorm, Json.numNormFields,
      (encodeProgFrom_wire 0 l.prog is his).2]

/-- The round trip at the BYTES, end to end and premise-free: a
program's own canonical document bytes decode back to it. This is the
form the P3 gate exercises — the recognizer emits these bytes, and the
door reads them as the program they came from. -/
theorem decodeLiftBytes_encodeLiftBytes {l : Lifted} {s : String}
    (hs : encodeLiftBytes l = some s) : decodeLiftBytes s = .ok l := by
  simp only [encodeLiftBytes] at hs
  cases hv : encodeLift l with
  | none => simp [hv] at hs
  | some v =>
    simp only [hv, Option.map_some, Option.some.injEq] at hs
    subst hs
    simp only [decodeLiftBytes,
      Json.parse_render' (encodeLift_canonical hv) (encodeLift_numNormal hv),
      decodeLift_encodeLift hv]

/-! ## Worked at elaboration

The lane's own shapes, run through the door in the source rather than
only described in a docstring. -/

/-- "The door answered exactly this program" — the reading the calls
below make, so an outcome is compared by substance and not by a derived
instance the carrier does not have. -/
private def answered (l : Lifted) : Except LiftRefusal Lifted → Bool
  | .ok l' => decide (l' = l)
  | .error _ => false

/-- "The door refused, by THIS name" — refusals are compared by name,
which is the whole point of naming them. -/
private def refusedWith (r : LiftRefusal) : Except LiftRefusal Lifted → Bool
  | .error e => decide (e = r)
  | .ok _ => false

/-- A two-line program: a chunk, then a leaf referring to it — the
`blob` shape of the vector registry, minus the rest of the tree. -/
private def chunkThenLeaf : Lifted where
  name := "chunkThenLeaf"
  storeBinder := "store"
  helperUnpinned := true
  prog := [
    .put 0 8 [0x61, 0x62] [],
    .put 0 9 [] [(8, .ans 0)]]

-- THE ROUND TRIP, run: the program's own document decodes back to it.
#guard (match encodeLift chunkThenLeaf with
        | some v => answered chunkThenLeaf (decodeLift v)
        | none => false)

-- And through the BYTES, which is the form the harness emits.
#guard (match encodeLiftBytes chunkThenLeaf with
        | some s => answered chunkThenLeaf (decodeLiftBytes s)
        | none => false)

-- THE DIRECTION LAW, run: a document carrying a word is refused BY
-- NAME. It is not stripped, not ignored, and not read as data.
#guard refusedWith .wordPresent (decodeLiftBytes
  "{\"helperUnpinned\":true,\"instructions\":[],\"kind\":\"lifted\",\
\"name\":\"p\",\"storeBinder\":\"store\",\"word\":[]}")

-- A REFUSAL verdict is not a program: the recognizer's own vocabulary
-- dies at this door.
#guard refusedWith .notLifted (decodeLiftBytes
  "{\"code\":\"E-BRANCH\",\"detail\":\"if in statement position\",\
\"kind\":\"refusal\",\"name\":\"p\"}")

-- OUT OF DOMAIN, both halves. A `load` line has no document spelling…
#guard (encodeLift { chunkThenLeaf with prog := [.load (.ans 0)] }).isNone

-- …and neither has a literal-address operand.
#guard (encodeLift { chunkThenLeaf with
          prog := [.put 0 8 [] [(8, .lit ⟨List.replicate 32 0, by decide⟩)]] }).isNone

-- A FORWARD reference is refused: answers resolve backwards only.
#guard refusedWith .refNotEarlier (decodeLiftBytes
  "{\"helperUnpinned\":true,\"instructions\":[{\"index\":0,\
\"payloadHex\":\"\",\"refs\":[{\"expectedTag\":8,\"source\":0}],\
\"tag\":9,\"version\":0}],\"kind\":\"lifted\",\"name\":\"p\",\
\"storeBinder\":\"store\"}")

-- An INDEX that is not its position is refused: the table is dense and
-- ordered, or it is not the instrument's table.
#guard refusedWith .indexNotPosition (decodeLiftBytes
  "{\"helperUnpinned\":true,\"instructions\":[{\"index\":1,\
\"payloadHex\":\"\",\"refs\":[],\"tag\":9,\"version\":0}],\
\"kind\":\"lifted\",\"name\":\"p\",\"storeBinder\":\"store\"}")

-- R7's hex domain, at the door: UPPERCASE is not canonical, and the
-- door refuses rather than lowercasing it.
#guard refusedWith .payloadNotHex (decodeLiftBytes
  "{\"helperUnpinned\":true,\"instructions\":[{\"index\":0,\
\"payloadHex\":\"FF\",\"refs\":[],\"tag\":9,\"version\":0}],\
\"kind\":\"lifted\",\"name\":\"p\",\"storeBinder\":\"store\"}")

-- A tag that does not fit the wire byte is refused by name.
#guard refusedWith .byteOutOfRange (decodeLiftBytes
  "{\"helperUnpinned\":true,\"instructions\":[{\"index\":0,\
\"payloadHex\":\"\",\"refs\":[],\"tag\":256,\"version\":0}],\
\"kind\":\"lifted\",\"name\":\"p\",\"storeBinder\":\"store\"}")

-- Bytes that are no canonical rendering die at the parser, by name.
#guard refusedWith .notADocument (decodeLiftBytes "not json at all")

-- STRICTNESS: a document whose keys are not in canonical order is
-- REFUSED, not sorted. It says `lifted`, so the namer does not call it
-- another verdict — it calls it no document, which is what it is.
#guard refusedWith .notADocument (decodeLiftBytes
  "{\"kind\":\"lifted\",\"name\":\"p\",\"storeBinder\":\"store\",\
\"instructions\":[],\"helperUnpinned\":true}")

end Cas.Lift
