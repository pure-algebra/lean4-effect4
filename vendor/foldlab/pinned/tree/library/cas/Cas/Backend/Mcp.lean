import Cas.Schema.Notation
import Cas.Vectors.Schema
import Cas.Lang.Defun
import Cas.Codec.Hex

/-!
# The MCP surface, as data — R9 and R11 made concrete

An MCP tool IS an operation: name, params, result — with the params
and result as CANONICAL SCHEMA CODES, so the manifest is a described,
versioned, language-neutral document (R11) generated from the
signatures, never hand-written per host. Any agent programs the store
both ways through this surface: as a CLIENT of `CasSig` (the tools
below), and as a HANDLER of `LlmSig` (the system calls the agent as an
operation; its answer enters only as recorded content — R15).

The node wire shape is REUSED from the conformance-vector wire format
(`Wire.VectorNode`'s described code) — one node document across
vectors, replay, and MCP; no second spelling.

The run tool carries the straight-line program document: instructions
whose operands name an EARLIER ANSWER BY INDEX or a LITERAL ADDRESS —
the defunctionalized program (F3's first citizen). The reply is the
word.

The document is a PROJECTION, not a second program language. One
identity carries straight-line programs — `Cas.Lang.PProg`, the
defunctionalized table (`Cas/Lang/Defun.lean`) — and `RunParams` is a
SPELLING of it, converted by `RunParams.toPProg` and given its meaning
by `RunParams.run`, which is `Cas.Lang.runP` and nothing else.

## The projection grew to the whole carrier (queue item 22)

An earlier revision of this module carried two theorems saying what the
document deliberately COULD NOT say — `RunRef.ofPRef_lit` (no literal
address) and `RunInstruction.ofPLine_load` (no load). Both were true and
both were limits, not laws: they described a spelling that served the
puts-with-answer-indices sub-fragment and nothing else, which is why a
stored program could be named but never RUN by address — the tool had
no way to say "the operand is this address".

Under the ruled growth those two theorems FLIP, and the triage is worth
stating rather than leaving in a diff. They were negative statements
about a partial function; their successors are the positive statements
of the same facts:

- `RunOperand.ofPIn_lit` — a literal address HAS a spelling, and names
  it;
- `RunInstruction.ofPLine_load` — a load HAS a spelling, under the
  operand's own representability side-condition;
- `ofPProg_isSome` — THE totality theorem the pair collapses into: every
  well-formed table has a document. That is strictly stronger than the
  two refutations it replaces, because it quantifies over the carrier
  instead of over two of its constructors.

The bound in `ofPProg_isSome` is not a hedge. `PLine.WF` bounds an
answer index at the 32-bit wire field, the document's number row bounds
it at `maxSafeNat` (2^53 − 1), and the first bound implies the second —
so the side-condition is the ENCODABILITY condition the carrier already
carries, not a new limit this spelling imposes.

On the whole carrier the two spellings now coincide: `toPProg_ofPProg`
says a table the document represents converts back to that same table,
and `ofPProg_isSome` says every well-formed table is represented. The
projection loses nothing and reaches everything.

An earlier revision of this note claimed the document was "exactly the
fragment the program emitter already generates". That was wrong in its
load-bearing half and is corrected here. `Cas.Backend.EmitProg` lowers
a `Tree` straight to TypeScript statements over host variable NAMES; it
never builds a `PProg`, so there is no carrier shared with this
document and no theorem relating the two. What is true — and is prose,
not a theorem — is that the emitter emits only puts whose references
name earlier answers, so its output falls inside the same sub-fragment.
Making that a theorem means routing the emitter through `PProg`, which
is its own slice and is not taken here.
-/

namespace Cas.Backend.Mcp

open Cas.Schema Cas.Schema.Notation

/-- One operand of a code point: the index of an earlier instruction's
answer, or a literal content address.

A union rather than a widened field, for the reason `ExchangeSubject`
is one: "what this operand names" is genuinely ALTERNATIVES, and a
number that sometimes means an index and sometimes means an address is
the out-of-band spelling this estate refuses everywhere else. The
literal arm carries hex because the whole document carries bytes as
hex; a string that is not 64 hex characters denotes nothing, which is
the same partiality `payloadHex` already has. -/
cas_union RunOperand where
  | answer (index : SafeInt)
  | literal (addressHex : String)

-- The generator's discrimination claim, checked at elaboration.
#guard RunOperand.schemaCode.discriminated

/-- One reference of a straight-line instruction: the expected kind
tag, and the operand naming what it points at. -/
cas_struct RunRef where
  expectedTag : SafeInt
  source : RunOperand

/-- One straight-line instruction: admit a node whose references name
operands, or load an operand.

`load` is what makes an address-named program executable at all: a
table that begins from stored content has to say "this address" and
then require it to be THERE, which is exactly the arm the earlier
document had no spelling for. -/
cas_union RunInstruction where
  | load (source : RunOperand)
  | put (version : SafeInt) (tag : SafeInt) (payloadHex : String)
      (refs : List RunRef)

#guard RunInstruction.schemaCode.discriminated

/-- LAW SM-22: this spells the WHOLE program table — literal-address
operands and loads included — so a stored program can be named by the
document that runs it. The ruling MOVED on 2026-08-29; it used to say
the opposite, and `Law.registry`'s row moved with it.

The run tool's params: a straight-line program.

NOT "self-contained", and the word was struck rather than softened. It
was true of the answer-index fragment — a document whose operands only
name earlier answers depends on nothing but itself, and `RunParams.run`
could be handed the empty word. It is FALSE of the grown document: a
literal-address operand and a `load` are questions about what the store
already holds, so a run's meaning is relative to its STARTING WORD.
`RunParams.run` has always taken that word as an argument; what changed
is that it is now load-bearing rather than ceremonial. -/
cas_struct RunParams where
  instructions : List RunInstruction

/-- The run-by-address tool's params: the address of a `cont` node.

There is no second field, and the absence is the design. A program is
content; its address is its identity; everything the tool needs to know
about it is reachable from that address by loading. A name, a version,
or an inlined copy beside the address would each be a second spelling
of a fact the store already holds. -/
cas_struct RunRefParams where
  root : String

/-- One answered binding. -/
cas_struct WordEntry where
  address : String

/-- The run tool's reply: the word, in admission order. -/
cas_struct RunResult where
  word : List WordEntry

/-! ## The projection onto the one program carrier

Everything in this section is about IDENTITY, not about the manifest:
the manifest's bytes are fixed by `tools` below and are untouched by
what follows. -/

/-- A byte as a document number — the registry's own conversion
(`Cas.Vectors.safeOfUInt8`), not a second one. -/
private abbrev safeOfUInt8 : UInt8 → SafeInt := Cas.Vectors.safeOfUInt8

/-- An in-range index as a document number. -/
private def safeOfNat (i : Nat) (h : i ≤ maxSafeNat) : SafeInt :=
  ⟨Int.ofNat i, by simpa using h⟩

/-- The document's operand as the carrier's. Partial only where the
carrier is stricter than the document: an address is 32 bytes, and a
hex string of any other length denotes no address at all. -/
def RunOperand.toPIn : RunOperand → Option Cas.Lang.PIn
  | .answer i => some (.ans i.val.natAbs)
  | .literal h =>
    (Cas.bytesOfHexS h).bind fun bs =>
      if p : bs.length = 32 then some (.lit ⟨bs, p⟩) else none

/-- The document's reference as an operand of the one carrier: an
expected kind tag and the operand. -/
def RunRef.toPRef (r : RunRef) : Option (UInt8 × Cas.Lang.PIn) :=
  r.source.toPIn.map fun i => (UInt8.ofNat r.expectedTag.val.natAbs, i)

/-- References as the carrier's operands. -/
def toPRefs : List RunRef → Option (List (UInt8 × Cas.Lang.PIn))
  | [] => some []
  | r :: rest =>
    r.toPRef.bind fun x => (toPRefs rest).map fun xs => x :: xs

/-- One instruction as one code point of the one carrier. Partial in
the payload and in the operands: the document spells bytes as hex, and
a string that is not hex denotes nothing. -/
def RunInstruction.toPLine : RunInstruction → Option Cas.Lang.PLine
  | .load src => src.toPIn.map .load
  | .put v t payloadHex refs =>
    (Cas.bytesOfHexS payloadHex).bind fun payload =>
      (toPRefs refs).map fun rs =>
        .put (UInt8.ofNat v.val.natAbs) (UInt8.ofNat t.val.natAbs) payload rs

/-- The instruction list as a code-point table. -/
def toPLines : List RunInstruction → Option Cas.Lang.PProg
  | [] => some []
  | i :: rest =>
    (i.toPLine).bind fun l => (toPLines rest).map fun ls => l :: ls

/-- THE conversion: the run tool's document IS a `Cas.Lang.PProg`,
spelled smaller. -/
def RunParams.toPProg (d : RunParams) : Option Cas.Lang.PProg :=
  toPLines d.instructions

/-- The run tool's MEANING, and its only one: convert to the carrier
and hand it to the carrier's direct interpreter. There is no second
semantics for this tool — `Cas.Lang.runP` agrees with the reference
handler (`runP_embed_agree`, and through it the R10 bridge
`run_interpretRef_agree`), so the word this tool replies with is the
word the semantics defines. -/
def RunParams.run (H : Bytes → Addr32) (d : RunParams) (w : Word) :
    Option (Cas.Lang.Status Cas.Lang.CasSig Addr32 × Word) :=
  d.toPProg.map fun p => Cas.Lang.runP H p w

/-- A carrier operand back as a document one. Partial only at the
number row: an answer index past `maxSafeNat` has no document spelling,
which is the same bound every other number in this document obeys. A
literal address always has one. -/
def RunOperand.ofPIn : Cas.Lang.PIn → Option RunOperand
  | .lit a => some (.literal (Cas.hexS a.val))
  | .ans i => if h : i ≤ maxSafeNat then some (.answer (safeOfNat i h)) else none

/-- A code point's operand back as a document reference. -/
def RunRef.ofPRef (r : UInt8 × Cas.Lang.PIn) : Option RunRef :=
  (RunOperand.ofPIn r.2).map fun src => ⟨safeOfUInt8 r.1, src⟩

/-- Operands back as document references. -/
def ofPRefs : List (UInt8 × Cas.Lang.PIn) → Option (List RunRef)
  | [] => some []
  | r :: rest =>
    (RunRef.ofPRef r).bind fun d => (ofPRefs rest).map fun ds => d :: ds

/-- A code point back as an instruction. -/
def RunInstruction.ofPLine : Cas.Lang.PLine → Option RunInstruction
  | .put v t payload refs =>
    (ofPRefs refs).map fun rs =>
      .put (safeOfUInt8 v) (safeOfUInt8 t) (Cas.hexS payload) rs
  | .load src => (RunOperand.ofPIn src).map .load

/-- A code-point table back as an instruction list. -/
def ofPLines : Cas.Lang.PProg → Option (List RunInstruction)
  | [] => some []
  | l :: rest =>
    (RunInstruction.ofPLine l).bind fun i =>
      (ofPLines rest).map fun is => i :: is

/-- A table back as a document. -/
def RunParams.ofPProg (p : Cas.Lang.PProg) : Option RunParams :=
  (ofPLines p).map RunParams.mk

/-! ### The flipped pair (queue item 22)

`RunRef.ofPRef_lit` and `RunInstruction.ofPLine_load` used to say the
document had NO spelling for a literal address and NO spelling for a
load. Under the growth both facts reverse, and each is restated as the
positive fact it became rather than deleted: a refutation that flips is
a theorem about the new surface, not a theorem to discard. -/

/-- FLIPPED (was: the document cannot say a literal address). It can,
and this names the spelling: the address as hex, under the operand's
own arm. -/
theorem RunOperand.ofPIn_lit (a : Addr32) :
    RunOperand.ofPIn (.lit a) = some (.literal (Cas.hexS a.val)) := rfl

/-- FLIPPED (was: the document cannot say a literal-address
reference). -/
theorem RunRef.ofPRef_lit (t : UInt8) (a : Addr32) :
    RunRef.ofPRef (t, .lit a)
      = some ⟨safeOfUInt8 t, .literal (Cas.hexS a.val)⟩ := rfl

/-- FLIPPED (was: the document cannot say a `load`). It can, exactly
when the loaded operand has a spelling — which, by `ofPIn_lit` above
and the number row's bound, is every literal and every in-range
index. -/
theorem RunInstruction.ofPLine_load (src : Cas.Lang.PIn) :
    RunInstruction.ofPLine (.load src)
      = (RunOperand.ofPIn src).map .load := rfl

/-- A byte survives the trip through the document's number row. -/
private theorem ofNat_natAbs_safeOfUInt8 (b : UInt8) :
    UInt8.ofNat (safeOfUInt8 b).val.natAbs = b := by
  show UInt8.ofNat b.toNat = b
  have hb := b.toNat_lt
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofNat']
  omega

/-- An operand survives the round trip. The literal arm is where the
address subtype meets the hex row: `bytesOfHexS_hexS` returns the
bytes, and the 32-byte proof is the address's own. -/
private theorem toPIn_ofPIn {x : Cas.Lang.PIn} {o : RunOperand}
    (h : RunOperand.ofPIn x = some o) : o.toPIn = some x := by
  cases x with
  | lit a =>
    simp only [RunOperand.ofPIn, Option.some.injEq] at h
    subst h
    simp only [RunOperand.toPIn, Cas.bytesOfHexS_hexS, Option.bind_some,
      dif_pos a.property]
  | ans i =>
    by_cases hb : i ≤ maxSafeNat
    · simp only [RunOperand.ofPIn, dif_pos hb, Option.some.injEq] at h
      subst h
      simp [RunOperand.toPIn, safeOfNat]
    · exact absurd h (by simp [RunOperand.ofPIn, dif_neg hb])

private theorem toPRef_ofPRef {r : UInt8 × Cas.Lang.PIn} {d : RunRef}
    (h : RunRef.ofPRef r = some d) : d.toPRef = some r := by
  obtain ⟨t, src⟩ := r
  cases ho : RunOperand.ofPIn src with
  | none => rw [RunRef.ofPRef, ho] at h; exact absurd h (by simp)
  | some o =>
    rw [RunRef.ofPRef, ho] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    simp [RunRef.toPRef, toPIn_ofPIn ho, ofNat_natAbs_safeOfUInt8]

private theorem toPRefs_ofPRefs :
    ∀ (refs : List (UInt8 × Cas.Lang.PIn)) (ds : List RunRef),
      ofPRefs refs = some ds → toPRefs ds = some refs
  | [], ds, h => by simp only [ofPRefs, Option.some.injEq] at h; subst h; rfl
  | r :: rest, ds, h => by
    cases hd : RunRef.ofPRef r with
    | none => rw [ofPRefs, hd] at h; exact absurd h (by simp)
    | some d =>
      cases hs : ofPRefs rest with
      | none => rw [ofPRefs, hd, hs] at h; exact absurd h (by simp)
      | some ds' =>
        rw [ofPRefs, hd, hs] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [toPRefs, toPRef_ofPRef hd, toPRefs_ofPRefs rest ds' hs,
          Option.bind_some, Option.map_some]

private theorem toPLine_ofPLine {l : Cas.Lang.PLine} {i : RunInstruction}
    (h : RunInstruction.ofPLine l = some i) : i.toPLine = some l := by
  cases l with
  | load src =>
    cases ho : RunOperand.ofPIn src with
    | none => rw [RunInstruction.ofPLine, ho] at h; exact absurd h (by simp)
    | some o =>
      rw [RunInstruction.ofPLine, ho] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp [RunInstruction.toPLine, toPIn_ofPIn ho]
  | put v t payload refs =>
    cases hr : ofPRefs refs with
    | none => rw [RunInstruction.ofPLine, hr] at h; exact absurd h (by simp)
    | some ds =>
      rw [RunInstruction.ofPLine, hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp [RunInstruction.toPLine, Cas.bytesOfHexS_hexS, ofNat_natAbs_safeOfUInt8,
        toPRefs_ofPRefs refs ds hr]

private theorem toPLines_ofPLines :
    ∀ (p : Cas.Lang.PProg) (is : List RunInstruction),
      ofPLines p = some is → toPLines is = some p
  | [], is, h => by simp only [ofPLines, Option.some.injEq] at h; subst h; rfl
  | l :: rest, is, h => by
    cases hi : RunInstruction.ofPLine l with
    | none => rw [ofPLines, hi] at h; exact absurd h (by simp)
    | some i =>
      cases hs : ofPLines rest with
      | none => rw [ofPLines, hi, hs] at h; exact absurd h (by simp)
      | some is' =>
        rw [ofPLines, hi, hs] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [toPLines, toPLine_ofPLine hi, toPLines_ofPLines rest is' hs,
          Option.bind_some, Option.map_some]

/-! ### Totality — what the flipped pair became

`RunRef.ofPRef_lit` and `RunInstruction.ofPLine_load` used to be two
refutations. Their real content was that `ofPProg` was PARTIAL on the
carrier for two structural reasons. Both reasons are gone, so the
honest successor is not two more equations but the statement that the
partiality is gone: every well-formed table has a document.

The remaining partiality is the number row's, and it is inherited
rather than imposed — `PLine.WF` already bounds an answer index at the
32-bit wire field, which is far inside `maxSafeNat`. -/

private theorem ofPIn_some_of_wf {x : Cas.Lang.PIn} (h : x.WF) :
    ∃ o, RunOperand.ofPIn x = some o := by
  cases x with
  | lit a => exact ⟨_, rfl⟩
  | ans i =>
    have hi : i < 4294967296 := h
    exact ⟨_, dif_pos (by simp only [maxSafeNat]; omega)⟩

private theorem ofPRef_some_of_wf {r : UInt8 × Cas.Lang.PIn} (h : r.2.WF) :
    ∃ d, RunRef.ofPRef r = some d := by
  obtain ⟨o, ho⟩ := ofPIn_some_of_wf h
  exact ⟨_, by rw [RunRef.ofPRef, ho]; rfl⟩

private theorem ofPRefs_some_of_wf :
    ∀ (refs : List (UInt8 × Cas.Lang.PIn)), (∀ r ∈ refs, r.2.WF) →
      ∃ ds, ofPRefs refs = some ds
  | [], _ => ⟨[], rfl⟩
  | r :: rest, h => by
    obtain ⟨d, hd⟩ := ofPRef_some_of_wf (h r List.mem_cons_self)
    obtain ⟨ds, hs⟩ :=
      ofPRefs_some_of_wf rest fun x hx => h x (List.mem_cons_of_mem r hx)
    exact ⟨d :: ds, by rw [ofPRefs, hd, hs]; rfl⟩

private theorem ofPLine_some_of_wf {l : Cas.Lang.PLine} (h : l.WF) :
    ∃ i, RunInstruction.ofPLine l = some i := by
  cases l with
  | load src =>
    obtain ⟨o, ho⟩ := ofPIn_some_of_wf h
    exact ⟨_, by rw [RunInstruction.ofPLine, ho]; rfl⟩
  | put v t payload refs =>
    obtain ⟨ds, hs⟩ := ofPRefs_some_of_wf refs h.2.2
    exact ⟨_, by rw [RunInstruction.ofPLine, hs]; rfl⟩

private theorem ofPLines_some_of_wf :
    ∀ (p : Cas.Lang.PProg), (∀ l ∈ p, l.WF) → ∃ is, ofPLines p = some is
  | [], _ => ⟨[], rfl⟩
  | l :: rest, h => by
    obtain ⟨i, hi⟩ := ofPLine_some_of_wf (h l List.mem_cons_self)
    obtain ⟨is, hs⟩ :=
      ofPLines_some_of_wf rest fun x hx => h x (List.mem_cons_of_mem l hx)
    exact ⟨i :: is, by rw [ofPLines, hi, hs]; rfl⟩

/-- THE TOTALITY THEOREM (queue item 22, discharged): every well-formed
table has a document. This is what the two refutations became — one
statement over the carrier in place of two about its constructors, and
strictly stronger than their conjunction. -/
theorem ofPProg_isSome {p : Cas.Lang.PProg} (h : ∀ l ∈ p, l.WF) :
    (RunParams.ofPProg p).isSome := by
  obtain ⟨is, hs⟩ := ofPLines_some_of_wf p h
  simp [RunParams.ofPProg, hs]

/-- THE AGREEMENT: the two spellings coincide. A `Cas.Lang.PProg` that
this document represents at all converts back to exactly that table —
the projection loses nothing on its own image — and by `ofPProg_isSome`
that image is every well-formed table. So `RunParams` adds a spelling
and not an identity. -/
theorem toPProg_ofPProg {p : Cas.Lang.PProg} {d : RunParams}
    (h : RunParams.ofPProg p = some d) : d.toPProg = some p := by
  cases hs : ofPLines p with
  | none => rw [RunParams.ofPProg, hs] at h; exact absurd h (by simp)
  | some is =>
    rw [RunParams.ofPProg, hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact toPLines_ofPLines p is hs

/-- The meaning transfers with the spelling: a table the document can
spell is RUN by the document exactly as the carrier runs it. -/
theorem run_ofPProg (H : Bytes → Addr32) {p : Cas.Lang.PProg}
    {d : RunParams} (h : RunParams.ofPProg p = some d) (w : Word) :
    d.run H w = some (Cas.Lang.runP H p w) := by
  simp [RunParams.run, toPProg_ofPProg h]

/-! ### The projection, executed

`toPProg_ofPProg` is the law; these are the witnesses that it is not
vacuous — a real two-line table in the served fragment, and the two
carrier shapes the document has no spelling for. -/

/-- A two-line table inside the sub-fragment: a value node, then a tree
node referencing the first line's answer. -/
private def sampleTable : Cas.Lang.PProg :=
  [ .put 0 1 [0xAB, 0xCD] [],
    .put 0 9 [] [(1, .ans 0)] ]

#guard (RunParams.ofPProg sampleTable).bind RunParams.toPProg
  = some sampleTable

/-- The table the earlier document had NO spelling for, and the reason
address-named programs could not run: a literal-address operand and a
load. Both round-trip now — this is the flipped pair, executed. -/
private def growthTable : Cas.Lang.PProg :=
  [ .load (.lit ⟨List.replicate 32 0xAB, by simp⟩),
    .put 0 9 [] [(1, .lit ⟨List.replicate 32 0xAB, by simp⟩)],
    .load (.ans 1) ]

#guard (RunParams.ofPProg growthTable).bind RunParams.toPProg
  = some growthTable

-- The load-only table the earlier `#guard` asserted was UNSPELLABLE.
-- It is spellable now, and the guard is flipped rather than deleted.
#guard (RunParams.ofPProg [Cas.Lang.PLine.load (.ans 0)]).isSome

/-- An MCP tool: an operation with described params and reply. -/
structure McpTool where
  name : String
  description : String
  params : Ast
  result : Ast

private def addressDoc : Ast := .struct [("address", false, .str)]

private def nodeDoc : Ast := Described.code (α := Cas.Vectors.Wire.VectorNode)

private def emptyDoc : Ast := .struct []

private def rootsDoc : Ast :=
  .struct [("roots", false, .arr .str)]

/-- The CAS tool table — `CasSig` and the root signature, projected. -/
def tools : List McpTool := [
  { name := "cas_put"
    description := "Admit one node; the reply is its content address. Admission is the only gate: well-formedness, reference presence, and kind agreement are checked, duplicates are inert, collisions refuse."
    params := nodeDoc
    result := addressDoc },
  { name := "cas_load"
    description := "Load the node at an address, fail-closed: the frame is parsed exactly and the kind is answered as stored."
    params := addressDoc
    result := nodeDoc },
  { name := "cas_run"
    description := "Run a straight-line program submitted inline: instructions in admission order, operands naming an earlier answer by index or a literal address, and loads requiring the address to be there. The reply is the word — the run's history, byte-decidable evidence."
    params := RunParams.schemaCode
    result := RunResult.schemaCode },
  { name := "cas_run_ref"
    description := "Run the program stored at an address: load the cont node, recover its table from the step nodes it names, and run it through the same admission doors. The reply is the word. A program is content, so this names one the way everything else in the store is named."
    params := RunRefParams.schemaCode
    result := RunResult.schemaCode },
  { name := "cas_publish_root"
    description := "Publish an address as a root."
    params := addressDoc
    result := emptyDoc },
  { name := "cas_list_roots"
    description := "List the published roots."
    params := emptyDoc
    result := rootsDoc }
]

/-- The manifest revision — bumped only by ruling.

Revision 1 (2026-08-29, the brain-stem package): `RunParams` grew
literal-address operands and the `load` instruction (queue item 22), so
`cas_run`'s params moved; and `cas_run_ref` joined the table, so a
program stored at an address can be run by naming it. The bump is what
the boot gate exists for — a host serving the old params against this
manifest is refused at start rather than at the first call. -/
def manifestVersion : Nat := 1

private def toolJson (t : McpTool) : Cas.Json.Value :=
  .obj [
    ("name", .str t.name),
    ("description", .str t.description),
    ("params", t.params.toJson),
    ("result", t.result.toJson)]

/-- The manifest: the versioned, language-neutral interchange document
(R11). Params and results are canonical schema projections — the same
tagged form the schema plane byte-pins across runtimes. -/
def manifest : Cas.Json.Value :=
  .obj [
    ("manifestVersion", .nat manifestVersion),
    ("language", .str "cas"),
    ("schemaRevision", .nat schemaRevision),
    ("tools", .arr (tools.map toolJson))]

/-- The rendered manifest document (manifest layout, trailing newline
— the fixture form). -/
def document : String := Cas.Json.render manifest ++ "\n"

end Cas.Backend.Mcp
