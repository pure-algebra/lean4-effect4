/-
PDD-3 — THE RE-ATTACK, against the fix pass.  Attack module 2.

SUBJECT      branch `agent/opus-cc-mac/pdd-3`, tip `c700279d`
             (fix-pass close); the fixes in `766d695f` (packet),
             `f8a2da76` (F2, N2), `599ef9eb` (F3), `c6a70338` (F1, F4,
             F5).  Attacked from `attack/opus-cc-mac/pdd-3` merged onto
             that tip.
FIRST PASS   `Attack.lean` + `RESULTS.md` beside this file, against
             `92a64ec4`.  UNTOUCHED — its one red guard
             (`dupHarmlessLast`, §7) is F1's receipt and stays red.
VERDICT      `RESULTS.md` §RE-RUN.

OUTSIDE EVERY LAKE TARGET, like its sibling.  Run: from `library/cas`,
    lake env lean contracts/attacks/PDD-3/Attack2.lean
Silence is a pass.  Measurements (wall clock, the TypeScript door, the
corpus sweep) are in `RESULTS.md` §RE-RUN with the code that produced
them.
-/
import Cas.Schema.Ingest

open Cas.Schema

namespace PDD3.Attack2

def refusalName : IngestRefusal → String
  | .notASchema => "notASchema" | .illFormed => "illFormed"
  | .wrongRevision => "wrongRevision" | .nonEmptyReferences => "nonEmptyReferences"
  | .unguardedCycle => "unguardedCycle" | .unknownDeclaration => "unknownDeclaration"

/-- The bytes door for DOCUMENTS, still composed by hand: `ingestBytes`
remains the bare-code arm and `ingestDocumentBytes` is still owed
(first pass, note N5). -/
def bytes (s : String) : Except IngestRefusal Document :=
  match Cas.Json.parse s with
  | some v => ingestDocument (deNumNorm v)
  | none => .error .notASchema

def answers (s : String) (r : IngestRefusal) : Bool :=
  match bytes s with
  | .error e => e == r
  | .ok _ => false

def admitted (s : String) : Bool :=
  match bytes s with | .ok _ => true | .error _ => false

def str : String := "{\"_tag\":\"String\",\"checks\":[]}"
def nul : String := "{\"_tag\":\"Null\",\"checks\":[]}"
def selfRef : String := "{\"$ref\":\"A\",\"_tag\":\"Reference\"}"
def env (refs rep : String) : String :=
  s!"\{\"revision\":1,\"value\":\{\"references\":\{{refs}},\"representation\":{rep}}}"

/-! ############################################################
## §1 — F1 CLOSED: one name, both key-position orders, every variant

The first pass's BREAK was one byte string read as two documents. The
gate is now `duplicateReferenceKey`, ahead of the decoder, so the answer
no longer depends on which pair a parser kept — nor on what else is
wrong with the document. The TypeScript half of each row is in
`RESULTS.md` §RE-RUN; every one of these answers `illFormed` there too.

Note what the first pass got WRONG, corrected here: the shipped BYTES
door (`Materialize.fromPayload`) never admitted these payloads. It
refused them at `decodedVersionedEnvelope`'s canonical re-render, which
predates the fix — ANONYMOUSLY, as a `TypeError`. The admit the first
pass exhibited came through `CanonicalSchema.fromEnvelope`, the
in-memory door, which takes a value `JSON.parse` has already
de-duplicated. So F1 was a NAMING divergence on the shipped path, not
an admit/refuse one. -/

-- The two key-position orders — the pair whose answers used to differ.
#guard answers (env s!"\"A\":{selfRef},\"A\":{str}" str) .illFormed
#guard answers (env s!"\"A\":{str},\"A\":{selfRef}" str) .illFormed

-- NEW spellings the fix pass did not name.
#guard answers (env s!"\"A\":{str},\"A\":{str}" str) .illFormed          -- identical values
#guard answers (env s!"\"A\":{str},\"A\":{nul},\"A\":{selfRef}" str) .illFormed  -- three-way
#guard answers (env s!"\"A\":{nul},\"A\":{nul},\"A\":{nul}" str) .illFormed      -- three identical

-- THE PARTNERS, without which refusing every table would pass.
#guard admitted (env s!"\"A\":{str},\"B\":{nul}" str)
#guard admitted (env s!"\"A\":{str}" str)
#guard admitted (env "" str)

/-! ### The node-level twin is still OWED, not silently fixed

The gate is scoped to the references table, as the packet says. A
duplicate `_tag` on a NODE still dies in Lean's exact decoder rather
than at a named byte gate, and a duplicate key INSIDE a table entry does
too. On the TypeScript side both are refused by the canonical re-render
without a name, which is the "one 'the bytes are not a canonical
spelling' refusal, named" that the packet records as owed. -/

#guard answers
  "{\"revision\":1,\"value\":{\"references\":{},\"representation\":{\"_tag\":\"String\",\"_tag\":\"Null\",\"checks\":[]}}}"
  .notASchema

#guard answers
  s!"\{\"revision\":1,\"value\":\{\"references\":\{\"A\":\{\"_tag\":\"String\",\"_tag\":\"Null\",\"checks\":[]}},\"representation\":{str}}}"
  .notASchema

/-! ### HOLE R1 — the two duplicate gates are not the same gate

Lean's `duplicateReferenceKey` pattern-matches the CANONICAL envelope
(`revision`/`value`, then `references`/`representation`, exactly two
keys each) and answers `false` for anything else. TypeScript's is a byte
scanner keyed on the container PATH `["value","references"]` and does
not care what else the envelope carries.

So a payload that is BOTH shape-broken and duplicate-keyed splits: Lean
falls through to the decoder and answers `notASchema`; TypeScript's
scanner fires first and answers `illFormed`. Both refuse — this is a
naming divergence, not an admission one — but `SchemaVerdicts.test.ts`
gates refusal names, so a corpus row for it would go red. -/

/-- An extra key in `value`, plus a duplicate table key. -/
def extraKeyAndDuplicate : String :=
  s!"\{\"revision\":1,\"value\":\{\"extra\":0,\"references\":\{\"A\":{str},\"A\":{nul}},\"representation\":{str}}}"

#guard answers extraKeyAndDuplicate .notASchema   -- TypeScript: illFormed

/-! ### HOLE R2 — the scanner unescapes for a reader that cannot read escapes

`CanonicalSchema.ts`'s `stringLiteral` exists so that `"A"` and
`"\u0041"` compare equal, and its stated reason is that they "are the
same name to Lean's reader". They are not: `Cas.Json.parse` has no
`\uXXXX` case at all and refuses the payload outright — in a KEY or in a
VALUE — while `\n`, `\"` and `\\` all parse. So the escaped-duplicate
spelling is `illFormed` in TypeScript and `notASchema` in Lean, and the
premise written into the docstring is false.

Pre-existing and far outside C6 — the parser is `Cas.Values.Json` — but
the sentence claiming the agreement is new in `c6a70338`. -/

#guard (Cas.Json.parse "{\"a\":\"A\"}").isSome
#guard !(Cas.Json.parse "{\"a\":\"\\u0041\"}").isSome
#guard !(Cas.Json.parse "{\"\\u0041\":\"x\"}").isSome
#guard (Cas.Json.parse "{\"a\":\"\\n\"}").isSome
#guard (Cas.Json.parse "{\"a\":\"\\\"\"}").isSome

/-! ############################################################
## §2 — F5 CLOSED: one refusal order, and the decoder still wins

`documentRefusal` tests guardedness first; the TypeScript gate now HOLDS
its `illFormed` refusals and replays them after the guardedness filter,
while `notASchema` and `unknownDeclaration` — the decoder's own answers
— are rethrown at once. Every row below matches on both hosts
(`RESULTS.md` §RE-RUN). The two that matter are the last pair: a table
that is cyclic AND undecodable is named for the DECODER, not the
cycle. -/

def objs (fields : String) : String :=
  s!"\{\"_tag\":\"Objects\",\"checks\":[],\"indexSignatures\":[],\"propertySignatures\":[{fields}]}"
def prop (n t : String) : String :=
  s!"\{\"isMutable\":false,\"isOptional\":false,\"name\":\{\"type\":\"string\",\"value\":\"{n}\"},\"type\":{t}}"
def bigint : String := "{\"_tag\":\"BigInt\",\"checks\":[]}"
def unknownDecl : String :=
  "{\"_tag\":\"Declaration\",\"checks\":[],\"representation\":{\"id\":\"effect/schema/Duration\",\"payload\":null},\"typeParameters\":[]}"

-- cycle + ill-formed entry -> the CYCLE
#guard answers (env s!"\"A\":{objs s!"{prop "b" selfRef},{prop "a" str}"}" selfRef)
  .unguardedCycle
-- ill formed alone -> illFormed (the control: the cycle is doing the work)
#guard answers (env s!"\"A\":{objs s!"{prop "b" str},{prop "a" str}"}" selfRef)
  .illFormed
-- cycle + empty table key -> the CYCLE
#guard answers (env s!"\"\":{str},\"A\":{selfRef}" selfRef) .unguardedCycle
-- cycle + ill-formed ROOT -> the CYCLE
#guard answers (env s!"\"A\":{selfRef}" (objs s!"{prop "b" str},{prop "a" str}"))
  .unguardedCycle
-- cycle + UNDECODABLE entry -> the DECODER wins
#guard answers (env s!"\"A\":{selfRef},\"B\":{bigint}" selfRef) .notASchema
-- cycle + UNKNOWN DECLARATION -> the decoder's other answer wins
#guard answers (env s!"\"A\":{selfRef},\"B\":{unknownDecl}" selfRef) .unknownDeclaration
-- undecodable root, guarded table -> the decoder
#guard answers (env s!"\"A\":{str}" bigint) .notASchema

/-! ############################################################
## §3 — F3 CLOSED, and the memo probed for the classic error

`Document.guardedMemo` is the procedure the door RUNS: `Document.wf`
(`Ingest.lean:394`) and `documentRefusal` (`:415`) both call it, and
`Document.wf_iff` goes through `references_guarded_decidable_memo`. The
naive `Document.guarded` survives only as the thing the memo is proved
equal to. So `guardedMemo_eq_guarded`'s subject is the shipped
procedure and not a paper twin.

THE CLASSIC ERROR: a memo that records a name on ENTRY calls a cycle
settled, because the name is already in the set when the walk comes
back round to it. `settleAllEntry` below is that error, written out.
The builder's control — the fan with its tail wired back to its head —
DOES fire against it, and so do the two cycle witnesses that were
already there. -/

def fanE (i : Nat) : String × Ast :=
  (s!"n{i}", .struct [("x", false, .reference s!"n{i+1}"),
                      ("y", false, .reference s!"n{i+1}")])

def fanT (n : Nat) : Document :=
  { references := (List.range n).map fanE ++ [(s!"n{n}", .str)],
    representation := .reference "n0" }

/-- The same fan with its tail wired back to the head — the builder's
control, and a cycle every name reaches twice over. -/
def fanCycle (n : Nat) : Document :=
  { references := (List.range n).map fanE ++ [(s!"n{n}", .reference "n0")],
    representation := .reference "n0" }

/-- THE ERROR, implemented: the name enters the memo on the way IN. -/
def settleAllEntry (d : Document) :
    Nat → List String → List String → Option (List String)
  | _, seen, [] => some seen
  | 0, seen, n :: ns =>
    if seen.contains n then settleAllEntry d 0 seen ns
    else if (d.out n).isEmpty then settleAllEntry d 0 (n :: seen) ns
    else none
  | fuel + 1, seen, n :: ns =>
    if seen.contains n then settleAllEntry d (fuel + 1) seen ns
    else
      match settleAllEntry d fuel (n :: seen) (d.out n) with
      | some s => settleAllEntry d (fuel + 1) s ns
      | none => none
termination_by fuel _ ns => (fuel, ns.length)

def guardedEntryMemo (d : Document) : Bool :=
  (settleAllEntry d d.references.length [] d.names).isSome

-- THE CONTROL FIRES: the on-entry memo ADMITS the tail-wired fan; the
-- shipped memo and the naive walk both refuse it.
#guard !(fanCycle 8).guardedMemo
#guard !(fanCycle 8).guarded
#guard guardedEntryMemo (fanCycle 8)
#guard !(fanCycle 40).guardedMemo
#guard guardedEntryMemo (fanCycle 40)

-- And it is over-covered: the two cycle witnesses that predate the memo
-- catch the same error, so the control is a second net rather than the
-- only one.
#guard guardedEntryMemo aliasCycle
#guard guardedEntryMemo bareStructCycle

-- The two walks agree wherever the naive one can still be run, and the
-- door answers the cycle by name at a size the naive walk cannot reach.
#guard (fanT 8).guarded == (fanT 8).guardedMemo
#guard (fanT 12).guarded == (fanT 12).guardedMemo
#guard (fanT 40).guardedMemo
#guard (match ingestDocument (fanCycle 40).envelope with
        | .error .unguardedCycle => true | _ => false)

/-! ############################################################
## §4 — F2: the prose narrowed, the semantics did not

The first pass predicted that closing F2 would stop §2's three theorems
from elaborating. It did not, and that is the honest outcome: the fix
narrowed what the door CLAIMS (constructibility, not productivity) and
left the admission semantics alone, because changing them is a ruling.
The three witnesses are still `Guarded` and still admitted, and they are
now cited in `Guarded.lean`'s own "What this does NOT decide". -/

def w1 : Document := { references := [("A", .susp (.reference "A"))],
                       representation := .reference "A" }
def w2 : Document := { references := [("A", .susp (.union [.reference "A", .null] .anyOf))],
                       representation := .reference "A" }
def w3 : Document := { references := [("A", .susp (.reference "B")), ("B", .reference "A")],
                       representation := .reference "A" }

#guard w1.guardedMemo && w2.guardedMemo && w3.guardedMemo
#guard (match ingestDocument w1.envelope with | .ok _ => true | .error _ => false)
#guard (match ingestDocument w2.envelope with | .ok _ => true | .error _ => false)
#guard (match ingestDocument w3.envelope with | .ok _ => true | .error _ => false)

/-! ############################################################
## §5 — F4 CLOSED, re-derived from the CORPUS and not from four names

The first pass's `guardedWrong` guards named the four C6 rows by hand.
The builder's note asked a follow-on breaker to read the corpus
instead, which `RESULTS.md` §RE-RUN does: all 76 rows, 61 decodable,
fuel-zero agrees on 59 and disagrees on exactly
`admit-reference-chain` and `admit-reference-chain-two` — the two new
rows — and six rows now carry a non-empty bare-edge relation where two
did. The corpus replay finds zero verdict-or-name mismatches.

The two new rows, re-derived here so the separation is a proposition
and not only a sweep. -/

def guardedWrong (d : Document) : Bool :=
  d.names.all (fun n => (d.out n).isEmpty)

#guard refChain.out "A" == ["B"]
#guard refChainTwo.out "A" == ["B"]
#guard refChainTwo.out "B" == ["C"]

#guard refChain.guardedMemo && !guardedWrong refChain
#guard refChainTwo.guardedMemo && !guardedWrong refChainTwo

theorem guardedWrong_still_not_the_decision :
    ¬ (∀ d : Document, guardedWrong d = true ↔ d.Guarded) := by
  intro h
  exact absurd ((h refChain).mpr refChain_guarded) (by decide)

/-! And the memo is the decision on the same witness, which is the
`#guard` above and not a `decide`: `settleAll` recurses
`termination_by`, so it does not reduce in the kernel — the same reason
every refusal call in `Ingest.lean` is a `#guard`. The kernel-checked
half is `guardedMemo_eq_guarded`, which is what makes the `#guard`'s
answer mean the absence of a cycle. -/

end PDD3.Attack2
