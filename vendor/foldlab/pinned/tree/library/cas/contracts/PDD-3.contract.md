# PDD-3 — References and recursion, slices 1–3

The contract packet for ticket PDD-3 (`.staging/wave-1/PDD-3.md`),
executing Lane A slices 1–3 of
`.staging/operational-structure/CORE-ABSTRACTIONS-PLAN.md` (:110-166)
and its theorem obligations (§3 addendum, :919-938).

Written under `.claude/skills/implement/CONTRACT.md`. Wave-1 flow
(operator-ruled): the builder writes the packet, the implementation
follows, an independent breaker comes afterward. The packet is
committed before any code under contract.

```
CATEGORIES inductive-data, specification-design, termination,
           abstraction-modules, algebraic-laws
BRANCH     agent/opus-cc-mac/pdd-3
```

CATALOG rows opened for those tags: §4.1–4.3 (exhaustive match,
destructors behind discriminators, structural recursion), §5.6/§6.x/§7.x
(prove by the function's own case split), §7.0 (round trips before
anything is built on a conversion), §3.1/§3.4/§11.2 (a remaining-work
measure, checked on every branch; write the explicit clause the moment
an edge fails the default), §8.0 (the spec form that composes), §9.1–9.5
(the abstraction function is the bridge; imports explicit and acyclic),
§1.6 (ghost values do not change executable results).

## Status — slices 1–3 LANDED, break pass in, fix pass done

| Slice | State |
|---|---|
| 1 — spelling probe | landed, 12 tests green |
| 2 — carrier | landed, two arms, round trip per constructor |
| 3 — document plane + guardedness | landed, `references_guarded_decidable` proved |

`lake --wfail build` green; `mise run --force check:cas` fully green
after regeneration through the emitters; the effects suite 47 files /
336 tests green. No `sorry`, no `native_decide`; the theorems use the
three standard Lean axioms and nothing else.

An independent breaker attacked the work on branch
`attack/opus-cc-mac/pdd-3` (`e8a31ba3`) and returned
**STANDS-with-holes plus one BREAK**: every law the packet writes
holds, and the DOOR's prose about itself did not. The attack record is
`library/cas/contracts/attacks/PDD-3/` on that branch —
`RESULTS.md` (verdict, gates verbatim, twelve failed attempts) and
`Attack.lean` (the witnesses, as derivations). Seven findings — one
BREAK, four holes, two notes — are carried in
[§Breaks](#breaks) with what each cost and what closed it.

The fix pass landed in four commits: `766d695f` (this packet),
`f8a2da76` (F2, N2 — prose), `599ef9eb` (F3 — the memoized walk),
`c6a70338` (F1, F4, F5 — the duplicate key, the missing witnesses, the
refusal order). The conformance corpus grew 71 → 76 cases.

Re-running the attack module against the fixed branch reddens EXACTLY
ONE guard: §7's `dupHarmlessLast`, which expected `unguardedCycle` and
now gets `illFormed`. That is F1's receipt. §2's three theorems still
elaborate, which is F2's honest receipt — the prose narrowed and the
semantics did not, because the semantics are an open ruling. §4's
`unsortedAndCyclic` did not change either, which is F5 closed the other
way round: TypeScript moved to Lean, not Lean to TypeScript.

Slices 4 and 5 are not in this ticket and are not started. What they
inherit is in [§Inherited by the follow-on](#inherited-by-the-follow-on-out-of-scope-here).

## The block that shaped it — RULED; slices 2 and 3 proceeded

The block below was raised against the plan's one-constructor carrier
and answered by the operator on 2026-08-30 (the ruling is at the head of
`.staging/wave-1/PDD-3.md`, and it amends the plan's :127-131):

> Slice 2 grows the universe by TWO constructors —
> `Ast.reference (name : String)` (the edge into the references table)
> and `Ast.susp (thunk : Ast)` (the guard), matching Effect's pinned
> two-node spelling. […] The §3-addendum theorem stands VERBATIM: every
> cycle passes through a `susp`. Neither constructor adds a sort.

So L2 is no longer a tautology and its falsifier is a real witness
table. The break ledger carries the finding.

## The carrier, as ruled

Two arms on `Ast`, and the two spellings the probe pinned:

| Arm | Projection | Role |
|---|---|---|
| `reference (name : String)` | `{"$ref":name,"_tag":"Reference"}` | the EDGE into the table |
| `susp (thunk : Ast)` | `{"_tag":"Suspend","checks":[],"thunk":…}` | the GUARD |

`WF` grows by exactly two clauses: `reference n` asks `n ≠ ""` (the
nonemptiness Effect itself imposes on `$ref`), `susp a` asks `a.WF`.
The ADDRESS discipline is deliberately not in `WF`.

Key order in the projection is canonical (sorted), which is what puts
`$ref` before `_tag`: `$` is 0x24 and `_` is 0x5F.

**The document plane.** A new `Document` — the Lean spelling of a shape
the projection already writes (`Ast.representationDocument`), so this
mints no carrier where a seat exists:

```
structure Document where
  references     : List (String × Ast)   -- strictly name-sorted
  representation : Ast
```

`Document.WF` is: names strictly ascending (the canonical-fields
argument, verbatim from `.struct` — it is what makes the spelling
unique), every name nonempty, every code `WF`, and **guarded**.

**Guardedness, made precise.** `Ast.bareRefs` collects the table names a
code mentions at positions **no `susp` guards** — the walk stops dead at
every `.susp`. That is the plan's own "non-suspend edge relation". The
table's edge relation is `n ⇝ m ⟺ m ∈ bareRefs (R n)`, and the document
is GUARDED when `⇝` has no cycle. Since `bareRefs` stops at each `susp`,
"no cycle in `⇝`" is exactly "every cycle of the references table passes
through a `susp`" — the theorem verbatim.

Checked against the probe's real documents: the anonymous linked list
has its only `reference` under the `susp`, so `⇝` has no edges at all —
guarded. The alias cycle `{A: reference B, B: reference A}` and the
bare structural cycle `{A: struct[next: reference A]}` both give cycles
in `⇝` — refused, and they are the L2 witness tables.

**The door.** `nonEmptyReferences` narrows rather than retires: `ingest`
keeps its type and its name as the BARE-CODE arm (every existing
theorem and `#guard` over it stands unchanged), and refuses a document
that carries a table with that name — now meaning "this arm answers a
bare code", not "the subset does not reach the table". The new
`ingestDocument` is the document door, and the taxonomy grows by one
arm, `unguardedCycle`, which is what the guardedness check answers with.
The emitted admission table describes the document door; the TypeScript
interpreter (`CanonicalSchema.admitDocument`) grows the same two node
forms and the same walk, because SM-19's agreement is held by that table
or it is not held at all.

## The claim scope — what v1 does NOT claim

Stated first, because the anti-overclaim class is the one this process
turns on (C5, CLAIM-GATES G0–G6).

- **GUARDEDNESS IS CONSTRUCTIBILITY, NOT PRODUCTIVITY.** Amended by the
  break pass (F2). The door decides that the EAGER revival of the table
  terminates: a cycle that closes through constructors alone — a
  `struct` field, a `union` member, an array element — is refused,
  because unfolding it builds an infinite code. It does NOT decide that
  forcing the result reaches a value. `Ast.susp` is a DELAY, not a
  constructor: putting the recursive occurrence under one defers the
  loop, it does not break it. Three admitted witnesses say so
  (`Attack.lean` §2, each proved `Guarded` through
  `references_guarded_decidable`, so this is a fact about the
  specification and not about the code):
  `{A: susp(reference A)}`, `{A: susp(union[reference A, null])}`, and
  `{A: susp(reference B), B: reference A}`. Measured against Effect's
  own validator, the first runs forever (killed at 60s) and the second
  throws `RangeError: Maximum call stack size exceeded`; the control —
  the guarded linked list this packet ships — decodes in 1ms. Deciding
  productivity needs a second relation over HEAD positions (what you
  reach through `susp` wrappers alone, before any constructor), and
  whether the estate wants it is a ruling. It is not claimed here, and
  the prose that used to claim it is narrowed.
- **No denotational adequacy for recursive codes.** `El` is not
  extended over the new constructor(s). A reference's target lives
  outside the code, in the references table, and extending a closed
  structural denotation to it needs either fuel-indexed semantics or a
  store-relative `El` — real theory, not commissioned here (plan HARD
  PARTS 2). `El`'s denotation is a fence on this ticket.
- **Cross-door agreement is bounded to ADMISSION.** For recursive
  schemas the two doors are claimed to agree on *admitted or refused*,
  and on nothing else. Value-plane verdict triples for recursive codes
  need a fuel-indexed Lean decode and are the named follow-on.
- **Nothing is claimed about the ADDRESS discipline.** The ruling's
  "reference name = target's content address (or annotated name)" is
  the door's and the materializer's question. It is deliberately not in
  `WF`, so no theorem here says a table key resolves in the store.
- **No soundness word attaches to host code** (estate C5). The
  TypeScript side is held by the byte gate and the battery, never by a
  theorem.
- **Live validation of recursive schemas stays Effect's.** Effect's
  `fromRepresentation` handles `Schema.suspend` natively; the estate
  gates differentially at admission and does not model it.
- **A DANGLING reference is not refused, and nothing says it resolves.**
  The door checks guardedness and nothing else about names: a `$ref`
  naming no table entry is admitted. Effect's own codec admits it too
  (slice 1 pinned that), and resolvability is the address discipline's
  question, which this ticket does not open. The door's guardedness
  answer is well defined regardless — a name with no entry has no
  outgoing edge, so it can lie on no cycle.
- **A DEAD table entry is not refused FOR BEING DEAD.** Corrected by the
  break pass (N1). The first spelling of this line said a dead entry is
  not refused, full stop, and that is false: `Document.guarded` runs
  `d.names.all`, over every name in the table rather than over the ones
  the root reaches, so a dead entry that CYCLES is refused
  `unguardedCycle` — `{A: reference "A"}` under a `String` root, which
  Effect reads back happily (`Attack.lean` §4, `deadCycle`). Both doors
  agree on it, so this is a claim-scope correction and not a
  divergence. What holds is the narrower sentence: being unreachable
  from the root is not itself a refusal, and the estate over-refuses
  relative to Effect on a dead cycle.
- **A DUPLICATE table key is REFUSED, and the ruling is assumed.** See
  [§The assumed ruling](#the-assumed-ruling-duplicate-table-keys-operator-override-invited).

### Inherited by the follow-on (out of scope here)

- **Slice 5's recursive byte-gate fixture meets SM-21.** Effect writes
  an `annotations` bag on a NAMED table entry (`{"identifier":"Node"}`,
  pinned in slice 1). The Lean spelling carries no bag and the decoder
  is exact on keys, so a named recursive fixture is unadmittable until
  SM-21 lands or the door strips the bag. Slice 5 is not in this ticket;
  the finding is recorded so the follow-on inherits it rather than
  rediscovering it. The ANONYMOUS linked list carries no bag and is
  unaffected.
- **Value-plane verdicts for recursive codes** need a fuel-indexed Lean
  decode — the named follow-on, per the addendum.
- **Slice 4 owes the faithful `Suspend` lowering.** The materialization
  emitter lowers `.susp` to its thunk, because the TypeScript fragment
  has no arrow and grows only with a real consumer. `Schema.suspend(() =>
  …)` printed verbatim, and the arrow it needs, are owed there. No
  registered fixture reaches the arm today, so no emitted byte depends
  on it.
- **The guardedness ruling has no registry row.** `references_guarded_
  decidable` deliberately carries no `LAW SM-<n>:` line: minting a row in
  `tools/Laws.lean` is an operator act, and a theorem claiming an id that
  belongs to another ruling is the status lie the law index exists to
  catch. OWED: the row.
- **The node-level duplicate key** — a duplicate `_tag` on a node, which
  Lean refuses `notASchema` and the in-memory TypeScript door admits.
  It predates this ticket and this pass deliberately did not widen to
  it. OWED: one "the bytes are not a canonical spelling" refusal, named,
  on both hosts, covering every duplicate key rather than the references
  table's alone (break-pass F1's provenance paragraph).
- **The productivity relation.** Deciding that forcing a document
  reaches a value, not merely that revival terminates, needs a second
  relation over HEAD positions — what a name reaches through `susp`
  wrappers alone, before any constructor. `Attack.lean` §2's `headName`
  is the sketch. Whether the estate wants it is a ruling (break-pass
  F2).
- **`ingestDocumentBytes`.** `ingestBytes` composes the parser with the
  BARE-CODE arm, so every document arriving as bytes is refused
  `nonEmptyReferences`. The TypeScript side has the composition and Lean
  does not, and that asymmetry is where the duplicate-key divergence
  lived. `Attack.lean` §7 writes the missing arm out in three lines
  (break-pass N5).

### The one divergence C6 does not close

Both doors refuse an EMPTY reference name; they NAME it differently.
Lean reads the shape and its gate answers `illFormed`; Effect's own
decoder refuses the spelling outright (`$ref` is `NonEmptyString`), so
the TypeScript door answers `notASchema` before the admission table is
consulted.

It is recorded, not closed, and neither repair is a builder's to make:
refusing the empty name in Lean's DECODER would falsify
`ofRepresentationJson_toRepresentationJson`, which holds unconditionally
over every code, and making the name nonempty BY CONSTRUCTION would
change `Ast.reference`'s ruled signature. The conformance corpus
therefore carries no row for this spelling and says so at the point of
omission; the divergence sits in `Cas/Backend/Admission.lean` beside the
annotation-bag one. Everything else about C6 agrees case for case.

### The assumed ruling — duplicate table keys (OPERATOR OVERRIDE INVITED)

The break pass's one BREAK (F1) is a byte string the two doors read as
two different documents. `{"A":<a reference to A>,"A":<a String>}` is a
references table carrying the name `A` twice. Lean's `Cas.Json.parse`
keeps both pairs and `Document.lookup` takes the FIRST, so the table
cycles; `JSON.parse` keeps the LAST, so it does not. One payload, two
documents, opposite verdicts — and the split runs both ways, because
`{"A":<a String>,"A":<a reference to A>}` reverses which door sees the
cycle.

**The fix pass ASSUMES this ruling: a duplicate table key is refused, at
both doors, by name, before anything is decided about the table's
content.** The reasoning: which pair wins is a parser's private habit,
not a fact about the document, so a door that picks a winner is
answering a question the bytes do not ask. Refusing costs nothing real —
no canonical spelling has a duplicate key, because a canonical spelling
sorts strictly ascending — and it is the only answer both hosts can give
without one of them guessing.

What that costs in mechanism, on each side:

- Lean asks it BEFORE the decoder, at the head of `ingestDocument`, of
  the canonicalized value: `duplicateReferenceKey` answers `illFormed`
  and nothing else runs. It used to fall through to `documentRefusal`,
  which tests guardedness first, so the same duplicate earned
  `unguardedCycle` in one direction and `illFormed` in the other. No
  document changes from admitted to refused — `pairwiseRefNames` already
  refused every duplicate — only the NAME moves, and it stops depending
  on what else is wrong with the document.
- TypeScript refuses it from the BYTES, because `JSON.parse` has already
  thrown one of the pairs away by the time any gate could look. The
  shipped byte door already turned these payloads away (the canonical
  re-render does not match the bytes), but ANONYMOUSLY — as
  `TypeError: Projection payload is not canonical JSON`, which the
  verdict gate reads as "refused without a name". It now answers
  `illFormed` with the repeated name in the message.

The alternative the operator may prefer: record the split as a third
divergence in `Cas/Backend/Admission.lean` beside the empty-name and
annotation-bag ones, and carry no corpus row. That is a smaller change
and a larger lie — the table's "agree case for case" line would have to
go, and a foreign payload would still get two answers. Overriding this
is deleting one `if` at the head of `ingestDocument`, two calls to
`CanonicalSchema.admitPayloadSpelling`, the `duplicateReferenceKey`
clause row, and two corpus rows.

**Owed, not fixed, and deliberately so.** The duplicate-key hazard is
older than this ticket. Its control is a duplicate `_tag` on a NODE with
an empty table — `{"_tag":"String","_tag":"Null","checks":[]}` — which
splits the same way and has nothing to do with the references table:
Lean answers `notASchema`, and the in-memory TypeScript door admits.
What PDD-3 changed is the REACH, because at the parent commit a
non-empty table was refused `nonEmptyReferences` by both doors and a
duplicate table key could not diverge. The node-level twin is an OWED
EDGE for a follow-on — a general "the bytes are not a canonical
spelling" refusal, named, on both hosts — and this pass deliberately did
not widen to it: the table gate refuses duplicates in the references
table and nowhere else, so no refusal name is claimed for a spelling the
two doors have not been reconciled on.

## The algebra

Write `R` for a references table — a finite map from name to code —
and `D = (R, r)` for a document: the table and the root code. Write
`refs(a)` for the multiset of table names a code mentions.

**L1 — the table induces a finite edge relation.** `E ⊆ dom(R) × dom(R)`
with `n E m ⟺ m ∈ refs(R n)`. `E` is finite because `dom(R)` is finite
and `refs` is a fold over a finite tree.

**L2 — guardedness is decidable.** The predicate "every cycle of `E`
passes through a guard" is decided by a search with fuel `|dom(R)|`.
Decidability is the theorem; the decision procedure IS the door.

**L2a — the search settles each name once.** Added by the fix pass (F3).
The walk carries the set of names already known to settle and consults
it before descending, so a name is explored once however many paths
reach it. The variant is `|dom(R)| - |visited|` — the `termination`
class, estate form fuel — and it is now a fact about the code rather
than a description of it. The naive walk, which the packet shipped, has
no visited set at all: a table whose entries each name the next one
twice makes it re-walk every path, and it is `Θ(2ⁿ)`. Measured:
`Attack.lean` §5's `fanTable`, 25 acyclic entries in a 7 657-byte
payload, 302 915 ms in Lean and 18 271 ms in TypeScript at 23 entries,
doubling per entry. This is the ingestion door for foreign content, so
the input is attacker-chosen and the door is synchronous on both hosts.
The memoized walk decides the SAME predicate, so
`references_guarded_decidable` is untouched over `Document.settles` and
`references_guarded_decidable_memo` is the same statement over
`Document.guardedMemo`, the procedure the door actually runs;
`Document.guardedMemo_eq_guarded` is the whole of the difference.

**L3 — the round trip extends per constructor.** For every new code `a`,
`ofRepresentationJson (toRepresentationJson a) = some a` on the
`RepNormal` image, and `SelfCodec` and `RepNormal` each grow by exactly
one case per constructor (SM.md:169-174 names the ripple list). This is
CATALOG §7.0's rule applied: the round trip is proved before anything
is built on the conversion.

**L4 — the door is total and every refusal is named.** `ingest` answers
either a document or one member of the refusal taxonomy. Growing the
carrier must not silently widen what is admitted: every spelling that
was refused before and is still not a code is refused with the same
name.

**L5 — the projection stays injective.** Two distinct well-formed
documents have distinct canonical bytes, up to the one literal-null
collapse of register R13. A second spelling for an existing shape would
break `toRepresentationJson_inj` as stated (the argument the tuple code
already carries, Ast.lean:141-148).

```
REQUIRES   A revision-1 schema-node envelope
           {revision, value:{references, representation}} whose bytes
           are a canonical rendering. The references table may be
           non-empty — which is exactly what this ticket changes; today
           a non-empty table is refused `nonEmptyReferences`
           (Ingest.lean:93-97).

ENSURES    ingest answers a well-formed DOCUMENT (table + root) whose
           guardedness check passed, or one named refusal. old = the
           envelope as presented; the door is pure, so there is no
           second state beyond its answer.

DECREASES  |dom(R)| - |visited| for the guardedness search: the walk
           carries the settled names and never descends into one twice,
           so every recursive edge either meets the memo and stops or
           adds a name (fuel = table size bounds the depth,
           existential-fuel discipline,
           Cas/Lang/Handler.lean:115-123). AMENDED by the fix pass —
           the shipped procedure had no visited set and the clause
           described an algorithm that did not exist (F3). Structural
           inclusion for every walk over a single code (CATALOG §4.3 —
           recursion on structurally included children, so the decrease
           is free).

FRAME      reads: the presented envelope only. writes: nothing — the
           door is a pure function. On the generated side, the byte
           footprint is src/cas/generated/SchemaAdmission.ts and the
           schema/verdict/address fixtures the emitters own; no
           generated file is hand-edited.

FALSIFIER  per law, below.
```

## Falsifiers

```
LAW        L1 — refs is a finite fold.
FALSIFIER  exhibit a well-formed code whose refs computation does not
           terminate, or a table whose edge set is not a subset of
           dom(R) x dom(R).
BATTERY    Lean: the decidability instance elaborates, or it does not.

LAW        L2 — guardedness is decided at the door:
           `Document.guarded d = true  <->  d.Guarded`
           (`references_guarded_decidable`), where `Guarded` is the
           honest no-cycle Prop over the non-suspend edge relation and
           `guarded` is the fuel-bounded search with fuel = table size.
FALSIFIER  exhibit an UNGUARDED cyclic table the door ADMITS, or a
           GUARDED cyclic table the door REFUSES.
BATTERY    DISCHARGED. Lean: `unguarded_alias_cycle_refused` and
           `unguarded_struct_cycle_refused` (their cycles EXHIBITED as
           `ReachPlus` derivations, not decided by the procedure under
           test), and `guarded_list_admitted` — the partner without
           which refusing every table would pass. The door's answers are
           `#guard`s beside them. Host side: the conformance corpus rows
           `refuse-unguarded-alias-cycle`,
           `refuse-unguarded-struct-cycle`, `admit-guarded-recursion`
           and `admit-references-table`, replayed by
           test/SchemaVerdicts.test.ts against the regenerated
           SchemaAdmission table — the cross-door gate.

           GREW in the fix pass, because all four of those rows have an
           EMPTY bare-edge relation and a door with fuel ZERO passed
           every one of them (F4, `Attack.lean` §3 `guardedWrong`):
           `admit-reference-chain` (`{A: reference B, B: String}`, one
           acyclic edge) and `admit-reference-chain-two` (two edges, so
           the search recurses more than once). Both admitted, both with
           a non-empty relation, so the fuel is exercised by a witness
           and not only by the theorem.

LAW        L2a — the memoized walk decides what the naive one decides:
           `Document.guardedMemo d = Document.guarded d`, hence
           `Document.guardedMemo d = true <-> d.Guarded`
           (`references_guarded_decidable_memo`).
FALSIFIER  exhibit a document the two procedures answer differently.
BATTERY    Lean: `references_guarded_decidable_memo` and
           `Document.guardedMemo_eq_guarded`, carried by
           `settleAll_grows`, `settleAll_settling` and
           `settleAll_isSome`; plus `#guard`s in Guarded.lean that the
           fan table admits at 30 entries — past where the naive walk
           can go — and that the two procedures agree at 8, where it
           can. Host side:
           library/effects/test/SchemaGuardednessCost.test.ts asserts
           the fan table at 40 entries returns inside a wall-clock
           budget, and that the same shape with its tail wired back to
           the head is still refused `unguardedCycle` — the partner
           that would catch a memo recording a name on the way IN
           rather than on the way out. A RUNTIME assertion on the host;
           nothing is timed in the kernel.

LAW        L3 — round trip per constructor.
FALSIFIER  exhibit a well-formed code `a` in the new constructor's
           family with
           ofRepresentationJson (toRepresentationJson a) != some a.
BATTERY    Lean `#guard` beside the existing per-increment worked
           calls (Ingest.lean:387-565 is the pattern); host side, the
           schemas byte gate in `mise run check:cas`.

LAW        L4 — refusals do not silently widen.
FALSIFIER  exhibit a spelling refused before this increment and
           admitted after, or refused after under a different name.
BATTERY    the clause table's `#guard`s (Cas/Backend/Admission.lean:
           385-469) plus the admission-map byte gate.

LAW        L6 — the two doors name a refusal in the same ORDER. A
           document with two defects earns the same name at both doors.
FALSIFIER  exhibit a document both doors refuse under different names.
BATTERY    added by the fix pass (F5). Corpus row
           `refuse-unguarded-and-illformed` — a table entry that is
           both on a bare cycle and out of field order — which Lean
           names `unguardedCycle` and the shipped TypeScript door named
           `illFormed`, because it ran `admitNode` over the entries
           before the guardedness filter. The reference handler's order
           is the order (R10): the TypeScript walk now filters
           guardedness first. Replayed by the "refused BY NAME" gate in
           test/SchemaVerdicts.test.ts.

LAW        L7 — a duplicate table key is refused, at both doors, by one
           name. ASSUMED RULING — see §The assumed ruling.
FALSIFIER  exhibit a byte string with a repeated references-table key
           that either door admits, or that the two doors name
           differently.
BATTERY    added by the fix pass (F1). Corpus rows
           `refuse-duplicate-reference-key` (the reference first, so
           Lean's first-pair lookup sees the cycle) and
           `refuse-duplicate-reference-key-last` (the reference last,
           so it does not) — both `illFormed`, both directions, gated
           for verdict AND for name.

LAW        L5 — the projection stays injective.
FALSIFIER  exhibit two distinct well-formed documents with equal
           canonical bytes.
BATTERY    Lean: `toRepresentationJson_inj` extended; host side, the
           addresses fixture in check:cas.
```

## Obligation classes that apply

`domain` (the table lookup is partial — a dangling name is a side
condition, and the probe shows Effect does not check it), `contract`,
`adequacy` (L2 is precisely where a too-weak `Q` lets a vacuous check
pass — see the Block), `invariant` (`WF` preserved on every exit path),
`termination` (the fuel variant), `abstraction` (the document is the new
abstraction boundary; every public contract states over it),
`conformance` (the byte gates), `claim-scope` (above).

Not applicable, generating nothing: `frame` beyond "the door is pure".

## Slice 1 — the spelling probe (LANDED)

Pinned from the estate's own runtime dependency, `effect@4.0.0-rc.112`
(`library/effects/package.json`; provenance row `effect-runtime`,
commit `2600f62f4532026928454dcea8d1c48557b3f942`,
`.reference/provenance/sources.lock.json`), file
`node_modules/effect/src/SchemaRepresentation.ts`. The probe executes
the library rather than reading it, so the pins are observations, not
transcriptions.

Battery: `library/effects/test/SchemaReferencesPin.test.ts` — 12 tests,
green.

The pinned spellings:

| What | Spelling |
|---|---|
| `Reference` | `{"_tag":"Reference","$ref":<non-empty string>}` — **exactly two keys**. No `checks`. No `annotations`. (`:1066-1069`, `:171-174`) |
| `Suspend` | `{"_tag":"Suspend","checks":[],"thunk":<Representation>}`, plus an optional `annotations` bag. `checks` is `Schema.Tuple([])` — the EMPTY tuple, so a `Suspend` can never carry a check. (`:984-989`, `:158-163`) |
| `Document` | `{"representation":<Representation>,"references":<References>}` (`:480-483`, `:1098-1103`) |
| `MultiDocument` | `{"representations":[<Representation>,...],"references":<References>}` (`:491-494`, `:1105-1110`) |
| `References` | `Schema.Record(Schema.String, Representation)` — a plain object, keys are arbitrary strings (`:470-472`, `:1096`) |
| key nonemptiness | `$ref` is `Schema.NonEmptyString`; the table KEY type is plain `Schema.String`. An empty `$ref` is rejected by Effect itself. |

What Effect's own codec does NOT check — all four ACCEPTED by
`fromJson`, so each is the estate door's job:

- a dangling `$ref` (a name with no table entry);
- a self alias `{A: Reference A}`;
- an alias cycle `{A: Reference B, B: Reference A}`;
- an unguarded structural cycle (a `Reference` back to `A` under a
  property signature, with no `Suspend` on the path);
- a dead table entry that nothing references.

Two further observations that bear on scope:

- **A non-empty references table does not imply recursion.** A shared
  NON-recursive named schema (an `identifier` annotation, used twice)
  allocates a table entry. So "the table is non-empty" and "the schema
  is recursive" are different questions.
- **A named table entry carries an `annotations` bag in practice**
  (`{"identifier":"Node"}`). That is the divergence already recorded at
  Cas/Backend/Admission.lean:52-62 and owned by Lane B1 (SM-21), not by
  this ticket — but a recursive fixture will meet it, so slice 5's
  byte-gate fixture depends on B1 or on stripping the bag at the door.

## Block — RAISED 2026-08-30, RULED the same day

Kept in full, because a spec bug caught before any implementation
existed is the record this process is measured by. The ruling is quoted
in [§Status](#status--the-block-is-ruled-slices-2-and-3-proceed) and the
ledger entry is in [§Breaks](#breaks).

**The plan's slice-2 carrier contradicts the pinned spellings, and the
contradiction is not cosmetic: under the carrier as written, this
packet's L2 is a tautology and its falsifier cannot be built.**

The plan specifies ONE constructor, `Ast.susp (name : String)`, "the
name is a references-table key", and the §3 addendum states the theorem
as "every cycle passes through a `susp`" (equivalently, "the
non-suspend edge relation is acyclic").

The probe shows Effect spells these as TWO different nodes:

- `Reference` carries the **name** (`$ref`) and is the table EDGE;
- `Suspend` carries an inline **code** (`thunk`) and is the GUARD.

A recursive schema's rev-1 JSON contains both. The probe's
linked-list document is
`{"representation":{"_tag":"Reference","$ref":"Objects_"},
"references":{"Objects_":{...,"next":{"_tag":"Suspend","checks":[],
"thunk":{...{"_tag":"Reference","$ref":"Objects_"}...}}}}}`.

Three consequences, in order of severity:

1. **L2 becomes vacuous.** If `susp name` is the only node that names a
   table entry, then every edge of `E` is a susp edge, so "every cycle
   passes through a susp" holds for every table. The check decides
   nothing and the door refuses nothing.
2. **The ticket's own falsifier is unconstructible.** The ticket asks
   for "an unguarded cycle the door must refuse (the witness table, as
   a counter-`example`/test)". Under a one-constructor carrier no such
   witness exists — which, by CONTRACT.md's `adequacy` class, means the
   specification is the bug, not the implementation.
3. **The carrier cannot decode what Effect emits.** `Reference` has two
   keys and `Suspend` has three, one of them a nested representation.
   `Ast.ofRepresentationJson` (SelfCodec.lean:1351-1385) matches EXACT
   object literals, key order and all — one arm per node family, each
   answering with one code. One constructor is one projection shape,
   hence one arm, so the other family has no spelling at all and slice
   3's "references table decoded and emitted through the envelope"
   would not decode a real recursive document.

The estate's own code already treats these as TWO missing
constructors, in both places that name the gap:

- `Ast.ofRepresentationDocument` — "revision 1's `references` is
  unreachable from the Lean side today (**no `Suspend`, no `Reference`
  constructor**)" (SelfCodec.lean:1444-1452);
- `IngestRefusal.nonEmptyReferences` — the same sentence, verbatim
  (Ingest.lean:93-97).

So the one-constructor collapse is drift introduced by the plan's
slice-2 line, not the estate's reading of the source.

The existing `Ast.ref (tag : UInt8)` is **not** a candidate for either
role: it is registry row zero `foldlab/cas/ref`, a `Declaration`,
unrelated to the references table (Ast.lean:74-86).

### The single question — ANSWERED: two constructors

> Does slice 2 add ONE constructor or TWO — that is, does
> `Ast.susp (name : String)` spell Effect's `Reference` (`$ref`), with
> the §3 addendum theorem restated as a POSITIONAL guardedness check
> (a cycle is unguarded when it closes through root/transparent
> positions only; guarded when it passes under a structural
> constructor) — or does the carrier grow BOTH
> `Ast.reference (name : String)` and `Ast.susp (thunk : Ast)`,
> matching Effect's pinned two-node spelling, so that "every cycle
> passes through a `susp`" stands verbatim and its falsifier is a real
> witness table?

Either answer is buildable and neither adds a sort (decision 2 is
satisfied both ways — kinds grow by arms). The estate cannot pick it
from inside the implementation without patching the spec, which is the
defect this process exists to kill (IMPLEMENTER.md step 4).

The two answers differ in what v1 can carry: the one-constructor answer
cannot spell a `Suspend` node at all, so the linked-list fixture of
slice 5 is unadmittable and the "recursive byte-gate fixture" would
have to be hand-shaped rather than taken from Effect. The
two-constructor answer admits what Effect actually writes.

## Breaks

```
BROKE      no implementation — the SPEC. The plan's slice-2 line,
           CORE-ABSTRACTIONS-PLAN.md:127-131 ("Carrier:
           `Ast.susp (name : String)` (one constructor; the name is a
           references-table key)"), carried into the ticket verbatim.
LAW        L2 — guardedness is decided at the door: the admission
           check decides "every cycle passes through a `susp`"
           (§3 addendum, CORE-ABSTRACTIONS-PLAN.md:919-926).
WITNESS    No witness exists, and THAT is the refutation. Under one
           constructor every table edge is a `susp` edge, so
           "every cycle passes through a `susp`" holds for every
           table: the law is a tautology, the door refuses nothing,
           and the ticket's own named falsifier — "an unguarded cycle
           the door must refuse" — has no solution to exhibit.
           The positive evidence is the pinned rev-1 document for the
           anonymous linked list, which carries BOTH node families:
           {"representation":{"_tag":"Reference","$ref":"Objects_"},
            "references":{"Objects_":{…"next":{"_tag":"Suspend",
            "checks":[],"thunk":{…{"_tag":"Reference",
            "$ref":"Objects_"}…}}}}}
           A one-constructor carrier has no spelling for one of them.
CLASS      adequacy — "is `Q` strong enough that no wrong
           implementation passes?" It was not: every implementation
           passed, including one that refuses nothing.
FIXED-BY   SPEC-BUG. Operator ruling 2026-08-30 amended the spec:
           two constructors, `Ast.reference (name : String)` and
           `Ast.susp (thunk : Ast)`; the §3-addendum theorem stands
           verbatim and its falsifier becomes a real witness table.
           Recorded at the head of `.staging/wave-1/PDD-3.md`.
```

The finding cost no implementation work: the probe ran first, as the
ticket ordered, and the adequacy class fired on the packet before a
line of Lean existed.

### The break pass — verdict STANDS-with-holes, one BREAK

Seven rows, one per finding, from the independent attack on
`attack/opus-cc-mac/pdd-3` (`e8a31ba3`). Every row cites the attack
module that carries its witness, per CONTRACT.md's ledger rule; the
attack is a regression object, so re-running
`lake env lean contracts/attacks/PDD-3/Attack.lean` after this pass is
the mechanical proof of what closed and what did not.

What the pass did NOT find is worth as much: twelve attacks failed —
the edge relation misses no nesting (checked per constructor field,
including all three `tuple` positions), the two walks agree on every
admitted node shape, key order is exact on both new arms, `repNorm` is
idempotent on suspends nested in suspends inside a union, a dangling
reference does not break the decision, and there is no `sorry` or
`native_decide` anywhere on the C6 path.

```
BROKE      f486689f — the document plane, both doors
LAW        L7 / the packet's cross-door claim, "Cross-door agreement is
           bounded to ADMISSION", and Cas/Backend/Admission.lean:64-67,
           "Nothing else about C6 diverges … agree case for case".
WITNESS    one byte string, two documents:
           {"revision":1,"value":{"references":{
              "A":{"$ref":"A","_tag":"Reference"},
              "A":{"_tag":"String","checks":[]}},
             "representation":{"_tag":"String","checks":[]}}}
           Lean keeps both pairs and looks up the FIRST, so the table
           cycles and the door answers unguardedCycle. JSON.parse keeps
           the LAST, so the in-memory TypeScript door ADMITS. The
           reversed spelling reverses which door sees the cycle. On the
           shipped BYTE door the payload was refused — but anonymously,
           as "Projection payload is not canonical JSON", which the
           verdict gate reads as refused without a name.
CLASS      conformance, claim-scope
FIXED-BY   c6a70338, under the ASSUMED RULING recorded in §The assumed
           ruling — refused at both doors, named illFormed, before
           either door decides anything about the table.
           Lean: `duplicateReferenceKey` at the head of
           `ingestDocument`, on the canonicalized value. TypeScript:
           `admitPayloadSpelling`, a references-table duplicate scan
           over the BYTES, called from `Materialize.fromPayload` and
           from `CanonicalSchema.get`. The clause is
           `duplicateReferenceKey`/`illFormed` in the admission table,
           so the name is Lean's. Corpus rows
           refuse-duplicate-reference-key and
           refuse-duplicate-reference-key-last carry both directions.
           RECEIPT: re-running the attack module against this branch
           reddens exactly one guard — §7's `dupHarmlessLast`, which
           expected `unguardedCycle` and now gets `illFormed`.
           OWED, out of scope by instruction: the node-level twin (a
           duplicate `_tag` on a node), which predates this ticket.
ATTACK     Attack.lean §7 — dupHarmlessLast, dupTagNode.

BROKE      f486689f — Guarded.lean:21-26 and Ingest.lean:105-116, the
           PROSE; no theorem moved.
LAW        the door's stated reason for existing: "resolving an
           unguarded cycle never terminates" and "the resolver unfolds
           A to get A, so the table is refused".
WITNESS    three documents whose resolver unfolds A to get A forever,
           ADMITTED by both doors and proved Guarded as a Prop:
           {A: susp(reference A)}                        (runs forever)
           {A: susp(union[reference A, null])}           (stack overflow)
           {A: susp(reference B), B: reference A}        (one remove)
           The control — this packet's own guardedList — decodes in 1ms
           on the same path, so the door is right about what Effect
           emits and wrong about why.
CLASS      adequacy, claim-scope. The same class as the Break above,
           one level up: the ruled theorem is the too-weak Q for the
           prose's claim.
FIXED-BY   f8a2da76, PROSE ONLY — no admission semantics moved, because
           whether the estate decides productivity is an operator
           ruling and it is open. Guarded.lean, the unguardedCycle
           docstring and the packet's claim scope now say what is
           decided: a constructible cycle is refused; a susp-guarded
           self-reference is admitted, and forcing it may diverge,
           because susp is a delay and not a constructor.
           RECEIPT, and it is the honest one: §2's three theorems STILL
           ELABORATE and its three admits guards still pass, because
           nothing about admission moved. This row closes when the
           ruling lands, not before.
ATTACK     Attack.lean §2 — suspBareSelf_guarded, suspUnionKnot_guarded,
           suspIndirect_guarded, and headName, which names the
           distinction the relation does not draw.

BROKE      f486689f — Document.settles, both hosts
LAW        DECREASES: "|dom(R)| - |visited| for the guardedness search".
WITNESS    there is no visited set on either side of the wire. The
           variant is the fuel, structurally, and the search re-walks
           every path: fanTable n, whose n+1 entries each name the next
           one twice, is ACYCLIC and ADMITTED after a Θ(2ⁿ) walk.
           25 entries, a 7 657-byte payload, 302 915 ms in Lean;
           TypeScript 18 271 ms at 23. Doubling per entry, on the
           ingestion door for foreign content, synchronous on both
           hosts.
CLASS      termination (the variant named an algorithm that did not
           exist), claim-scope
FIXED-BY   599ef9eb — the memoized walk on both hosts.
           `Document.settleAll` threads the settled names and consults
           them before descending; `guardedMemo_eq_guarded` proves it
           agrees with the naive walk, so
           references_guarded_decidable stands VERBATIM and
           references_guarded_decidable_memo is the same statement over
           the procedure the door runs.
           library/effects/test/SchemaGuardednessCost.test.ts is the
           host-side runtime assertion at a size the naive walk cannot
           reach.
           RECEIPT: Guarded.lean's `#guard (fanOutTable 30).guardedMemo`
           elaborates in milliseconds where the naive walk at 25 took
           302 915 ms; the host assertion at 40 entries returns inside
           a 1s budget.
ATTACK     Attack.lean §5 — fanEntry, fanTable.

BROKE      f486689f — the BATTERY, not the door
LAW        Guarded.lean:46-48, "fuel = |table| is precisely enough to
           force a repeat and no more".
WITNESS    guardedWrong, a door with fuel ZERO —
           `d.names.all (fun n => (d.out n).isEmpty)` — agrees with the
           shipped door on all four C6 corpus rows, on every other
           witness in the attack, and on all 67 empty-table rows: 71 of
           71. Both admitted C6 rows have an EMPTY bare-edge relation.
           The spec is adequate and the battery was not: the theorem
           was the only thing standing between the shipped door and a
           door that never follows an edge.
CLASS      adequacy
FIXED-BY   c6a70338 — corpus rows admit-reference-chain
           ({A: reference B, B: String}) and admit-reference-chain-two
           (two edges), plus `refChain`/`refChainTwo` and their
           `Guarded` proofs in Ingest.lean. Both are admitted by the
           real door and refused by the fuel-zero one, so the corpus
           now separates them: 76 rows, and the fuel-zero door fails 2.
           RECEIPT, stated because it is not what RESULTS.md predicted:
           §3's own agreement `#guard`s still PASS, because they name
           the four original rows rather than reading the corpus. The
           battery closed; the attack module's hardcoded four did not
           move. A follow-on breaker should read the corpus.
ATTACK     Attack.lean §3 — guardedWrong,
           guardedWrong_is_not_the_decision, chain1, chain2.

BROKE      f486689f — the refusal NAMES, across the doors
LAW        L4/L6 — a refused code is refused by name, and by the same
           name (test/SchemaVerdicts.test.ts).
WITNESS    a table entry both on a bare cycle and out of field order —
           {A: struct[b: reference A, a: String]}, root reference A.
           Lean answers unguardedCycle, because documentRefusal tests
           guardedness first; the TypeScript door answered illFormed,
           because it ran admitNode over every entry before its
           guardedness filter. Same bytes, both doors refuse, different
           names, and no corpus row asked.
CLASS      conformance
FIXED-BY   c6a70338 — the reference handler's order IS the order (R10),
           so `admitDocument` holds a discipline's refusal, runs the
           guardedness filter, and replays the held one after. Which
           stage a refusal belongs to is read off its NAME in the
           admission table — notASchema and unknownDeclaration are the
           decoder's and win at once, illFormed is a discipline's and
           waits — so the door still refuses an undecodable entry
           before it names a cycle, which is what Lean does. Corpus row
           refuse-unguarded-and-illformed carries it, and the order is
           written down in Cas/Backend/Admission.lean.
           RECEIPT: §4's `unsortedAndCyclic` guard did NOT change
           answer, and that is the correct outcome — RESULTS.md
           predicted it would, on the assumption the repair might move
           Lean. It did not: TypeScript moved to Lean.
ATTACK     Attack.lean §4 — unsortedAndCyclic, unsortedOnly.

BROKE      92a64ec4 — the packet's claim scope, line "A DEAD table
           entry is not refused".
LAW        the claim-scope class: the stated boundary of a claim equals
           its actual coverage.
WITNESS    {A: reference "A"} under a String root. A is unreachable
           from the root and both doors refuse it unguardedCycle,
           because Document.guarded runs d.names.all over every name
           rather than the reachable ones.
CLASS      claim-scope
FIXED-BY   766d695f — the line now reads "not refused FOR BEING DEAD",
           and the over-refusal relative to Effect is stated where the
           dangling-reference line is.
ATTACK     Attack.lean §4 — deadCycle.

BROKE      326064e3 — stale prose, SelfCodec.lean:1502-1505
LAW        none. A sentence that says the carrier has no Suspend and no
           Reference constructor, in the commit that added both.
WITNESS    the docstring on Ast.ofRepresentationDocument still carried
           the pre-C6 sentence. Its IDENTICAL twin on
           IngestRefusal.nonEmptyReferences was narrowed in the same
           commit, and the packet's own Block quotes the two as a pair.
CLASS      claim-scope
FIXED-BY   f8a2da76 — narrowed like its twin: the arm answers ONE CODE,
           so it reads an empty table and refuses a non-empty one for
           that reason, not for want of a constructor.
ATTACK     RESULTS.md N2.
```

Three notes from the pass are recorded and NOT closed here, because
none is this ticket's to close: `El.lean` is in the diff under a fence
(N3 — two forced `Empty` arms and a docstring; adding a constructor
makes the match non-exhaustive, and no existing arm moved), the effects
suite's `BrainStem.test.ts` times out on a cold full-suite run at the
default 5s and passes alone in 199ms (N4 — known baseline, unrelated to
the schema plane), and `ingestBytes` still composes the parser with the
BARE-CODE arm so every document arriving as bytes is refused
`nonEmptyReferences` (N5 — there is no `ingestDocumentBytes`; the
TypeScript side has the composition, and that gap is where the
duplicate-key divergence lived). N6 — that `Document.WF`'s strict-order
clause is unreachable at the door except through duplicates — stands,
and is now unreachable outright: the spelling gate turns a duplicate
away before the decoder runs, so nothing reaches the clause. It earns
its place on the ENCODE side, where
`Document.representationDocument_canonical` needs it, and that is where
its docstring already says it lives.
