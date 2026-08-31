# PDD-3 — break pass, results

```
SUBJECT     branch agent/opus-cc-mac/pdd-3, tip 92a64ec4 (packet close)
            work in 4c39bf4e (packet amend) / 326064e3 (slice 2, the
            carrier) / f486689f (slice 3, the document plane)
PACKET      library/cas/contracts/PDD-3.contract.md
TICKET      .staging/wave-1/PDD-3.md (ruled 2026-08-30: two constructors)
BREAKER     independent; did not build this work
ATTACK      ./Attack.lean — OUTSIDE every lake target (lakefile roots are
            `Cas`, `Cas.Backend.+`, `examples`, `tools`; `contracts/` is
            under none), so nothing here reaches `lake build` and no
            ledger byte moves.  Run: from library/cas,
            `lake env lean contracts/attacks/PDD-3/Attack.lean`
            — silence is a pass.
```

## VERDICT — STANDS-with-holes

Every stated law holds.  `references_guarded_decidable` is sound AND
complete, proved from an inductively-stated `ReachPlus` rather than from
the procedure restated, with a hand-proved pigeonhole and no Mathlib; the
two witness cycles are EXHIBITED as derivations, not decided; the partner
falsifier exists; the axiom census is the standard three everywhere; the
commit order is packet-first; every gate is green.  I could not falsify
a single equation the packet writes.

What does not stand is the DOOR'S BEHAVIOURAL claims about itself.  The
theorem decides exactly what it says it decides, and the prose around it
says it decides something stronger.  One finding meets the BREAK bar (a
references-table spelling one door refuses and the other ADMITS);
its cause is inherited rather than introduced, and that is stated at the
finding.  Four holes and six notes follow.

| # | Grade | One line |
|---|---|---|
| F1 | BREAK | A references table one door refuses and the other admits |
| F2 | HOLE | `Guarded` decides constructibility, not productivity — two admitted documents whose validator never returns |
| F3 | HOLE | The door is `Θ(2ⁿ)` in the table size: 25 acyclic entries = 303s |
| F4 | HOLE | No witness anywhere distinguishes fuel `\|table\|` from fuel `0` |
| F5 | HOLE | Refusal NAMES diverge across the doors on an unguarded-and-ill-formed table |
| N1–N6 | NOTE | claim-scope imprecision, stale prose, a fence crossed under totality, a flaky test, a missing bytes arm, a dead WF clause |

---

## Gates, verbatim

**`lake build`** — from `library/cas`, clean worktree, no `.lake` cache
carried in (built from scratch in this worktree):

```
Build completed successfully (92 jobs).
```

**`mise run --force check:cas`** — exit 0.  Every emitter reports `ok`:

```
ok vectors/index.json (2045 bytes) — 7 vectors
ok schemas/index.json (1031 bytes) — 10 schemas
ok schemas/addresses.json (1321 bytes) — 10 addresses
ok conformance/schema-verdicts.json (74211 bytes) — 71 cases
ok conformance/admission-map.json (10774 bytes) — 22 rows (12 admitted, 8 deferred, 2 rejected)
ok ../effects/src/cas/generated/SchemaAdmission.ts (14198 bytes) — 12 nodes, 35 clauses
ok ../effects/src/cas/generated/ConformanceVectorSchema.ts (1834 bytes) — 6 mirrors
ok ../effects/test/generated/VectorPrograms.ts (19433 bytes) — 7 programs
ok ../effects/test/generated/VectorProgramAddresses.json (2816 bytes) — 7 program addresses
ok ../effects/test/generated/VectorProgramLifts.json (11193 bytes) — 7 lift documents (round-tripped)
ok ../effects/test/generated/EmittedLayers.ts (7758 bytes) — 13 layers
ok mcp/cas-tools.json (12391 bytes) — 6 tools
ok ../effects/src/cas/generated/lift/manifest.json (5478 bytes) — 8 rules
ok ../effects/src/cas/generated/grammar/manifest.json (21676 bytes) — 11 sorts
ok REGISTRY.md (14529 bytes) — 11 sorts, the kind-tag registry
ok surface/cas-surface.json (976501 bytes) — 2098 declarations
10 of 10 controls fire
ok surface/cas-obligations.json (18170 bytes) — 71 obligations
13 of 13 controls fire
ok surface/cas-laws.json (9825 bytes) — 9 of 37 rulings bound, 28 unbound
```

71 verdict cases as claimed.  `git status --porcelain` after the forced
run: EMPTY — the gate regenerates to the committed bytes.

**`bun --bun vitest run`** (library/effects, after
`bun install --frozen-lockfile`):

```
 Test Files  1 failed | 45 passed (46)
      Tests  1 failed | 333 passed (334)
```

The one failure is `test/BrainStem.test.ts` — `Test timed out in 5000ms`,
the test taking 5536ms on a cold import.  Re-run alone it passes in
199ms (`Tests 1 passed (1)`).  A cold-start flake against the default
5s timeout, not a defect of this work, and unrelated to the schema
plane.  See N4.

**Axiom census** — run by me on the public theorems, not taken from the
packet.  Every one of the 37 declarations checked depends on
`[propext, Classical.choice, Quot.sound]` or a subset; two
(`Document.envelope_nil`, `Document.representationDocument_nil`) depend
on none.  No `sorryAx`, no `Lean.ofReduceBool` — so no `native_decide`
anywhere on the path.  Selected:

```
'Cas.Schema.references_guarded_decidable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cas.Schema.Document.wf_iff'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Cas.Schema.ingestDocument_guarded'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Cas.Schema.guarded_list_admitted'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Cas.Schema.unguarded_alias_cycle_refused' depends on axioms: [propext]
'Cas.Schema.aliasCycle_cyclic'            depends on axioms: [propext]
'Cas.Schema.Document.ofEnvelope_envelope' depends on axioms: [propext, Quot.sound]
'Cas.Schema.envelope_nil'                 does not depend on any axioms
```

`grep` for `sorry` / `native_decide` / `axiom ` across `Guarded.lean`,
`Ingest.lean`, `Ast.lean`, `SelfCodec.lean`, `Admission.lean`: nothing.

**Commit order** — PASS, and the roles are clean in both directions:

```
1fa2b45e 00:57:10  the contract packet          -> contracts/PDD-3.contract.md ONLY
e280ad1f 01:02:00  slice 1, the spelling probe  -> test/SchemaReferencesPin.test.ts ONLY
7adc6dc6 01:03:34  the Block                    -> contracts/PDD-3.contract.md ONLY
4c39bf4e 01:13:06  packet amend under the ruling-> contracts/PDD-3.contract.md ONLY
326064e3 01:24:42  slice 2, the carrier         -> no packet file
f486689f 01:48:52  slice 3, the document plane  -> no packet file
92a64ec4 01:49:26  packet close                 -> contracts/PDD-3.contract.md ONLY
```

No implementation commit touches the packet; no packet commit touches
code.  The packet precedes every slice it specifies.

---

## F1 — BREAK: a references table Lean refuses and TypeScript ADMITS

```
BROKE      f486689f — the document plane, both doors
LAW        the packet's cross-door claim: "Cross-door agreement is
           bounded to ADMISSION" (PDD-3.contract.md:126-129), and
           Cas/Backend/Admission.lean:64-67, "Nothing else about C6
           diverges: the guardedness walk, the two node shapes and the
           empty table key are all interpreted from the columns below
           and agree case for case."
WITNESS    one byte string, both doors, opposite answers:

           {"revision":1,"value":{"references":{
              "A":{"$ref":"A","_tag":"Reference"},
              "A":{"_tag":"String","checks":[]}},
             "representation":{"_tag":"String","checks":[]}}}

           Lean  : REFUSE unguardedCycle
           TS    : ADMIT
CLASS      conformance (model <-> carrier), claim-scope
```

The bytes carry the table key `A` twice.  Lean's `Cas.Json.parse` keeps
both pairs; `Document.lookup` takes the FIRST (`Guarded.lean:127`), which
is the self-reference, so the table cycles and the door names
`unguardedCycle`.  `JSON.parse` keeps the LAST, which is a `String`, so
`Object.keys(references)` has one entry with no bare successor and
`admitDocument` admits.  **The two doors read different documents out of
one byte string**, and the disagreement is not confined to the name.

Both directions of the split exist:

| bytes | Lean | TypeScript |
|---|---|---|
| `{"A":ref A, "A":String}` | REFUSE `unguardedCycle` | **ADMIT** |
| `{"A":String, "A":String}` (two well-formed entries) | REFUSE `illFormed` | **ADMIT** |
| `{"A":String, "A":ref A}` | REFUSE `illFormed` | REFUSE `unguardedCycle` |

**Provenance, stated because it changes what is owed.**  The duplicate-key
hazard PREDATES this ticket.  The control is a duplicate `_tag` on a NODE
with an empty table —

```
{"revision":1,"value":{"references":{},
  "representation":{"_tag":"String","_tag":"Null","checks":[]}}}
Lean: REFUSE notASchema      TypeScript: ADMIT
```

— which splits the same way and has nothing to do with C6.  What PDD-3
changed is the REACH: at the parent commit a non-empty `references`
object was refused `nonEmptyReferences` by BOTH doors, so a duplicate
table key could not diverge.  Reading the table converted an agreement
into a disagreement, and `Admission.lean`'s "agree case for case" line
was written over it.

The repair is a ruling, not a patch: either the door takes canonical
BYTES and refuses a non-canonical spelling before either parser sees it
(the estate has `Cas.Json.parse` and `canonicalJson`, so the machinery
exists), or the divergence joins the two already recorded in
`Cas/Backend/Admission.lean` with a corpus row that says so.  A corpus
row today would go red: `test/SchemaVerdicts.test.ts` gates admission AND
the refusal name.

Attack: `Attack.lean` §7, `dupHarmlessLast` and `dupTagNode`.

---

## F2 — HOLE: `Guarded` decides constructibility, not productivity

The module's own statement of purpose (`Guarded.lean:21-26`):

> resolving an unguarded cycle never terminates … The refusal is this
> door's to make or nobody's.

and the taxonomy's (`Ingest.lean:105-116`, `IngestRefusal.unguardedCycle`):

> Resolving one never terminates — the resolver unfolds `A` to get `A` —
> so the table is refused rather than carried.

Two documents whose resolver unfolds `A` to get `A` forever, ADMITTED by
both doors:

```
W1  references {"A": susp(reference "A")}          root reference "A"
W2  references {"A": susp(union[reference "A", null])}  root reference "A"
W1' references {"A": susp(reference "B"),
                "B": reference "A"}                root reference "A"
```

`Attack.lean` §2 proves each is `Guarded` as a PROP —
`suspBareSelf_guarded`, `suspUnionKnot_guarded`, `suspIndirect_guarded`,
each through `references_guarded_decidable`, so this is a fact about the
SPECIFICATION and not about the implementation — and `#guard`s that
`ingestDocument` admits all three.

Measured, on the estate's own TypeScript door (`CanonicalSchema.fromEnvelope`
then `fromRepresentation` then `Schema.decodeUnknownSync`):

```
[knot] door...
[knot] ADMITTED by the door
[knot] revived
[knot] decoder built
                              <- W1: killed at 60s.  No output, no
                                 stack overflow: an infinite loop.

W2: THREW RangeError — Maximum call stack size exceeded.

Forcing W1's Suspend by hand: "forced 5000 levels, still Suspend".
```

CONTROL — the builder's own `guardedList` (corpus row
`admit-guarded-recursion`), same code path:

```
guardedList: ADMITTED / revived / decoder built
  {"value":"a","next":null}                       -> {"next":null,"value":"a"} in 1ms
  {"value":"a","next":{"value":"b","next":null}}  -> ok in 1ms
  {"value":1,"next":null}                         -> SchemaError: Expected string at ["value"]
```

So the door is RIGHT about the shape Effect emits and wrong about its own
reason for existing.  `Ast.susp` is a DELAY, not a constructor: it defers
the loop, it does not break it.  `bareRefs` stopping dead at every `susp`
decides that the EAGER revival terminates — which is what `bareStructCycle`
is about and a real property worth deciding — but it does not decide that
resolution reaches a node.

The distinction, named in `Attack.lean` §2 as `headName`: the productive
positions are the ones that build a JSON value.  `susp` builds none, and
neither does `union`, so the repair is not one line — it is a second
relation over head positions, or a claim-scope line saying guardedness is
constructibility only.  Either is a ruling.

Note this is the SAME class as the builder's own recorded Break, one
level up: `adequacy`, "is `Q` strong enough that no wrong implementation
passes?"  There the operator ruled the spec.  Here the ruled theorem
("every cycle passes through a `susp`") is itself the too-weak `Q` for the
door's stated purpose, so the ruling needs revisiting or the prose needs
narrowing.

---

## F3 — HOLE: the door is exponential in the table size

The packet's `DECREASES` line (`PDD-3.contract.md:243`):

> `|dom(R)| - |visited|` for the guardedness search

There is no visited set in `Document.settles`, on either side of the
wire.  The variant is the FUEL, structurally, and the search re-walks
every path.  A table whose entries each name the next one TWICE gives
`Θ(2ⁿ)`, and the table is ACYCLIC, so the door does the whole exponential
walk and then ADMITS.

`Attack.lean` §5, `fanTable n` — `n+1` entries, every one well formed:

| entries | Lean `Document.guarded` | TypeScript `fromEnvelope` |
|---|---|---|
| 13 | 22 ms | 14 ms (n=10, 11 entries) |
| 17 | 406 ms | 120 ms (n=14) |
| 21 | 7 893 ms | 12 254 ms (n=20) |
| 23 | 35 329 ms | 18 271 ms (n=22) |
| 25 | **302 915 ms** | — |

The n=24 payload is **7 657 bytes**.  Five minutes of CPU for a 7.5 KB
document, doubling every entry.  This is the ingestion door for FOREIGN
content — "a hoovered carrier, a model-minted schema — any spelling"
(`Ingest.lean:8-12`) — so the input is by definition attacker-chosen, and
the door is synchronous on both hosts.

The fix is the memoisation the packet already describes: settle each name
once and cache, which is what `|dom(R)| - |visited|` means.  It changes no
theorem statement — `references_guarded_decidable` is about the
predicate, not the schedule — but it does change `Document.settles`, so
it is a builder's job with a re-proof, not a note.

---

## F4 — HOLE: nothing distinguishes fuel `|table|` from fuel `0`

`Guarded.lean:46-48`:

> Completeness is where the fuel bound earns its exact value … `fuel =
> |table|` is precisely enough to force a repeat and no more.

No witness tests it.  The four C6 rows in
`conformance/schema-verdicts.json` are `admit-references-table`
(`{Node: String}`), `admit-guarded-recursion` (`guardedList`),
`refuse-unguarded-alias-cycle` and `refuse-unguarded-struct-cycle` — and
**both admitted rows have an EMPTY bare-edge relation**, as do both
admitted `#guard`s in `Ingest.lean`.

`Attack.lean` §3 exhibits the wrong-but-passing implementation:

```lean
def guardedWrong (d : Document) : Bool :=
  d.names.all (fun n => (d.out n).isEmpty)     -- fuel ZERO
```

and `#guard`s that it agrees with the shipped `Document.guarded` on all
four corpus rows, on both §1 witnesses, on both §2 witnesses, and on
every empty-table document — which is 67 of the corpus's 71 rows.  A door
that never followed an edge at all passes the entire battery.

It is NOT a correct implementation, and the attack proves it:

```lean
theorem guardedWrong_is_not_the_decision :
    ¬ (∀ d : Document, guardedWrong d = true ↔ d.Guarded)
```

with witness `chain1 = {A: reference "B", B: String}` — `Guarded`, one
acyclic edge, admitted by the shipped door and refused by the fuel-zero
one.  So the spec is adequate and the BATTERY is not: the fuel is held
by the theorem alone, and the theorem is the only thing standing between
the shipped door and the fuel-zero one.

Owed: two corpus rows, `chain1` and `chain2` (a two-edge chain, so
`settles` recurses more than once).  Both admit through the real door
today — `Attack.lean` §3 `#guard`s it — so adding them is a regeneration,
not a repair.

---

## F5 — HOLE: the doors name the same refusal differently

`documentRefusal` (`Ingest.lean:400-402`) is
`if d.guarded then .illFormed else .unguardedCycle` — guardedness FIRST,
so an unguarded document earns `unguardedCycle` whatever else is wrong
with it.  The TypeScript door runs `admitNode` over every table entry
BEFORE the guardedness filter (`CanonicalSchema.ts:665-676`), so it earns
the entry's own refusal.

Witness — a table entry that is both cyclic and ill formed (`b` before
`a`, unsorted):

```
Lean:       REFUSE unguardedCycle
TypeScript: REFUSE illFormed
```

Control, same table with the cycle removed: both say `illFormed`.
Control, the two shipped witness tables: both doors say `unguardedCycle`,
so the name is the guardedness answer and not a coincidence — the
taxonomy probe attack #4 asked for FAILS, which is the good news here.

`test/SchemaVerdicts.test.ts` gates refusal names ("a refused code is
refused BY NAME, and by the same name"), so a corpus row for this
spelling goes red.  There is none, and `Admission.lean:64-67` says there
is nothing left to record.

A second instance of the same shape, this one inside the recorded
empty-name family: a table entry carrying BOTH a cycle and an empty
`$ref` gives Lean `unguardedCycle` and TypeScript `notASchema` (Effect's
`NonEmptyString` fires first).  Cause already recorded; the interaction
with `unguardedCycle` is not.

Cheapest repair: make the TypeScript door run its guardedness filter
before `admitNode`, or make `documentRefusal` test the canonical-fields
clause first.  Either is a one-line reorder plus a corpus row; which one
is a ruling, because it decides which defect a document with two defects
is named for.

---

## Notes

**N1 — claim-scope: "A DEAD table entry is not refused" is not quite
true.**  `PDD-3.contract.md:147`.  A dead entry that CYCLES is refused:
`{A: reference "A"}` with root `String` earns `unguardedCycle` at both
doors even though `A` is unreachable.  `Document.guarded` runs
`d.names.all`, over every name, not over the reachable ones.  Both doors
agree, so it is not a divergence — but the line should read "a dead entry
is not refused for being dead", and the over-refusal relative to Effect
(which reads it back happily) should be stated where the dangling-reference
line is.  `Attack.lean` §4 `deadCycle`.

**N2 — stale prose, twin left behind.**  `Ast.ofRepresentationDocument`
(`SelfCodec.lean:1502-1505`) still says: "revision 1's `references` is
unreachable from the Lean side today (no `Suspend`, no `Reference`
constructor)".  Both constructors landed in 326064e3.  The builder
narrowed the IDENTICAL sentence on `IngestRefusal.nonEmptyReferences`
(`Ingest.lean:93-104`) and did not narrow this one, though the packet's
own Block quotes them as a pair (`PDD-3.contract.md:409-414`).

**N3 — a fence was crossed, under totality.**  The ticket fences `El`'s
denotation; `Cas/Schema/El.lean` is in the diff.  Inspected: the change
is two `Empty` arms and a docstring.  No existing arm moved, no denotation
of any pre-existing code changed, and the arms are forced — adding a
constructor makes the match non-exhaustive.  The builder says so in the
commit body.  Recorded because a fence crossing should be visible in the
break record, not because it is wrong.

**N4 — one flaky test in the effects suite.**
`test/BrainStem.test.ts` times out at the default 5000ms on a cold
full-suite run (5536ms observed) and passes in 199ms when run alone.  The
packet claims 334/334; I measured 333/334 cold and 334/334 warm.  Unrelated
to the schema plane, but the margin is 10% and it will bite CI.

**N5 — the bytes door does not reach the document plane.**
`ingestBytes` (`Ingest.lean:939-942`) composes `Cas.Json.parse` with the
BARE-CODE arm, so every document arriving as bytes is refused
`nonEmptyReferences`.  There is no `ingestDocumentBytes`.  The TypeScript
side does have the composition (`Materialize.fromPayload` takes bytes and
reads a document), which is exactly where F1 lives.  Nothing claims
otherwise, so this is not a break — but the two hosts' doors are not the
same shape any more, and the missing arm is the one the divergence needs.
`Attack.lean` §7 writes the composition out in three lines.

**N6 — `Document.WF`'s strict-order clause is unreachable at the door
except through duplicates.**  `ingestDocument` runs `canonValue` first,
which sorts the table's keys, so `pairwiseRefNames` can only ever fail on
a DUPLICATE name — which is F1.  The packet calls it "the one clause the
encoder cannot supply by construction" (`Guarded.lean:460-462`); at the
door the normaliser supplies it.  `Attack.lean` §6 `outOfOrder` admits.

---

## Failed attempts — every one of them

The attack module keeps these as `#guard`s, because a proof that failed
is earned confidence.

1. **The edge relation misses a nesting.**  `Ast.bareRefs` ends in
   `| _ => []`.  I looked for a constructor with a nested `Ast` falling
   into the catch-all.  There is none: the catch-all covers `null`,
   `bool`, `int`, `str`, `lit`, `ref`, `enum`, and none carries an `Ast`
   (`LitVal` and `EnumValue` are scalars, `ref` is a `UInt8`).  Checked
   per position, including the three separate `tuple` fields and the
   `decl` type parameters.  `Attack.lean` §1.

2. **A reference hidden in `decl`'s payload.**  The `decl` arm walks
   `typeParameters` and not `payload`.  `DeclPayload` is five scalars
   (`Declarations.lean:56-62`) — nothing can hide there.

3. **The two walks disagree.**  Lean's `bareRefs` is constructor-by-
   constructor; TypeScript's is a generic `Object.values` descent
   (`CanonicalSchema.ts:592-613`).  I went through every admitted node
   shape looking for a position one walks and the other does not.  They
   agree on the exactly-spelled subset; the `checks` array is the only
   place TypeScript descends where Lean has no term, and `gateChecks`
   pins its one admitted spelling first.

4. **Extra keys on the new arms.**  `gateKeys` is REQUIRED-not-exact
   (`CanonicalSchema.ts:358-370`) and the `Reference` row's
   `checks: "none"` makes `gateChecks` return before it looks at
   anything, so `{"_tag":"Reference","$ref":"A","checks":[]}` looked like
   a TypeScript admit against a Lean `notASchema`.  It is not: the
   `excessProperties` byte comparison (`:132-135`) catches it upstream.
   Both doors refuse — Lean `notASchema`, TypeScript `notASchema`.

5. **Key order on the new arms.**  The decoder matches exact object
   literals; I tried every permutation of `Reference`'s two keys and
   `Suspend`'s three.  Only the canonical order decodes.  `Attack.lean` §6.

6. **`repNorm` not idempotent on the new arms.**  Suspends inside
   suspends inside a union carrying a reference and a literal null — the
   R13 collapse's own territory.  Idempotent, and the round trip lands on
   the normal form.  `Attack.lean` §6.

7. **The decoder accepts a table spelling the encoder cannot write.**
   `Document.ofRepresentationDocument` does accept an out-of-order table,
   but `canonValue` sorts before it is reached and the WF gate would
   catch what survives, so no reachable spelling is silently admitted.
   Became N6 rather than a finding.

8. **Mutual recursion with the `susp` on one side only.**
   `{A: struct[next: ref B], B: susp(struct[next: ref A])}` — admitted,
   and correctly: one guard on the cycle is enough for the eager revival,
   which is what the relation decides.  Its unguarded twin (no `susp`) is
   refused `unguardedCycle`.  `Attack.lean` §2 neighbourhood.

9. **A dangling reference breaking the decision.**  Admitted, and the
   decision is well defined — a name with no entry has no outgoing edge.
   Exactly as the packet says.

10. **`guarded_list_admitted` is vacuous.**  It is not: it runs through
    `references_guarded_decidable`, so the check's `true` means the
    absence of a cycle and not merely its own answer.  What IS weak is
    that its edge relation is empty — that is F4, not a defect in the
    theorem.

11. **The refusal is a coincidental `illFormed` from an earlier check.**
    It is not.  Both shipped witness tables earn `unguardedCycle` by name,
    and so does a cyclic table with an unrelated defect on it — that is
    F5, and it is the door being TOO eager to name the cycle, not too
    reluctant.

12. **A `native_decide` or a `sorry` hiding in the C6 path.**  None.  The
    axiom census is the standard three; `guarded_list_admitted` uses
    `by decide`, which is kernel reduction, not `ofReduceBool`.

---

## Regression objects

If F1–F5 are repaired, re-run

```
lake env lean contracts/attacks/PDD-3/Attack.lean
```

and the module's status is the mechanical proof of what closed:

- **F2 closed** ⇒ `suspBareSelf_guarded`, `suspUnionKnot_guarded` and
  `suspIndirect_guarded` STOP ELABORATING (the documents are no longer
  `Guarded`), and the three `admits` guards go red.  That failure is the
  fix's receipt.
- **F4 closed** ⇒ the `guardedWrong` agreement guards in §3 go red as
  soon as `chain1`/`chain2` join the corpus; `guardedWrong_is_not_the_
  decision` keeps standing, because it is a fact about the fuel-zero door
  and not about the battery.
- **F1, F3, F5 closed** ⇒ §7's `dupHarmlessLast` guard and §4's
  `unsortedAndCyclic` guard change answer, and §5's timings are re-taken.

Nothing in this file is imported by any lake target, so a red `#guard`
here reddens only this file — which is the point: it is evidence, not a
gate.

---
---

# RE-RUN — the break pass, against the fix

```
SUBJECT     branch agent/opus-cc-mac/pdd-3, tip c700279d (fix-pass close)
            766d695f packet · f8a2da76 F2/N2 · 599ef9eb F3 · c6a70338 F1/F4/F5
METHOD      the fix merged onto attack/opus-cc-mac/pdd-3; every probe re-run
            from that tree.  The FIRST-PASS record above is untouched.
ATTACK      ./Attack.lean  — unchanged, re-run, exactly one red (below)
            ./Attack2.lean — the re-attack, elaborates clean
```

## VERDICT — STANDS-AMENDED

Five findings closed, two notes closed, one narrowed by ruling rather than
by code and saying so, and **one of my own first-pass gradings withdrawn**.
Two small new divergences fall out of the F1 gate itself; both are naming,
neither is admit-versus-refuse, and both are recorded here rather than
carried silently.

| # | Grade now | Evidence |
|---|---|---|
| F1 | **CLOSED — and DOWNGRADED from BREAK** | one name, both key orders, five spellings; my BREAK grade was an artifact of my entry point |
| F2 | **CLOSED BY NARROWING** — prose only, ruling owed | witnesses cited in `Guarded.lean`; semantics deliberately untouched |
| F3 | **CLOSED** | 41 entries: Lean 0 ms, TypeScript 147 ms; was `Θ(2ⁿ)` |
| F4 | **CLOSED** | re-derived over all 76 corpus rows, not my four names |
| F5 | **CLOSED**, TypeScript moved to Lean | seven order rows, both hosts identical |
| N1 | CLOSED | claim-scope line now reads "not refused FOR BEING DEAD" |
| N2 | CLOSED | the stale twin narrowed like its sibling |
| N3–N6 | unchanged, correctly | fence / flake / bytes-arm / dead clause, all still true and all recorded |
| R1 | **new HOLE** | the two duplicate gates are not the same gate |
| R2 | **new NOTE** | the scanner unescapes for a reader with no `\u` case |

## WITHDRAWN — my F1 grade was wrong

F1 said "a references table Lean refuses and TypeScript ADMITS", graded
BREAK. The admit was real, but I obtained it through
`CanonicalSchema.fromEnvelope(JSON.parse(payload))`. The SHIPPED bytes
door is `Materialize.fromPayload`, and it has always run
`decodedVersionedEnvelope` first, which re-renders the parsed value and
refuses when the bytes differ. At `92a64ec4`:

```
library/effects/src/cas/Value.ts:218
        throw new TypeError("Projection payload is not canonical JSON")
library/effects/src/cas/Materialize.ts:120
    const envelope = yield* decodedVersionedEnvelope(payload)
```

A duplicate key makes a payload non-canonical, so the shipped door
already refused my witness at the subject commit — ANONYMOUSLY, as a
`TypeError`, which `SchemaVerdicts.test.ts` reads as "refused without a
name". The defect was real and worth the fix, but it was a NAMING
divergence on the shipped path, not an admission one, and BREAK
overstated it. The builder reached the same correction independently and
wrote it into the packet (§The assumed ruling: "already turned these
payloads away … but ANONYMOUSLY"). The record stands corrected here
rather than quietly.

## F1 — CLOSED. Both key orders, five spellings, one name

`ingestDocument` now asks `duplicateReferenceKey` BEFORE the decoder, and
`admitPayloadSpelling` reads the payload bytes ahead of any parser, wired
into `Materialize.fromPayload` and `get`. Every row, both hosts:

| payload | Lean | TypeScript |
|---|---|---|
| `{"A":ref A,"A":String}` — reference FIRST | `illFormed` | `illFormed` |
| `{"A":String,"A":ref A}` — reference LAST | `illFormed` | `illFormed` |
| `{"A":String,"A":String}` — IDENTICAL values | `illFormed` | `illFormed` |
| `{"A":String,"A":Null,"A":ref A}` — THREE-way | `illFormed` | `illFormed` |
| `{"A":Null,"A":Null,"A":Null}` — three identical | `illFormed` | — |
| `{"A":String,"B":Null}` — partner | ADMIT | ADMIT |
| `{"A":String}` — partner | ADMIT | ADMIT |

The last two are the partner without which refusing every table would
pass. Corpus rows `refuse-duplicate-reference-key` and
`refuse-duplicate-reference-key-last` carry the first two.

**The node-level twin is recorded owed, not silently fixed** — confirmed,
which is what the fix's scoping claims:

| payload | Lean | TypeScript |
|---|---|---|
| duplicate `_tag` on the ROOT node | `notASchema` | refused UNNAMED (`TypeError: … not canonical JSON`) |
| duplicate `_tag` INSIDE a table entry | `notASchema` | refused UNNAMED |

Both refuse; TypeScript still refuses without a name. That is exactly the
packet's owed row — "one 'the bytes are not a canonical spelling'
refusal, named, on both hosts" — and the gate did not quietly widen to
cover it.

## R1 — new HOLE: the two duplicate gates are not the same gate

Lean's `duplicateReferenceKey` pattern-matches the CANONICAL envelope
(`revision`/`value`, then `references`/`representation`, exactly two keys
each) and answers `false` for anything else. TypeScript's is a byte
scanner keyed on the container path `["value","references"]`, and it does
not care what else the envelope carries. A payload that is both
shape-broken and duplicate-keyed therefore splits:

```
{"revision":1,"value":{"extra":0,
  "references":{"A":{"_tag":"String","checks":[]},"A":{"_tag":"Null","checks":[]}},
  "representation":{"_tag":"String","checks":[]}}}

Lean:       REFUSE notASchema   (the gate's pattern misses; the decoder answers)
TypeScript: REFUSE illFormed    (the scanner fires first)
```

Both refuse, so this is a naming divergence and not an admission one —
but `SchemaVerdicts.test.ts` gates refusal names, so a corpus row for it
would go red. Cheapest repair: let Lean's gate find the references object
wherever it sits, or let the TypeScript scanner stand down when the
envelope is not the canonical two-key shape. Either is a small change
plus a corpus row. `Attack2.lean` §1, `extraKeyAndDuplicate`.

## R2 — new NOTE: the scanner unescapes for a reader with no `\u` case

`CanonicalSchema.ts`'s `stringLiteral` exists so that a plain `"A"` and an
escaped `"A"` compare equal, and its stated reason is that they "are
the same name to Lean's reader". They are not. `Cas.Json.parse` has no
`\uXXXX` case at all and refuses the payload outright — in a key or in a
value — while `\n`, `\"` and `\\` all parse:

```
plain              true
A in value    false
A in key      false
\n in value        true
escaped quote      true
escaped backslash  true
```

So the escaped-duplicate spelling is `illFormed` in TypeScript and
`notASchema` in Lean, and the premise written into the new docstring is
false. The parser gap is pre-existing and far outside C6; the sentence
claiming the agreement is new in `c6a70338`. `Attack2.lean` §1.

## F2 — CLOSED BY NARROWING, and the semantics were right to stay

`Guarded.lean` now opens with "a cycle with no guard on it cannot be
BUILT" and carries a "What this does NOT decide" section naming all three
witnesses, the `guardedList` control, the `headName` sketch and the branch
this record sits on; `IngestRefusal.unguardedCycle` is narrowed the same
way. The admission semantics did not move, and that is correct — the
productivity relation is an open ruling, recorded owed in the packet's
follow-on list.

Verified untouched:

```
w1  {A: susp(reference A)}               guarded=true  memo=true  door=ADMIT
w2  {A: susp(union[reference A, null])}  guarded=true  memo=true  door=ADMIT
w3  {A: susp(ref B), B: ref A}           guarded=true  memo=true  door=ADMIT
```

## F3 — CLOSED. The memo, and the classic error probed

`Document.guardedMemo` is the procedure the door RUNS, not a paper twin:
`Document.wf` (`Ingest.lean:394`) and `documentRefusal` (`:415`) both call
it, `Document.wf_iff` goes through `references_guarded_decidable_memo`,
and the only surviving uses of the naive `Document.guarded` in
`Ingest.lean` are three `#guard` witnesses. So `guardedMemo_eq_guarded`'s
subject is the shipped procedure.

The first pass's `fanTable`, re-run on both hosts:

| entries | Lean, first pass | Lean, now | TypeScript, first pass | TypeScript, now |
|---|---|---|---|---|
| 13 | 22 ms | 0 ms | — | — |
| 26 | 302 915 ms (at 25) | **0 ms** | — | **149 ms** (7 972 B) |
| 31 | out of reach | **1 ms** | out of reach | **147 ms** (9 547 B) |
| 41 | out of reach | **0 ms** | out of reach | **147 ms** (12 697 B) |

And the two walks still agree wherever the naive one can be run
(`fanT 8`, `fanT 12`).

**The on-ENTRY memo control fires.** A memo that records a name on the way
IN calls a cycle settled. I implemented that error on both hosts and ran
it against the builder's control — the fan with its tail wired back to its
head:

```
Lean        shipped memo  fanCycle 8  = false    ENTRY memo = true
            shipped memo  fanCycle 40 = false    ENTRY memo = true
            shipped memo  aliasCycle  = false    ENTRY memo = true
TypeScript  shipped  fanCycle 8 / 40 / aliasCycle -> REFUSE unguardedCycle
            ERROR    fanCycle 8 / 40 / aliasCycle -> ADMIT
            both agree on the ACYCLIC fan 40      -> ADMIT
```

So the control discriminates, and it is over-covered: the two cycle
witnesses that predate the memo catch the same error, so it is a second
net rather than the only one. `Attack2.lean` §3. The shipped door answers
the tail-wired fan at 41 entries by name — `unguardedCycle`, 16 ms.

## F4 — CLOSED, re-derived from the CORPUS

The builder's note asked a follow-on breaker to read the corpus instead of
naming four rows. Done — all 76 rows, decoded and compared:

```
corpus rows read: 76
decodable rows compared : 61 (undecodable: 15)
fuel-zero AGREES on     : 59
fuel-zero DISAGREES on  : 2
    admit-reference-chain      (fuel-zero false, door true)
    admit-reference-chain-two  (fuel-zero false, door true)
rows with NON-EMPTY bare edges: 6
    refuse-unguarded-alias-cycle    out:[A, B]
    refuse-unguarded-struct-cycle   out:[A]
    admit-reference-chain           out:[A]
    admit-reference-chain-two       out:[A, B]
    refuse-unguarded-and-illformed  out:[A]
    refuse-duplicate-reference-key  out:[A, A]
corpus replay against the door — mismatches: 0
```

Two rows now separate the fuel-zero door from the shipped one, where none
did; six rows carry a non-empty edge relation, where two did. The replay
also confirms the door still answers every recorded verdict AND every
recorded refusal name. `Attack2.lean` §5 re-derives the separation as a
proposition.

## F5 — CLOSED, and TypeScript moved to Lean

Seven order rows, both hosts, identical answers:

| table | Lean | TypeScript |
|---|---|---|
| cycle + ill-formed entry | `unguardedCycle` | `unguardedCycle` |
| ill-formed entry alone (control) | `illFormed` | `illFormed` |
| cycle + empty table key | `unguardedCycle` | `unguardedCycle` |
| cycle + ill-formed ROOT | `unguardedCycle` | `unguardedCycle` |
| **cycle + UNDECODABLE entry** | **`notASchema`** | **`notASchema`** |
| **cycle + unknown declaration** | **`unknownDeclaration`** | **`unknownDeclaration`** |
| undecodable root, guarded table | `notASchema` | `notASchema` |

The held-refusal replay is right: `illFormed` is held and replayed after
the guardedness filter, while `notASchema` and `unknownDeclaration` — the
decoder's own answers — are rethrown at once. **Undecodable still wins.**

## The three prediction divergences

§Regression objects above predicted three receipts. All three were wrong,
and each was wrong in the same direction — I assumed a fix would move
semantics where it correctly moved a claim:

1. **"F2 closed ⇒ §2's three theorems STOP ELABORATING."** They still
   elaborate. The fix narrowed the prose and left admission alone, because
   the productivity relation is a ruling. My prediction assumed the only
   honest close was a semantic one; narrowing the claim is the other
   honest close, and the cheaper one.
2. **"F4 closed ⇒ §3's `guardedWrong` agreement guards go red."** They are
   still green. They name the four ORIGINAL corpus rows, which did not
   move; the separation lives in the two NEW rows. The prediction was
   written against a battery I had hard-coded instead of read — which is
   exactly the note the builder left for a follow-on breaker, and §F4
   above is me taking it.
3. **"F1/F3/F5 closed ⇒ §7's `dupHarmlessLast` AND §4's
   `unsortedAndCyclic` change answer."** Only the first did.
   `unsortedAndCyclic` was always `unguardedCycle` in Lean; F5 closed by
   TypeScript adopting Lean's order, so the Lean-side guard could not move.

## Attack.lean re-run — exactly one red, as predicted

```
contracts/attacks/PDD-3/Attack.lean:454:0: error: Expression
  match ingestDocumentBytes dupHarmlessLast with
  | Except.error IngestRefusal.unguardedCycle => true
  | x => false
did not evaluate to `true`
```

One guard, and it is F1's receipt: the duplicate-key payload that earned
`unguardedCycle` now earns `illFormed`. Everything else in the module —
§1's edge census, §2's three theorems, §3's `guardedWrong` sweep and
`guardedWrong_is_not_the_decision`, §4's taxonomy, §5's fan, §6's twelve
failed attacks, §7's bytes composition — still elaborates. The file is
left as it is: a red that is a receipt is evidence, and editing it would
destroy the trace.

`Attack2.lean` elaborates clean.

## Gates — re-run, verbatim

`lake build` and `mise run --force check:cas` → exit 0:

```
ok conformance/schema-verdicts.json (77310 bytes) — 76 cases
ok conformance/admission-map.json (10774 bytes) — 22 rows (12 admitted, 8 deferred, 2 rejected)
ok ../effects/src/cas/generated/SchemaAdmission.ts (14580 bytes) — 12 nodes, 36 clauses
ok schemas/addresses.json (1321 bytes) — 10 addresses
ok surface/cas-surface.json (983228 bytes) — 2122 declarations
ok surface/cas-obligations.json (18399 bytes) — 72 obligations
ok surface/cas-laws.json (9825 bytes) — 9 of 37 rulings bound, 28 unbound
10 of 10 controls fire
13 of 13 controls fire
Build completed successfully (92 jobs).
```

`schemas/addresses.json` is byte-for-byte what it was at `92a64ec4` — the
fix moved no address. `git status --porcelain` after the forced run: EMPTY.

`bun --bun vitest run`:

```
 Test Files  47 passed (47)
      Tests  336 passed (336)
```

47 files where there were 46 (`SchemaGuardednessCost.test.ts` is new), 336
tests where there were 334. **All green, including `BrainStem.test.ts`** —
N4's cold-start flake did not reproduce on this run, so it stays a note
about the 5 s margin rather than a finding.

## Axiom census — the fix-pass theorems

Every new declaration on the memo path depends on
`[propext, Classical.choice, Quot.sound]` or a subset. No `sorryAx`, no
`Lean.ofReduceBool` — so no `native_decide`, and the well-founded
`settleAll` recursion introduced no axiom of its own:

```
'Cas.Schema.references_guarded_decidable_memo'    [propext, Classical.choice, Quot.sound]
'Cas.Schema.Document.guardedMemo_eq_guarded'      [propext, Classical.choice, Quot.sound]
'Cas.Schema.Document.settleAll_grows'             [propext, Quot.sound]
'Cas.Schema.Document.settleAll_settling'          [propext, Quot.sound]
'Cas.Schema.Document.settleAll_isSome'            [propext, Quot.sound]
'Cas.Schema.Document.settles_succ / _mono / _uniform'  [propext, Quot.sound]
'Cas.Schema.Document.settling_of_out'             [propext, Quot.sound]
'Cas.Schema.Document.wf_iff'                      [propext, Classical.choice, Quot.sound]
'Cas.Schema.ingestDocument_wf / _guarded / _nil'  [propext, Classical.choice, Quot.sound]
'Cas.Schema.refChain_guarded / refChainTwo_guarded'    [propext, Classical.choice, Quot.sound]
```

## What is still owed

Nothing that blocks the landing. R1 and R2 are new and small; the first
pass's N3 (a fence crossed under totality), N5 (`ingestDocumentBytes`) and
N6 (the dead `WF` clause) stand as recorded; and the packet already
carries the productivity ruling, the registry row, the node-level
duplicate-key refusal and the `Suspend` lowering as owed.
