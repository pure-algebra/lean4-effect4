# Conformance workflow — dual-lane verified development

Status: RATIFIED by grilling 2026-08-26 (operator, in-session; rulings
WGR-1 through WGR-7 plus two rider rules — instructional closure and plain
meaning; recommendations accepted throughout, with the staged option selected
for cycle-state modeling). This document owns the workflow's process
vocabulary; the library's domain vocabulary stays with the
[Effect Replay context](../../docs/effect-replay/CONTEXT.md).
Claim posture: workflow rules only; no model, theorem, or implementation
claim is admitted by this document.

## 1. Purpose

This library's development doubles as the testbed for a second deliverable:
an AI-generated but conformance-verified programming workflow. Two model
harnesses work in separate lanes — one authors the Lean model, invariants,
and conformance vectors; one writes the TypeScript implementation against
them — with a human ratification point between the lanes and the Lean kernel
underneath both.

Effect is the deliberate entrance because the M0 contract already reified the
observable surface as data: operations, decisions, histories, and outcomes
are first-order values. Conformance-by-vectors works precisely because the
seam is data; arbitrary imperative TypeScript has no comparably cheap seam.

The claim ceiling is fixed: this workflow produces a kernel-checked model
plus a forced-agreement implementation. It never produces "verified
TypeScript." Gate vocabulary is unchanged — model theorems are G1/G2
material, differential agreement is G4-labeled sampled evidence, and no
metric below promotes a claim across a gate.

## 2. Trust architecture

The central design problem is **correlated error**: when one model harness
writes the conformance code and another writes the implementation, the
kernel guarantees the proofs but nothing guarantees the statements. A
mis-quantified invariant proves cleanly and constrains nothing, and two
harnesses drawing on similar priors can be wrong in the same direction.

Every trust anchor exists to break that correlation:

| Anchor | What it secures | Who or what carries it |
| --- | --- | --- |
| Lean kernel | proofs of stated theorems | machine |
| Ratified statement schemas | quantifier structure of every invariant | human, once per schema |
| Ratified sentence templates | plain meaning of every invariant | human, once per schema |
| Sampled vector review | vectors mean what the contract means | human, per ratification point |
| Deterministic generation | manifests come from the model, not hands | generated-vectors law |
| Anti-vacuity kits | statements are non-trivial | compile-checked `#guard`s |
| Mutation kill-rate | vectors actually pin the semantics | machine, measured |
| Lane independence | no shared blind spots between lanes | workflow rule |

Both harnesses hold `TOOLS.md` rows with the estate's standard empty trust
contribution. The gates and the anchors above carry all trust; the harnesses
carry none.

## 3. The two lanes

**Conformance lane**: extends the Lean model from the ratified contract,
instantiates statement schemas with their sentences and anti-vacuity kits,
maintains the declared mutants, and generates the manifest by executing the
model. It never edits the TypeScript tree.

**Implementation lane**: edits the TypeScript implementation until the gate
is green against the **last ratified manifest**. Failures carry obligation
IDs pointing at exact Lean statements. It never edits the Lean tree and
never edits a manifest.

**Coupling rule:** the versioned manifest is the only interface between the
lanes. A lane editing the other lane's tree, or either lane hand-editing a
manifest, is a named defect.

**Ratified-manifests-only rule:** a generated-but-unratified manifest is
invisible to the implementation lane. While a new manifest version awaits
ratification, the implementation lane keeps working against the previous
ratified version — the pipeline never blocks on ratification.

**Independence rule:** the lanes run in separate harness contexts. One
context playing both roles in a single conversation is a named defect — the
independence is part of the trust argument, not an operational convenience.

## 4. Statement schemas — the ratified catalog

A **statement schema** fixes an obligation family's shape once, under
grilling. A schema bundle has three ratified parts: the **statement
template** (quantifier structure with named holes), the **sentence template**
(plain meaning with the same holes; section 5), and the **kit template**
(what a positive and a falsification witness look like for that shape;
section 10). Harness-authored work only *instantiates* bundles; audit means
reading a small diff against a known shape. A statement that fits no
ratified schema is a stop condition.

Realization (M1 refinement): each family is a Lean structure in
`Effects/Conformance.lean` whose fields are the template's holes, whose laws
are proof fields, and whose anti-vacuity kit is also fields. An obligation
instance is a term of the family structure — a term without its law or kit
does not elaborate, so proved-without-kit is unrepresentable for Lean-side
artifacts.

The catalog (WGR-2), seeded from the obligation ledger:

| Schema family | Statement shape | First instances |
| --- | --- | --- |
| WF-PRESERVE | `∀ s i, WF s → hyp → WF (step s i)` | reducer step well-formedness; record append |
| TRACE-EXCLUDES | `∀ s i, mode/flag s = m → d ∈ decisions (step s i) → d ≠ bad` | RPL-002; SES-001 (aborted session never appends) |
| EXACT-STEP | `∀ s q, hyp → measure (step s q) = measure s + δ` | RPL-003; record append length |
| FAIL-CLOSED | `∀ s q, ¬hyp → step s q rejects ∧ consumes nothing` | RPL-004; RPL-005's completion form |
| DISTINCTNESS | `∀ s q q', content q = content q' → occurrences distinct` | CMP-002 |
| HOMOMORPHISM | `interp (bind p k) = …` over both outcome cases | CMP-001; return/bind laws |
| CODEC | `decode ∘ encode = some` ∧ `encode` injective on canonical forms | CAS-001 |
| REJECTION-CLAUSE | `∀ raw, admit raw = error c ↔ Clause c raw` | CAS-002 node admission |
| AGREEMENT | `∀ x, hyp x → rel (observeF (f x)) (observeG (g x))` | RMT-015 remote-load refinement; RMT-016 cache observation (added at the remote Pass A, 2026-08-27; generalized to the relational form at the R1 correction — equality instances take `rel := Eq`) |

Cross-cutting: every checker carries the boolean-reflection iff
(`check x = true ↔ Prop x`) — one judgment, one decision surface, one iff.

Deliberate exclusions, ratified: **CTX-001/002 have no Lean schema** — they
are TypeScript-side obligations (typecheck, layer graph, tripwire fixtures),
and a Lean statement claiming them would fake coverage. **CAS-003 is a
review rule, not a schema** — "every address law carries its lattice level"
is checked by reading theorem signatures.

## 5. The plain-meaning rule

Auditability needs humans to read what is actually being tested and
conformed to, in the domain language of the codebase. The plain-language
layer therefore follows the same schema/instance discipline as the formal
layer:

- every schema family ratifies a **sentence template** with named holes;
- every instance fills the holes **in the minted domain vocabulary** — the
  Effect Replay context document is the glossary that makes those sentences
  precise;
- every declared mutant states **what killing it represents**, in the same
  register;
- sentences are **single-sourced** as fields of the typed artifact — the
  `sentence` field of a schema-bundle instance, the `represents` field of a
  mutant — and **projected** onto the ledger, briefings, and manifest family
  headers by the emitter, which reads typed instances and never parses
  comments. Docstrings carry the ratified *templates*; fields carry the
  *instances*. Hand-editing a projection is the derived-surface defect. The
  ratification diff shows sentence and statement together, so a statement
  that moved under an unmoved sentence is visible in one review.

```lean
/-- SCHEMA EXACT-STEP sentence: "When <hypothesis>, one reducer step changes
    <measure> by exactly <δ> — <domain gloss>."

    When the emitted request matches the entry at the cursor, one reducer
    step advances the cursor by exactly one — a matching request consumes
    exactly one occurrence: never zero, never two. -/
theorem RPL_003_exact_consumption ... := ...
```

Manifest rows stay data: the family header carries the obligation's
sentence; case ids stay readable; boundary cases may carry a one-line note.

## 6. The manifest — the inter-lane contract

Per-family JSON files, generated by executing the Lean model:

```text
library/effects/conformance/manifest/
  RPL-003.json
  RPL-004.json
  ...
```

```json
{
  "family": "RPL-003",
  "model": "effects-model@<version>",
  "meaning": "<projected obligation sentence>",
  "rows": [
    { "case": "repeat-identical-002",
      "input":  { "state": "...", "request": "..." },
      "expect": { "decisions": ["consume", "substitute"], "outcome": "..." } }
  ]
}
```

The five ratified rules (WGR-4):

1. **Lean writes it, through a canonical printer** — sorted keys, declared
   number handling, rows sorted by case id.
2. **Version binding is to the declared model version, not the commit.** Any
   semantics-affecting model change bumps `effects-model@x.y.z`;
   regeneration under an unchanged version must be byte-identical (the
   gate's ratchet check); a bump is a declared transformation, and old
   manifests are deleted — git history is the CAS that keeps them
   recoverable.
3. **Family digests live on the ledger** and nowhere else.
4. **Inputs are authored as Lean fixtures** (handwritten scenarios are
   canonical inputs; outputs are never written by hand). A scenario
   conceived on the TypeScript side is transcribed into a Lean fixture by
   the conformance lane.
5. **The TypeScript suite consumes rows verbatim**, decodes, and compares
   decision traces structurally under the declared normalization — never by
   re-serialization, so printer quirks cannot masquerade as agreement.

One name binds all surfaces: ledger ID = Lean theorem name = manifest
family = TypeScript test name. A red test is one grep from its statement.

## 7. Mutation runs — the honesty metric

Row counts do not measure coverage; kill rates do. Ratified form (WGR-3):

- **Declared mutants only** — no automated mutation tooling. One
  hand-declared mutant per obligation-ledger falsification case is the
  floor, named by the obligation it attacks
  (`Effects/Mutants/RPL003_SkipAdvance.lean`, `test/mutants/RPL-003-*.ts`),
  each carrying its plain-meaning header (what killing it represents).
- **Quarantine:** mutants are never proof-bearing and never imported by the
  real model; a gate grep asserts `Effects/` never imports
  `Effects/Mutants/`.
- **Two directions, both asserted by the gate:**

```text
direction 1 (vector sensitivity):    manifest(mutant model) ≠ manifest(model)
direction 2 (suite discrimination):  suite(TS mutant, ratified manifest) = RED
```

- **A survivor fails the task** — hard, never a warning — and becomes a
  conformance-lane vector task before any milestone exit. No waivers.
- Placement: `check:effects:mutation` runs inside the root check and at
  every ledger regeneration; the inner dev loop may run it targeted. Kill
  rate lands on the ledger per family and is quoted as evidence, never as
  proof.

## 8. Cycle state and harness alignment

Ratified model (WGR-1): **cycle state is a derived projection of the tree at
a commit.** Nothing about the cycle lives outside the repo. Ratification
events are committed documents (the M0 pattern, now a rule); everything else
is computed by gate tasks. The commit hash is the state identity.

**Plane boundary:** git is the CAS of the development plane; the library's
runtime CAS is a different plane. They share the discipline — canonical
bytes, content addressing, derived-never-hand-maintained — and no
implementation. Routing development state through the effects `CasStore` is
a named defect.

**Two generated surfaces**, each a deterministic function of
`(commit, lane)`:

- the **conformance ledger** (section 9) — committed, byte-compared, the
  ratchet's substrate; and
- the **briefing** — on-demand, never committed
  (`mise run brief:effects -- --lane=<lane>`): commit and version identity,
  the lane's next targets with statements and sentences excerpted from
  source, red rows, and the standing rules in scope. Everything in it is
  derived, so briefing drift is impossible by construction.

**Ratchet-driven targeting:** obligations sit in the dependency DAG the plan
already declares; `next()` is the least red obligation whose dependencies
are green, per lane. Each run tells the next step.

**Staged Lean lift:** phase 1 (M1) implements the ledger schema and the
transition-legality check as gate scripts. Phase 2 — only after the workflow
has survived real slices — lifts the transition system into a small Lean
model with the monotonicity theorem and conformance-checks the script
against it, entering through its own Pass A like any extension.

**Statelessness rule (the alignment guarantee):** a lane harness must be
fully resumable from `(commit, lane, briefing)` alone. Relying on
conversation memory for cycle state is a named defect — sessions are
stateless functions of the tree.

**Instructional closure (rider):** everything that shapes a lane —
`AGENTS.md`, context documents, lane role definitions, briefing inputs — is
versioned in-tree, so `(commit, lane)` determines the full harness input.
If anything load-bearing is ever found living outside the tree, it either
moves in-tree or is declared here as an explicit exception.

## 9. The conformance ledger

`library/effects/CONFORMANCE-LEDGER.md`, generated by the gen task,
byte-compared by the gate, transition-checked between commits (green never
regresses except through a declared model-version bump). Shape (WGR-5): a
narrow status table plus per-obligation sentence blocks:

```markdown
| ID      | Schema      | Proof   | Kit | Vectors   | Kill | Stamp |
| ------- | ----------- | ------- | --- | --------- | ---- | ----- |
| RPL-003 | EXACT-STEP  | proved  | ok  | 7/7 green | 2/2  | G1    |

## RPL-003 — exact consumption
<projected sentence>
Manifest: RPL-003.json · sha256 <digest> · <n> rows
```

Mechanical rules: `Proof: proved` is written only when kernel evidence
exists *and* the kit markers are found — proved-without-kit renders as
`pending` by construction; the axiom report gates the G1 stamp; family
digests live here and nowhere else. Wired into the root `gen`/`check` tasks
like every derived surface.

## 10. Anti-vacuity kits — gate-enforced

`#guard` fails at compile time, so enforcement is nearly free (WGR-7):

```lean
#guard checkExactConsumption exampleMatchingStep          -- positive witness
#guard !(checkExactConsumption exampleMismatchStep)       -- falsification witness
```

For Lean-side artifacts, presence is type-enforced (M1 refinement): kits are
fields of the schema-bundle structures, so an instance without its witnesses
does not elaborate and the ledger emitter needs no grep. The `#guard` and
naming-convention route remains for artifacts outside the structures — the
mirrored TypeScript mutants and any standalone checkers. Truth is the Lean
build itself in both routes. Review still reads kits at ratification — for
meaning, not existence. Each schema family's kit template (ratified with the
bundle) defines what its witnesses look like: a falsification witness for
WF-PRESERVE is an ill-formed raw state; for TRACE-EXCLUDES it is the
record-mode trace that does delegate; DISTINCTNESS is positive-only by shape
(its only falsification would deny the law itself).

## 11. The ratification point

Fires **per manifest version, not per commit** — whenever the conformance
lane emits a version carrying new or changed statements. The ratifier sees a
generated projection: schema-instance diffs (statement and sentence
together), sampled vectors, mutation survivors, and the ledger delta. Proofs
are not reviewed by hand; the kernel and the axiom report carry them. A
rejection returns named corrections to the conformance lane while the
implementation lane continues against the previous ratified version. In this
repository the ratifier is the operator and the cadence rides the milestone
rhythm.

## 12. One loop iteration

```text
ratified contract
      |
      v
[conformance lane]  extend model, instantiate schema bundles (statement +
      |             sentence + kit), maintain mutants, execute model
      |             -> manifest v(n)
      v
[ratification]  schema-instance diffs, sampled vectors, mutation survivors;
      |         statements and sentences only, never proofs
      v
[implementation lane]  brief from (commit, lane); edit TypeScript until gate
      |                green vs ratified manifest v(n)
      v
[ledger update]  gate stamps, kill rates, green rows; ratchet holds
      |
      v
next slice — or a contract-level surprise from either lane hits the stop
conditions and returns to grilling
```

## 13. Stop conditions

Stop and return to grilling if:

- a statement appears that fits no ratified schema;
- a lane edits the other lane's tree, or any hand edits a manifest;
- the implementation lane consumes an unratified manifest;
- one harness context plays both lanes in a single conversation;
- an anti-vacuity kit is missing, or a falsification witness cannot be
  produced for a stated invariant;
- a mutation survivor is waived instead of covered;
- a projected sentence is hand-edited, or a statement changes under an
  unchanged sentence without review;
- development state is routed through the library's runtime CAS, or a
  load-bearing harness input is found out-of-tree and left undeclared;
- a kill rate or vector count is quoted as proof, or any surface says
  "verified TypeScript";
- a pending proof is treated as proved on any ledger or claim surface; or
- manifest or ledger regeneration is not byte-identical from declared
  sources under an unchanged model version.

## 14. Ratification record (2026-08-26)

- **WGR-1** — cycle state as derived tree projection; git/runtime plane
  boundary; ledger + briefing surfaces; ratchet-driven `next()`; staged Lean
  lift (phase 1 scripts, phase 2 own Pass A); statelessness rule. Rider:
  instructional closure.
- **WGR-2** — the eight-family schema catalog with CTX-*/CAS-003 exclusions;
  instances name their schema; bundles carry statement, sentence, and kit
  templates.
- **WGR-3** — declared mutants only, one per falsification case as floor,
  quarantined and gate-grepped; both mutation directions asserted; survivor
  fails the task.
- **WGR-4** — per-family manifests under the five rules; model-version
  binding with byte-identical regeneration; ledger-carried digests.
- **WGR-5** — ledger shape as in section 9 with the mechanical
  proved-without-kit rule.
- **WGR-6** — lane roles landed in `TOOLS.md`; per-manifest-version
  ratification cadence; ratified-manifests-only consumption.
- **WGR-7** — gate-enforced kits via compile-checked `#guard`s plus
  convention grep; kit templates ratified per schema family.
- **Rider: plain meaning** — sentence templates per schema, mutant meanings,
  single-source sentences projected to ledger/briefing/manifest headers.
- **M1 refinement (2026-08-26, recorded at the M1 opening):** schema bundles
  are realized as Lean structures with laws and kits as fields
  (`Effects/Conformance.lean`), per the
  [`tree-sitter-plan-prior-art`](research/tree-sitter-plan-prior-art.md)
  note. This strengthens WGR-7 (kit presence type-enforced for Lean-side
  artifacts; grep route retained for TS-side) and the plain-meaning rule
  (sentence source is the typed `sentence`/`represents` field; docstrings
  carry templates) without changing either rule's substance.
- **M2 ratification (2026-08-27, manifest version `effects-model@0.1.0`):**
  the operator ratified the CAS-001 (CODEC) and CAS-002 (REJECTION-CLAUSE)
  statement-and-sentence pairs — including CAS-001's identity-canon reading
  (the carrier's declared equivalence is equality, so canonicality lives in
  decoder exactness) and CAS-002's fixed kit store with the `Unit` admitted
  carrier — the `effects-model@0.1.0` declaration with the
  append-to-`ratifiedManifestVersions` committed-document mechanic, and the
  five first vectors. Riders: the fixed kit-store semantics are re-examined
  when application-level Effect testing brings real contexts, which may be
  different things; vector growth is a declared next-cycle task under the
  unchanged version (row additions change no statement, so they do not
  re-fire ratification); family digests on the ledger are deferred to the
  implementation-lane consumption step, where a manifest consumer exists to
  digest for. The CAS node, content identifier, and node admission code
  labels left pending in the context document were filled at this
  ratification.
- **M3 ratification (2026-08-27, additive under `effects-model@0.1.0`):**
  the operator ratified the seven replay statement-and-sentence pairs —
  RPL-002 (TRACE-EXCLUDES: replay hermeticity as an empty live-delegation
  projection), RPL-003 (EXACT-STEP over the `MatchesAt` hypothesis),
  RPL-004 (FAIL-CLOSED over the same hypothesis, so the two partition the
  invoke step with no third behavior; rejection also aborts the session
  structurally — terminal-for-the-attempt is state, not prose), RPL-005
  (FAIL-CLOSED over completion, the carried terminal-so-far exhibited by a
  full output equation), SES-001 (TRACE-EXCLUDES with the status as the
  guarded mode — an aborted session's step emits nothing at all; the
  transport-seam half stays M4 TypeScript evidence), SES-002 (WF-PRESERVE
  with the trivial hypothesis — totality preserves well-formedness on
  every input; minted plan-first as a new section-7 row at the M3 slice),
  and CMP-002 (DISTINCTNESS with content as the entire input — a
  byte-identical invocation and outcome still keeps occurrences distinct;
  position is the occurrence identity). Version ruling: the seven replay
  families land additively under the unchanged `effects-model@0.1.0` — no
  pre-existing statement changed and the CAS families regenerate
  byte-identical, so rule 2's ratchet is satisfied without a bump; bumps
  stay reserved for semantics-affecting model changes (a store-side
  acyclicity clause, if ever adopted, is the first genuine 0.2.0).
  Ratification fired on the new statements, not on a version transition.
  Carrier-discharge ruling: RPL-001 is discharged by carrier construction
  — the agreement theorem `step_iff_reduce` plus reducer determinism —
  recorded in the generator's declared discharge list and rendered as
  `discharged`, which the transition check holds green; the registry route
  was rejected so that "instantiated" keeps meaning proved-with-kit.
  Taxonomy-fidelity ruling: the `violated` session outcome and the
  `outcomeInadmissible` mismatch category stand as ratified caller-visible
  taxonomy with no emitting reducer rule in this slice; their emitting
  rules arrive with their milestones through Pass A. The replay-term code
  labels left pending in the context document were filled at this
  ratification.
- **Bridge-evidence ruling (2026-08-27, at the accepted M3 delivery
  review):** the operator accepted the proposed flip mechanism for bridge
  rows — a declared evidence list in the generator naming the accepted
  differential suite, entered only at a delivery review, mirroring the
  carrier-discharge mechanic. BRG-001 flips to `evidenced — differential
  suite` on the strength of the accepted M3 delivery: the line-by-line
  correspondence review of the mirrored reducer passed rule-for-rule and
  all seven replay families are consumed structurally. `evidenced` is
  G4-labeled sampled agreement, never proof; the transition check holds
  it green. The tsSide rows (CTX-*) are not covered by this ruling and
  get their own mechanism decision when M4 delivers them.
- **CMP-001 ratification (2026-08-27, no manifest surface):** the
  operator ratified the CMP-001 statement-and-sentence pair —
  HOMOMORPHISM over the reified sequential program, interpreted through
  the reducer into Lean's built-in `EStateM` (its `Result` is the
  family's ratified shape: ok-with-state or error-with-state), with the
  bind law stated as a monad morphism so a nested program continues from
  exactly the state its prefix reached. Rulings carried: the fail
  channel is the three-case interpretation halt — the program's own
  typed failure, the session's typed rejection, and the absorbed
  totality case — mirroring the session boundary and never widening a
  wrapped method's error union (`replay_invoke_result` pins the
  reachable leaf results); the kit runs both branches through a leaf
  over a failure-recording fixture (the positive program recovers, the
  failing one re-raises); CMP-001 carries no manifest family on
  principle — reified programs hold meta-level continuations and
  nothing serializes a continuation — so its declared mutant is killed
  on the two-leaf witness run, the stated direction-1 analogue for a
  vectorless family; and the briefing consume list derives from the
  actual manifest surface, so an unvectored instantiated family never
  renders as consumable. Two context entries were minted at this
  ratification: reified program and interpretation halt.
- **M4 Pass A (2026-08-27):** the operator ratified the eight-item
  docket as recommended. (1) The `Violated` session-outcome wire shape
  flattens toward the Lean carrier and the manifest (`service` at top
  level) — a freeze-postdating TypeScript correction landing in the M4
  packet, before any tripwire vector exists. (2) tsSide rows flip
  through the same declared-evidence-list mechanic as bridge rows,
  rendered `evidenced — TypeScript evidence`, built with its first
  consumer at the M4 delivery review. (3) Direction-2 TypeScript
  mutants are an M4 deliverable: one mutated reducer per replay
  falsification case under `test/mutants/`, meanings mirrored verbatim
  from the Lean mutant headers, with a task asserting the suite goes
  red under each. (4) The M2 kit-store rider is closed by finding:
  manifest rows carry store bindings as data and the suite instantiates
  a store per fixture, so application-level contexts are realized by
  construction — no model change. (5) Vector growth lands as a declared
  additive batch on the CAS families under the unchanged version:
  nontrivial-payload and multi-reference round trips, a wrong-kind
  reference beside a resolving one, and a two-resolving-references
  admission. (6) The error review adds `ContentNotFound` only — a
  TypeScript-owned load-miss clause; the model's read stays an Option —
  while the collision and scheme-version clauses stay deferred, the
  latter requiring a plan section-7 entry first. (7) Family digests
  stay deferred, re-scoped as a dedicated slice: the cost driver is a
  Lean-side SHA-256 or a two-stage generation pipeline, neither on M4's
  critical path. (8) M4 history persistence rides the in-memory store
  with internal history/witness Schemas carrying no canonicality claim
  and no digest-preimage authority; the canonical history-node codec is
  a future declared plan section-7 entry.
- **M4 acceptance (2026-08-27):** the M4 implementation delivery was
  reviewed first-hand and accepted: every session transition drives the
  mirrored reducer (invoke, recorded append, append-failure abort,
  completion), the transport seam is four defect classes with the
  session boundary converting them to the tagged session outcome, both
  Pass A riders landed (flat `Violated`; `ContentNotFound` with
  admission's `DanglingReference` untouched and put-collision still
  `StoreFailure`), the kit realizes the ratified live-role/record/replay
  shape with the runtime brand and typed double-wrap rejection, replay
  construction closes over nothing live, tripwires surface flat
  `Violated` outcomes with both permanent negative fixtures, and the
  seven direction-2 mutants carry the Lean meanings verbatim with the
  suite asserted red under each. CTX-001 and CTX-002 flip through the
  tsSide declared-evidence list, built at this review per the Pass A
  ruling. Observations recorded, no action owed: the
  operation-description schema bound narrowed to service-free codecs
  (freeze-postdating, in service of caller-facing type identity);
  history loading carries an operational cycle guard — a load-side
  fail-closed check, not a store-admission semantics change, so the
  parked acyclicity question is untouched; interpreter-invariant
  breaches map to `StoreFailure` (error-review backlog); the stored
  witness carries a consumed count and history root rather than the
  entry list — a representation for the witness re-freeze review to
  weigh. The first `OutcomeInadmissible` emission arrived with this
  milestone at outcome decode, as the M3 taxonomy-fidelity ruling
  anticipated.
- **M5 acceptance (2026-08-27):** the compositional-chaining delivery
  was reviewed first-hand and accepted — one test-side file, nothing
  else touched. Two independently described leaf services compose under
  one transparent orchestration service through ordinary Layer
  composition (the orchestration is never described or wrapped; its
  control code re-executes while leaves substitute), record uses the
  by-value kit overload and replay the bare kit, and the same caller
  program runs under both graphs. All four ratified fixtures hold
  record-then-replay: repeated identical leaves stay distinct
  occurrences consumed in order; a nested typed failure re-injects
  through the failure channel; recovery control flow re-executes over
  substituted leaves with record and replay agreeing on outcome and
  trace; and a mid-orchestration divergence rejects at the frozen
  cursor with no live fallback. The exit holds: replayed orchestrations
  consume the full nested history with zero live invocations on both
  fakes. Observation recorded, no action owed: Effect's span tracing
  consults the default Clock, so a traced method inside replayed
  orchestration trips the ambient tripwire — the fixtures keep
  orchestration control methods untraced, the reject-first answer; a
  deterministic tracing clock in the replay environment is a future
  D7-revisit candidate if a fixture ever demands spans.
- **Ergonomics review ratification (2026-08-27):** the operator ratified
  the eight-item review docket as recommended. Hardening-packet rulings:
  operation descriptions become statically checked —
  `ServiceDescriptions` maps each method through per-method inference so
  a mispaired schema fails to compile, with a `describeService` helper
  deriving ids under an explicit revision; kit identity becomes
  deterministic — the live-role key derives from the service key and
  `replayable` memoizes the core kit per service tag; the session
  runtime moves onto `ReplayShape.run` at a declared freeze-postdating
  re-freeze, retiring the runtime WeakMap and making `session` ordinary
  (wrapped-method types untouched); interpreter invariant breaches die
  as defects — `StoreFailure` is reserved for genuine storage and
  encoding failures; and the unary-request constraint, the tracing
  trap, and the birth-frozen surface documents get truthful statements.
  Witness re-freeze (the held-open M3 exit): the count-plus-root stored
  representation is ratified as selected — consumed entries stay
  recoverable through the root chain — and the context entry's code
  label gains its TypeScript half. Descriptor Pass A pre-rulings:
  acyclicity is a per-projection obligation only — store admission is
  untouched, so no clause growth and no version bump (the M4 load guard
  is the operational realization); and the leaf-first descriptor design
  (`Cas.value` over a project-owned canonical JSON of the Encoded form,
  typed roots that never bypass runtime kind validation, projection
  decode failures outside `CasError`, eager `Cas.service` hydration
  with `layerAs` targeting the kit's live role) is adopted as the
  working draft the descriptor grill amends rather than reopens. New
  descriptor obligations enter plan section 7 first; a family misfit
  stops for a WGR-2 catalog event.
- **Hardening acceptance (2026-08-27):** the ergonomics-hardening
  delivery was reviewed first-hand and accepted: statically checked
  descriptions with the explicit-revision `describeService` helper and
  a compile-time negative fixture; deterministic live-role keys with
  the core kit memoized per service tag (tag-key identity verified
  against the pin in a fixture); session execution on
  `ReplayShape.run` with the runtime WeakMap and its failure path
  deleted; interpreter invariant breaches kept on the defect channel
  end to end; and the truthful surface documents, including the
  claim-surface separation restated in the README. Both
  freeze-postdating corrections (the widened shape, the defect
  posture) landed as ratified. Observations recorded, no action owed:
  a repeated `replayable` call returns the memoized kit and silently
  ignores a differing descriptions argument — per-service contract
  identity makes that a consumer error, and a stricter check can ride
  a later slice; and record-mode `session` returns the session outcome
  but not the recorded history root, which consumers today must
  recover from their own address boundary — a named API gap for a
  future ruling (the natural home is the descriptor slice or a widened
  record-mode result).
- **Remote Pass A (2026-08-27):** the operator ratified the nine-item
  docket as recommended, over the landed remote-CAS research pair.
  (1) The exchange alphabet and the sans-io client decision machine
  shape are minted — events and commands are data, absence and
  corruption never share a member, and HTTP/TLS/wall-clock/server
  internals stay outside the model. (2) The schedule-vector manifest
  shape is ratified: rows carry operations plus an ordered scripted
  server-event schedule (including declared interruption points), with
  expectations computed by executing the model — additive under the
  unchanged declared model version, and acknowledged as novel ground.
  (3) Sixteen obligations enter plan section 7 as the RMT family at
  the R1–R4 milestones, two tsSide and one standing review among them.
  (4) The WGR-2 catalog event lands with one amendment called and
  accepted: the two anticipated new shapes share a quantifier
  structure, so ONE family — AGREEMENT,
  `∀ x, hyp x → observe (f x) = observe (g x)` — is added, with
  RMT-015 and RMT-016 as its first instances; sentence template "On
  ⟨domain⟩, ⟨computation A⟩ and ⟨computation B⟩ agree at
  ⟨observation⟩ — ⟨domain gloss⟩"; kit = a positive agreement witness
  plus a mutated computation that satisfies the hypothesis yet
  observably diverges. (5) Evidence lanes use existing flip mechanics
  only — instances, the tsSide evidence list, and declared-evidence
  entries for the property and live lanes. (6) The mutant floor is
  one declared mutant per falsification case in both directions, with
  wrong-bytes-for-address threaded as the canonical fault. (7) The R
  lane ratchets before M6 — the rank map now orders R1 through R6
  between E3 and M6. (8) Provenance: Part-I byte receipts are minted
  at R1's landing, the first gated consumer, with the preserved bytes;
  Parts II–IV stay pending-pin. (9) Operator rider during the
  landing: the remote model prefers Lean's standard-library carriers —
  `Std.HashMap`, `Std.HashSet`, and kin with their lemma APIs — over
  bespoke map carriers, the same built-ins-first posture as the
  EStateM ruling; a carrier that fights a proof falls back only with
  the divergence documented. R1 opens as conformance-lane model work.
- **R1 ratification point: REJECTED with named corrections
  (2026-08-27).** The operator's review of the landed R1 candidate
  (`42257bba`) returned corrections to the conformance lane per
  section 11; the accurate status of that commit is a landed R1
  candidate pending acceptance, and its manifests, though committed
  under the conformance-leads ruling, are not accepted conformance
  evidence until the corrected slice ratifies. Named corrections:
  (1) RMT-001's law must exclude the caller path as well as the cache
  — no delivered result without admission — and the vector
  instantiation must verify through the real CAS discipline (canonical
  node bytes and addresses under a declared toy digest), not a toy
  length oracle; (2) RMT-002's sentence overclaims — the model
  supports "no verification or admission decision after an over-budget
  declaration", the body-consumption half is a TypeScript shell
  obligation at R2 with a streaming byte counter, and the key-count
  budget is R3's; (3) RMT-003 must be temporally terminal — the
  rejection memory becomes a set of key-content pairs with a
  monotonicity theorem and a trace-level corollary, closing the
  overwrite hole; (4) the machine gains client-assigned operation
  identifiers and an in-flight map before any shared Effect service
  exists — busy-serialization of unrelated operations is rejected;
  (5) the schedule-vector shape returns to separate operations and
  schedule fields with per-entry correlation to operation identifiers
  and complete schedule accounting, and the event encoder becomes
  total (batch results and capability limits fully encoded); these
  vector corrections land inside the open ratification cycle, nothing
  having consumed the candidate vectors; (6) AGREEMENT is regrilled
  before any instance: the family generalizes to a relational form
  (two observations and an explicit relation, equality as the
  diagonal) so remote-load refinement and trace-inclusive cache
  observation are both expressible; (7) the owed Part-I provenance
  receipts are minted; (8) the R2 architecture records the deep seam —
  CasStore, verified semantic adapter, remote transport, HttpClient —
  with the raw transport never a CasStore, closure as a named backend
  capability, retries and redirects decided by the semantic core never
  the HTTP shell, and the typed remote error surface replacing the
  catch-all store failure.
- **R1 correction landing (2026-08-27):** the conformance lane landed
  the corrected slice against every named correction. The machine now
  carries client-assigned operation identifiers with an in-flight map
  — unrelated operations proceed concurrently, wire events correlate
  per operation, and commands and decisions are identifier-tagged;
  the caching law covers both halves of RMT-001 (`returned` mirrors
  delivery, and neither cache nor return is reachable without
  entitlement); RMT-002 gains the exclusion theorem — no verification,
  cache, or return decision after an over-budget declaration — with
  the sentence restated to the model's altitude, the shell half
  recorded as R2 evidence in the plan row, and the key-count budget
  deferred to R3; RMT-003 is temporal — the rejection memory is a set
  of key-content pairs, monotonicity is a theorem, and the whole-run
  corollary composes them; the schedule-vector shape carries separate
  identifier-tagged operations, correlated schedule entries, and an
  explicit interleaving with complete accounting by construction; the
  event encoder is total; vector keys are 32-byte addresses computed
  by a declared toy digest over canonical admitted-node encodings from
  the ratified codec, the oracle named in every family document; the
  AGREEMENT family is generalized to the relational form (two
  observations and an explicit relation, equality as the diagonal)
  with no instances yet; and the Part-I byte receipts are minted at
  `.reference/provenance/receipts/remote-cas-wire-sweep-sources.json`.
  Documented divergence per the standard-carrier rider: the
  monotonicity theorem, the temporal corollary, and the three instance
  kits draw `Classical.choice` through the standard library's
  container lemmas — the per-step laws stay `propext`/`Quot.sound` —
  and the constructive fallback (a list-backed rejection memory) is on
  the table if the operator prefers axiom purity over the ratified
  carrier posture.
- **R1 acceptance (2026-08-27):** the operator ratified the corrected
  slice as recommended. The three restated pairs stand; the two
  amendments stand — `integrityMismatch` joins the alphabet, and the
  split operations/schedule/sequence form is THE schedule-vector
  shape; the in-cycle vector correction reading is affirmed; and the
  standard-library carriers are KEPT with the `Classical.choice`
  divergence standing documented ("keep std"). Rulings landing with
  the acceptance, from the transport-standards survey
  (`research/remote-transport-standards-and-lean-models.md`, receipt
  minted) and the operator's streaming direction: (a) weak trace
  refinement is the R-lane's conformance shape — real protocol
  transcript, normalized events, the remote machine, CAS admission —
  with PolyFun noted as the reusable weak-simulation machinery and
  `Std.Http`/lean-grpc as harness substrates; (b) HTTP and gRPC are
  the primary CAS data planes; SSE and WebSocket are advisory
  notification/progress channels unless acknowledgement,
  deduplication, replay, and resumption are defined above them;
  (c) the standards bind the R4 retry obligations — HTTP retries
  require application idempotency or evidence the original request
  was not applied (RFC 9110 §9.2.2), gRPC success is final-trailer
  gated with an explicit commitment boundary, and the machine's next
  additions are `AttemptId`, explicit `knownUnprocessed |
  possiblyProcessed` evidence, and a protocol-completion witness
  carrying byte counts and terminal framing, entering with their R
  slices through plan section 7; (d) LeanServer is ratified as a
  first-class differential conformance PEER — never a standards
  oracle — admitted in the tool register, bound through an abstract
  peer interface so conformance suites stay isolated, its audited
  gaps named detection targets; (e) the streaming architecture is
  ratified as the four-service separation — `CasStore` (whole
  admitted nodes, backend-independent), `CasTransfer` (streamed
  upload/download mechanics), `CasEvents` (notifications and
  progress), `RemoteCasTransport` (raw untrusted protocol streams,
  adapter-internal) — under the ruled laws: `load` returns admitted
  nodes never partial streams; raw chunks stay untrusted inside the
  transport; a public download stream emits early only when each
  chunk is independently content-addressed or Merkle-proven,
  otherwise whole-object verification precedes any trusted byte
  (scoped temporary spool permitted); `putStream` checks the address
  incrementally and succeeds only after complete consumption and
  remote commitment; upload retry requires a restartable source —
  a one-shot stream is never transparently retried; notification
  delivery never constitutes admission; `Scope` owns connections,
  bodies, spools, subscriptions, and cancellation, and backpressure
  never substitutes for explicit encoded, decoded, decompressed, and
  queued-byte limits; the library enforces user-chosen policy bounds,
  prevents partial admission, closes scoped resources, and redacts
  errors. Five streaming obligation candidates are named for their R
  slices: fragmentation invariance, terminal completion before
  admission, interruption exclusion, budget enforcement, and
  per-operation stream isolation. The remote context labels fill at
  this acceptance, and three entries are minted for the streaming
  planes.
- **Layer-design ratification and the R2 conformance half
  (2026-08-27):** the operator ratified the layer-semantics review's
  eight-item decision docket as recommended
  (`research/effect4-layer-semantics-remote-service-design.md`, D1–D8):
  one `layerRemote` provides `CasStore` and `CasTransfer` from one
  shared adapter build with `CasEvents` a separate layer and the
  transport never a service key; one additive `CasError` member wraps
  the typed remote error at the R2 interface re-freeze; explicit
  Schema-validated remote configuration carries the four ruled byte
  budgets, authority mode, and redacted credentials — no ambient
  reference carries semantic policy; upload restartability is a tagged
  source (`replayable`/`oneShot`) with the address recheck on every
  attempt; downloads present one uniform verified-bytes stream in a
  caller scope with early emission an adapter capability, never API
  shape; the completion witness rides the internal transport channel's
  typed terminal; concurrency is per-operation child scopes over
  machine state keyed by operation identifier; and the differential
  lane binds an abstract conformance-peer interface. Two operator
  riders land with the ratification: **R2 assumes real transport** —
  the packet stands up the real HTTP realization of the seam and real
  TypeScript test harnesses now, not a fake-only baseline; and
  **LeanServer is ADOPTED for real server semantics**
  (`AfonsoBitoque/LeanServer`) — a standing adoption to plan for
  absolutely, landing at its own slice rather than necessarily this
  or the next one, always behind the abstract peer interface and
  never as a standards oracle. The R2 conformance half landed with
  the ratification: the machine gains the dedup amendment (an upload
  naming an already-admitted key with verifying content completes as
  success with zero wire commands and only the verification decision —
  placed inside the verified arm so the ratified entitlement guard is
  untouched), every R1 statement holds verbatim over the amended step,
  and the three R1 families regenerate byte-identical, so the change
  is additive at the unchanged declared model version. `RMT-004`
  lands as the EXACT-STEP instance over the command-accumulating
  state; `RMT-015` lands as the first genuinely relational AGREEMENT
  instance — machine-delivered bytes against the logical store's
  node, related by exact canonical encoding, on leaf admitted nodes
  within the byte budget. Two schedule families emit additively, two
  declared mutants join (thirteen killed), and the ledger transition
  is two newly green, legal.
- **Conformance-harness ratification (2026-08-27):** the operator
  ratified the vitest-harness design docket
  (`research/effect-vitest-conformance-harness.md`, V1–V8) with two
  riders. First, **upstream semantics lead**: the harness integrates
  with the existing vitest and Effect testing APIs at their own
  idioms — `layer()` blocks as the lane selector, `it.effect` and
  `it.effect.each` as the testers, `it.prop` for properties, the
  library's own `expect`/`assert` with the Equal-aware testers, and
  Schema decoding for loading. No custom describe or it wrappers and
  no `makeMethods` runner: harness surface is plain data and Effect
  functions called inside ordinary tests, so a reader who knows
  @effect/vitest reads the suites unaided (the note's custom-runner
  sugar is DEMOTED to not-planned). Second, **dogfood on the current
  slice**: V6's after-R2 sequencing is amended — the test-tree
  harness lands inside R2 itself as a packet rider, with the remote
  families consumed through it and the existing replay fixture
  module delegating to it compatibly so the committed green suites
  stay untouched; the shipped `/conformance` subpath still waits for
  the M6 packaging review. The rider is written to absorb the
  implementation lane's in-flight structures, never to restart them,
  and shape conflicts come back as questions per the workflow.
- **R2 pre-acceptance audit and correction ratification
  (2026-08-27):** the implementation lane delivered the R2 baseline
  and the operator directed a concerted pre-acceptance review —
  alignment with the Effect HTTP semantics, no reimplementation of
  what composes from built-ins, corrections landed before the shape
  hardens. Four parallel read-only audits ran (built-in composition;
  ratified-shape rule-by-rule; mirror and vector correspondence;
  idiom and resource safety) plus a worktree agent building the
  operator-directed seeded production sync-load fixtures (landed:
  graph generators, sync planners, peer preload, seven profiles, six
  end-to-end tests; every module labeled sampled evidence, never
  conformance vectors). Audit verdict: architecturally faithful —
  the ratified-shape table returned twenty of twenty-one rules met
  with the mirror verified rule-for-rule twice independently, the
  client path composes the pinned HTTP modules end to end, and the
  apparent hand-rolls (budget counters, the witness pull loop) were
  verified necessary at the pin. The operator ratified the
  consolidated correction docket as recommended. Blocker tier:
  socket-cleanup assertions made real (in-scope, plus a
  caller-interrupt test); interruption clears machine in-flight
  state (the interruption-exclusion shell half); the adapter owns
  manual-redirect semantics so production wiring cannot silently
  auto-follow. Major tier: budget errors report observed quantities
  honestly (tests re-pinned); the queued budget redefined as
  buffered-bytes-awaiting-admission so rechunking is invariant;
  oversize uploads flow through the machine step so adapter and
  mirror transcripts agree; transport failure classification
  consumes the typed reason taxonomy (pre-send failures are
  known-unprocessed), defects never launder into wire evidence, sent
  bytes report transmission; the differential boundary grows to a
  shared scenario set covering uploads, dedup, and rejections; the
  ratified harness rider is absorbed (closed strict envelope decode,
  the step service tag with layer-selected lanes, delegating replay
  fixtures, remote direction-2 mutants); the missing named span and
  Schema-decoded header parsing land. A minor batch follows the
  audit lists. Scope ruling: the fixtures-discovered cold
  root-first-pull gap (fetched parents resolve references against
  the local mirror) is DOCUMENTED as a named R2 limitation and
  DEFERRED to R3, whose closure slice gains discovery-order pull
  explicitly; the fixtures' pull planner already models both orders.
  Acceptance review remains open until the correction delivery.
- **Merkle design ratification (2026-08-27):** the operator ratified
  the Merkle conformance and proof-infrastructure design's nine-item
  docket as recommended
  (`research/merkle-conformance-proof-infrastructure.md`, K1–K9) and
  directed the MRK-1 slice — resolving K7's sequencing question as
  MRK-1 before R3. Binding decisions: the first slice is the chunk
  tree, inclusion proofs, and the verified-streaming decoder
  (consistency proofs second); the model altitude is an abstract
  address function over STRUCTURAL pre-images — domain separation
  and position binding as constructor identity and an index field,
  byte prefixes deferred to the codec layer with exactness proofs;
  the collision posture is constructive witness disjuncts with no
  collision-resistance axiom and per-obligation Level-1 hypotheses
  only where needed; the decoder is a sans-io machine with temporal
  trace laws; existing schema families carry the instances, and a
  new family may be minted only through a named WGR-2 stop
  condition; vectors are toy-digest, model-executed, with hostile
  mutations and malleability-acceptance cases; the mechanized prior
  art is utilized restate-and-reprove per the design's source
  verdicts (VCVio's binding kernel and addressed position binding as
  the primary Lean-shaped source, LambdaAuth's disjunct discipline
  including its keeps-consuming correction, the ADS-functor merge
  algebra, the Agda consistency template, the Dafny incremental-root
  skeleton, and veri-auth's statement architecture); and the
  prover/ideal/verifier triad is adopted as the statement
  architecture, with every future proof-stream optimization a
  verified refinement re-proving both security and correctness
  halves. Ten MRK obligations enter plan section 7 with this record;
  the greenfield standing (no prover has mechanized bao-style
  streaming or the RFC 9162 verification algorithms) is recorded
  with the splash discipline unchanged — novelty is claimed only
  after the verifier passes.
- **MRK-1 ratification (2026-08-27):** the operator ratified the
  landed MRK-1 slice as recommended. The five statement pairs stand —
  chunking as a lossless declared partition with its checked inverse
  (CODEC); the decoder's emit-only-verified gate with the run-level
  soundness carrying the collision witness in the consumed prefix and
  the decoder under no obligation to detect it (TRACE-EXCLUDES); the
  final-chunk length rule (TRACE-EXCLUDES); slice–whole agreement
  with the universal theorem as the law (relational AGREEMENT); and
  the inclusion-verifier reflection with completeness and binding as
  named theorems (AGREEMENT). Three carrier discharges stand:
  complete-decode root determination (notably collision-free — the
  decoder recomputes every address, so the theorem needs no
  disjunct), run composition over concatenation, and position
  binding composed from per-index binding and completeness. Two
  design findings are recorded with the ratification: the MRK-010
  plan row was corrected IN CYCLE before the inventory mirrored it —
  the original "never verifies at another index" phrasing is
  falsified by a legitimately duplicated chunk, and the true law is
  binding per index with the anti-replay corollary — and
  side-carrying proof formats were found to admit an injective-hash
  counterexample, so the verifier derives combination sides from the
  index and count (RFC 9162's own design, now with its reason
  proved). Axioms: propext and quotient soundness throughout,
  including the constructive collision walk, except the slice–whole
  agreement theorem drawing classical choice through one list lemma
  — the documented keep-std divergence class. Five vector families
  emit additively at the unchanged model version with hostile rows
  (tampered chunk, forged parent, truncation exposing no length, a
  length tamper refuted by tree geometry); five declared mutants
  join, eighteen killed; the ledger holds fifty-one rows with eight
  newly green, legal. Four context entries are minted — chunk tree,
  inclusion opening, verified-streaming decoder,
  encoding-malleability boundary — and the R2-delivered transfer and
  transport code labels fill. MRK-007 waits for the second Merkle
  slice; MRK-009 stands as review.
- **R2 correction acceptance (2026-08-27):** the correction delivery
  was reviewed first-hand — the full diff read against the ratified
  docket item by item, both gates run personally (ninety TypeScript
  tests across fourteen files; the Lean gate untouched and green;
  zero ledger transitions, as expected — no remote row is
  TypeScript-primary, so the delivered halves complete evidence
  columns of rows already green) — and ACCEPTED. Blockers: cleanup
  evidence is real (socket counts asserted inside the live peer
  scope at eight sites, and a gated peer holds a response mid-body
  while a caller fiber is interrupted — socket closed, in-flight
  cleared, nothing cached, all observed with the peer alive);
  interruption clears machine state on every drive path and on the
  invalid-acknowledgement arm, each with a test; the transport
  itself supplies manual-redirect semantics around every request, so
  plain fetch wiring keeps redirects observable machine denials — a
  test proves it with the plain client. Majors: budget errors report
  actually-observed quantities; the queued budget is a buffered
  counter with a one-chunk-versus-many equivalence fixture and the
  README's honest four-stage binding table (the decompressed stage
  documented as shared in this profile); oversize uploads flow
  through the machine step so the transcripts agree; transport
  failures classify by the typed reason (pre-send failures
  known-unprocessed, reset/timeout/cancelled reachable, defects no
  longer laundered, prepared-byte witness documented); the
  differential table holds seven named scenarios; headers decode
  through Schema with exact media-type comparison and shared status
  cases; the missing span landed. The harness rider is absorbed to
  its ratified letter: closed strict envelopes with the oracle TEXT
  pinned as a literal, a non-empty rows floor, named kill witnesses,
  the step-service tag with layer-selected lanes, five
  direction-2 TypeScript mutants whose meanings are byte-verbatim
  the Lean mutant sentences, the replay fixture module delegating
  under its unchanged signature, a self-test labeled
  never-evidence, and the mirrored guards' first consumers asserting
  law shadows over the manifest rows. The cold-pull ruling landed as
  directed, which required widening the sanctioned `RemoteFailure`
  cause to admit `DanglingReference` — a second touch of the frozen
  file reviewed and accepted as the ruling's own carrier. Recorded
  observations: the exact media-type comparison is now
  case-sensitive (profile-owned; the R4 header-discipline pass may
  revisit); manual-redirect ownership rides the fetch client's
  request-options reference, so a hypothetical non-fetch client that
  follows redirects internally would still bypass — the transport
  matrix slice owns that; the budget error's operation identifier
  became optional for the one non-operation construction site; the
  differential lanes share the mirror's step function, so full
  implementation independence waits on the Lean executable lane.
- **R1 ratification (2026-08-27):** the operator ratified the
  scope-and-ambient analysis's first recommendation: replay
  construction provides `TracerTimingEnabled = false` alongside the
  tripwire Clock and Random. Span timing is thereby reclassified from
  ambient use to disabled instrumentation — spans still exist and
  propagate, the runtime never consults the Clock for them (verified
  at the pin: the timing reads are guarded by exactly that
  reference), and genuinely semantic Clock use still trips the wire
  as ratified. This supersedes the `fnUntraced` caveat once the
  implementation-lane rider lands; the reject-first boundary is
  otherwise unchanged, and the describe-a-Time-service recipe remains
  the principled route to deterministic time under replay.
- **Descriptor Pass A (2026-08-27):** the operator ratified the
  eight-item docket as recommended. Six obligations enter plan
  section 7 and the inventory as the PRJ family — descriptor identity
  checked at read, the descriptor round trip, the typed projection
  rejection, hydration matching by-value construction, non-recursive
  single-wrapped hydrated record construction, and the standing
  equal-roots review rule — all tsSide at the new E2/E3 milestones or
  review; no new schema family, so no WGR-2 event, and PRJ-002's Lean
  CODEC lift stays a deferred declared disposition change. One
  pre-ruling amendment was called and accepted: the projection error
  taxonomy covers both codec directions (`ProjectionCodecFailure`
  with an encode/decode direction), not decode alone. Four context
  entries minted: value descriptor, typed root, projection codec
  failure, hydrated service layer. The declared canonical JSON
  encoding of the Schema's Encoded form is documented and versioned
  by descriptor kind tag and revision, with no cross-claim against
  the Lean printer. The record-root gap closes through the widened
  session result — outcome plus witness id plus optional history
  root — the third freeze-postdating widening, with the session
  outcome taxonomy itself untouched. The ergonomics lane lands in
  plan section 9 as E2–E3 sequenced before M6, and the briefing rank
  map encodes that order. One implementation packet carries the R1
  and session-result riders first, then E2, then E3; PRJ rows flip
  through the tsSide evidence list at the delivery review.
- **E2/E3 acceptance (2026-08-27):** the descriptor-slice delivery was
  reviewed first-hand and accepted. Both riders landed as ratified:
  replay construction provides `TracerTimingEnabled = false` — proved
  live by flipping an M5 orchestration method back to a traced
  `Effect.fn` that now replays clean while the semantic-Clock fixtures
  still surface `Violated` — and sessions return the widened result
  (outcome, witness id, optional history root), with record mode
  reporting a root only when the attempt appended an occurrence.
  `Cas.value` enforces the declared canonical JSON inside the exact
  revision/value envelope, on write and on read — the decoder
  re-canonicalizes and byte-compares, a closed-input read mirroring
  the codec discipline — with reserved kind tags guarded and leaf-only
  nodes enforced; `ProjectionCodecFailure` carries both directions and
  is never folded into the store's failure clause. `Cas.service`
  hydrates eagerly with construction errors on the layer channel and
  `layerAs` feeding the kit's internal live role, wrapped-live-role
  rejection intact. PRJ-001 through PRJ-005 flip through the tsSide
  evidence list; PRJ-003's coverage exceeds the floor (typed decode
  failure, dangling-root pass-through, non-finite encode, noncanonical
  bytes). Observation recorded, no action owed: a wrong-kind root
  surfaces as the store's `UnknownKind` clause rather than a
  projection-side clause — a deliberate reuse worth revisiting if the
  M6 documentation finds it blurs the family boundary.
- **Codec-discipline and structure ratification (2026-08-27):** the
  operator ratified the Schema assessment's recommendations — S1, the
  sanctioned JSON-safe constructor vocabulary for CAS value fields
  (bytes as hex, big integers as decimal strings, instants as epoch
  milliseconds, the Option encodings with the nullable-inner caveat),
  documented as the README's value-schema discipline; S2, custom
  codecs enter through `decodeTo`/`encodeTo` under three rules —
  deterministic total encode, Encoded lands in the JSON subset, and a
  per-descriptor put-get-put same-root fixture (a normalizing decode
  silently splits one logical value across two roots), with set-like
  data encoded as explicitly sorted arrays; S3, the static
  `Schema.Json` bound on the value descriptor's Encoded form, adopted
  behind an assignability verification and dropped without loss if it
  fights hand-written interface Encoded types; S4 stays noted-only —
  and directed a proper Effect-ecosystem file structure in place of
  the flat single-depth `src/`. Ratified layout: `cas/` and `replay/`
  plane directories mirroring the Lean tree's own structure, an
  `internal/` subtree for the non-public storage and live-binding
  carriers (the ecosystem's internal convention), top-level namespace
  facades and the public barrel. The runtime session/reducer split
  mirrors the Lean `Session`/`Reducer` split, so the correspondence
  review aligns file by file. The restructure changes no public type
  and no behavior — the compiler and the full suite are the proof —
  and the context document's provisional TypeScript code labels update
  at the acceptance review.
- **Codec-discipline and restructure acceptance (2026-08-27):** the
  delivery was reviewed first-hand and accepted. The tree matches the
  ratified layout exactly — git tracked the moves as renames, the
  session carriers and pure reducer split out of the runtime with
  bodies, helper names, and branch order unchanged (verified against
  the reviewed mirror), and the barrel keeps every public name while
  exposing `Cas` as a namespace export. The README carries the
  value-schema discipline and the module map; the demonstration
  custom-codec fixture (hex plus `decodeTo`) holds the put-get-put
  same-root assertion. The S3 verification succeeded, so the
  `Schema.Json` Encoded bound is RETAINED — every legal descriptor
  compiled, and the intentionally unsafe fixture that was previously
  caught only by the runtime guard is now also a compile-time
  rejection. Gates run personally: 49/49 TypeScript tests across nine
  files, Lean gate green, no ledger transition. The context document's
  TypeScript code labels moved to the new paths, and the stale
  "pending" qualifiers on shipped surfaces (operation descriptions,
  the service kit, the four descriptor entries) were filled with their
  real labels at this review.
- **R3 ratification (2026-08-27):** the operator ratified the R3
  opening docket P1–P8 as recommended — presence as planning, closure
  through the `confirmed` set with gated publish, exact order-sensitive
  batch accounting, first-class interruption, the key-count budget,
  the closed capability-document codec, the extended R3 state summary,
  and the TypeScript discovery-order pull staging area — and the
  conformance half landed in the same cycle. The machine grew the four
  R3 state components and the find-missing/publish operations with the
  R1/R2 arms untouched, so the five committed families regenerate
  byte-identical; every prior law re-proved over the extended machine.
  New named theorems: presence never admits (cache, confirmed, and
  published frozen across any batch-answering event, with the cached,
  returned, and issued-publish decisions excluded), batch misalignment
  fails the whole batch closed, no publish issues without the root and
  its declared closure confirmed (full case-bash exclusion over all
  inputs), a publish acknowledgment confirms nothing, and interruption
  admits nothing while erasing the in-flight entry. `ControlCodec`
  carries the closed capability codec with decode-of-encode identity
  on representable fields and the exactness theorem — a successful
  decode's input IS the canonical encoding of its result — whose
  contrapositive is the RMT-014 fail-closed law. Five schema
  instances (RMT-005 TRACE-EXCLUDES, RMT-006 FAIL-CLOSED, RMT-007
  TRACE-EXCLUDES over the entitlement mode, RMT-008 FAIL-CLOSED over
  interruptions, RMT-014 FAIL-CLOSED over the codec) enter the
  registry; four schedule families run under the extended renderer
  (planning, confirmed, and published sizes in the state summary) and
  the codec family carries its own declared oracle; five mutants
  (presence-admits, partial-batch, publish-unconfirmed,
  interrupt-admits, accept-truncated) are declared and killed. Design
  choices carried in the ratified letter and worth restating: batch
  accounting is exact ORDER-SENSITIVE per-key accounting — a
  reordered answer rejects, deliberately, because the request order
  is the only alignment witness the client controls; a `found`
  answer's bytes are dropped unverified rather than opportunistically
  admitted; and the interrupted-at-upload path leaves the terminal
  rejection memory untouched (interruption is not an integrity
  verdict). The R3 codex packet — the discovery-order pull staging
  area as centerpiece, the machine-mirror catch-up, the control-
  document Schema codecs, and the adapter counterparts — is owed
  next; RMT rows 005–008 and 014 flip green on the Lean side at this
  landing with their TypeScript evidence columns filling at the
  delivery review.
- **Wire contract W1–W6 and the server direction (2026-08-27):** the
  implementation lane stopped correctly at the unminted wire choices
  for the R3 adapter half and asked for the contract; the operator
  directed the target server design first, the reference server as
  the destination, publication as the goal, and verified partial
  reads as the active workstream, delegating prioritization. Under
  that delegation the cas-http/0 R3 extension landed as the normative
  `PROFILE-CAS-HTTP-0.md` (W1 resource spaces and the shared
  status→event table; W2 the canonical key-list document; W3 the
  required capabilities endpoint carrying exactly the eight-byte
  canonical document; W4 positional find-missing whose response is
  exactly N status bytes in request order, presence never carrying
  content bytes on this profile; W5 publish carrying the declared
  closure with client-side gating as the law and server verification
  optional; W6 the caller surface on the streamed-transfer service
  with the `push` composite as the developer-facing headline and
  three error-vocabulary extensions, no new error class). Two
  decision points were flagged and stand accepted with the
  delegation: the declared closure travels on the publish wire so
  any server can verify, and `push` is in F1 scope while `pull`
  waits for the staging-area slice. The profile document is now the
  normative home; the README profile section consolidates into it at
  the next acceptance review. The target design landed as
  `research/server-reference-and-verified-reads.md`: the
  four-artifact published shape (client, reference server,
  conformance kit, profile document), the blob-mode ruling question
  answered — a blob is a node graph, not a second store:
  position-bound leaves per the proved pre-image model, parents as
  ordinary two-reference nodes, the root an ordinary content
  identifier so negotiation, closure-gated publish, and pull apply
  verbatim; the chunk recipe is a PROFILE constant (a
  capability-derived chunk size would fragment content identity
  across authorities); blob mode is explicit, never a threshold —
  and the proof plane whose range-stream wire language is exactly
  the verified-streaming decoder's input alphabet, so the committed
  MRK stream vectors constrain the wire directly. Sequencing
  recorded in plan section 9: F1 (in flight) → F2 → F3 on the
  implementation lane, S1/S2 after; conformance lane next is the
  MRK-2/partial-reads docket Q1–Q5, presented for ratification (Q5,
  the key-list codec exactness closing the RMT-014 narrowing
  observation, deliberately waits for F1 acceptance so committed
  manifests do not move mid-slice). The CasBlob/CasSync service
  mints stay G0 proposals from the streaming-sync survey; W6
  deliberately extends the ratified streamed-transfer service
  instead, and any service split is an F2 docket decision.
- **MRK-2 conformance half landed (2026-08-27):** the ratified Q1–Q4
  built and landed in one cycle; Q5 waits for the F1 delivery as
  ratified. Q1: the consistency verifier is the RFC 9162 subproof
  shape over the standards split — a bare hash list consumed
  linearly down one spine with the whole walk derived from the two
  sizes, the anchored flag tracking the left-spine phase — with the
  reflection iff, completeness of the honest generator, and the
  prefix-agreement corollary, all resting on the new
  shared-split-point lemma (between the split point and the total,
  the split point is stable). Q2: the proof-document codecs land
  under the control-codec discipline with decode-of-encode identity
  and exactness; the shared big-endian field tools were extracted to
  a wire module with the capability codec re-based on them, its
  encodings unchanged. Two boundary semantics are documented rather
  than fought and carried as vector rows: the framings are
  self-delimiting, so a truncation landing on a document boundary
  reads as a DIFFERENT document whose wrong content the verifier
  rejects, and a trailing skip tag extends a stream's item list —
  transport length-delimits, verification decides. One design
  correction recorded: the research sketch had the stream's skip
  item carrying a hash; the model's skip is bare (a skipped
  subtree's address is bound by its parent, and a carried hash
  would be an unverified side channel) — the model is right and the
  sketch was amended. Q3: ranged stream-generation completeness —
  the honest extractor's stream decodes to done and emits exactly
  the owed ranged emissions, assembled on the standing generation
  and characterization lemmas — is the server-half theorem behind
  the range-stream endpoint. Q4: the blob refinement tie — the
  Merkle address function instantiated as the address of the
  canonical blob-node encoding, so a blob root IS an ordinary
  content identifier and the closure machinery applies verbatim.
  One ruling made in the build and flagged for review: the
  pre-image carrier's parent holds child ADDRESSES only, so a
  per-child expected-kind cannot be derived at that altitude — the
  materialization uses ONE declared blob tag with the leaf/parent
  separation STRUCTURAL (payload-with-index and no references
  versus empty payload and exactly two), and codec non-malleability
  turns that into byte-level separation, with the collision-transfer
  theorem keeping every Merkle collision disjunct meaningful on
  bounded pre-images. Ledger: MRK-007 flips through its AGREEMENT
  instance, MRK-011/012 enter as CODEC instances with vector
  families and killed mutants (equal-roots shortcut, pad-short
  opening, lenient tags), MRK-013/014 enter as carrier discharges;
  26 declared mutants killed; committed families regenerate
  byte-identical; three context entries minted (consistency proof,
  proof documents, blob node graph). One elaboration hazard
  recorded for the proof-engineering laws: a five-deep cons pattern
  with a catch-all arm and a four-times-duplicated arithmetic
  expression sent the functional compiler into an eight-minute
  divergence — reading the field through the shared reader with a
  match-hypothesis for the termination proof fixed compile time to
  seconds, and the dependent-match decoder construction hit a
  kernel recursion limit that the admitted-node decoder's
  bind-and-recheck shape avoids entirely.
- **Prior-art review adopted; MRK-3 and S-M ratified (2026-08-27):**
  the operator's G0 prior-art and usability review of the server
  target (Unison newly pinned with per-blob digests; the CAS wire and
  streaming sources reused through standing receipts) was reviewed
  first-hand, its claims about this estate verified against the
  landed sources, and adopted as the development priority. One
  reconciliation recorded: the review's first blocking finding — the
  range wire alphabet contradicting the decoder's input language —
  had already been caught and discharged in the MRK-2 landing hours
  earlier (parent frames mandatory, skip bare, exactness theorems,
  vectors, and a lenient-tags mutant committed); the review evaluated
  the design sketch, not the landed slice, and its tag-numbering
  variant is declined in favor of the committed vectors. Everything
  else stands and is minted: MRK-015 through MRK-019 (incremental
  fragmentation-invariant frame parsing; the adversarial
  ranged-binding theorem whose conclusion stays
  expected-bytes-or-collision until a hash assumption is declared;
  byte-range slicing as flatten-drop-take; the blob manifest
  committing recipe id, total bytes, and leaf count with unknown
  recipes failing closed; response-framer closure and
  proof-amplification budgets) and SRV-001 through SRV-006 (the
  server transition system with publication correctness — a client
  publish theorem is never a server theorem; the admission pipeline;
  three-outcome write-if-absent with same-address-different-bytes an
  integrity fault; capability truth as the five-way intersection;
  declared durability classes; compare-and-set root heads). The
  blob-representation ruling: the four-kind manifest graph with
  REFERENCED content chunks is the headline recipe — restoring
  cross-position dedup and authenticating the totals the decoder
  alone cannot — with the landed inline-leaf tie retained as the
  first frozen recipe and the collision-transfer substrate; F2 was
  gated on this ruling and is now unblocked, building `CasBlob` on
  the manifest graph only. Cheap corrections landed with this
  record: the profile documents the second capability field as the
  node-body bound renaming at `/1`; the shared-codec
  drift-impossibility claim is softened to the honest form; the
  review's hostile-fixture list joins the vector backlog; subpath
  packaging and the report, inspection, and repository surfaces fold
  into the F2, F3, and S-lane letters. The review and its receipt
  are committed with this record.
- **F1 acceptance (2026-08-27):** the delivery (two commits, roughly
  twenty-two hundred lines) was reviewed first-hand against the F1
  packet and the W1–W6 letter, and the gates run personally: one
  hundred thirteen TypeScript tests across fifteen files with both
  typechecks and the frozen install, the Lean tree and committed
  manifests untouched by the delivery, and — as at R2 — zero ledger
  transitions, since the R3 rows are Lean-primary and the delivered
  halves complete evidence columns of rows already green. ACCEPTED.
  The machine mirror extends arm by arm in correspondence order:
  the four planning-and-closure state components, exact
  request-order batch accounting by structural equality, presence
  noting that drops found bytes and admits nothing, the key-count
  budget, the entitlement-gated publish, total four-state wire
  dispatch, and the cache-entitlement guard narrowed to the
  uploading arm. The wire half follows the profile to the letter:
  capabilities at the control plane parsed by the closed eight-byte
  decoder with re-encode comparison, find-missing posting the
  canonical key-list document with 413 mapping to capacity for
  batches only, publish putting the declared closure to the root
  registry, and acknowledgments accepting 200, 201, and 204 — with
  204 handled as header-terminated per its standard and nonempty
  acknowledgment bodies refused as a typed protocol violation. The
  public surface lands the ratified letter: capabilities, missing,
  publish, and the push composite on the streamed-transfer service;
  presence as request-order subsequences documented as planning
  data; push enumerating the local closure children-first with a
  typed dangling-reference failure before any wire traffic,
  negotiating in capability-sized batches, and publishing last; the
  three error-vocabulary extensions exactly as ratified. Five
  conformance fixtures consume the R3 families through closed
  Schema envelopes with the extended state summary; five mutants
  carry the Lean meanings byte-verbatim and run red. Observations,
  no action owed: the capability probe per layer acquisition is an
  early carrier for the R4 capability-discovery row; the package
  description was updated to name the delivered scope; Q5 and the
  F3 staging-area slice remain the open R3-adjacent work.
- **MRK-3 conformance half landed; proof lane pauses for
  development (2026-08-27):** four of the five ratified items built
  and landed in one cycle, and the operator directed a pause on the
  proof lane after this set — working code takes priority. V1: the
  four-kind manifest graph — chunk data content-addressed WITHOUT
  position (cross-position dedup restored), leaves binding index and
  length over a chunk reference, the manifest committing recipe id,
  total bytes (a 64-bit wire field, added to the shared tools), and
  leaf count — with the composed address function, the root-address
  tie, node well-formedness, the two-layer collision transfer, and
  the recipe-gated closed manifest codec; chunk data and manifests
  carry their own kind tags while parents and leaves share the tree
  tag with structural separation, the constraint recorded at MRK-2
  now scoped to the tree plane. V4: the adversarial ranged binding —
  ANY accepted trace for a root and range emits exactly the
  committed ranged emissions or exhibits a computable collision —
  proved over the trace-general consumption decomposition with the
  named accepted-prefix judgment, the honest-generator half kept
  separate as ratified. V3: the incremental frame parser — front
  classification into complete frame, valid prefix, or malformed;
  greedy drain; fold-over-fragments equal to single-shot parse of
  the flattened bytes; completion agreeing exactly with the
  whole-string reader, so a truncation leaves a remainder or reads
  as a strictly different document. V5: the response framer —
  acceptance is exactly one complete decode with done first reached
  at the last item, nonempty trailing content after an accepted
  response refused (the machine's absorb-after-done stays an
  internal convenience), the linear amplification bound (an honest
  stream is at most twice the leaf count minus one), and a decidable
  anti-vacuity example. Ledger: MRK-015, MRK-016, and MRK-019
  discharge by carrier construction, MRK-018 flips through its
  CODEC instance with a vector family and a killed
  guess-unknown-recipe mutant; twenty-seven declared mutants killed.
  DEFERRED under the development directive: MRK-017 (byte-range
  slicing, V2) stays pending at MRK-3, and the Q5 key-list codec
  exactness stays open — both resume when the proof lane does. The
  conformance lane's next work is development-facing: the F2b
  CasBlob packet on the landed manifest graph, the S1 reference
  server, and the profile's proof-plane clauses promoted from
  planned to ratified as the implementation consumes them.
- **Release-gap pass: profile consolidation, blob recipe, auth and
  deadline clauses, hash docket (2026-08-27):** under the
  development directive the release-facing gaps were surveyed beyond
  the prior-art review and the owed consolidation landed: the
  profile document is now the sole wire authority (statuses
  upgraded to implemented after the F1 acceptance, the
  acknowledgment-closure and identity-content-encoding clauses
  captured, the README wire restatement reduced to a pointer), and
  the blob node-graph section freezes recipe 1 — fixed 65536-byte
  chunks, the four node shapes with tags and payloads, the
  recipe-gate rule, and the chunk-size-is-profile-constant law.
  Two ratified clauses landed under the operator's direction as
  normative-pending-implementation: AUTHENTICATION (an opaque
  bearer credential per authority, structurally redacted, scoped by
  the no-redirect rule, no challenge negotiation, server principals
  explicit with root-update authorization independent of upload)
  and DEADLINES (a default thirty-second per-request deadline
  resolving as the machine's silence event with the typed timeout
  reason — wall-clock stays in the shell, the model unchanged);
  both become riders on the next implementation packet. The
  CasScheme0 hash docket is landed as a research ruling document
  and presented for ratification — SHA-256 over the canonical node
  encoding via WebCrypto, full width, profile-pinned scheme with no
  per-address prefix, the hash as an injected Effect service with
  generated known-answer fixtures — with the publication gate
  stated plainly: the package cannot interoperate across processes
  and must not publish before the scheme is ratified and landed.
  Remaining named gaps queued: the portable-replay-history flagship
  example, the claim matrix, the axiom-profile gate, client
  concurrency documentation, memory bounds on large-graph push, and
  stable trace-span names.
- **F2a and F2b acceptance (2026-08-27):** both deliveries reviewed
  first-hand, gates run personally — one hundred forty-five
  TypeScript tests across nineteen files, and the full Lean gate
  untouched and green (two hundred forty-one jobs, sixty-six ledger
  rows, twenty-seven mutants, byte-exact manifests), confirming zero
  Lean or vector surfaces moved. ACCEPTED. F2a: six pure mirrors
  (chunk recipe, standards-split tree, derived-side inclusion,
  anchored consistency rebuild, streaming decoder, closed proof
  codecs with the committed 0-skip/1-chunk/2-parent tags), eight
  families consumed through the strict harness with pinned oracles,
  eight direction-2 mutants byte-verbatim with named kill
  witnesses. F2b: the blob surface is contract-exact against the
  profile's section 12 — tags eight, nine, and ten with the frozen
  payload layouts, recipe gating with unknown recipes failing
  closed, the sixty-five-thousand-five-hundred-thirty-six-byte
  chunker with the empty-input one-empty-chunk rule and u32/u64
  field guards, strict bigint byte ranges, subtree-pruned verified
  walks with per-leaf geometry validated against the
  manifest-derived plan, all-or-nothing get behind a
  safe-integer materialization guard, and the boundary suite run
  under both the memory lane and the reference-peer lane per the
  harness addendum, with children-first deduplicated transfer and
  publication-last ordering evidenced remotely. The push budget
  guard checks the largest encoded node against the declared
  node-body bound before any wire traffic — classified as an
  encoded-stage budget error, which is accepted as the more precise
  class than the packet's policy suggestion. Observations recorded:
  (1) a small canonicality gap — the read plan does not enforce
  that total bytes fit the leaf count under the fixed chunk size,
  so a forged but self-consistent graph whose FINAL chunk exceeds
  the recipe size reads successfully; one geometry guard in plan
  loading closes it, queued as a rider on the next slice; (2) the
  test tree already carries a Crypto service seam for digests — the
  in-flight CasScheme0 slice must reconcile its CasHash service
  with that existing seam rather than minting a parallel one,
  flagged for that delivery's review.
- **Track C batches and the blob-graph family; Lean-as-oracle
  directive (2026-08-27):** the operator directed making more use of
  the Lean code to test correctness, which folded into the batch as
  its centerpiece. Landed across three commits: the split-point
  characterization (`pow2Below_spec` — a power of two, strictly
  below the total, total at most its double — the spec the RFC-shape
  interop claim rests on), the remote-kit environment extracted so
  instance files import it and the laws directly instead of chaining
  through one another, the remote-vectors and registry import
  corrections, the dead Markdown constructors and unused projection
  typeclass deleted with the module rule rewritten to
  constructors-follow-surfaces, and the emitter consolidation — one
  `sortRows`, one `renderRows`, one `familyDocAt` with an optional
  oracle carrying the field order in exactly one place, the
  duplicate address encoder dropped — with every committed manifest
  regenerating byte-identical through all of it. The directive's
  deliverable: the BLOB-GRAPH FAMILY, emitted as `MRK-014.json` and
  attached to the MRK-014 carrier row as its implementation-side
  evidence — the model materializes the complete recipe-1 node
  graph for each chunk-list case (every chunk-data, leaf, parent,
  and manifest node with exact payload bytes, reference lists, and
  toy-digest addresses over the ratified codec's canonical
  encodings), so an implementation binds its graph construction to
  the model with the digest injected instead of self-testing node
  shapes; the identical-chunks case makes cross-position
  deduplication visible as shared addresses, and a
  position-free-leaf mutant is declared and killed —
  twenty-eight declared mutants total. Consumption lands as a rider
  on the Track B packet: bind `CasBlob`'s materialization to the
  family through the harness. Queued next under the same
  directive: a fragmentation vector family from the incremental
  parser (vectors first, driving the TypeScript framer that Track
  B's transport work will need), and the emitter-fold-to-runner tie
  deferred from the review.
- **F4 acceptance — scheme evidence and policy tests
  (2026-08-27):** the redirected scheme-slice delivery was reviewed
  first-hand in its worktree and merged; gates run personally, one
  hundred fifty-six tests across twenty-two files on main. Test
  tree only, sources untouched, exactly as re-scoped after the
  discovery that the digest seam, bearer header, and deadline had
  shipped since the R2-era slices. Landed: known-answer fixtures
  generated through the SHIPPED SHA-256 address path (eight
  vectors — five raw pre-images and three canonical node
  re-encodings agreeing with the committed manifest bytes),
  anchored on all three published FIPS 180-2 reference digests,
  with a regeneration-equality gate verified non-vacuous by
  mutation and a CRLF-normalized byte compare for the Windows
  working tree; the authentication clause's FIRST test evidence
  (credential on every request, absent header without one, 401
  terminal, structural redaction with positive controls); and the
  two uncovered deadline gates (stall-before-headers,
  inside-deadline with clean machine state). Profile amendments
  landed with this record: section 10 amended to the shipped
  letter — `operationDeadlineMs`, REQUIRED with no default, which
  is stricter than the drafted optional-with-default form — and
  section 9 names the `credentials` field. TWO DEFECTS the
  delivery surfaced, queued on Track B: the credential field was
  UNCONSTRUCTIBLE as shipped — the schema's Redacted label option
  demands an undocumented label at construction, so the ratified
  auth clause had shipped entirely unexercised (fix: export a
  credential constructor or drop the label) — and the package
  ships NO crypto layer, so scheme-0 is a caller obligation rather
  than the shipped default the hash docket requires (fix: ship the
  WebCrypto SHA-256 layer as the production default; also surface
  a wrong-width digest as a typed store failure, not a die).
  Process note recorded: the agent's worktree had branched
  thirty-five commits behind and was fast-forwarded cleanly before
  work; worktree bases should be pinned to the intended commit at
  spawn.
- **Four-lens code review consolidated; Track A landed
  (2026-08-27):** four read-only reviews (runtime correctness, test
  quality, the Lean tree, cross-surface coherence — eighty-eight
  findings) were verified on their sharpest claims first-hand and
  consolidated into four tracks; the operator ruled proceed as
  proposed. TRACK A (evidence integrity) is LANDED: the CODEC
  schema gains the structurally-carried `law_exact` field — the
  direction a lax codec omits, which round-trip plus injectivity
  does not imply — filled across all five instances, including the
  newly proved chunking exactness (`Recipe.unchunk_exact`, the one
  ledger sentence claim that had no theorem anywhere) and three new
  bounded-decoder exactness theorems; the command stream is now
  law-bound by `step_commands_mirrored` (every wire command appears
  in the decision trace as its issued decision — previously prose
  only, leaving every trace-level exclusion silent about commands);
  MRK-018's rejection kit now exercises the recipe gate itself (a
  well-formed sixteen-byte document with an unregistered recipe)
  rather than truncation; RMT-007's entitled kit publishes against
  a NON-empty confirmed closure, so the closure half of the gate is
  witnessed in Lean, not only in vectors; the mutant quarantine
  gate now also walks the TypeScript sources for test-mutant
  imports; and the implementation briefing's consumable-manifest
  list includes the remote and Merkle families it had silently
  omitted since their slices landed. Committed manifests and the
  ledger regenerate byte-identical — the strengthening is invisible
  to ratified surfaces by design. Track A's remaining item — the
  sentence-versus-field alignment for the four bundles whose
  sentences carry conjuncts only docstring-cited theorems prove —
  awaits the operator's policy ruling (second law fields versus
  narrowed sentences), since sentences are ratified surfaces.
  Tracks B (host-boundary fault packet, led by the verified
  replay-session record race) and C (mechanical consolidation,
  split between lanes) proceed next; Track D rulings pending: the
  push present-node confirmation cost, the sentence policy, and
  peer-dependency timing.
- **CasScheme0 ratified (2026-08-27):** the operator ratified the
  hash docket as recommended, H1 through H6. The profile gains the
  addressing section: an address is the full thirty-two-byte
  SHA-256 digest of the canonical node encoding, nothing prepended
  and never truncated, domain separation inside the digest input,
  the scheme pinned by the profile revision with no per-address
  prefix, migration reserved to a future revision through
  registered decoders and non-authoritative alias indexes, and the
  digests-are-not-secrets boundary. The implementation packet cut
  with this record carries the injected `CasHash` service with the
  WebCrypto SHA-256 default layer, generated known-answer fixtures
  anchored on the FIPS 180 reference digests, and the
  authentication and deadline riders — one slice, the publication
  gate's last semantic prerequisite on the client side.
- **One front door landed; external host-boundary review verified;
  harness-enforcement directive (2026-08-27):** the architecture
  review's first candidate is landed: the package barrel exports
  exactly two namespaces, `Cas` and `Replay`, one per plane — the
  flat duplicates, the bare `value` leak, and the reducer clause
  helpers leave the public surface (the helpers stay
  module-internal for Lean correspondence), and inside a namespace
  the `Cas` prefix of internal module names drops (`Cas.Store`,
  `Cas.Transfer`, `Cas.Blob`, `Cas.RemoteConfig`). The
  `replayable` name collision is resolved: the upload source is
  `restartable`, and it is now a STREAM FACTORY — every retry
  attempt acquires a fresh stream, so a queue-backed or otherwise
  consumptive stream can no longer be labeled re-runnable; the
  bounded-retry test witnesses reacquisition. README rewritten to
  the two-door surface; both typechecks and one hundred sixty-six
  tests green. An external read-only review of `0fa1bde7` was
  verified claim-by-claim first-hand and every finding CONFIRMED.
  One nuance sharpens its first item: the redirect origin check
  compares the URL the adapter itself built against the origin it
  was built from — vacuous by construction, not merely misdirected
  — and actual redirect denial exists today only for fetch
  clients, where the manual-redirect request option makes a `3xx`
  fall into the invalid-status arm; for any other HttpClient the
  guarantee is unenforced. The concurrency finding needs the model
  to speak first: if the reducer refuses interleaved delegation,
  the runtime binds that refusal; if the model is silent, the
  exclusivity rule lands in Lean before the runtime enforces it.
  NEW OPERATOR DIRECTIVE reshaping priority: the Lean-vector
  vitest harness must substantially ENFORCE correctness — cut as
  Track E ahead of the fault items: a family coverage gate (every
  committed manifest bound or the suite is red, row counts exact),
  rendered-row agreement for the reducer and remote-machine
  families rather than outcome-only comparison, the MRK-014
  blob-graph binding over an injected toy address, law lanes that
  fuzz beyond the fixtures (codec exactness both directions,
  fragmentation invariance mirroring the proved theorems), and a
  briefing-emitted manifest index as the TypeScript-side authority
  for what must be bound. Lean-side prerequisites queued in this
  lane: the fragmentation vector family and the manifest-index
  emission.
- **Track E prerequisites landed: the fragmentation family and the
  manifest index (2026-08-27):** both Lean-side anchors for the
  harness-enforcement track are in. The FRAGMENTATION FAMILY is
  emitted as `MRK-015.json` and attached to the MRK-015 carrier row
  as its implementation-side evidence: one seventy-eight-byte frame
  body carrying all three proof-stream tags (skip, a
  length-prefixed chunk, a parent with two toy-digest addresses,
  plus an empty-payload chunk) is split five ways — single-shot,
  byte-by-byte, inside the length prefix, inside a parent address,
  and a ragged multisplit with empty fragments interleaved as a
  sixth — with IDENTICAL model-executed expectations, making the
  invariance a visible fixture; the truncation row completes with a
  nonempty partial-frame remainder, the unknown tag is malformed,
  and the empty fragmentation parses to nothing. The family is
  parameterized by the parser under test (`FeedFn`, real function
  `feedAll`), compile-time guards witness the carrier laws on the
  fixtures, and a BOUNDARY-DROPPED mutant — a framer that drains
  each fragment in isolation, discarding the carried partial frame
  — is declared and killed: twenty-nine declared mutants total.
  The MANIFEST INDEX is emitted as `INDEX.json` beside the
  families: the sorted names of every consumable manifest, bound to
  the model version, projected from the new single `allFiles` list
  that the emitter, the briefing, and the index now all read (the
  briefing's inline concatenation is gone, and its
  implementation-lane text names the index as the authority — a
  family it names without a suite binding is a red gate, never a
  silent gap). Every previously committed manifest and the ledger
  regenerated byte-identical through the change; the Track E
  packet's first item consumes the index instead of globbing.
- **Review pins landed: every confirmed finding is an executable
  test (2026-08-27):** the operator directed a test per review
  finding; `test/ReviewPins.test.ts` carries fifteen. The
  discipline: each pin exercises one confirmed fault's exact
  scenario and asserts the CURRENT defective behavior with the
  fixed behavior stated beside it — the suite is green while the
  defect stands and fails loudly the moment a fix lands, so the
  fix author flips the pin in the same change; resolved findings
  are LOCKS asserting the fixed behavior (the two-door barrel; the
  restartable factory's witness already stood in the remote
  suite). Pinned: the followed redirect an auto-following client
  makes invisible to the vacuous origin check; completion-order
  history rejecting program-order replay (first authoring attempt
  itself demonstrated the nondeterminism — under one Deferred wake
  order the history landed in INVOCATION order, so the landed pin
  gates alpha's resumption on beta's history commit in the store,
  forcing completion order by construction); the interruption
  window that commits a history node the aborted witness never
  reports (stale root asserted against the committed-but-
  unpublished node); a non-plain terminal prototype failing
  witness persistence after the program succeeded; the aborted
  witness whose receipt is discarded and the unbounded
  uninterruptible store write that makes cancellation stall
  without bound (two hundred yields, interrupt unsettled); the
  AbortError nested under a TypeError classifying as
  connectionFailed; the 204 acknowledgement accepting a hostile
  content-encoding; putStream reporting raw payload length as
  encoded-stage evidence (true canonical size asserted strictly
  larger); the witness-envelope consistency lock across both
  persistence paths; kit memoization returning the first kit for a
  conflicting registration; the phantom Scope on loadStream pinned
  at the type level; blob get planning the manifest twice (load
  count asserted); describeService accepting an empty prefix and a
  fractional revision; and the barrel lock (exactly two plane
  doors, clause helpers absent). One hundred eighty-one tests
  green across twenty-three files. The codex packet consumes these
  pins as its per-item exit criteria: an item is done when its pin
  is flipped to the fixed assertion and green.
- **SES-003 delegation protocol at effects-model@0.2.0; version pin
  corrected (2026-08-27):** the operator ruled the full sequential
  protocol in — both clauses, no shortcuts — and directed the
  version machinery to stop taxing development. This is the FIRST
  GENUINE SEMANTICS-AFFECTING BUMP: `effects-model@0.2.0` appended
  to the ratified list, every manifest re-stamped, and the two
  fixtures whose bare recorded shorthand became unlawful (SES-001,
  CMP-002) RESTATED as solicited sequences under their unchanged
  sentences. The protocol: session state carries the outstanding
  delegation (`pending`); a record-mode invocation registers it and
  a second invocation while one is outstanding is the typed
  `DelegationOutstanding` rejection; a recorded outcome appends
  only when it names exactly the registered invocation — none
  outstanding, or a different invocation, is the typed
  `UnsolicitedOutcome` rejection — so cross-wired, duplicated, and
  interleaved outcomes can never enter a durable history. SES-003
  minted plan-§7-first (FAIL-CLOSED; the solicitation predicate is
  the hypothesis, history length the frozen measure), with the
  refusal laws, the append-solicitation INVERSION (an append
  happened only for the registered invocation), and the run-level
  ORDER-COINCIDENCE theorem: a solicited run appends exactly its
  calls in invocation order and returns to a clean state — the
  Lean carrier for "invocation order IS append order". The Step
  relation splits the record rules four ways with explicit
  premises, mirroring the replay side's rule-per-rule form;
  `step_iff_reduce` and every law re-proved over the extended
  state; WF gains the replay-carries-no-delegation clause. CMP-002
  restates its emission as the solicited pair. Five-row SES-003
  family committed; TWO mutant directions declared and killed in
  BOTH lanes (accept-interleaved-invoke, accept-unsolicited;
  thirty-one Lean mutants, direction-2 red suites TS-side with the
  Lean meanings verbatim). Runtime enforcement (Layer 2): the
  session layer converts the model's record-mode rejection into the
  same typed session outcome as a replay mismatch, and a late
  outcome arriving after an abort is ABSORBED per the model rather
  than dying; overlapping record invocations now refuse
  deterministically — the M4-era concurrent-serialization test is
  rewritten to the refusal semantics and review lock 2 asserts it
  with zero history nodes committed. VERSION PIN CORRECTED: the
  TypeScript suites derive the expected model from committed
  `INDEX.json` (one shared `ManifestModel` now sourced, not
  hand-pinned), so this bump — and every future one — edits ONE
  Lean line and zero suites. The manifest-corpus invariants suite
  landed with it: the index names exactly the committed files, every
  family decodes through one closed envelope at the declared model
  with unique canonically-ordered case ids, and every family is
  BOUND to a named suite or DECLARED LEADING with its packet item —
  a model-side family can never again be a silent gap (MRK-014 and
  MRK-015 are the two declared leads). One hundred eighty-seven
  tests across twenty-four files; thirty-one mutants killed; ledger
  gains SES-003 instantiated. Named observations: (1) completion
  with an outstanding delegation remains model-permitted — the
  runtime cannot reach it (a live handler in flight means the
  program is not terminal) — revisit with Layer 3; (2) sound
  CONCURRENT recording (event identity, per-key causal matching,
  soundness resting on the ambient tripwires intercepting all
  nondeterminism) is reserved as its own designed milestone, per
  the plan's standing line — the refusal is the boundary, not the
  end state.
- **Worktree delivery accepted: profile letter, presence encoder,
  export surface (2026-08-27, merged @bb9f4272):** a three-commit
  worktree delivery reviewed first-hand hunk-by-hunk, every claim
  verified against the shipped letter, and merged. (1) The profile
  gains four rules that were in force but unrecorded — a third
  party writing a server from the profile alone would have failed
  against the shipping client: `cas-profile` and `accept` on every
  request (the reference peer answers 400 without the profile
  header, verified); `retry-after` honored only as an integer count
  of seconds with the date form dropped rather than a violation —
  an asymmetry now stated explicitly against `content-length`,
  whose malformed value IS a violation on both body and
  acknowledgment paths (verified in both); and acknowledgment
  closure sharpened — content-type may be absent but never
  different, non-zero declared length or any body byte is the
  unexpected-body violation (matches the shipped checks exactly).
  No exchange changed meaning; `/0` stands, no bump. The known
  pin-7 gap (204 bypassing the encoding guard) is neither
  introduced nor claimed fixed. (2) `encodePresenceDocument`
  completes the control plane's orphan codec pair, total over the
  status alphabet, with a round-trip test carrying the exactness
  direction, length-exactness both ways, and alphabet closure; the
  reference peer deliberately KEEPS its independent hand-rolled
  writer — the differential side must not adopt the implementation
  under test. (3) The package declares a root-only export surface
  shipping the source and the wire authority, consistent with the
  one-front-door ruling; the multi-subpath map was correctly
  skipped as prejudging the server-core shape. Delivery predates
  the 0.2.0 slice; the merge composed cleanly with zero file
  overlap — one hundred eighty-eight tests across twenty-four
  files on the merged tree.
- **Axiom profile enforced at build time (2026-08-27):** the
  release-queue axiom gate landed as a compile-time elaboration
  command in its own exe root, riding the default lake build so
  `check:effects` enforces it with zero task wiring. The sweep
  walks every constant declared under `Effects.*` with a
  shared-cache collector: only `propext`, `Quot.sound`, and
  `Classical.choice` may be reachable; `sorryAx` and the
  native-decide axioms are refused by name; every declared
  carrier-discharge citation must resolve to a real constant, so a
  renamed or typo'd theorem can no longer sit behind a green
  discharged row; and the resolved carriers are held to the strict
  base profile. FINDING sharpened by the gate's first run: all
  NINE discharge carriers stand on `propext`/`Quot.sound` alone —
  the choice-exception list is EMPTY; the documented
  `Classical.choice` users are instance-side only. The quarantined
  mutant tree is deliberately outside the sweep. The declared
  Merkle vector-growth batch (single-leaf opening, empty stream,
  manifest upper-boundary values, a five-chunk blob graph) is
  QUEUED, deferred while the in-flight implementation delivery
  consumes those exact manifests — growth lands after its
  acceptance under the ratified same-version mechanism.
- **CAS-004 canonical value encoding; printer totalized
  (2026-08-27):** two operator rulings landed through the harness
  rather than as hand-written assertions. INTEGERS ONLY: canonical
  value numbers are safe integers — the one number form whose
  textual rendering is language-neutral — so fractional and unsafe
  values are refused at encoding, never formatted; and key order is
  CODEPOINT order (equal to UTF-8 byte order), pinned because the
  shipped comparator was UTF-16 code-unit order, which silently
  disagrees on astral-plane keys — a second accidental-canonicality
  hole found while designing the family. CAS-004 minted
  plan-§7-first as a tsSide obligation: the model computes each
  structure's canonical bytes through a new total compact renderer
  and the implementation reproduces them byte-for-byte (eight rows:
  the escape set with raw controls, safe-integer extremes, the
  astral-versus-private-use key pair, codepoint sorting, nested and
  empty composites); the binding suite consumed every row on first
  run and the row flipped evidenced. The manifest printer itself is
  TOTALIZED in the same pass — the one `partial def` in the tree is
  gone: fields render before they sort, so both renderers are
  structural, and every committed manifest regenerated
  byte-identical through the rewrite, gate-proved. One JSON model
  now serves both surfaces (the pretty manifest printer and the
  compact value encoding), extended with an integer constructor.
  The operator's pointer at predictable-machines/lean4-tree-sitter
  is dispositioned: it stays the pending-admission Stage-1
  extractor instrument per TOOLS.md and does not enter the vector
  trust boundary — a C-FFI parser cannot anchor model-executed
  expectations, and the need here was a canonical encoder; the
  reuse instinct landed as the one-JSON-model consolidation
  instead. CALLER-SUPPLIED EXECUTION IDENTITY is ruled and queued:
  the session accepts an explicit executionId with the
  process-local counter demoted to a documented dev default —
  implementation rides the optimization packet because the session
  files are wet under the in-flight delivery. Also deferred there:
  the CAS-004 direction-1 mutant wiring, which waits on the
  mutation-runner dedupe in the worktree slice.
- **Tightening slice accepted and merged; CAS-004 mutant wired
  (2026-08-27):** the eight-item worktree delivery was reviewed
  first-hand and merged. Landed: the line-ending pin
  (`.gitattributes`, renormalize proven zero-content — root cause
  was autocrlf with no attributes, and regeneration now leaves the
  tree stat-clean); ONE FOLD (`runSteps`) behind both the session
  run and the manifest emitter, with `run` and `scenarioRow` as
  projections and the run equations surviving as `rfl` lemmas — the
  vectors are now generated by the function the laws are proved
  about, so the two cannot drift; the mutation runner deduped to a
  grouped table with stdout/stderr proven byte-identical; the
  take/drop privates replaced by core's `List.take_left`/
  `List.drop_left` (the brief's hypothesized names did not exist —
  verified in the toolchain source); the README and plan prose
  brought to the shipped surface, including the missing `keys`
  budget stage in a five-stage table; the dead fixture parameter
  removed; three decide-size constraints stated where they are
  real; and the briefing's consumable list rebuilt over the
  manifest index with ledger-shared status, so carrier-discharged
  families are no longer invisible to the implementation lane.
  Contract answers: the line-ending globs stay strictly scoped to
  the regenerated noise class — the five stragglers are stable or
  tool-owned; completed-milestone lists in the plan read as
  history, so the M1-era "eight templates" stands unedited. Board
  item raised by the delivery, awaiting the operator: `CONTEXT.md`
  still says six mismatch categories, its Replay-session Form
  omits the `pending` field and WF clause, and the
  delegation/solicitation protocol has no minted vocabulary — a
  ratification-surface amendment. With the deduped runner merged,
  the queued CAS-004 direction-1 mutant landed in the same pass: a
  declaration-order renderer, killed — thirty-two declared
  mutants. Both full gates green on the merged tree: one hundred
  ninety-six tests across twenty-six files, with the in-flight
  optimization delivery's caller-supplied execution identity
  composing cleanly.
- **Guaranteed-teeth conformance batch: access-set family, format
  goldens, purity gate (2026-08-27):** three enforcement classes
  landed under the operator's directive that tests be provably able
  to catch bad behavior — teeth demonstrated by a killed mutant, a
  golden byte, or a mechanical scan, never by assertion of intent.
  (1) MRK-020 minted plan-§7-first: READ COMPLEXITY IS CONFORMANCE
  — for each chunk list and range the model materializes the exact
  address set an honest ranged read may load (manifest, parents on
  intersecting paths, intersecting leaves, their chunk data), so a
  linear walk or a skipped boundary leaf is a red vector row, not a
  benchmark; compile-time guards pin the spine arithmetic (a
  one-chunk slice of eight touches five nodes; the full range
  touches every node exactly once), and the FULL-WALK mutant is
  declared and killed — thirty-three mutants. The family leads its
  binding, declared in the index registry until the shared read
  plan lands. (2) The internal storage format is pinned by GOLDEN
  BYTES: histories and witnesses are durable CAS content, so the
  recorded hex of a representative witness (covering the new
  protocol categories and optional fields), history entry, and
  nested stored value must encode and decode exactly forever — an
  encoder change that would strand existing artifacts turns red
  before it lands — plus a sixty-four-seed structural round-trip
  sweep beyond the fixtures. Captured against the just-optimized
  encoder, so the optimization is now permanently guarded. (3) The
  SRC PURITY GATE: nothing under src/ may run an Effect
  (runSync/runPromise/runFork/unsafe forms) — runtime execution
  belongs to callers — enforced as the first step of the
  TypeScript task. Queued with specs for the implementation lane,
  behind its in-flight parts: the exchange-count arithmetic suite
  (missing batches exactly ceil(N/maxBatchKeys), uploads exactly
  the missing count, publish exactly once — after the streaming
  push), the MRK-020 binding through a load-counting store (after
  the shared read plan), and the paired-perturbation reducer sweep
  (every generated lawful script paired with a one-edit unlawful
  twin that must reject).
- **Engineering rulings R1–R11 ratified; attested presence lands as
  RMT-017 at effects-model@0.3.0 (2026-08-27):** the operator
  ratified the recommendation sheet wholesale. In force: R1 a
  witness-sink service with a no-op default, one receipt per
  attempt, never able to fail the operation it observes; R2
  attested presence (landed below); R3 every ratified sentence
  conjunct gains a named law field — sentences never narrow; R4
  peer dependencies stay exact-rc until effect 4 stable, alphas
  only until then; R5 the decision-transcript capacity is
  configuration (already shipped by the implementation lane,
  default 4096 — confirmed ratified); R6 a `probeAt`
  acquisition-versus-first-use configuration field; R7 publish
  gates for 0.1.0-alpha.1 — private flips only when pins are
  flipped, publish mechanics accepted, main pushed CI-green, and
  R4 landed, explicitly NOT gated on a server; R8 the proof pause
  lifts for MRK-017 only, after the optimization packet; R9 one
  push to origin after the in-flight deliveries merge; R10 sound
  concurrent recording stays a designed post-alpha milestone; R11
  the CONTEXT.md vocabulary amendments. The R2 landing is the
  program's second genuine semantics bump: the machine gains a
  wire-less `attest` operation — a key the peer reported present
  whose bytes the client holds and verifies locally enters the
  confirmed set; without the presence report or the local
  verification the attestation is refused with a typed result; and
  attestation NEVER admits to the cache, so presence stays
  non-admission for every read path. Rationale pinned in the
  model's docstring: downloading a present node only proves
  retention at confirmation time — the local bytes are the
  stronger evidence, and the peer's own presence claim is the
  entitlement. Four theorems (confirmation, both refusal
  directions, cache non-admission), a FailClosed instance with
  both kits, four schedule rows through upload-presence-publish
  composition, and the AttestWithoutPresence mutant — a machine
  confirming on local bytes alone — declared and killed:
  thirty-four mutants. Every committed manifest re-stamped to
  0.3.0 model-line-only, byte-identical elsewhere, and the
  ratified-versions list append IS this record's event. The
  TypeScript mirror was compiler-forced end to end: the op union
  extension broke the step's narrowing-by-exclusion, the
  differential normalizer's exhaustive switch, and the adapter's
  result classifier, and the index registry's bound-or-leads suite
  refused the new family until it was bound — every seam the
  harness work was built to guard fired. Classification note: the
  adapter maps `AttestRefused` to an invariant breach today
  because no adapter operation issues an attest; the streaming
  push rework adopts the operation for locally-held present nodes
  and lifts that arm to a typed policy failure. Two hundred five
  tests across twenty-seven files; both full gates green at the
  commit.
- **R3 landed: sentence riders make docstring citations load-bearing
  (2026-08-27):** the ratified rule — sentences never narrow, and
  every conjunct a ratified sentence claims must be discharged by a
  proof the build forces — gains its mechanism. A `SentenceRider`
  carries the obligation id, the quoted sentence fragment, and the
  discharging statement WITH its proof as dependent fields, so
  renaming, weakening, or deleting the cited theorem breaks the
  instance file at compile time instead of leaving a stale
  docstring. Six riders declared beside their instances and
  coverage-checked in the registry: RMT-001's return half (the
  admission theorem's second conjunct, previously carried by prose),
  RMT-003's rejection-set monotonicity and whole-run terminality
  (the run corollary was cited but nothing forced it), RMT-017's
  entitled-confirmation and cache-non-admission directions, and
  SES-003's append-in-invocation-order run half — which until now
  was forced only accidentally, through CMP-002's kit proof
  happening to use it. Elaboration note for future riders: cite
  theorems in `@`-form — a bare name in an inferred-Prop position
  inserts implicit-argument metavariables that cannot resolve, while
  the fully quantified constant is itself the proposition. The
  riders change zero generated bytes: manifests and ledger
  regenerate identically, thirty-four mutants stand. With this the
  ratified R1–R11 sheet is fully executed on the model lane; the
  remaining rulings live in the implementation packet.
- **Remote-lane remediation accepted (2026-08-27):** the
  implementation lane delivered the full addendum, reviewed
  first-hand hunk-by-hunk against the pre-registered attack list,
  both gates run personally — thirty-four mutants, two hundred
  eighty-four tests across twenty-nine files, build and dist smoke.
  The P1: push now preflights the COMPLETE closure retaining only
  identifiers and a running maximum encoded length, checked after
  capability acquisition and before any negotiation or upload — the
  regression pins the exact geometry (batch cap one, oversized
  parent behind a small child) and proves the withheld prefix: one
  wire request total, zero gets, zero puts, and a typed budget
  error carrying no fabricated operation or attempt identity.
  ATTESTED PRESENCE IS NOW LOAD-BEARING ON THE WIRE: the push
  present-path attests locally-held bytes (re-digested, not
  trusted) instead of downloading nodes to confirm them — the exact
  TOCTOU the RMT-017 amendment was ruled for — with the adapter
  tests observing zero gets, cache size zero, confirmed size one;
  `AttestRefused` lifted from an invariant-breach die to the typed
  policy code `attestRefused` (additive public-union extension).
  Also verified in force: timeout errors carry the bytes actually
  received through a shared reference; policy errors derive
  evidence from their underlying exchange and preflight budget
  errors carry no identity; retryable capability-probe failures
  invalidate the infinite-TTL cache while auth failures stay
  memoized; the decision transcript is a true ring with an exposed
  dropped counter; the authority Schema admits only http(s) and the
  credential label constraint is gone; `remoteConfig` names its
  defaults out loud; the header codec's bound lives in the Schema
  and the tri-state became a tagged pair; the five error
  constructors closed over config (thirty-seven call sites
  shortened); the wire drivers carry spans; the dispatch and
  interrupt-cleanup helpers deduplicate nine and four sites; and
  the barrel is pure re-exports again. Two observations, neither
  blocking: the probe docstrings still say "one memoized probe"
  while failed probes now retry — under-promising, one-line
  truth-up owed; and the batch-cap-zero path avoids a zero-step
  loop only because presence negotiation fails typed first — an
  explicit guard would state it. With the streaming push landed,
  the queued exchange-count arithmetic suite and the deferred test
  consolidations unblock.
- **SRV-001 minted: the model server is a program, and its run is the
  vector (2026-08-27):** the interaction-tree seam gains its
  executable half and its first conformance family in one move.
  Reification is interpretation: `traced` transforms any handler to
  also reify each event with its answer — the same combinator shape
  as `tiered` — with the erasure theorem proving tracing
  observationally free, so every handler law transports to its
  traced form. `runServer` folds a request script through the tree
  denotations; `runServerTraced` is the same fold under the
  transformation, and its output — outcomes plus the reified
  storage transcript — IS a conformance row, never hand-typed. The
  vector server instantiates the tree at the shared remote vector
  environment (toy-digest addresses over ratified CAS-codec
  encodings) with FULL admission as the judgment parameter, and
  seven compile-time `#guard`s query it in place: capabilities,
  loads, the upload round trip, dangling and non-canonical and
  oversized refusals — the server answers at elaboration, forever.
  Four scripted sessions render with hex-string addresses and
  bytes — the wire profile's own representation — so the
  implementation binding decodes rows through its branded address
  schema and the stock hex codec, and a decoded request IS the
  protocol's `CasRequest` (an identity function witnesses it; the
  compiler proves the alignment, no cast). The binding replays each
  session through the semantic core over a recording backend under
  the vector digest — the core now takes its address function
  explicitly, quantifying over the digest exactly as the model does
  — and must reproduce outcomes AND the exact storage-event
  sequence, in order: the transcript is law, so a skipped admission
  check, an extra load, or a reordered negotiation is a red row.
  The AdmitDangling mutant — a judgment that never consults the
  declared references — is declared and killed: thirty-five
  mutants. Additive at 0.3.0: every existing manifest byte-stable,
  INDEX gains one name, the index registry binds the family, and
  SRV-001 enters the ledger tsSide-evidenced. Deprecation note:
  `String.mk` is deprecated at this toolchain — `String.ofList`.
