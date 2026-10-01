**The one thing:** R1–R9 require only that a full program stays typed and safe; what it does — composed-module behaviour (no requirement at all for 6 of the 13 module families and 4 of the 13 workstreams), exactly-once release, deadlock, the face simulations — has no requirement, and the two terms R1–R2 rest on, "lawful Σ" and "Σ ⊆ Σ'", are undefined: define both (A1, A2) before the milestone is restated over Σ.

# Completeness of R1–R9: what the requirements miss

Seat: COMPLETENESS of the 2026-09-30 model probe. Note under review:
`docs/research/2026-09-30-full-program-model-requirements.md` (base `74b526d4`; read at HEAD
`7cae243a`, which adds only that note and an eleven-line STATE.md paragraph). Research only:
nothing tracked was edited; no build, no generator. Two Lean probes in this folder, compiled
through the one-compiler lock (§5).

**Method.** Every place the research already enumerated what a full program needs was read and
each item mapped to R1–R9: post-Phase C §11 (W0–W12, the 13 families, the 18 unstable groups,
the §11.4 contract shape), the design-issue map, the language cut §§1–6, the stateful
catalogue, the charter (end state §10), the dogfood conclusions and applied findings, the host
boundary, machine state §7, LCNF route §8, every open decisions row and DI, plus the
DESIGN-BASIS required proof graph, the papers review G1–G8, core math §§9–10 and the literature
note's INV-TAPE rules. Where a note already settles a point it is cited, not re-derived.

**Words.** *proved* (a kernel theorem I ran), *tested* (a finite check I ran), *reading* (read in
code or notes), *assumed*. In the tables: **Rn** covered; **Rn (part: …)** partly, with what is
missing; **uncovered → Ax** no requirement, with the proposed addition of §4 (A2 is R2
rewritten); **→ Rn change** a change to an existing requirement, also in §4; **n/a** not a
requirement on the model (process, packaging, a bug fix), with the reason. Every cell is
*reading* unless it names a probe.

## 1. The verdict

- **What R1–R9 cover.** The typing and safety half of the model, over an open signature:
  typing (R1), the extension rule (R2), data (R3), cells (R4), services (R5), the host premise
  (R6), retained code (R7), runs and numbers (R8), never-goes-wrong (R9). That is W0–W2 and
  W10 in part, and the charter's *Sound* and *Extensible*.
- **What no requirement covers.** What a full program *does* once it is typed:
  - the behaviour of composed library modules against a contract (W3–W9; row 79; DI-89's
    "one behaviour law" per form; post-Phase C §11.4), which is how queues, caches, schedules,
    transactions and streams reach programs at all (system map §3 item 4);
  - resource safety: a release runs at most once, and exactly once in a finished run
    (DESIGN-BASIS, required proof graph, "Scope and runtime");
  - deadlock and liveness (papers review G6–G7; core math §9);
  - the faces as named simulations: typed lowering to TypeScript, the LCNF stages, identity
    across faces (LCNF route §8; DI-49; DI-81);
  - the charter's *Simple* and *A base for higher-order APIs*.
- **Two undefined terms.** R1 quantifies over "every lawful Σ" and R2 over "Σ ⊆ Σ'"; neither is
  defined, and neither exists in the tree. Lawfulness is spread over four checks today
  (`LawfulTable`, `checkTable`, the `int` scan, and row 97's interim rule in flight). The order
  must be DI-47's append-only relation: the probe shows an inserted row re-points every call of
  an existing program, so it stops checking (`Extension.lean`, tested).
- **Mis-scoped.** R1's Σ lists cells and data as components; cells are the core's polymorphic
  rows, not something an application supplies. R7 and R8 state features, not theorem shapes.
  R8 cites `journal_replays` (proved, about `Run`) for row 98's typed replay route, which is
  open.

## 2. Coverage

### 2.1 Workstreams (post-Phase C §11.2)

| W | owns | coverage | missing, with source |
| --- | --- | --- | --- |
| W0 control and typing | order, errors, interruption, races, scopes, finalizers, frontiers | R1, R9; R6 for the host premise | exactly-once finalization (DESIGN-BASIS proof graph, "Scope and runtime") → A4; deadlock, liveness (papers review G6, G7) → A5; §11.1's totality over the pinned surface (every export gets a disposition; an unregistered head is refused by name, DI-89) has no requirement, though the note lists it among its sources → A6 |
| W1 values, types, atoms, data | scalars, errors, records, collections, equality, mutation, embeddings, generic cells, binder terms | R3, R4; R2 for atoms | collections and their key, duplicate and order policy (machine state §5; catalogue §3 item 3; DI-78), equality (DI-35), `int`/float carriers and inhabitance (language cut §2; DI-67) → R3 change |
| W2 context, config, layers | service identity, Config, memo layers, LayerMap, ManagedRuntime, ScopedRef, Resource | R5 | Config and reference keys (Config D1–D5; provision algebra §6, `KeyKind`); key identity (`PROV-FB-KEY-FORGERY`, papers G5, DI-05, DI-64); `build_total` and `lower_refines_build` in the tree (provision §§2–3) → R5 change; the resource wrappers → A3 with R7 |
| W3 observations, identity, storage | public and private state, holder, trace, journal, typed ids, container refinements | uncovered → A3, A6 | rows 78, 79, 85, 101; DI-81 |
| W4 retained behaviour | code entries, captures, FiberHandle/Set/Map, Cache, RcMap, Pool, Request | R7 (part: a design, no theorem) | entry signature and capture layout established at resolution (machine state §5) → R7 change; each module's behaviour → A3 |
| W5 coordination, waking | Ref, Deferred, Latch, Semaphore, Queue, PubSub, SynchronizedRef | R4 (Ref, Deferred only) | a new store family such as Latch is not an extension point of R2 (row 81) → A2; composed modules → A3 |
| W6 time, schedules, random | Clock, Duration, Cron, Schedule, Random; retry, repeat, timeout | uncovered → A2, A3 | clock and random as decision sources (row 83; DB-14; catalogue note 7); Schedule as data (DI-89 forms) |
| W7 transactions | TxRef family | uncovered → A3 | rows 80, 84 |
| W8 streams | Stream, Channel, Pull, Sink | uncovered → A3 | DI-11's pull kernel as a contract |
| W9 schema, codecs | Schema, AST, parser, transformations, JSON Schema | R3 (part: the embedding of new data types only) | rows 1, 4, 5, 9, 10, 11, 35, 39; DI-08 → A6 (K2 for each face) |
| W10 host | host services, table-aware semantics | R6 | the acceptance converse (host boundary §4.5); inbound entries (pass synthesis §7, "Several roots"); the algebraic row meaning (DI-69) → R6 change; lifecycle (row 100) parked |
| W11 source and target | readers, authoring, profiles, LCNF/OCaml, backends | R8 (part: names one entry path), R2 (printer and reader entries) | the stage connections (LCNF route §8); typed lowering (DI-49, DI-24); rows 26–33 → A6 |
| W12 publication, surfaces | bytes and key table, CAS, replay-relative tapes, compatibility, digest, API, MCP, observability | R8 (part: the run API) | DI-01, 04, 05, 06, 25; rows 14, 18 → A2 (identity under ⊑), A6 |

No workstream is covered beyond typing and safety; W3, W6, W7 and W8 have no requirement.

### 2.2 Module families (post-Phase C §11.3) and unstable groups

| family (modules) | coverage |
| --- | --- |
| Control (8) | R1, R9 (part: release and deadlock → A4, A5) |
| Context/resources (10) | Context, Layer: R5. Config, ConfigProvider, References: uncovered → R5 change. LayerMap, LayerRef, ManagedRuntime, ScopedRef, Resource: uncovered → A3 with R7 |
| Cells/coordination (10) | Ref, Deferred: R4. MutableRef, Latch, Semaphore, PartitionedSemaphore, Queue, PubSub, SynchronizedRef, SubscriptionRef: uncovered → A3 (Latch also A2) |
| Ownership/behaviours (10) | R7 (part: the code reference); behaviour uncovered → A3 |
| Transactions (11) | uncovered → A3 (rows 80, 84) |
| Time/retry/random (7) | uncovered → A2 (decision sources), A3 |
| Streams (6) | uncovered → A3 (DI-11) |
| Schema (9) | R3 (part) → A6 |
| Observability (6) | uncovered: §11.2 W12 asks a diagnostic versus program-visible contract → A6 (observations as projections) |
| Host services (6) | R6 (the lane is parked) |
| Collections (15) | uncovered → R3 change |
| Scalars/structural values (16) | R3 (part: records, Option, Result), R8 (numbers); BigInt, BigDecimal, Number beyond `nat`, Redacted, RegExp: uncovered → R3 change |
| Pure protocols/utilities (23) | uncovered: §11.4 gives type-only entries "a mapping obligation"; Equal, Hash, Order need DI-35's equality → R3 change, A6 |

Six families have no requirement (transactions, time, streams, observability, collections,
pure protocols); none is covered past typing. Of the 18 unstable groups, the host-bound ones
(ai, cli, http, httpapi, process, rpc, socket, sql) sit under R6 and A3; persistence, workflow,
eventlog, cluster and workers need durable-journal and distributed-identity obligations that no
requirement names (host boundary §4.2, last bullet; §11.3: "no automatic identification with the
local machine journal"); devtools and observability → A6; encoding and schema → R3; reactivity →
A3.

### 2.3 The charter (end state §10): seven properties, seven rules

| item | coverage |
| --- | --- |
| *Sound* | R1, R9 (part: R1 asks for the milestone over Σ but no requirement states the milestone itself; DI-17's "every failure fits the declared type" rides on it) |
| *Predictable* | R6 (table-aware agreement), R8 (part). Missing: one meaning equation per operation of Σ (end state §4.1, `meaning_<op>`); print/read as an exact embedding for every lawful Σ (R2 lists the entries, not the law); identity across faces (DI-81) → A2, A6 |
| *Simple* | uncovered: "no construct without an equation; no evaluator without a simulation; no second denotation" has no requirement; R2's local obligations omit the meaning clause → A2 |
| *Extensible* | R2 (part: the order is undefined; forms, equations, store families and decision sources are not extension points) → A2 |
| *Arbitrary complexity* | R1/R9 (the typed reference world), R6 (host rows). Missing: "row handlers in the algebra" (S8d; DI-69's `denoteRows_eq_session`, not in the tree) → R6 change |
| *Data in the IR* | R3, R7 (part). Sharing has no requirement: no procedure form, so a planner unrolls to 17 KB per event (dogfood 6, F21; end state §8, "Where the basis is thin") — recorded as an open question, §4 |
| *A base for higher-order APIs* | uncovered: "every compiler into `Eff` returns a `Verified`-family bundle whose theorems are inherited" → A3 |
| rule 1, finite checks are evidence | n/a (the note keeps its status words) |
| rule 2, certificates by kernel decision | uncovered for Σ: nothing requires Σ's lawfulness to be decidable by the kernel → A1 |
| rule 3, no construct without an equation | R2 (part: rows only, through the protocol entry) → A2 |
| rule 4, no fragment without its agreement theorem | R6 for host rows; R1 restates `MeaningSound`/`LoopSound` but not `run_eq_meaning`, `loopAgreement`, `run_eq_ref` over Σ → R1 change |
| rule 5, no evaluator without a simulation | R2 (part: "stage connection") → A6 |
| rule 6, models are data | R7 (part) → A3 (a compiler's inputs are data) |
| rule 7, proofs reach code only as `Prop` fields | uncovered for Σ: the shape of a lawful Σ must be a runtime structure with `Prop` fields, as `AdmittedProgram` is → A1 |

### 2.4 Decisions rows still open or unfinished (`docs/core/decisions.md`)

| rows | topic | coverage |
| --- | --- | --- |
| 2 | names for records and sums | R3 |
| 1, 3, 4, 5, 6 and 35 (exactness residue), 9, 10, 11, 39 | the schema face: canonical schema object, `Ty.app`, checks, D12's shape, `ofSchema` exactness, `schemaOf`, one `Val → Json`, `Schema.*` text, the wipe | R3 (part: new data types only) → A6 (K2 with all three laws, per face) |
| 7, 97 (route), 100 | handles at the boundary; the registry; host resources | R6 (part); 97's interim rule is in flight; 100 parked → R6 change names its shape |
| 8, 24 | key spelling and dedupe; minted spellings | n/a (bug fixes) |
| 14, 18 | table by digest; `digest_inj`, `observe_inspect`, `build_check` | uncovered → A2 (identity stable under ⊑), A6 (the observation is a projection) |
| 15, 16, 17, 19, 22, 23 | MCP server; `Await`; reading-type codecs; root modules; `gen` without a lift; two verbs | n/a (surface; the laws they need are rows 14 and 18) |
| 20, 91, 92, 93, 94 | fork site; fork ledger; reader switch; trace agreement; automation | n/a here (slice 6, in flight); the ledger is the creation evidence R6 needs |
| 21, 51, 90 | service table threading; `ServiceOk`; contexts typed by static key types | R1, R5 |
| 26, 27, 28, 29, 31, 32, 33 | TypeScript rules; LCNF recipe; what verified lowering means; the LLVM steer; the rung-3 reader; vendoring order; `lean4-typescript` additions | R8 (part: one entry path) → A6 |
| 30 | `compileEff` stays exempt | n/a as a fold question; `Eff → Prim` has no theorem (papers review G1) → A6 |
| 41, 86, 87, 88, 89 | the milestone and its contracts | R1 (parametrise), R9 |
| 42, 43, 44, 45 | generic cells; binder-term rows; typed world; per-cell promise table | R4 |
| 49, 50, 53, 110 | generation in place; ledger; Protocol's home; generic lifts | n/a (tooling, placement) |
| 52 | progress as corollaries | R9 (part: "never halts" on `Stuck.unknown*` is not named) → R9 change |
| 54, 95, 98, 99 | external rows in the reference; host-free tapes; typed replay route; when the guarantee is claimed | R6; R8 for 98 (over-claimed, §3) |
| 78, 85, 101 | completion and memo cleanup; first storage refinement; how stages compose | uncovered → A6 |
| 79 | the observation and agreement each composed module and target owes | uncovered → A3 |
| 80, 84 | transaction profile; its first fragment | uncovered → A3 |
| 81 | scheduled-wake primitive (Latch) | uncovered → A2 (store families), A3 |
| 82 | typed behaviour values | R7 |
| 83 | clock, random, behaviour-bearing context | uncovered → A2 (decision sources) |
| 96, 104, 105, 106, 107 | `Fits`; layer environment; layer value; fresh tokens; never goes wrong | R4 (96's D2), R5 (104, 105), R1 (106), R9 (107) |
| 108, 109 | numbers on every face; FloatLib | R8; 109 parked (binary64 belongs to W6, uncovered) |

Rows not listed (12, 13, 25, 34, 36–38, 40, 46–48, 55–77, 102, 103) are settled. They are
constraints the requirements keep (rows 55 and 60 on variance, for example), not requirements.

### 2.5 Design issues (`docs/DESIGN-ISSUES.md`) and the Config questions

| DI | topic | coverage |
| --- | --- | --- |
| 01, 04, 05, 06 (open) | unit of publication; replay-relative tapes; key position; `Cid` in jobs | uncovered → A2 (identity under ⊑) |
| 08, 16 (open) | Schema in the release; the surface lane's package | n/a (architecture) |
| 21 (deferred) | class-shaped units and `Effect.fn` on the foreign face | uncovered → A6 (reader admission) |
| 46 (open) | `Canonical` for the stores and memo map | n/a (a run is data through its journal, K5) |
| 95 (open, implemented) | wildcard classifier | n/a (stale row) |
| 09, 31, 62, 74 | error elimination and payloads | R3 (the owner row it proposes) |
| 10 (deferred) | a neutral-stack bind law | uncovered; the DESIGN-BASIS "Logic" edge is empty → §4, open question |
| 11 | streams as the pull kernel; queues composed | uncovered → A3 |
| 17 | every failure fits the declared type | R9 (part, through the milestone) |
| 23, 57, 58, 59 | multi-fiber tapes; table-aware agreement; envelope validation; the DB-15 pair | R6 |
| 65 | host laws do not force determinism; terminal observation needs completed cleanup | R6 (part) → A4 |
| 69 | the row table's meaning as a `Family`; `denoteRows_eq_session` | uncovered (the algebraic row meaning, P5) → R6 change |
| 24, 29, 49, 55, 76, 77, 88 | the printed face: requirement rows, oracle binding, printer output type-checked, literal types and the F3 branch, uncompared programs, unit spelling, the readers' roles | uncovered → A6 (typed lowering) |
| 22, 25, 64, 79 | link-table positions; CAS kinds; row identity with receiver; alphabet migration | R2 (part: no order) → A2 |
| 35, 67, 78 | equality; inhabitance; collection authoring | uncovered → R3 change |
| 39, 89 | derived error heads; how any Effect module enters `Eff` (rows generated per module; forms with a typing lemma and one behaviour law) | R2 (part: rows only) → A2 (forms), A3 |
| 56 | scalar domain | R8 |
| 80, 97, 98 | `refSet` answers unit; `deferredPoll` | R4, R7 (97) |
| 81, 73 | fiber identity, compared up to one partial bijection | uncovered → A6 |
| 85 | the application face | R8 (part) |
| 90 | the `Effects` package | n/a (row 53) |
| Config D1–D5 | provider carrier; error image; print and read; provision; scalar codecs | uncovered → R5 change |

The other ruled rows (DI-00, 02, 03, 07, 12–15, 18–20, 26–28, 30, 32–34, 36–38, 40–45, 47, 48,
50–54, 60, 61, 63, 66, 68, 70–72, 75, 82–84, 86, 87, 91–94, 96, 99, 100) are landed or settled
constraints.

### 2.6 The other enumerations

| source and item | coverage |
| --- | --- |
| language cut §6 (a dated snapshot, its own header says), the cuts in the order programs hit them: records; error payloads; generic `Ref`/`Deferred`; binder-term rows; the atom alphabet; service carriers; the absent modules of §4. At HEAD all hold but the atoms: 33 now, with list, option and arithmetic (`NativeAtom`, `Machine/Term.lean`); map atoms and removal by equality are still missing | R3; R3 (owner row); R4; R4; R2 (part: no requirement says which atom families a full program needs) → R3 change; R1, R5; uncovered → A3 |
| language cut §5: `.program`-kind (external) rows stop at `pending .unsupported` in the reference (`Laws/Program/DenoteR.lean:603`) | R6 |
| language cut §§1–5, the rest: functions as values (profile, DI-20/28); defects as an alphabet that grows with rows; `FiberRef` only through the context map; `getId` answers a number; the logical clock | R7; R2 (part); R5 (part); uncovered → A6 (DI-81); uncovered → A2 (decision sources) |
| post-Phase C §11.4, the six-piece module contract | in the note only as an order item (its §5 item 5), not a requirement → A3 |
| catalogue §3, the minimal basis: generic rows; binder-term read-modify-write; map atoms and list removal; handles inside values typed; a program value; a Latch store | R4; R4; uncovered → R3 change; R4 with row 96; R7; uncovered → A2 |
| catalogue §5: Q1 the fidelity a composed module owes (values, relative to the tape); Q3 print the expansion or the module call; Q4 the program value; Q5 Latch or delete the scheduled-wake half; Q7 where randomness comes from; Q8 user clocks refused | uncovered → A3; uncovered → A6; R7; uncovered → A2 (store families); uncovered → A2 (decision sources); uncovered → A2 |
| dogfood conclusions §2 and §8: a result-level disagreement through identity inside a merged layer; "equality relations between identities" must agree | uncovered → A6 |
| dogfood conclusions §5, §7: lazy `getOrElse` fallback admitted only for pure total terms; a derived-forms library with behavioural laws (D-G) | uncovered → A6 (reader admission), A3 |
| dogfood D-F, the engine and host rows | R8 |
| dogfood applied §2, the other findings: positional binders, layer references by path (authoring); encounter-order and multi-fiber tapes; the import header, the printed `undefined`, unit from a row or a literal, the key's carrier and `noninjective` (faces); fixture owner, count pins, wire size (process) | n/a (authoring surface); R6; uncovered → A6; n/a |
| host boundary §4.1 interfaces (`RequestFits` … `RegistryAgrees`); §4.5 receipt and application | R6 |
| host boundary §4.5, "the converse is owed: every semantically valid, representable reply is accepted" | uncovered → R6 change |
| host boundary §4.2 lifecycle; §4.3 declarations from creation evidence | R6 (part: parked; for cells there is no creation record today, pass synthesis §2.1) |
| machine state §7: six storage interfaces, fourteen families, "creation facts in append-only records", "declarations are derived views" | uncovered (interfaces) → A6; R4, R6 (part: derived declarations) |
| LCNF route §8: eight connections | 1 (source to reference) implicit in R1; 2 (reference to runtime) R6; 8 (`Eff` to TypeScript) R2 (part); 3–7 uncovered → A6 |
| LCNF route §8: the seven rules for every stage (allowed behaviour only; no new stuck state; a stuttering bound; identities related consistently; budgets correspond; certificates bind the artifact; universal claims need a checked certificate) | uncovered → A6 |
| DESIGN-BASIS, required proof graph: Algebra; Admission (stable refusal classification pending); Operational semantics; Recursive meaning (divergence adequacy pending); Logic (empty); Scope and runtime (exactly-once finalization); Schema and services; TypeScript target (typed lowering pending) | model; R1 (part); R1, R9; uncovered; uncovered; uncovered → A4; R3, R5 (part); uncovered → A6 |
| papers review G1–G8 | G1 (`Eff → Prim` has no theorem) → A6; G2 landed (`Laws/Machine/Approximation.lean`); G3 (pure steps central) uncovered, needed only when an optimization relies on it; G4 is the milestone (R1); G5 (key freshness) → R5 change; G6, G7 → A5; G8 deferred (DI-10) |
| core math §1 (behavioural equivalence is a congruence, so a rewrite is justified once), §9 (fairness, deadlock), §10 (time, streams) | uncovered → A3 (congruence for expansions), A5, A2 and A3 |
| literature note Q7: INV-TAPE-1 (no off-tape choice), INV-TAPE-2 (a frontier names what it awaits); its §B trap T8 (an inlined library expansion changes every stored program's address) | uncovered → A2; A5 (a deadlock names no reason, probe); A2 |

## 3. Flags on R1–R9 (mis-scoped, duplicated, over-claimed)

1. **R1's Σ is not the tree's `Signature`, and its lawfulness is undefined.**
   - `Signature` (`Program/Typing/Rules.lean:49-69`) holds `rowOf`, `atomOf`, `scopeKey`,
     `serviceTy`, `dom`, `constAtom`; no data, no cells. Cells at every type are the core's
     template rows ("No `Row.params` … a row is a function of the operation's data", rows 42–43
     plan §2b), not something an application supplies: take cells out of Σ_app. Structural
     records extend the sort `Ty` (type algebra §1.3), not Σ; Σ needs a type-declaration part
     only if nominal or recursive types are admitted, which R3 records as open with no owner.
   - Typing reads `atomOf`, but evaluation is the closed match `NativeAtom.eval` (rows 64, 66).
     A meaning theorem over Σ needs Σ's atoms to be the native table, or a premise that each
     atom's evaluation fits its scheme (row 74's `sound_of_poly` is the shape).
   - "Lawful" names no definition; nothing like it exists. Lawfulness is four checks today
     (`Api.lean:372-395`): `LawfulTable` (`Codegen/Read.lean:1943`), `checkTable`
     (`Program/Native.lean:322-352`), the `int` scan (`Program/Admission.lean:100-106`), and row
     97's interim rule (in flight). → A1.
   - Charter rule 4 pairs each fragment with its agreement theorem; R1 restates
     `MeaningSound` and `LoopSound` over Σ but not `run_eq_meaning`, `loopAgreement`,
     `run_eq_ref`.
2. **R2's order is undefined, and "rows: additive by construction" over-claims.**
   - Theorems quantified over every table re-instantiate at Σ'; facts about one program do not.
     Its type, certificate, run and digest need a transport lemma, and none exists (no
     `effTy_congr`, `Signature.Extends` or similar under `src/`; tested by grep). A certificate
     is indexed by its table (`Api.Typed table`, `Api.lean:443-445`), so it is re-issued.
   - The order must be DI-47's: "Reject reorder/removal/reframing/tag reuse; declared appends
     are allowed", with link-table positions (DI-22) and receiver-qualified row identity
     (DI-64). Probe `Extension.lean` (tested): appending a fresh row keeps the program's type and
     exit; inserting it in front re-points every call and the program no longer checks; a
     clashing name makes `LawfulTable` false.
   - Extension points left out: **forms** (DI-89: higher-order APIs are templates "each with a
     typing lemma and one behaviour law"), **equations** (the charter's *Extensible*: "a row, an
     atom or an equation"), **store families and handle kinds** (row 81's Latch adds a store,
     six rows and a handle kind, catalogue §3 item 6; a family that holds typed values also
     needs a world column, and the world `⟨Γ, Π, Ρ, Θ⟩` is a fixed record,
     `Laws/Program/Typed/World.lean:52-57`, as `Stores` is a fixed record of seven fields,
     machine state §1, and the handle kinds a closed list of six, `Machine/Value.lean:60-67`).
   - Local obligations left out: a meaning clause (charter rule 3); a decision-source clause
     (literature note Q7, INV-TAPE-1); the rc.112 cite and census row (AGENTS.md representation
     rules); the target entry checked by the rows lane (rows 68, 75); the `Fits` clause for a new
     `Ty` constructor (host boundary §4.4, "every `Ty` constructor has its clause"); an
     append-only wire tag (DI-47); for a store family, its handle kind with a `HandlesFit` clause,
     a world table when it holds typed values, and a storage interface (machine state §7).
   - Its per-point status list repeats §4's table and R1, R4, R5.
3. **R3** says "named records"; the ready design is structural (`record (fields)`,
   `variant (cases)`), with `Ty.foreign id args` as the nominal form (type algebra §1.3). It
   omits collections, equality, numeric carriers and inhabitance (§2.1, W1).
4. **R5** repeats R1's threading and misses key identity, reference keys and Config, the build
   theorems and scope elimination (§2.1, W2). `Program/Provision.lean:37` describes a
   `build_total` "proved once over the algebra"; no declaration of that name exists under
   `src/`, `Test/`, `tools/` or `workshop/` (tested by grep). The note's own sentence (§1:
   "proved in the 2026-09-04 workshop spike only") is right; the module header is not.
5. **R6** has the receipt and application theorems and the table-aware agreement, but not the
   acceptance converse (host boundary §4.5), declared equations for host rows, inbound entries
   (§4, R6 change), or the algebraic row meaning (DI-69). It also introduces H afresh, while the
   tree already has a host specification as relations (`HostSpec`, `Program/Profile.lean:178`).
6. **R7** is a representation choice ("take typed first-order code references"), not a
   theorem shape.
7. **R8** over-claims and states features. "The run API is the K5 action of the session journal
   (row 98): `journal_replays` is proved": `journal_replays` is about `Run`
   (`Laws/Run.lean:184`), while row 98's checked typed replay is "open, recommended" and the
   certificate-first `Typed.replay` "runs unchecked answers" (host boundary §3). "The OCaml
   engine needs a table-aware keyed entry path" is a feature; no face gets a theorem shape.
8. **R9** is right and is a clause of the milestone (row 107; addendum 3, H2). It omits "never
   halts" (`Stuck.unknownFiber/unknownScope/unknownRace`, row 52's other corollary).
9. **§0 and §2 of the note.** "Designed for an open signature" holds for operations, not for
   state: a new store family is not additive (point 2). "H is a relation from calls to replies"
   leaves out the host starting work: the machine has `runFork` and `runCallback` for new roots
   (`Machine/Fibers.lean:2181-2200`), but `Api.load` makes one root (`Api.lean:255-260`) and a
   `HostSession.Session` is indexed by one program (`Api/HostSession.lean:84`); the pass
   synthesis lists "several roots" as open (§7). The note's §8 cites post-Phase C §11 for
   "totality over the pinned surface", but no requirement states it (→ A6).

## 4. Proposed additions and changes (theorem shapes over the open signature)

Names are proposals. `Σ` is a signature with its tables, `H` a host relation the boundary
admits, `p` an admitted program, `t` a tape. None of these is claimed.

**A1. A lawful signature is one decidable judgment** (fixes R1's "lawful"; charter rules 2, 7).

```lean
structure AdmittedSig (Σ : Sig) where          -- runtime data, every law a Prop field
  lawful : LawfulSig Σ                          --   as AdmittedProgram is (Program/Admission.lean:89)
instance : DecidablePred LawfulSig               -- reduced by the kernel, never cbv or native_decide
def admitSig : (Σ : Sig) → Except SigRefusal (AdmittedSig Σ)   -- refusal at a path, with a reason
theorem admitSig_ok_iff : (admitSig Σ).isOk ↔ LawfulSig Σ       -- K4: located and complete
```

`LawfulSig` gathers clauses that exist or are ruled: row names (`LawfulTable`); registrable rows
(`checkTable`); what the reader needs of a signature (`LawfulSpelling`,
`Codegen/Read.lean:892`); no `int` (DI-67); no internal handle kind in a host answer or error
(row 97); no open template variable in a host row (pass synthesis K10); templates admissible and
well scoped (rows 42–43 plan §2d); every key a row requires has a service type (author receipt
C3); every service type closed and inhabited (DI-67's invariant, extended to the service table);
every atom's evaluation fits its scheme (rows 64, 74). Every requirement then quantifies over
admitted signatures.

**A2. The extension order and its transport lemmas** (replaces R2's "Σ ⊆ Σ'" and widens its
obligations). `Σ ⊑ Σ'` is DI-47's relation: declared appends only, no reorder, removal,
reframing or tag reuse; fresh names; receiver-qualified row identity (DI-64); positions in the
link table (DI-22).

```lean
theorem typeOf_mono (h : Σ ⊑ Σ') : typeOf Σ p = some τ → typeOf Σ' p = some τ
theorem replay_mono (h : Σ ⊑ Σ') (hH : H'.restrict Σ = H) (ht : t uses only Σ's rows) :
    obs (replay Σ' H' p t) = obs (replay Σ H p t)
theorem read_mono (h : Σ ⊑ Σ') : read Σ' (write Σ p) = some p     -- identity on the wire (DI-01, DI-05)
```

The extension points gain forms (DI-89), equations, and store families with their handle kinds
(row 81). Each extension brings, beside R2's list: its meaning clause (a `meaning_<op>`
equation, a protocol entry, or the host's contract; end state §4.1); a decision-source clause,
so nothing chooses off the tape (literature note Q7, INV-TAPE-1; clock and random are tape
decisions or a seed fixed at load, DB-14, row 83, catalogue note 7); its rc.112 cite and census
row; its target entry, checked by the rows lane (rows 68, 75); its `Fits` clause (host boundary
§4.4); an append-only wire tag; and for a store family, a handle kind with its `HandlesFit`
clause, a world table when it holds typed values, and a storage interface (machine state §7).
Probe: `Extension.lean`.

**A3. Library code inherits theorems** (W3–W9; the charter's *A base for higher-order APIs*;
row 79; DI-89; DI-11). Two forms, one rule: the theorem is about the expansion, on a named
observation and profile.

```lean
-- a composed module M (a DI-89 form, or a DI-11 composite program) and its contract C_M
theorem M_refines (hΣ : AdmittedSig Σ) (h : Σ_M ⊑ Σ) (hp : p uses M) (ht : t ∈ Profile_M) :
    C_M.observe (replay Σ H (expand p) t) ∈ C_M.allowed t       -- directed inclusion (R79)
-- a compiler c : Model → Eff, whose models are data (charter rule 6)
theorem c_bundle (hΣ : AdmittedSig Σ) (h : Σ_c ⊑ Σ) (m : Model) (hm : m.WellFormed) :
    typeOf Σ (c m) = some (τ m) ∧ meaning Σ (c m) = spec m       -- on a named fragment
```

`C_M` is the six-piece contract of post-Phase C §11.4, with a satisfiability witness and one
discriminating counterexample; the proof route is `Projects`/`Refines` (machine state §7, "what
is proved today"). The fidelity a composed module owes rc.112 — values relative to the tape,
schedule, or trace — is the owner's (catalogue §5 Q1; row 79 is ruled for the agreement shape,
not for each module's level). Typing alone is not enough: "Each composed module therefore needs
its own behavior law on a named profile, as DI-89 requires; typing is not enough" (machine state
§5); the tree has no program logic that gives mutual exclusion (catalogue §3, the trade-off).

**A4. Resources are released** (DESIGN-BASIS, required proof graph, "Scope and runtime";
DI-65; literature note §A item 5).

```lean
theorem release_atMostOnce (hΣ) (hp) : ∀ r, (finalizerRuns (replay Σ H p t) r) ≤ 1
theorem finished_released (hΣ) (hp) (h : (replay Σ H p t).outcome = .finished) :
    (∀ s, scopeClosed s) ∧ ∀ r registered, finalizerRuns r = 1
theorem frontier_keeps (hΣ) (hp) (h : (replay Σ H p t).outcome = .frontier) :
    ∀ s open, its releases are retained                         -- AGENTS.md: state kept for finalization
```

Host-owned resources add compensation at most once and no repeated host work (host boundary
§4.2; row 100, parked). Today only finite witnesses exist (`finalizerRuns`,
`Laws/Machine/Witnesses.lean:181-191`). Probe: `Outcomes.lean`, part 2.

**A5. Deadlock is named; liveness is relative to fairness** (papers review G6, G7; core math
§9, citing Lee et al., "Fair operational semantics", PLDI 2023; literature note Q7, INV-TAPE-2).

```lean
def Deadlocked (m : Machine) : Bool          -- every live fiber parked; no host call, timer or runnable work
theorem noReason_deadlocked (h : (replay Σ H p t).outcome = .frontier) (hr : reasons = []) :
    Deadlocked (replay Σ H p t).machine
theorem deadlocked_fixed (h : Deadlocked m) (hd : ¬ d.isInterrupt) : stepDecision d m = m
theorem row_live (hfair : FairTape interp fuel m t) : Eventually P (replay … t)   -- per named row
```

`FairTape` exists (`Laws/Machine/Scheduling.lean:432`); `Deadlocked` and `Eventually` do not.
Fairness stays a hypothesis (DB-03). If armed dispatcher work can leave the reason list empty,
`noReason_deadlocked` is false and `awaitDecision` must name that work; the statement settles
it. Probe: `Outcomes.lean`, part 1.

**A6. Every face is a named connection** (LCNF route §8; DESIGN-BASIS, "TypeScript target";
machine state §5, "keep four obligations distinct"; rows 28, 29, 31, 85, 101, 108).

```lean
theorem face_F (hΣ) (hp) (ht : t ∈ Profile_F) :
    obs_F (run_F p t) = ρ • obs (replay Σ H p t)     -- inside the profile
  ∨ run_F refuses p t                                -- outside it, intermediates included (row 108)
```

`ρ` is one partial bijection on identities, extended by first appearance (DI-81; dogfood
conclusions §8: equality relations between identities must agree; LCNF route §8 rule 4). Where
no theorem exists, the face carries its evidence tier as data — stamped, tested or proved (M1
kickoff §5.2) — and never claims more. The same requirement holds the print/read exact embedding
for every admitted Σ (system map §5, K2), typed lowering as a differential against the pinned
compiler (DI-49, DI-24, row 68), the observation as a projection of the machine
(`observe_inspect`, row 18) and an injective wire identity (`digest_inj`, rows 14, 18). On the
source side the authoring surface and the reader are elaborations total by refusal (system map
§5, K4: `explain_none_iff`, `authoring_scoped`, `open_total`) for every admitted Σ, and the
reader is total over the pinned surface: every export of the 137 modules has one of §11.1's
dispositions, and a source naming an undispositioned head is refused at its path (post-Phase C
§11.1; DI-89, "an unregistered head refuses by name"). The TypeScript face run on pinned rc.112
is the faithfulness lane (system map, layer 9): agreement on the named observation, or a signed
divergence such as `U-01`, never an unnamed difference (dogfood conclusions §2: a result-level
disagreement through identity).

**Changes to the others.**

- **R1.** Σ is `(rows, services, atoms)`, plus a type-declaration table only if nominal or
  recursive types are admitted; cells leave Σ. Lawful means A1. State the agreement theorems
  (`run_eq_meaning`, `loopAgreement`, `run_eq_ref`) over Σ beside `MeaningSound`/`LoopSound`;
  meaning theorems take Σ's atoms at the native evaluator, or a premise that each atom's
  evaluation fits its scheme.
- **R3.** Say structural (`record`, `variant`) or nominal (`foreign`). Add collections with
  their key, duplicate and order policy ("container laws fix their hidden parameters once",
  machine state §5); equality (DI-35's `Val.eqAt`); numeric carriers, or their refusal by name
  (language cut §2); inhabitance, `∀ admitted τ, τ.normalize = never ∨ ∃ w v, Fits w v τ`
  (DI-67 restated over row 96's `Fits`); assignability agreement for each new constructor
  (row 68).
- **R5.** Add minted keys that a term cannot spell (`PROV-FB-KEY-FORGERY`; papers review G5);
  reference keys and Config (provision algebra §6, `KeyKind`; Config D1–D5); `build_total` and
  `lower_refines_build` in the tree (provision §§2–3); scope elimination (DI-63); context
  services validated at any runtime-to-`Fits` bridge (side audit, "ContextBridge"). Leave the
  threading to R1.
- **R6.** Name H as the tree's own host specification: `HostSpec`, five relations over an
  abstract host state (`Program/Profile.lean:178`), lawful by `LawfulHostSpec` (`:198`; DI-65),
  rather than a new notion. Add the converse, "every semantically valid, representable reply is
  accepted" (host boundary §4.5); declared equations of a host row as premises `H ⊨ E`
  (literature note Q11: correctness of a handler is relative to the declared theory); the
  algebraic row meaning (DI-69); inbound entries, by one of two shapes: each host-started root
  is a recorded command typed at a declared entry type, so the typed state covers several roots;
  or inbound events are only replies to outstanding pulls (DI-11's kernel) and host-started
  roots are refused by name. Which one is the owner's. Write row 100's lifecycle shape now, even
  while parked.
- **R7.** As a theorem: `resolve Σ ref = some (entry, caps) → HasTy Σ caps.types entry.body
  τ_ref`, with the entry's signature and capture layout fixed at resolution ("a digest alone
  does not", machine state §5), and the typed state extended to stored behaviours with their
  lifetime (row 82; catalogue §3 item 5; literature note Q12, a capture is closure conversion
  over a first-order code pointer).
- **R8.** Replace by A6; record row 98 as open.
- **R9.** Add "never halts" (row 52) beside the exit clause; both are clauses of the milestone.

**Open questions no row tracks** (not requirements yet): sharing, for which there is no
procedure form (dogfood 6, F21; end state §8); a program logic (DESIGN-BASIS "Logic" edge is
empty; DI-10 defers the bind law); durable journals and idempotency for persistence, workflow,
eventlog and cluster (host boundary §4.2, last bullet).

**Rows to propose** (the coordinator owns `decisions.md`): A1 lawful signature; A2 the
extension order (DI-47 applied to Σ); A3 module contracts as behaviour requirements, with the
fidelity level per module; A4 resource release; A5 deadlock and fairness; A6 faces as
connections; R6's inbound-entry choice.

## 5. Probes (tested)

Two files in this folder, each with a red control that flips the claims it rests on. Finite
checks only; no theorem is stated, so no axiom line is printed. Command, from the repository
root, for each file `F`:

```sh
bash /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh \
  lake env lean -M6144 -DwarningAsError=true /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-30-model-probe/completeness/F
```

| file | exit | what it shows |
| --- | --- | --- |
| `Outcomes.lean` | 0 | A checked program whose root awaits a deferred nothing completes stops at a frontier with no reason; the host protocol reports `parked`, as for a sleeper (whose one reason is its timer); a clock advance and flushes leave it there; one interruption finishes it. A scope's release is owed while its body is parked (the cell still holds 0) and has run after one interruption (the cell holds 1). |
| `OutcomesRed.lean` | 1 | Exactly two guard errors, at the two flipped claims (line 51: the deadlock's reasons expected non-empty; line 91: the release expected to have run at the frontier). |
| `Extension.lean` | 0 | Appending a fresh row keeps the type and the exit of an acquire, read and close program; inserting the row in front makes it fail to check; appending a clashing name makes `LawfulTable` false; the certificate exists at both tables as different types. |
| `ExtensionRed.lean` | 1 | Exactly one guard error, at the flipped claim (line 72: insertion expected harmless). |

The first compile of `Outcomes.lean` failed on a missing `import Effect4.Api.HostProtocol`; the
results above are after that fix. The files' digests are in §6.

What the probes do not show: anything about all programs or all tables. They make the gaps in
§3 concrete (no reason for a deadlock; positions, not names, identify rows) and keep red
controls for A2 and A5.

## 6. Receipt

- **Base and head.** Read at `7cae243a` (`refactor/phase1-phase3`); the note under review is at
  that commit. No commit, no checkout, no `git add`.
- **Files written** (all under `docs/research/2026-09-30-model-probe/completeness/`, gitignored):
  `note.md`, `Outcomes.lean`, `OutcomesRed.lean`, `Extension.lean`, `ExtensionRed.lean`.
  `git status --short` printed nothing afterwards.
- **Commands.** Reads (`sed`, `grep`, `awk`, a Python tabulation of the two registers); the
  compiles of §5 through the lock, each file at least twice (the first `Outcomes.lean` run
  failed on a missing import). No `lake build`, no `make`, no generator. The Codex worktree
  was not read.
- **Digests.**
  `55d1fabe83af156a3d98da87ac0143052ca13205d75d04fc94ab243dc3fc04e1  Outcomes.lean`;
  `21cb85ef594ee2ed6d3cc77c90d8fa8ae3290165a7089051d59c7a053357f4bf  OutcomesRed.lean`;
  `d3cd1bb3d5f933145ba1a94ee19af329f4d3d3940c8a396033b3b5caa238e8a8  Extension.lean`;
  `29e3f7e1d2c12633bbfc33c588262dccbb814cc1b89f4322f101df014e9b72b4  ExtensionRed.lean`.
- **Axioms.** No theorem was stated, so none was printed.
- **The note's own counts, re-checked in passing** (tested by grep, reading for the lines): 188
  explicit `(sig : Signature` binders under `Laws` (219 with the implicit ones); 89
  `nativeSignature` uses in 15 `Laws` files; the ten typed-state uses (`Typed/Admission` 1,
  `Assembly` 2, `Residual` 3, `ForkSource` 4); admission at `Program/Admission.lean:90, 108,
  191`; `LoopSound` at `effTy nativeSignature` (`:298`, `:307`); the Ref rows still at `number`
  with `FnName` (`Program/Native.lean:56-63`, `:91-99`). All hold.
- **Evidence classes.** Every coverage cell is *reading*. The grep results (no `Deadlocked`,
  `Eventually`, `effTy_congr`, `Signature.Extends`, `build_total` declaration) are *tested*
  searches, bounded by the patterns tried. The probes are *tested* on one program each.
- **Open.** Every A-item and R-change of §4 is a statement to write, not a result. A5's
  `noReason_deadlocked` may be false if armed dispatcher work can leave the reason list empty;
  that is the first thing to check. The fidelity level of A3, the inbound-entry choice of R6,
  and whether nominal or recursive types enter Σ are the owner's.
