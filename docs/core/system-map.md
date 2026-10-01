# The system map: what Effect4 is for, how it works, how it is organized

The authority for the frame: the goal, the layers and their owners, the sorts with their one
representation each, the kinds of arrow between them and what each owes; since 2026-10-01 also what
a full program is (§1.1) and the requirements it must satisfy, with their status (§8). Written
2026-09-30 at `be15b062`. It replaces the former `docs/core/ontology.md`, whose formal frame (its §5) is carried here and
whose dated 2026-09-17 sections are kept as history in
`docs/research/2026-09-17-ontology-and-do-now-probe.md`.

Status words: **proved** means a theorem at the trust ceiling `[propext, Quot.sound]`;
**exists** means code without that theorem; **open** means planned, with its decisions row.

## 1. The goal

The entry point is the Lean model of Effect's fiber machine: Effect's runtime reified in Lean as a
general model with defined semantics. Its definitions (the API) are kept apart from its theorems,
so everything built on it builds on the verified core. Around it:

- **Programs are typed, first-order data.** One canonical tree that can be inspected as a graph,
  stored by its digest, and folded over.
- **The model runs natively.** The same Lean machine is compiled through LCNF into OCaml today.
  WASM is next, most likely through that same generated OCaml.
- **Code generation and read-back.** Programs print as Effect TypeScript and read back.
- **Ergonomic APIs for running full Effect programs,** and authoring through MCP tools.

The power is Effect everywhere with one defined semantics. Every behavior the model has cites the
line of the pinned Effect rc.112 source it transcribes, and proofs connect the faces, or the gap is
written down with its decisions row.

**Scope discipline (owner, 2026-09-30).** The route above stands. A finding is fixed as a bounded
repair that keeps the verified claims true, not by redefining the route. A large contract is
written down and parked until a need arrives.

### 1.1 What a full program is (2026-10-01)

A full program is a closed term over a signature `Σ = Σ_core ⊕ Σ_app`, run against a lawful host
specification `H`, with its load inputs, under one root. What a program must satisfy is §8; this
paragraph says what the words mean. Sources: the model probe
(`docs/research/2026-09-30-model-probe/synthesis.md` §2.1) as Codex's audit amended it
(`docs/research/2026-09-30-codex-review-model-probe/audit.md` §2), and decisions rows 111–118.

- **`Σ_core` is the closed inductives the language owns:** the `Eff` and `Ty` constructors, the
  built-in `NativeOp` rows, `SyncOp`, `FiberOp`, `NativeAtom`, `Err`, `Defect`, `HandleKind`. It
  grows only by constructor appends under DI-47's finite gate over the retained baseline (read by the mirror census's configuration; no comparator has run since `243ca0dd`)
  (`Test/fixtures/baseline/`, rows 56 and 61): a finite gate and a discipline, not a theorem.
- **`Σ_app` is data an application supplies:** the row table and the service table (row 111).
  Later, and only if admitted, nominal data declarations (row 2; DB-15) and code entries (row 82).
  "Lawful" is one decidable check with a located refusal, whose evidence travels with the program
  source so that every milestone statement quantifies over lawful sources (row 114). Service
  carriers are keyed by service code (row 113).
- **Not in `Σ`:** cells, which the world types at allocation (row 44; the generic rows are core
  template rows, rows 42–43), and structural records and variants, which are growth of the type
  language (DB-15's amendment, row 2).
- **Extension is conservative only under named obligations** (C1–C8, row 111): declared appends
  with fresh, unreserved names, never an insertion or an override. A published program and a
  session are pinned to their complete assembled table (row 115: no `Package.install` order
  appends on the assembled table; `HostSession.start` refuses another table). The host-row
  protocol entry carries the row's domain bit so that typing is monotone in the table (row 116).
- **`H` is the tree's own `HostSpec`,** lawful by `LawfulHostSpec` (`Program/Profile.lean`); the
  empty relation is "no host". The lane is parked (rows 95–101) except the interim handle rule
  (row 97). M6's premise is a predicate on tapes (row 95), not a host relation, so the lane brings
  its own obligations when it unparks (`host-boundary.md` §4.5).
- **A run has load inputs** (the environment snapshot and the seed; the clock is a tape decision,
  DB-14) **and one root.** Host-started roots are refused by name; the recorded-entry route for a
  server-shaped program is written down in `host-boundary.md` and parked.
- **"Signature" names three things** (row 142): the syntax signature (`binders.json`, `LayerView`:
  the constructors of `Eff` as data for the generator); the language signature `Σ = Σ_core ⊕ Σ_app`
  of this section; and the typing signature `Signature Op` (`Program/Typing/Rules.lean`) that
  `nativeSignature` (`Program/Native.lean`) builds from `Σ`'s tables for the checker.

## 2. The layers

Status here is the layer's; the requirements' status is §8's, the one owner (row 142).

| Layer | What it is | Owner | Status |
| --- | --- | --- | --- |
| 1. Programs as data | One program representation, `Eff`: a first-order tree with a digest, stored by content, printed and read back. Names are data; no closures, promises or runtime objects in program syntax. | §4 below; `AGENTS.md` vocabulary | exists |
| 2. Types and certificates | `Ty`/`EffTy` and one checker, a fold that certifies a type or refuses with a located reason; certificates by kernel decision. | `Program/Checker.lean`; `docs/core/traversal-census.md` | proved sound and complete against `HasTy` at every path; `explain = none ↔ wellTyped`. `HasTy`'s layer rules disagreed with the runtime in two places; rows 104 and 105 are repaired (2026-10-01, `E4-PROV-CE-005` and `-006`) |
| 3. Meaning | One denotation; a reference machine for proofs; the native (frame) machine for execution. | `docs/core/machine-state.md` | proved: meaning soundness; `run_eq_meaning` (straight fragment); `loopAgreement` (looped); `run_eq_ref` (the two machines, **empty host table only**) |
| 4. Choices as data | Every scheduling, timing and host-answer choice is a decision; a run's journal replays it. | `Run.lean`, `Api/Runner.lean` | proved: `replay_unique`, `journal_replays` |
| 5. The typed-state guarantee | A checked program never reaches a malformed state, and every fiber finishes at its type. | `docs/core/post-phase-c-synthesis.md`; `Laws/Program/Typed/` | slices 1–5 proved (world, admission, protocols, stack walk, delivery, assembly); M5–M7 open. As stated, M5 and M6 are false even on programs that use no host (four registered counterexamples); the bounded repairs are rows 95–96 and 104–107, all landed by 2026-10-01 (row 107 part one; part two is row 117). The typed state now carries the scheduler's queue and observer facts (row 106, `Typed/Scheduler.lean`), a fiber typed by its queued finish with current code inert on a halted machine (row 133), and `ExitOk` at every typed exit position; `StepPreserves` is stated at the dispatch premise `m.stuck = none`; the M6 ledger stands at 20 open, 0 proved. The formal pass (2026-10-01) found four statement defects in M5–M6 (rows 134–137), each repaired as a statement by seats A–C of the landing plan |
| 6. The host boundary | Host services are rows in a table. A program's call parks a fiber; the host answers through one keyed session that checks each reply and prepares it. | `docs/core/host-boundary.md` | exists: session, envelope, admission, preparation. Next: the interim handle rule that closes the live hole (row 97). The full host-services contract is parked until needed |
| 7. State and storage | The machine's state families, each owned by one of six storage interfaces with laws; facts fixed at creation in append-only ledgers; derived views, such as a handle's declared type, computed from ledgers and the checker. | `docs/core/machine-state.md` §7 | arena laws and `Projects`/`Refines` proved; the fork ledger landed 2026-10-01 (row 91; `Laws/Machine/ForkLedger.lean`, written by `spawn` only, the old per-fiber field gone); the trace agreement through it proved (row 93, 2026-10-01); the registry and further storage instances are parked (rows 97, 101) |
| 8. Compilation | Three compilations: a program to the machine's first-order runtime code (`compileEff`); the Lean machine itself to OCaml through Lean's LCNF (OCaml is made only from LCNF); a program to and from Effect TypeScript. Each stage is a named connection with its own evidence. | `docs/core/lcnf-route.md` §8 | printer/reader laws and completeness over the template table proved; the OCaml engine checked by differential runs (finite); number policy mixed; rows 28/29/31 open |
| 9. Faithfulness to Effect | The pinned vendor source, the runtime census and its coverage report, the truth harness against real Effect runs, signed divergences (`U-01`). | `docs/RUNTIME-COVERAGE.md`, `docs/UPSTREAM-BACKLOG.md` | exists; coverage is quoted only from the report |
| 10. Authoring and use | A named authoring surface elaborated once into `Eff`; a certificate-first API; the MCP face after LCNF, by the owner's order. | `docs/core/api-surface.md` | exists in part; ergonomic run APIs and MCP authoring are the next expansion |

**How the pieces connect.** A program comes in, from the authoring surface or read from
TypeScript. The checker certifies it. The machine runs it, reference for proofs and native for
execution, with explicit choices, and with host calls through the keyed session. The same machine,
compiled through LCNF, runs natively in OCaml. The printer writes the program back as Effect
TypeScript. Every arrow is one of the kinds in §5 with its obligation met, or it is listed as open.

## 3. Where it is going (the owner's route, 2026-09-30)

**Now: finish the foundation, small.**
1. **Slice 6's last item:** the fork ledger and the trace agreement through it, both landed
   2026-10-01 (rows 91–94; `docs/research/2026-09-30-origin-ledger-and-step-invariants-plan.md`).
   Slice 6 is complete.
2. **Three bounded fixes found on 2026-09-30:**
   - M6's finish line covers runs with no host answers (row 95; landed 2026-09-30);
   - the proof's value check looks inside pairs, Results and exits (row 96; proof side only;
     landed 2026-09-30 as `Fits`);
   - host rows may not answer with internal handles (fiber, cell, deferred, scope, context), the
     interim rule of row 97 (`host-boundary.md` §5); Codex's repair is checked and lands with
     brief addendum 4.
3. **M5–M7:** the typed-state guarantee, the proof that makes "verified runtime" complete on runs
   without host answers. Row 99 says what is claimed until the host lane lands. The design pass
   of 2026-09-30 (`docs/research/2026-09-30-pass/synthesis.md`) found M5's and M6's statements
   false even on programs that use no host, so four more bounded repairs come first (ruled
   2026-09-30, with Codex by brief addendum 2):
   - a layer's body is built in the environment it was checked in (row 104);
   - a layer's value must fit its key's type (row 105);
   - M6's typed state keeps tokens fresh (row 106);
   - an exit clause, or an explicit disclaimer, for "never goes wrong" (row 107).

   Row 96's judgment also reads liveness from the world's tables (landed). The generic lifts are
   landed (row 110). All four repairs landed by 2026-10-01 (Codex: F at `d20f3292`, G at
   `57c93ba4`, H1 at `d554cd71`, H2 part one at `abc7b124`; merged `0c534f06`), with row 39's
   Schema wipe in the same merge; the M6 ledger stands at 20 open, 0 proved; H2 part two is row
   117, and H1's halt extension of row 133 awaits the owner's ratification.

**Next: expand on the proven route.**
4. **More of Effect, one module at a time, queues first.** Each is modeled in Lean over the
   machine's existing pieces (references, deferreds, wake lists) by DI-89's routes, then generated
   to OCaml through LCNF, and printed and read back as Effect TypeScript.
5. **Ergonomic APIs for running full Effect programs.** These include the checked typed replay over
   the session journal (row 98), and authoring through MCP after LCNF (the owner's order).
6. **WASM,** through the generated OCaml first rather than a new backend. Not yet checked.
7. **Numbers to DI-56's profile** (row 108). Today one checked program gives three different
   answers on Lean, OCaml and TypeScript, and none refuses. The rule: each face equals the exact
   Lean reference inside its range and refuses outside it. The owner places it, before WASM at
   the latest.

**Parked until needed** (written down, not scheduled):
- **The full host-services contract** (`host-boundary.md` §4; row 97's route part, row 100): the
  handle registry beyond fibers, the reply lifecycle and resource ownership, the 20-constructor
  boundary matrix.
- **Storage replacements** (row 85) and the composition of stages (row 101).
- **Proofs of the compilation stages** (rows 28/29/31).
- **FloatLib,** when a JavaScript-number type is added for durations, clocks and random numbers
  (`lcnf-route.md` §8).

## 4. Sorts: one representation each

Each syntax sort has one owner, and its signature is data the generator reads.

| Sort | The one representation | Signature as data | Maps out |
| --- | --- | --- | --- |
| program | `Eff` (`Program/Eff.lean`) | `binders.json` → `LayerView` | `cataFam`, unique by `hom_eq_cata_eff` |
| type | `Ty` (`Program/Ty.lean`, 20 constructors); types up to `≡N` (equal normal forms) are the checker's types, `Ty/≡N ≅ CTy`, ordered by `Ty.subN` (row 137) | its generated family description | `cata_ty` (`Program/Fold.lean`) |
| term | `Term` (`Machine/Term.lean`) | generated | `cata_term` |
| value | `Store.Val` | its inductive; `Kind`/`Shape` classify it | `cata_val`; `Canonical` gives exact embeddings |
| schema carrier | `Representation` | its inductive | embeddings from `Ty` (row 6) |
| run | `List Command`, the free monoid on `Command` | the `Runner` group | the monoid action (§5, K5) |

TypeScript syntax (vendored) and LCNF (Lean's) are external sorts, reached by the printer and
reader and by `translateClosure`.

At a fixed input and budget policy, observing and stepping a state gives a coalgebraic view,
`S → Ω × S^Command`. That view does not make a state stored data. The journal acts by replay:
`replay_unique` proves the action unique from its empty, append and singleton equations, not that
different command words give different machines. `journal_replays` reconstructs a run, including
the journal it keeps. Serialization and resumption need their own contracts. `obs` is not
injective, and the tree does not claim it: "equal observations imply equal runs" would be
injectivity of the behaviour map, which nothing needs (row 146).

**Value fits type.** The runtime has one executable check, `Val.hasTy`, and no types in values.
The proof side has one judgment, `Fits` (`Laws/Program/Typed/Membership.lean`): constructor-complete
over the actual encoding, shape and handle evidence in one derivation, with its generated fold
connector; it replaced `StrongValue` on 2026-09-30 (row 96, landed). Declared types of handles come from
creation evidence and the checker, not from values (row 97). Anything else that checks a value
against a type is a leak by §6.

## 5. Arrows: five kinds and what each owes

| Kind | Shape | Obligation | Proved instances |
| --- | --- | --- | --- |
| K1 fold | `cataFam alg : F → A` | being an algebra; uniqueness is free | the generated algebras; the checker is one `Except`-valued fold |
| K2 exact embedding | `write : A → F`, `read : F → Option A` | total on its domain; `read (write a) = some a`; `read v = some a → v ≡ write a` modulo a named normaliser (a lawful prism, a partial isomorphism with a total forward map) | `Canonical` (`ofVal_toVal`, `ofVal_exact`); `read_print`, `read_exact` on the readable domain; the store, node and program byte codecs; `Config.Val`. `Ty.schema`/`ofSchema` and the JSON codec are retractions until their exactness lands (row 128; the JSON normaliser is key order) |
| K3 simulation | two behaviours, one observation, on a named fragment | the fragment named by exclusion or policy; the observation named; the statement is an equal-observation theorem (adequacy against the meaning, semantic preservation against the reference) proved through a relation preserved by every step | `run_eq_meaning` on `Straight`; `loopAgreement` on `Looped`; `run_eq_ref` at the empty table, through the book's `ReplayRel`/`BMeans`; `Refines` and `Projects` (`Laws/Machine/Refinement.lean`) as the relation kinds |
| K4 located refusal | `Src → Except Refusal F` | the refusal is located and complete: `explain = none ↔ wellTyped` (a sound and complete decision procedure for the declarative judgment) | `explain_none_iff`; `admitProgram_certificate` and `admitted_unique` (`Laws/Run.lean`). `elaborate_scoped` (the elaboration's fact; the tactic `authoring_scoped` is its user) and `open_total` (a totality fact) are facts about K4 arrows' outputs, not K4 laws |
| K5 monoid action | `List Command × S → S` | `replay_unique`, `journal_replays` | both |

A hand traversal that is not a fold is an exemption listed by name by `#traversal_census`, whose
instrument (`Laws/Auto/Traversals.lean`) and document (`docs/core/traversal-census.md`) are the
census's one owner (row 142; the coherence principle is the dated record of 2026-09-17). Two folds agree when their algebras do; no pairwise agreement
proof is written. A read without exactness is a widening, not an embedding. A simulation is never
called "equivalent" without its observation.

## 6. Coherence, composition, generation

**Coherence is counted per sort.** The principle allows one free object, plus any number of K2
embeddings with all three laws, plus folds, which are views rather than representations.
Anything else is a leak. The census is owned by `docs/core/coherence-principle.md` and
`docs/core/traversal-census.md`.

**Composition at `Eff` is scope-correct, not raw.** For a signature and a fixed context Γ,
programs are checked at Γ ++ [A] with answer B and an error and service grade. Variables are
absolute positions, and a successful bind appends its answer. The proposed operations are:

```text
idAt Γ          := succeed (var Γ.length)
composeAt Γ p q := bind p (q.weaken Γ.length)
```

- **Typing closes.** It is derived from `HasTy.bind` and `hasTy_weaken`, with the error join by
  `Ty.join` and requirements by union.
- **Raw bind is not categorical composition.** Well-scoped pure examples return different values
  after raw reassociation.
- **The laws are future work.** Identity and associativity are to be proved for `composeAt` at a
  named meaning, over fitting environments and stores.
- **Not yet a theorem.** A category or graded Freyd structure remains a proposed organization.
  The witnesses are in `docs/research/2026-09-19-critique-response.md` §2.

**Generation is a fixed point.** Stage 0 is the tables (`binders.json`, `manifest.json`, the
template table, `cases-policy.json`); stage 1 is the generated Lean. The committed tree must be a
fixed point of the generator (`check-gen`). Every generated declaration is a fold or an embedding
of §5, which keeps the generated sugar inside the proofs.

## 7. Evidence discipline

- Every claim names its theorem or its finite probe. A finite check is reported as one.
- The trust ceiling is `[propext, Quot.sound]` for every `Effect4.*` and `Test.*` declaration.
- Runtime coverage is quoted only from `scripts/report-effect-runtime-coverage.sh`.
- A refusal is located. A gap is written down with its row, never hidden behind a `True`.
- Probes and receipts live in `docs/research/` as evidence; the authority documents cite them.

## 8. What a full program must satisfy: the requirements (2026-10-01)

Each requirement is a theorem shape over the open signature of §1.1, not a capability. **Status
lives in this table only**; a basis row or a note that needs it links here. The shapes and their
pedigree are in the model probe's synthesis (§2.2, §3.1) as Codex's audit amended them (§1–§6);
the detail of each lives with the owner named. Status words are the document's: proved, exists,
open.

| Requirement | Shape, in one line | Status at `0c534f06` | Owner of the detail; rows |
| --- | --- | --- | --- |
| R1 the signature is a parameter | `AdmittedSig Σ` with `admitSig_ok_iff`; every milestone statement takes it | typing proved over any signature (`check_sound`, `check_complete`); admission, the typed state (13 places) and the faces (22 lines) pinned to the built-in signature; meaning, loop and run soundness carry over by corollary (proved) | this map §1.1; rows 21, 111, 114, 118; the Σ_app slice of the M5–M7 brief, after G. R1's exception (row 138, ruled 2026-10-01): M7 is declared at the empty row table, over the service half of Σ_app; the table-aware agreement (DI-57's host-free part) is R6's. M7 is declared as scope `M7` in `Laws/Program/Typed/Assembly.lean` over `M7Fragment` (lawful source, empty row table, checked, closed, answer-free tape); its route is proved (`m7_of_ledger`; seat C, merged `38686e44`). M7's claim is about the frame machine at the empty host table on answer-free tapes with observation `obs`; the OCaml engine is outside it until row 28 is ruled, and nothing in M7 is "verified lowering" or general host safety |
| R2 extension is conservative | C1 syntax, C2 meaning, C3 checker, C4 protocol typing, C5 world, C6 local lawfulness, C7 representation, C8 forms, over DI-47's relation on Σ_app | C1 proved for binary injections; C2 proved for the generic handler, host rows operational until DI-69; C3's monotone half proved (`R2Probe.lean`), reflection open; C4 proved for the generic judgment, open for `TypedProg`; C5 red controls proved; C6 open; C7 conditional on row 115 (row 105 landed 2026-10-01); C8 open per form. The binary sum is a coproduct of free monads (`sum_is_coproduct`, `Laws/Effects/Sum.lean`, merged `a561d604`), not a tensor (`sum_not_tensor`, red); C4 in both directions for the generic judgment (`Typed.inl_iff`, `Typed.inr_iff`); C1 vacuous for Σ_app (DB-01) | DB-01 (the obligations); rows 111, 115, 116; DI-47, DI-69, DI-22, DI-64 |
| R3 data | the type language closed under records and variants as `Ty` growth: records by one constructor over a field list in canonical name order (row 119), variants with row 130; each constructor brings its `Fits` clause, embeddings, folds, assignability and inhabitance | DB-15 amended 2026-10-01: records by row 119's ruled design, the slice after M5–M7; rows 120–132; recursive types are row 124 (open); inhabitance is row 127 (seat A) | DB-15; rows 119–132; DI-62, DI-67; post-Phase C §11.2 W1 |
| R4 state | the world types every cell at any type; rows as templates; a function row takes a binder term | the world ruled and defined (row 44), its order laws proved; steps 3–5 open; the native spellings read as cells at `nat` (row 96 D2) | `machine-state.md`; rows 42–45, 55, 96 |
| R5 services | the service table in Σ_app, read by the typed state as a static world component; a layer's value fits its key; requirement rows grade programs; code-valued services through R7 with a capture law | open: row 105 landed 2026-10-01 (G, `57c93ba4`); rows 112–114 ruled; owed `build_total`'s restoration and `lower_refines_build` (row 147), reference keys and Config, minted keys, context validation at any runtime bridge | `machine-state.md` §5; the provision algebra; DB-12, DB-17; rows 51, 82, 90, 104, 105, 112–114, 147 |
| R6 the host | `H : HostSpec` with `LawfulHostSpec`; receipt and application theorems and their converse; DI-57's table-aware reference relation; DI-69; a world extension meeting C5; a retirement edge; per-row cancellation; one root | open, parked by the owner (2026-09-30); the interim handle rule landed on Codex's branch (row 97) | `host-boundary.md` §§4.2, 4.5, 4.6; rows 95–101; DI-57, DI-58, DI-65, DI-69 |
| R7 retained behaviour | `resolve_typed`: a resolved code entry is typed at its reference's type, with capture layout fixed at resolution and identity by allocation or structure | open | `machine-state.md` §5; row 82; the stateful catalogue §5 Q4 |
| R8 runs and faces as named connections | inside a profile a face's observation equals the reference's up to one identity bijection; outside it the face refuses, intermediate values included; the profile is data (row 79) | printer and reader laws and the fragment simulations proved; typed lowering open; numbers open (row 108); K2 holds on the readable domain, which excludes annotated loops (DI-91) | `lcnf-route.md` §8; this map §5; rows 79, 98, 101, 108; DI-49, DI-56, DI-81 |
| R9 never goes wrong | `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex` at every typed position; `NoShapeDefect` reads the core `Defect` alphabet and `ty.requires` only | ruled (row 107); part one landed 2026-10-01 (`abc7b124`, merged `0c534f06`); part two open (row 117: a saved frame transports `missingService` across a change in the requirement row); "never halts" is declared as M7c (`M7.never_halts`) and follows from `J` (`machineTyped_not_halted`), so from M5 and M6 (`m7_of_ledger`, proved); its content is the halting arms of the eighteen command proofs (row 139's census) | `Laws/Program/Typed/`; DB-16; rows 52, 107, 117; `E4-TYPED-CE-007` repaired, `E4-TYPED-CE-008` seeded |
| R10 library code inherits theorems | a composed module's law is `Agrees profile module expansion` (row 79); each form owes a typing lemma, one behaviour law, lexical well-scoping, reader admission, a readable expansion (C8) and a stable identity; a composite owes post-Phase C §11.4's contract by a stuttering route | ruled (DI-89, row 79), undelivered: no form has a behaviour law; none of DI-89's named forms exists; DI-39's six rows not landed | `machine-state.md` §5, §7; DI-89, DI-11, DI-39; row 79 |
| R11 resources are released | at most once per registration, counted by identity; exactly once in close order over closed scopes and structured regions, with a completed-cleanup receipt (the closed bit is set before cleanup runs); state retained at frontiers | one close proved (`ScopeMachine.runState_complete` and siblings); the whole run open; a scope a finished run leaves open is an observation (rc.112 does the same) | `machine-state.md` §7; DB-07; DI-65; `host-boundary.md` §4.2 |
| R12 frontiers name what they await | `Deadlocked` requires nothing armed; stability stated over the allowed internal decisions with a named progress observation, not as a whole-machine fixed point; liveness under `FairTape` with row-specific enabling; divergence by compatible prefixes (DB-03) | open; armed dispatcher work is invisible to the frontier today (`awaitDecision_iff`); INV-TAPE-1 and INV-TAPE-2 are defined in `docs/research/2026-09-07-lit-papers.md` Q7 (tracked since seat H, `1efb963e`), recorded as proposed in DB-03, unruled (the model probe's D7); M7c leaves a frontier as the only unfinished end of an answer-free run at the empty host table once the ledger closes, and says nothing about what the frontier awaits | `machine-state.md` §7; `Laws/Api/Frontier.lean`; DB-03 |
| R13 a run's inputs are data | a congruence law: equal recorded program, signature, profile, budgets, tape and load inputs give equal replay observations; supplied values fit the admitted load requirements | designed (the 2026-09-10 Config route B), not implemented; restates M5's `typedState_load` when Config lands | `host-boundary.md` (the header); `Program/Config.lean`; rows 51, 83 |


## 9. The glossary: the tree's names in the literature's terms (2026-10-01)

One row per named object: its site, the literature's name for it in one line, the mark of the
note that read the literature (**read** with the note; **by name**; **assumed**; **standard**),
the law that makes it that thing, and the correction the formal pass applied
(`docs/research/2026-10-01-formal-pass/synthesis.md` §5, the organization seat's table as its
verifier and the other verifiers corrected it). Sites are at `dceae006`; the coordinator re-checks
them with a probe at each landing commit. `AGENTS.md`'s vocabulary and the basis (DB-16, DB-17)
link here and copy nothing (row 142).

| Tree name (site) | Literature name, in one line | Mark | The law that makes it that thing | Correction applied |
| --- | --- | --- | --- | --- |
| `Eff` (`Program/Eff.lean:264`) | initial algebra (term algebra) of a binding signature; variables are positions | by name (coherence principle: GTWW 1977; Fiore, Plotkin, Turi 1999) | `hom_eq_cata_eff` (`Program/Fold.lean:1270`), `cata_build`, `build_view` | — |
| `cataFam`, `cata_eff` (`Program/LayerView.lean:414`; `Fold.lean:1104`) | catamorphism, the unique algebra map out | by name (MFP 1991; Hutton 1999) | `hom_eq_cata_eff` | `fold_of`'s pairing is a paramorphism (Meertens 1992, by name) |
| `Program S` (package `Algebra/Program.lean:33`) | free monad on a signature | read (Plotkin and Pretnar §1, §5, lit-papers Q11) | `program_is_free` (`Algebra/Universal.lean:98`) | — |
| `Signature Op` (`Program/Typing/Rules.lean:47`) | the typed presentation of an effect signature: arities and coarities, atom types, service carriers, domain | by name (operation signatures, Plotkin and Pretnar, read via Q11) | `check_sound`, `check_complete` over every signature (`Laws/Program/Typing/CheckSound.lean:37`, `:361`) | "signature" names three things: the syntax signature (`binders.json`), the language signature Σ = Σ_core ⊕ Σ_app (§1.1), and this typing view built by `nativeSignature` (`Program/Native.lean:316`) |
| Σ_app, `RowTable` (`Program/Native.lean:82`) | the application's signature as data: operations by position, service constants sorted by their code | by name | owed: C1–C8 (rows 111–116) | C1 is the identity for Σ_app |
| `Ty` (`Program/Ty.lean:37`) | initial algebra of a ground signature: first-order types with unions, literals, a top and a bottom | by name (TAPL ch. 15–16) | `sub_refl`, `sub_trans`, `sub_antisymm_canonical`, `normalize_idem`, `sub_not_complete` | — |
| `subN` (not yet named; read at `Typing/Rules.lean:114-117`, `HasTy.lean:186-187`) | the checker's order: `sub` after `normalize`; its kernel is equality of normal forms, so `Ty/≡N ≅ CTy` | standard | `subN_equiv_iff` (probe) | name it; atom arguments use raw `sub` (TY-02 partly) |
| `CTy` (`Program/Ty.lean:842`) | bounded join-semilattice; `join` is the least upper bound | by name (TAPL §16.3) | `instIsPartialOrder`, `instLawfulOrderSup`, the join laws (`Laws/Program/TypeAlgebra.lean:1096-1121`) | meets are not claimed; "not a lattice" dropped (TY-17 partly) |
| `inhabited` (owed, row 127) | the emptiness test of a regular tree type, a fold | by name (TATA) | `inhabited_of_fits`, `inhabited_of_hasTy` (probe) | — |
| `Fits` (`Laws/Program/Typed/Membership.lean:87`) | the world-indexed value interpretation `V⟦τ⟧(W)` of a Kripke model for first-order references; a store typing | by name (TAPL §13.4; Ahmed 2004; Ahmed, Dreyer, Rossberg 2009) | `Fits.eq_cata`, `fits_mono`, `fits_sub`, `fits_hasTy` (type erasure to `Val.hasTy`), `fits_live` | "logical relation" is loose (no arrow clause); no step indexing because worlds hold syntactic types read as declarations; `Effect4.Program.Fits` (`Laws/Program/Typed.lean:309`) is a different judgment (an environment fits pointwise): rename it `EnvFits` |
| `World` (`Laws/Program/Typed/World.lean:52`) | a Kripke world, here a store typing: Γ fibers, Π deferreds, Ρ cells, Θ tokens, ordered by extension | read (de Vilhena §4.3, Jacobs Prop. 6.2.4, papers review A3) | `World.le` order laws; `Typed.mono` (`Laws/Effects/Protocol.lean:57`) | `Typed.World` extends `Machine.World` (`Laws/Machine/Handles.lean:868`): a parent and its extension, not two names for one thing; row 141 renames the parent `HandleWorld` in wave 3, and the glossary states the extension either way |
| `TypedProg` (`Typed/Residual.lean:186`) | protocol-typed weakest precondition on free-monad programs at a world | read (de Vilhena Def. 2.2, 2.4–2.8, papers review §1.3; Xia et al. §3.2, §7, lit-papers Q7, Q10) | `guard_inv`; `typedProg_mono` (probe; R5) | its own inductive since slice 5, sharing the protocol shape of the generic `Typed`, not an instance of it; not closed under bind |
| `ExitOk`, `NoShapeDefect` (`Typed/Admission.lean:30`, `:23`) | exit typing with the "does not go wrong" clause over the closed `Defect` alphabet | by name (Milner 1978) | part one landed (`abc7b124`); part two is row 117 | the meaning-level judgment is `Denote.ExitHasTy` (renamed from `Denote.ExitOk` on 2026-10-01, row 141, seat F); the connector `Typed.exitHasTy_of_fitsExit` (`Laws/Program/Typed/ExitConnector.lean`) holds under two premises, each necessary (`Test/Program/ExitConnector.lean`) |
| `FrameAccepts`, `StackAccepts`, `SavedOk` (`Typed/Contracts.lean:32`, `:51`, `:67`) | the typing of a K-machine state `k ▷ e`; stacks are the free category on frame typings | by name (Harper, PFPL ch. 28) | `popR_typed` (`Typed/Stack.lean:133`); `stackAccepts_append`, `_split` (probe) | typed at one world today; Kripke closure owed (F3) |
| `TypedState` (`Typed/Assembly.lean:123`) | configuration typing: the invariant of a type-safety proof by initiation, consecution and transfer | by name (Wright and Felleisen 1994) | owed: M5, M6's 20 goals, M7 | not upward closed (exact support); "Kripke" applies to `Fits`, `TypedProg` and the amended stacks only |
| `CodeInert` (`Typed/Assembly.lean:84`) | a position is typed by what it will deliver: code is inert on a halted machine, with a queued `finish`, or a published exit | — (row 133) | `m9_root_inert` (probe) | row 134 replaces the halt disjunct by the split keyed on `running`: a running fiber is typed by its queued continuing command, or inert if there is none (`running_exempt_at_m6`, probe) |
| `denote` (`Laws/Program/Denote.lean:66`) | initial-algebra semantics into the free monad on the store signature | read (Plotkin and Pretnar §1, §5) | `denote.eq_cata`; `meaning_never_wrong` | — |
| `storeHandler`, `meaning` (`Denote.lean:124`, `:130`) | a comodel of state; `meaning` runs the free model against it | by name (Plotkin and Power 2008; Ahman and Bauer 2020) | `put_get`, `get_get`, `put_put` on live cells (`Laws/Program/StoreComodel.lean`, seat E; `put_get_dead_fails` red) | lawful on live cells only (`E4-DEN-CE-002`) |
| `denoteR` (`Laws/Program/DenoteR.lean:799`) | elaboration of scoped syntax into first-order effects with bracket markers | read (Wu, Schrijvers, Hinze §9–10; Bach Poulsen and van der Rest, lit-papers Q2) | `denoteR_straight` (`:1380`); `guardR_bind` (`Laws/Program/Intro/Prepare.lean:44`, already in the tree); `eraseControl_guardR_bind` (`Laws/Program/ScopeMarkers.lean`, seat E) | not "a defunctionalized continuation semantics": the defunctionalized continuations are `Cmd` and `ScopeFrame` |
| `iter`, `denoteB` (`Laws/Program/Iter.lean:30`; `DenoteB.lean:208`) | the Kleene chain of the least fixed point; a budget is an approximant | by name (Capretta 2005; Elgot 1975); read (Jacobs Thm 5.3.4) | `denoteB_mono`, `meaningB_unique`; `conv_fixpoint`, `conv_least`, `conv_unique` (`Laws/Program/IterLimit.lean`, seat E) | Elgot's laws hold at the limit only; `Iter.lean`'s "Elgot iteration cut at a budget" is the approximant, not the law |
| `RunMachine`, `Cmd`, `driveStep` (`Machine/Fibers.lean:438`, `:727`, `:1846`) | an abstract machine with a defunctionalized continuation (rc.112's synchronous call stack) | by name (Felleisen and Friedman 1986); read (Danvy and Nielsen 2001, lit-papers Q12) | `driveState_lift`; `run_eq_ref` | not a runner past the first fiber operation |
| `Beh`, `Obs` (`Laws/Machine/Behaviour.lean:74`, `:30`) | behaviour of a deterministic Moore machine on a tape word | read (Jacobs ch. 2, papers review §1.4) | `Beh_fuel_irrelevant`; `behaviour_unique` for the Runner (`Laws/Api/Runner.lean`, seat E); `replayEval_append` (`Laws/Machine/Approximation.lean`) | "equal observations imply equal runs" is injectivity of the behaviour map: not claimed, not needed (the coherence principle's census row 38 says "finality") |
| `replay` (`Api/Runner.lean:75`) and the journal (`List Command`, `Command` at `:35`) | the free monoid action; a journal is a word, an event-sourced log | standard; by name | `replay_unique`, `replay_append`, `journal_replays` (`Laws/Run.lean:184`) | four functions named `replay`; row 98 owns the public typed route |
| `FairTape` (`Laws/Machine/Scheduling.lean:432`) | the finite restriction of weak fairness | by name (Lee et al. 2023, core math §9) | `flush_fair_prefix` | no consuming theorem; liveness owed (R12) |
| the lifts (`Laws/Machine/Lift.lean:48`, `:278`, `:308`, `:638`) | the invariance rule for a transition system, with a monotone ghost world and relative induction | by name (Manna and Pnueli; Owicki and Gries) | `driveState_lift`, `stepDecisionState_lift`, `replayEval_lift`, `driveStep_append` (a frame law) | — |
| the book (`Laws/Machine/Book.lean:196`) | a lock-step forward simulation lifted to tapes | by name (Lynch and Vaandrager 1995) | `book_replayEval`, `bookMeans_obs`; `replay_rel` (`Laws/Program/RuntimeR.lean:162`) | this, not `run_eq_meaning`, is the vocabulary's "simulation" relation |
| `Projects`, `Refines` (`Laws/Machine/Refinement.lean:20`, `:31`) | a refinement mapping and a forward simulation that also matches frontiers | by name (Abadi and Lamport 1991; Hoare 1972) | `projects_compose`, `projects_induces_refines` | — |
| the guard (`Laws/Program/Guard/Core.lean`; `Guard.Reachable` `:32`) | an inductive invariant of the native machine about who owns resume keys and tokens | by name | `driverContract`; `parkHandshake_reachable` owed | "exclusive ghost tokens" is an analogy: the tokens are machine state |
| the fork ledger (`ForkRecord`, `Machine/Fibers.lean:236`) | an append-only history variable written by one transition | by name (Abadi and Lamport 1991) | `step_agrees`, `reachable_agrees` | one observation reads it (`originOf`, used by `Api/Supervision.lean:226`); no transition does |
| `Canonical` (`Store/Domain/Canonical.lean:33`) | a lawful prism into the value sort | by name (Pickering, Gibbons, Wu 2017) | class fields `ofVal_toVal`, `ofVal_exact`; `decode_exact` (`:82`) | `Ty.Canonical` (`Program/Ty.lean:810`) is the normal-form predicate: write `Ty.Normal` there |
| `printT`, `read` (`Codegen/Templates.lean:438`; `Codegen/Read.lean`) | a partial isomorphism (invertible syntax description) on the readable domain | by name (Rendel and Ostermann 2010) | `read_print` (`Laws/Codegen/ReadPrint.lean:1904`), `read_exact` (`Laws/Codegen/Read.lean:887`) | the readable domain excludes annotated loops (DI-91) |
| `Representation`, `Ty.schema`/`ofSchema` (`Schema/Bridge.lean:38`, `:79`) | the free algebra of rc.112's Schema AST signature; `Ty` reaches it by a section with a partial left inverse | by name (Rendel and Ostermann) | `ofSchema_schema` (`:140`); exactness owed (row 128) | not an ornament (McBride 2011): an ornament's forgetful map is total; a partial isomorphism onto the image, a retraction until exactness lands |
| the JSON codec (`Schema/Codec.lean:230`, `:239`) | a retraction on the codec domain; exact modulo key order once proved | by name (Foster et al. 2007) | `decode_encode`, `decode_of_encode` | row 128; the normaliser is key order, not identity |
| provision and layers (`LayerTerm` `Program/Eff.lean:383`; `build` `Program/Provision.lean:297`) | a requirement row calculus; requirement rows grade programs (a flat coeffect: what the context must provide) | by name (Katsumata 2014; Petricek, Orchard, Mycroft 2014) | `provide_closed`, `merge_rows_comm`, `satisfies_iff_subset_keysRow` (`:168`) | satisfaction is inclusion into the key row, not an adjunction; grading soundness is row 117; `build_total`'s restoration and `lower_refines_build` owed (R5) |
| `HostSpec`, `LawfulHostSpec` (`Program/Profile.lean:176`, `:196`) | an environment specification for external calls | by name (CompCert's external functions; CakeML's oracle, model-probe synthesis §3.1) | the `LawfulHostSpec` fields; the rest parked (R6) | — |
| `Session` (`Api/HostSession.lean:84`) | a protocol automaton with capability ledgers (call ids, tokens) | by name | `advance_step` (`Laws/Run.lean:791`) | `open_total` (`:230`) is a totality fact, not a K4 law |
| `HasTy` (`Laws/Program/Typing/HasTy.lean:64`) | the declarative typing judgment; the checker is its sound and complete decision procedure | by name (TAPL ch. 16; Dunfield and Krishnaswami 2021) | `check_sound`, `check_complete`, `hasTy_unique` | its namespace `Conform.Effect4.Typing` is a tool root's (legacy) |
| `Straight`, `Looped` (`Program/Fragment.lean:22`; `Laws/Program/DenoteB.lean:125`) | fragments named by exclusion: a simulation's domain | — | `Straight.eq_cata`, `Looped.eq_cata` | — |
| `ScopeLive` (`Laws/Program/Typed/World.lean`, row 156, pass I2) | the presence predicate of a world-indexed (Kripke) invariant: a proposition on the world monotone along its order, here by scope persistence | standard (possible-worlds models; by name) | `scopeLive_mono`; read by name by `HandleFits`' scope arm, the five scope-handle posts, the protocols' scope arms and `TypedProg.scopeExit` | one name for scope presence at the world (Codex's second-eyes review and seat I's refutation, `E4-TYPED-CE-018`, `E4-SCHED-CE-020`); the machine-store spelling at three clauses is owed one definition (seat D3) |
| K1–K5 (system map §5) | catamorphism; lawful prism; an equal-observation statement (adequacy, semantic preservation) proved through a simulation relation; a sound and complete decision procedure with a located refusal; a free monoid action | by name (as above; Plotkin 1977 for adequacy) | as in §2's last row | `docs/DESIGN-ISSUES.md`'s K1–K6 are obligation kinds: rename them O1–O6 |
| "Schema and program" (`AGENTS.md` vocabulary) | data descriptions as objects, programs as arrows, graded by error and requirement columns | by name (Power and Robinson 1997; Levy, Power, Thielecke 2003; Katsumata 2014) | — | an analogy (system map §6: "a proposed organization"); no carrier holds a refused foreign name (data probe NS0) |
