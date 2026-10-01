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
  grows only by constructor appends under DI-47's compatibility gate over the retained baseline
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

## 2. The layers

| Layer | What it is | Owner | Status |
| --- | --- | --- | --- |
| 1. Programs as data | One program representation, `Eff`: a first-order tree with a digest, stored by content, printed and read back. Names are data; no closures, promises or runtime objects in program syntax. | §4 below; `AGENTS.md` vocabulary | exists |
| 2. Types and certificates | `Ty`/`EffTy` and one checker, a fold that certifies a type or refuses with a located reason; certificates by kernel decision. | `Program/Checker.lean`; `docs/core/traversal-census.md` | proved sound and complete against `HasTy` at every path; `explain = none ↔ wellTyped`. `HasTy`'s layer rules disagree with the runtime in two places (rows 104–105) |
| 3. Meaning | One denotation; a reference machine for proofs; the native (frame) machine for execution. | `docs/core/machine-state.md` | proved: meaning soundness; `run_eq_meaning` (straight fragment); `loopAgreement` (looped); `run_eq_ref` (the two machines, **empty host table only**) |
| 4. Choices as data | Every scheduling, timing and host-answer choice is a decision; a run's journal replays it. | `Run.lean`, `Api/Runner.lean` | proved: `replay_unique`, `journal_replays` |
| 5. The typed-state guarantee | A checked program never reaches a malformed state, and every fiber finishes at its type. | `docs/core/post-phase-c-synthesis.md`; `Laws/Program/Typed/` | slices 1–5 proved (world, admission, protocols, stack walk, delivery, assembly); M5–M7 open. As stated, M5 and M6 are false even on programs that use no host (four registered counterexamples); the bounded repairs are rows 95–96 (landed 2026-09-30) and 104–107 (in flight; `docs/STATE.md`) |
| 6. The host boundary | Host services are rows in a table. A program's call parks a fiber; the host answers through one keyed session that checks each reply and prepares it. | `docs/core/host-boundary.md` | exists: session, envelope, admission, preparation. Next: the interim handle rule that closes the live hole (row 97). The full host-services contract is parked until needed |
| 7. State and storage | The machine's state families, each owned by one of six storage interfaces with laws; facts fixed at creation in append-only ledgers; derived views, such as a handle's declared type, computed from ledgers and the checker. | `docs/core/machine-state.md` §7 | arena laws and `Projects`/`Refines` proved; the fork ledger is next (row 91); the registry and further storage instances are parked (rows 97, 101) |
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
1. **Slice 6's last item:** the fork ledger and the trace agreement
   (`docs/research/2026-09-30-origin-ledger-and-step-invariants-plan.md`; rows 91–94).
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
   landed (row 110); M6's instances follow once rows 104–107 land. Codex's first receipt
   (2026-09-30, `docs/STATE.md`): rows 104 and 105 are checked repairs that were held only by
   generated-file scope, lifted by brief addendum 4; row 106 gained a ruling, a token is typed by
   what its observer delivers; row 107 is held for the model-probe synthesis.

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
| type | `Ty` (`Program/Ty.lean`, 20 constructors) | its generated family description | `cata_ty` (`Program/Fold.lean`) |
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
the journal it keeps. Serialization and resumption need their own contracts.

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
| K2 exact embedding | `write : A → F`, `read : F → Option A` | total on its domain; `read (write a) = some a`; `read v = some a → v ≡ write a` modulo a named normaliser | `Canonical` (`ofVal_toVal`, `ofVal_exact`); `read_print`, `read_exact` on the readable domain |
| K3 simulation | two behaviours, one observation, on a named fragment | the fragment named by exclusion or policy; the observation named | `run_eq_meaning` on `Straight`; `loopAgreement` on `Looped`; `run_eq_ref` at the empty table |
| K4 elaboration | `Src → Except Refusal F` | the refusal is located and complete: `explain = none ↔ wellTyped` | `explain_none_iff`, `authoring_scoped`, `open_total` |
| K5 monoid action | `List Command × S → S` | `replay_unique`, `journal_replays` | both |

A hand traversal that is not a fold is an exemption listed by name by `#traversal_census`
(`docs/core/traversal-census.md`). Two folds agree when their algebras do; no pairwise agreement
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

| Requirement | Shape, in one line | Status at `56da0e1e` | Owner of the detail; rows |
| --- | --- | --- | --- |
| R1 the signature is a parameter | `AdmittedSig Σ` with `admitSig_ok_iff`; every milestone statement takes it | typing proved over any signature (`check_sound`, `check_complete`); admission, the typed state (13 places) and the faces (22 lines) pinned to the built-in signature; meaning, loop and run soundness carry over by corollary (proved) | this map §1.1; rows 21, 111, 114, 118; the Σ_app slice of the M5–M7 brief, after G |
| R2 extension is conservative | C1 syntax, C2 meaning, C3 checker, C4 protocol typing, C5 world, C6 local lawfulness, C7 representation, C8 forms, over DI-47's relation on Σ_app | C1 proved for binary injections; C2 proved for the generic handler, host rows operational until DI-69; C3's monotone half proved (`R2Probe.lean`), reflection open; C4 proved for the generic judgment, open for `TypedProg`; C5 red controls proved; C6 open; C7 conditional on rows 105 and 115; C8 open per form | DB-01 (the obligations); rows 111, 115, 116; DI-47, DI-69, DI-22, DI-64 |
| R3 data | the type language closed under records and variants through the `Ty`/`Fields` spine; each constructor brings its `Fits` clause, embeddings, folds, assignability and inhabitance | refused by DB-15 as written (records, `json`, `int`, `Err.value`); open as one DB-15 amendment; recursive types untracked | DB-15; row 2; DI-62, DI-67; post-Phase C §11.2 W1 |
| R4 state | the world types every cell at any type; rows as templates; a function row takes a binder term | the world ruled and defined (row 44), its order laws proved; steps 3–5 open; the native spellings read as cells at `nat` (row 96 D2) | `machine-state.md`; rows 42–45, 55, 96 |
| R5 services | the service table in Σ_app, read by the typed state as a static world component; a layer's value fits its key; requirement rows grade programs; code-valued services through R7 with a capture law | open: row 105 landing (G); rows 112–114 ruled; owed `build_total`'s restoration, `lower_refines_build`, reference keys and Config, minted keys, context validation at any runtime bridge | `machine-state.md` §5; the provision algebra; DB-12; rows 51, 82, 90, 104, 105, 112–114 |
| R6 the host | `H : HostSpec` with `LawfulHostSpec`; receipt and application theorems and their converse; DI-57's table-aware reference relation; DI-69; a world extension meeting C5; a retirement edge; per-row cancellation; one root | open, parked by the owner (2026-09-30); the interim handle rule landed on Codex's branch (row 97) | `host-boundary.md` §§4.2, 4.5, 4.6; rows 95–101; DI-57, DI-58, DI-65, DI-69 |
| R7 retained behaviour | `resolve_typed`: a resolved code entry is typed at its reference's type, with capture layout fixed at resolution and identity by allocation or structure | open | `machine-state.md` §5; row 82; the stateful catalogue §5 Q4 |
| R8 runs and faces as named connections | inside a profile a face's observation equals the reference's up to one identity bijection; outside it the face refuses, intermediate values included; the profile is data (row 79) | printer and reader laws and the fragment simulations proved; typed lowering open; numbers open (row 108); K2 holds on the readable domain, which excludes annotated loops (DI-91) | `lcnf-route.md` §8; this map §5; rows 79, 98, 101, 108; DI-49, DI-56, DI-81 |
| R9 never goes wrong | `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex` at every typed position; `NoShapeDefect` reads the core `Defect` alphabet and `ty.requires` only | ruled (row 107); part one in flight (brief addendum 5); part two open (row 117: a saved frame transports `missingService` across a change in the requirement row); "never halts" is M7's corollary (row 52) | `Laws/Program/Typed/`; rows 52, 107, 117; `E4-TYPED-CE-007`, proposed `E4-TYPED-CE-008` |
| R10 library code inherits theorems | a composed module's law is `Agrees profile module expansion` (row 79); each form owes a typing lemma, one behaviour law, lexical well-scoping, reader admission, a readable expansion (C8) and a stable identity; a composite owes post-Phase C §11.4's contract by a stuttering route | ruled (DI-89, row 79), undelivered: no form has a behaviour law; none of DI-89's named forms exists; DI-39's six rows not landed | `machine-state.md` §5, §7; DI-89, DI-11, DI-39; row 79 |
| R11 resources are released | at most once per registration, counted by identity; exactly once in close order over closed scopes and structured regions, with a completed-cleanup receipt (the closed bit is set before cleanup runs); state retained at frontiers | one close proved (`ScopeMachine.runState_complete` and siblings); the whole run open; a scope a finished run leaves open is an observation (rc.112 does the same) | `machine-state.md` §7; DB-07; DI-65; `host-boundary.md` §4.2 |
| R12 frontiers name what they await | `Deadlocked` requires nothing armed; stability stated over the allowed internal decisions with a named progress observation, not as a whole-machine fixed point; liveness under `FairTape` with row-specific enabling; divergence by compatible prefixes (DB-03) | open; armed dispatcher work is invisible to the frontier today (`awaitDecision_iff`); INV-TAPE-1 and INV-TAPE-2 not yet in a tracked file | `machine-state.md` §7; `Laws/Api/Frontier.lean`; DB-03 |
| R13 a run's inputs are data | a congruence law: equal recorded program, signature, profile, budgets, tape and load inputs give equal replay observations; supplied values fit the admitted load requirements | designed (the 2026-09-10 Config route B), not implemented; restates M5's `typedState_load` when Config lands | `host-boundary.md` (the header); `Program/Config.lean`; rows 51, 83 |
