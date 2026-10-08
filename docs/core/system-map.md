# The system map: what Effect4 is for, how it works, how it is organized

The authority for the frame: the goal, the layers and their owners, the sorts with their one
representation each, the kinds of arrow between them and what each owes; since 2026-10-01 also what
a full program is (§1.1) and the requirements it must satisfy, with their status (§8). Written
2026-09-30 at `be15b062`. It replaces the former `docs/research/2026-09-17-ontology-and-do-now-probe.md`, whose formal frame (its §5) is carried here and
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
| 1. Programs as data | One program representation, `Eff`: a first-order tree with a digest, stored by content, printed and read back. Names are data; no closures, promises or runtime objects in program syntax. | §4 below; the dictionary, `docs/core/controlled-english.md` | exists |
| 2. Types and certificates | `Ty`/`EffTy` and one checker, a fold that certifies a type or refuses with a located reason; certificates by kernel decision. | `Program/Checker.lean`; `docs/core/traversal-census.md` | proved sound and complete against `HasTy` at every path; `explain = none ↔ wellTyped`. `HasTy`'s layer rules disagreed with the runtime in two places; rows 104 and 105 are repaired (2026-10-01, `E4-PROV-CE-005` and `-006`) |
| 3. Meaning | One denotation; a reference machine for proofs; the native (frame) machine for execution. | `docs/core/machine-state.md` | proved: meaning soundness; `run_eq_meaning` (straight fragment); `loopAgreement` (looped); `run_eq_ref` (the two machines, **empty host table only**) |
| 4. Choices as data | Every scheduling, timing and host-answer choice is a decision; a run's journal replays it. | `Run.lean`, `Api/Runner.lean` | proved: `replay_unique`, `journal_replays` |
| 5. The typed-state guarantee | A checked program never reaches a malformed state, and every fiber finishes at its type. | `docs/research/history/post-phase-c-synthesis.md`; `Laws/Program/Typed/` | slices 1–5 proved (world, admission, protocols, stack walk, delivery, assembly); M5, M6 and M7 proved (2026-10-03: `typedState_load`; the M6 ledger 20 of 20; the M7 ledger 4 of 4, `m7_proved` and `exitHandles_valid` at `Typed/Commands/Clauses/All.lean`). `J` holds without the closed-row premise and on tapes whose host answers are ghost-admitted (`reachable_typed`); every recorded exit satisfies the meaning layer's judgment on every fragment (`exits_hasTy`, `Typed/Results.lean`). As stated, M5 and M6 are false even on programs that use no host (four registered counterexamples); the bounded repairs are rows 95–96 and 104–107, all landed by 2026-10-01 (row 107 part one; part two is row 117). The typed state now carries the scheduler's queue and observer facts (row 106, `Typed/Scheduler.lean`), a fiber typed by its queued finish with current code inert on a halted machine (row 133), and `ExitOk` at every typed exit position; `StepPreserves` is stated at the dispatch premise `m.stuck = none`; the M6 ledger then stood at 20 open (closed 2026-10-03). The formal pass (2026-10-01) found four statement defects in M5–M6 (rows 134–137), each repaired as a statement by seats A–C of the landing plan |
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
   Schema wipe in the same merge; the M6 ledger then stood at 20 open (closed 2026-10-03); H2 part two is row
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
   Lean reference inside its range and refuses outside it. The owner places it, no later than
   WASM.

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
| type | `Ty` (`Program/Ty.lean`); types up to `≡N` (equal normal forms) are the checker's types, `Ty/≡N ≅ CTy`, ordered by `Ty.subN` (row 137) | its generated family description | `cata_ty` (`Program/Fold.lean`) |
| term | `Term` (`Machine/Term.lean`) | generated | `cata_term` |
| value | `Store.Val` | its inductive; `Kind`/`Shape` classify it | `cata_val`; `Canonical` gives exact embeddings |
| schema carrier | `Representation` | its inductive | an exact embedding from `Ty` modulo `normS` (rows 6, 128) |
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
| K2 exact embedding | `write : A → F`, `read : F → Option A` | total on its domain; `read (write a) = some a`; `read v = some a → v ≡ write a` modulo a named normaliser (a lawful prism, a partial isomorphism with a total forward map) | `Canonical` (`ofVal_toVal`, `ofVal_exact`); `read_print`, `read_exact` on the readable domain; the store, node and program byte codecs; `Config.Val`; the JSON codec modulo `normJ` (`decode_iff`); `Bridge.schema`/`ofSchema` modulo `normS` (`ofSchema_exact`, `ofSchema_schema` with `reservedFree`), at the bridge (row 128) |
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
Anything else is a leak. The census is owned by `docs/research/history/coherence-principle.md` and
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
lives in this table only**; a basis row or a note that needs it links here. A requirement with plan
nodes also has a derived status, in the plan section of `generated/semantics.md`. The plan reads it
from the planned goals and theorems the registry names (`tools/ProofGraph/Plan.lean`). Where the two differ,
the derived status holds and this table is stale. The shapes and their
pedigree are in the model probe's synthesis (§2.2, §3.1) as Codex's audit amended them (§1–§6);
the detail of each lives with the owner named. Status words are the document's: proved, exists,
open.

| Requirement | Shape, in one line | Status at `0c534f06` | Owner of the detail; rows |
| --- | --- | --- | --- |
| R1 the signature is a parameter | `AdmittedSig Σ` with `admitSig_ok_iff`; every milestone statement takes it | typing proved over any signature (`check_sound`, `check_complete`); the typed state reads the source's signature (`27896d8c`); program admission runs at Σ_app (`AdmittedProgram program app`, `admitProgram` running `admitSig`, `src/Effect4/Program/Admission.lean`; seat S, 2026-10-04), and every admitted program denotes a lawful source (`lawfulSig_of_admitted`); code generation (22 lines) and authoring stay pinned to the built-in signature until the Σ_app slice's steps 4 and 3; meaning, loop and run soundness hold, for straight and looped programs only, at an application's signature over any table with service declarations at fresh codes (`meaning_typed_app`, `run_typed_app`, `meaningB_typed_app`, `src/Effect4/Laws/Program/SoundAnySignature.lean`, restored 2026-10-04 by C3's reflection) | this map §1.1; rows 21, 111, 114, 118; the Σ_app slice of the M5–M7 brief, after G. R1's exception (row 138, ruled 2026-10-01): M7 is declared at the empty row table, over the service half of Σ_app; the table-aware agreement (DI-57's host-free part) is R6's. M7 is declared as scope `M7` in `Laws/Program/Typed/Assembly.lean` over `M7Fragment` (lawful source, empty row table, checked, closed, answer-free tape); its route is proved (`m7_of_ledger`; seat C, merged `38686e44`). M7's claim is about the frame machine at the empty host table on answer-free tapes with observation `obs`; the OCaml engine is outside it until row 28 is ruled, and nothing in M7 is "verified lowering" or general host safety |
| R2 extension is conservative | C1 syntax, C2 meaning, C3 checker, C4 protocol typing, C5 world, C6 local lawfulness, C7 representation, C8 forms, over DI-47's relation on Σ_app | C1 proved for binary injections; C2 proved for the generic handler, host rows operational until DI-69; C3 proved both ways: the monotone half (`check_ext`) and its reflection (`check_restrict`, TY-04), both in `src/Effect4/Laws/Program/Signature.lean`; C4 proved for the generic judgment, open for `TypedProg`; C5 red controls proved; C6 proved (`lawful_append`, `src/Effect4/Laws/Program/Signature.lean`); C7 conditional on row 115 (row 105 landed 2026-10-01); C8 open per form. The binary sum is a coproduct of free monads (`sum_is_coproduct`, `Laws/Effects/Sum.lean`, merged `a561d604`), not a tensor (`sum_not_tensor`, red); C4 in both directions for the generic judgment (`Typed.inl_iff`, `Typed.inr_iff`); C1 vacuous for Σ_app (DB-01) | DB-01 (the obligations); rows 111, 115, 116; DI-47, DI-69, DI-22, DI-64 |
| R3 data | the type language closed under records and variants as `Ty` growth: records by one constructor over a field list in canonical name order (row 119), variants with row 130; each constructor brings its `Fits` clause, embeddings, folds, assignability and inhabitance | records, maps and tuples landed in the data wave (`4594b8fa` onward), with the exact codecs (`03403dc8`) and inhabitance (`de926765`, row 127); rows 120–132; recursive types are row 124 (open) | DB-15; rows 119–132; DI-62, DI-67; post-Phase C §11.2 W1 |
| R4 state | the world types every cell at any type; rows as templates; a function row takes a binder term | the world ruled and defined (row 44), its order laws proved; steps 3 and 4 landed (seats T3a and T3b). Step 5 landed for a binder term and for `Deferred.make` (seat T5). It is open for `Ref.make<A>`; the native spellings read as cells at `nat` (row 96 D2). The match of a row's template is the match by bounds: sound, least and complete on every template of the tree (`Bounds.matchB_complete`, the claim `template-match-complete`; row 303) | `machine-state.md`; rows 42–45, 55, 96, 303 |
| R5 services | the service table in Σ_app, read by the typed state as a static world component; a layer's value fits its key; requirement rows grade programs; code-valued services through R7 with a capture law | open: row 105 landed 2026-10-01 (G, `57c93ba4`); rows 112–114 ruled; `build_total` restored 2026-10-04, conditional on a typed leaf semantics (`src/Effect4/Laws/Program/BuildTotal.lean`); owed `lower_refines_build` (row 147), reference keys and Config, minted keys, context validation at any runtime bridge | `machine-state.md` §5; the provision algebra; DB-12, DB-17; rows 51, 82, 90, 104, 105, 112–114, 147 |
| R6 the host | `H : HostSpec` with `LawfulHostSpec`; receipt and application theorems and their converse; DI-57's table-aware reference relation; DI-69; a world extension meeting C5; a retirement edge; per-row cancellation; one root | open, parked by the owner (2026-09-30); the interim handle rule landed (row 97, `bc77e97f`); partial results since (`bff5e18b`, `69974993`, `567d3837`): the plan section of `generated/semantics.md` lists them | `host-boundary.md` §§4.2, 4.5, 4.6; rows 95–101; DI-57, DI-58, DI-65, DI-69 |
| R7 retained behaviour | `resolve_typed`: a resolved code entry is typed at its reference's type, with capture layout fixed at resolution and identity by allocation or structure | open | `machine-state.md` §5; row 82; the stateful catalogue §5 Q4 |
| R8 runs and faces as named connections | inside a profile a face's observation equals the reference's up to one identity bijection; outside it the face refuses, intermediate values included; the profile is data (row 79) | printer and reader laws and the fragment simulations proved; typed lowering open; numbers open (row 108); K2 holds on the readable domain, which excludes a stated type outside the readable types and a fold's stated accumulator type (DI-91) | `lcnf-route.md` §8; this map §5; rows 79, 98, 101, 108; DI-49, DI-56, DI-81 |
| R9 never goes wrong | `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex` at every typed position; `NoShapeDefect` reads the core `Defect` alphabet and `ty.requires` only | ruled (row 107); part one landed 2026-10-01 (`abc7b124`, merged `0c534f06`); part two open (row 117: a saved frame transports `missingService` across a change in the requirement row); "never halts" is declared as M7c (`m7_proved`) and follows from `J` (`machineTyped_not_halted`), so from M5 and M6 (`m7_of_ledger`, proved); its content is the halting arms of the eighteen command proofs (row 139's census) | `Laws/Program/Typed/`; DB-16; rows 52, 107, 117; `E4-TYPED-CE-007` repaired, `E4-TYPED-CE-008` seeded |
| R10 library code inherits theorems | a composed module's law is `Agrees profile module expansion` (row 79); each form owes a typing lemma, one behaviour law, lexical well-scoping, reader admission, a readable expansion (C8) and a stable identity; a composite owes post-Phase C §11.4's contract by a stuttering route | ruled (DI-89, row 79), undelivered: no form has a behaviour law; none of DI-89's named forms exists; DI-39's six rows not landed | `machine-state.md` §5, §7; DI-89, DI-11, DI-39; row 79 |
| R11 resources are released | at most once per registration, counted by identity; exactly once in close order over closed scopes and structured regions, with a completed-cleanup receipt (the closed bit is set before cleanup runs); state retained at frontiers | one close proved (`ScopeMachine.runState_complete` and siblings); the whole run open; a scope a finished run leaves open is an observation (rc.112 does the same) | `machine-state.md` §7; DB-07; DI-65; `host-boundary.md` §4.2 |
| R12 frontiers name what they await | `Deadlocked` requires nothing armed; stability stated over the allowed internal decisions with a named progress observation, not as a whole-machine fixed point; liveness under `FairTape` with row-specific enabling; divergence by compatible prefixes (DB-03) | open; R12-a (`fairTape_unarmed`) and R12-b (`frontier_empty_iff_deadlocked`, decisions row 201 (b)) proved: armed work makes the tape frontier await a decision; INV-TAPE-1 and INV-TAPE-2 are defined in `docs/research/2026-09-07-lit-papers.md` Q7 (tracked since seat H, `1efb963e`), recorded as proposed in DB-03, unruled (the model probe's D7); M7c leaves a frontier as the only unfinished end of an answer-free run at the empty host table once the ledger closes, and says nothing about what the frontier awaits | `machine-state.md` §7; `Laws/Api/Frontier.lean`; DB-03 |
| R13 a run's inputs are data | a congruence law: equal recorded program, signature, profile, budgets, tape and load inputs give equal replay observations; supplied values fit the admitted load requirements | designed (the 2026-09-10 Config route B), not implemented; restates M5's `typedState_load` when Config lands | `host-boundary.md` (the header); `Program/Config.lean`; rows 51, 83 |
| R14 a sketch checks and explains its types | a program with holes checks at a type with a gap; omitting a part keeps admission and loses information only (graduality); a selected address has a context typing that composes with any fitting focus; each queried type fact has a minimal slice; a total checker marks every refusal | open: approved by the owner as first-class work (2026-10-06, row 282). One part has its generic half proved: each queried type fact has a minimal type slice, for every monotone view (`SliceView.lattice_minimal`). No view of a real program exists. A second part is proved: the checker admits a sketch modulo its holes, and that language is a conservative extension (`holes_conservative`, `sketch_weakening`, `Sketch.hole_hasTy`). A third part is proved: a typed program splits at an address, and a program of the focus's type stands in the focus's place (`NodeHasTy.replace`, the claim `typed-replacement`). It is the law of the two edits of a sketch (`Sketch.check_fill`, `Sketch.check_omit`), and its focus is computed: a step function with one case for each arm of `Node.child` answers the focus's environment, and the law holds at that answer (`NodeHasTy.replace_envAt`, the claim `focus-function`). A fourth part is proved: a formed program that the checker admits has closed types (`check_closed`, the claim `checked-types-closed`), since a type variable is formed in a template only. A fifth part is proved in its slow form: the address table of a program lists every address with its typing environment and the checker's answer there. The head of its refusals is the located refusal of `explain`, and the list is empty exactly when the checker admits the program (`refusals_nil_iff`, the claim `address-table`). The table is the specification of total marking, and it does not mark past a refused sibling. The slot table answers the typing environment of the five term slots that extend their node's (`hasTy_extSlotEnv`, the claim `term-slot-environment`). A groundwork is proved, and it is no part of the row: a rule that reads a union member by member has one definition and its laws (`UnionRule.lift_laws`, the claim `union-rule-lift`), so each conversion of an eliminator owes member facts only. The first eliminator is converted: the fiber rule is the extended rule of its member rule, and the contract of a converted eliminator is stated once (`UnionRule.Eliminator.extend_laws`, the claim `union-rule-extend`). Four more rules are converted: the list rule, the exit rule and the cause rule are extended rules, and the option rule is the guarded rule alone (row 304). The match of a template joins the lower bounds of each parameter, and it is monotone in its arguments (`Bounds.matchArgsB_monotone`; row 303). The tests by equality are not converted, so the proposed claim `checker-monotone` stays open. No goal states another part; the study's plan gives each part its slice | `docs/research/2026-10-06-type-slicing-plan.md`; `docs/research/2026-10-06-seat-GAP-study.md`; `docs/research/2026-10-06-seat-UNION-receipt.md`; `docs/research/2026-10-06-seat-REPLACE-receipt.md`; `docs/research/2026-10-06-seat-TRACE-receipt.md`; `docs/research/2026-10-06-seat-FORM-receipt.md`; `docs/research/2026-10-06-seat-PILOT-receipt.md`; `docs/research/2026-10-06-seat-TABLE-receipt.md`; rows 281, 282, 285, 286, 288, 292, 293, 294, 296, 297, 298, 302, 303, 304 |


## 9. The glossary (moved 2026-10-03)

The table of the tree's names in the literature's terms moved to the dictionary,
`docs/core/controlled-english.md` §3.9. Each site is now cited by name and path, not by line. The
dictionary owns every word's meaning, with its tree anchor and its literature term. This map keeps
the frame and uses the words as the dictionary defines them. Decisions row 142 placed the glossary
here, and the move asks for its amendment.

## 10. Why it holds together: the constructions, and when the design is stable (2026-10-01)

The owner's question (2026-10-01): the work keeps expanding, so on what theoretical basis can the
design be called stable, rather than on a plan? This section states the basis the tree already
rests on, as five constructions with the theorem that instantiates each, and then the stability
criteria as conditions a reader can check, each with its status. The evidence words are §7's.

### 10.1 The five constructions

1. **Types are a free object with a signature-generic order.** `Ty` is an initial algebra; every
   traversal is `cata_ty` or generated from the signature (`hom_eq_cata_eff` is the pattern:
   two folds agree when their algebras do). The order `sub` is the least preorder generated by
   the constructors' congruence rows (the variance table), the declared leaf edges, and the
   union rules; its laws are `sub_trans_core`, `sub_antisymm_normal` on normal forms,
   `hasTy_normalize` (membership is invariant under normalisation), `fits_sub` (membership is
   closed under the order). Identity is equality of normal forms, the kernel of `Ty.subN`
   (row 137). **Instance:** `TypeAlgebra.lean`, `Fold.lean`; proved.
2. **Stored programs are first-order trees; their residual semantics has protocol-indexed typing
   over a Kripke world.** `Eff` stores child trees; `RProgram` has Lean-function continuations.
   `TypedProg root w ty p` requires ordinary operation continuations to accept permitted replies
   at every accessible world; its control markers have their own clauses. Construct-specific
   compatibility lemmas connect sequencing (`seq_typed`); unrestricted bind closure is refuted
   (`E4-TYPED-CE-030`). Value membership, residual typing and closed stacks have named transport
   laws (`fits_mono`, `typedProg_mono`, `stackAccepts_mono`, `savedOk_mono`, `scopeLive_mono`).
   `leHost` is compatible world extension, not execution. Store typing and configuration validity
   are re-established by transitions; conditional resume typing also needs stability of the
   addressed declaration. `TypedProg` is not an execution weakest precondition without a
   connecting theorem. The checker is sound and complete against `HasTy` (`check_sound`,
   `check_complete`), a different judgment from machine safety. Program admission is a located
   refusal complete against the judgment. **Instance:** `Typed/Residual.lean`, `Membership.lean`,
   `Contracts.lean`; proved.
3. **The machine is a transition system with an invariant proved by one lift rule.** The typed
   state is `J` (machine-only) inside `I` (the configuration with its queue); `StepPreserves` for a
   command is exactly the lift's `step` premise (`guarded_stepKeeps_of_stepPreserves`), and the
   lifts (`FoldLift`, `DecisionLift` as its corollary through `FoldLift.ofDecisionLift`) carry an
   invariant through every fold, loop and decision once, by relative induction over a monotone
   ghost world. `machineTyped_not_halted` extracts `stuck = none` from the maintained invariant;
   it supplies no successor. **Instance:**
   `Typed/Assembly.lean`, `Machine/Lift.lean`; the rule proved, and the eighteen command instances
   (M6, proved 2026-10-03, `Typed/Commands/`).
4. **Handlers meet their protocols by one adequacy theorem.** For every row, the handler's
   answer lies in the row's post over a store that stays typed (`storeStep_typed` and its
   instances, 66 proved of 74), so a post can never again contradict a handler: a post is a
   theorem about the handler, not a description beside it. **Instance:** `Typed/Adequacy.lean`.
5. **The claim is one route theorem over the boundary's embeddings.** M5 (a checked program
   denotes a typed program, `load_typed_of_denotesTyped`) and M6 (steps preserve) give M7 by
   `m7_of_ledger` (proved): at the empty host table, on answer-free tapes, with observation
   `obs`, every exit fits, every store fits, the run never halts; the reference and the frame
   machine agree (`run_eq_ref`, `replayR_bmeans_reachable`); the meaning layer connects through
   `exitHasTy_of_fitsExit`, whose two premises hold on every run (`exits_hasTy`). Boundaries are exact embeddings (write/read pairs with a named
   normaliser: the JSON codec modulo `normJ`, the Schema bridge modulo `normS`, row 128). **Instance:**
   `Assembly.lean`, `RuntimeR.lean`, `ExitConnector.lean`; the route proved, and with M5 and M6
   proved, M7 (`m7_proved`, `exitHandles_valid`, 2026-10-03) and the meaning-layer exit judgment
   on every fragment (`exits_hasTy`, `Typed/Results.lean`).

### 10.2 Where the expansion came from, and why it is bounded

Every refutation of the formal pass and the landing (rows 134–137, 156; `E4-TYPED-CE-009`
through `-018`) was a clause written outside construction 2 or 4: a frame typed at one world
instead of at every later world; a post stated beside the handler instead of as the handler's
theorem; a code clause read at a cut it could not see; a comparison in the raw order instead of
the checker's; a presence fact spelled at a store instead of as a world-indexed predicate. Each
repair moved the clause into the construction and proved its monotonicity or its adequacy once.
No repair changed a construction. That is the reason the expansion is bounded: a clause can be
missing or weak only in five enumerated places, and each is finite. (The first version of this
section, 2026-10-01 morning, named three; wave 2 found the other two the same day, by
refutation: seat D3's eight command refutations, rows 134 (a)–(e), and seat D2's three
refutations of the denotation statement, rows 170 and 175. The list below is the amended one,
and the finiteness claim for the two new places rests on a census that is not yet an instrument,
row 181.)

- A **missing clause that excludes a halting site** can only come from a halting site of the
  machine that `I` does not exclude: the census of halting sites is finite (nine, decisions row
  139, receipt C step 4), and every site has its clause (row 156 closed the last).
- A **missing clause that types a field** (the shape of rows 134 (a)–(e): a step is well defined
  and keeps every clause `J` states, but writes a field whose contents `J` never typed, so no later
  world is typed): bounded by the fields of the machine state the steps write, which are finite
  (the records `RState`, `Stores`, `SchedulerState` and the queue); the check is a census of those
  fields against the rows of `Typed/Sources.lean` (row 181, owed as an instrument; until it
  exists, this place is bounded by reading, not by a gate).
- A **missing premise of a statement** (the shape of rows 170 and 175: the proposition quantifies
  over more than the construction's instance can handle, a point whose completed view is untyped,
  a world whose service table is not the source's, a root whose references are malformed): bounded
  by the data the statement reads, the fields of `Point`, `ProgramSource` and `World`, which are
  finite; the check is that every field a denotation arm reads is constrained by the statement's
  premises, read off the arm lemmas (seat D2's receipt lists them).
- A **post too weak for its handler** cannot recur: construction 4 proves each post against the
  handler (8 instances open, all of one kind: the memo-table clause and six `f.total` rows).
- A **post too weak for a continuation** (the shape of `E4-TYPED-CE-018`) can appear only in a
  denotation arm of M5, and the arms are the finite list of `denoteRWith`'s cases; each is an
  instance of construction 2's sequencing law or a row's post.

### 10.3 The stability criteria, as conditions, with status

| Criterion | The check | Status (2026-10-01) |
| --- | --- | --- |
| S1 every reused world-indexed fact names its transport conditions; transitions re-establish state validity | persistent predicates use `M3bWorld`; conditional lookups use stability or freshness; changing-state clauses use `StepPreserves` | 0 open, 6 proved; the six cover their named predicates, not every clause of `J` and `I` |
| S2 every row's post is the handler's theorem | `M3bAdequacy` | 8 open, 66 proved |
| S3 every halting site of the machine has the clause that excludes it | row 139's census against `MachineLive`, `QueueOk`, `fiberPre`, `ScopeLive` | complete; the three machine-store spellings have one name since seat D3's step 0 (`Stores.ScopeLive`, `2f8a786a`) |
| S4 every fact has one name at every site (no second spelling) | the dictionary (`docs/core/controlled-english.md`) and §§4–5; the census instrument (row 143) | holds for the typed state since row 156; the renames of row 141 pending |
| S5 the eighteen command proofs and the denotation lemma close, every clause they needed named by a decisions row with its checked refutation (a statement found false is repaired at the contract, never weakened: rows 156, 170, 175) | `M6Ledger`, `M3bAssembly`; the register's `E4-TYPED-CE-*` rows | 9 and 3 open after seat D3 (the ledger 21 open of 484); wave 2 is finding the missing clauses as much as closing goals: M5 needed the formation premise, the completed view and the world's service table (rows 170, 175, proved on seat D2; row 176 under measurement), and seat D3 refuted eight command statements on constructed typed states (`E4-TYPED-CE-024`–`029`: timers, deferred waiters, terminal stacks, observer and race key disjointness, fresh-id bounds), the five clauses ruled as row 134 (a)–(e); the criterion is met when the ledger closes with those clauses in the rows, and not before. **Met 2026-10-03**: `M3bAssembly` and `M6Ledger` closed (20 of 20, `Typed/Commands/Clauses/All.lean`, `053aa3d9`), every repair in a decisions row (134, 151, 156, 170, 175, 188, 190) and its refutation repaired in the register |
| S6 the type signature is closed for the target profile: every form the profile needs is a constructor or an `app` declaration, and the order and membership laws are theorems over the signature's description (a 22nd constructor costs its arms and no law) | probe T's census; the data wave's commits 2 and 4 (the shared table of exceptional rules, the generated `TyView`) | the census is in; the laws are per constructor today; the wave makes them generic |
| S7 the boundary embeddings are exact | row 128's two theorems | landed at today's forms (seat W1, `cdd62673`: `decode_iff`, `ofSchema_exact`); W5 extends both at the wave's forms |
| S8 every field of the machine state a step writes is typed by a clause of `J` or `I` (the field census), and every field a denotation arm reads is constrained by the statement's premises | row 181's instrument (owed); seat D2's arm list | not an instrument yet: five fields found untyped by refutation (rows 134 (a)–(e)), three statement premises by refutation (rows 170, 175); the census is the instrument that would have found them first |

When S1–S7 hold, "stable" is a theorem of the tree, not a judgment: a new program form is a
signature row or an `app` declaration and reopens no law; a new machine behaviour is a halting
site with its clause or a command with its instance; and M7's claim is reached by the one route.
Until then, the open counts above are the distance, and every row of this table is re-checked at
each landing like §8.

### 10.4 What stability buys, in outcomes (the owner's question, 2026-10-01)

The criteria are not an end: each exists because an outcome a user can see depends on it, and
"stable" means that adding the next form or behaviour cannot take an earlier outcome away. One row
per outcome, with the construction that delivers it, the acceptance that demonstrates it, and the
status. This is the table a release reads; §10.3 is the table a landing reads.

| Outcome (what a user does) | Delivered by | Demonstrated by | Status (2026-10-01) |
| --- | --- | --- | --- |
| O1 author a complex program as data: records with optional fields, tagged unions, maps, tuples, nominal references to Effect's module types, error payloads, numbers, `null`/`undefined`, through the authoring surface and its generated forms, with located refusals | construction 1 (the closed signature, S6) and the checker (construction 2) | the data wave's p2 handler (commit 10) and p1, p3, p5 as far as their non-data needs allow; the typed corpus; the admission census | the forms are probed (rows 157–167); the wave lands them once (row 162) |
| O2 run it: the machine executes it under the host session with scripted host answers, every exit typed, every store typed, never halting on the fragment | constructions 3 and 4 (S1–S3, S5) and the route (construction 5) | `run_eq_ref` at the empty table; the truth harness's differential (121/127 agree); M7's four lines, proved from M5 and M6 (`m7_proved`, `exitHandles_valid`, 2026-10-03) | the route and M7 proved on the M7 fragment (the empty host table, answer-free tapes), and on ghost-admitted host answers at the empty table (`obs_typed`); executable admission of scripted host answers open (`admit_sound`, rows 97–99) |
| O3 print it as idiomatic TypeScript that tsgo 7 accepts and that behaves as rc.112, and read it back exactly | the faces (`read_print`, `read_exact`), the exact embeddings (S7), the vendored syntax after row 164 | `check-target` (row 68's vectors, both readings), `check-truth` (the corpus differential), the p2 printed module against its idiomatic signatures | present forms green; the wave's commits 8–10 for the new forms |
| O4 lower it to a concrete implementation: the OCaml engine from LCNF, the CAS store with content addresses, byte-identical generated groups | the generated groups (one producer order), the LCNF route, conservativity (DI-47) | `make check-gen`, `dune build`, `make check-ocaml`, the CAS goldens; `run_eq_ref` carried through `replayR_bmeans_reachable` | green today; the wave regenerates once (row 162) and keeps the goldens byte-identical |
| O5 extend it without reopening O1–O4: a new Effect module is a row table or an `app` declaration, a new behaviour is a halting site with its clause or a command with its instance | S3, S4, S6, S8 | the census instruments (rows 143, 181), §10.3's table re-checked at each landing | holds once S5–S8 close |
| O6 the proof infrastructure stays manageable: obligations are declared by name, searched by `aesop` banks, counted per scope, and the map is measured, not drawn | the ledger commands (`#typed_state_obligations`, `#obligation_proved`, `#obligation_audit`), the banks (row 65), the architecture map (`make gen-architecture`) | the open counts per scope; the map's "0 imports against the direction" | in place; the counts are the distance |

The link the owner asked for: O1 is why S6 matters (a form the signature cannot say is a program a
user cannot write); O2 is why S1–S5 matter; O3 and O4 are why S7 and the generated groups matter;
O5 is what "stable" means for the next slice; O6 is the tooling that makes the rest affordable.
A criterion with no row here is not a criterion.
