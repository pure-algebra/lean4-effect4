# The model of a full program: requirements on the proof architecture

Status: **synthesis for the owner's review, 2026-09-30; nothing implemented.** Base `74b526d4` on
`refactor/phase1-phase3`.

The owner asked for real, full Effect programs to be formalized as requirements of the proof
architecture and the mathematical model, not kept as a feature list. The note builds on the
research already done and does not redo it. Its sources are listed in §8; each claim cites one.

## 0. The short answer

- **The model is already the right one, and it was designed for an open signature.**
  - Programs are the free object over a signature of operations.
  - Control constructs are scoped operations, elaborated into that algebra.
  - Behavior is a function of the decision tape.
  - Typing is a world-indexed protocol per operation.
- **The charter (2026-09-16) already states what real programs need, as a theorem property.**
  *Extensible*: a capability is a row, an atom or an equation, and "adding one changes no
  theorem's statement about the others".
- **The architecture meets that only in part.**
  - The typing layer is stated over any signature.
  - Admission, the soundness theorems and the typed-state milestone are pinned to the one
    built-in signature.
  - Three parts of that signature are closed: service types, cell types and data types.

That is why real programs keep meeting walls: not a missing list of features, but statements
fixed to one signature.

**The one requirement that changes the order of work.** State the milestone (M5–M7) over a
signature parameter before proving it. Otherwise every later service, cell type or data type
reopens proved statements (§5).

## 1. The model, as the research already states it

**One shape at four levels** (M1 kickoff §3), with its prior art:

| Level | Object | What it is |
| --- | --- | --- |
| 0 | `Program S`, the free monad over a signature `S`, typed by `Typed o Ψ w Q p` | an interaction tree with a Hazel-style protocol (pre and post per operation) |
| 1 | the world `⟨Γ, Π, Ρ, Θ, s⟩` and its order | a Kripke resource order: tables and allocation persistent, cell contents exclusive (the Iris split) |
| 2 | the typed stack, delivery | defunctionalized continuations, one delivery lemma |
| 3 | the machine invariant, the store, the observation | the store is a comodel and the machine a runner (Plotkin–Power; Ahman–Bauer) |

The rest of the model, by source:

- **Operations are algebraic, and meaning is initial** (end-state §8).
  - `Effects.Program S` is free and initial, and `interpret_pinned` makes an interpretation
    unique once each operation agrees.
  - So a new capability is a new operation or equation, never a new evaluator.
- **Control is scoped syntax** (end-state §8).
  - `catchCause`, `onExit`, `scoped`, `acquireRelease`, `fork` and `raceAll` are scoped or
    higher-order effects.
  - They are elaborated into an algebraic tree (`denoteR`) plus a handler for fiber control.
  - The fiber layer has no equational theory yet; its correctness is a simulation.
- **Behavior is a function of the tape** (core math §2).
  - Scheduling, time and host answers are decisions.
  - Full meaning is relational over them; determinism holds only for a fixed complete tape.
- **Partiality is a budget** (core math §3; end-state §8). Loops are a limit of finite
  approximations, the discipline of the delay monad.
- **Protocols compose by coproduct** (theoretical review §4.3). `Ψ_S ⊕ Ψ_F`: store operations
  and fiber operations are verified separately, and adding one leaves the other half's proofs
  intact.
- **Services and layers are one row calculus** (provision algebra §§1–2).
  - A requirement row is a join-semilattice.
  - A context is a right-biased merge.
  - A layer is typed `⟨out, error, requires⟩`, and `provide` is one equation on rows.
  - The row laws are proved in the tree (`Program/Provision.lean`: `provide_closed`,
    `merge_rows_comm`, …). Build totality was proved in the 2026-09-04 workshop spike only.
- **The faces are exact embeddings and simulations on named observations** (system map §5,
  K2–K3).
  - Printing and reading are exact embeddings.
  - The two machines agree; the fragment theorems relate machine and meaning.
  - OCaml through LCNF, and real Effect through the truth lane, are checked by differential
    runs.
- **A run is data.** The journal acts on the session (K5): `replay_unique`, `journal_replays`.

## 2. What a full program is, in the model

A full program is a closed term of the free object over an **open signature**,
`Σ = Σ_core ⊕ Σ_app`, run by the runner against a host `H`.

- **`Σ_core` belongs to the language:** fiber control, the store over typed cells, time, the
  pure atoms. It grows by the atom and row discipline (one typing row, one evaluation arm, one
  printer entry each), and only by the language's owners.
- **`Σ_app` belongs to packages and applications:**
  - **host rows:** operations with typed request, answer and error, answered by `H`;
  - **services:** keys with their carrier types;
  - **data types:** records and variants;
  - **cell types:** `Ref<A>`, `Deferred<A, E>` at any `A`;
  - **retained behaviors:** typed code references for APIs that keep code.
- **`H` is a relation, not a function,** from calls to replies, constrained by the boundary
  contract (`host-boundary.md` §4). The empty relation is "no host".

**"Proven and reified"** means the charter's seven properties (end-state §10), stated **for
every lawful `Σ` and every `H` the contract admits**. They are: sound, predictable, simple,
extensible, arbitrary complexity, data in the IR, and a base for higher-order APIs. Stating them
for the built-in `Σ` alone is not that.

## 3. The requirements, as theorem shapes

Status words: **proved**, **exists** (code without the theorem), **open** (with its owner).

**R1. The signature is a parameter.** Every judgment, certificate and theorem takes
`Σ = (rows, services, atoms, data, cells)` with its lawfulness, and is stated for every lawful
`Σ`.
- **Typing: proved over any signature.**
  - `Signature Op` (`Program/Typing/Rules.lean:49`) carries `rowOf`, `atomOf`, `scopeKey` and
    `serviceTy`.
  - The checker and `HasTy` are stated over it: 188 `sig : Signature` binders in the proof
    graph.
- **Pinned to the built-in signature:** 89 uses in 15 proof files.
  - `AdmittedProgram` extends `TypedProgram (nativeSignature table)` (`Program/Admission.lean:90`).
  - `MeaningSound` and `LoopSound` are stated at `effTy nativeSignature`
    (`LoopSound.lean:298`, `:307`).
  - `ProgramSource` carries a program and a row table only (`Typed/Admission.lean:84-86`), and
    the typed state reads the signature through it.
- **The service table can be supplied** (`nativeSignatureWith`), but only the layer checker uses
  it. Building, admitting and running refuse a seventh carrier (probe of 2026-09-30:
  `serviceCarrier … signature none`).
- **Source:** the author seat's receipt C2 and the findings ledger 4B (2026-09-17); row 21.

**R2. Extension is additive.** This makes the charter's *Extensible* precise.
- **Conservativity.** For `Σ ⊆ Σ'` (one more row, service, atom, data type or cell type), every
  theorem about `Σ`-programs holds for them in `Σ'`.
- **Local obligations.** `Σ'` brings only its own:
  - its typing row;
  - its protocol entry in the coproduct;
  - its printer template and reader entry;
  - for a runtime operation, its LCNF closure entry and stage connection.
- **Status, per extension point:**
  - **rows:** additive by construction. The theorems quantify over the row table, and
    `interpret_pinned` and `Protocol.sum` are per operation;
  - **services:** fixed (six type codes);
  - **cells:** fixed at `number`;
  - **data types:** `Ty` is closed;
  - **atoms:** additive by the atom owner.
- **Sources:** end-state §8 and §10; theoretical review §4.3; the layers steer ("a row is an
  extension point").

**R3. Data** (workstream W1; row 2).
- **The shape.** The type language is closed under named records and variants.
  - The design is ready: a mutual spine `Ty`/`Fields` (type algebra note §1.3).
  - Each needs its exact embedding to Schema and JSON (K2), its `Fits` clause, and its folds
    generated from the signature.
- **Open, with no owner yet:**
  - **Recursive types.** JSON values and trees need them, and no register row covers them.
  - **Structured error payloads.** The basis refuses `Err.value` (language cut §3); an owner
    ruling is needed.

**R4. State** (W1; rows 42–44).
- **The shape.** Cells are typed by the world at every type: `Ρ key = some A`,
  `Π key = some (A, E)`.
  - Rows become templates.
  - Rows that take a function take a binder term (row 43), as `iterate`'s step does.
- **Status:**
  - **The typed world: proved (row 44).**
  - **Type constructors and the template calculus: landed** (steps 1–2, 2026-09-18).
  - **The rows, the store and the faces: open** (steps 3–5, stopped at the owner's 2026-09-18
    pause).
- **Bridge.** Until those steps land, row 96's D2 reads the native spellings as cells declared
  at `nat`.

**R5. Services** (W2; rows 21, 90, 104–105).
- **The shape.**
  - The context is typed by `Σ`'s service table (row 90).
  - Layers are typed by the provision algebra, with the two gap repairs (rows 104–105).
  - Requirement rows grade programs.
- **What R1 demands here.** The service table is part of `Σ`, threaded through admission,
  `Built`, `HostSession.start`, `Run.open` and the soundness statements. That is the threading
  deferred on 2026-09-17 "until an application needs a seventh carrier".

**R6. Host** (W10; rows 95–101; DI-57).
- **The shape.**
  - Meaning is relational over `H`'s replies.
  - The safety theorem holds for every `H` admitted by the boundary judgment: receipt and
    application theorems (`host-boundary.md` §4.5).
  - The reference relation is table-aware, so machine agreement covers host rows.
- **Status.**
  - **Exists:** the session and the interim rule.
  - **Parked by the owner on 2026-09-30:** the boundary judgment and the table-aware relation.
- **Parking is sound if the premise is stated now.** The milestone says "for every `H` the
  boundary judgment admits"; with no hosts that is the empty relation. The lane then adds its
  judgment without restating M6.

**R7. Retained behavior** (W4; rows 43, 82).
- **The shape.** APIs that keep code (callbacks, handlers, resolvers) take typed first-order
  code references with typed captures. Pure functions take binder terms (row 43).
- **Status: open.** Row 82's design is not settled.

**R8. Runs, composition, faces.**
- **The run API is the K5 action of the session journal** (row 98): `journal_replays` is
  proved.
- **The OCaml engine needs a table-aware keyed entry path** (W10/W11).
- **Numbers** follow DI-56's profile (row 108).
- **Composition.** `composeAt`'s typing closure is derivable; its meaning laws are future work
  (system map §6).

**R9. Never goes wrong** (row 107; addendum 3, H2). The exit judgment excludes shape defects at
every typed position, as part of the safety theorem for every `Σ`.

R1 and R2 are the requirements that make R3–R9 additive.

## 4. Where the architecture stands against R1–R2

| Part of the model | Over any `Σ` today? |
| --- | --- |
| typing, the checker's laws (`HasTy`, `check`, `explain`) | yes |
| per-operation meaning (`interpret_pinned`), protocols (`Protocol.sum`) | yes, for rows |
| admission (`AdmittedProgram`) and `Built` | built-in services only |
| meaning soundness, loop soundness | built-in signature, empty table |
| typed state (`ProgramSource`, `PointTyped`) | rows yes, services no |
| cells | `number` only (rows 42–43 steps 3–5) |
| data types | `Ty` closed (row 2's spine designed) |
| host | the empty relation only (rows 95, 99) |

The pinning is narrow. The typed modules reach the built-in signature in ten places
(`Typed/Admission` 1, `Assembly` 2, `Residual` 3, `ForkSource` 4), mostly through
`ProgramSource`, and runtime admission in three (`Program/Admission.lean:90, 108, 191`).

## 5. What follows for the order

1. **The signature parameter before the M5–M7 proofs** (R1 for services). `ProgramSource`
   carries the service table beside the row table, with `ServiceDef.Agrees`.
   - `PointTyped` checks under `nativeSignatureWith root.table root.services`.
   - Admission, `Built` and `HostSession.start` take the same signature.
   - Row 21 becomes "thread it".
   - The cost is statement-level, because the checker already takes any signature. It belongs
     after Codex's H items and before the M5–M7 brief. `MeaningSound` and `LoopSound` follow:
     today they are stated at the built-in signature with the empty table.
2. **Generic cells before the M6 store arms** (R4). Rows 42–43 steps 3–5. The synthesis already
   orders it this way: W1's authorized cell work comes before the corresponding W0 store proof
   arms (post-phase-c §11.2).
3. **The host premise stated now** (R6). The milestone quantifies over hosts the boundary
   judgment admits, empty for now. The lane stays parked.
4. **Data types additive later** (R3). With R1–R2 in place, records and variants extend the
   generated folds and add `Fits` clauses, with no proved statement restated. Recursive types and
   error payloads get owner rows now, so they are tracked.
5. **Module contracts as real programs reach them** (post-phase-c §11.4): signature and profile,
   state and relations, open parameters, the implementation-to-contract relation, a witness and
   a discriminating counterexample. First, the families the language cut ranks highest: Ref and
   Deferred, Context and Layer, host services, Schedule and retry, Queue.

## 6. What this note does not decide

- The Lean shape of the signature parameter: one structure, or the row and service tables side
  by side as today.
- Recursive types, error payloads and retained behavior. Each needs an owner row and a design.
- An equational theory for the fiber layer (deferred, end-state §8).

## 7. If the owner accepts

- `docs/core/system-map.md` gains §2 "What a full program is" (this note's §2), with R1–R9 as
  the requirement rows under §5's arrow kinds.
- `docs/core/decisions.md`:
  - row 21 becomes the threading;
  - new rows for recursive types, error payloads and the signature parameter's shape.
- The next Codex brief, after H, carries §5 items 1–3 before the M5–M7 proofs.

## 8. Sources

- [Core goals and end state](2026-09-16-core-goals-and-end-state.md) §§1, 3, 8, 10: the goals
  G1–G7, the proof chain, the algebraic basis, the charter.
- [`docs/core/language-cut.md`](../core/language-cut.md) §§1–6: every alphabet against
  Effect, and the cuts that stop real programs, ranked.
- [`docs/core/post-phase-c-synthesis.md`](../core/post-phase-c-synthesis.md) §11:
  - totality over the pinned surface;
  - workstreams W0–W12 and their order;
  - per-module contracts;
  - the [design-issue map](2026-09-20-foundation-review-evidence/design-issue-map.md).
- [M1 kickoff](2026-09-20-m1-kickoff-confidence-and-design-representations.md) §3: one shape at
  four levels.
- [Runtime semantics, the core mathematics](2026-09-05-runtime-semantics-core-math.md) §§1–8.
- [Theoretical review of slices 3–6](2026-09-21-foundations-review-and-theoretical-analysis.md)
  §4: Kripke orders, defunctionalized stacks, extensible protocols.
- [The provision algebra](2026-09-04-provision-algebra.md) §§1–2.
- [The type algebra](2026-09-18-research-type-algebra.md) §1.3: records and variants.
- [Rows 42–43 plan](2026-09-18-rows-42-43-plan.md) §§1, 2e.
- [The author seat's receipt](2026-09-17-seat-author-receipt.md), C2.
- The [dogfood conclusions](2026-09-16-dogfood-conclusions-review.md) and the
  [applied findings](2026-09-16-dogfood-findings-applied.md).
- `docs/core/system-map.md` §§4–6; `docs/core/host-boundary.md` §4; decisions rows 2, 21, 42–44,
  82, 90, 95–110.
