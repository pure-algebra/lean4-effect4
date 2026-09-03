# The reification push, seen from the algebra: a plan for what is provable now

Status: plan, 2026-09-03. Synthesis of three research notes written the same
day (`2026-09-03-algebra-denotation.md`, `2026-09-03-frame-simulation.md`,
`2026-09-03-mechanical-families.md`) against the design basis
(`docs/DESIGN-BASIS.md` DB-01..DB-06) and the two proof graphs. Nothing here is
built yet; every packet names its statement, its reuse, its size and its
refusals. Estimates are lines of Lean unless marked in days.

## 1. The diagnosis

The trace lane built emitters and checked them against each other: the traced
service over the algebra, the Flow runner, the region runner, two lowerings,
and the host, compared under masks. That was the fast road to working code and
it paid: every packet of the approved plan is landed, five host facts are
pinned, 24 lowering rules are ledgered. But the design basis already says what
those emitters *are*. DB-02 specifies the bridge as `CheckedFlow --elaborates-->
Program` with preservation theorems; DB-03 makes the denotation relational over
decision tapes; DB-05 keeps Scope a separate signature summand handled by the
reified `Scope`; and the five `Effect4/Semantics` stubs (Step, Configuration,
Approximation, Equivalence, Logic) are the layer between. None of it was
written. The cost is concrete:

- The "internal oracle" (runner agrees with the traced service under `m2`) is
  checked executably on four programs when it should be a theorem schema.
- `fuelFor` is asserted in a docstring, never proved.
- The region runner and the reified rc.112 `Scope` already disagree on the
  failure payload when two releases fail (`closeFrame` keeps the first,
  `Scope.closeResult` merges every one); no golden can reach it because the
  host cannot lower a fallible release. Only a lemma against `Scope` sees it.
- The frame machine, reified from rc.112 source with citations, has never been
  related to `interpret` by any theorem, so `semantics` stays open although
  the relation is provable on the fragment the lowerings use.
- The structured and dispatch forms are compared only on the host, because
  they emit `Stmt` directly and no Lean object sits between them.

The corrective is one object and its consequences: `Flow.denote`.

## 2. What the algebra fixes (theorems), and what it cannot (evidence)

Three facts constrain every statement below.

1. **A denotation is tape-indexed and fuel-free.** `Program` is inductive
   (finite on every branch), admitted flows may cycle, so the tape is the
   termination measure: `(tape.length, (raw.reachSet block).length)` decreases
   at every step, and the second component decreases at a non-`choose` edge
   exactly by `CyclesWF`. `fun tape => denote flow tape input` *is* DB-03's
   relational denotation. Missing lemma, one statement:
   `reachSet_length_lt_of_edge (cycles : CyclesWF raw) (edge : EdgeNoChoose raw s t) : (reachSet t).length < (reachSet s).length`.
2. **The traced service emits only `op`/`answer`/`failed`.** `decide`, `enter`,
   `leave`, `finalizer`, `done`, `frontier` have no algebra producer. So the
   denotation lands in a signature sum (`Sig ⊕ₛ DecSig`, later `⊕ₛ ScopeSig`)
   and the interpreting handler is a `Handler.sum` whose extra summands log
   those rows. The reusable law is `interpret_projects_fst` in its general
   form (arbitrary `Handler S (StateT σ M)` with a `Projects` side condition),
   used once today.
3. **The algebra has no bracket former and `interpret` is a fold.** Regions are
   operations of a scope summand with a *stateful upper handler* (the frame
   stack), collapsed by `Handler.mapHom` along `MonadHom.stateT (interpretHom …)`,
   which is `through` with a state slot; failure stays `Except`-shaped in the
   denotation. The frame machine's `PrimInterp` is pure, so any simulation is
   relative to an answer tape (a control-flow simulation modulo an oracle).
   Host fidelity is evidence forever; a Lean-side TypeScript interpreter would
   only relocate it.

## 3. Packets

Ordered by value per proof effort. D-packets are Lean theorems (light
ceremony, D2); M-packets are mechanical host evidence; A-packets change a
frozen alphabet and get a breaker.

### D1 — `Flow.denote` and `run = interpret ∘ denote` (~500)

*Fence:* new `Effect4/Semantics/Denotation.lean`; `Effect4/Semantics/Runs.lean`
(a guarded `tracedFlowService`); lean4-effects `Effects/Flow/Raw.lean`
(`reachSet_length_lt_of_edge`), `Effects/Family.lean` (`FlowAlphabet.toAlphabet`),
`Effects/Trace.lean` (`interpret_log_append`, "the log is a writer").
*Declarations:* `Flow.Sig a := (a.toAlphabet.toFamily (fun _ => Val)).toSignature`;
`Flow.DecSig := ⟨DecisionId × Bool, fun _ => Unit⟩`; `Flow.denoteFuel`
(structural on fuel, mirrors `plan` case for case) and `Flow.denote`
(well-founded on the measure); `Flow.traceHandler := (traced service).toHandler.sum decisionHandler`.
*Theorems:* T1 `runTape fuel = interpret traceHandler (denoteFuel fuel …)`
(one induction on fuel; `interpret_vis`, `Handler.sum_handle_inl/inr`);
T2 `denoteFuel fuel = denote` for `fuel ≥ fuelFor` (the measure theorem);
corollary `runDefault_no_fuel_frontier`, which is the `fuelFor` claim the proof
agent is currently proving directly — whichever lands first, the other becomes
its corollary. *Evidence:* the `m2` oracle for the four programs becomes a
`by rfl`/`decide` instance of T1. *Buys:* half of `docs/TRACE-DAG.md` edge
`semantics`, scoped to the Lean-to-Lean pair; discharges DB-04 for the runner.

### D2 — regions as a scope summand; the `Scope` lemmas (~550)

*Fence:* `Effect4/Flow/Region.lean`, `Effect4/Runtime/Scope.lean`
(`closeExitsM`, a coverage row), `Effect4/Semantics/Denotation.lean`.
*Declarations:* `Flow.ScopeFam` (`enter : RegionId → Unit`, `acquire : Op × Val × Op → Except Val Val`,
`leave : RegionId × Val → Except Val Val`); `Flow.scopeHandler : Handler ScopeSig (StateT (Stack a) (Program (Sig ⊕ₛ DecSig)))`;
`Frame.toScope : Frame a → Scope Nat (a.Op × Val) …` (registration order, since
`releases` is stored latest-first). *Theorems:* L1 `closeFrame_log` (the log of
a close is `leave` then, in `Scope.closeOrder`, `finalizer` before each release's
rows; reuses `closeOrder_eq`, `closeExits_reverse`, `closeOrder_last_first`);
L2 `closeFrame_failure` against `Scope.closeResult` (`closeResult_reasons`,
`asVoidAll_reasons`); the region runner equals `interpret (scopeHandler.mapHom (MonadHom.stateT (interpretHom traceHandler)))`
(`interpret_mapHom`). *Decision required before writing L2:* the divergence in
§1. The honest fix is to make the runner carry a cause (a list of failures,
first first) and project the first for the wire, so L2 states the merge and
`E4-FLOW-CE-019` is re-pinned to "the wire shows the first failure of the
merged cause"; the alternative, restricting L2 to at most one failing release,
must say so in the statement. *Buys:* two host-only facts become lemmas; the
finalizer half of D4 gets its Lean subject.

### D3 — the control skeleton IR; dispatch ≡ structured (~700, one repo edit)

*Fence:* new `Effect4/Target/TypeScript/Skeleton.lean`; `FlowLower.lean`,
`StructuredLower.lean`, `RegionLower.lean` refactored to `render ∘ skeleton`
with the byte-identical outputs pinned by the existing batteries; lean4-typescript
`Structure.Shapes` instantiated at `Skeleton` instead of `Stmt`.
*Declarations:* `Skeleton` (labelled blocks, loops, switch, break/continue,
assign, perform, return); `⟦·⟧ : Skeleton → tape → Program (Sig ⊕ₛ DecSig)`
(same measure); `render : Skeleton → List Stmt`, a printer with no semantics.
*Theorems:* T3 `⟦skeletonDispatch flow⟧ = Flow.denote flow`; T4
`⟦skeletonStructured flow⟧ = ⟦skeletonDispatch flow⟧` for reducible graphs.
*Do first, cheaply:* the factoring, while the lowerings are fresh; T4 is not
sayable without it. *Buys:* closes `structured-agreement` with no TypeScript
fidelity claim; the proof agent's well-scoping lemma is a stepping stone.

### D4 — the frame machine simulates `interpret` on the lowering fragment (~800, two fences)

*Fence A (the unlocking lemma, ~80, do first):* `Effect4/Runtime/Runtime.lean`:
`step_preserves_uninterrupted` (`interruptedCause = none ∧ deferredInterrupt = false`
is `step`-invariant; nothing in the module writes `interruptedCause`), hence
`popFrom` never skips and `getCont` never defers on the fragment. Sharpens
`FRAME-FB-NONNULL` to "vacuous on the fragment". Then `run_add`/`run_mono`
(~60), which the module lacks and DB-04's `∀ fuel ≥ bound` form needs.
*Fence B (~600):* `compile : Nat → Program (Flow.Sig a) Val → Prim Nat Nat Val Val Unit Unit Unit`
with continuations in a table inside `PrimInterp` (DB-02, separations 4–5;
gate the output with `DecidableEq (Prim …)` so nobody instantiates `ν` at a
function type); in-fragment `success, failure, sync, onSuccess, onFailure,
onSuccessAndFailure, onExit` (+ `setInterruptible` only as the frame `ensure`
pushes); `answersOf`, `bound`; theorem `compile_simulates`: for `fuel ≥ bound p`
and `answersOf H p s0 = tape`, `FrameFiber.run (tapeInterp tape) fuel (start (compile 0 p))`
finishes with `exitOf ((interpret H p).run.run s0).1`, `H` into
`ExceptT (Cause Val Unit Unit Unit) (StateT St Id)` (at `Cause`, not the raw
error; `Cause.fail` as a corollary). The finalizer half, stated against the
region runner through `FrameEvent.traceOf`, is its own fence after D2 and needs
the §1 divergence settled the same way (the machine uses `Cause.combine`).
*Buys:* `semantics` closes for the Lean pair; `FrameEvent.toTrace` gets its
consumer; no census row turns green (coverage is clause-by-clause and a
composite is nobody's clause) but the evidence kind changes from single
transitions to a composed run. `bridges` cannot close by theorem: no Lean
statement reaches the host.

### D5 — the script embedding as a per-program receipt (~300)

*Fence:* `Effect4/Target/TypeScript/ScriptFlow.lean`, `Effect4/Meta/Derive.lean`.
*Declarations:* `denoteScript`, `interpret_vis_of_pure` (a pure operation
erases: `interpret h (.vis op k) = interpret h (k v)` when `h.handle op = pure v`),
`Script.toFlow_denote` (induction over steps with the `Build` invariant).
*Also:* `effect_program` emits `example : denoteScript rows name.script = name := by rfl`,
because the elaborator builds program and script independently and nothing
relates them today. *Buys:* the oracle is a corollary per program.

### M0 — wire hardening and the frontier latch (0.5 d each; no bump)

`Trace.escape` must escape C0 controls and `wire` must refuse naturals above
2^53 − 1; a die currently renders `{"failure":[]}`, byte-identical to a unit
failure: mark the run invalid until A1. The budget path pushes one `frontier`
per primitive past the budget (`tracer.ts:167-169`): latch it, then add the
first budget golden. Planted mutants for each; `E4-TARGET-CE-` rows for the
`nat`/`int` non-injectivity as a declared answer-type profile.

### A1 — alphabet v0.6.0: `Outcome.defect`, an interrupt producer (breaker)

The only re-freeze in this plan. `Effects.Trace.Outcome` gains `defect`; a
Lean emitter for `interrupted` appears (today only the P-T11 projection can
produce it); the region contract's "no interrupt cause" refusal is lifted by
M2. Breaker packet in lean4-effects, per D2's exception for re-freezes.

### M1 — `Scopes` as a traced family (1.5 d)

`effect_signature Scopes` over a handler in `StateT (Scope …) Id` wrapping
`Scope.make`/`addExit`/`removeUnsafe`/`close`; host tail over rc.112 `Scope`;
goldens for LIFO close, add-after-closed, remove, and the idempotent second
close (`close_idempotent`, `close_twice`); the patched `scope.close-*` rows
recorded beside them. Needs one DSL feature, an opaque `Handle` spelling for an
op that takes a scope. Nine census rows get their first host observation; none
turns green (their missing clauses are model facts).

### M2 — interruption as decisions (2 d; after A1, M0)

An `Interrupts` decision family answering, at each interruptible point, whether
the interrupt is delivered; the runner treats masks as deferral and finalizers
observe `interrupted`; host injection through `fiber.interruptUnsafe()` at a
counted primitive (the budget path already does it). Three goldens: unmasked
delivery, masked deferral then delivery at unmask, a finalizer seeing
`interrupted`; patched `frame.deferred-interrupt` and `frame.exit-fail-cause.skip`
rows recorded. Nine census rows observed; the interruptor id stays unwitnessable
(the wire drops it).

### M3 — `Fibers` and a two-fiber host (3 d; after M2)

Fork, join, await, interrupt as a host service with a Lean handler over
`Supervision`; the nine assertions of `harness/fiber-supervision/runtime-check.ts`
re-expressed as goldens; a tape-driven `shouldYield`. Honest limit: the Lean
scheduler's `Machine` carries no program, so the Lean face of two fibers is a
sequential projection, and scheduler insensitivity stays a host protocol until
a two-fiber model exists (a new model, not an extension). Fourteen rows
observed; the weakest Lean face of the four.

### Refused for this cycle

`Refs`, `Deferreds`, `Layers` (8-line stubs, no census rows; a census re-pin
comes first); the logic layer (DB-06 `wp ↔ wlp ∧ total`) until D1 fixes the
computational semantics it would be stated over; a Lean-side TypeScript
interpreter (relocates host fidelity, proves nothing D3 does not).

## 4. Order and what closes when

```
week 1: D1 (T1, T2)  ─┐   M0 (0.5 d + 0.5 d)   D3 factoring only (statement)
                       ├─ settle the cause-merge divergence (one decision, then D2 L1/L2)
week 2: D2, D4-A ─────┘   M1 Scopes           D3 T3/T4 begins
week 3: D4-B (fragment)   A1 breaker → M2 Interrupts     D5
later:  D4 finalizer half, M3 Fibers, DB-04 approximation laws, DB-06 logic
```

| Edge | Today | After |
| --- | --- | --- |
| `TRACE-DAG.semantics` | open, "no simulation theorem" | closed for the Lean pair: runner = `interpret ∘ denote` (D1), frame machine simulates `interpret` on the fragment (D4); host stays evidence |
| `TRACE-DAG.structured-agreement` | open | closed by T4 (D3) |
| `TRACE-DAG.bridges`, `FRAMES-DAG.bridges` | open | open by construction; `FrameEvent.toTrace` gains a consumer (D4) |
| DB-04 for the runner | docstring | T2 + `run_add`/`run_mono` |
| region facts | host-pinned | L1/L2 lemmas against the reified `Scope` (D2) |

## 5. What this does not claim

The host is never the subject of a theorem; every M-packet adds observations,
not proofs, and no census row turns green from a golden. Interruption and
scheduling remain evidence-only until A1 and a two-fiber model. The lowering's
faithfulness to Effect v4 generator semantics stays a receipt.
