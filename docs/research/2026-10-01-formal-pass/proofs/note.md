# Formal pass, seat PROOFS: M5–M7 as theorem statements, their proof shapes, and the gaps

Seat PROOFS of the 2026-10-01 formal pass. Base: `refactor/phase1-phase3` at `efd67af1` (slice 6
complete). Read-only on tracked files; probes and logs beside this note, each compiled alone
through the one-compiler lock (`serial.sh lake env lean -M6144 -DwarningAsError=true <probe>`).
Codex's uncommitted slice-6 worktree was not read; its committed evidence under
`docs/research/2026-09-30-seat-codex-slice6-evidence/` was.

Evidence words: **proved** (a kernel theorem compiled here, axioms printed at
`[propext, Quot.sound]` or less), **tested** (a finite check run here), **reading** (code or notes
read, not run), **assumed**. Literature: **read** (this seat or a named note read it), **by name**
(cited from the seat's knowledge, not reread today), **assumed**. Short paths are under
`src/Effect4/`; line numbers are at `efd67af1`.

## The one thing first

**M6's decision and capstone statements put the whole typed state where only a cut-tolerant
predicate can stand.** `RReachable` (`Laws/Program/Typed/Assembly.lean:81`) includes the machine
a replay stops at when a command budget runs out, and `stepDecisionState` drops the unfinished
residue there (`Machine/Fibers.lean:2139-2140`). Row 133 (ruled) types a fiber in the window
between its finishing walk and its `finish` by the queued `finish` — information that lives only
in that residue. Probe A proves the window is reached by a checked, host-free program
(`StaleCode.capstone_false_window`: the root has not exited, its stack is empty, its code slot
holds a `Fail` its type cannot hold, and the dropped residue is exactly
`[finish root e, drainDue]` with `e` clean), and that the current capstone is also false on the
*finished* run of the same program (`capstone_false_finished`; a new host-free refutation that
rows 95–107 do not touch). Through the tree's own replay lift, the ledger's `typedState_load` and
`decision_preserves` therefore cannot both be proved for this program
(`ledger_jointly_false_window`, `ledger_jointly_false_finished`): no proof effort closes M5 and M6
as declared. The lift already has the right shape for the repair: `Guarded J I O`
(`Laws/Machine/Lift.lean:278-283`) keeps a machine-only `J` across a cut and a residue-carrying
`I` while the loop runs. Restate `decision_preserves` and `typedState_reachable` over a
cut-tolerant, observation-level `J` (world validity, the store columns, every recorded exit and
`finalizing` exit typed, `stuck = none`; no code typing) and put the full typed state, with row
133's queue-relative clause and rows 106/133's queue facts, in `I`. M7 transfers only what `obs`
reads (every exit and the stores), so it needs only `J`.

Second in weight, and cheaper to fix: **five protocol posts contradict what the machine answers**,
and no obligation says a protocol is fulfilled by its handler. The await-by-value post reads the
target's answer column while the checker and the machine use the encoded exit, so the denotation
lemma M5 needs fails for programs that await a forked fiber by value (probe E proves the local
refusal, `await_code_refused`; the program-level step is reading); the close-scope post says the answer is the exit passed to close, while
`Scope.close` answers `void` (probe F, `close_code_refused`); three store posts say `bool` where
the store answers `unit` (probe D).
Third: the typed state cannot yield "never halts" (probe C: halting preserves it), and saved
stacks are not Kripke-closed (seat ALGEBRA's probe, re-run here).

## 0. Reading log

- Ledger and statements: `Laws/Auto/Obligations.lean`; `Laws/Program/Typed/{Assembly,State,
  Contracts,Frames,Sources,Validity,World,Membership,Admission,Residual,Stack}.lean`.
- Machine: `Machine/Fibers.lean:249-2240` (RunFiber, Stuck, RunMachine, RunDecision, RunInterp,
  Cmd, settle, exitFiber, driveStep, driveState, stepDecisionState, replayEval);
  `Laws/Program/EvaluateR.lean` (popR, deliverR, evaluateFiberR); `Laws/Program/RuntimeR.lean`
  (loadR, replayR, replay_rel, run_eq_ref, BMeans.exitOf); `Laws/Machine/Approximation.lean:731`.
- Lifts and relations: `Laws/Machine/Lift.lean`, `Laws/Machine/Book.lean:1-60,196-370`,
  `Laws/Machine/Refinement.lean:1-60`, `Laws/Program/Guard/*` (headers, and the hand inductions
  by `grep`), `Guard/Core.lean:1-80`, `Guard/Handshake.lean`.
- Protocol rows against their handlers: `Machine/Stores.lean:1940-1990` (`syncOpStep`),
  `Laws/Program/InterpR.lean:100-200,360-375` (`acquireInR`, close programs, `exitValue`),
  `Laws/Program/DenoteR.lean:190-285,505-556,645-660`, `Program/Checker.lean:190-200,375-381`,
  `Test/Program/{AdmissionCensus,LoadedAdmission,TypedCorpus}.lean` (the parts cited).
- Soundness on the straight fragment: `Laws/Program/MeaningSound.lean:1-40,300-335,736-775`.
- Notes: `docs/core/system-map.md` (§1.1, §4, §5, §8), `docs/core/decisions.md` rows 1–133,
  `docs/core/post-phase-c-synthesis.md` §5–§6 (H, I), the Codex receipt
  (`2026-09-30-seat-codex-slice6-receipt.md`, After addendum 5, H1, H2), its H1 candidate
  (`after-addendum-4/H1/candidate/src/.../Typed/Scheduler.lean`) and `TerminalSavedWitness`, the
  audit (`2026-09-30-codex-review-model-probe/audit.md`) and `SavedFrameTransport.lean`, the side
  audit (`2026-09-30-side-audit/audit.md` §1–§2, consistent with this note), the pass
  synthesis §2.3–§2.4 and its `lift/Lift.lean:849-1113`, the register rows the brief names, the
  pedigree notes `2026-09-05-runtime-semantics-core-math.md` §8 and
  `2026-09-05-effects-papers-review.md` §1.3–§1.4 (for what was read of the literature), and seat
  ALGEBRA's `note.md` and `P2KripkeTyping.lean` (re-run here, §5).

## 1. The formal statements

### 1.0 The frame: a labelled transition system with a world-indexed invariant

**States and configurations.** `RState` is the reference machine (`InterpR.lean:93`). A
*configuration* is `(m, q) : RState × List RCmd`: the machine and the command residue. The
residue is a defunctionalized continuation (Danvy and Nielsen, PPDP 2001, by name: each
higher-order continuation replaced by a first-order constructor and an `apply` function): every
`Cmd` constructor (`Machine/Fibers.lean:727-789`) is one frame of rc.112's synchronous JavaScript
call stack ("everything that rc.112 runs synchronously on the current stack … is a command",
`:720-726`), and `driveStep` (`:1846`) is its `apply`. Inside each fiber, `ScopeFrame` plays the
same role for the fiber's own stack: the named frames (`asyncFinalizer`, `iter`, `loop`) are
defunctionalized and their `apply` is the interpreter hook; `answer` and `resume` keep Lean
closures (reading).

**Two layers of transition** (reading):
- *command step*, deterministic: `(m, c :: q) ↦ driveStep interp m c q`;
- *decision step*, labelled by `d : Api.Decision` (`RunDecision`, `:461-486`: `fire`, `flush`,
  `evaluate`, `yieldVerdict`, `answerAsync`, `interruptFrom`, `installMiddleware`, `advance`):
  `δ_k(m, d) := stepDecisionState interp k m d : RState × Bool` (`:2111`). It runs the command
  loop from a fresh residue at command budget `k`; on a false receipt (budget exhausted) it
  returns the machine and **drops the residue** (`loop`, `:2139-2140`).

The tape is the label sequence; the machine is a deterministic function of (tape, budget), and
every nondeterministic choice — scheduler, clock, interruption, host answer — is a label
(DB-03). The host is an external oracle: its only action is `answerAsync`. Initial state
`s₀ := loadR root.program k k'` (`RuntimeR.lean:41-45`); runs `replayEval interp k tape s₀`
(`Machine/Fibers.lean:2188-2200`), which stops at the first stuck machine or false receipt.

`Reach(root, k) := { (replayR root.program k tape).machine | ∀ d ∈ tape, NoHostAnswer d }`
(`Assembly.lean:76-82`). `ReplayResult.machine` returns the machine of a finished, stuck *or
frontier* result (`Laws/Machine/Approximation.lean:731-735`), so `Reach` contains the machine at
a budget cut, without its residue.

**Worlds.** `World` (`Typed/World.lean:52-57`): the existence world (ids, stores) and four ghost
tables — Γ (fiber → `EffTy`), Π (deferred → `Ty × Ty`), Ρ (ref → `Ty`), Θ (fiber × token →
`EffTy`). `World.leHost` (`Typed/Validity.lean:38-39`) is a preorder (proved there, `:112-116`):
tables extend, stored cells keep their typing (`CellCompatible`), external spellings extend. In
the literature's terms the world is a *store typing* (Pierce, TAPL 2002, §13.4–13.5, by name)
generalised to fibers, promises and tokens, and the typed state is a *Kripke* predicate: a
family indexed by worlds that must be upward-closed in the order (by name: the possible-worlds
reading of store typing; the effects-papers review records the same requirement from MCA,
de Vilhena §4.3 and Jacobs Prop. 6.2.4 as "future-stable predicates, upper sets in the state
preorder", `2026-09-05-effects-papers-review.md` §A3, read).

**The typed state** (reading, `Assembly.lean:67-72`):
`TypedState root rootTy w m := WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧ ActiveDelivery`.
- `WorldValid` (`Validity.lean:19-34`): the world describes this machine (ids, table domains,
  token bound below `nextToken`, closed columns, root at `rootTy`).
- `RStateOk (preds root)`: the generated positionwise predicate (`#typed_state`,
  `Typed/State.lean:24-26`, from the source table `Typed/Sources.lean`). Printed in
  `logs/print-typed-state.log` (tested): every fiber's frame satisfies `SavedOk` at its Γ type
  (`RunFiberOk.c0`, for exited fibers too), its pending list, `finalizing` and `exit` fit Γ
  (`c2`, `c3`), its dispatcher tasks are `ResumeOk`, its context's services fit; races; the
  store columns. **No clause reads `stuck`, `nextRace`, `armed` or scope liveness.**
- `ActiveDelivery`: a parked fiber's saved stack expects its token's declared type.

`SavedOk w final x := ∃ tin, TypedProg w tin x.current ∧ StackAccepts w tin final x.stack ∧
InterruptProvenance x` (`Typed/Contracts.lean:67-69`) is exactly the typing of a K-machine state
`k ▷ e`: code at an intermediate type and a stack from that type to the answer type (Harper,
PFPL 2nd ed. 2016, ch. 28 "Control Stacks", by name; Felleisen and Friedman's CK machine, by
name). `StackAccepts` composes frame arrows through existential middles (decisions row 48).

**The queue.** `QueueOk root w q` (`Assembly.lean:93-96`) types queued `resume` codes only. Rows
106 and 133 (ruled) amend it: `RCmdOk` on every queued command, the guard's per-command
conditions, a token typed by what its observer delivers, a queued `finish` typed at its fiber's
Γ entry. Codex's uncommitted H1 candidate adds `SchedulerState`, `ObserverState`,
`RegistrationState` conjuncts and nine `QueueOk` fields (reading of the committed evidence copy,
`after-addendum-4/H1/candidate/.../Scheduler.lean`).

**The exit judgment.** Today `FitsExit w ty ex := Fits w (reifyExitVal ex) (exitOf ty.answer
ty.error)` (`Membership.lean:152-153`). Ruled (row 107): `ExitOk w ty ex := FitsExit w ty ex ∧
NoShapeDefect ty ex`; part one excludes `badName` and `notImplemented` and ignores `ty`; part two
(row 117) adds `missingService` when `ty.requires` is empty.

### 1.1 M5: initiation

```
M5  ∀ root rootTy k k', Lawful root → typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      ∃ w, TypedState root rootTy w (loadR root.program k k')
```
Lean: `M3bAssembly.typedState_load` (`Assembly.lean:154-156`), open; it lacks the `Lawful`
premise (rows 111–116: the service table travels on the source with its lawfulness evidence).
Its parts: `initial_world_valid` (proved in the tree, `Validity.lean:162`); the empty-everything
clauses (pending, races, stores, captures, the empty context's services); and the one real
lemma, *denotation typing*: `TypedProg root w rootTy (denoteR p p (rootPoint k'))` — the
"fundamental lemma" of the denotation into the residual judgment, by induction on addressed
source (`Node.at_`) with the checker's inversion lemmas (post-Phase C plan F). A compile frontier
(`k'` too small) types at any type because `fiberPost .frontier = False`
(`Residual.lean:165`). As the protocol table stands the denotation lemma fails for programs that
await a forked fiber by value or close a scope with a typed failure: the await-by-value and
close-scope posts refuse the denoted code at its checked type (G6; proved locally by probes E and
F; that a fork's continuation must type that code is reading), so G6's repair precedes any M5
proof. Premises: lawful source; checked type; closed columns. None on the
requirement row: a root that requires a service runs in the empty load context and may die
`missingService`, which `FitsExit` admits and part two admits at a nonempty row. Load inputs
(Config, seed) join when R13 lands.

### 1.2 M6: consecution (the typed state is an inductive invariant)

Three layers, each a declaration in `M6Ledger` (`Assembly.lean:165-245`):

```
M6a (one per command c ∈ Cmd)   StepPreserves root rootTy c :=
      ∀ w m q, TypedState w m → QueueOk w (c :: q) →
        ∃ w' ≥ w, TypedState w' m' ∧ QueueOk w' q'        where (m', q') = driveStep interp m c q
M6b decision_preserves          ∀ d w m, TypedState w m → AnswerOk w m d →
                                   ∃ w' ≥ w, TypedState w' (δ_k(m, d)).1
M6c typedState_reachable        typeOf … = some rootTy → ClosedEff rootTy → m ∈ Reach(root, k) →
                                   ∃ w, TypedState w m
```
M6c follows from M5 and M6b by the replay lift (`foldl_lift`/`replayEval_lift`; the pass's lift
seat proved the implication, `2026-09-30-pass/lift/Lift.lean:1016-1047`, reading); M6b follows
from M6a and the decision's outside-loop edits by `DecisionLift` (`Laws/Machine/Lift.lean:308-355`;
`m6_decision_preserves`, lift seat `:950-955`, reading). Premises: the tape predicate
`NoHostAnswer` (row 95; the host premise `AnswerOk` is kept in M6b for when the lane unparks);
lawful sources (rows 111–116). Status: 18 + 2 open, 0 proved (`#typed_state_obligations
M6Ledger ceiling 20`, `Assembly.lean:274`).

The 18 commands, what each must show, and the known statement defects (reading of
`driveStep`, `Machine/Fibers.lean:1849-1994`):

| Command | What preservation must show | Known defect of the candidate statement |
| --- | --- | --- |
| `evaluate` | flags only; queues `loop` | none |
| `loop` | the evaluator: 31 `SyncOp` and 40 `FiberOp` arms, yield injection, then `settle` | the H1 return window (a walk that finishes leaves the code slot stale, `EvaluateR.lean:67,97-99`): same shape as `deliver`, reached by a `loop` in probe A; allocation needs Kripke-closed stacks (G2); five rows' posts exclude the real answer (G6); a release on a closed scope reads a refused position (R2) |
| `deliver` | the walk (`popR_typed`, proved, `Typed/Stack.lean:105`) then `settle` | H1 `TerminalSavedWitness` (row 133) |
| `finish` | `exitFiber`: middleware re-entry (code returns the exit) or publish, `observe`s, `exitDone`, `drainDue` | `E4-SCHED-CE-017` (queued finish untyped; row 106); exited fiber's code slot (row 133; probe A, reachable) |
| `resume` | `deliver_active` / `deliver_stale` (proved, `Stack.lean:358,373`) | `E4-SCHED-CE-016` (token not yet allocated; freshness, row 106) |
| `launch` | spawn the next entrant at the race's result type | needs the race payload typing (H1 candidate `RacePayload`) |
| `enrollRace` | live set; fire the race observer at once if exited | same |
| `registrationDone` | buffered settle code at the host's saved stack, or park at the race token | needs `RegistrationState` (H1 candidate); `parkOf` is `none` on the reference |
| `interruptTarget` | record; unpark an idle interruptible fiber with a clean failure | `InterruptProvenance` (in `SavedOk`) |
| `afterInterrupt` | `asVoid(awaitCode kind)` at the interrupt op's saved answer frame | none known |
| `raceCancel` | the live-set walk to `interruptTarget`s and `afterInterrupt` | none known |
| `trackChild` | children list and untrack observer (code-free) | none |
| `observe` | `fireObserver`: resume (token typed by delivery), countdown, race callback, scope finalizer drop | `E4-SCHED-CE-018` (row 106 addendum 4) |
| `exitDone` | clear observers, stack, children, context; code slot kept | exited fiber's code slot (row 133; probe A) |
| `closeParAwait` | iterator frame `closeDoneName` and the await-all park | needs Kripke-closed hook protocols (G2) |
| `link` | `linkScope`: record, register, or halt on an unknown scope | halting is not excluded by the invariant (G4) |
| `drainDue` | due completions to resumes (typed by the promise column) | none known |
| `wake` | move a waiter batch to due (payload `Unit`, no code) | none |

### 1.3 M7: transfer, and the safety corollaries

"The compiled machine" in the plan (`post-phase-c-synthesis.md` §5.1, §6 I) is the frame
machine that runs `compileEff`'s first-order code (`Api.replay`), not the OCaml engine (system
map §2 row 8 has three compilations). The transfer is the K3 simulation `run_eq_ref`
(`RuntimeR.lean:211-215`), whose fragment is: every `e : NativeEff`, every compile and command
budget, every tape, **at the empty host table and the empty oracle**; whose observation is `obs`:
every fiber's id and exit, and the whole stores; and whose relation `BMeans` is lock-step (each
`driveStep` matched by one `driveStep`) and equates every code-free field
(`Laws/Machine/Book.lean:13-20`, `BookMeans.nextId … forks`, `:342-370`).

```
M7a (exits)       ∀ root, root.table = [] → typeOf … = some rootTy → ClosedEff rootTy →
                  ∀ k tape, (∀ d ∈ tape, NoHostAnswer d) →
                    ∃ w, ∀ id ex, ((Api.replay root.program k tape).machine.fiber? id).bind exit = some ex →
                           ∃ ty, w.Γ id = some ty ∧ ExitOk w ty ex
M7b (never halts) … → (Api.replay root.program k tape).outcome ≠ .stuck _
M7c (no shape defect) is M7a with ExitOk's part one; part two after row 117
```
Route: M6c at the reference; `replay_rel` gives `BMeans` at the end of both replays;
`BMeans.exitOf` (`RuntimeR.lean:239-245`) transports every fiber's exit, detached fibers
included; `RunFiberOk.c3` types each exit at Γ. M7b needs `m.stuck = none` in the invariant
(absent, G4). Not claimed by M7: termination, fairness (R12), resource release (R11: an
at-most-once safety property over registration identities and an exactly-once liveness property
over closed scopes, neither read by the typed state; the audit's amended shape, §5), any host
behaviour, the OCaml engine. No M7 declaration exists (tested: `grep` over `src/Effect4/Laws`; the
`M7` in `Laws/Machine/{Witnesses,Clauses,StoresLaws}.lean` is an older machine label, "an unknown
scope halts", T4).

**The OCaml engine (LCNF route).** No theorem connects it today; the evidence is finite
differential runs (`lcnf-route.md` §8; system map §2 row 8). The owed shape, per stage, is a K3
connection on a named observation inside a profile, refusing outside it (row 108, DI-56): (i) the
Lean definitions to their LCNF (Lean's compiler: trusted, or validated per module); (ii) the
LCNF-to-OCaml translator, a forward simulation in CompCert's sense (Leroy, CACM 2009 and JAR
2009, by name) from an LCNF semantics (`Conform.Lcnf.Semantics`) to the OCaml target semantics on
`obs` or its wire encoding — or row 28's cheaper option (b), rule coverage plus a scalar-fragment
simulation; (iii) the number profile (row 108). M7's exported statement must stop at the Lean
frame machine and say so.

## 2. The shapes against the literature

| Shape (source; evidence) | The tree's statement | Same shape? | Deviation, and what it buys or costs |
| --- | --- | --- | --- |
| Syntactic type soundness: preservation and progress (Wright and Felleisen, Inf. Comput. 1994, by name; store-typing extension: Pierce, TAPL §13.5, by name) | Preservation: M6a/M6b with `∃ w' ≥ w` (store-typing extension). Progress: none declared; row 52 plans "never halts" and "no wrong-shape exit" as corollaries | Preservation yes. Progress: the machine is total and deterministic per label, so W-F progress ("a non-value can step") is trivially true; the meaningful analogue is a *safety invariant*: never `stuck ≠ none`, never a shape defect | The typed state does not contain `stuck = none`, and halting preserves it (a halted machine stays typed), so "never halts" does not follow from M6 as stated (G4). Term-level progress — a typed term evaluates, so no `badName` arises (`InterpR.lean:231-252`) — is the real content of ExitOk part one and needs its own lemma family (the nine decoders' totality, row 52) |
| Type safety for abstract machines: typed stacks `k ÷ τ`, frames `f : τ ⇒ τ'` (Harper, PFPL ch. 28, by name; CK/CEK machines, Felleisen and Friedman 1986, by name) | `SavedOk` = code at `tin` + `StackAccepts tin final`; `FrameAccepts` per frame; `popR_typed` (proved) is the K-machine's pop lemma | Yes, and the stacks form the free category on frame typings (probe B, proved: `stackAccepts_append`, `stackAccepts_split`) | (a) The machine's *return state* (`ε ◁ v`) is not a state: the returned exit sits in a queued `finish` and the code slot is stale. `WalkTyped (_, some ex) := FitsExit w tout ex` (`Stack.lean:39-42`) already discards the frame; the state predicate does not (H1, row 133; probe A). CompCert's `Returnstate` typing is the standard form (by name). (b) Frame arms quantify at one world, so stacks are not Kripke-closed (G2; seat ALGEBRA, re-run here) |
| Inductive invariant of a transition system (Lamport, TLA 1994; Manna and Pnueli, by name; Jacobs, coalgebra invariants, ch. 6, read by the 2026-09-05 review) | M5 = Init ⇒ Inv; M6a/b = Inv ∧ Next ⇒ Inv′ up to world extension; M6c = □Inv by the lift | Yes; the invariant is a Kripke family (a presheaf on the world preorder) closed under labelled steps | **Quantifying over all typed states, not reachable ones** buys local per-command proofs, a generic lift to the capstone, and cheap refutation by constructed states (H1's witnesses). It costs inductive strengthening: every history fact a step needs (token freshness, ownership, observer delivery, registration, the return window) must be a conjunct, and every constructed counterexample is a demand to add one. The guard family proves many of those facts on native reachable states (§4 item 5 and R4: the cheaper relative-induction route) |
| Forward simulation with stuttering (Milner 1989; Lynch and Vaandrager, Inf. Comput. 1995, by name; the core-math note §8, read) | `run_eq_ref` via `BMeans` and `StepAgrees`: lock-step on commands, both machines deterministic per tape, equality of classification, `obs` and receipts | Yes, a lock-step bisimulation; stuttering appears only against the denotation (`run_eq_meaning`, fuel-counted) | Infinite stuttering is replaced by explicit budgets and the `Suffices` receipt (DB-04), which plays the role of CompCert's measure. The fragment is the empty host table (DI-57), so M5–M6's arbitrary `root.table` does not transfer (R1) |
| Refinement mappings, history and prophecy variables (Abadi and Lamport, TCS 1991, by name) | `Refinement.Projects` (`Laws/Machine/Refinement.lean:20-29`): an abstraction function commuting with steps under a concrete invariant; `Refines` (`:31-37`): a forward relation that also matches frontiers | Yes for the storage interfaces (data refinement: abstraction function plus representation invariant; Hoare 1972, by name) | The fork ledger (row 91) and `m.trace` are history variables in the A–L sense: recorded, never read by behaviour; `BookMeans` equates the first and ignores the second. No prophecy is needed anywhere in M5–M7: both machines are deterministic per tape, and the return window's exit is in the residue (state), not the future |
| Compiler correctness as a simulation diagram (Leroy 2009, by name) | Frame machine ↔ term reference: `run_eq_ref` (behaviour equality, stronger than refinement). LCNF → OCaml: nothing | First half yes; second half absent | The OCaml stage needs a per-stage K3 statement with a profile (row 28 decides its depth). M7 must not be read as covering it |
| Protocol-typed soundness for effects (de Vilhena, thesis 2022, ch. 2 and 4; de Vilhena and Pottier, POPL 2021; read by the 2026-09-05 review) | `Ψ_S`/`Ψ_F` (`Residual.lean`) are protocols: a certificate (Hazel's binders), a pre and a post; `TypedProg` is the effect-weakest-precondition analogue for free-monad programs at a world; its continuations quantify over later worlds | Yes for programs; no for the handler side | Hazel's handler rule asks the handler to answer within each operation's post; the tree has no such adequacy obligation, and five rows fail it (G6). No separation logic (DB-02): fibers share one global Kripke world, so interference is handled by monotonicity — every fiber's typing must survive the world growth other fibers cause (a rely in Jones's rely/guarantee sense, by name). The stack and hook judgments break that (G2). The audit's caution stands: world-order weakening is not protocol monotonicity |
| Coalgebraic bisimulation and invariants (Jacobs, *Introduction to Coalgebra*, ch. 2, 5, 6; read by the 2026-09-05 review) | The machine at a fixed budget is a Moore coalgebra `S → Ω × S^D` (system map §4); `run_eq_ref` over all tapes is Moore bisimilarity on `obs` and classification | Yes | Invariants in Jacobs's sense are closed under *all* successors; here closure is relative to admitted labels (`AnswerOk`, `NoHostAnswer`) and up to world extension. That restriction is the rely of an assume-guarantee specification for the open host (Abadi and Lamport, "Conjoining specifications", 1995, by name): `decision_preserves` already has the safety A/G shape (rely: admitted answers; guarantee: typed state), which is sound for safety; liveness needs separate assumptions (R12, `FairTape`) |

## 3. Gaps, ranked, each with its smallest amendment

### Fundamental: cannot be closed as stated

**G1. The capstone and `decision_preserves` cannot hold a queue-relative typed state.**
Proved (probe A): a checked program with no host on its tape reaches, at command budget 6, a
machine whose root has not exited, has an empty stack, and holds in its code slot a `Fail` its
type ⟨nat, never, ∅⟩ cannot hold (`window6`). The residue the cut drops, recomputed from the
`advance` decision's own steps (`advanceState`'s first round, `Machine/Fibers.lean:2066-2080`,
reading), is exactly `[finish root e, drainDue]` with `e` clean (`residue6_shape`, proved on the
recomputation), and the recomputed machine agrees with the replay's on the root
(`residue6_machine`, proved). Every world refutes `TypedState` there (`window_untyped`), so
`typedState_reachable`'s proposition is false at budget 6 (`capstone_false_window`); and, by
`replayEval_lift` with `AnswerOk` admitted on every answer-free tape (`admitted_noAnswer`), the
declared `typedState_load` and `decision_preserves` are jointly false at this program
(`ledger_jointly_false_window`). Under row 133 the fiber is typed by its queued `finish`, but the
machine `RReachable` hands the capstone has no queue. The same holds one level down: the lift
proves `decision_preserves` from `J := TypedState` (`2026-09-30-pass/lift/Lift.lean:849-955`,
reading), and `J` must hold at every cut (`loop_entry`, `Laws/Machine/Lift.lean:477`). The
positive control shows what does survive: the observation-level clause (every recorded exit fits
its declared type) holds at both machines (`exitsTyped6`, `exitsTyped7`, proved).
*Smallest amendment:* restate M6b and M6c over `Guarded J I O`'s split, which the lift already
provides. `J` (machine-only, cut-tolerant, observation-level): `WorldValid`, the store columns,
every recorded `exit` and `finalizing` typed at Γ, and `stuck = none` (G4). It carries no code
typing, so it needs no queue and no shape test for the return window (a walk can finish with a
bare exit, an `unguard` marker or a `finishFinalizer` marker in the code slot,
`EvaluateR.lean:190,194,299`). `I` (configuration): `J`, the code typing (`SavedOk` for every
fiber that is neither exited nor has a queued `finish`, row 133), the active-delivery clause, the
bookkeeping, and the amended `QueueOk`. M6a becomes `StepKeeps (Guarded J I O)`; `J` is
re-established after each step from `I` before it. The capstone claims `J` on `Reach`; a separate
configuration capstone claims `I` on reachable configurations (the replay with its residue) if a
consumer needs it. M7 needs only `J`. No runtime change.

**G2. Saved stacks and hook protocols are not Kripke-closed, so no step that grows the world can
keep other fibers' stacks typed.** `FrameAccepts`'s `run`/`skip` and the `asyncFinalizer`,
`IteratorProtocol` and `LoopProtocol` premises quantify at the one world the stack is checked at
(`Typed/Contracts.lean:32-48`; `Residual.lean:268-308`). An exit that mentions a handle allocated
later is outside them. Proved by seat ALGEBRA and re-run here (`stackAccepts_not_mono`, and the
repair `stackAcceptsK_mono`, `stackAcceptsK_now`, `bad_not_kripke`, with `typedProg_mono` closing
the open `M3bWorld` obligation; §5). No obligation in the ledger states stack monotonicity.
`Contracts.ResumeOk` is conditional on a Θ entry and has no weakening law of its own (its
docstring says so, `Contracts.lean:70-75`); freshness (row 106) is what makes it stable.
*Smallest amendment:* quantify the frame arms and the three hook premises over later worlds, as
`TypedProg` already does; declare `savedOk_mono` and `stackAccepts_mono` in `M3bWorld`; keep the
token-freshness facts (row 106) in `I` beside the clauses they stabilise (`ResumeOk`,
`PendingOk`, the queued resumes).

**G3. On reachable runs, not only constructed states, the code slot of a finished fiber is
stale and untypable.** Proved (probe A): the same program finishes at budget 7 with a clean exit
that fits, while its root's code slot still holds the escaped `Fail` (`finished7`,
`finished7m`), so `TypedState` fails at every world (`finished_untyped`) and the current capstone
is false on a *finished*, host-free run (`capstone_false_finished`; jointly with M5,
`ledger_jointly_false_finished`). This is the reachable form
of H1: after the signed divergence U-01 the exit is sanitized, but `popR` returns
`(frame, some exit)` without writing `current` (`EvaluateR.lean:67`, `:97-99`) and neither
`publish` nor `cleared` touches it (`Machine/Fibers.lean:1747-1764`). Row 133's exited-fiber
exemption is required, not only its queued-finish clause; and the H1 shape applies to `loop`
as well as `deliver` (both reach `deliverR`'s walk, `EvaluateR.lean:299`, `Fibers.lean:1857-1864`;
tested: in probe A the finishing walk is the sixth command of the cut decision, a `loop`, and the
residue after it is `[finish, drainDue]`, `probes/WindowScout4.lean`, `logs/window-scout4.log`).
*Smallest amendment:* register the probe as a counterexample (proposed `E4-TYPED-CE-009`, "the
saved-code clause types every fiber's code slot"); in row 133's implementation require `SavedOk`
only of a fiber that has not exited and has no queued `finish` (that clause lives in `I`, G1), for
`loop` and `deliver` both.

**G4. "Never halts" is not a consequence of M6.** The generated predicate has no clause on
`stuck` (printed, `logs/print-typed-state.log`). Proved (probe C): halting keeps the typed state
(`typedState_halt`), a command whose result is `(m.halt why, [])` — `linkScope` on an unknown
scope, `Machine/Fibers.lean:1010` — meets `StepPreserves`'s conclusion at the same world
(`halting_result_typed`), and a typed machine always has a typed stuck twin
(`typed_not_imply_running`). So M6c's conclusion cannot exclude a stuck reachable machine.
Liveness of the handles a halt checks is also missing:
`HandleFits` at the scope kind checks only the target string (`Membership.lean:56`), `fiberPre`
is `True` at `raceRegister`/`cancelRace` (`Residual.lean:133`), and a queued `link` carries an
untyped scope. Halting sites: `postTask` (`:712`), `registerRace` (`:941`), `linkScope`
(`:1010-1029`), `join` (`:1608`), the observer's scope drop (`:1671`), the scoped-exit glue
(`EvaluateR.lean:319`). Row 52 ("adopt as corollaries") and system map R9 ("'never halts' is
M7's corollary") assume facts the typed state does not carry (reading).
*Smallest amendment:* add to `J`: `m.stuck = none`; scope liveness (the scope arm of
`HandleFits` reads the scope store, as the cell and promise arms read Ρ and Π); race-id liveness
for codes that name a race (Codex's `RegistrationState` covers `raceRegister`); a typed scope on
queued `link`. Each command proof then shows its halting arms unreachable — the real progress
content.

**G5. Part two of the exit judgment is a coeffect fact, not a transport fact.** Proved (probe
B): part two composes along a frame exactly when the frame does not empty the requirement row
(`exitOk2_transport`, `forbidden2_mono`), and fails in general (`exitOk2_transport_refuted`,
`requirement_condition_fails`; the audit's `AuditH2` shape restated); part one composes wherever
`FitsExit` does (`exitOk1_transport`). At a discharging frame (`.scoped`, a provision region, a
loop or iterator frame at a vacuous answer) the only argument is that the discharged services
were present, and `Defect.missingService` names no key (`Machine/Alphabets.lean:51`), so the
failure cannot be attributed after the fact. The formal object is coeffect soundness: the context
at each position provides that position's requirement row (Petricek, Orchard and Mycroft, ICFP
2014, by name; Effect's `R` parameter is that row). `preds.ServiceOk` is `ServicesFit` only
(present services fit), not presence (audit §1, reading).
*Smallest amendment (row 117's contract):* a presence clause per position, `Provides ctx
ty.requires`, in `SavedOk`'s current-code typing; a `requires`-monotone condition on
non-discharging frame arms (`tout.requires = ∅ → tin.requires = ∅`, the side condition of
`exitOk2_transport`); at `scopeExit`/`release` the restored context provides the outer row. With
presence, part two follows from the absence of `missingService` production, not from transport.

**G6. Five protocol posts contradict the machine's answers, and no obligation says a protocol
is fulfilled by its handler.** *The await-by-value row, which breaks M5.* Proved (probe E): the
checker types `awaitFiber t .awaitValue` at `pure (exitOf a e)` (`Program/Checker.lean:196`), the
reference delivers `success (reifyExitVal ex)` (`InterpR.lean:368-370`,
`exitValue_delivers`), and that value fits the checked type (`delivered_fits_checked`); but
`fiberPost` for the row reads the target's *answer* column (`Typed/Residual.lean:153-155`), which
is `join`'s value, so at a world declaring the target at `pure nat` the post refuses the delivered
value (`post_excludes_delivered`) and `TypedProg` refuses the denotation's await code at the
checked type (`await_code_refused`). A fork's continuation must type that code for every
completed-exit list, the empty one included (`fiberPost .construction`, `Residual.lean:167`), so
the denotation lemma, and with it M5, is false for any program that awaits by value a fiber it
forked — the typed corpus's `awaitFiber.value` and `forkValue` entries
(`Test/Program/TypedCorpus.lean:62,127`; that last step is reading). No loaded-admission test
covers an await (`Test/Program/LoadedAdmission.lean`, reading). Row 106's H1 ruling ("a token is
typed by what its observer delivers, `awaitValue` the encoded exit") fixed the token's type in
Codex's candidate but not this post (`implementation.patch` touches no `fiberPost`, reading).
*The close-scope row.* Proved (probe F): the checker types `closeScope s e` at `pure unit`
(`Program/Checker.lean:377-381`) and, with no finalizer in the scope, the close program is
`pure (success unit)` (`closeScopeR`, `InterpR.lean:166-169`; `close_no_finalizer`), but the post
says the answer is the argument exit (`.closeScope _ ex => ans = ex`, `Residual.lean:160`), so it
refuses the real answer when the argument is a failure (`post_excludes_answer`), and `TypedProg`
refuses the denoted close code (`.vis (.inr (.closeScope s ex)) pure`, `DenoteR.lean:197`) at
`pure unit` for a typed-failure argument at every world (`close_code_refused`). In generated code
the same op closes a provided layer's scope inside `onExitR` (`DenoteR.lean:531-555`), where the
finalizer restores the body's exit, so the runtime result is right; the post is what is wrong.
`closeIter`'s identical post (`Residual.lean:160`) was not checked.
*The three store rows.* Proved (probe D): `scopeRemove` and
`deferredAwaitCleanup` answer `Val.unit` on every store, `scopeAdd` answers `Val.unit` on an open
scope (`scopeRemove_answer`, `awaitCleanup_answer`, `scopeAdd_open_answer`;
`Machine/Stores.lean:1953-1954,1966-1978`), while all three posts say `∃ b, ans = Val.bool b`
(`Typed/Residual.lean:70,74`), so the real answer fails the post at every world
(`*_post_excludes`). `TypedProg`'s store arm types a continuation only where the post holds, so
it admits a program whose next step is untyped (`admitted`, `next_untyped`,
`store_step_leaves_typing`): the impossible-post shape the plan forbids
(`post-phase-c-synthesis.md` §5.3), the converse of `E4-SCHED-CE-013`. On a closed scope
`scopeAdd` answers the reified closing exit (reading), which ties this to R2. The admission
census walked these rows on `Val.bool true` (`Test/Program/AdmissionCensus.lean:112`, reading),
the post's answer rather than the machine's, so it could not see the mismatch. Every other store
row's answer has the post's shape on a sample store (tested, `probes/PostScout.lean`,
`logs/post-scout.log`; the memo rows and the fiber rows were not scouted). In Hazel's terms the
missing fact is the handler rule's premise: the handler answers within the protocol's post.
*Smallest amendment:* the await-by-value post `∃ ty, w'.Γ target = some ty ∧ Fits w' ans
(.exitOf ty.answer ty.error)` (the checker's own rule, as row 106 already rules for the token);
the close-scope post "a success or a clean failure" (`Scope.close` answers `void`; a finalizer's
defect or interruption is clean), and the same review for `closeIter`;
posts `ans = Val.unit` for `scopeRemove` and `deferredAwaitCleanup`, and
`ans = Val.unit ∨ ∃ ex, ans = reifyExitVal ex ∧ FitsExit w' ⟨unknown, unknown, ∅⟩ ex` for
`scopeAdd` (with R2's closed-exit clause); and one adequacy obligation per row, `syncOpStep op st =
some (st', ans) → storePre w op cert → … → ∃ w' ≥ w, storePost w' op cert ans` (and its fiber-row
analogue against the `FiberAction` helpers), declared beside the 18 command goals.

### Rigor: true route, missing premise or statement

**R1. M7's fragment and observation must be stated.** M5–M6 quantify over any
`ProgramSource`, whose table may hold host rows (`Admission.lean:27-29`); `run_eq_ref` holds at
the empty table only (`RuntimeR.lean:203-210`). M7 needs `root.table = []` (or a table-independent
fragment) and `NoHostAnswer` tapes, names `obs` as the observation, and says "the frame machine",
not "the compiled machine". *Amendment:* declare M7a–c with those premises in the ledger.

**R2. Refused source rows become `True` clauses that a step consumes.** `ScopeState.closed.exit`
and `Stores.externals` are refused (`Typed/Sources.lean:29,53-54`; `StoresOk.c5 : True`, printed).
A release registered on a closed scope runs with that stored exit in its environment, and
`capture_lookup` takes its fit at `Exit<unknown, unknown>` as a premise (`Assembly.lean:131-133`)
that the typed state cannot supply. *Amendment:* un-refuse the closed-exit position with
`Fits w (reifyExitVal ex) (exitOf unknown unknown)` (that is, `Live`, DI-94) before the `loop`
case that runs `scopeAdd` on a closed scope; keep `externals` refused while the lane is parked.

**R3. The ledger does not mirror the decision lift.** `DecisionLift` has thirteen fields
(`Lift.lean:308-355`): the command step, the snapshot `O` of tasks a `fire` drained, and the
outside-loop edits (drain, ran, task, skip, yield, interrupt, middleware, two clock steps,
answer). The ledger declares the 18 command goals and `decision_preserves` only; the lift seat's
`M6Edits` (`2026-09-30-pass/lift/Lift.lean:849-871`) is the missing list. *Amendment:* declare the
edits and the snapshot fact as obligations beside the 18.

**R4. Two reachability notions, and the bridge M7 needs.** `Guard.Reachable`
(`Guard/Core.lean:41-44`) is native, per-decision budgets, continuing past frontiers;
`Typed.RReachable` is the reference, one budget, stopping at the first frontier. M7 uses the
second; the guard's facts are about the first. *Amendment:* one lemma, every `replayR` machine is
`BMeans`-related to a `Guard.Reachable` machine at the empty table (the replay is a prefix fold at
constant budget), so code-free guard facts transport for free (`BookMeans` equates every
code-free field).

**R5. Lawful sources are not on `ProgramSource` yet.** Rows 111–116 are ruled; `typedState_load`
and `typedState_reachable` still take any source with a checked program (`Assembly.lean:154,241`).
*Amendment:* the Σ_app slice's source-carried evidence, before the M5/M6 proofs that read the
service table.

**R6. Term progress is unstated.** ExitOk part one is a claim that typed terms never produce
`badName`/`notImplemented` (`InterpR.lean:231-252`; `E4-TYPED-CE-003`'s next action). It needs a
lemma family over `evalTerm` and the decoders at fitting environments, not a typed-state clause.
The tree already has the sharper technique on the straight fragment: `meaning_never_wrong`
(`Laws/Program/MeaningSound.lean:746-749`) proves the meaning independent of the wrong-shape exit
it is given as a parameter, which says "never goes wrong" without an exit predicate (its
docstring: a program may legitimately die). The machine analogue — the reference interpreter
parametric in its wrong-shape exits, the typed run independent of them — is the cleaner M7c
(reading).

**R7. Liveness is outside M5–M7.** M7 is safety. R12's statements (`FairTape`, row enabling, a
host that eventually answers) are separate, with liveness assume-guarantee reasoning that is not
circular-sound in general (Abadi and Lamport 1995, by name).

### Tidiness

**T1. The ledger as the one list.** Open today: `M6Ledger` 20, `M3bAssembly.typedState_load`,
`M3bWorld.typedProg_mono`, `M4Handshake.parkHandshake_reachable` (`Guard/Handshake.lean:26`)
(tested: `grep '#proof_wanted'`). Missing as declarations: M7a–c, stack monotonicity, the decision
edits (R3), the `J`/`I` split (G1). `typedProg_mono` is proved in seat ALGEBRA's probe and can land.

**T2. Stale docstring.** The capstone's docstring (`Assembly.lean:230-240`) lists
`E4-PROV-CE-005` as refuting it (repaired 2026-10-01) and not probe A's refutation.

**T3. Controls in the library.** `World.lean`'s `worldGood`/`worldBad` controls (`:272-292`,
`:726-760`) and `Contracts.Example` (`Contracts.lean:86-105`) are red/positive controls in
`src/`; they belong under `Test/` as controls.

**T4. Name collisions cost every probe.** `World` (`Typed.World` vs `Machine.World`), two
`pure_inv`s, two `Reachable`s (tested: probe A hit the first). Worse, row 107's `ExitOk w ty ex`
will collide in meaning with the existing `Effect4.Program.Denote.ExitOk answer error s ex`
(`Laws/Program/MeaningSound.lean:324`), a coarse exit typing by `Val.hasTy` and `validIn` that
`run_typed` concludes (`:761`). Two exit judgments under one name is a coherence leak by system
map §6; rename the meaning-level one, or derive it from `Fits` by `fits_hasTy`
(`Typed/Membership.lean:269`) once M7 subsumes `run_typed` on the straight fragment. "M7" itself
names two things: the milestone and an older machine repair ("an unknown scope halts",
`Laws/Machine/Witnesses.lean:60,1059`, `Clauses.lean:827`, `StoresLaws.lean:640`).

## 4. The proof route for the M5–M7 brief

1. **Statements first, then proofs.** Land G6's post corrections with the per-row adequacy
   obligations, G1's `J`/`I` split, G2's Kripke closure, G3/row 133's exemptions, G4's liveness
   clauses and R1's M7 declarations as one statement slice, before any `step_*` or M5 proof. Keep
   probes A, C, D, E and F as its red controls: each refutes today's statement, and none may refute
   the amended one (probe A's `exitsTyped6`/`exitsTyped7` become positive controls for `J`).
2. **The induction principle is the lift family, not hand inductions.** M6a is
   `StepKeeps (Guarded J I O)`; M6b is `stepDecisionState_lift` over `DecisionLift`; M6c is
   `replayEval_lift` from M5. The frame law `driveStep_append` handles every residue suffix.
3. **Values by `Fits` lemmas only.** No case analysis on `Ty` outside `Membership.lean` (row
   132): `fits_mono`, `fits_sub`, `fitsExit_of_clean`, `fitsExit_failure_iff`,
   `cleanExit_of_never_fits`, `fitsExit_mono`, `await_fits`; check by the environment census.
4. **Stacks by the category laws.** `stackAccepts_append`/`split` (probe B) and the Kripke-closed
   arms; `popR_typed`, `saveAnswerR_typed`, `deliver_active`, `deliver_stale` already proved.
5. **Relative induction for bookkeeping.** Prove `Book` (token freshness, ownership, races,
   registration) once — the guard family has most of it on native machines — and transport it
   through `BMeans` (R4) instead of re-proving `SchedulerState` on the reference; state M6a as
   `Book m q → Typed w m q → step → Typed w' m' q'` (Lamport-style: an invariant inductive
   relative to a separately proved one). The 38 guard files (14,687 lines, tested by `wc`) stay
   the native bookkeeping proof, with one tidiness pass: `Guard/OuterDriver.lean` (three hand
   inductions over a fire's tasks and the flush and advance rounds, `:102,172,279`),
   `Guard/Single.lean` (six: due list, fuel, tasks, two round loops, history, `:113-478`) and
   `Guard/Decision.lean:69` (history) replicate what `stepDecisionState_lift`, `driveState_lift`
   and `foldl_lift` already provide, as row 110 found for `Guard/Driver.lean`; and the generic
   `foldl_lift` lives in `Guard/Core.lean:62` rather than beside the other lifts in
   `Laws/Machine/Lift.lean` (reading). The 8 simulation files (6,324 lines) are `run_eq_ref`'s K3
   proof and are not redundant with the lifts (their lifting is `Book`'s, a second lift family
   for binary relations; leave it).
6. **Order.** The statement slice (item 1) → per-row protocol adequacy (G6; the handler side,
   which also feeds every `loop` arm) → typedProg_mono and stack monotonicity → M5's denotation
   lemma → the easy commands
   (`evaluate`, `trackChild`, `exitDone`, `wake`, `drainDue`, `resume`) → `finish`/`observe`
   (row 106/133 statements) → race commands → `deliver`/`loop` per evaluator arm, families in the
   post-Phase C order → edits → M6c → M7 (exits, never halts) → part two after row 117.

## 5. Probes

All compiled through the lock, one at a time, from the working tree at `efd67af1` with its built
oleans (`src/` unchanged since `d20f3292`, 02:02; oleans 03:58; tested by `git log` and `ls -l`).

**Probe A, red control: `probes/StaleCode.lean`**, log `logs/stale-code.log`, exit 0. Twenty
theorems, every one at `[propext, Quot.sound]`: `typed_source`, `reach6`, `reach7`, `window6`,
`finished7`, `finished7m`, `only_root6`, `only_root7`, `residue6_shape`, `residue6_machine`,
`untyped_of_stale`, `window_untyped`, `finished_untyped`, `capstone_false_finished`,
`capstone_false_window`, `admitted_noAnswer`, `ledger_jointly_false_window`,
`ledger_jointly_false_finished`, `exitsTyped6`, `exitsTyped7`. The program is `E4-SCHED-CE-008`'s
preempted catch with a one-millisecond timer instead of the deferred answer and one pure bind;
the tape is `[evaluate, flush, interruptFrom root, advance 1, flush]`. Scouting runs (not claims):
`probes/WindowScout*.lean` with `logs/window-scout*.log` found the budget (6 for one bind, 2b+4
for b binds) and the dropped residue. Lessons for probe authors (tested; exit codes in
`logs/bisect-exits.txt`): elaborator `decide` on a replay exhausts 6 GB (T2, exit 137); `decide
+kernel` on the same proposition takes seconds (T4); `classify (replayR …)` exhausts memory even
under `decide +kernel` (T6b, T6b1), while `m.finished = true ∧ m.stuck = none` does not (T8);
`Api.typeOf` needs `rfl'`, not `decide` (T1, T3).

**Probe B, positive: `probes/FrameCategory.lean`**, log `logs/frame-category.log`, exit 0. Nine
theorems: `stackAccepts_append`, `stackAccepts_split`, `stackAccepts_id`, `stackAccepts_push`
(each `[propext]`), `exitOk1_transport`, `forbidden2_mono` (`[propext]`), `exitOk2_transport`,
`exitOk2_transport_refuted` (red control), `requirement_condition_fails` (each at most
`[propext, Quot.sound]`).

**Re-run of seat ALGEBRA's `probes/P2KripkeTyping.lean`** (sha256
`ef61e87e135c5d2e26134214b1c41c97e1fa431af363ad82fdae1621aa38a888`), log
`logs/rerun-algebra-P2KripkeTyping.log`, exit 0: `storePre_mono`, `fiberPre_mono`,
`typedProg_mono`, `stackAccepts_not_mono`, `stackAcceptsK_mono`, `stackAcceptsK_now`,
`bad_not_kripke`, each at `[propext, Quot.sound]`.

**Probe C, red control: `probes/HaltTyped.lean`**, log `logs/halt-typed.log`, exit 0. Four
theorems at `[propext, Quot.sound]`: `typedState_halt`, `queueOk_nil`, `halting_result_typed`,
`typed_not_imply_running`. (A first attempt closed `typedState_halt` by `exact h`, which fails:
the generated structures take the machine as a parameter, so the types are not definitionally
equal; the fields are. Retained in the log history only as this remark.)

**Probe D, red control: `probes/StorePostAdequacy.lean`**, log `logs/store-post-adequacy.log`,
exit 0. Nine theorems, each at most `[propext, Quot.sound]`: `scopeRemove_answer`,
`awaitCleanup_answer`, `scopeAdd_open_answer` (each `[propext]`), `scopeRemove_post_excludes`,
`scopeAdd_post_excludes`, `awaitCleanup_post_excludes`, `admitted`, `next_untyped`,
`store_step_leaves_typing`. The scout `probes/PostScout.lean` (log `logs/post-scout.log`, no
claims) lists each store row's answer shape on a sample store.

**Probe E, red control: `probes/AwaitValuePost.lean`**, log `logs/await-value-post.log`, exit
0. Five theorems, each at most `[propext, Quot.sound]` (`target_declared` uses none):
`target_declared`, `exitValue_delivers`, `delivered_fits_checked`, `post_excludes_delivered`,
`await_code_refused`. A first statement of `post_excludes_delivered` quantified over every world
and failed to compile: the post *does* admit the delivered value when the target is declared at an
exit, `unknown` or a union holding one; the restated theorem fixes the world.

**Probe F, red control: `probes/CloseScopePost.lean`**, log `logs/close-scope-post.log`, exit
0. Three theorems: `close_no_finalizer` (`[propext]`), `post_excludes_answer`,
`close_code_refused` (each `[propext, Quot.sound]`).

**Reading aid:** `probes/PrintTypedState.lean`, `logs/print-typed-state.log`: the generated
`Preds`, `RunMachineOk`, `RunFiberOk`, `RSavedOk`, `StoresOk`, `RCmdOk`.

## 6. Proposed register and decision rows (for the coordinator; not written to the registers)

| ID / row | Proposal |
| --- | --- |
| `E4-TYPED-CE-009` (proposed) | SEEDED: "The saved-code clause types every fiber's code slot on reachable runs" (a residue of `E4-SCHED-CE-008` in the code slot after U-01). Witness: `docs/research/2026-10-01-formal-pass/proofs/probes/StaleCode.lean` (`capstone_false_finished`, `capstone_false_window`, `ledger_jointly_false_window`, `ledger_jointly_false_finished`). Next action: row 133's two exemptions, and G1's statement split |
| decisions row (proposed) | M6's machine-only predicate is cut-tolerant: `decision_preserves` and `typedState_reachable` over `J`; the full typed state with row 133's clause over configurations (`I`); M7 transfers `J` |
| decisions row (proposed) | The typed state carries `stuck = none` and scope/race liveness, so row 52's corollaries follow |
| decisions row (proposed) | Row 117's contract is a presence (coeffect) clause plus a requirement-monotone side condition on non-discharging frames |
| decisions row (proposed; seat ALGEBRA's too) | Frame arms and hook protocols quantify over later worlds (Kripke closure); `stackAccepts_mono` and `savedOk_mono` join `M3bWorld` |
| decisions row (proposed) | M7 is declared now: at the empty host table, on answer-free tapes, observation `obs`, conclusions M7a–c; the OCaml engine is outside it until row 28 is ruled |
| `E4-SCHED-CE-019` (proposed) | SEEDED: "Every store postcondition admits the store's answer." Witness: `probes/StorePostAdequacy.lean` (`store_step_leaves_typing`). Next action: correct the three posts; declare per-row protocol adequacy (store and fiber rows) in the ledger |
| `E4-TYPED-CE-011` (proposed) | SEEDED: "The close-scope post describes `Scope.close`'s answer." Witness: `probes/CloseScopePost.lean` (`close_code_refused`, `post_excludes_answer`). Next action: the post at `void`'s exits; check `closeIter` |
| `E4-TYPED-CE-010` (proposed) | SEEDED: "M5 loads every checked program into a typed state": the await-by-value post reads the target's answer column, so `TypedProg` refuses the denoted await at its checked type. Witness: `probes/AwaitValuePost.lean` (`await_code_refused`). Next action: the post at `exitOf ty.answer ty.error`, with row 106's token rule |
