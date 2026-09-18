# The typed-state invariant on the reference machine — the plan (2026-09-18)

Ruled the core milestone by the owner on 2026-09-18, no shortcuts. This note is the design;
implementation starts from its §3 in order. Every claim about the tree below was read at HEAD
(`4f2fadc8` and after) with the file and line.

## 0. What it claims, and what it is for

**Claim.** For every program the checker admits, on the machine an application runs, every
fiber's exit has the shape the fiber's type says, at every step of every run, for the whole
alphabet — fork, race, daemons, scopes, the scheduler, timers included — under any decision tape.

**Not claimed.** Nothing about an external host table (the reference lacks external rows, the
answer's conversion and allocation, the prepared answer and evaluator selection: the four gaps
of `run_eq_ref`, `Test/contracts/machine-scheduler-core.contract.md` "Table-aware agreement",
DI-57). The statement is at the empty table, as `run_eq_ref` is; the table-aware version is that
contract's later slice and reuses this one unchanged.

**For.** The boundary decodes a fiber exit without a runtime check; a catch receives a failure
that fits its column (DI-17); no `badShape` exit on an admitted run; the premise the elaboration
and loop obligations (O10/O11, S8a-L) were waiting on. It is the whole-alphabet form of
`TypedProgram.run_sound` / `run_soundB` (`Laws/Program/TypedRun.lean:83-112`).

## 1. What exists, verified

- **The reference signature is a coproduct.** `RSig := Effects.Signature.sum StoreSig FiberSig`
  (`Laws/Program/Sched.lean:196`), `FiberSig := ⟨FiberOp, FiberOp.answer⟩` (`:193`),
  `RProgram := Effects.Program RSig ExitV` (`:205`), `rHandler := Handler.sum storeHandler
  fiberRefusal` (`:220`), `interpret_inl_store` (`:229`): a store-only program interprets by the
  store handler alone. `Effects.Program` is `pure` / `vis op k`
  (`.lake/packages/effects/Effects/Algebra/Program.lean:33`). So a fiber's residual is one of
  three things: an exit, a store operation with its continuation, a fiber operation with its
  continuation. The store summand's typing is already proved; the fiber summand is the work.
- **The fiber alphabet** (`Sched.lean:120-190`, about forty operations) answers in four kinds:
  `Val` (fork, forkIn, awaitAll, yieldNow, the interrupt family, getId, getContext, setContext,
  the children ops, runIn, dropObservers, refuse, suspend, sync, ambientScope, closeWalk,
  foreignRelease, `await _ .awaitValue`); `ExitV` (`await _ .joinEffect`, unguard,
  finishFinalizer, scoped, scopeExit, mask, closeScope, raceAll, raceRegister, async,
  forkScoped, frontier, gen, loop, closeIter); `Option ExitV` (`guard_`); `List (FiberId ×
  ExitV)` (construction). The clause for each is read off the checker's rule for the constructor
  that emits it.
- **The reference state.** `RState`/`RFiber` (`Laws/Program/InterpR.lean:94-95`) are the shared
  `RunMachine`/`RunFiber` at frame type `RProgram` and saved type `RSaved` (`:52`: `current :
  RProgram`, `stack : List ScopeFrame`, `interruptible`, `interruptedCause`, `deferredInterrupt`).
  A fiber's `exit : Option ExitV` is a field of `RunFiber` (`Machine/Fibers.lean:238`).
- **The checker at every path**, with one inversion per constructor
  (`Laws/Program/Typing/CheckInversion.lean`) and soundness/completeness (`CheckSound.lean`).
- **The value-level invariant.** `TypedAt tys env s` (`Laws/Program/MeaningSound.lean:254`:
  `Fits env tys`, values valid in `s`, `s.WF`, `HeapNat s`) with `push`, `later`, `bound`,
  `empty`; `evalTerm_hasTy`/`evalTerm_isSome` (`Laws/Program/Typed.lean`); `sound` (`:480`) and
  `soundB` (`LoopSound.lean:306`), by induction on the term, one arm per constructor.
- **The typed-residual shape already used once.** `SoundB pw pd s a e`
  (`LoopSound.lean:164`) is a predicate on programs of the free monad over `StoreSig` saying
  the stores stay well formed and every reachable answer fits. The new predicate is that shape
  over `RSig`.
- **The reference step, per store operation.** `evaluateR_pure/frontier/store/store_missing/
  suspend/sync` (`Laws/Program/RuntimeR.lean:81-116`), each an equation of one `evaluateR` step
  on a `vis (.inl op) k` frame.
- **The pairing with the compiled machine, per fiber and per step.** The generic book
  (`Laws/Machine/Book.lean:191` `BookMeans C S`, `:965` `book_stepDecisionState`) instantiated at
  the native alphabets: `BMeans root := BookMeans (CodeMeans root) (Means root)`
  (`Laws/Program/Simulation/Fibers.lean:38`), `replay_rel` by `book_replayEval`
  (`RuntimeR.lean:162`), `BMeans.exitOf` (`:239`), `run_eq_ref` and `run_eq_ref_exit`
  (`:211`, `:248`) on `Obs` = every fiber's exit and the stores (`Laws/Machine/Behaviour.lean`).
  The per-step obligations of the simulation — `Simulation/{Deliver,Drive,Evaluate,Hooks,
  Pending,Walk}.lean`, 9,400 lines — are the map of what one scheduler step does, fiber field by
  field; the typed step reuses that case split.
- **The certificate.** `TypedProgram nativeSignature e` (`TypedRun.lean`), the whole-program
  checker's result, is the hypothesis of the load lemma.

## 2. The statement (S0)

One file, `Laws/Program/TypedState.lean`.

- `Γ : FiberId → Option EffTy`, the fiber typing table of a state: the type each live or exited
  fiber was forked at. Extended at every fork by the child's type from the fork rule's inversion.
- `TypedProg (Γ) (t : EffTy) (s : Stores) : RProgram → Prop`, the `SoundB` shape over `RSig`:
  `pure ex` — `ex` fits `⟨t.answer, t.error⟩` by the exit-shape predicate `sound` already uses;
  `vis (.inl op) k` — for every answer `syncOpStep op s = some (state, value)`, `value` valid in
  `state`, `state.WF`, and `TypedProg Γ t state (k value)`, with the missing-key fallback as
  `evaluateR_store_missing` has it; `vis (.inr op) k` — one clause per fiber operation: the
  answer the scheduler may deliver for `op` under `Γ` (a fork's `Val` is a handle whose type is
  the child's `fiberOf`; an `await target`'s `ExitV` fits `Γ target`; a `raceAll`'s `ExitV` fits
  the entrants' common type; an interrupt answers `Val.unit`; a `closeScope`/`scopeExit` carries
  an exit that fits the scope body's type; `refuse` has no typed answer — under typing it is
  unreachable, which is the no-`badShape` corollary), and `TypedProg Γ t s' (k answer)` for every
  such answer at every later store `s'`.
- `TypedFiber Γ s (f : RFiber)`: `TypedProg Γ (Γ f.id) s f.frame.current`; every `ScopeFrame` of
  `f.frame.stack` typed at its scope's type; `f.exit = some ex → ex` fits `Γ f.id`;
  `f.frame.interruptedCause` an admitted cause.
- `TypedState (m : RState)`: `∃ Γ`, every fiber of `m` is `TypedFiber Γ m.state`, `m.state.WF`,
  `HeapNat m.state`, every race's entrants and every pending wait name fibers `Γ` types, and the
  root is typed at the program's type.
- `typedState_load : TypedProgram nativeSignature e → TypedState (loadR e fuel)`, from S1.

## 3. The lemmas, in order

- **S1 `denoteR_typed`.** `check nativeSignature tys p e = .ok t → TypedAt tys env s → TypedProg
  Γ t s (denoteR root e ⟨p, env, fuel⟩)`, by induction on `e`. The store arms are `sound`'s and
  `soundB`'s arms (inversion, `evalTerm_hasTy`, `TypedAt.push`); the reference denotation
  restricts to the meaning on the straight fragment after control erasure (`DenoteR.lean`
  header), which is why those arms carry over. The fiber arms are new: each is the constructor's
  inversion lemma plus the clause of §2 for the operation the arm emits. Fuel: a `frontier` is a
  residual, not an exit; its clause is the budget clause `loopAgreement` uses.
- **S2 `typedState_step`.** On the shared scheduler, `replayEval` one command at a time: if
  `TypedState m` then `TypedState (step m)`. Case split on what the running fiber's residual is
  (§1's three things) and, for a fiber operation, on the operation; the scheduler's own moves
  (park, wake, deliver an exit to a waiter, finalize, interrupt, close a scope, register a race,
  spawn) are the cases of `Simulation/*` already enumerated for the pairing. One lemma per fiber
  operation, proved once, because the scheduler is one piece of code. The store case is
  `evaluateR_store` plus §2's store clause.
- **S3 the transfer.** `TypedState (replayR e fuel tape).machine`, with `replay_rel` and
  `BMeans.exitOf`, gives: every fiber exit in `obs (Api.replay e fuel tape).machine` fits `Γ` —
  the compiled machine's exits are the reference's. Corollary `TypedProgram.run_typed` for every
  `e` (the whole-alphabet form of `run_sound`/`run_soundB`); no `badShape` exit on an admitted
  run; DI-17 guard delivery.

Files: `Laws/Program/TypedState.lean` (§2, S1), `Laws/Program/TypedStep.lean` (S2, split per
operation family as `Simulation/*` is if it grows), the corollaries into `TypedRun.lean`; the
battery `Test/Program/TypedStateContract.lean` prints axioms and pins the three corollaries on
the dogfood programs. Proof search is `aesop` with the checker's rules already registered
(`CheckInversion.lean`); induction hypotheses by hand.

## 4. What is new, and how large

New text: the predicate of §2 (one clause per fiber operation), the fiber arms of one induction
(S1), one preservation lemma per fiber operation on the shared scheduler (S2), one transfer (S3).
Nothing in the machine, the compiler, the checker, the meaning proofs or the pairing changes. S0
and S3 are days; S1's store arms are mechanical and its fiber arms are the inversion plus a
clause each; S2 is the substance and the part that cannot be shortened — about forty operations,
each with the scheduler's bookkeeping for it, which `Simulation/*` has already enumerated once
for the pairing. The two facts §0 of the previous discussion could not promise are now read: the
alphabet and its answers are §1's second bullet; the pairing is per fiber and per step
(`book_stepDecisionState`), so S3 is one theorem.

## 5. Risks, named

1. `Γ` for fibers forked mid-run: fresh ids; `TypedState` is `∃ Γ` and the fork case extends it.
2. Daemons and detached fibers outlive scopes; their exits still fit their own `Γ` entry, so no
   clause depends on the parent being alive.
3. The `guard_` / `unguard` pair and `finishFinalizer`: the delivered exit is the guarded
   body's; its clause reads the `catchIf`/`catchCause`/`onExit` rules, which is where DI-17 is
   discharged, and where a mistake would show first.
4. Interrupts: the cause an interrupted fiber exits with is `interrupt`, which the cause typing
   says contributes `never` to the error column; the clause must say so at the exit, not only at
   the term.
5. The reference's four table gaps are inherited, stated, and not hidden.

## 6. After the scout (2026-09-18, `docs/research/2026-09-18-typed-state-proof-graph-scout.md`)

An Opus seat mapped the graph, ran ten probes and filed eleven corrections. The plan stands with
these amendments; the scout note is the detail and carries the file:line for each.

- **The table is read in `∀`-form.** Every clause that consults the fiber table is `∀ ty, Γ x =
  some ty → …`, never `∃ ty, …`; the `∃`-form is antitone in `Γ` and a fork's extension of the
  table breaks it (probe `P6_bind`, the repaired form stamped `[propext]` in `P7_variance`).
  Coverage of the table is asserted once, in `TypedState`.
- **A fiber handle carries no type in `Val.hasTy`** (`Program/Typed.lean:55`, coarse by DI-17),
  and `validIn` on a handle is always true. So `TypedAt` cannot support the `await` clause. The
  invariant gains a field `HandlesFit Γ tys env` (every handle in scope at a `fiberOf` type is
  typed by the table no more loosely than its static type), in `∀`-form; `Val.hasTy` is not
  touched. **This widens every S1 statement and is the owner's call** (scout F, question 1).
- **S1 is not an induction on the term.** `denoteAction` is a path lookup, so S1 is the weight
  induction of `code_intro_aux` with the `Node.at_` premise (`Intro.lean:27`); `sound`'s lemmas
  are reused, its arms are not (four arms reproduced at 5 to 14 lines each in `P5_s1_arms`).
- **S2 is 65 arms, not 40**: `evaluateFiberR` 40, `driveStep` 18, `popR` 7; the `book_*` ladder
  is binary and carries `MachineOk` for one side only, so a generic unary ladder
  (`Laws/Machine/Keeps.lean`, imports `Machine/Fibers` only) is needed; the invariant must also
  cover the command residue, the dispatcher and the races, which carry `RProgram`.
- **Placement** (scout §D.2): `Laws/Program/Typed/{Residual,Denotation,State,Step/*}.lean` close
  at 121 to 122 modules with no `Simulation/*` or `Book` import; `RuntimeR` (26 modules, 10,690
  lines) enters only at `Typed/Transfer.lean` (S3). Enabling move, first and on its own: the six
  `evaluateR_*` equations (`RuntimeR.lean:81-119`, no consumers anywhere) into `EvaluateR.lean`
  (probe `P9`). Two further cheap moves are listed in §D.3 with their consumer lists (none
  outside `Laws/`).
- **The shape of the residual predicate**: shape B (three clauses plus one 40-arm `AnswerOk`
  definition) compiles and inverts cleanly; taken.
- **Aesop**: `#auto_census` closes 65 of 68 in `CheckInversion`, 1 of 19 in `LoopSound`, 0 of 37
  in `MeaningSound`; the search closes a `succeed` arm outright but never applies the `fiber`
  constructor (dependent `op.answer` unification), so fiber arms start with a hand `cases` on
  the operation; `Later` accessors register as `forward`, not `destruct`. The rule set proposal
  is scout §C, to be applied with S0.
- **Sizes corrected**: `Simulation/*` is 6,008 lines (4,747 for the six named); `run_eq_ref_exit`
  is root-only but `BMeans.exitOf` is per fiber, so S3 stands; the honest estimate is about 150
  lemmas and 5,300 to 8,600 lines, S2 alone 3,000 to 5,000 and its own wave, split by operation
  family.

Order after the scout: Move 1 (`EvaluateR.lean`), then `Keeps.lean`, then S0 in `Typed/Residual`
with the `∀`-form and `HandlesFit` once ruled, then S1, then S2 by family, then S3.
