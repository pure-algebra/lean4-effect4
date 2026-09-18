# The typed-state invariant: proof-graph scout (2026-09-18)

Scout note for the plan `docs/research/2026-09-18-typed-state-plan.md`, the milestone the owner
ruled on 2026-09-18. Read at `d9769061`. Nothing is landed; this note and the scratch files under
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/131bb391-fca6-4e88-a9fb-f63a8eeec300/scratchpad/scout/`
are the whole output.

Words used as the brief defines them. **Proved** means a theorem exists at HEAD with its
`file:line`. **Reproduced** means I re-derived it in a scratch file. **Tested** means a scratch
file compiled with `lake env lean` and I report the output. **Stamped** means `#print axioms`
printed the ceiling. **Assumed** means I did not check it.

---

## A. The proof graph, mapped

### A.0 The alphabet, counted

`FiberOp` has exactly **40** constructors (`src/Effect4/Laws/Program/Sched.lean:96-159`;
counted with `awk '/^inductive FiberOp/,/^deriving DecidableEq$/' | grep -cE '^  \| [a-zA-Z]'`,
output `40`). The plan's "about forty operations" is exact. In order:

```
fork forkIn forkScoped await awaitAll awaitAllFailFast yieldNow async interrupt interruptAs
interruptScoped interruptAll mask closeScope scoped scopeExit foreignRelease raceAll
raceRegister cancelRace getId getContext setContext snapshotChildren awaitNewChildren runIn
dropObservers refuse ambientScope closeWalk closeIter frontier guard_ unguard finishFinalizer
suspend sync gen loop construction
```

`FiberOp.answer` (`Sched.lean:165-173`) sorts them into four answer types, and the plan's §1
list is right except that it does not name `awaitAllFailFast` and `cancelRace` (both fall in the
`_ => Val` arm, so the plan's classification is still correct, only its enumeration is short by
two).

The source alphabets that feed this are smaller and are the ones the checker sees:
`Eff` has **25** program constructors (`src/Effect4/Program/Eff.lean`, the mutual block's `Eff`
family), `ActionTerm` has **16** (`Eff.lean:395-411`), `LayerTerm` has **10** (`Eff.lean:421-440`).
Between the source action and the runtime operation sits the machine's own action alphabet
`WithFiberAction`, with **23** constructors, produced by the point lookup `actionAt`
(`src/Effect4/Program/Compile.lean:971-1050`). That lookup is where the extra seven come from
(`setInterruptible`, `interruptAs`, `ambientScope`, `refuse`, `dropObservers`, `cancelRace`,
`closePar`): they exist at the machine, never in a source program.

### A.1 S0, the statement

**Consumes, proved and read:**

| name | file:line | shape |
| --- | --- | --- |
| `RSig` | `Laws/Program/Sched.lean:196` | `Signature.sum StoreSig FiberSig` |
| `FiberSig` | `Sched.lean:193` | `⟨FiberOp, FiberOp.answer⟩` |
| `FiberOp.answer` | `Sched.lean:165` | `FiberOp → Type`, four arms |
| `RProgram` | `Sched.lean:205` | `Effects.Program RSig ExitV` |
| `Effects.Program` | `.lake/packages/effects/Effects/Algebra/Program.lean:33` | `pure` / `vis op (Answer op → Program)` |
| `rHandler`, `interpret_inl_store` | `Sched.lean:220`, `:229` | the store half only |
| `RState`, `RFiber`, `RSaved`, `ScopeFrame` | `Laws/Program/InterpR.lean:94`, `:95`, `:52`, `:43` | the shared machine at `RProgram`/`RSaved` |
| `RunFiber.exit` | `src/Effect4/Machine/Fibers.lean:238` | `Option (Exit β ε δ ι α)` |
| `TypedAt` | `Laws/Program/MeaningSound.lean:254` | `Fits`, `validIn`, `WF`, `HeapNat` |
| `TypedAt.push`, `.later` | `MeaningSound.lean:261`, `:276` | the two weakenings |
| `ExitOk` | `MeaningSound.lean:285` | success: `hasTy` and `validIn`; failure: `causeAdmits` |
| `SoundB`, `StoreOk` | `Laws/Program/LoopSound.lean:164`, `:157` | three fields about a run |
| `Stores.WF`, `Stores.HeapNat` | `Laws/Machine/StoresLaws.lean:218`, `Laws/Program/Progress.lean:71` | |
| `Fits` | `Laws/Program/Typed.lean:341` | inductive over `List Val × TyEnv` |

**Missing, and the closest existing shape.**

The predicate itself. `SoundB` (`LoopSound.lean:164`) is **not** the closest shape in kind: it is
a statement about `runP pd s`, a *run* of a `StoreSig` program under the store handler, and
`RSig` has no semantics on purpose (`Sched.lean:36-38`, refusal `SCHED-FB-FIBER-HANDLER`). The
new predicate has to be syntactic, over the `Effects.Program` tree. The closest existing thing in
kind is `CodeMeans` (`Laws/Program/Means.lean:90`), an inductive predicate on `RProgram` with 59
constructors, one per operation shape, whose continuation hypotheses are `∀ v, …`. That is the
template.

**Two shapes, both tested** (probe 1, `scratchpad/scout/P1_typedprog.lean`):

* *Shape A*, one constructor per operation (42 clauses). It compiles, but the first draft was
  **refused by the kernel**: a constructor hypothesis of the form
  `∀ s' v, step = some (s', v) → (A ∧ B ∧ C ∧ TypedProgA … )` gives
  `(kernel) invalid nested inductive datatype 'And', nested inductive datatypes parameters
  cannot contain local variables`. The fix is to hoist the side conditions into a separate
  `structure` and pass it as its own hypothesis. This trap will bite on the very first draft of
  the real file.
* *Shape B*, three clauses (`pure`, `store`, `fiber`) with a 40-arm `AnswerOk Γ s : (op :
  FiberOp) → op.answer → Prop` defined by recursion on the operation. It compiles, `cases` on
  it at a concrete operation works with no cast, and it is the shape I recommend: the 40 arms
  become a `def` (readable, one line each) instead of 40 inductive constructors.

**`FiberOp.answer` in a `∀ answer : op.answer` clause.** Tested, it behaves. Because `FiberOp.answer`
is an `abbrev` with a `match`, `(FiberOp.fork child opts).answer` reduces to `Val`,
`(FiberOp.await t .joinEffect).answer` to `ExitV`, `(FiberOp.guard_ k).answer` to `Option ExitV`,
all by `rfl`, so `.vis (.inr op) k` typechecks against a `Val`-, `ExitV`- or
`Option ExitV`-valued `k` with no transport. Inversion by `cases` at a concrete operation gives
the hypothesis directly (`Scout.typedB_fiber_inv`, stamped `[propext]`).

**One dependent trap, found and stamped.** When the operation *mentions* the answer, as
`FiberOp.sync (v : Val)` does, `subst` on `hok : answer = v` fails with
`failed to create binder due to failure when reverting variable dependencies`, because
`answer : (FiberOp.sync v).answer` mentions `v`. The workaround that compiles is
`show TypedProg Γ t s (.pure (.success answer))` first (which forces the reduced type), then
`rw`. Probe 5 (`P5_s1_arms.lean`) carries the fix in a comment.

**Three structural lemmas the predicate needs, all reproduced and stamped** (probe 6/7,
`P6_bind.lean`, `P7_variance.lean`):

* `TypedProg.bind`, the analogue of `SoundP.bind` (`MeaningSound.lean`, used by every composite
  arm) and `SoundB.thenB` (`LoopSound.lean:199`). Proved by induction on the derivation, with
  a store-monotonicity structure `Later s s'` (`le`/`wf`/`heap`, exactly `LoopSound.StoreOk` at
  `:157`) and `Later.trans`. `[propext]`.
* `TypedProg.widen`, the analogue of `SoundP.widen` / `SoundB.widen` (`LoopSound.lean:176`).
  `[propext, Quot.sound]`.
* `TypedProg.monoΓ`, new, and the one that forced a design change: see §E.2.

**`Γ` is not recoverable from a handle value.** `Val.hasTy v (.fiberOf a e)` is
`match v with | Value.fiber _ => true | _ => false` (`src/Effect4/Program/Typed.lean:55`): it
ignores both type arguments. `Val.validIn s (Val.fiber id) = true` unconditionally
(`Laws/Machine/StoresLaws.lean:111`). DI-17's ruling says this on purpose ("Keep fiberOf
explicitly coarse", `docs/DESIGN-ISSUES.md:91`). So nothing in the value world connects a fiber
handle to the type its fiber was forked at, and every such connection has to come from `Γ`. That
has three consequences the plan's §2 does not carry, all in §E below.

### A.2 S1, `denoteR_typed`

**Consumes, proved:**

| name | file:line | what it gives |
| --- | --- | --- |
| `denoteR` | `Laws/Program/DenoteR.lean:797` | `denoteRWith root p.fuel e p` |
| `denoteRWith` / `denoteLayerWith` | `DenoteR.lean:783`, `:789` | a mutual block, fuel-indexed |
| `denoteEffBody` | `DenoteR.lean:580-690` | the 25 arms |
| `denoteR_zero` … `denoteR_provideService` | `DenoteR.lean:823-1075` | one equation per arm, premise `p.fuel ≠ 0` |
| `denoteFiberAction` | `DenoteR.lean:170-212` | `WithFiberAction → RProgram` |
| `denoteAction` | `DenoteR.lean:216` | `match actionAt root p with …` |
| `actionAt` | `Program/Compile.lean:971` | the point lookup, with `refuse` fallbacks |
| `Checker.inv_*` | `Laws/Program/Typing/CheckInversion.lean:45-471` | 68 inversions, one per arm at every path |
| `Conform…Typing.inv_*` | `Laws/Program/Typing/Inversion.lean:21-130` | 13 of them lifted to `effTy` |
| `effTy` | `Program/Typing.lean:28` | `(check sig env [] e).toOption` |
| `evalTerm_hasTy`, `evalTerm_isSome` | `Laws/Program/Typed.lean:774`, `:830` | |
| `evalTerm_validIn` | `MeaningSound.lean:215` | |
| `causeAdmits_of_forall`, `causeAdmits_combine`, `restore_ok` | `MeaningSound.lean:311`, `:445`, `:461` | the error-column algebra |
| `code_intro_aux` | `Laws/Program/Intro.lean:27` | the induction template: weight descent with a `Node.at_` premise |
| `intro_withFiber` | `Laws/Program/Intro/Fibers.lean:75-120` | the template for the fiber arms |
| `Point.weight`, `weight_child_lt`, `weight_childWith_lt` | `Laws/Program/Intro/Weight.lean:35`, `:40`, `:43` | the measure |
| `at_child_of`, `denoteAt_of_at` | `Weight.lean:19`, `:29` | address bookkeeping |

**How `denoteR` unfolds, read from the arms.**

* `simp only [denoteR]` does **not** reduce anything: it rewrites to `denoteRWith root p.fuel …`
  and stops (tested, probe 2b, output quoted in §B). Every arm has to go through its
  `denoteR_*` equation lemma, each of which carries `p.fuel ≠ 0`, so the first step of every arm
  is `cases hf : p.fuel`. The zero case is `denoteR_zero` (`DenoteR.lean:823`), a
  `FiberOp.frontier`, which under typing must be admitted as a residual, not an exit.
* **fork**: `denoteR root (.withFiber a) p = denoteAction root p` (`denoteR_withFiber`,
  `DenoteR.lean:867`), and `denoteAction` looks the action up: `actionAt root p`
  (`Compile.lean:971`). With the addressing premise, the fork arm reduces to
  `.vis (.inr (.fork (.at_ ((p.child 0).child 0)) opts)) (fun v => .pure (.success v))`
  (tested, probe 2d). So a fork emits `FiberOp.fork` carrying **a `Body.at_` addressing the
  grandchild point**, not a program. The child's environment is `((p.child 0).child 0).env`,
  which is `p.env` (`Point.child` changes only `path` and `fuel`, `Compile.lean:79-80`). The
  body is resolved later: `bodyR interp (.at_ q) = interp.suspendBody (.body q)`
  (`EvaluateR.lean:49-50`), `(interpR root).suspendBody (.body q) = denoteAt root q`
  (`InterpR.lean:305-306`), and `interpR_body` ties the two through `denoteBody`
  (`RuntimeR.lean:77`, `InterpR.lean:191`); then `denoteAt root q = denoteR root e q` whenever
  `Node.at_ (.eff root) q.path = some (.eff e)` (`Weight.lean:29`). **That is how the child's
  typing environment is known**: not from the `FiberOp`, but from the point it carries, and the
  checker's `inv_action_fork` (`CheckInversion.lean:295`) types the child at
  `check sig env (p ++ [0]) program`, the same `env`. The fork answer's type is
  `.fiberOf q.answer q.error` with `error = .never`.
* `forkIn` carries `(p.child 0).child 0` and a scope number resolved by `evalTerm`; if the term
  is not a scope handle, `actionAt` answers `WithFiberAction.refuse (Cause.die Defect.badName)`
  (`Compile.lean:988-992`). `forkScoped` does not appear as an action at all: `actionAt` turns it
  into `.ambientScope` (`Compile.lean:994`), and `denoteFiberAction` re-reads the node to emit
  `ambientScope` then `forkIn` (`DenoteR.lean:203-211`).
* **gen**: `denoteR root (.gen ss) p = suspendR p (.vis (.inr (.gen p)) pure)`, that is
  `.vis (.inr (.suspend p)) (fun _ => .vis (.inr (.gen p)) pure)` (`denoteR_gen`,
  `DenoteR.lean:874`; tested, probe 2e). `FiberOp.gen` answers `ExitV`.
* **loop**: `denoteR root (.iterate ct i t s r b) p = suspendR p (match evalTerm p.env i with |
  some c => .vis (.inr (.loop p c)) pure | none => .pure badShapeExit)` (`denoteR_iterate`,
  `DenoteR.lean:880`; tested, probe 2f). `FiberOp.loop` answers `ExitV` and carries the point and
  the initial cursor `Val`. Both entries are behind one counted `suspend`.
* **bind** is `(guardR .onSuccess (denoteR root a (p.child 0))).bind (seqR fun v => constructR
  fun completed => denoteR root b ({p with completed}.childWith 1 v))` (`denoteR_bind`,
  `DenoteR.lean:827`). Every composite arm has this shape: a `guardR`, a `bind`, a `constructR`.
  `guardR kind body` is `.vis (.inr (.guard_ kind)) (fun | none => body.bind (fun ex => .vis
  (.inr (.unguard ex)) pure) | some ex => .pure ex)` (`DenoteR.lean:69`). So **`guard_`,
  `unguard` and `construction` are the three operations S1 meets most often**, and their clauses
  carry the whole weight of the composite arms.

**Missing for S1, with the closest existing lemma:**

| missing | closest in shape |
| --- | --- |
| `TypedProg` clauses for the 40 operations (`AnswerOk`) | `CodeMeans` (`Means.lean:90`), 59 constructors |
| `TypedProg.bind` | `SoundP.bind`, `SoundB.thenB` (`LoopSound.lean:199`) |
| `TypedProg.guardR`: `guardR kind body` typed from `body` typed | `CodeMeans.onSuccess` (`Means.lean:148`) |
| `TypedProg.constructR`, `TypedProg.prepareR` | `prepareR_denoteR` (`Intro.lean` header) |
| the 25 arms of the induction | `sound`'s 25 arms (`MeaningSound.lean:480-728`) |
| `actionAt` forward-shape lemmas, one per `ActionTerm` constructor (16) plus the two masks | `intro_withFiber`'s inline `simp [actionAt, h]` (`Intro/Fibers.lean:84`, `:98`) |
| `Val.hasTy_fiberOf_inv`, `_scope_inv`, `_list_fiberOf_inv`, `_context_inv`, `_exitOf_inv` | `Val.hasTy_bool_inv` (`Typed.lean:81`), `hasTy_unit_inv` (`:67`), `hasTy_prod_inv` (`:160`) |
| `exitOk_of_noFail`: an interrupt-or-defect-only cause fits every column | reproduced and stamped, probe 8 |
| `effTy`-level inversions for the 12 arms `Typing/Inversion.lean` does not lift | the 13 it does (`Inversion.lean:21-130`) |

`Typing/Inversion.lean` lifts only the arms `MeaningSound`/`LoopSound` needed: `succeed`, `fail`,
`failCause`, `sync`, `suspend`, `perform`, `bind`, `catchCause`, `matchCause`, `onExit`, `exit`,
`select`, `iterate`. It has **nothing** for `withFiber`, `awaitFiber`, `scoped`,
`acquireRelease`, `provideLayer`, `service`, `provideService`, `gen`, `yieldNow`,
`uninterruptible`, `interruptible`, `catchIf`. All twelve exist at the `check` level in
`CheckInversion.lean`. Recommendation: **state S1 over `check nativeSignature tys p.path e =
.ok t`**, not over `effTy`, and use `Checker.inv_*` directly. That is also the path-aware form,
which matches the point discipline, and it costs no new lifting lemmas. `effTy_ok` /
`ok_effTy` (`Typing/Sound.lean`) bridge to `effTy` at the root for the S3 corollary.

**Four arms reproduced end to end** (probe 5, `P5_s1_arms.lean`): `succeed`, `sync`, `yieldNow`
and `withFiber .getId`, each against a shape-B `TypedProg`. All four stamped
`[propext, Quot.sound]`. The `succeed` arm is five lines and reuses `inv_succeed`,
`evalTerm_isSome`, `evalTerm_hasTy`, `evalTerm_validIn`: exactly the lemmas `sound`'s arm uses,
in a *new* proof (see §E.3).

### A.3 S2, `typedState_step`

**Consumes, proved:**

| name | file:line | shape |
| --- | --- | --- |
| `evaluateR` | `Laws/Program/EvaluateR.lean:330` | one fiber step |
| `evaluateRawR` | `EvaluateR.lean:290` | splits `pure` / `vis .inl` / `vis .inr` |
| `evaluateFiberR` | `EvaluateR.lean:156-285` | **the 40-arm dispatcher** |
| `deliverR`, `popR` | `EvaluateR.lean:127`, `:66` | delivery and the `ScopeFrame` pop |
| `prepareScopedExitR`, `prepareIterR` | `EvaluateR.lean:302`, `:322` | the two glue passes |
| `evaluateR_pure/frontier/store/store_missing/suspend/sync` | `Laws/Program/RuntimeR.lean:81-119` | six equations |
| `driveStep` | `src/Effect4/Machine/Fibers.lean:1795` | one command, 18 `Cmd` constructors |
| `driveState` | `Machine/Fibers.lean:1945` | the fuel-bounded command loop |
| `stepDecisionState` | `Machine/Fibers.lean:2058` | one decision, eight arms |
| `replayEval` | `Machine/Fibers.lean:2135` | the tape |
| `MachineOk`, `StepAgrees` | `Laws/Machine/Book.lean:236`, `:622` | the unary invariant slot and the step obligation |
| `book_driveState`, `book_stepDecisionState`, `book_replayEval` | `Book.lean:632`, `:965`, `:1102` | the ladder, **binary** |
| `StoresOk`, `storesOk_syncOpStep`, `storesOk_closeScope` | `Simulation/Hooks.lean:45`, `:175`, `Simulation/Actions.lean:422` | the store invariant already carried |

**What is missing, and it is more than the plan says.**

1. **There is no unary ladder.** `book_driveState` / `book_stepDecisionState` / `book_replayEval`
   are relations between two machines. The only unary thing they carry is `MachineOk StOk`, and
   they carry it for the **left** instance `i₁` only (`StepAgrees`, `Book.lean:626`: the
   `MachineOk` conclusion is about `driveStep i₁ …`). S2 is a unary statement about the term
   instance. So S2 cannot reuse `book_*`; it needs its own four-level ladder. The cheapest form
   is a *generic* one in a new `Laws/Machine/Keeps.lean`, parameterised by a machine predicate
   `P` and a command-list predicate `Q`, with one hypothesis
   `∀ m c r, m.stuck = none → P m → Q (c :: r) → P (driveStep i m c r).1 ∧ Q (driveStep i m c r).2`
   and three derived lemmas (`keeps_driveState`, `keeps_stepDecisionState`, `keeps_replayEval`)
   whose proofs are `book_*`'s inductions with the second machine deleted. `MachineOk StOk` is
   then an instance of it. Closest in shape: `book_driveState` (`Book.lean:632`), 40 lines.
2. **The invariant has to cover the command residue, the dispatcher and the races, not only the
   fibers.** `Cmd.resume (fiber) (token) (answer : κ)` carries code (`Machine/Fibers.lean:703`),
   `Task.resume (target) (token) (answer : κ)` carries code (`:118`), a `Dispatcher` holds tasks
   (`:131-135`), and `Race.programs : List κ` carries code (`:407`). `CmdMeans` and `RaceMeans`
   (`Book.lean:203`, `:191`) relate exactly those. `Pending` is code free (`:84-93`), so parks
   need no clause. The plan's §2 `TypedState` lists fibers, stores, races' entrants and pending
   waits; it does not list the dispatcher tasks or the command residue, and both carry
   `RProgram`.
3. **`ScopeFrame` carries functions.** `ScopeFrame.resume (kind) (next : ExitV → RProgram)` and
   `.answer (next : ExitV → RProgram)` (`InterpR.lean:43-50`). So `TypedFiber`'s stack clause is
   higher order in the same way the `vis` clauses are: `∀ ex s', Later s s' → ExitOk … s' ex →
   TypedProg Γ t' s' (next ex)`. The other five `ScopeFrame` constructors are first order.
4. **The per-operation lemmas are per arm of `evaluateFiberR`, not "per fiber operation on the
   shared scheduler".** The scheduler (`driveStep`) does not see `FiberOp` at all; it sees
   `Cmd`. The fiber operations are dispatched by `evaluateFiberR` (`EvaluateR.lean:156-285`),
   which is the term instance's `FiberEvaluator`. So S2 is really three families:
   40 arms of `evaluateFiberR`, 18 arms of `driveStep`, and the delivery pass
   (`deliverR` plus `popR`'s seven `ScopeFrame` arms plus `prepareScopedExitR`,
   `prepareIterR`). Sixty five arms, not forty.
5. The `Simulation/*` modules (6,008 lines) are the *proofs* of the pairing, not the step. They
   enumerate the same case split, so they are a map of the work, but S2 reuses **no lemma** from
   them: every one of them concludes a `BMeans`/`FMeans`/`IterRel`, which is binary. The one
   thing S2 does reuse is the store-invariant family (`storesOk_*`, `Simulation/Hooks.lean:45-180`,
   `Simulation/Deliver.lean:409`, `Simulation/Actions.lean:422`), which is unary. Those four or
   five lemmas should move out of `Simulation/*` (see §D).

### A.4 S3, the transfer

**Consumes, proved:**

| name | file:line | statement |
| --- | --- | --- |
| `BMeans` | `Laws/Program/Simulation/Fibers.lean:38` | `BookMeans (CodeMeans root) (Means root)` |
| `replay_rel` | `Laws/Program/RuntimeR.lean:162` | every tape, every budget, `ReplayRel` |
| `BMeans.exitOf` | `RuntimeR.lean:239` | **per fiber**: `∀ (id : FiberId), (m₁.fiber? id).bind RunFiber.exit = (m₂.fiber? id).bind RunFiber.exit` |
| `run_eq_ref` | `RuntimeR.lean:211` | outcome and `obs` agree, empty table |
| `run_eq_ref_exit` | `RuntimeR.lean:248` | **root only**: `(Api.replay e fuel tape).exit = ((replayR …).machine.fiber? Api.root).bind RunFiber.exit` |
| `obs` | `Laws/Machine/Behaviour.lean:49` | `⟨m.fibers.map (f.id, f.exit), m.state⟩`, every fiber |
| `TypedProgram` | `src/Effect4/Program/CheckedTyping.lean:19` | `ty` and `typeOfProgram sig program = some ty` |
| `TypedProgram.run_sound`, `run_soundB` | `Laws/Program/TypedRun.lean:83`, `:112` | the straight and looped machine corollaries |
| `typeOfProgram_looped` | `TypedRun.lean:75` | on `Looped`, the checker is `effTy` |

**Per fiber or only the root?** Both are available. `BMeans.exitOf` is quantified over every
`FiberId` (checked with `#check`, output in §B), so a per-fiber corollary is one line;
`run_eq_ref_exit` merely instantiates it at `Api.root`. Independently, `run_eq_ref`'s second
conjunct is `obs … = obsR …`, and `obs` is the whole list of `(id, exit)` pairs
(`Behaviour.lean:49-50`), so every fiber's exit already agrees as a list. The plan's S3 is
therefore one theorem, as it says, and the "every fiber exit in `obs`" phrasing is the one that
needs no new lemma at all.

**Missing for S3:** only the statement and its corollaries. `TypedProgram.run_typed`, the
whole-alphabet analogue of `run_sound`/`run_soundB`; the no-`badShape` corollary; the DI-17
guard-delivery corollary. Each is a few lines given S2. Closest in shape:
`TypedProgram.run_soundB` (`TypedRun.lean:112`), eight lines.

### A.5 `SoundB`: generalise or restate?

**Restate.** `SoundB pw pd s answer error` (`LoopSound.lean:164`) has three fields, all about
`runP pd s`: `independent`, `exit`, `stores`. `runP` runs a `Effects.Program StoreSig` under
`storeHandler` in `StateT Stores Id`. There is no such run for `RSig` and there must not be one:
`fiberRefusal` is explicitly not a semantics (`Sched.lean:36-38`, `:216`), and `RDEN-FB-HANDLER`
(`DenoteR.lean:29-31`) forbids using `rHandler` to interpret a frontier as a finished result. A
parameter over the signature would not help either, because `SoundB`'s `independent` field is
about the wrong-shape-exit parameter `bad`, which `denoteR` does not take at all (`denoteR` uses
`badShapeExit` literally, e.g. `DenoteR.lean:584`).

So the new predicate is a fresh inductive that borrows `SoundB`'s *content* (exit fits, stores
stay inside the invariant) and none of its *form*. What does carry over verbatim is
`StoreOk` (`LoopSound.lean:157`), which is exactly the `Later s s'` structure the composition
lemma needs; reuse it by name rather than defining a second one.

---

## B. Probes: commands and outputs

All run from `/Users/pooks/Dev/lean4-effect4` with
`lake env lean <scratchpad>/scout/<file>.lean`. The scratchpad path is
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/131bb391-fca6-4e88-a9fb-f63a8eeec300/scratchpad/scout`.

### B.1 `P3_signatures.lean`: the cited statements

`#check` of 27 declarations. The three that matter:

```
@BMeans.exitOf : ∀ {root : NativeEff} {m₁ : FMachine} {m₂ : RState},
  BMeans root m₁ m₂ →
    ∀ (id : FiberId), (RunMachine.fiber? m₁ id).bind RunFiber.exit
                    = (RunMachine.fiber? m₂ id).bind RunFiber.exit

run_eq_ref_exit : ∀ (e : NativeEff) (fuel : Nat) (tape : List Api.Decision),
  (Api.replay e fuel tape).exit
    = ((ReplayResult.machine (replayR e fuel tape)).fiber? Api.root).bind RunFiber.exit

evaluateR_store : ∀ (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (op : SyncOp)
  (k : Val → RProgram) (state : Stores) (value : Val),
  syncOpStep op m.state = some (state, value) →
    evaluateR interp m (answerR f (Effects.Program.vis (Sum.inl op) k)) yielding =
      { machine := { … m with state := state … },
        fiber := answerR (answerR f (…)) (k value), yielding := yielding,
        outcome := Outcome.answered, nested := [Cmd.drainDue] }
```

`book_stepDecisionState`'s conclusion is
`MachineOk StOk (stepDecisionState i₁ fuel a decision).fst ∧ BookMeans C S … ∧ …`: the unary
half is about `i₁` only, which is the §A.3 finding.

### B.2 `P2_denoteR_reduce.lean` and `P2b_denoteR_unfold.lean`: how `denoteR` reduces

`P2_denoteR_reduce.lean` compiles clean. It shows: `denoteR_bind` fires by `rw`; the fork arm
with the addressing premise reduces to `.vis (.inr (.fork (.at_ ((p.child 0).child 0)) opts))
(fun v => .pure (.success v))` by `rw [denoteR_withFiber …]; have hact : actionAt root p = …
:= by simp [actionAt, h]; unfold denoteAction; rw [hact]; rfl`; `gen` and `iterate` reduce as
quoted in §A.2.

`P2b_denoteR_unfold.lean` deliberately mis-states the right-hand side so the residual goal
prints:

```
⊢ denoteRWith root p.fuel (Eff.bind a b) p = pending PendingReason.compileFuel p
```

after `simp only [denoteR]`, and

```
⊢ Effects.Program.bind (guardR GuardKind.onSuccess (denoteRWith root k a (p.child 0)))
      (seqR fun v => constructR fun completed =>
          denoteRWith root k b ({ path := p.path, env := p.env, fuel := k + 1, tape := p.tape,
              completed := completed, root := p.root }.childWith 1 v))
    = pending PendingReason.compileFuel p
```

after `simp only [denoteR, hf, denoteRWith, denoteEffBody]`. Conclusion: **`simp only [denoteR]`
alone reduces nothing**; the `denoteR_*` equations are the route and each needs the fuel case
split first.

### B.3 `P1_typedprog.lean`: the predicate, two shapes

First run: `error: (kernel) invalid nested inductive datatype 'And', nested inductive datatypes
parameters cannot contain local variables` at the shape-A declaration. After hoisting the four
side conditions into `structure StoreStepOk`, both shapes compile:

```
'Scout.typedA_pure_exit' depends on axioms: [propext]
'Scout.typedB_fiber_inv' depends on axioms: [propext]
```

### B.4 `P5_s1_arms.lean`: four arms of S1

```
'Scout.arm_succeed' depends on axioms: [propext, Quot.sound]
'Scout.arm_sync' depends on axioms: [propext, Quot.sound]
'Scout.arm_yieldNow' depends on axioms: [propext, Quot.sound]
'Scout.arm_getId' depends on axioms: [propext, Quot.sound]
```

Before the fix, `arm_sync` failed with
`failed to create binder due to failure when reverting variable dependencies` and `arm_getId`
with `Application type mismatch: rfl … but is expected to have type Val.validIn s answer = true`.
The second is the reason every value-answering clause of `AnswerOk` must carry `validIn` beside
`hasTy`: `ExitOk` at a success wants both (`MeaningSound.lean:285-287`).

### B.5 `P6_bind.lean` and `P7_variance.lean`: the structural lemmas

```
'Scout.TypedProg.bind' depends on axioms: [propext]
'Scout.TypedProg.widen' depends on axioms: [propext, Quot.sound]
'Scout.AnswerOk.anti' depends on axioms: [propext]
'Scout.TypedProg.monoΓ' depends on axioms: [propext]
```

`P6`'s first `monoΓ` attempt failed:

```
error: Application type mismatch: The argument h2 has type AnswerOk Γ' s' op answer
but is expected to have type AnswerOk Γ s' op answer
```

That is the variance finding of §E.2. `P7` is the repaired version.

### B.6 `P8_guard.lean`: interrupt-only exits

```
'Scout.exitOk_of_noFail' depends on axioms: [propext, Quot.sound]
```

`exitOk_of_noFail (a e : Ty) (s : Stores) (c : CauseV) (h : ∀ r ∈ c.reasons, ∀ e a, Reason.fail
e a ≠ r) : ExitOk a e s (.failure c)`, and `Cause.interrupt who` (`Machine/Cause.lean:652`)
satisfies it. This is the plan's risk 4 as a lemma, and it is three lines.

### B.7 `P9_evaluateR_move.lean`: the six `evaluateR_*` equations move

All six compile with only `import Effect4.Laws.Program.EvaluateR` and
`import Effect4.Laws.Machine.Behaviour`:

```
'Effect4.Program.Sched.evaluateR_store'' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.evaluateR_sync'' depends on axioms: [propext, Quot.sound]
```

and they have **no consumers anywhere** outside `RuntimeR.lean`
(`grep -rn --include="*.lean" -E "evaluateR_(pure|frontier|store|store_missing|suspend|sync)\b"
src Test` returns nothing else).

### B.8 `#auto_census` (probe 4)

```
Effect4.Laws.Program.LoopSound: 1 of 19 theorems closed from their statements; 5 source lines
  5  46-50  Effect4.Program.Denote.iterateStepWith_badShape  [propext]

Effect4.Laws.Program.MeaningSound: 0 of 37 theorems closed from their statements; 0 source lines

Effect4.Laws.Program.Typing.CheckInversion: 65 of 68 theorems closed from their statements;
  353 source lines they now take
```

Every closed `CheckInversion` proof is `[Quot.sound, propext]`. Reading: the checker's rule set
is fully productive, the soundness modules' is not. S1's *inversion* step is free from the
existing rules; S1's *denotation* step is not, and needs its own.

### B.9 `P10_aesop.lean`: what `aesop` closes of the S1 arms

Final run is silent (all three theorems proved), stamped:

```
'Scout.aesop_succeed' depends on axioms: [propext, Quot.sound]
'Scout.aesop_sync'    depends on axioms: [propext, Quot.sound]
'Scout.aesop_yieldNow' depends on axioms: [propext, Quot.sound]
```

Three intermediate failures, each a finding:

* With `attribute [aesop safe constructors] TypedProg` alone, `succeed` stopped at
  `⊢ Val.validIn s val = true`: the forward rule `evalTerm_validIn` could not fire because
  `TypedAt.valid`'s `∀`-shaped conclusion was not in context. `have hvalid := hat.valid` before
  the call fixes it, and then `succeed` closes outright.
* `sync` and `yieldNow` stopped at the goal `TypedProg Γ t s (.vis (.inr (FiberOp.sync …)) k)`:
  **`aesop` will not apply the `fiber` constructor**, because the constructor's `op` index
  determines the dependent type of `k`, and that unification is higher order. The fiber arms need
  an explicit `refine .fiber <op> _ ?_ ?_ ?_` first.
* With `attribute [aesop safe destruct] Later.le Later.wf Later.heap`, `sync` was left with
  `⊢ s'.WF` while `Stores.HeapNat s'` had been derived: **`destruct` clears the hypothesis**, so
  only one projection survives. Switching to `safe forward` closes it.

---

## C. The aesop setup, proposed

All of this is a proposal in code blocks. Nothing is applied.

### C.1 What to register, and where

In the new `Laws/Program/Typed/Residual.lean` (see §D), beside the definitions:

```lean
-- the predicate's own introduction rules; safe, they are the only way in
attribute [aesop safe constructors] TypedProg

-- the answer predicate is a definition with 40 arms: normalise it so a concrete
-- operation reduces its clause away
attribute [aesop norm simp] AnswerOk

-- the store-monotonicity accessors.  FORWARD, never destruct: `destruct` clears the
-- hypothesis and only the first projection survives (probe 10, §B.9).
attribute [aesop safe forward] Later.le Later.wf Later.heap

-- the exit-shape predicate is a `def` by cases on the exit
attribute [aesop norm unfold] ExitOk

-- store monotonicity of validity
attribute [aesop safe forward] Val.validIn_mono
```

In `Laws/Auto/Denotation.lean`, a new shared module beside `Laws/Auto/Inversion.lean`, holding
the `denoteR` equations as normalisation rules. They all carry `p.fuel ≠ 0`, so they are
conditional rewrites and `aesop` discharges the side condition from the context:

```lean
attribute [aesop norm simp]
  denoteR_succeed denoteR_fail denoteR_failCause denoteR_sync denoteR_suspend
  denoteR_perform denoteR_bind denoteR_gen denoteR_catchCause denoteR_catchIf
  denoteR_matchCause denoteR_onExit denoteR_exit denoteR_uninterruptible
  denoteR_interruptible denoteR_select denoteR_iterate denoteR_yieldNow
  denoteR_awaitFiber denoteR_withFiber denoteR_scoped denoteR_acquireRelease
  denoteR_provideLayer denoteR_service denoteR_provideService
```

In the same module, the checker inversions as `safe destruct` (they are implications from a
successful check to an existential; `destruct` is right because the premise is consumed):

```lean
attribute [aesop safe destruct]
  Checker.inv_succeed Checker.inv_fail Checker.inv_failCause Checker.inv_sync
  Checker.inv_suspend Checker.inv_perform Checker.inv_bind Checker.inv_gen
  Checker.inv_catchCause Checker.inv_catchIf Checker.inv_matchCause Checker.inv_onExit
  Checker.inv_exit Checker.inv_uninterruptible Checker.inv_interruptible
  Checker.inv_select Checker.inv_iterate Checker.inv_yieldNow
  Checker.inv_awaitFiber_join Checker.inv_awaitFiber_await Checker.inv_withFiber
  Checker.inv_scoped Checker.inv_acquireRelease Checker.inv_provideLayer
  Checker.inv_service Checker.inv_provideService
  Checker.inv_action_fork Checker.inv_action_forkIn Checker.inv_action_forkScoped
  Checker.inv_action_runIn Checker.inv_action_interrupt Checker.inv_action_interruptScoped
  Checker.inv_action_interruptAll_self Checker.inv_action_interruptAll_by
  Checker.inv_action_awaitAll Checker.inv_action_awaitAllFailFast
  Checker.inv_action_snapshotChildren Checker.inv_action_awaitNewChildren
  Checker.inv_action_raceAll Checker.inv_action_setContext Checker.inv_action_getContext
  Checker.inv_action_getId Checker.inv_action_closeScope
```

Per call, never in a rule set (each introduces the environment fact the arm needs and would
otherwise fire on every goal):

```lean
aesop (add safe forward [evalTerm_isSome, evalTerm_hasTy, evalTerm_validIn,
                         TypedAt.wf, TypedAt.heap])
```

with `have hfits := hat.fits` and `have hvalid := hat.valid` introduced by hand first. That exact
call closes the `succeed` arm (tested).

### C.2 New small lemmas the search will need

```lean
/-- A value of a fiber type is a handle.  `Val.hasTy` at `.fiberOf` ignores both type
arguments (`Program/Typed.lean:55`), so this is all it gives, and it is what the fork and
await clauses need. -/
theorem Val.hasTy_fiberOf_inv {v : Val} {a e : Ty} (h : Val.hasTy v (.fiberOf a e) = true) :
    ∃ id, v = Val.fiber id

/-- Likewise for the three other handle shapes `actionAt` reads. -/
theorem Val.hasTy_scope_inv {v : Val} (h : Val.hasTy v Ty.scope = true) :
    ∃ s, v = Val.scopeHandle s
theorem Val.hasTy_context_inv {v : Val} (h : Val.hasTy v Ty.context = true) :
    ∃ c, Val.context? v = some c

/-- The `.list` arm admits TWO shapes (`Program/Typed.lean:72-79`): a `Value.fiberSnapshot`
read back by `Val.snapshot?`, and an ordinary `Val.list` each of whose members is a handle.
The interrupt-family and children clauses have to take both, because `actionAt`'s `handles`
reader takes both (`Program/Compile.lean:981-985`). -/
theorem Val.hasTy_list_fiberOf_inv {v : Val} {a e : Ty}
    (h : Val.hasTy v (.list (.fiberOf a e)) = true) :
    (∃ ids, Val.snapshot? v = some ids) ∨
      (∃ vs, v = Val.list vs ∧ ∀ x ∈ vs, ∃ id, x = Val.fiber id)

/-- An interrupt-or-defect cause fits every error column: the plan's risk 4.
Reproduced and stamped in probe 8. -/
theorem exitOk_of_noFail (a e : Ty) (s : Stores) (c : CauseV)
    (h : ∀ r ∈ c.reasons, ∀ err ann, Reason.fail err ann ≠ r) : ExitOk a e s (.failure c)

/-- One per `ActionTerm` constructor (16) plus the two masks: the forward shape of the point
lookup.  Each is `by simp [actionAt, h]`, as `Intro/Fibers.lean:84` does inline. -/
theorem actionAt_of_fork {root : NativeEff} {p : Point} {b : NativeEff}
    {o : Supervision.ForkOptions}
    (h : Node.at_ (.eff root) p.path = some (.eff (.withFiber (.fork b o)))) :
    actionAt root p = some (.fork (resolve root ((p.child 0).child 0)) o)

/-- Γ lookup, in the `∀`-form the variance argument forces (§E.2). -/
theorem Table.mono_get {Γ Γ' : Table} (h : ∀ id ty, Γ id = some ty → Γ' id = some ty)
    {id : FiberId} {ty : EffTy} : Γ id = some ty → Γ' id = some ty
```

### C.3 What to keep OUT of the rule set

* `TypedProg.bind`. It is a transitivity: applying it backwards leaves `tb` a metavariable. Pass
  it per call, as `AGENTS.md` says of transitivities.
* `TypedProg.widen` and `TypedProg.monoΓ`, for the same reason (`t'` and `Γ'` are metavariables
  in the backward direction).
* `Ty.hasTy_join_left` / `hasTy_join_right`. They split the target type and loop with `Ty.join`
  normalisation.
* `denoteR` itself as `norm unfold`. It unfolds to `denoteRWith root p.fuel` and then stalls
  (probe 2b); the equations do the work and the unfold only makes the goal bigger.
* `ExitOk.widen`, `ExitOk.later`. Both create type metavariables.
* Any `Later`/`StoreOk` accessor as `destruct` (probe 10, §B.9).

### C.4 Which arms `aesop` closes, and which need a hand `cases` first

From the three arms tested plus the shape of the rest:

**Expected to close from the rules plus a hand induction hypothesis** (the arm's whole content is
an inversion, an `evalTerm` fact and one constructor): `succeed`, `fail`, `failCause`, `sync`,
`yieldNow`, `service`, `snapshotChildren`, `getContext`, `getId`, `setContext`,
`suspend` (one `ih`), `uninterruptible`/`interruptible` (one `hres`). Twelve or thirteen of the
twenty five.

**Needs an explicit step first, with the reason:**

| arm | what has to be done by hand | why |
| --- | --- | --- |
| every arm emitting a `vis (.inr op)` | `refine .fiber <op> _ ?_ ?_ ?_` | the constructor's `op` index fixes the dependent type of `k`; `aesop` will not solve that unification (tested, §B.9) |
| `withFiber` (all 16 actions) | `cases a` then `rw [hact]` where `hact : actionAt root p = …` | `denoteAction` is a lookup at the point, not structural on the action; the case split is on the *lookup's* answer |
| `bind`, `catchCause`, `catchIf`, `matchCause`, `onExit`, `exit` | `refine TypedProg.bind ih ?_` | `bind` is a transitivity, kept out of the rule set |
| `bind`, `catchCause`, `matchCause`, `onExit` | `cases` on the body's exit (`success` / `failure`) | the continuation's type differs per branch, as in `sound`'s `bind` arm (`MeaningSound.lean:503-518`) |
| `awaitFiber` | `cases evalTerm p.env t`, then `cases p.awaitExit ⟨id⟩ mode`, then `cases mode` | three nested matches (`DenoteR.lean:647-655`) and the construction-view shortcut |
| `select` | `cases (evalTerm p.env s).bind d.decide` | three-way match with a `badShapeExit` arm |
| `iterate`, `gen` | `cases evalTerm p.env initial` / unfold `walkR` | the loop and generator entries are frontier-shaped |
| `perform` | `cases op`, then `cases (NativeOp.row op).kind` | external-first routing then the three kinds (`DenoteR.lean:594-603`) |
| `provideLayer`, `acquireRelease`, `provideService`, `scoped` | a hand `rw` chain | each expands to four or more `guardR`/`seqR` levels (`DenoteR.lean:525-571`, `:662-690`) |
| every `p.fuel = 0` case | `cases hf : p.fuel` | every `denoteR_*` equation is conditional |

---

## D. File placement and the smallest reorg

Closures computed by walking `import` lines over `src/`; "lines" is the sum of the closure's
source lines. Both roots are built, so these are compile-cost proxies, not measurements.

### D.1 The closures as they stand

| module | closure | lines | `Simulation/*` + `Book` in it |
| --- | --- | --- | --- |
| `Laws/Program/Sched` | 41 | 27,995 | 0 |
| `Laws/Program/DenoteR` | 44 | 31,621 | 0 |
| `Laws/Program/InterpR` | 49 | 37,802 | 0 |
| `Laws/Program/EvaluateR` | 50 | 38,145 | 0 |
| `Laws/Program/Typing/CheckInversion` | 30 | 20,335 | 0 |
| `Laws/Program/MeaningSound` | 116 | 74,686 | 0 |
| `Laws/Program/LoopSound` | 117 | 75,238 | 0 |
| `Laws/Machine/Book` | 24 | 23,774 | 1 |
| `Laws/Program/Simulation/Drive` | 128 | 72,183 | 8 |
| `Laws/Program/RuntimeR` | 133 | 75,109 | 9 |
| `Laws/Program/TypedRun` | 132 | 81,514 | 1 (`Book` only) |

`MeaningSound` and `InterpR` are **independent**: neither is in the other's closure, and
`MeaningSound`'s closure does not contain `DenoteR` at all. A file importing both is the first
place in the tree where the store-side soundness graph and the `RSig` denotation meet. There is
no cycle risk: nothing under `MeaningSound` or `InterpR` can import the new file.

### D.2 The proposed placement, with its cost

```
Laws/Program/Typed/Residual.lean      -- §2: Later (reuse StoreOk), AnswerOk, TypedProg,
  imports LoopSound, InterpR,            --      bind / widen / monoΓ, the exit-shape lemmas,
          Typing/CheckInversion          --      the aesop rules
                                         --  121 modules, 77,551 lines, 0 Simulation/Book

Laws/Program/Typed/Denotation.lean    -- S1: denoteR_typed, the 25 arms + the layer companion
  imports Typed/Residual,                --  needs the weight descent: see D.3
          (the weight lemmas)            --  121 modules if D.3 is taken, 128 otherwise

Laws/Program/Typed/State.lean         -- §2: TypedState, TypedFiber, the machine clauses
  imports Typed/Denotation, EvaluateR    --  122 modules, 77,894 lines, 0 Simulation/Book

Laws/Program/Typed/Step/*.lean        -- S2: one file per operation family, mirroring
  imports Typed/State                    --      Simulation/*: Fibers, Scope, Race, Deliver,
                                         --      Walk, Commands.  Same closure as State.

Laws/Machine/Keeps.lean               -- the generic unary ladder (§A.3 item 1)
  imports Machine/Fibers only            --  small; `Book.lean`'s closure minus the book

Laws/Program/Typed/Transfer.lean      -- S3: through replay_rel and BMeans.exitOf
  imports Typed/Step/*, RuntimeR         --  148 modules, 88,584 lines, 9 Simulation/Book
```

**The Simulation tree enters exactly once, at the last file.** Delta from
`Typed/Step` to `Typed/Transfer`: 26 modules, 10,690 lines, all nine of
`Book`, `Simulation/{Actions,Deliver,Drive,Evaluate,Fibers,Hooks,Pending,Walk}`. That is the
number the placement is protecting.

If instead S3's corollaries go into `TypedRun.lean` (as the plan proposes), `TypedRun`'s closure
grows from 132/81,514 to 152/89,729: **+20 modules, +8,215 lines**, and `TypedRun` acquires the
whole `Simulation/*` tree. `TypedRun` today has only `Book` from that group. I recommend the
separate `Typed/Transfer.lean` and leaving `TypedRun.lean` where it is; re-export from
`TypedRun` is not possible without the import, so the corollaries simply live in the new file.

### D.3 Three moves, each cheap, each with its consumer list

**Move 1: the six `evaluateR_*` equations, `RuntimeR.lean:81-119` into `EvaluateR.lean`.**
Tested (probe 9): they compile against `EvaluateR` alone. **Consumers: none**, anywhere in
`src/` or `Test/` (grep in §B.7). Cost: 2 files touched. Payoff: S2 can use them without
importing `Book` and the Simulation tree. Without this move, `Typed/Step/*` would have to import
`RuntimeR` and the 26-module delta lands at S2 instead of S3.

**Move 2: the address and weight lemmas, `Intro/Weight.lean:19-77` into a new
`Laws/Program/PointWeight.lean` (or into `DenoteR.lean`, which already holds the
`Point.*_fuel` lemmas at `:805-812`).** The pieces are `at_child_of`, `at_childWith_of`,
`denoteAt_of_at`, `Point.weight`, `weight_child`, `weight_child_lt`, `weight_childWith_lt`,
`weight_completed`, `fuel_child_le`, `weight_redirect_le`, `Point.spineWalk`,
`foldl_child_eq_spineWalk`, `Point.spineChild_eq`. Read: they mention only `Point`, `Node.at_`,
`denoteAt` and `omega`. The rest of `Weight.lean` (`suspendBodyAt_*`, `resolve_intro_of`,
`entrants_intro`, the `actionAt_*` shape lemmas, `finalizer_intro`) is pairing work and stays.
Measured: importing `Intro/Weight` into the proposed `Typed/Residual` closure adds **7 modules,
2,818 lines**, namely `Intro/{Identity,Equations,Prepare,Weight}`, `Means`, `Book`,
`EvaluateR`, because `Intro/Identity` imports `Means`. Consumers of the moved names, all inside
`Laws/`: `Intro.lean`, `Intro/{Sequential,Fibers,Errors,Scope,Region,Memo,Merge,Layer,
AcquireRelease}.lean`, `Agreement/Loop.lean`, `Simulation/*`. Cost: 1 new file, `Weight.lean`
gains one import, no other file changes (the names keep their namespace
`Effect4.Program.Sched` / `_root_.Effect4.Program.Point`). **Assumed**: I did not compile the
extracted file; the reading of its dependencies is from the source, not from a build.

**Move 3: the unary store-invariant lemmas out of `Simulation/*`.**
`StoresOk` (`Simulation/Hooks.lean:45`), `storesOk_empty` (`:47`), `storesOk_of_deferreds`
(`:54`), `storesOk_wakeList` (`:163`), `storesOk_syncOpStep` (`:175`),
`storesOk_closeScopeUnsafe` (`Simulation/Deliver.lean:409`), `storesOk_closeScope`
(`Simulation/Actions.lean:422`) are unary facts about `Stores`, sitting in modules whose purpose
is the binary pairing. S2 needs them. Consumers, all inside `Laws/`: `Simulation/*` and
`RuntimeR.lean` (`load_ok`). Moving them to `Laws/Machine/StoresOk.lean` costs 3 files touched
and lets `Typed/Step/*` keep its zero-Simulation closure. **Assumed**: I did not check whether
`storesOk_closeScope` needs anything else from `Simulation/Actions.lean`; it is stated over
`root` and `completed`, so it may have to stay.

**Nothing moves that has a consumer outside `Laws/`.** Checked: the `evaluateR_*` names have no
consumers at all; the `Weight.lean` and `StoresOk` names are used only under
`src/Effect4/Laws/`. `RuntimeR.lean`'s own theorems do have consumers outside `Laws/`
(`Test/Program/SimulationContract.lean:42,68,79,103-121`, `Test/Program/CatchIfContract.lean:72`)
and `Laws/Program/ReasonsR.lean:184-228`, so `RuntimeR.lean` itself must not be renamed or
split beyond removing the six unreferenced equations.

### D.4 The battery

`Test/Program/TypedStateContract.lean`, as the plan says, must be reachable from
`Test/All.lean`. An agent may not edit `Test/All.lean` (`AGENTS.md` "Working"), so the
coordinator adds that import at the merge.

---

## E. Corrections to the plan

**E.1 S1 is not an induction on `e`.** The plan's §3 says "by induction on `e`". It cannot be.
`denoteR` is one half of a mutual block with `denoteLayerWith` (`DenoteR.lean:783-793`), and
three of its arms leave the subterm entirely: `withFiber` goes through `denoteAction` and
`actionAt root p`, a **lookup at the root by path** (`DenoteR.lean:216`, `Compile.lean:971`);
`fork`/`forkIn`/`mask`/`scoped` carry `Body`s resolved later by `denoteAt root q`
(`InterpR.lean:99`); `provideLayer` descends into `denoteLayer`. The tree already solved this:
`code_intro_aux` (`Intro.lean:27`) is an induction on a natural number bounding `p.weight`, with
the premise `Node.at_ (.eff root) p.path = some (.eff e)`, and `resolve_intro_of` /
`layer_intro` as its companions. S1 must have the same shape: a weight induction, the
addressing premise, and three statements (programs, layers, resolved points) rather than one.
The fix also changes the statement: `TypedProg Γ t s (denoteR root e p)` needs
`Node.at_ (.eff root) p.path = some (.eff e)` as a premise, and the checker path must be
`p.path`.

**E.2 The `Γ` clauses must read the table in `∀`-form, not `∃`-form.** The plan's §2 writes the
clauses as facts: "a fork's `Val` is a handle whose type is the child's `fiberOf`; an `await
target`'s `ExitV` fits `Γ target`". Written as `∃ ty, Γ target = some ty ∧ …`, the answer
predicate is **monotone** in `Γ`; since it sits in a *hypothesis* position of the operation
clause, `TypedProg` is then **antitone** in `Γ`, and a fork, which extends `Γ`, destroys typing.
Tested: `P6_bind.lean` fails with
`Application type mismatch: h2 has type AnswerOk Γ' s' op answer but is expected to have type
AnswerOk Γ s' op answer`. The repair, tested in `P7_variance.lean` and stamped `[propext]`:
every clause that *reads* the table reads it as `∀ ty, Γ x = some ty → …`, and no clause asserts
`Γ id = some ty` positively. `AnswerOk` is then antitone, `TypedProg` monotone, and
`TypedProg.monoΓ` holds. Coverage ("`Γ` types every live fiber") is asserted by `TypedState`,
which is a positive statement about the machine and is re-established at each fork by
construction. The plan's §5 risk 1 says `TypedState` is `∃ Γ` and the fork case extends it: that
is right, but it only works with this variance.

**E.3 A fiber handle carries no type, so `TypedAt` is not enough.** `Val.hasTy v (.fiberOf a e)`
ignores `a` and `e` (`Program/Typed.lean:55`), and DI-17 rules that on purpose
(`docs/DESIGN-ISSUES.md:91`, "Keep fiberOf explicitly coarse"). `Val.validIn s (Val.fiber id)`
is `true` unconditionally (`Laws/Machine/StoresLaws.lean:111`). So from
`TypedAt tys p.env s` and `tys[i]? = some (.fiberOf a e)` one learns only that `env[i]` is
*some* handle. The `await x` arm's clause, which wants "the delivered exit fits the type the
checker gave `x`", therefore has no premise to hang on. A fourth field is needed on the
invariant, in `∀`-form so E.2 still holds:

```lean
/-- Every fiber handle in scope at a fiber type is typed by the table no more loosely than
its static type says. -/
def HandlesFit (Γ : Table) (tys : TyEnv) (env : List Val) : Prop :=
  ∀ i a e id ety, tys[i]? = some (.fiberOf a e) → env[i]? = some (Val.fiber id) →
    Γ id = some ety → Ty.sub ety.answer.normalize a.normalize = true ∧
                      Ty.sub ety.error.normalize e.normalize = true
```

This has to be threaded through `TypedAt.push` (a `bind` binding a fork's handle extends both
`tys` and `env`) and through every arm of S1. It is the single largest omission in the plan's §2
and it touches every statement.

**E.4 `p.completed` is a third place `Γ` enters.** `denoteR root (.awaitFiber t mode) p` answers
from `p.awaitExit ⟨id⟩ mode` (`DenoteR.lean:649`, `Compile.lean:120`) when the construction view
already holds the target's exit, and `constructR` threads that view into every composite arm
(`DenoteR.lean:53`, `:59`). So S1's premise list needs "every `(id, ex)` in `p.completed` has
`ex` fitting `Γ id`", again in `∀`-form. The plan does not mention `completed`.

**E.5 The store arms do not "carry over".** The plan's S1 says "The store arms are `sound`'s and
`soundB`'s arms ... which is why those arms carry over". They do not, in the literal sense:
`sound` concludes `SoundP (denoteWith bad e env) (denote e env) s t.answer t.error`, a statement
about `runP` of a `StoreSig` program (`MeaningSound.lean:291`), and there is no run for `RSig`.
What carries over is the *lemma set*, not the *arms*: `inv_*`, `evalTerm_isSome`,
`evalTerm_hasTy`, `evalTerm_validIn`, `TypedAt.push`, `causeAdmits_*`, `restore_ok`,
`reify_ok`, `exitOk_fail`. Reproduced: `arm_succeed` (probe 5) reuses four of those lemmas and
is a fresh five-line proof. The control-erasure remark (`DenoteR.lean:23-26`) is about the
*straight fragment after erasure*, which is a different statement from "the arms carry over" and
is not usable as a proof step here.

**E.6 S2's case split is 65 arms, not 40.** See §A.3 item 4: 40 arms of `evaluateFiberR`
(`EvaluateR.lean:156-285`), 18 of `driveStep` (`Machine/Fibers.lean:1795`, `Cmd` has 18
constructors), and seven `ScopeFrame` arms in `popR` (`EvaluateR.lean:66`). The plan's
"one lemma per fiber operation, proved once, because the scheduler is one piece of code" is right
in spirit and short by 25 arms in count.

**E.7 The `book_*` ladder is binary and cannot carry S2.** `StepAgrees` (`Book.lean:622`) states
the unary `MachineOk StOk` conclusion for `i₁` only. S2 is unary at `i₂`. A new generic ladder is
needed (§A.3 item 1, §D.2 `Laws/Machine/Keeps.lean`). The plan's S2 reads as if
`book_stepDecisionState` could be reused; it cannot.

**E.8 The invariant must cover the command residue, the dispatcher and the races.** §A.3 item 2:
`Cmd.resume`, `Task.resume` and `Race.programs` all carry `RProgram`. The plan's `TypedState`
lists fibers, stores, races' entrants and pending waits; "entrants" in `Race` is
`state.live`, a `FiberId` set, while `Race.programs : List κ` is the code and is a separate
field (`Machine/Fibers.lean:403`, `:407`). `RaceAllState` holds three `List FiberId` fields,
`unstarted`, `starting` and `live` (`src/Effect4/Machine/Supervision.lean:30-33`), none of which
carries code; `Race.programs` is the code field and needs its own clause.

**E.9 One drafting trap, for the implementer.** A constructor hypothesis may not put the
inductive under an `And`: the kernel refuses it as a nested inductive (tested, §B.3). Hoist
side conditions into a `structure`. The natural first draft of the store clause hits this.

**E.10 A second drafting trap.** `subst` fails on `answer = v` when the operation mentions `v`
(`FiberOp.sync v`, `FiberOp.loop p v`, `FiberOp.refuse c`): `show` the reduced type first, then
`rw` (tested, §B.4).

**E.11 The `Simulation/*` figure is wrong.** The plan's §1 says
"`Simulation/{Deliver,Drive,Evaluate,Hooks,Pending,Walk}.lean`, 9,400 lines". Measured with
`wc -l`: those six are **4,747** lines, and all eight files of the directory (adding
`Actions.lean` 793 and `Fibers.lean` 468) are **6,008**. The figure matters because it is the
plan's yardstick for S2's size; at 6,008 for a binary statement whose two sides already agree
field by field, a unary statement with a real invariant per field is not obviously smaller.

---

## F. Handoff

**Read, in full:** `AGENTS.md`; `docs/research/2026-09-18-typed-state-plan.md`;
`docs/research/2026-09-16-strict-proof-obligations.md` rows O9, O11, O14 and §D5;
`Test/contracts/machine-scheduler-core.contract.md` (whole file, "Table-aware agreement" at
`:87-136`); `src/Effect4/Laws/Program/Sched.lean` (241 lines, all);
`src/Effect4/Laws/Program/InterpR.lean` (417, all);
`src/Effect4/Laws/Program/DenoteR.lean` (header, `:43-330`, `:576-700`, `:780-1010`, plus the
declaration index of all 1,553); `src/Effect4/Laws/Program/RuntimeR.lean` (309, all);
`src/Effect4/Laws/Program/EvaluateR.lean` (`:43-330`);
`src/Effect4/Laws/Program/MeaningSound.lean` (`:1-60`, `:180-340`, `:440-560`);
`src/Effect4/Laws/Program/LoopSound.lean` (`:1-60`, `:150-360`);
`src/Effect4/Laws/Program/TypedRun.lean` (121, all);
`src/Effect4/Laws/Program/Typing/CheckInversion.lean` (473, all);
`src/Effect4/Laws/Program/Typing/Inversion.lean` (`:1-60` plus the index);
`src/Effect4/Laws/Auto/{Inversion,Census}.lean`; `src/Effect4/Laws/Program/Intro.lean`;
`src/Effect4/Laws/Program/Intro/{Fibers,Weight}.lean`;
`src/Effect4/Laws/Program/Simulation/Fibers.lean` (`:1-120`);
`src/Effect4/Laws/Machine/Book.lean` (`:175-260`, `:620-650`, `:950-1010`);
`src/Effect4/Laws/Machine/Behaviour.lean` (102, all);
`src/Effect4/Program/Checker.lean` (`:190-360`); `src/Effect4/Program/Typed.lean` (`:20-70`);
`src/Effect4/Program/CheckedTyping.lean`; `src/Effect4/Machine/Fibers.lean`
(`:71-160`, `:215-280`, `:395-420`, `:687-710`, `:1795-2160`);
`src/Effect4/Program/Compile.lean` (`:57-130`, `:971-1050`);
`src/Effect4/Program/Eff.lean` (`:390-440`); `docs/DESIGN-ISSUES.md` rows DI-17, DI-39, DI-57.

**Ran** (every command from `/Users/pooks/Dev/lean4-effect4`, one `lake` at a time, no
`make check`, no root build):

| file | command | result |
| --- | --- | --- |
| `P3_signatures.lean` | `lake env lean …` | compiled, 27 `#check`s printed |
| `P2_denoteR_reduce.lean` | `lake env lean …` | compiled clean after removing one redundant `rfl` |
| `P2b_denoteR_unfold.lean` | `lake env lean …` | two deliberate failures, residual goals quoted in §B.2 |
| `P1_typedprog.lean` | `lake env lean …` | first run: kernel nested-inductive error; after the fix, compiled, `[propext]` twice |
| `P5_s1_arms.lean` | `lake env lean …` | first run: two errors (§B.4); after the fixes, four theorems at `[propext, Quot.sound]` |
| `P6_bind.lean` | `lake env lean …` | `TypedProg.bind` `[propext]`; `widen` `[propext, Quot.sound]`; `monoΓ` failed (variance) |
| `P7_variance.lean` | `lake env lean …` | three theorems at `[propext]` |
| `P8_guard.lean` | `lake env lean …` | `exitOk_of_noFail` `[propext, Quot.sound]` |
| `P9_evaluateR_move.lean` | `lake env lean …` | six equations compiled against `EvaluateR` alone |
| `P4_census_loopsound.lean` | `timeout 900 lake env lean …` | `1 of 19` |
| `P4b_census_meaningsound.lean` | `timeout 1200 lake env lean …` | `0 of 37` |
| `P4c_census_checkinv.lean` | `timeout 1500 lake env lean …` | `65 of 68` |
| `P10_aesop.lean` | `timeout 600 lake env lean …` | three failures then three theorems at `[propext, Quot.sound]` |

Closure figures in §D come from a Python walk of the `import` lines under `src/`, not from a
build.

**Compiled:** every scratch file above, in its final state. **Did not compile:** the extracted
`PointWeight.lean` of move 2 and the `StoresOk` extraction of move 3 (both **assumed** from
reading, marked in §D.3); the generic `Laws/Machine/Keeps.lean` ladder (**assumed**, its shape
read off `book_driveState`).

**Open questions for the coordinator.**

1. **E.3 is a decision, not a detail.** `HandlesFit` adds a field to the run invariant and
   changes every S1 statement. The alternative is to make `Val.hasTy` at `.fiberOf` consult an
   allocation-like table, which would change the core checker and contradict DI-17's
   "keep fiberOf explicitly coarse". My recommendation: add `HandlesFit` beside `TypedAt`, do
   not touch `Val.hasTy`. Owner-level, because it widens the invariant the whole milestone is
   about.
2. **Shape A or shape B** for `TypedProg`. I recommend B (three clauses plus a 40-arm `AnswerOk`
   definition): it compiles, inverts cleanly, and keeps the 40 arms as one readable `def`. A is
   closer to `CodeMeans` and the tree's habit. Coordinator's call.
3. **Move 1 (the six `evaluateR_*` equations) should be done first, on its own.** It has no
   consumers, it is two files, and without it S2 imports the Simulation tree. It could land
   before any of S0.
4. **Does `Laws/Machine/Keeps.lean` belong to this milestone or before it?** It is generic, it
   subsumes `MachineOk`, and it is the only way S2 gets a ladder. It could be lifted out as its
   own small slice.
5. **S1 over `check … p.path e = .ok t` or over `effTy`?** I recommend `check`: all 68
   inversions exist at that level and 65 of 68 close by `aesop` today, while `effTy` has only 13
   lifts and would need 12 more.

**Estimate, honest.**

| piece | new lemmas | new lines | confidence |
| --- | --- | --- | --- |
| S0 §2 (`Later`, `AnswerOk` 40 arms, `TypedProg`, `HandlesFit`, `TypedFiber`, `TypedState`) | 6 definitions + 8 structural lemmas (`bind`, `widen`, `monoΓ`, `later`, `guardR`, `constructR`, `prepareR`, `wf`) | 450 to 600 | high; three of the eight are reproduced and stamped |
| S1 `denoteR_typed` | 25 program arms + 10 layer arms + 3 resolved-point companions + 18 `actionAt` shape lemmas + 5 `hasTy_*_inv` + `exitOk_of_noFail` | 1,400 to 2,200 | medium; four arms reproduced at 5 to 14 lines each, but `provideLayer`, `acquireRelease` and the join arms are the long ones and I did not attempt them |
| `Laws/Machine/Keeps.lean` | 4 | 150 to 250 | medium; the shape is `book_driveState`'s with one machine deleted |
| S2 `typedState_step` | 40 (`evaluateFiberR`) + 18 (`driveStep`) + 8 (`popR`, `deliverR`, the two prepare passes) + 4 ladder instantiations | 3,000 to 5,000 | low; this is the part the plan calls "the substance", and I did not reproduce a single arm of it. The `Simulation/*` tree spends 6,008 lines on the same case split for a *binary* statement with the two sides' bookkeeping already equal; a unary statement with a real invariant per field is not obviously cheaper |
| S3 the transfer + corollaries | 4 | 150 to 250 | high; `BMeans.exitOf` is already per fiber and `obs` is already every fiber |
| battery `Test/Program/TypedStateContract.lean` | n/a | 150 to 300 | high |
| **total** | **~150 lemmas** | **5,300 to 8,600 lines** | |

The plan's "S0 and S3 are days" matches. "S1's store arms are mechanical" matches, for about
half the arms. "S2 is the substance and the part that cannot be shortened" matches, and my
estimate is that it is between three and five thousand lines, which is the same order as
`Simulation/*` and should be planned as a wave of its own, split by operation family across
files from the start.
