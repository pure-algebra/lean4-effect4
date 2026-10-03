# Slices two and three: the term scheduler and the simulation invariant

## Current routing after the 2026-09-06 audit

Implementation is paused. Read [the revised synthesis](2026-09-06-wave2-synthesis.md)
for the current order and the [wave-2 audit](2026-09-06-wave2-audit.md) and
[checkpoint audit](2026-09-06-p0-checkpoint-audit.md) for checked evidence.
Eff/NativeEff remain the IR for arbitrary admitted Effect TS programs, with
the established closure limit; the pinned TypeScript source is semantic ground truth.

The original decisions and signatures below are historical worksheets.
In particular, D8's command stutter plus extra fuel is refuted by automatic
yielding; BookMeans cannot retain unconditional counter equality as written.
Introduction needs a source-address premise. Probe removal of the extra
unfolding budget with runtime loops/generators before building an adequacy
framework; the other frontiers and residual-state obligations remain.
R5 becomes a later corollary with its fixed-budget premise still owed.
Keep the false cleanup delimiter. Use Option.Rel and List.foldl_rel; extract
ordinary shared actions with the existing core. Acquisition must register
release on the ambient scope. The submitted checkpoint candidate's blanket
marker folding and single tick are rejected. P0 first checks the source/reference
contract and a phase prototype; P1a reference corrections, P1b extraction and
P2 term changes are serialized. Existing frame counts are not automatically
the host contract: exit/gen/loop and automatic-yield/resume discrepancies are
recorded in the new audit. Implementation remains paused.

## Historical worksheets and scouting

Companion to `2026-09-05-first-slice-worksheets.md`. The deep per-node strategy is in
`2026-09-05-tactics-cheatsheet-dag-strategy.md` §3 (REF/*) and §4 (SIM/*); this page adds
what the coordinator's late probes settled, the decisions to fix before typing, and the
arm map the largest definition needs. Read the strategy sections first; they carry the
statements.

R2 correction, authorized and implemented 2026-09-06: the current statement is in
`Test/contracts/program-denote-r.contract.md`, with the checked findings and receipts in
`2026-09-06-w3-r2-continuation.md`. Its two budgets are separate; frontiers retain residual
control instead of becoming failed exits; straight agreement requires both budgets to
cover `Agreement.depth`. The source classifier and straight restriction are proved at
`[propext, Quot.sound]`.

R3/R4 update, 2026-09-06: both are implemented in `Program/InterpR.lean`,
`EvaluateR.lean` and `RuntimeR.lean`; acceptance record
`2026-09-06-r3-r4-implementation.md`, contract
`Test/contracts/program-runtime-r.contract.md`. The owner authorized one further
R2 correction after a checked cleanup/sequence collision: raw terms now retain
control boundaries, and straight agreement is after `eraseControl`. `Body` has
the three scouted constructors. The saved stack also retains resumptions and
cleanup delimiters. The addressed `.body` interpreter hook is implemented, and
the store delivery keeps the shared `answered`/`deliver` split. The reference's
discarded terminal mask differs in eight checked runs; live masks and the fixed
exits/stores observation agree. R5 and the general simulation remain owed.

## Settled since the strategy note

* **The `onExit` inversion goes through** (`scratchpad/dag/p12_onexit_inversion.lean`, at
  `[propext, Quot.sound]`): with `CodeMeans` as the relation of finding F1, the local step
  that sets `current := onSuccessAndFailure p (restore ex) (merge ex)` on a finalizer
  program `p` meaning `fm` yields exactly the reference term
  `bind fm (fun fex => pure (restoreAfterFinalizer ex (finVoid fex)))`. Two ingredients:
  `contAOf_restore`/`contEOf_merge` (`Agreement.lean`) and one `funext fex; cases fex <;>
  rfl` to align the two continuation spellings. So the crux's hardest inversion is a
  twenty-line lemma; the `sync` case of `means_step` is the only SIM/local case left
  unprobed.
* **`Effects.Algebra.Sum`, `Universal`, `Handler.Category`, `Handler.Composition` build
  cleanly** in this tree (10 jobs). REF/sig can import `Sum` and AGR/congruence can import
  `Universal`; the OPEN item is closed and `interpret_inl` need not be reproved inline.
* **The `withFiber` arm map** (`Fibers.lean`, line numbers after the first slice landed
  on 2026-09-06; every earlier citation into `Fibers.lean` in these notes moved by about
  seventy lines), the spine of `evaluateR` and the check on `FiberOp`: `fork` 976,
  `forkIn` 983, `forkScoped` 991, `runIn` 1003, `interrupt` 1007, `interruptScoped` 1009,
  `interruptAll` 1012, `awaitAll` 1018, `awaitAllFailFast` 1021, `snapshotChildren` 1024,
  `awaitNewChildren` 1026, `raceAll` 1030, `setInterruptible false` 1048, `setInterruptible
  true` 1051, `setContext` 1055, `getContext` 1060, `getId` 1062, `closeScope` 1064,
  `refuse` 1070, `dropObservers` 1073, `cancelRace` 1081. Four of these are missing from
  the strategy note's `FiberOp`: `interruptScoped`, `refuse cause` (the S3 refusal defect),
  `dropObservers token` (R2-3) and `cancelRace raceId`. Add them; `refuse` denotes to
  `pure (Exit.failure (die …))` and is a refusal row, not a feature. New anchors: `Task`
  102, `class FiberCore` 156, `RunMachine` 373, `Cmd` 580, `injectYield` 826,
  `evaluatePrim` 844, `iteration` 1124, `exitFiber` 1201, `drive` 1331,
  `stepDecisionState` 1397, `stepDecision` 1424, `replayEval` 1463.
* **D1 as it landed is not the interface sketch of the reuse review.** The first slice
  (`2026-09-06-first-slice-implementation.md`, "D1 working design") parameterises the
  records by three types with the frame instance as defaults — `κ` the code (`Prim`),
  `φ` the saved frame state (`FrameFiber`), `η` the frame event — with `class FiberCore`
  supplying the pure reads and writes of saved state, small code fragments and start,
  and the evaluator passed separately to the shared loop (no recursive interpreter
  record). `RunInterp … St κ` carries the code type; the tape carries `Completion`, not
  code (D6). So the term scheduler instantiates `κ := Program RSig ExitV`, `φ := RFiber`'s
  saved state, supplies its `FiberCore` instance and its `evaluateR`, and reuses
  `drive`/`stepDecision`/`replayEval` and their generic laws as they are. `eraseCode`
  (decision 4 below) becomes the `φ`-erasure, and the generic trace laws are conditional
  on a command-step premise (`CORE-FB-TRACE`), which `evaluateR` must discharge as the
  frame evaluator does.

## Decisions to fix before slice two starts

1. **`Sim` over a pairwise list relation**, not indices (strategy §4, recommended there):
   every `sim_*` lemma then destructs one `cons` instead of carrying two bounds. Amended
   2026-09-06: `List.Forall₂` does not exist on this toolchain (no Batteries, no Mathlib);
   write a six-line `ListRel` inductive with a single universe (wave-2 book lane, `p01`).
2. **`sim_fire` as its own lemma**, cut out of `sim_stepDecision`, because `flush` is a
   fold of `fire` and the two cases would otherwise be mutually recursive (strategy §4,
   `sim_stepDecision`, OPEN). State it on `fireState` with the per-decision receipt.
3. **Three clause lemmas owed in `Clauses.lean`** before `sim_context`: `withFiber_setContext`,
   `withFiber_getContext`, `withFiber_getId` (the table's last row says they are absent).
   Coordinator surface; batch them with the D1 gate.
4. **`eraseCode`** — amended 2026-09-06: not needed. Thirteen of `RunFiber`'s fifteen
   fields and seven of `RunMachine`'s ten are code-free and compare by equality; the rest
   are pairwise relations with the code relation (wave-2 book lane, `p01`, `p04`). Relations
   all the way, as finding F1 says; no functorial maps.
5. **Fuel in `denoteR` is a leading structural argument**, never `p.fuel` (strategy §3:
   the well-founded version compiles but its arms do not reduce). The compile's
   `Point.fuel` is separate from this unfolding budget: choice does not consume compile
   fuel, and loops reuse their saved point. Arm equations require positive compile fuel;
   the straight restriction requires depth bounds on both budgets. `p.fuel = n` is a
   permitted specialization, not the general contract.
6. **`.vis`, not `.perform`**: `Effects.Program` has `pure` and `vis`; write every meaning
   as `.vis (.inl op) k`.

## Slice two, in order (Layer R; strategy §3 has each statement)

R1 landed 2026-09-06: `src/Effect4/Program/Sched.lean` (`FiberOp` with the four added
constructors, `FiberSig`, `RSig`, `RProgram`, `rHandler`, `interpret_inl_store`,
`meaning_via_rsig`), battery `Test/Program/SchedContract.lean`, report, packet
`Test/contracts/program-sched.contract.md`, row `E4-SCHED-CE-001`; committed as `c080063`
(gate 268 jobs, 262 modules / 35,224 declarations). R2 starts from `meaning_via_rsig`.

### R2 scouted (2026-09-06): what `denoteR` has to say, arm by arm

`compileEff` (`Compile.lean:280–356`) at fuel `0` is `frontier p`. The corrected `denoteR`
keeps compile-fuel and unfolding-fuel exhaustion as visible frontier operations, with the
residual address. The table below is the original scouting map; its `pure outsideExit`
frontier cells are superseded by the corrected packet, as are its open generator estimate
and the scope operation that omitted the allocated id.

| `Eff` arm | compile emits | `denoteR` (fuel structural, `p` the point) |
| --- | --- | --- |
| `succeed`, `fail`, `failCause`, `yieldError`, `sync`, `suspend`, `perform` (sync row), `bind`, `branch`, `exit`, `catchCause`, `matchCause`, `onExit` | as `Denote.lean:88–147` | `Program.inl` of the `denote` arm, with `p.env` for `env` and `p.child i`/`p.childWith i v` where `denote` recurses at `env`/`env ++ [v]` (`bind`: `childWith 1 v`; `catchCause`: `childWith 1 (exitErr c)`; `matchCause`: `childWith 1 x`/`childWith 2 (exitErr cause)`; `onExit`: `childWith 1 (reifyExitVal ex)`; `suspend`/`branch`: `child 0`) |
| `perform` (async row), `callback` | `Prim.async (registerAwait cell) true (some (cancelAwait cell))` | `vis (.inr (async (registerAwait cell) request)) k`; `badShape` when the request does not evaluate or decode |
| `perform` (program row), `acquireRelease` | `frontier p` | `pure outsideExit` (the compile refuses them; so does the denotation, one row each) |
| `gen body` | `Prim.iterator (gen p [] false) unit` stepped by `iterNext` | **open sub-design**: a denotation of `Stmts` with the program counter (`bindYield`, `yieldDiscard`, `ret`, `ifElse`, `whileTrue`, `breakLoop`), fuel-unrolled on `whileTrue`; mirror `iterNext`'s arms one for one |
| `whileLoop initial test step body` | `Prim.whileLoop (loop p) cursor` through `loopTest`/`loopBody`/`loopStep`/`loopDone` | fuel-unrolled: test the cursor, run the body at `childWith`, step, recurse at `fuel` |
| `yieldNow priority` | `Prim.yieldNowWith priority` | `vis (.inr (yieldNow priority)) (fun _ => pure (success unit))` |
| `awaitFiber fiber mode` | `Prim.suspend (park (join id mode))` when `fiber` evaluates to `Val.fiber id` | `vis (.inr (await id mode)) k`, `badShape` otherwise |
| `uninterruptible`, `interruptible`, `withFiber action` | `Prim.withFiber (EffThunk.act p)`, decided at run time by `withFiberOf` through `actionAt root p` | `vis (.inr fop) k` with `fop` the `FiberOp` image of `actionAt root p`; the mapping `WithFiberAction → FiberOp` is the arm map of this note |
| `scoped body` | `onSuccess (sync (scopeMake sequential)) (scopeOpen p)`, then `scopeProvide`/`scopeBody` | `vis (.inl (scopeMake sequential)) (fun s => vis (.inr (scoped (p.child …))) …)`: the store makes the scope, the fiber op runs the body under it and closes it |
| `choose site left right` | by `p.tape` | the same: `true :: rest` → left at the path-extended point, `false :: rest` → right, `[]` → `pure outsideExit` |

**Two findings that change R1 before R2 is written.**

1. **Answers are not all `Val` in the direct interface.** The machine resumes a join with `exitValue exit mode`,
   which is a value for `awaitValue` and an *exit* (`Prim.ofExit`) for `joinEffect`; a mask,
   a scope, an `acquireRelease` and a race hand their continuation the body's or the
   winner's *exit*. The original scout claimed the existing exit encoding was not
   injective; that claim was false. `SchedContract.exit_encoding_roundtrip` proves it is
   reversible, and `exit_encoding_distinguishes` disproves the proposed collision.
   The owner retained a dependent answer as the direct interface: `FiberOp.answer : FiberOp →
   Type`, `ExitV` for `mask`, `scoped`, `acquireRelease`, `raceAll` and `await _ .joinEffect`,
   also `ExitV` for async, scoped forks, scope close and frontiers; `Val` otherwise.
   The scope id, `forkIn` link key, `closeScope` arm and residual frontier addresses are
   now explicit. This changes `RSig_answer_inr`, the battery's `example`, `fiberRefusal`
   (which then needs a default answer per operation) and packet claim 2 of
   `program-sched.contract.md`. Small; do it as R2's first edit.
2. **`withFiber` is decided at run time.** The compile emits one `Prim.withFiber
   (EffThunk.act p)` for `uninterruptible`, `interruptible` and every `withFiber action`,
   and the interp's `withFiberOf` reads the action at the point. `denoteR` must therefore
   evaluate `actionAt root p` itself to choose the `FiberOp`, which is why `denoteR` takes
   `root`, and why the correspondence lemma for this arm is stated through `actionAt`
   rather than through the constructor.

The generator sub-design is implemented in `Program/DenoteR.lean`: `denoteGen`,
`denoteYield` and `inlineYield` retain scan reset, block-local environments and the advanced
program counter. `inlineYield_eq_headExit` is a universal proof against the compiler's
immediate exit projection; generator execution comparisons are finite probes.

| step | what | size | note |
| --- | --- | --- | --- |
| R1 | `FiberOp` (with the three missing constructors), `FiberSig`, `RSig` pinned `.{0, 0}`, the store lift by `Handler.sum` | 110 | probed whole (`dag/p4b`) |
| R2 | `denoteR root : Nat → NativeEff → Point → Program RSig ExitV`, one arm per `compileEff` arm (`Compile.lean:280–356`) and per `Stmt`; `denoteR_straight` | 350 | shape probed (`dag/p11`); the twenty fiber arms are new |
| R3 | `ScopeFrame`, `RFiber`, `RState`; `obsR`; `loadR` with `choices`; and, scouted 2026-09-06 (section below): the `Body` amendment, the D4 store-program denotations, `interpR` | 120 → ~450 | `RunFiber`'s fields with `code` for `frame`, no trace; the state is zero code (probed), the interpreter and the D4 denotations are the lane |
| R4 | `evaluateR`: on `pure ex` the exit path, on `vis (.inl op) k` the store step, on `vis (.inr fop) k` the arm of the map above, each mirroring its `evaluatePrim` line and using the same `interpOf` hooks | 320 | under D1 the loop, decisions, `fire`, `flushAll`, `replayEval` are shared; without D1 add 250 lines of skeleton |
| R5 | `replayR_straight` (REF/base): one straight-line fiber is `meaning`, through `denoteR_straight`, `interpret_inl`, and `meaning_via_rsig` (`dag/p4b`) | 120 | the check that R1–R4 are right |

### R3 scouted (2026-09-06, after R2 landed): what the term scheduler's state consists of

Historical scout: the implementation addendum above supersedes its two-slot
saved stack, all-evaluator-hooks-as-stubs suggestion, and claim that `progOf`
has only six atomic cases. The required synthesized shapes have direct terms;
arbitrary stored primitive programs are outside the Completion profile.

Probe `scratchpad/dag/p13_r3_state.lean` (copy in `docs/research/probes/`), at the real
alphabets, passes at `[propext]`: `RSaved` (the frame's five fields with a term for the
code and a `ScopeFrame` list for the stack), its `FiberCore` instance mirroring `frameCore`
(`Fibers.lean:182`) field for field, `RState := RunMachine … RProgram RSaved Unit`,
`RFiber`, `RInterp`, `loadR` as `Api.load` with `denoteR e fuel e (rootPoint fuel choices)`
where `Api.load` has `compile`, `obsR := obs` unchanged, and `replayEval`/`Suffices` at the
term instance once any `FiberEvaluator` instance exists (a stub in the probe; the real one
is R4's `evaluateR`). `Beh` (`Behaviour.lean:73`) is generic too. So REF/state is the zero
the strategy note promised, and `loadR`/`obsR`/`replayR`/`SufficientR`/`BehR` are thirty
lines. R3's real content is elsewhere, in three places the note did not weigh.

**1. What the loop itself asks of the interpreter, measured.** Outside `evaluatePrim`
(`Fibers.lean:844–1103`) the shared loop consults seventeen `RunInterp` fields:
`encodeFiber`, `stackAnnotations`, `cancelName`, `parkCancelName`, `exitsValue`,
`voidValue`, `budgetOf`, `scopeStatus`, `scopeLinkFiber`, `exitValue`, `dropFinalizer`,
`raceSettle`, `restoreName`, `emptyContext`, `dueResumes`, `answerCode`, `asyncFiberError`.
Only four are code-valued, and they are R3's `interpR`: `exitValue exit mode` (the term
`.pure exit` for `joinEffect`, `.pure (.success (reifyExitVal exit))` for `awaitValue`),
`answerCode` (the term of `completionPrim`: `.pure exit`, or `vis (.inl (refGet cell))`),
`dueResumes` (the same two shapes: `DeferredStore.complete` pushes the completing program
itself onto `due`, `Stores.lean:727`), and `raceSettle live exit` (the term of
`raceSettleProgram`, `Stores.lean:1117`, see 3). Every other loop-consulted field is a
name, a value, a context read or a store query and is copied from `interpOf`/`stores`
verbatim. The code-valued fields only the evaluator reads (`contA`, `contE`,
`suspendBody`, `iterNext`, `loopBody`, `cancelThenFail`, `finalizerProgram`, `closeScope`,
`registerAsync`'s immediate resume, `parkOf`, `withFiberOf`, `syncState`) are R4's: the
term evaluator reads terms, not names, so `interpR` carries them as refusal stubs named in
the header (`RSTATE-FB-EVALUATOR-FIELD`), or as direct term images where one exists
(`finalizerProgram`: `.fin p` is `denoteR` at `p.childWith 1 (reifyExitVal exit)`,
`.scopeClose scope` is `vis (.inr (.closeScope scope exit))`, `.restoreCtx prev` is
`vis (.inr (.setContext prev))`, `.store (finalizerName fin)` is `denoteFin fin exit`).

**2. The one place the loop composes code with a name.** `FiberCore.onSuccess` is called
once, `Fibers.lean:704`, on `Resume.continueWith name`, and the only producer of
`continueWith` is `exitFiber` (`:1213`) with `interp.restoreName exit`. So the term core's
`onSuccess code name` must read exactly `EffName.restore exit` (as `contAOf` does,
`Compile.lean:555`: success continues with `.pure exit`, failure passes through) and may
refuse every other name by identity, named in the header (`RSTATE-FB-ONSUCCESS-NAME`).
`pushAsyncFinalizer` (`:694`) pushes `ScopeFrame.asyncFinalizer name`; the interrupt path
that runs it is inside the evaluator (R4, through `cancelThenFail`, whose term image is
`bind (denoteCancel name) (fun _ => .pure (.failure cause))` with `denoteCancel` over
`cancelProgramOf`'s four shapes, `Compile.lean:585`: a store op, `dropObservers token`,
`cancelRace race`, and success).

**3. The synthesized programs need bodies the signature cannot address (D4, met here).**
Two of the store's own programs enclose a program that has no address in the root:
`raceSettleProgram` masks `ProgName.interruptFibers live` under `setInterruptible … false`,
and `closeParChain` (`Stores.lean:1151`) forks `ProgName.finalizerOf fin exit` as an
immediate daemon. `FiberOp.mask flag (body : Point)` and `fork (child : Point) options`
cannot name either. Amend R1 once more, before R3 is typed: a first-order

```lean
inductive Body
  | at_ (p : Point)                          -- a subterm of the root
  | fin (fin : FinName) (exit : ExitV)       -- a store finalizer (finProgram)
  | interruptFibers (live : List FiberId)    -- the race settle's masked body
```

and `mask flag (body : Body)`, `fork (child : Body) options` (`forkIn`, `forkScoped`,
`raceAll` keep `Point`), with `denoteBody root n : Body → RProgram` (`denoteR` at the
point; `denoteFin`; `vis (.inr (.interruptAll live none))`). The alternative, two atomic
operations `settleRace live exit` and `forkFinalizer fin exit options`, is smaller but
gives S1's `CodeMeans` two more shapes to invert; `Body` keeps one shape per `Prim`
constructor. The store's other synthesized programs are direct: `denoteFin` over the seven
`FinName` shapes (`Stores.lean:1041`: two interrupt ops, `closeScope`, a `scopeRemove`
store op, a pure exit, an external-register async, `awaitNewChildren`), `progOf` (this
scout said six atomic shapes; it has 24 constructors, several compound, and the landed
R3 covers the ones this source profile synthesizes, `RSTATE-FB-STORE-CODE`), `closeSeqChain` (structural on the finalizer list, ending in
`.pure (voidAllOf captured)`; read the stores' `contAOf`/`contEOf` for `Name.closeSeq`
before writing its failure accounting), `closeParChain` (structural on the list, ending in
`awaitAll forked` then `mergeAwaitedExits`, a pure merge of the exits value). None needs a
general `Stores.Program → RProgram` translation, which would recurse through named
continuations and is not structural; write them per shape, which is what D4 said.

**Sizes, corrected.** The R1 amendment 25 lines; `ScopeFrame`/`RSaved`/`termCore` 60;
the D4 denotations (`denoteFin`, `denoteCloseSeq`, `denoteClosePar`, `denoteCompletion`,
`denoteRaceSettle`, `denoteCancel`, `denoteBody`) 120; `interpR` 130 (mostly `interpOf`'s
fields carried over); `loadR`/`obsR`/`replayR`/`SufficientR`/`BehR` 30; a structural
battery (the loaded root holds the denotation by `rfl`, `interpR`'s four code fields and
each D4 shape on examples) 80. About 450 lines, not the table's 120; R4's 320 stands.
R3's battery cannot run a program until R4 exists, so R3 and R4 are one seat in sequence,
or R3 is the coordinator's and R4 the seat's.

**Hazards.** `RSaved` has no `DecidableEq` (a term inside); the loop's derived instances
are conditional, so nothing breaks (the D1 fixture is the proof), and the three separation
gates stay pinned to the frame instance (a refusal row, as REF/state said). The evaluator
class fixes `η` as an out-parameter, so `RState`'s event type is chosen by `evaluateR`'s
instance; take `Unit` (the trace is not observed, D3). The unfolding budget in `loadR` is
the compile fuel, so `replayR_straight` carries `depth e ≤ fuel` once, plus the machine's
step bound. `closeParChain`'s fork options `⟨true, true, mode⟩` are data and carry over.

### Readiness for slice three (2026-09-06, after R3/R4 landed and were verified)

**Superseded in part by the wave-2 synthesis, `2026-09-06-wave2-synthesis.md`, which is
now the entry point for R5 and slice three.** Four scouting notes (27 probe files, all
within the ceiling) corrected this section where it conflicts: R5 keeps the frame
theorem's fuel hypotheses (the claim below that it does not is wrong); the sync answering
step is lockstep but its delivery is not, and the pure `sync` costs the term nothing; the
simulation stutters in both directions with cost 0, 1 or 2 per machine step; `Minted` is
not a clause of `Sim`; decisions 1 and 4 above are amended (`ListRel` inductive, no
`eraseCode` maps); the generator's bind flag is not readable off the counter and need not
be; the unfolding budget has no closed measure outside the straight fragment. The text
below is kept as the record.

R3/R4 as landed (`Program/InterpR.lean`, `EvaluateR.lean`, `RuntimeR.lean`; record
`2026-09-06-r3-r4-implementation.md`; the coordinator's own gate re-run: 282 jobs, 276
modules / 38,771 declarations, ceiling `[propext, Quot.sound]`, boundary 7 modules / 41
declarations unchanged; every new receipt within the ceiling; 227 guards across the five
Sched/DenoteR/RuntimeR batteries, 32 of them complete frame-versus-term comparisons on
identical decision tapes). Three corrections to the scouts above are on the record and
were right: the saved stack carries answer continuations (`ScopeFrame.resume kind next`),
not two constructors; `Stores.progOf` has 24 constructors, not six, and the direct shapes
cover the ones this source profile synthesizes (`RSTATE-FB-STORE-CODE` for the rest); and
the term evaluator keeps the machine's `answered`/`deliver` split, so the strategy note's
`c = 2` argument for `sim_sync` is retired.

**The plan-changing finding: control boundaries are visible operations.** The probe
`probes/p14_r3_cleanup_collision.lean` showed `onExit(yield, cleanup)` and
`bind(yield, cleanup)` had definitionally equal denotations while the machine runs the
cleanup only for the first under interruption. A plain `bind` cannot say "run this on any
exit", which is the scoped-effects point of the core-math note (§ scoped effects, Piróg
et al.): handlers and finalizers are scopes, not continuations. So `denoteR` now brackets
every `bind`/`catchCause`/`matchCause`/`onExit` body with `guard_ kind` … `unguard ex`
(and `finishFinalizer` after a finalizer), `eraseControl` removes exactly those markers,
and `denoteR_straight` is stated after erasure. The store meaning is unchanged; the raw
term is what the scheduler needs. Record this in the graph note as C17 when it is next
revised.

**What slice three inherits, and what it must re-cut before S1 is typed.**

1. `CodeMeans`/`FrameMeans` relate frame stacks to marker structure: `Prim.onSuccess body
   n` ↔ `guardR .onSuccess` with a `ScopeFrame.resume .onSuccess k` slot once entered;
   `onFailure`/`onSuccessAndFailure`/`onExit body f flag` likewise; `setInterruptible`
   frames ↔ `restoreMask`/`finalizerMask`; `asyncFinalizer name` ↔ the same. The `onExit`
   inversion probed in `dag/p12` was against the erased shape; re-probe it against
   `onExitR` (`DenoteR.lean:52`) and `popR` (`EvaluateR.lean:42`), which walks slots in
   `getCont`'s order. That probe is the first thing S1 does.
2. Local steps are no longer one-to-one: entering a boundary is one term step
   (`guard_` saves the slot) where the frame pushes in the same step it sets `current`,
   and leaving is `unguard` then the pop. Keep the `∃ c` accounting per local step and
   make the cost a function of the marker structure (the strategy note's AGR/fuelFor
   already wants `cost : Decision → RState → Nat`); `sim_sync` itself is lockstep.
3. Exited fibers are related by exit and bookkeeping only, never by the saved mask
   (`E4-RTERM-CE-005`: `finishFrame`, `Fibers.lean:963`, returns the incoming fiber and
   discards the final pop's mask; the term keeps it). `RuntimeRContract.FiberControl`
   with `frameControl`/`termControl` (`Test/Program/RuntimeRContract.lean:33`) is exactly
   this projection and should be lifted into `Sim`'s bookkeeping clause rather than
   rewritten; it also settles decision 4 for fibers. Dispatcher tasks still carry code, so
   the bookkeeping clause for `Dispatcher`/`Bucket`/`Task` is a `Forall₂` with `CodeMeans`
   on the task's code (F1: relations, not erasure maps).
4. The frontier case (item 4 of "Where the next probes should go") stands; the
   unfolding-fuel frontier has no machine counterpart, so `Sim` is stated at a sufficient
   unfolding budget with `loadR`'s budget equal to the compile fuel.
5. Still owed before `sim_context`: the three clause lemmas (`withFiber_setContext`,
   `withFiber_getContext`, `withFiber_getId`). Still unprobed: the `sync` disjunct of
   `means_step`, now simpler since both sides take `answered` then `deliver`.

**R5 first, and its statement changes.** `replayR_straight` needs one new lemma before the
induction: markers are transparent on an uninterrupted straight run (a `resume .onSuccess`
slot popped by a success is `next ex`; `popR` never sees an interruption there), so that
`denoteR_straight`'s erased equality lifts to the run. Its fuel bound is not the frame
theorem's `2 * steps e + 6`: each `bind` costs two more local steps. State it with an
explicit measure `stepsR e` rather than a guessed constant, as `Agreement.steps` did.
Size: the strategy note's 180 lines plus about 60 for transparency and the measure.

**Decision for the owner, none blocking.** Whether the R3/R4 unit is committed before R5
starts (recommended: it is verified and self-contained), and whether `Sim` is stated over
the raw term (recommended, since interruption is the point of slice three) with the
erased term appearing only in R5.

## Slice three, in order (Layer S, the crux; strategy §4)

| step | what | size | note |
| --- | --- | --- | --- |
| S1 | `CodeMeans` (seventeen `Prim` constructors, ten with meaning arms), `FrameMeans`, `Means`, `scopesOf`, `Sim` over `Forall₂`; the introduction lemma "the compile of a plain program has a meaning" from `plainCode_compileEff`, `plain_at`, `plainCode_resolve`, `plainCode_contAOf`/`contEOf` | 470 | two crux steps probed (`dag/p5c`), the `onExit` inversion probed (`dag/p12`) |
| S2 | `means_step` (SIM/local): the twenty-four `step_*` cases of `Agreement.lean` and the three `exitFrom` shapes, consumed by the invariant; `evaluatePrim_localStep` generalised from `PlainCode` to `∃ t, CodeMeans root cur t`, with `parkOf_plain` re-proved as "a code with a meaning is not a park" | 280 | the `sync` disjunct is the one unprobed case |
| S3 | `sim_local`, `sim_sync` (drops `Quiet`: due resumes are commands on both sides), `sim_yield`, `sim_exit`, `sim_context`, `sim_fire` | 400 | each mirrors `drive_loop_running`: `have hit`, `rw` the clause, `M_update`, `rfl` on records; under D5' via `driveState_loop_*` |
| S4 | `sim_stepDecision` for the six single-loop decisions and `flush` through `sim_fire`; `run_eq_meaning` recovered as the straight-line corollary of the invariant | 240 | the receipt hypothesis `(stepDecisionState … ).2 = true` is mandatory (`APPROX-FB-REFRESH`) |
| S5 | `sim_fork`, `sim_await` (the two-fiber base; `Minted` from W3 is consumed here) | 300 | the first theorem the tree has ever had about two fibers |

## Hazards specific to these slices (beyond the cheat sheet)

* A constructor premise with `∃` is refused by the kernel in a nested inductive; use an
  implicit function parameter plus a universally quantified premise (`dag/p5c`).
* `RunMachine.update`'s `if g.id = f.id` and `disarm`'s `filter` never reduce on a variable
  id; use the `M_update`-style `rfl` lemmas and the clause projections, never `simp` on
  the definitions.
* `interruptEach` and `fireObserver` are folds; induct with `interruptEach_cons`
  (`Clauses.lean:835`) and `fireObserver_fold_grows` (`Approximation.lean:450`).
* Record equalities on `Api.Machine` by `cases; simp_all` were probed choice-free, but
  `#print axioms` each lane's lemmas anyway.

## Where the next probes should go, if a seat has an hour

1. The `sync` disjunct of `means_step` (`dag/p5c` plus `step_sync_op`, `syncOpStep`).
2. `sim_fire` on `fireState` for a machine with one armed owner and one queued task
   (the `Myield` shape of tonight's `fire_Myield`, restated on `fireState`).
3. One fiber-level arm of `denoteR` against its `compileEff` arm, `fork`, with the child's
   meaning at `p.child 0` (the introduction lemma's first non-straight case).
4. Added after R2 landed (2026-09-06): the frontier correspondence for S1/S2. The machine's
   `Prim.frontier p` must be related to the term `pending compileFuel (.effect p)`, and the
   machine's iterator saved state `gen p pc bind` (`Compile.lean:143`, with the environment
   in the surrounding frame) to `ResumePoint.generator p pc env scanFuel`; check that
   `bind` is recoverable from the statement at `pc` and that the machine's scan budget
   reset at a resumed yield matches `denoteYield`'s. The unfolding-fuel frontier has no
   machine counterpart: `Sim` is stated at a sufficient unfolding budget, the way
   `Approximation`'s laws are stated at sufficient fuel. R4 answers no frontier; it parks
   the fiber exactly where the machine parks on `Prim.frontier` (D5').
