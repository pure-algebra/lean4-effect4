# 2026-10-06 seat LIFT receipt: each live fiber of a run holds the saved mask's chain at its start flag

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-lift-brief.md`, with the dispatch message.
Design note: `docs/research/2026-10-06-seat-LIFT-design.md`. The coordinator sent eight
messages after the dispatch. Each one is named below where it changed the slice.

**The one thing to know before merging:** one sentence of the required property on the main
line is false. `docs/core/semantics.md` reads "The machine holds one table of start flags". The
machine holds none. The table is proof data: it is the world of the lift (`basesOrder`), and a
theorem gives it as a witness. The coordinator's first message says the same: the machine
stores no base, and it must not gain one. Item 9 holds the sentence that replaces it.

The coordinator's seventh message reports that the semantics registry on the main line holds
the claim. I read its text in the coordinator's checkout, and I wrote nothing there. Three
more differences are of substance, or close to it. Item 9 holds a replacement for each.

- **"Each entry that returns a machine holds it with no premise"** is exact in one reading
  only: no premise for the command condition. An entry that starts a run takes no hypothesis.
  An entry that steps a machine takes the invariant at the machine that it starts from.
- **"Each entry"** is each entry outside `Machine/` and `Laws/`, as item 7 measures it.
  `Machine.runCallback` returns a machine and has no statement. The property's citation names
  `src/Effect4/Laws/Api/MaskRuns.lean` alone, and the entries of `src/Effect4/Api.lean` have
  their theorems in `src/Effect4/Laws/Program/MaskRuns.lean`.
- **The bracket owes a second fact.** R11's line names the first: the body's run returns to
  the entry's stack. The second is that the fiber is live at both cuts. `MaskRuns.flag_eq`
  takes both, and no theorem states either at a cut.

Six more facts stand beside these.

- **This hand-back changes no Lean file.** The head of the code is `81a362a8`. The coordinator
  merged it on the main line as `d734aa6a`. The commit after `81a362a8` holds this receipt,
  the design note's addendum and two filed texts.
- **Parts A and B are proved in place.** The stop rule did not apply. No planned goal of the
  slice is open. The goal gate counts 24 planned goals, as at the base.
- **The invariant ranges over the live fibers.** The form over every fiber of the table is
  false at a reached machine (reproduced: a finite probe). The coordinator accepted the range.
- **The lift reaches a run of a compiled program.** `Api.replay` runs the native evaluator. So
  the statements over a command take one premise on the evaluator, and both evaluators meet it.
- **Two law files are outside the brief's list.** The coordinator asked for each:
  `src/Effect4/Laws/Program/MaskRuns.lean` and `src/Effect4/Laws/Api/MaskRuns.lean`.
- **R11 stays open.** The bracket of a region has no statement. Item 8 says what it owes, for
  a reader with no part in this session.

The sections below carry the brief's item numbers. Item 1 is the bold line above.

## 2. Base, head and commits

| Item | Value |
| --- | --- |
| Branch | `seat/lift`, in the worktree `/Users/pooks/Dev/lean4-effect4-mask` |
| Base | `f3568844` |
| Main-line head taken in | `0c4f9774`, by the merge `69839047` |
| The main line | `831a76f3` when I read it last. Since `0c4f9774` it changes `Test/All.lean` and `src/Effect4/Laws.lean`, at other lines. It changes no file under `src/Effect4/Machine`, `src/Effect4/Api` or `src/Effect4/Laws/Machine`, and none of `src/Effect4/Api.lean`, `src/Effect4/Run.lean`, `src/Effect4/Program/Admit.lean` and `src/Effect4/Program/Compile.lean` (tested: `git diff --stat 0c4f9774 refactor/phase1-phase3` over those paths). `git merge-tree --write-tree 81a362a8 refactor/phase1-phase3` reports no conflict (tested). I ran no second merge. The coordinator's eighth message says that `81a362a8` is merged there as `d734aa6a`, and that every gate passed on the merged tree. I ran none of those gates |
| Head of the code | `81a362a8` |
| Head | the commit that holds this receipt |

Nothing is pushed.

| Commit | Step | Content |
| --- | --- | --- |
| `a677c591` | 0 | the design note |
| `53986af3` | 1 | part A, the frames. The coordinator merged it as `3475c065` |
| `ac4fdbf5` | 2 | part B: the invariant, the command condition and the lift, proved in place |
| `b88ff25d` | 3 | the lift at the compiled program's interpreter, in a second module |
| `4fdf38e0` | 4 | the battery's part B, and a compiled program |
| `8791cda4` | 5 | the placed structure holds each statement; `MaskRuns.entry_eq` |
| `69839047` | — | the merge of the main line at `0c4f9774` |
| `a3b0ab09` | 6 | `MaskRuns.flag_eq`: along a run, a live fiber's flag is a function of its stack |
| `81a362a8` | 7 | the invariant at each entry that returns a machine, with a third module |
| the head | — | this receipt, the design note's addendum, the probe and the falsifying script |

The coordinator's eight messages, and what each changed:

| Message | What it changed |
| --- | --- |
| 1 | It accepted the invariant over the live fibers, the third alternative and the table as proof data. It asked for the finding's reach and for the invariant's range in this receipt |
| 2 | It merged part A as `3475c065`. It asked for the default concept and the registry claim's text |
| 3 | It asked for the second module, for the statement at `Api.load`, and for a control at a compiled program |
| 4 | It named `0c4f9774` to merge before the default build. It asked what the run API and `Api.runSync` still owe |
| 5 | It asked that item 8 be written for a reader with no part in this session |
| 6 | It chose to land the run entries as step 7, with four points and a stop rule |
| 7 | It reported the semantics registry and the required property on the main line |
| 8 | It reported the merge `d734aa6a` and its gates |

## 3. Changed files

`git diff --stat f3568844..81a362a8` over the slice's paths lists seven files and 4168 inserted
lines. Three of those lines are the main line's imports in the two root files. The counts of
declarations come from `grep` over the lines that open one.

| Group | File | What changed |
| --- | --- | --- |
| The laws | `src/Effect4/Laws/Machine/MaskRuns.lean` | new: 94 theorems, 12 definitions, 2 instances and the structure `MaskChainRuns` |
| The laws | `src/Effect4/Laws/Program/MaskRuns.lean` | new: 8 theorems |
| The laws | `src/Effect4/Laws/Api/MaskRuns.lean` | new: 19 theorems |
| The laws | `src/Effect4/Laws.lean` | three imports, in order, after `import Effect4.Laws.Machine.MaskDiscipline` |
| The batteries | `Test/Machine/MaskRuns.lean` | new: 61 guards, 22 pinned outputs and 31 proved items |
| The batteries | `Test/All.lean` | one import, after `import Test.Machine.MaskDiscipline` |
| The notes | the design note, this receipt, and two filed texts | `docs/research/2026-10-06-seat-LIFT-probe-exited-fiber.lean.txt` and `docs/research/2026-10-06-seat-LIFT-falsify.py.txt` |

I edited no file under `src/Effect4/Machine/`, no file of another seat and none of the
coordinator's six files. `MaskDiscipline.lean` is unchanged.

**Why the third module is where it is.** The run API's statements read `Effect4.Run`. They
reuse `drive_eq_play` (`src/Effect4/Laws/Run.lean`) and `submit_machine`
(`src/Effect4/Laws/Api/HostSession.lean`). Both are in layer 5 of the role register
(`tools/Tools/ArchitectureRoles.lean`), above `Laws/Program` in layer 3. So the statements are
in `src/Effect4/Laws/Api`, whose area has its row already. The claim's pointer keeps its
smaller imports: `src/Effect4/Laws/Program/MaskRuns.lean` gained no import. A law module may
import the core, so the import of `Effect4.Run` is inside the layering.

## 4. Commands, results and evidence

Each Lean, Lake or `make` command ran through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, named `SLOT` below. Each `make` took the
three flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`. A scratch file is
in the session's scratch folder, which no later session holds.

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build Effect4.Laws.Machine.MaskRuns Effect4.Laws.Program.MaskRuns Effect4.Laws.Api.MaskRuns Effect4.Laws Test.Machine.MaskRuns`, at `81a362a8` | `Build completed successfully (685 jobs).` | tested |
| `SLOT lake build`, at `81a362a8` | `Build completed successfully (1014 jobs).`, with the gate lines below | tested |
| `SLOT lake env lean -M6144 -DwarningAsError=true Test/Machine/MaskRuns.lean` | exit 0, no output | tested |
| the falsified copy of the battery (item 8, the last part) | 113 changed checks, 118 errors, each at a changed check | tested |
| `SLOT make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` | tested |
| `python3 scripts/check-language.py --strict` on this receipt and on the design note | `PASS`, no finding in either | tested |
| `#print axioms`, `#plan_status` and `#semantics_census` in one scratch file | item 5 | tested |

Each step before step 7 had its own narrow build, and its commit message holds the result.

### The gate lines of the default build

| Gate | The base `f3568844` | The head of the code `81a362a8` |
| --- | --- | --- |
| Library roots | 175 API and utility modules, 309 Laws-only modules | 176 and 313 |
| Modules and axioms | 756 modules and 88826 declarations | 764 modules and 89657 declarations |
| Planned goals | 24 goals; 11 declarations rest on goals | 24 goals; 11 declarations rest on goals |
| Proof style | not read at the base | 1911 recorded uses and 52 recorded unread commands in 1161 entries |

Each run of the axiom gate reads: "semantic/test axioms are [propext, Quot.sound]; exact
implementation boundary (17 module(s), 23 declaration(s)) additionally allows
Classical.choice". The goal gate adds: "no other declaration reaches sorryAx". The library-root
gate adds: "every library source is reachable; Effect4 never reaches Laws".

The base's default build gave no gate line, because Lake restored `Test.All` from its cache.
So I ran `Test/All.lean` by itself for the base's lines. The difference between the two
columns holds the main line's merge too, not this slice alone.

### Not run

`make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`,
`make check-truth`, the conservativity script and `make gen-semantics`, as the brief lists.
Also not run: `make check`, `make check-full`, `make check-semantics`, `make check-cases` and
`make gen-architecture`. The slice adds no match on a family of the case policy
(`tools/Conform/Effect4/cases-policy.json`): its matches read `Cmd`, `Prim`, `ReplayResult` and
a sum. No TypeScript compiler and no host ran.

### What is proved, what is tested, and what is only read

- **Proved:** each theorem of the three modules, at every interpreter, tape, fuel and budget
  that its statement names.
- **Tested:** each guard of the battery, on its finite inputs. A guard over a compiled program
  reads one tape at each command budget below a bound.
- **Reproduced:** the reached machine whose exited fiber breaks the chain, by one finite probe.
- **Assumed, by reading only:** no compiled program reaches that machine (item 7). No consumer
  reads a fiber after its exit (item 7). The measure of the entries misses none (item 7).
- **Assumed, on the coordinator's report:** the gates of the merged tree. The eighth message
  lists the default build with 1018 jobs. It lists 768 modules and 90105 declarations at
  `[propext, Quot.sound]`, and 24 planned goals. It lists `check-semantics`, `check-truth` and
  the conservativity script too.
- **Not consulted:** the vendored rc.112 source. The slice transcribes no behaviour.

No evidence of the slice is host-only. The bounded evidence is the battery's and the probe's.

## 5. The statements as compiled, the axioms and the plan status

The namespaces are `Effect4.FrameFiber` for part A's first statements, and `Effect4.Machine`
for the rest of the first module. The second module is in `Effect4.Program` and `Effect4.Api`.
The third is in `Effect4.Api.HostSession`, `Effect4.Api.Runner` and `Effect4.Run`. Each
statement over the frame machine or the fiber machine takes the four instances
`[DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]`. The machine's types are at
their default carriers: the code is `Prim`, and the frame is `FrameFiber`.

### Part A, the frames

```lean
theorem step_maskChain (base : Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (f : FrameFiber ν σ β ε δ ι α) (valid : MaskChain base f.interruptible f.stack)
    {next : FrameFiber ν σ β ε δ ι α} (running : (f.step interp).fst = FrameStep.running next) :
    MaskChain base next.interruptible next.stack

theorem popFrom_unanswered_stack (demand : Arm) (skip : Bool) :
    ∀ (frames : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α), f.stack = [] →
      (popFrom demand skip frames f).answer = ContAnswer.empty →
        (popFrom demand skip frames f).fiber.stack = []

theorem popFrom_unanswered_flag (base : Bool) (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α) (scratch : f.stack = [])
    (valid : MaskChain base f.interruptible frames)
    (unanswered : (popFrom demand skip frames f).answer = ContAnswer.empty) :
    (popFrom demand skip frames f).fiber.interruptible = base
```

`getCont_unanswered_stack` and `getCont_unanswered_flag` state the same of `getCont`.
`step_finished_stack` and `step_finished_flag` state it of a finished step, at
`Machine.frameExitState`. `MaskChain.base_eq` gives one base for one flag and one stack.

### Part B, the invariant and the command condition

```lean
def basesOrder : WorldOrder (List Bool) :=
  ⟨fun bases bases' => bases <+: bases', List.prefix_refl, List.IsPrefix.trans⟩

def MaskKept (bases : List Bool) (f : RunFiber ν σ β ε δ ι α χ) : Prop :=
  ∃ base, bases[f.id.value]? = some base ∧
    (f.exit = none → MaskChain base f.frame.interruptible f.frame.stack)

def MaskRuns (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  bases.length = m.nextId ∧ ∀ f ∈ m.fibers, MaskKept bases f

def ClearReady (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) :
    Cmd ν σ β ε δ ι α → Prop
  | Cmd.exitDone id => ∀ f, m.fiber? id = some f →
      f.exit.isSome = true ∨ f.frame.stack = [] ∨ bases[id.value]? = some f.frame.interruptible
  | _ => True

def Exited (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) : Prop :=
  id.value < m.nextId ∧ ∀ f ∈ m.fibers, f.id = id → f.exit.isSome = true

def ClearsExited (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) : Prop :=
  ∀ id, Cmd.exitDone id ∈ cmds → Exited m id

def IterKeepsMask (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (it : Iter ν σ β ε δ ι α χ St) : Prop :=
  MaskAged m it.machine ∧ MaskLater f it.fiber ∧ noClear it.nested = true ∧
    ∀ exit, it.outcome = Outcome.finished exit → it.fiber.frame.stack = []

def EvaluatorKeepsMask (interp : RunInterp ν σ β ε δ ι α χ St) : Prop :=
  ∀ (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool),
    IterKeepsMask m f (evaluator.evaluate interp m f y)
```

The world is a table of start flags in the prefix order. Entry `n` is the flag that the fiber
with id `n` started with. The machine stores no base, and it gains none.

### Part B, the lift

```lean
theorem driveStep_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (bases : List Bool)
    (m : RunMachine ν σ β ε δ ι α χ St) (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α))
    (kept : MaskRuns bases m) (ready : ClearReady bases m c) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveStep interp m c rest).1

theorem maskRuns_stepKeeps (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (ts : List (Machine.Task ν σ β ε δ ι α)) :
    Lift.StepKeeps basesOrder interp
      (Lift.Guarded (fun bases m => MaskRuns bases m) (fun _ m cmds => ClearsExited m cmds)
        (fun _ _ _ => True) ts)

theorem replayEval_maskRuns (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsMask interp) (fuel : Nat) (tape : List (RunDecision ν σ β ε δ ι α))
    (bases : List Bool) (m : RunMachine ν σ β ε δ ι α χ St) (kept : MaskRuns bases m) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replayEval interp fuel tape m).machine

theorem MaskRuns.flag_eq {bases bases' : List Bool} {m m' : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) (kept' : MaskRuns bases' m') (grown : bases <+: bases')
    {f g : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m.fibers) (mem' : g ∈ m'.fibers)
    (same : g.id = f.id) (live : f.exit = none) (live' : g.exit = none)
    (stack : f.frame.stack = g.frame.stack) :
    f.frame.interruptible = g.frame.interruptible
```

`maskRuns_decisionLift`, `driveState_maskRuns` and `stepDecisionState_maskRuns` state the same
of a decision's edits, of the command loop and of one decision. `MaskRuns.entry_eq` gives a
live fiber one entry in each table that holds the invariant. `IterKeepsMask.finished_stack` and
`IterKeepsMask.finished_flag` state the completed exit at its event. The driver issues
`Cmd.finish` at an empty stack, and at the base where the fiber is live.

The structure `MaskChainRuns` holds twelve statements at the frame evaluator, as its fields.
They are `empty`, `start`, `spawn`, `sameBase`, `sameFlag`, `command`, `guarded`, `loop`,
`decision`, `replay`, `finished` and `finishedAtBase`. `saved_mask_chain_runs` proves it.

### The compiled program, and the program interface

```lean
theorem evaluateNative_keepsMask (root : NativeEff) (table : RowTable)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (y : Bool) :
    IterKeepsMask m f (evaluateNative root m f y table)

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem compiled_mask_chain_runs (root : NativeEff) (table : RowTable) (fuel : Nat)
    (tape : List (RunDecision EffName EffThunk Val Err Defect FiberId Ann)) (bases : List Bool)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (kept : MaskRuns bases m) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases'
      (replayEval (evaluator := evaluatorFor root table) (interpOf root table) fuel tape
        m).machine

theorem load_maskRuns (program : Program) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    MaskRuns [true] (load program compileFuel answers)

theorem replay_maskRuns (program : Program) (fuel : Nat) (tape : List Decision)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (compileFuel : Nat) :
    ∃ bases, [true] <+: bases ∧
      MaskRuns bases (replay program fuel tape answers table compileFuel).machine
```

A printed form of `compiled_mask_chain_runs` hides the instance `evaluatorFor root table`.

### The entries of step 7

An entry that steps a machine has a statement with one hypothesis: the invariant at that
machine. The statement concludes the invariant at the machine that the entry returns, at a
table that the first is a prefix of. An entry that starts a run takes no hypothesis. An opened
run, a loaded runner and a started session hold the invariant at `[true]`. `Api.runSync` and
`Api.replayChecked` return a machine that holds it at a table that starts with `true`.

| Entry | Its theorem | Module |
| --- | --- | --- |
| `Machine.runSyncExit` | `Machine.runSyncExit_maskRuns`, through the helper `flushRootState_maskRuns` | `Laws/Machine/MaskRuns.lean` |
| `Program.steppedBy` | `Program.steppedBy_maskRuns` | `Laws/Program/MaskRuns.lean` |
| `Program.replayCheckedFrom` | `Program.replayCheckedFrom_maskRuns`: the result's machine, and a refused decision's | the same |
| `Api.runSync` | `Api.runSync_maskRuns` | the same |
| `Api.replayChecked` | `Api.replayChecked_maskRuns` | the same |
| `HostSession.start`, `advance`, `applyReply`, `applyPending` | `start_maskRuns`, `advance_maskRuns`, `applyReply_maskRuns`, `applyPending_maskRuns` | `Laws/Api/MaskRuns.lean` |
| `HostSession.bindCall`, `submit`, `inspect` | the helpers `bindCall_machine` and `inspect_machine`, and `submit_machine` of `Laws/Api/HostSession.lean`: the machine is the same | the same |
| `Runner.load`, `step`, `replay` | `load_maskRuns`, `step_maskRuns`, `replay_maskRuns` | the same |
| `Runner.stepRow`, `stepBytes`, `replayRows`, `replayBytes` | `stepRow_maskRuns`, `stepBytes_maskRuns`, `replayRows_maskRuns`, `replayBytes_maskRuns` | the same |
| `Run.open`, `step`, `play` | `open_maskRuns`, `step_maskRuns`, `play_maskRuns`, and `open_play_maskRuns` for a journal from an opened run | the same |
| `Run.driveFrom`, `drive` | `driveFrom_maskRuns`, `drive_maskRuns` | the same |

```lean
theorem runSync_maskRuns (program : Program) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (compileFuel : Nat) :
    ∃ bases, [true] <+: bases ∧
      MaskRuns bases (runSync program fuel answers table compileFuel).1

theorem play_maskRuns (s : Run) (rows : List Command) (bases : List Bool)
    (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (s.play rows).machine

theorem open_play_maskRuns (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (rows : List Command) :
    ∃ bases, [true] <+: bases ∧
      MaskRuns bases ((Run.open b id budget profile).play rows).machine
```

### Axioms, plan status and census

- **Axioms.** Each of the 121 theorems is at `[propext, Quot.sound]` or at fewer axioms
  (tested). The census prints the axioms of each tagged theorem, and the battery pins 20.
- **Plan status** of both placed theorems, pinned in the battery: "proved; nearest []; 0
  lemmas, 0 definitions" and "next goals: 0". The counts are of the battery's own tree.
- **Census** (`#semantics_census`, one scratch file at `81a362a8`):

| Module | Tagged theorems | Untagged |
| --- | --- | --- |
| `Effect4.Laws.Machine.MaskRuns` | 93 | 13: the twelve projections of `MaskChainRuns`, and the helper `flushRootState_maskRuns` |
| `Effect4.Laws.Program.MaskRuns` | 8 | 0 |
| `Effect4.Laws.Api.MaskRuns` | 17 | 2: the helpers `bindCall_machine` and `inspect_machine` |

Step 7's three helpers carry no tag, on the coordinator's word. The helpers of the earlier
steps carry the concept's tag.

## 6. Each landed theorem's placement

| Statements | Concept; requirement; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| Part A | `scope-lifetime-finalization`; R11; steps of `saved-mask-chain-runs` | the polymorphic frame machine, one fixed base, every demand, skip flag and carried cause; the pop asks for an empty scratch stack | nothing of a run | part B: `evaluatePrim.stepFrame` and `evaluatePrim.finishFrame` |
| Part B: the invariant and its lift; `saved_mask_chain_runs` | the same; the general form of the claim, placed at R11 | the fiber machine at the frame evaluator, every interpreter, tape and fuel, with no admission; the statements over a command reach each evaluator that meets `EvaluatorKeepsMask` | a run of a compiled program, which uses another evaluator | `compiled_mask_chain_runs` |
| `compiled_mask_chain_runs` | the same; the claim's pointer, placed at R11 | every program, row table, tape and fuel, at the native evaluator, from each machine that holds the invariant | see below | the bracket's law, then the waiting wrapper under a masked caller, Semaphore's protected permit and Pool's `use` |
| `MaskRuns.flag_eq`, `MaskRuns.entry_eq` | the same; steps, and fields of the general form | two machines at tables in the prefix order, one fiber live in both | that a body's run returns to the entry's stack | the bracket's law |
| The entries of step 7 | the same; steps of the claim, each naming its entry | every built program, journal, budget and host function | an entry that a later change adds | a law that reads the chain at that entry |

No statement of the slice establishes the bracket of a region. None gives a flag or a stack
of an exited fiber as a state invariant. None gives a cleanup's multiplicity, a delivery, a
budget or liveness. None gives an agreement with a target or a law of a host. An invariant is
not progress.

## 7. Choices, differences from the brief, and findings

### The invariant's range, and what it does not cover

The brief's condition protects an invariant over every fiber of the table. That form is false
at a reached machine (reproduced). Under a toy interpreter, fiber 1 evaluates the registration
of a race that fiber 0 hosts. The tape is `[.evaluate ⟨0⟩, .fire ⟨0⟩]`. Fiber 0 ends exited,
with flag false and an empty stack, and it started at true. The filed probe holds the run:
`docs/research/2026-10-06-seat-LIFT-probe-exited-fiber.lean.txt`. The battery holds it as the
control `reached`.

I read two arms of `Machine.driveStep` (`src/Effect4/Machine/Fibers.lean`) for the cause.

1. The arm of `Cmd.registrationDone` continues the race's host. It does not ask which fiber
   evaluated the registration, or whether the host has exited.
2. The arm of `Cmd.loop` steps the fiber that it names. It does not ask whether it has exited.
   The arm of `Cmd.evaluate` does ask.

**Which interpreter reaches it (assumed: by reading only).** Only an interpreter that no
compiled program has. The park code of a race is built at one place:
`interp.parkCode (ParkKind.race raceId)` in `Machine.beginRace`, as the host's own code. The
compile builds a park thunk at one place, and it is a join (`src/Effect4/Program/Compile.lean`,
the arm of `awaitFiber`). The stores' programs build joins only (`progOf` and `contAOf`,
`src/Effect4/Machine/Stores.lean`). So under `interpOf root table` a race's registration is
evaluated by its host. A hand-written code of the same alphabet reaches the machine, as the
probe's does. I propose no line for `Test/Counterexamples/REGISTER.md`: no compiled program is
a witness. I proved none of this paragraph.

**What the invariant does not cover.** An exited fiber's flag and its stack. The invariant
asks only that an exited fiber has its entry in the table.

**Whether a consumer reads a fiber after its exit (assumed: by reading only).** None does. The
bracket's law reads a fiber between a region's entry and its end. The waiting wrapper reads its
caller while the caller runs it. The machine and the compile read a flag at five places.

| Reader | Whose flag |
| --- | --- |
| `Machine.interruptRecord` | an interrupt's target, after its guard `f.exit.isSome` |
| `Machine.spawn` | the parent's, under `MaskMode.inherit` |
| the two readers of `Machine/Fibers.lean` that pass the flag to `interp.closeScope` | the evaluated fiber's |
| the action `getInterruptible` | the evaluated fiber's |
| `Program.exitScoped` | the evaluated fiber's |

By the reading above, only the finding's run evaluates an exited fiber.

### The command condition

`ClearReady` has three alternatives at `Cmd.exitDone`: the fiber has exited, or its stack is
empty, or its flag is its base. The brief names the last two. The first is the one that the
driver's own commands meet. `Cmd.finish` needs no condition: `exitFiber.exitStore` publishes
the fiber before it clears it.

**No premise for the condition stays open at an entry.** There are two reasons.

1. The command loop discharges it. `maskRuns_stepKeeps` carries the pending fact `ClearsExited`
   through `Lift.Guarded`: each pending `Cmd.exitDone` names a fiber that has exited. A command
   issues `Cmd.exitDone` only for the fiber that it has published, and no command resets an exit.
2. An entry's first commands hold no `Cmd.exitDone`. They are `[Cmd.evaluate id, Cmd.drainDue]`,
   a task's commands, a resume or the clock's drain (`clearsExited_of_noClear`,
   `taskCmds_noClear`, `drainOwed_noClear`).

The condition stays a hypothesis at two statements only, for a caller that runs its own
commands. `driveStep_maskRuns` asks `ClearReady` of one arbitrary command.
`driveState_maskRuns` asks `ClearsExited` of an arbitrary list. No entry outside `Machine/`
calls `driveStep` or `driveState` (the measure below).

### The evaluator

`driveStep` takes its evaluator as an instance. `Api.replay` runs `evaluateNative` under
`evaluatorFor root table`, not `evaluatePrim` (`src/Effect4/Program/Compile.lean`). So the
general form at `evaluatePrim` alone does not cover a run of a compiled program. The statements
over a command take `EvaluatorKeepsMask`. `evaluatePrim_keepsMask` and
`evaluateNative_keepsMask` meet it. A third evaluator owes its own proof of the premise.

### The measure of the entries

Four `grep` commands list each place outside `src/Effect4/Machine` and `src/Effect4/Laws`
that makes or changes a machine. The first lists each use of a function of
`src/Effect4/Machine/Fibers.lean` whose result holds a machine.

```sh
grep -rn -E '\b(interruptEach|countdownPark|beginRace|registerRace|spawn|launchEntrant|forkFinalizers|linkScope|injectYield|evaluatePrim|iteration|fireObserver|exitFiber|settle|drainOwed|driveStep|driveState|fireStep|fireState|flushAllState|advanceState|flushRootState|stepDecisionState|stepDecision|replayEval|runFork|runCallback|runSyncExit)\b' \
  src/Effect4 --include='*.lean' | grep -v -E '^src/Effect4/(Laws|Machine)/' \
  | grep -v -E ':[0-9]+:\s*(--|/--|[^:]*`)'
```

Its output, as the declaration that holds each line (tested: the command at `81a362a8`; the
declarations by reading):

| File | Declaration | The function | What it returns | Its theorem |
| --- | --- | --- | --- | --- |
| `src/Effect4/Api.lean` | `Api.replay` | `replayEval` | a reading with a machine | `Api.replay_maskRuns` |
| `src/Effect4/Api.lean` | `Api.runSync` | `runSyncExit` | a machine and an exit | `Api.runSync_maskRuns` |
| `src/Effect4/Program/Provision.lean` | `Program.runNative`, and one `open` line | `runSyncExit` | the exit alone | none is owed |
| `src/Effect4/Program/Compile.lean` | `Program.exitScoped`, `Program.evaluateNative` | `evaluatePrim` | an evaluation | `evaluateNative_keepsMask` |
| `src/Effect4/Program/Admit.lean` | `Program.replayCheckedFrom` | `replayEval`, `stepDecisionState` | a result or a refusal, each with a machine | `replayCheckedFrom_maskRuns` |
| `src/Effect4/Program/Admit.lean` | `Program.replayStepsFrom` | `stepDecisionState` | the frontiers alone | none is owed |
| `src/Effect4/Program/Admit.lean` | `Program.steppedBy` | `stepDecisionState` | a machine | `steppedBy_maskRuns` |
| `src/Effect4/Api/HostSession.lean` | `HostSession.advance` | `stepDecisionState` | a session | `advance_maskRuns` |
| `src/Effect4/Api/HostSession.lean` | `HostSession.inspect` | `replayEval` at the empty tape | a reading with the session's machine | `inspect_machine` |

The other three commands found the rest (tested):

- **A machine's methods and its constructions:** `RunMachine.empty` and `RunFiber.make` in
  `Api.load` (`Api.load_maskRuns`), `RunMachine.empty` in `Api.runSync` and in
  `Program.runNative`, and `m.emit` in `Program.exitScoped`.
- **A write of the fields `fibers` or `nextId`:** `Api.load` alone. Two more lines write the
  field `fibers` of `Run.Observation`, which holds no machine.
- **A record update of a machine or a fiber:** `Program.enterScoped` and `Program.exitScoped`
  alone, which `evaluateNative_keepsMask` reads.

A session's machine is written at four places: `Run.open` and `HostSession.start` by
`Api.load`, `HostSession.applyReply` by `Program.steppedBy`, and `HostSession.advance`.

**The three entries that return the exit alone:** `Program.runNative`, `Api.Typed.runSync` and
`Api.Built.runSync`. `Program.replayStepsFrom` and `Api.replaySteps` return the frontiers alone.

**The entries that are another entry at given arguments, with no theorem of their own
(assumed: by reading).** `Api.run`, `Api.runAdmitted`, `Api.replayAdmitted`, `Api.Typed.replay`,
`Api.Typed.run` and the three runs of `Api.TestClock` are `Api.replay`. The three are `run`,
`runSequential` and `runDilated`. `Runner.inspect` and `Run.inspect` are `HostSession.inspect`.
`Run.answer`, `Run.receive`, `Run.control` and `Run.controlOnce` play a journal. `Run.runPure`
and `Run.runClock` play a journal from an opened run. `Run.runWith` drives an opened run that
played its start. `HostSession.retire`, `Run.runner` and `Run.machine` keep or read the machine.
`Runner.result` is the transition that `Runner.step` records.

A second `grep` reads the result types of the definitions outside `Machine/` and `Laws/`
(tested). It lists each result that names a reading, a run, a runner, a session or a machine.
It found one name that the first reading missed, `Api.TestClock.runDilated`, and no entry of
a new kind.

**A later entry is not covered until someone adds its theorem.** The measure reads names, so a
new function that returns a machine is outside it. `Machine.runFork` and `Machine.runCallback`
are inside `Machine/` and have no caller outside it. `runFork` is a step of `runSyncExit`'s
proof, and `runCallback` has no statement.

My message before step 7 listed the entries by reading. The measure then found two more base
entries, `Program.steppedBy` and `HostSession.inspect`, and the runner's rows of bytes. Step 7
covers them.

### Smaller findings

- **Codex's connector is true as written.** `cleared_maskChain_iff` elaborates unchanged, and
  `Iff.rfl` proves it. It is the case of `Cmd.exitDone` under the brief's two alternatives.
- **The appendix's two statements are renamed:** `popFrom_unanswered_stack` and
  `popFrom_unanswered_flag`. Its word "empty" also reads as a pop of an empty stack.
- **Lean stops at 100 errors.** The falsified copy needs the option `maxErrors`. Without it the
  comparison reported 17 pinned outputs as not red, which were red.
- **`nomatch` takes a list of terms.** `⟨fun h => nomatch h, rest⟩` parses `rest` as its second
  term. The proofs write `(nomatch h)`.
- **A rewrite by a lemma over an evaluator takes the wrong instance** where the goal names
  `evaluatorFor program table`. A `letI` of that instance before the rewrite repairs it.

## 8. What the bracket's law still owes

This item is written for a reader with no part in this session.

### What the bracket is

R11's open part "the run-level half of saved-mask-restoration" asks one thing. A region that
changes no flag ends with its entry flag, for an arbitrary body. Seat MASKPOP's receipt names
its missing fact in its item 8, line 7: the body's run returns to the entry's stack
(`docs/research/2026-10-06-seat-MASKPOP-receipt.md`). This slice proves the other half. Along a
run, a live fiber's flag is a function of its stack.

### The statements that the next slice starts from

| Statement | Where | What it gives |
| --- | --- | --- |
| `Machine.MaskRuns` | `src/Effect4/Laws/Machine/MaskRuns.lean` | the invariant: each live fiber holds the chain at its entry of the table of start flags |
| `Machine.MaskRuns.flag_eq` | the same | two machines at tables in the prefix order, one fiber live in both with one stack: one flag |
| `Machine.MaskRuns.entry_eq` | the same | one machine at two tables: a live fiber has one entry |
| `Machine.IterKeepsMask.finished_stack`, `finished_flag` | the same | the driver issues `Cmd.finish` at an empty stack, and at the base where the fiber is live |
| `Program.compiled_mask_chain_runs` | `src/Effect4/Laws/Program/MaskRuns.lean` | the invariant after a replay at the compiled program's interpreter, from a machine that holds it |
| `Api.load_maskRuns`, `Api.replay_maskRuns`, `Api.runSync_maskRuns`, `Api.replayChecked_maskRuns` | the same | the invariant at the program interface, with no premise |
| `Run.open_maskRuns`, `Run.play_maskRuns`, `Run.open_play_maskRuns`, `Run.drive_maskRuns` | `src/Effect4/Laws/Api/MaskRuns.lean` | the invariant at a journaled run, with no premise on the built program |
| `Machine.saved_mask_pop_discipline` | `src/Effect4/Laws/Machine/MaskDiscipline.lean` | the chain through a pop and through each region's entry, at one frame machine |
| `Program.Typed.saved_mask_restoration` | `src/Effect4/Laws/Program/Typed/Mask.lean` | the mask's law at the boundaries of a region, on the frame machine |
| `Run.play_append`, `Api.Runner.replay_append`, `Machine.replayEval_append_machine` | `src/Effect4/Laws/Run.lean`, `src/Effect4/Laws/Api/Runner.lean`, `src/Effect4/Laws/Machine/Approximation.lean` | two cuts of one run: the second is reached from the first |

The composition below compiles from the landed theorems (tested: one scratch file, with
warnings as errors). It is not landed. It is the form in which the bracket reads this slice.

```lean
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)

/-- Two cuts of one journaled run: a fiber that is live at both with one stack has one flag. -/
example (s : Run) (a b : List Command) (bases : List Bool) (kept : MaskRuns bases s.machine)
    (f g : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (mem : f ∈ (s.play a).machine.fibers) (mem' : g ∈ (s.play (a ++ b)).machine.fibers)
    (same : g.id = f.id) (live : f.exit = none) (live' : g.exit = none)
    (stack : f.frame.stack = g.frame.stack) :
    f.frame.interruptible = g.frame.interruptible := by
  obtain ⟨bases₁, _, kept₁⟩ := Run.play_maskRuns s a bases kept
  obtain ⟨bases₂, le, kept₂⟩ := Run.play_maskRuns (s.play a) b bases₁ kept₁
  rw [Run.play_append] at mem'
  exact kept₁.flag_eq kept₂ le mem mem' same live live' stack

/-- Two cuts of one replay at the compiled program's interpreter. -/
example (root : NativeEff) (table : RowTable) (fuel : Nat) (tape : List NativeDecision)
    (bases : List Bool) (m : NativeMachine) (kept : MaskRuns bases m)
    (f g : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (mem : f ∈ m.fibers)
    (mem' : g ∈ (replayEval (evaluator := evaluatorFor root table) (interpOf root table) fuel tape
      m).machine.fibers)
    (same : g.id = f.id) (live : f.exit = none) (live' : g.exit = none)
    (stack : f.frame.stack = g.frame.stack) :
    f.frame.interruptible = g.frame.interruptible := by
  obtain ⟨bases', le, kept'⟩ := compiled_mask_chain_runs root table fuel tape bases m kept
  exact kept.flag_eq kept' le mem mem' same live live' stack
```

### Each premise that stays open

1. **The stack at the region's end is the entry's stack.** No theorem states it. It is the
   bracket's own fact, and the hypothesis `stack` above. It needs a definition of the two cuts,
   the region's entry and its end, and a law of the frame machine's stack between them.
2. **The fiber is live at both cuts.** The hypotheses `live` and `live'` above. The invariant
   says nothing of an exited fiber. A body that runs has not published its exit, but no theorem
   states that at a cut.
3. **The two cuts are of one run.** The hypothesis `grown` of `flag_eq`. The lift discharges it
   where the second cut is reached from the first, as the composition shows.
4. **The command condition: nothing is open.** Item 7 gives the two reasons. A caller that runs
   `driveStep` or `driveState` on its own commands owes `ClearReady` or `ClearsExited`.
5. **The evaluator's premise: nothing is open** for `evaluatePrim` and `evaluateNative`.
6. **An entry that a later change adds** owes its theorem.

One trap is recorded in the tree. `src/Effect4/Laws/Machine/LiveStack.lean` notes that a
passing `asyncFinalizer` frame grows the stack during a pop. So "a frame that does not answer
leaves the stack alone" is false, and premise 1 is about two cuts, not about each pop.

### What the wrapper under a masked caller owes beyond the bracket

The semantics registry keeps one client premise for the run-level half. Nothing is acquired
or registered before the body begins (decisions rows 227, 244 to 246). The wrapper's delivery,
its cleanup and its budget are other claims. This slice gives none of them.

### The commands that reproduce the battery and its red controls

Run each from the worktree. `SLOT` is the Lean slot of item 4, and no `lake` runs without it.

```sh
# The battery: it exits 0 and prints nothing.
SLOT lake env lean -M6144 -DwarningAsError=true Test/Machine/MaskRuns.lean

# The same through Lake, with the three law modules:
SLOT lake build Effect4.Laws.Machine.MaskRuns Effect4.Laws.Program.MaskRuns \
  Effect4.Laws.Api.MaskRuns Effect4.Laws Test.Machine.MaskRuns
```

The red controls are fixtures of the battery, so the first command runs them.

| Red control | What it shows |
| --- | --- |
| `pushNoMask`, with its two guards | a step that pushes a restoring frame and keeps the flag breaks the chain |
| `unanswered_needs_empty_scratch` (proved) | the unanswered pop needs the empty scratch stack |
| `unanswered_flag_needs_chain`, `base_needs_flag` (proved) | the flag's statement needs the chain, and one base needs one flag |
| `answered`, with its three guards | a finished frame's statement needs a finished step |
| `trap`, with `#guard !runs [true] (clear trap)`, and `exitDone_needs_ready` (proved) | an arbitrary `Cmd.exitDone` on a live fiber breaks the invariant, so the command condition is needed |
| `#guard !runs [false] trap`, `#guard !runs [true, true] …` | a live fiber's entry is no arbitrary bit |
| `sameFlag_needs_one_run` (proved) | `flag_eq` needs the prefix order between the two tables |
| `reached`, with `#guard !everyFiber …` | the form over every fiber is false at a reached machine |
| each guard `fitting … == [table]` | exactly one table fits every cut, so each other table is red at some cut |

A second check asks that no check of the battery is empty. The filed script
`docs/research/2026-10-06-seat-LIFT-falsify.py.txt` changes each check so that it must fail.
Copy it to a scratch folder `OUT` as `falsify.py`, then run:

```sh
python3 OUT/falsify.py write Test/Machine/MaskRuns.lean OUT
SLOT lake env lean -M6144 -DwarningAsError=true -DmaxErrors=1000 OUT/battery-red.lean \
  > OUT/battery-red.log 2>&1
python3 OUT/falsify.py compare OUT
```

The second command exits 1, and the third exits 0 (tested at `81a362a8`). The third prints
the counts: 118 errors, and no error outside a changed check. Red are 61 of 61 guards, 22 of
22 pinned outputs and 30 of 30 proved controls. The battery holds 31 proved items. The one
that the copy leaves is `atNat`, the general form at the alphabets `Nat`. Six examples read
it.

## 9. The text of the semantics registry, and the proposals

### What the main line holds

The coordinator's seventh message reports four things, and I read each in the coordinator's
checkout.

- The claim `saved-mask-chain-runs`: concept `scope-lifetime-finalization`, role
  `preservation`, pointer `Effect4.Program.compiled_mask_chain_runs`.
- The three law modules are default modules of the concept. So the twelve projections and
  step 7's three helpers inherit it, with no tag of their own.
- R11's line "the lift of saved-mask-pop-discipline to runs" is gone. The run-level half reads
  as the bracket of a region.
- `docs/core/semantics.md` holds the required property.

### The differences, each with its replacement (proposals)

- **C1, the false sentence of the property.** For "The machine holds one table of start
  flags.":

  > A table of start flags is proof data: the machine stores no base.

- **C2, the entries, in the property.** For "Each entry of the program interface that returns
  a machine holds it with no premise (`src/Effect4/Laws/Api/MaskRuns.lean`).":

  > Each entry outside the machine that returns a machine keeps it, with no premise for the
  > condition. An entry that starts a run holds it outright. An entry that steps a machine
  > keeps it from that machine. (`src/Effect4/Laws/Program/MaskRuns.lean`,
  > `src/Effect4/Laws/Api/MaskRuns.lean`).

- **C3, the entries, in the claim's title.** For "so each entry that returns a machine holds
  it with no premise":

  > so each entry outside the machine that returns a machine keeps it, with no premise for the
  > condition

- **C4, the bracket's second fact, in R11's line.** After "that the body's run returns to the
  entry's stack":

  > at a fiber that is live at both cuts, which no theorem states at a cut

- **C5, a precision of the property, not a difference of substance.** The condition is on
  `Cmd.exitDone` alone. `Cmd.finish` publishes the fiber before it clears it, so it asks for
  nothing. The property's sentence reads as a condition on each command that clears.

### The proposals that stay

- **P1. The documents.** A row of `docs/ARCHITECTURE.md` for each of the three modules. The
  role register needs no row: the areas `src/Effect4/Laws/Machine`, `src/Effect4/Laws/Program`
  and `src/Effect4/Laws/Api` hold them.
- **P2. Two general statements may move to `src/Effect4/Laws/Machine/Lift.lean`.**
  `admittedReplay_true`: with no admission, every tape is admitted. And the lift of
  `flushRootState`, in the form of `FoldLift.flushAllState_lift`. Neither reads the mask.
- **P3. A question for the owner, not a recommendation.** The arm of `Cmd.loop` could refuse an
  exited fiber, as the arm of `Cmd.evaluate` does. The invariant could then range over every
  fiber. It is a change of the machine. I did not read rc.112 for it.
- **P4. The next slice** is the bracket. Its first statements are item 8's premises 1 and 2.
  The two examples follow as placed statements, then the waiting wrapper under a masked caller.

## 10. The requirements R1 to R13

The slice advances R11 alone. R11 gains two placed nodes, both proved. One of its eight open
parts is now a theorem: the lift of `saved-mask-pop-discipline` to runs. R11 stays open. Its
run-level half of `saved-mask-restoration` still owes the bracket. Six more open parts are
untouched. They are release at most once, the close order, the state at a frontier, and the
open scope of a finished run. They are the pool's two claims and the waiting request's
obligation too. The goals `cleans_once`, `cleanup_keeps` and `releases_once` stay goals. The
slice's theorems rest on no planned goal. R10 and R12 gain no theorem. The waiting wrapper,
Semaphore's protected permit and Pool's `use` are consumers after the bracket. The slice
states no delivery, no budget and no liveness. R1 to R9 and R13 have no relation to the slice.
It types nothing, and it changes no language signature, no data, no world, no service and no
host law. It states no agreement with a target. The report as committed at the head of the
code counts the open parts of each requirement. For R1 to R13 in order, the counts are 4, 5,
6, 6, 2, 7, 4, 6, 1, 13, 8, 9 and 4. One `awk` command counts the lines that open with
"- Open:". The report is not regenerated here, so R11's count still holds the part that this
slice proves. On the main line the semantics registry now holds one line for R11's two lines
of the mask.

## 11. Open obligations

None of the brief's table. No planned goal of the slice is open. Item 8 lists what the next
slice owes. Item 9 holds five replacements and four proposals, and no one has ruled them.

## 12. Proposed decisions rows (proposals only)

| Topic | Proposal |
| --- | --- |
| The range of the saved mask's chain along a run | The invariant ranges over the live fibers. A fiber's base is proof data, a table of start flags in the prefix order, and the machine stores no base. An exited fiber's flag and stack are outside the invariant: a hand-written interpreter reaches a machine where a second fiber steps an exited one. No compiled program reaches it (by reading) |
| The entries that return a machine | Each entry outside `Machine/` and `Laws/` that returns a machine has a theorem that names it. A new entry owes its theorem in the slice that adds it |
