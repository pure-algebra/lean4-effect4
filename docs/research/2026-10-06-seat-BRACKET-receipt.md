# 2026-10-06 seat BRACKET receipt: a region ends at its entry's stack and at its entry flag

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-bracket-brief.md`, with the dispatch message.
Design note: `docs/research/2026-10-06-seat-BRACKET-design.md`. The coordinator sent one
message after the dispatch, with three asks. Each one is named below where it changed the
slice.

In this receipt a cut of a run is a state of one fiber on a run. On the frame machine it is a
`FrameFiber`, and on the fiber machine it is a fiber of a reached machine. It is the brief's
sense of the word, and item 9 proposes a dictionary entry for it. A fiber is live while its
`exit` is `none`.

**The one thing to know before merging:** the bracket is proved, and it reads a region by one
premise. The later cut's stack shape `above ++ below` is a premise, and it is the region's
only mark on the machine. The theorem then gives the entry's stack and the entry flag at the
region's end. It does not give that a body's run keeps that shape. So R11's open part "the
bracket of a region" becomes a claim, and one new open part takes its place: the carrying
fact. Item 8 opens with it.

Seven more facts stand beside it.

- **Both placed theorems are proved in place.** The stop rule did not apply. The goal gate
  counts 24 planned goals, as at the base. Step 1 added two goals, and step 2 proved both.
- **The second fact is a placed theorem** (the coordinator's first ask):
  `Program.stepped_live`. At each cut of a compiled command loop, a fiber that a pending
  command steps has not exited. Decisions row 278, point 1, says that nothing proves this. The
  sentence is stale at the merge, and item 9 holds its replacement.
- **Three sentences on the main line are stale at the merge.** They are R11's open part of the
  semantics registry, the required property in `docs/core/semantics.md`, and row 278. I read
  each in the coordinator's checkout, and I wrote nothing there. No claim of this slice is
  entered there yet.
- **Two law modules, not one.** The coordinator accepted the difference from the brief.
- **The carrying fact is not started** (the third ask). I judge it a slice of its own. Lean
  elaborates its statement in scratch, and a finite probe finds no counterexample on eight
  runs.
- **The end of a region is no cut between two steps in general.** It is inside the pop that
  delivers the body's exit. So the bracket's conclusion is about a fiber inside a step,
  `FrameFiber.regionEnd`, and about how the pop goes on from it.
- **No file outside the brief's list changed**, but for the second law module. I edited no
  file under `src/Effect4/Machine/`, no file of seat WORKQ and none of the coordinator's six
  files.

The sections below carry the brief's item numbers. Item 1 is the bold line above.

## 2. Base, head and commits

| Item | Value |
| --- | --- |
| Branch | `seat/bracket`, in the worktree `/Users/pooks/Dev/lean4-effect4-mask` |
| Base | `76a6f215` |
| Main-line heads taken in | none |
| The main line when I read it last | `e4f25c5a`. Since the base it changes `Test/All.lean` by three lines and `src/Effect4/Laws.lean` by one line, at other places. It changes no file under `src/Effect4/Machine`, `src/Effect4/Laws/Machine` or `src/Effect4/Laws/Program/Guard`, and none of `src/Effect4/Laws/Program/MaskRuns.lean` and `src/Effect4/Program/Compile.lean` (tested: `git diff --stat 76a6f215 refactor/phase1-phase3` over those paths). `git merge-tree --write-tree 473c85f1 refactor/phase1-phase3` exits 0 (tested). I ran no merge |
| Head of the code | `473c85f1` |
| Head | the commit that holds this receipt |

Nothing is pushed.

| Commit | Step | Content |
| --- | --- | --- |
| `0b21b8c2` | 0 | the design note |
| `5095b7af` | 1 | both law modules: the cuts, the two facts and each step proved; the bracket as two planned goals, placed at R11; the two imports in the Laws root |
| `b5835ac3` | 2 | the bracket along a run, and both goals proved in place |
| `b315e78b` | 3 | the battery, and its import in `Test/All.lean` |
| `473c85f1` | 4 | two docstrings: the battery's head, and `stepped_live`'s; no statement and no check changes |
| the head | — | this receipt, the design note's addendum, the falsifying script and the carrying fact's text |

The coordinator's message, and what each ask changed:

| Ask | What it changed |
| --- | --- |
| The design and the two modules are accepted | nothing |
| 1. Land `stepped_live` as a placed theorem | It is placed at R11. It reads each pending command, not the head alone, and the pointer reads its cuts the same way. The toy interpreter's two cuts are its red control. Item 9 proposes its claim |
| 2. Say the reach in the same words everywhere | The three sentences stand in both module heads, in both placed docstrings, in item 1 and in item 9's claim |
| 3. The carrying fact, under the stop rule, or first in item 8 | Not started. Item 8 opens with its statement, the arms that it crosses and an estimate |

## 3. Changed files

`git diff --stat 76a6f215..473c85f1` lists six files and 2420 inserted lines. The counts of
declarations come from `grep` over the lines that open one.

| Group | File | What changed |
| --- | --- | --- |
| The laws | `src/Effect4/Laws/Machine/MaskBracket.lean` | new: 25 theorems, 5 definitions and the structures `RegionEnds` and `RegionBracket` |
| The laws | `src/Effect4/Laws/Program/MaskBracket.lean` | new: 12 theorems and the structure `LoopCut` |
| The laws | `src/Effect4/Laws.lean` | two imports, in order, after `import Effect4.Laws.Api.MaskRuns` |
| The batteries | `Test/Machine/MaskBracket.lean` | new: 65 guards, 16 pinned outputs and 15 proved items |
| The batteries | `Test/All.lean` | one import, after `import Test.Machine.MaskRuns` |
| The notes | the design note, this receipt, and two filed texts | `docs/research/2026-10-06-seat-BRACKET-falsify.py.txt` and `docs/research/2026-10-06-seat-BRACKET-carry.lean.txt` |

**Why two law modules.** The general form imports `Effect4.Laws.Machine.MaskRuns` alone. The
pointer imports `Effect4.Laws.Program.MaskRuns` and `Effect4.Laws.Program.Guard.Decision`: it
reads the guard's invariants. Seat LIFT's modules have the same split.

## 4. Commands, results and evidence

Each Lean, Lake or `make` command ran through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, named `SLOT` below. The `make` call took
the three flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`. `LEAN` stands
for `SLOT lake env lean -M6144 -DwarningAsError=true`. A scratch file is in the session's
scratch folder, which no later session holds.

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build`, at the base `76a6f215` | `Build completed successfully (1018 jobs).` Lake restored `Test.All` from its cache, so the run gave no gate line | tested |
| `LEAN Test/All.lean`, at the base | exit 0; the base's gate lines, in the table below | tested |
| the scratch probes of the design note | each statement proved at `[propext, Quot.sound]` or at fewer axioms | tested |
| `SLOT lake build Effect4.Laws.Machine.MaskBracket Effect4.Laws.Program.MaskBracket`, at step 1 | `Build completed successfully (389 jobs).` | tested |
| `SLOT lake build Effect4.Laws`, at step 1 | `Build completed successfully (686 jobs).` | tested: the root's anchor |
| `#plan_status` and `#print axioms` in one scratch file, at step 1 | both placed theorems read "goal", each with its statement as its one next goal; `stepped_live` reads "proved" | tested |
| `SLOT lake build` of the two modules and `Effect4.Laws`, at step 2 | `Build completed successfully (686 jobs).` | proved: the kernel accepts each theorem |
| the same scratch file, at step 2 | item 5's plan status and axioms | tested |
| `LEAN Test/Audit/ProofStyle.lean`, at step 2 | `proof style: 1911 recorded uses and 52 recorded unread commands in 1161 entries`, and no finding | tested |
| `SLOT lake build Effect4.Laws.Machine.MaskBracket Effect4.Laws.Program.MaskBracket Test.Machine.MaskBracket`, at step 3 | `Build completed successfully (399 jobs).` The battery takes ten seconds | tested |
| the falsified copy of the battery (item 8, the last part), at `b315e78b` and at `473c85f1` | 96 errors, each at a changed check; the comparison exits 0 | tested |
| `SLOT lake build`, at `b315e78b` and again at `473c85f1` | `Build completed successfully (1021 jobs).` each time, with the gate lines below | proved, for the laws; tested, for the batteries |
| `SLOT make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` | tested |
| `#semantics_census` on both modules, in one scratch file | item 5's census | tested |
| the carrying fact's statement, in one scratch file | Lean elaborates each definition and statement; two `sorry` bodies | tested: an elaboration, and no proof |
| the carrying fact's probe, in one scratch file | eight rows, each with no failing input (item 8) | tested: a finite probe |
| `python3 scripts/check-language.py --strict` on this receipt and on the design note | `PASS`, no finding in either | tested |

### The gate lines of the default build

| Gate | The base `76a6f215` | The head of the code `473c85f1` |
| --- | --- | --- |
| Jobs | 1018 | 1021 |
| Library roots | 176 API and utility modules, 314 Laws-only modules | 176 and 316 |
| Modules and axioms | 768 modules and 90105 declarations | 771 modules and 90314 declarations |
| Planned goals | 24 goals; 11 declarations rest on goals | 24 goals; 11 declarations rest on goals |
| Proof style | not read at the base | 1911 recorded uses and 52 recorded unread commands in 1161 entries |

Each run of the axiom gate reads: "semantic/test axioms are [propext, Quot.sound]; exact
implementation boundary (17 module(s), 23 declaration(s)) additionally allows
Classical.choice". The goal gate adds: "no other declaration reaches sorryAx". The
library-root gate adds: "every library source is reachable; Effect4 never reaches Laws". The
slice adds three modules and 209 declarations.

### Not run

`make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`,
`make check-truth`, the conservativity script and `make gen-semantics`, as the brief lists.
Also not run: `make check`, `make check-full`, `make check-semantics`, `make check-cases` and
`make gen-architecture`. The slice adds no match on a family of the case policy
(`tools/Conform/Effect4/cases-policy.json`, nine families): its matches read `Prim`,
`ContAnswer`, `Cmd` and `LoopNext`. No TypeScript compiler, no OCaml build and no host ran. No
install and no download ran.

### Red or stale for a reason outside the slice

Nothing that I ran is red. The proof-style gate lists 52 unread commands, as at the base. One
identifier is reserved outside the slice: `over`. A command of
`src/Effect4/Laws/Auto/Positions.lean` declares the token, so each module that imports it
refuses `over` as a name. The slice's hypothesis is named `inside`.

### What is proved, what is tested, and what is only read

- **Proved:** each theorem of the two modules, at every alphabet, stack, demand, skip flag,
  carried cause, program and row table that its statement names.
- **Tested:** each guard of the battery, on its finite inputs. A guard over a compiled program
  reads the root's first command loop on one schedule.
- **Tested, a finite probe:** the carrying fact's statement at one command, on eight runs.
- **Reproduced:** seat LIFT's reached machine, at the cuts of its command loop. At two of the 17
  cuts of the toy run's second decision, a pending command steps the exited fiber 0.
- **Assumed, by reading only:** the kinds of stack writes outside a frame step. The fiber
  machine pushes, it pops through `getCont`, and it clears an exited fiber. Item 8 lists the
  places.
- **Not consulted:** the vendored rc.112 source. The slice transcribes no behaviour.

No evidence of the slice is host-only. The bounded evidence is the battery's and the probe's.

## 5. The statements as compiled, the axioms and the plan status

The namespaces are `Effect4.FrameFiber` for the frame machine's statements, `Effect4.Machine`
for the statements over a run, and `Effect4.Program` for the second module. Each statement over
a pop takes the four instances `[DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
[DecidableEq α]`.

### The cuts

```lean
def under (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α)) :
    FrameFiber ν σ β ε δ ι α :=
  { f with stack := f.stack ++ below }

def own (f : FrameFiber ν σ β ε δ ι α) (above : List (Prim ν σ β ε δ ι α)) :
    FrameFiber ν σ β ε δ ι α :=
  { f with stack := above }

def regionEnd (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α)) (demand : Arm)
    (skip : Bool) (cause : Option (Cause ε δ ι α) := none) : FrameFiber ν σ β ε δ ι α :=
  (f.getCont demand skip cause).fiber.under below

def Steps {κ : Type (max u v)} (id : FiberId) : Cmd ν σ β ε δ ι α κ → Prop
  | Cmd.loop fiber _ => fiber = id
  | Cmd.deliver fiber _ => fiber = id
  | _ => False

structure LoopCut (p : NativeEff) (table : RowTable) (bases : List Bool) (m : NativeMachine)
    (cmds : List NCmd) : Prop where
  state : GuardState m
  queue : GuardQueue p table m cmds
  registration : RegistrationQueue cmds
  kept : MaskRuns bases m
```

The machine's code holds no mark of a region. Its entry is a cut, whose stack is `below`. A
cut inside it has the stack `above ++ below`, and `g.own above` is the fiber with its own
frames alone. Its end is `regionEnd (g.own above) below demand skip cause`, read where the pop
of the own frames answers nothing.

### The bracket's conclusion

```lean
structure RegionEnds (entry g : FrameFiber ν σ β ε δ ι α) (above : List (Prim ν σ β ε δ ι α))
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α)) : Prop where
  stack : (regionEnd (g.own above) entry.stack demand skip cause).stack = entry.stack
  flag : (regionEnd (g.own above) entry.stack demand skip cause).interruptible =
    entry.interruptible
  answer : (g.getCont demand skip cause).answer =
    ((regionEnd (g.own above) entry.stack demand skip cause).getCont demand skip
      ((g.own above).getCont demand skip cause).carriedCause).answer
  fiber : (g.getCont demand skip cause).fiber =
    ((regionEnd (g.own above) entry.stack demand skip cause).getCont demand skip
      ((g.own above).getCont demand skip cause).carriedCause).fiber
  carried : (g.getCont demand skip cause).carriedCause =
    ((regionEnd (g.own above) entry.stack demand skip cause).getCont demand skip
      ((g.own above).getCont demand skip cause).carriedCause).carriedCause
```

### The frame machine

```lean
theorem MaskChain.append_iff {base flag : Bool} {above below : List (Prim ν σ β ε δ ι α)} :
    MaskChain base flag (above ++ below) ↔
      ∃ mid, MaskChain mid flag above ∧ MaskChain base mid below

theorem MaskChain.above {base entry flag : Bool} {above below : List (Prim ν σ β ε δ ι α)}
    (valid : MaskChain base flag (above ++ below)) (entered : MaskChain base entry below) :
    MaskChain entry flag above

theorem getCont_under_answered (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α))
    (answered : (f.getCont demand skip cause).answer ≠ ContAnswer.empty) :
    (f.under below).getCont demand skip cause =
      { f.getCont demand skip cause with
        fiber := (f.getCont demand skip cause).fiber.under below }

theorem step_under (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (next : FrameFiber ν σ β ε δ ι α)
    (running : (f.step interp).fst = FrameStep.running next) :
    ((f.under below).step interp).fst = FrameStep.running (next.under below)

theorem regionEnd_stack (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α))
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α))
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (regionEnd f below demand skip cause).stack = below

theorem regionEnd_flag (entry : Bool) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)) (own : MaskChain entry f.interruptible f.stack)
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (regionEnd f below demand skip cause).interruptible = entry

theorem regionEnds_of_base (base : Bool) (entry g : FrameFiber ν σ β ε δ ι α)
    (above : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)) (inside : g.stack = above ++ entry.stack)
    (entered : MaskChain base entry.interruptible entry.stack)
    (valid : MaskChain base g.interruptible g.stack)
    (unanswered : ((g.own above).getCont demand skip cause).answer = ContAnswer.empty) :
    RegionEnds entry g above demand skip cause
```

`popFrom_append_answered` and `popFrom_append_unanswered` state the pop of `above ++ below`
from the pop of `above`. They ask for no scratch premise. `getCont_under_unanswered` and
`getCont_regionEnd` state the pop that goes on. `resumeValue_under` and `resumeCause_under`
are the two steps of `step_under`. `regionEnds_of_chain` is the bracket from the chain of the
own frames.

### A run

```lean
theorem MaskRuns.above {bases bases' : List Bool} {m m' : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) (kept' : MaskRuns bases' m') (grown : bases <+: bases')
    {f g : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m.fibers) (mem' : g ∈ m'.fibers)
    (same : g.id = f.id) (live : f.exit = none) (live' : g.exit = none)
    {above : List (Prim ν σ β ε δ ι α)} (inside : g.frame.stack = above ++ f.frame.stack) :
    MaskChain f.frame.interruptible g.frame.interruptible above

theorem MaskRuns.bracket {bases bases' : List Bool} {m m' : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) (kept' : MaskRuns bases' m') (grown : bases <+: bases')
    {f g : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m.fibers) (mem' : g ∈ m'.fibers)
    (same : g.id = f.id) (live : f.exit = none) (live' : g.exit = none)
    {above : List (Prim ν σ β ε δ ι α)} (inside : g.frame.stack = above ++ f.frame.stack)
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α))
    (unanswered : ((g.frame.own above).getCont demand skip cause).answer = ContAnswer.empty) :
    RegionEnds f.frame g.frame above demand skip cause
```

The structure `RegionBracket` holds six statements as its fields: `chain`, `between`,
`answered`, `frames`, `inside` and `ends`. `saved_mask_region_bracket` proves it.

### The compiled program's interpreter

```lean
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stepped_live (p : NativeEff) (table : RowTable) {m : NativeMachine} {cmds : List NCmd}
    (state : GuardState m) (queue : GuardQueue p table m cmds) {c : NCmd} (pending : c ∈ cmds)
    {id : FiberId} (steps : Steps id c) {f : NFiber} (found : m.fiber? id = some f) :
    f.exit = none

theorem clearsExited_of_guard (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {cmds : List NCmd} (state : GuardState m) (queue : GuardQueue p table m cmds) :
    ClearsExited m cmds

theorem LoopCut.step {p : NativeEff} {table : RowTable} {bases : List Bool} {m : NativeMachine}
    {c : NCmd} {rest : List NCmd} (cut : LoopCut p table bases m (c :: rest)) :
    ∃ bases', bases <+: bases' ∧ LoopCut p table bases'
      (driveStep (evaluator := evaluatorFor p table) (interpOf p table) m c rest).1
      (driveStep (evaluator := evaluatorFor p table) (interpOf p table) m c rest).2

theorem LoopCut.load (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    LoopCut p table [true] (Api.load p compileFuel answers)
      [Cmd.evaluate Api.root, Cmd.drainDue]

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem compiled_region_bracket (p : NativeEff) (table : RowTable) {bases bases' : List Bool}
    {m m' : NativeMachine} {cmds cmds' : List NCmd} (entry : LoopCut p table bases m cmds)
    (later : LoopCut p table bases' m' cmds') (grown : bases <+: bases') {c c' : NCmd}
    (pending : c ∈ cmds) (pending' : c' ∈ cmds') {id : FiberId} (steps : Steps id c)
    (steps' : Steps id c') {f g : NFiber} (found : m.fiber? id = some f)
    (found' : m'.fiber? id = some g) {above : List NCode}
    (inside : g.frame.stack = above ++ f.frame.stack) (demand : Effect4.Arm) (skip : Bool)
    (cause : Option CauseV)
    (unanswered : ((g.frame.own above).getCont demand skip cause).answer = ContAnswer.empty) :
    RegionEnds f.frame g.frame above demand skip cause
```

`LoopCut.drive` states `LoopCut.step` of the command loop at every budget. `LoopCut.evaluate`
and `LoopCut.task` give a cut at the start of an `evaluate` decision and at a dispatcher task
whose keys are reserved. `LoopCut.live` is `stepped_live` at a cut, and `LoopCut.pending` is
`clearsExited_of_guard` at a cut. `guarded_driveStep_maskRuns` keeps the chain's invariant
through one command, under the guard's queue alone. A printed form of the pointer shows the
fiber's default code and frame types at each `f.frame`.

### Axioms, plan status and census

- **Axioms.** Each of the 37 theorems is at `[propext, Quot.sound]` or at fewer axioms
  (tested). The census prints the axioms of each tagged theorem, and the default build's axiom
  gate reads each declaration. The battery pins 13.
- **Plan status** of the three placed theorems, pinned in the battery: "proved; nearest [];
  0 lemmas, 0 definitions" and "next goals: 0". The counts are of the battery's own tree. At
  step 1 the two brackets read "goal".
- **Census** (`#semantics_census`, one scratch file at `b315e78b`; step 4 changes no
  declaration):

| Module | Tagged theorems | Untagged |
| --- | --- | --- |
| `Effect4.Laws.Machine.MaskBracket` | 20 | 11: the five projections of `RegionEnds` and the six of `RegionBracket` |
| `Effect4.Laws.Program.MaskBracket` | 11 | 4: the projections of `LoopCut` |

The census does not list a private theorem. The two modules hold six, and each carries the
concept's tag.

## 6. Each landed theorem's placement

| Statements | Concept; requirement; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The frame machine's steps | `scope-lifetime-finalization`; R11; steps of `saved-mask-region-bracket` | the polymorphic frame machine, at every stack, demand, skip flag, carried cause and scratch stack | nothing of a run; nothing of a pop that an own frame answers, but that the frames under it stay | the bracket along a run |
| The first fact: `regionEnd_stack`, with `getCont_regionEnd` | the same | a pop of the own frames that answers nothing | that a cut has the stack `above ++ below` | `RegionEnds.stack`, and its last three fields |
| `MaskRuns.above`, `MaskRuns.bracket`; `saved_mask_region_bracket` | the same; the general form of the claim, placed at R11 | two machines that hold `MaskRuns` at tables in the prefix order, at every interpreter and evaluator, and a fiber live at both cuts | that a fiber is live at a cut; that a body's run keeps the shape | `compiled_region_bracket` |
| The second fact: `stepped_live` | the same; the proposed claim `stepped-fiber-live`, placed at R11 | every program and row table, each machine and pending commands that hold the guard's state and queue | that a fiber is stepped; a fiber that no pending command steps; a hand-written interpreter | `compiled_region_bracket`, and each law that reads a fiber at its own step |
| `LoopCut` and its seven theorems | the same; steps of both claims | a compiled command loop from a cut; the start of an `evaluate` decision; a dispatcher task whose keys are reserved | a cut at the start of each other decision | a proof that reads two cuts of one run |
| `compiled_region_bracket` | the same; the claim's pointer, placed at R11 | every program, row table, demand, skip flag and carried cause, at two cuts of one command loop's run | see below | the waiting wrapper under a masked caller, then Semaphore's protected permit and Pool's `use` |

The later cut's stack shape `above ++ below` is a premise, and it is the region's only mark on
the machine. The theorem then gives the entry's stack and the entry flag at the region's end.
It does not give that a body's run keeps that shape.

No statement of the slice gives a cleanup, a release count, a delivery, a budget or liveness.
None states a region whose fiber exits inside it. None gives an agreement with a target or a
law of a host. The client premise of the mask's derived form stays with the client. Nothing is
acquired or registered before the body begins (decisions rows 227 and 244 to 246). The bracket
takes no hypothesis for it, and it states nothing of the form's two checkpoints before its
body. An invariant is not progress.

## 7. Choices, differences from the brief, and findings

### Choices

- **C1. The home.** The cuts are on the frame machine, the second fact is at the compiled
  program's interpreter, and the journaled run is not the home. A region's entry and its end
  fall inside one row's command loop (tested: the battery's decision cut shows an exited root).
- **C2. The end is a fiber inside a step.** `regionEnd` is the fiber that the pop of the own
  frames leaves, over the entry's stack. The bracket states its stack and its flag, and it
  states that the fiber's pop goes on as the pop of that fiber.
- **C3. One case for both kinds of region.** A region that changes its flag and a region that
  changes no flag differ in their own frames only. The statement reads the entry's stack and
  the entry flag.
- **C4. A cut of a compiled command loop is a structure** (`LoopCut`): the guard's three
  invariants and the chain's invariant. Each command gives a cut again.
- **C5. A cut reads a fiber that a pending command steps**, not the head command's fiber alone.
  The guard's queue speaks of each pending command. So a parent whose next step waits behind a
  child's run is read too.
- **C6. Two structures hold the conclusion and the general form.** `RegionEnds` has five
  fields, and `RegionBracket` has six.
- **C7. The pop's law is stated once, privately** (`popFrom_append`), over a joined pop. Its two
  public forms split on the first pop's answer.
- **C8. No bank.** The module registers no rule. Each proof takes no `first`, no `try` and no
  `simp_all`, and each `simp` names its lemmas.

### Each difference from the brief

- **Two law modules** (C1, item 3). Accepted.
- **The bracket's conclusion is not one flag at a cut.** The brief's two facts read as a cut
  with the entry's stack. Such a cut does not exist where the last own frame passes (finding
  F1). The conclusion is over `regionEnd`.
- **The second fact is proved for the cuts of a compiled command loop, and it is a premise in
  the general form.** No general statement gives it (finding F3).
- **The stack's shape at the later cut is a premise.** It is the definition of a cut inside a
  region. The carrying fact would give it from the entry (item 8).
- **Three additions**: `stepped_live` as a placed theorem, `LoopCut.task`, and the step
  between the cuts, `step_under`.

### Findings

- **F1. The end of a region is no cut between two steps in general.** A restoring frame
  passes inside the pop that delivers the body's exit, and so does a handler of the other
  arm. On one frame run the stacks have lengths 1, 2 and 0 (tested: the battery).
- **F2. Seat LIFT's reading is a consequence of landed theorems.** `GuardQueue.authority`
  gives the fiber of each pending `Cmd.loop` and `Cmd.deliver` as running.
  `GuardState.exited` gives each exited fiber as not running. Both are in
  `src/Effect4/Laws/Program/Guard/Core.lean`. So no compiled program reaches a machine where
  the command loop steps an exited fiber (proved: `stepped_live`).
- **F3. The same fact is false at a hand-written interpreter, at two cuts** (reproduced). The
  toy run's second decision has 17 cuts. At two of them a pending command steps fiber 0,
  which has exited.
- **F4. On the failure path a restoring frame's replacement is discarded while the fiber is
  interrupted** (tested: the battery; `popFrom`, `src/Effect4/Machine/Frames.lean`). So one
  pop ends an interrupted child's inner region, its outer region and the fiber. My first
  account of that run was wrong, and the cuts corrected it.
- **F5. The pop's law over two lists asks for no scratch premise.** Both sides drain the same
  pushed frame. The pop's other laws ask for an empty scratch stack.
- **F6. A dropped candidate is false** (tested: a red control). "The step that ends a region is
  the step of the region's end, with its code unchanged" fails on a failure. A skipped handler
  rewrites the carried cause. With the delivered exit as the code, the two steps agree on that
  input. No theorem states that form.
- **F7. The word "cut" has another dictionary meaning** (`docs/core/controlled-english.md`):
  an applicability decision of the semantics registry. The brief, seat LIFT's receipt and
  this slice use it for a state of a run (item 9, P4).
- **F8. The identifier `over` is reserved** in each module that imports
  `src/Effect4/Laws/Auto/Positions.lean` (item 4).

## 8. What the waiting wrapper under a masked caller still owes

This item is written for a reader with no part in this session.

### First: the carrying fact

**What it is.** The shape `above ++ below` is kept along the fiber machine's evaluator arms and
commands while the fiber is inside the region. The bracket takes that shape as a premise at
the later cut. A wrapper's law needs it from the entry: its body is an arbitrary program.

**I did not start it.** I judge it a slice of its own: a second pass over each evaluator arm
and each command, as seat LIFT's part B was. No file of the tree holds a line of it.

**Its statement**, as Lean elaborates it in scratch (tested: an elaboration; no proof). The
filed text holds it: `docs/research/2026-10-06-seat-BRACKET-carry.lean.txt`.

```lean
/-- The evaluation of this fiber ends the region of its own frames `above`: its code is an exit,
and the pop of the own frames that delivers the exit answers nothing. -/
def EndsRegion (f : FrameFiber ν σ β ε δ ι α) (above : List (Prim ν σ β ε δ ι α)) : Prop :=
  match f.current with
  | Prim.success _ => ((f.own above).getCont Arm.contA false).answer = ContAnswer.empty
  | Prim.failure cause =>
    ((f.own above).getCont Arm.contE true (some cause)).answer = ContAnswer.empty
  | _ => False

/-- What one evaluation leaves of a region. -/
def IterKeepsUnder (f : RunFiber ν σ β ε δ ι α χ) (it : Iter ν σ β ε δ ι α χ St) : Prop :=
  ∀ above below, f.frame.stack = above ++ below →
    (∃ above', it.fiber.frame.stack = above' ++ below) ∨ EndsRegion f.frame above

/-- The fiber `id` is inside a region over `below`. -/
def Inside (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId)
    (below : List (Prim ν σ β ε δ ι α)) : Prop :=
  ∀ f ∈ m.fibers, f.id = id → f.exit = none → ∃ above, f.frame.stack = above ++ below

def EvaluatorKeepsUnder (interp : RunInterp ν σ β ε δ ι α χ St) : Prop :=
  ∀ (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool),
    IterKeepsUnder f (evaluator.evaluate interp m f y)

theorem driveStep_keepsUnder (interp : RunInterp ν σ β ε δ ι α χ St)
    (evaluates : EvaluatorKeepsUnder interp) (m : RunMachine ν σ β ε δ ι α χ St)
    (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α)) (id : FiberId)
    (below : List (Prim ν σ β ε δ ι α)) (allocated : id.value < m.nextId)
    (exited : ∀ id', c = Cmd.exitDone id' → ∀ f, m.fiber? id' = some f → f.exit.isSome = true)
    (inside : Inside m id below) :
    Inside (driveStep interp m c rest).1 id below ∨
      (Steps id c ∧ ∃ f above, m.fiber? id = some f ∧ f.frame.stack = above ++ below ∧
        EndsRegion (runloopTop f).frame above)
```

Three points of its form.

1. **It is an until statement.** After one command the fiber is still inside, or the command
   ended the region. The lift's world order (`src/Effect4/Laws/Machine/Lift.lean`) carries an
   invariant, and it does not carry this form as it stands. The command loop, each fold and
   each decision owe an induction of their own.
2. **It has seat LIFT's two premises.** The evaluator's premise has the form of
   `EvaluatorKeepsMask`. The premise on `Cmd.exitDone` is the chain's pending condition, and
   `clearsExited_of_guard` gives it at a compiled cut.
3. **The loop's top stands in the end.** `Cmd.loop` turns a deferred interrupt into a failure
   before it evaluates. So the end reads `runloopTop f`.

**A finite probe finds no counterexample** (tested: the filed text's second part). It reads
each pair of consecutive cuts, each live fiber and each split of its stack.

| Run | Inputs | The frames stay | The command ends the region | Neither |
| --- | --- | --- | --- | --- |
| `nested` | 73 | 63 | 10 | 0 |
| `interrupted` | 141 | 130 | 11 | 0 |
| `formUnderMask` | 41 | 35 | 6 | 0 |
| the toy run, its first decision | 76 | 75 | 1 | 0 |
| the toy run, its second decision | 39 | 36 | 3 | 0 |
| `s3`, `s6` and `s7Regions` of `Test/Program/MaskContract.lean` | 333, 209 and 362 | 317, 191 and 317 | 16, 18 and 45 | 0 |

**The arms that it must cross** (by reading `src/Effect4/Machine/Fibers.lean` and
`src/Effect4/Program/Compile.lean`).

| Group | Arms | What each does to a stack |
| --- | --- | --- |
| `evaluatePrim`, its own arms | `yieldNowWith`; `async` with an answer, with a finalizer, with none; a refused park; a race's registration; `awaitAll`; a join at an unknown, an exited and a live target; `sync` with and without a state | nothing, or a push of `asyncFinalizer` |
| `evaluatePrim.withFiber` | the 24 actions of `WithFiberAction`, and `setInterruptible` at both flags | nothing; a push of a restoring frame at three arms; a push of `asyncFinalizer` in a countdown park |
| `evaluatePrim.finalizerOr`, `stepFrame`, `finishFrame` | an exit that meets a finalizer program; a frame step that goes on; a finished frame | a pop through `getCont`; `step_under`; the end |
| `evaluateNative` | `enterScoped`; `exitScoped` with a scoped frame, with a close program and with none; the fall to `evaluatePrim` | nothing; a pop through `getCont` |
| `iteration`, `settle` | the loop's top, the counter, the injected yield; the six outcomes | nothing |
| `driveStep` | the 18 commands of `Cmd` | `registrationDone` pushes `asyncFinalizer` on the race's host; `closeParAwait` pushes an iterator; `exitDone` and `finish` clear an exited fiber; each other command writes no stack outside an evaluation |
| The helpers | `interruptRecord`, `interruptEach`, `linkScope`, `fireObserver` at its six observers, `exitFiber` at its two clauses, `countdownPark`, `spawn`, `start`, `launchEntrant`, `forkFinalizers`, `drainOwed`, `postTask` | nothing; a push of `asyncFinalizer` in `countdownPark`; a new fiber over an empty stack; the clearing of a published fiber |
| Outside the command loop | the edits of a decision (the fields of `Lift.DecisionLift`); `fireState`, `flushAllState`, `advanceState`, `flushRootState`, `stepDecisionState`, `replayEval`; each entry that returns a machine | nothing; each owes the until form's induction |

**My estimate.** One seat and one slice. Seat LIFT's part B crosses the same arms, and it is
1789 lines of `src/Effect4/Laws/Machine/MaskRuns.lean`, with its docstrings (one `awk`
command). The pop's steps are landed here: `getCont_under_answered` and `step_under`. A second
pass costs the same order again.

**A proposal for its form** (not a ruling). Classify each arm's write to a frame once, as a
relation between two frames. It has five cases: a write of another field, a push, a step
that goes on, a pop with a new code, and an exit. Prove that classification over the
evaluator arms and the commands. The chain's lift and the carrying fact are then two readers
of one theorem, and a third law costs one case analysis.

### How a wrapper reads the bracket

`protectedBy` (`src/Effect4/Modules/Waiting.lean`) binds the acquisition and then installs the
hook. Under a masked caller the form pushes no restoring frame. The wrapper needs the flag
false when the bind's continuation starts.

1. The entry is the cut at which the acquisition begins. Its stack is the bind's frame over
   the caller's stack, and its flag is false.
2. At each later cut inside, `MaskRuns.above` gives the chain of the own frames at false.
3. At the cut whose pop delivers the acquisition's exit, the pop of the own frames answers
   nothing. `compiled_region_bracket` gives the region's end: the entry's stack, flag false.
4. The pop goes on as the pop of the region's end. The bind's frame has no hook
   (`ensure_of_no_contAll`, `src/Effect4/Machine/Frames.lean`), so it answers at flag false.

Step 2 needs the shape at each cut, which is the carrying fact. Step 3 needs the cut itself:
the wrapper owes an invariant that places its fiber in its own code.

### What else the wrapper owes

- **A cut across a wait.** A wait parks the fiber, and its region then spans decisions.
  `LoopCut.task` gives a cut at a dispatcher task whose keys are reserved. The guard's fold
  lift holds those premises (`src/Effect4/Laws/Program/Guard/OuterDriver.lean`), and no
  statement of this slice exports them along a `fire`.
- **The client premise.** Nothing is acquired or registered before the body begins (decisions
  rows 227 and 244 to 246). The bracket does not discharge it.
- **Its delivery, its cleanup and its budget.** They are other claims, and this slice gives
  none.

### The commands that reproduce the battery and its red controls

Run each from the worktree. `SLOT` is the Lean slot of item 4, and no `lake` runs without it.

```sh
# The battery: it exits 0 and prints nothing.
SLOT lake env lean -M6144 -DwarningAsError=true Test/Machine/MaskBracket.lean

# The same through Lake, with the two law modules:
SLOT lake build Effect4.Laws.Machine.MaskBracket Effect4.Laws.Program.MaskBracket \
  Test.Machine.MaskBracket
```

The red controls are fixtures of the battery, so the first command runs them.

| Red control | What it shows |
| --- | --- |
| `handled`, with its four guards | the end is no cut between two steps: the stacks have lengths 1, 2 and 0 |
| `answering`, with its four guards, and `ends_needs_unanswered` (proved) | a pop that an own frame answers ends no region |
| `above_at_entry_not_base` (proved), with two guards | the own frames hold the chain at the entry flag, and not at the fiber's base |
| `above_needs_one_base` (proved) | the chain's split needs one base |
| `skipping`, with its four guards | the ending step with its code unchanged is another step |
| `flag_needs_stack` (proved), with four guards | a pair of cuts with two stacks has two flags |
| `bracket_needs_live` (proved), with one guard | a fiber that has exited at the second cut has the entry's stack and another flag |
| the toy run, with its seven guards | at two cuts a pending command steps an exited fiber: `stepped_live` is false at a hand-written interpreter |
| the decision cut of `nested` | a journal's rows show no fiber inside the region |

A second check asks that no check of the battery is empty. The filed script
`docs/research/2026-10-06-seat-BRACKET-falsify.py.txt` changes each check so that it must fail.
Copy it to a scratch folder `OUT` as `falsify.py`, then run:

```sh
python3 OUT/falsify.py write Test/Machine/MaskBracket.lean OUT
SLOT lake env lean -M6144 -DwarningAsError=true -DmaxErrors=1000 OUT/battery-red.lean \
  > OUT/battery-red.log 2>&1
python3 OUT/falsify.py compare OUT
```

The second command exits 1, and the third exits 0 (tested at `473c85f1`). The third prints the
counts: 96 errors, and no error outside a changed check. Red are 65 of 65 guards, 16 of 16
pinned outputs and 14 of 14 changed proved controls. The battery holds 15 proved items. The
one that the copy leaves is `atNat`, the general form at the alphabets `Nat`. Three examples
read it.

## 9. The text of the semantics registry, and the proposals

### What the main line holds

I read the coordinator's checkout at `e4f25c5a`, and I wrote nothing there. No claim of this
slice is entered. Three sentences there are stale at the merge.

- **S1, R11's open part "the bracket of a region"** (`tools/Tools/SemanticsRegistry.lean`).
  It ends "no goal states the bracket". The bracket is a theorem now.
- **S2, the required property of `saved-mask-chain-runs`** (`docs/core/semantics.md`). It
  reads "Two facts of the bracket stay open: a body's run returns to the entry's stack, and
  the fiber is live at both cuts."
- **S3, decisions row 278, point 1.** It reads "No compiled program reaches it, by the seat's
  reading; nothing proves that."

### The proposed claims

```lean
{ id := "saved-mask-region-bracket", concept := "scope-lifetime-finalization", role := .preservation
  title := "A region of a compiled program ends at its entry's stack and at its entry flag, for an arbitrary body: at two cuts of one command loop's run where a pending command steps the fiber, the later cut's stack shape above ++ below is a premise, and it is the region's only mark on the machine; the theorem then gives the entry's stack and the entry flag at the region's end, which is the fiber that the pop of the own frames leaves where no own frame answers, and the pop goes on from it; it does not give that a body's run keeps that shape (the run-level half of saved-mask-restoration; no premise on an exit, by stepped-fiber-live; no cleanup, no release count, no delivery, no budget, no liveness; nothing of a region whose fiber exits inside it; the client premise of the mask's derived form stays: nothing acquired or registered before the body begins, decisions rows 227, 244 to 246)"
  pointer := .witness `Effect4.Program.compiled_region_bracket },
{ id := "stepped-fiber-live", concept := "scope-lifetime-finalization", role := .inversion
  title := "At each cut of a compiled command loop, a fiber that a pending command steps has not exited: the guard's queue gives the fiber of each pending Cmd.loop and Cmd.deliver as running, and the guard's state gives each exited fiber as not running (every program and row table, each machine and pending commands that hold GuardState and GuardQueue; false at a hand-written interpreter; no statement that a fiber is stepped, and nothing of a fiber that no pending command steps)"
  pointer := .witness `Effect4.Program.stepped_live },
```

Both theorems carry `@[semantics "scope-lifetime-finalization" (requirement := R11)]`. The
second claim's concept is the coordinator's to choose: `reactive-scheduling` fits a law of the
command loop too, and the tag then changes with it.

### The replacements (proposals)

- **For S1**, in R11's open parts, in place of the bracket's line:

  > the carrying fact of a region (scope-lifetime-finalization, serving
  > saved-mask-region-bracket): the stack shape above ++ below is kept along the fiber
  > machine's evaluator arms and commands while the fiber is inside the region, until the
  > command that ends it; the bracket takes the shape as a premise at the later cut; its
  > statement elaborates and a finite probe on eight runs finds no counterexample
  > (docs/research/2026-10-06-seat-BRACKET-carry.lean.txt); the frame machine's own step keeps
  > the shape (step_under); no goal states it

- **For S2**, after "It states no bracket of a region.":

  > The bracket is `saved-mask-region-bracket`.

  and a new property after it:

  > - **A region ends at its entry's stack and at its entry flag
  >   (`saved-mask-region-bracket`)**: A region is no syntax of the machine. Its entry is a
  >   cut of a run, and a later cut is inside it where the fiber's stack is own frames over
  >   the entry's stack. The later cut's stack shape `above ++ below` is a premise, and it is
  >   the region's only mark on the machine. The theorem then gives the entry's stack and the
  >   entry flag at the region's end. It does not give that a body's run keeps that shape. The
  >   end is inside a pop: the fiber that the pop of the own frames leaves, where no own frame
  >   answers. At a compiled command loop a fiber that a pending command steps has not exited
  >   (`stepped-fiber-live`), so the statement takes no premise on an exit.
  >   (`compiled_region_bracket`, `stepped_live`
  >   (`src/Effect4/Laws/Program/MaskBracket.lean`); the general form is
  >   `saved_mask_region_bracket` (`src/Effect4/Laws/Machine/MaskBracket.lean`)).

- **For S3**, in row 278, point 1, for "No compiled program reaches it, by the seat's reading;
  nothing proves that.":

  > No compiled program reaches it: at each cut of a compiled command loop, a fiber that a
  > pending command steps has not exited (`stepped_live`, seat BRACKET).

### The proposals that stay

- **P1. The default modules.** Add `Effect4.Laws.Machine.MaskBracket` and
  `Effect4.Laws.Program.MaskBracket` to the `defaultModules` of
  `scope-lifetime-finalization`. The 15 projections then inherit the concept.
- **P2. The documents.** A row of `docs/ARCHITECTURE.md` for each of the two modules. The role
  register needs no row: the areas `src/Effect4/Laws/Machine` and `src/Effect4/Laws/Program`
  hold them.
- **P3. Two equations may move to `src/Effect4/Machine/Frames.lean`**, beside
  `popFrom_pass_no_push`: `popFrom_append_answered` and `popFrom_append_unanswered`. They are
  general equations of the frames, with no word of the chain. The move edits a file of the
  machine, so it is the coordinator's.
- **P4. A dictionary entry** (`docs/core/controlled-english.md`): "cut of a run", a state of
  one fiber on a run. Its qualifier is "of a run" or "of the command loop", at its first use.
  The entry "cut" is the semantics registry's applicability decision.
- **P5. The next slice** is the carrying fact, in item 8's form. Its consumer is the waiting
  wrapper under a masked caller.
- **P6. The invariant's range.** With `stepped_live`, row 278's point 4 has a second answer for
  compiled programs: no command steps an exited fiber there. The invariant over every fiber is
  still false at a hand-written interpreter. I propose no change.

## 10. The requirements R1 to R13

The slice advances R11 alone. R11 gains three placed nodes, each proved:
`saved_mask_region_bracket`, `compiled_region_bracket` and `stepped_live`. One of its eight
open parts becomes a claim: the bracket of a region. One new open part takes its place, the
carrying fact. So R11 stays open, and its count stays eight if the coordinator enters item 9's
text. Seven more open parts are untouched. They are release at most once, the close order,
the state at a frontier and the open scope of a finished run. They are the pool's two claims,
Semaphore's protected permit and the waiting request's obligation too. The goals
`cleans_once`, `cleanup_keeps` and `releases_once` stay goals. The slice's theorems rest on
no planned goal. R10 and R12 gain no theorem. The waiting wrapper, the protected permit and
Pool's `use` are consumers after the carrying fact. The slice states no delivery, no budget
and no liveness. R1 to R9 and R13 have no relation to the slice. It types nothing, and
it changes no language signature, no data, no world, no service and no host law. It states no
agreement with a target. The report as committed at the head counts the open parts of each
requirement. For R1 to R13 in order, the counts are 4, 5, 6, 6, 2, 7, 4, 6, 1, 13, 8, 9 and 4.
One `awk` command counts the lines that open with "- Open:". The report is not regenerated
here.

## 11. Open obligations

None of the brief's table. No planned goal of the slice is open. Item 8 lists what the next
slice owes: the carrying fact first. Item 9 holds two claims, three replacements and six
proposals, and no one has ruled them.

## 12. Proposed decisions rows (proposals only)

| Topic | Proposal |
| --- | --- |
| The bracket of a region | A region is read by its stack alone: its entry is a cut of a run, and a later cut is inside it where the stack is own frames over the entry's stack. The region's end is the fiber that the pop of the own frames leaves where no own frame answers. It has the entry's stack and the entry flag. The shape at the later cut is a premise, and the carrying fact is the next slice |
| A stepped fiber of a compiled program is live | At each cut of a compiled command loop, a fiber that a pending command steps has not exited (`stepped_live`). It replaces the reading of row 278, point 1 |
