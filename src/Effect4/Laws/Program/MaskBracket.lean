import Effect4.Laws.Machine.MaskBracket
import Effect4.Laws.Program.MaskRuns
import Effect4.Laws.Program.Guard.Decision

/-!
# Laws.Program.MaskBracket — a region of a compiled program ends with its entry flag

`Laws/Machine/MaskBracket.lean` states the bracket of a region in its general form: a region
ends at its entry's stack and at its entry flag, where the fiber is live at both cuts. That
second fact is a premise there. This module gives it at the compiled program's interpreter, and
it states the bracket there with no such premise (`compiled_region_bracket`).

* **A cut of a compiled program's command loop** (`LoopCut`): a machine and its pending
  commands. They hold the guard's invariants (`Guard.GuardState`, `Guard.GuardQueue`,
  `Guard.RegistrationQueue`, `Laws/Program/Guard/Core.lean`), and the machine holds the chain's
  invariant `MaskRuns` at a table of start flags. A cut reads a fiber that a pending command
  steps (`Machine.Steps`).
* **The second fact: at each cut of a compiled command loop, a fiber that a pending command
  steps has not exited** (`stepped_live`). The guard's queue gives each pending `Cmd.loop` and
  `Cmd.deliver` a running fiber, and the guard's state gives each exited fiber as not running.
  So no compiled program reaches the machine where the command loop steps an exited fiber. A
  hand-written interpreter does (`Test/Machine/MaskBracket.lean` holds two such cuts).
* **The cuts of one run** (`LoopCut.step`, `LoopCut.drive`, `LoopCut.evaluate`,
  `LoopCut.task`). Each command and each command loop gives a cut again, at a table that grows
  at its end. The guard's queue gives the chain's command condition, so it is no premise
  (`clearsExited_of_guard`). The loaded machine under its first commands is a cut.
* **The bracket** (`compiled_region_bracket`): two cuts of one run, each with a pending command
  that steps the fiber. The first is the region's entry. At the second the fiber's stack is the
  own frames over the entry's stack. Where the pop of the own frames answers nothing, the
  region ends at the entry's stack and at the entry flag, and the pop goes on from there.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), requirement R11. The
  proposed registry claim is `saved-mask-region-bracket`, the run-level half of
  `saved-mask-restoration`, and its pointer is `compiled_region_bracket`.
  `Machine.saved_mask_region_bracket` is its general form;
- reach: every program and row table, at the native evaluator, at each pair of cuts of a
  command loop that hold `LoopCut` at tables in the prefix order. It asks for no typing and no
  admission. A fiber is live while its `exit` is `none`;
- the later cut's stack shape `above ++ below` is a premise, and it is the region's only mark
  on the machine. The theorem then gives the entry's stack and the entry flag at the region's
  end. It does not give that a body's run keeps that shape: no theorem keeps it along the
  fiber machine's evaluator arms and commands;
- it gives no cleanup, no release count, no delivery, no budget and no liveness. It states
  nothing of a region whose fiber exits inside it. It gives a cut at the start of an
  `evaluate` decision and at a dispatcher task whose keys are reserved: the guard's own lift
  holds the other queues. The client premise of the mask's derived form stays with the client:
  nothing is acquired or registered before the body begins (decisions rows 227 and 244 to
  246). The bracket reads a region from its entry, so it states nothing of the two checkpoints
  of that form before its body;
- consumers: the waiting wrapper under a masked caller, then Semaphore's protected permit and
  Pool's `use`.

The design is `docs/research/2026-10-06-seat-BRACKET-design.md`.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine Effect4.FrameFiber Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue

/-! ## The second fact: a stepped fiber is live -/

/-- **At each cut of a compiled command loop, a fiber that a pending command steps has not
exited** (the proposed registry claim `stepped-fiber-live`; concept
`scope-lifetime-finalization`, requirement R11). The guard's queue gives the fiber of each
pending `Cmd.loop` and `Cmd.deliver` as running and not parked, and the guard's state gives each
exited fiber as not running. It is the second fact of the bracket, and its own source.

So no compiled program reaches a machine where the command loop steps an exited fiber. The
invariant `MaskRuns` ranges over the live fibers for that machine's sake
(`Laws/Machine/MaskRuns.lean`). Decisions row 278, point 1, records this fact as read, not
proved.

Reach: every program and row table, and each machine and pending commands that hold the guard's
state and the guard's queue. `Guard.driveStep_invariants` keeps both along a command loop, and
`Guard.guardState_reachable` gives the state at each reachable machine.

It does not establish that a fiber is stepped, and it gives nothing of a fiber that no pending
command steps. The statement is false at a hand-written interpreter: there the command loop
steps an exited fiber, and `Test/Machine/MaskBracket.lean` holds two such cuts.

Its consumers are `compiled_region_bracket`, and each law that reads a fiber at its own step. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stepped_live (p : NativeEff) (table : RowTable) {m : NativeMachine} {cmds : List NCmd}
    (state : GuardState m) (queue : GuardQueue p table m cmds) {c : NCmd} (pending : c ∈ cmds)
    {id : FiberId} (steps : Steps id c) {f : NFiber} (found : m.fiber? id = some f) :
    f.exit = none := by
  have authority := queue.authority c pending
  have active : ActiveAt m id := by
    cases c with
    | loop fiber y =>
      have same : fiber = id := steps
      rw [← same]
      exact authority
    | deliver fiber y =>
      have same : fiber = id := steps
      rw [← same]
      exact authority
    | _ => exact absurd steps (fun h => h)
  obtain ⟨g, lookup, running, -⟩ := active
  have same : g = f := Option.some.inj (lookup.symm.trans found)
  subst same
  cases live : g.exit with
  | none => rfl
  | some exit =>
    have idle := (state.exited g (List.mem_of_find?_eq_some found) (by rw [live]; rfl)).2
    rw [idle] at running
    cases running

/-! ## The chain's command condition, from the guard -/

/-- Two fibers of a table with one id are one fiber, where the ids are distinct. A step of
`clearsExited_of_guard`. -/
@[semantics "scope-lifetime-finalization"]
private theorem mem_eq_of_ids_nodup :
    ∀ (fibers : List NFiber), (fibers.map RunFiber.id).Nodup →
      ∀ {f g : NFiber}, f ∈ fibers → g ∈ fibers → g.id = f.id → g = f
  | [], _, _, _, mem, _, _ => nomatch mem
  | first :: rest, unique, f, g, memf, memg, same => by
    have split := List.nodup_cons.mp unique
    rcases List.mem_cons.mp memf with rfl | memf'
    · rcases List.mem_cons.mp memg with rfl | memg'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨g, memg', same⟩) split.1
    · rcases List.mem_cons.mp memg with rfl | memg'
      · exact absurd (List.mem_map.mpr ⟨f, memf', same.symm⟩) split.1
      · exact mem_eq_of_ids_nodup rest split.2 memf' memg' same

/-- **The guard's queue meets the chain's pending condition.** Each pending `Cmd.exitDone` names
a fiber that has exited: the guard's queue gives the fiber that a lookup finds, and the ids of
the table are distinct. A step of `LoopCut.pending`. -/
@[semantics "scope-lifetime-finalization"]
theorem clearsExited_of_guard (p : NativeEff) (table : RowTable) {m : NativeMachine}
    {cmds : List NCmd} (state : GuardState m) (queue : GuardQueue p table m cmds) :
    ClearsExited m cmds := by
  intro id pending
  obtain ⟨f, lookup, exited⟩ := queue.authority _ pending
  have mem := List.mem_of_find?_eq_some lookup
  have fid : f.id = id := fiber_id_of_lookup lookup
  refine ⟨by rw [← fid]; exact state.fibersBelow f mem, ?_⟩
  intro g memg same
  rw [mem_eq_of_ids_nodup m.fibers state.fiberIds mem memg (same.trans fid.symm)]
  exact exited

/-- **One command of a compiled program's loop keeps the chain's invariant, under the guard's
queue alone.** The chain's command condition is on `Cmd.exitDone`, and the guard's queue gives
its first alternative: the fiber has exited. A step of `LoopCut.step`. -/
@[semantics "scope-lifetime-finalization"]
theorem guarded_driveStep_maskRuns (p : NativeEff) (table : RowTable) (bases : List Bool)
    (m : NativeMachine) (c : NCmd) (rest : List NCmd)
    (queue : GuardQueue p table m (c :: rest)) (kept : MaskRuns bases m) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases'
      (driveStep (evaluator := evaluatorFor p table) (interpOf p table) m c rest).1 := by
  letI := evaluatorFor p table
  refine driveStep_maskRuns (interpOf p table)
    (fun m f y => evaluateNative_keepsMask p table m f y) bases m c rest kept ?_
  cases c with
  | exitDone id =>
    intro f found
    obtain ⟨g, lookup, exited⟩ := queue.authority _ (List.mem_cons_self ..)
    cases lookup.symm.trans found
    exact Or.inl exited
  | _ => trivial

/-! ## A cut of a compiled program's command loop -/

/-- **A cut of a compiled program's command loop.** The machine and its pending commands hold
the guard's three invariants, and the machine holds the chain's invariant at the table `bases`.
Where a pending command steps a fiber (`Machine.Steps`), the cut reads that fiber. -/
structure LoopCut (p : NativeEff) (table : RowTable) (bases : List Bool) (m : NativeMachine)
    (cmds : List NCmd) : Prop where
  /-- The guard's invariant of the machine. -/
  state : GuardState m
  /-- The guard's invariant of the pending commands. -/
  queue : GuardQueue p table m cmds
  /-- A race's pending work is followed by the command that returns to its host. -/
  registration : RegistrationQueue cmds
  /-- Each live fiber holds the saved mask's chain at its entry of the table. -/
  kept : MaskRuns bases m

/-- At a cut each pending `Cmd.exitDone` names a fiber that has exited: the chain's pending
condition. Its consumer is a proof that runs the chain's lift from a cut. -/
@[semantics "scope-lifetime-finalization"]
theorem LoopCut.pending {p : NativeEff} {table : RowTable} {bases : List Bool}
    {m : NativeMachine} {cmds : List NCmd} (cut : LoopCut p table bases m cmds) :
    ClearsExited m cmds :=
  clearsExited_of_guard p table cut.state cut.queue

/-- **The fiber that a cut reads is live.** It is `stepped_live` at a cut. -/
@[semantics "scope-lifetime-finalization"]
theorem LoopCut.live {p : NativeEff} {table : RowTable} {bases : List Bool} {m : NativeMachine}
    {cmds : List NCmd} (cut : LoopCut p table bases m cmds) {c : NCmd} (pending : c ∈ cmds)
    {id : FiberId} (steps : Steps id c) {f : NFiber} (found : m.fiber? id = some f) :
    f.exit = none :=
  stepped_live p table cut.state cut.queue pending steps found

/-- **One command gives the next cut**, at a table that the first one is a prefix of. The
guard's three invariants are kept by `Guard.driveStep_invariants`, and the chain's invariant by
`guarded_driveStep_maskRuns`. A step of `LoopCut.drive`. -/
@[semantics "scope-lifetime-finalization"]
theorem LoopCut.step {p : NativeEff} {table : RowTable} {bases : List Bool} {m : NativeMachine}
    {c : NCmd} {rest : List NCmd} (cut : LoopCut p table bases m (c :: rest)) :
    ∃ bases', bases <+: bases' ∧ LoopCut p table bases'
      (driveStep (evaluator := evaluatorFor p table) (interpOf p table) m c rest).1
      (driveStep (evaluator := evaluatorFor p table) (interpOf p table) m c rest).2 := by
  obtain ⟨bases', grown, kept'⟩ :=
    guarded_driveStep_maskRuns p table bases m c rest cut.queue cut.kept
  have guarded := driveStep_invariants p table m c rest cut.state cut.queue cut.registration
  exact ⟨bases', grown, guarded.1, guarded.2.1, guarded.2.2, kept'⟩

/-- **The command loop gives a cut at every budget**, at a table that the first one is a prefix
of. So two cuts of one command loop are two cuts of one run: their tables are in the prefix
order. It is `Lift.driveState_lift` at `LoopCut.step`. -/
@[semantics "scope-lifetime-finalization"]
theorem LoopCut.drive {p : NativeEff} {table : RowTable} {bases : List Bool} {m : NativeMachine}
    {cmds : List NCmd} (cut : LoopCut p table bases m cmds) (fuel : Nat) :
    ∃ bases', bases <+: bases' ∧ LoopCut p table bases'
      (driveState (evaluator := evaluatorFor p table) (interpOf p table) fuel m cmds).1
      (driveState (evaluator := evaluatorFor p table) (interpOf p table) fuel m cmds).2 :=
  letI := evaluatorFor p table
  Lift.driveState_lift basesOrder (interpOf p table)
    (fun bases m cmds => LoopCut p table bases m cmds)
    (fun _ _ _ _ _ cut => cut.step) fuel bases m cmds cut

/-- **The start of an `evaluate` decision is a cut**: a machine that holds the guard's state and
the chain's invariant, under the commands `[Cmd.evaluate id, Cmd.drainDue]`. A step of
`LoopCut.load`. -/
@[semantics "scope-lifetime-finalization"]
theorem LoopCut.evaluate (p : NativeEff) (table : RowTable) {bases : List Bool}
    {m : NativeMachine} (state : GuardState m) (kept : MaskRuns bases m) (id : FiberId) :
    LoopCut p table bases m [Cmd.evaluate id, Cmd.drainDue] :=
  ⟨state, LocalDecision.guardQueue_evaluate_drainDue p table m id,
    ⟨True.intro, True.intro, True.intro⟩, kept⟩

/-- **A dispatcher task's commands are a cut**, where the machine reserves the task's keys and the
task's code registers no race (`Guard.OuterDriver.taskCmds_guardQueue`). The guard's own lift
gives both premises along a `fire`, a `flush` and an `advance`. -/
@[semantics "scope-lifetime-finalization"]
theorem LoopCut.task (p : NativeEff) (table : RowTable) {bases : List Bool} {m : NativeMachine}
    (state : GuardState m) (kept : MaskRuns bases m) (task : NTask)
    (reserved : ReservedKeys m (taskKeys task)) (sites : taskRaceSites task = []) :
    LoopCut p table bases m (taskCmds task) :=
  ⟨state, OuterDriver.taskCmds_guardQueue p table m task reserved sites,
    OuterDriver.taskCmds_registration task, kept⟩

/-- **The loaded machine under its first commands is a cut**, at the table of its root. So each
cut of the root's first command loop is a cut, with no premise on the program. -/
@[semantics "scope-lifetime-finalization"]
theorem LoopCut.load (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    LoopCut p table [true] (Api.load p compileFuel answers)
      [Cmd.evaluate Api.root, Cmd.drainDue] :=
  LoopCut.evaluate p table (guardState_load p compileFuel answers)
    (Api.load_maskRuns p compileFuel answers) Api.root

/-! ## The placed theorem -/

/-- **A region of a compiled program ends at its entry's stack and at its entry flag**, for an
arbitrary body (the proposed registry claim `saved-mask-region-bracket`; concept
`scope-lifetime-finalization`, requirement R11). It is the run-level half of
`saved-mask-restoration`, at the compiled program's interpreter `interpOf p table` and under
the native evaluator.

The two cuts are cuts of one command loop's run (`LoopCut`, at tables in the prefix order), and
at each a pending command steps the fiber. The first is the region's entry: its stack is the
entry's stack, and its flag is the entry flag. At the second the fiber is inside the region: its
stack is the own frames `above` over the entry's stack. Where the pop of the own frames answers
nothing, the body's exit has passed each own frame. Then the region's end has the entry's stack
and the entry flag, and the pop of the fiber goes on as the pop of the region's end
(`RegionEnds`).

Its two facts are its steps. The stack at the region's end is the entry's stack
(`FrameFiber.regionEnd_stack`). The fiber is live at both cuts (`stepped_live`), so the
statement takes no premise on an exit. Its general form is
`Machine.saved_mask_region_bracket`, which takes that premise.

Reach: every program, row table, demand, skip flag and carried cause. It asks for no typing and
no admission. A region that changes its flag and a region that changes no flag are one case: the
statement reads the entry's stack and the entry flag alone.

The later cut's stack shape `above ++ below` is a premise, and it is the region's only mark on
the machine. The theorem then gives the entry's stack and the entry flag at the region's end. It
does not give that a body's run keeps that shape.

It gives no cleanup, no release count, no delivery, no budget and no liveness, and nothing of a
region whose fiber exits inside it. The client premise of the mask's derived form stays with the
client: nothing is acquired or registered before the body begins (decisions rows 227 and 244 to
246).

Its consumers are the waiting wrapper under a masked caller, then Semaphore's protected permit
and Pool's `use`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal compiled_region_bracket (p : NativeEff) (table : RowTable) {bases bases' : List Bool}
    {m m' : NativeMachine} {cmds cmds' : List NCmd} (entry : LoopCut p table bases m cmds)
    (later : LoopCut p table bases' m' cmds') (grown : bases <+: bases') {c c' : NCmd}
    (pending : c ∈ cmds) (pending' : c' ∈ cmds') {id : FiberId} (steps : Steps id c)
    (steps' : Steps id c') {f g : NFiber} (found : m.fiber? id = some f)
    (found' : m'.fiber? id = some g) {above : List NCode}
    (inside : g.frame.stack = above ++ f.frame.stack) (demand : Effect4.Arm) (skip : Bool)
    (cause : Option CauseV)
    (unanswered : ((g.frame.own above).getCont demand skip cause).answer = ContAnswer.empty) :
    RegionEnds f.frame g.frame above demand skip cause

end Effect4.Program
