import Effect4.Laws.Program.SourceOpportunityMachine
import Effect4.Laws.Machine.Handshake
import Effect4.Laws.Machine.WriterWeights

/-!
Concept: scope-lifetime-finalization R11.
Consumer: actual native evaluator closure for application source-use bounds.
The debit excludes the acting stored row until the returned fiber is installed.
It measures the existing machine, frame and trace fields only.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- The actual evaluator spends only its acting frame's source reservation.
Consumer: command settlement and the source-use history invariant. -/
def Debit (root : NativeEff) (q : List Nat) (m : NativeMachine) (fiber : SourceFiber)
    (next : SourceIteration) : Prop :=
  recorded q next.machine + outside root q fiber.id next.machine + frame root q next.fiber.frame ≤
    recorded q m + outside root q fiber.id m + frame root q fiber.frame

/-- Replacing active code leaves saved source reservations intact.
Consumer: administrative native actions and answered primitive commands. -/
theorem replace_current_debit (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (code : NCode)
    (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann)
    (carried : current root q code ≤ current root q fiber.frame.current) :
    Debit root q m fiber
      ⟨m, {fiber with frame := {fiber.frame with current := code}}, yielding, outcome, [], []⟩ := by
  unfold Debit frame
  dsimp only
  omega

/-- Diagnostic events leave the stored source reservation unchanged.
Consumer: native observer and interruption actions. -/
theorem outside_emit (root : NativeEff) (q : List Nat) (owner : FiberId)
    (m : NativeMachine) (events) : outside root q owner (m.emit events) = outside root q owner m := rfl

/-- A shared keyed replacement decreases the off-owner source reservation.
Consumer: native observer metadata and interruption actions. -/
theorem outside_update_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner : FiberId) (old next : SourceFiber) (same : next.id = old.id)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (member : old ∈ m.fibers)
    (carried : frame root q next.frame ≤ frame root q old.frame) :
    outside root q owner (m.update next) ≤ outside root q owner m :=
  FiberSum.outside_update_le (fun fiber => frame root q fiber.frame) m owner old next unique
    (fiber_lookup_of_mem_nodup m unique old member) same carried

/-- A metadata-only fiber edit retains the off-owner source reservation.
Consumer: countdown observers, child tracking and scope links. -/
theorem outside_modify_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner target : FiberId) (edit : SourceFiber → SourceFiber)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup)
    (same : ∀ fiber, (edit fiber).id = fiber.id)
    (carried : ∀ fiber, frame root q (edit fiber).frame ≤ frame root q fiber.frame) :
    outside root q owner (m.modify target edit) ≤ outside root q owner m := by
  unfold RunMachine.modify
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    exact outside_update_le root q m owner fiber (edit fiber) (same fiber) unique
      (List.mem_of_find?_eq_some found) (carried fiber)

/-- Mask restoration frames carry no source opportunity.
Consumer: actual native masking and interruptibility reads. -/
theorem mask_debit (root : NativeEff) (q : List Nat)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (body : NCode) (flag : Bool)
    (carried : current root q body ≤ current root q fiber.frame.current) :
    Debit root q m fiber
      (evaluatePrim.withFiber interp m fiber yielding (.setInterruptible body flag)) := by
  dsimp only [current] at carried
  cases flag
  all_goals
    unfold Debit
    simp only [evaluatePrim.withFiber, FrameFiber.uninterruptible,
      FrameFiber.interruptibleRegion, FrameFiber.setFiberInterruptible]
  all_goals repeat' split
  all_goals
    simp only [frame, List.map_cons, List.sum_cons, Option.getD_none, Option.getD_some,
      current, cata_prim, saved, Nat.zero_add]
  all_goals omega

/-- A fresh child's source reservation appears once outside the acting row.
Consumer: the actual fork evaluator debit. -/
theorem spawn_outside_le (root : NativeEff) (q : List Nat)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (m : NativeMachine) (fiber : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) :
    outside root q fiber.id (spawn interp m fiber program options site).1 ≤
      outside root q fiber.id m + current root q program := by
  unfold spawn outside
  simp only [RunMachine.emit, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  unfold ControlWeights.omitted
  simp only [frame, RunFiber.make, FrameFiber.start, List.map_nil, List.sum_nil, Nat.add_zero]
  split <;> omega

/-- A native fork transfers its source reservation into the actual child.
Consumer: fork, forkIn and forkScoped cases of complete native evaluation. -/
theorem fork_debit (root : NativeEff) (q : List Nat)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat)
    (carried : current root q program ≤ current root q fiber.frame.current) :
    Debit root q m fiber (evaluatePrim.withFiber interp m fiber yielding (.fork program options site)) := by
  dsimp only [current] at carried
  cases options with
  | mk daemon immediate mode =>
    cases daemon <;> cases immediate
    all_goals by_cases same : (⟨m.nextId⟩ : FiberId) = fiber.id
    all_goals
      unfold Debit outside recorded frame
      dsimp only [evaluatePrim.withFiber, spawn, start, RunMachine.emit, RunMachine.arm,
        RunFiber.make, FrameFiber.start, current, cata_prim]
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, if_true,
        List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, ControlWeights.omitted, same,
        FrameFiber.start, runEvent, Nat.add_zero, Nat.zero_add]
      omega

/-- Scope linking adds no reservation beyond the actual forked program.
Consumer: the scoped-fork evaluator case. -/
theorem fork_in_debit (root : NativeEff) (q : List Nat)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (program : NCode)
    (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat)
    (carried : current root q program ≤ current root q fiber.frame.current) :
    Debit root q m fiber
      (evaluatePrim.withFiber interp m fiber yielding (.forkIn program options scope site)) := by
  have previous := fork_debit root q interp m fiber yielding program {options with daemon := true} site carried
  exact previous

/-- An ambient-scope fork either transfers into its child or discards active code on refusal.
Consumer: actual Workers forkScoped evaluation. -/
theorem fork_scoped_debit (root : NativeEff) (q : List Nat)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat)
    (carried : current root q program ≤ current root q fiber.frame.current) :
    Debit root q m fiber
      (evaluatePrim.withFiber interp m fiber yielding (.forkScoped program options site)) := by
  cases found : interp.ambientScope fiber.context with
  | some scope =>
    simpa only [evaluatePrim.withFiber, found] using
      fork_in_debit root q interp m fiber yielding program options scope site carried
  | none =>
    simp only [evaluatePrim.withFiber, found]
    exact replace_current_debit root q m fiber yielding (.failure (.die interp.missingScope))
      .continue_ (Nat.zero_le _)

/-- Applying an interruption discards active opportunities and preserves saved frames.
Consumer: actual interrupt and scope-link actions. -/
theorem interrupt_record_le (root : NativeEff) (q : List Nat) (table : RowTable)
    (completed : List (FiberId × ExitV)) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (fiber : SourceFiber) :
    frame root q (interruptRecord (interpAt root completed table) who extra fiber).1.frame ≤
      frame root q fiber.frame := by
  exact Machine.WriterWeights.interrupt_weight_le (weightModel root q) _ fiber

/-- Addressed messages cannot increase the source reservations outside a named owner.
Consumer: eager countdown and scope-link adapters; settlement uses the shared total bound. -/
theorem outside_edits_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner : FiberId) (edits : List (FiberEdit Err Defect FiberId Ann))
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    outside root q owner (applyFiberEdits edits m).1 ≤ outside root q owner m := by
  apply (FiberSum.fiberEdits_le (ControlWeights.omitted (fun fiber : SourceFiber => fiber.id)
    (fun fiber : SourceFiber => frame root q fiber.frame) owner) (fun _ _ => rfl) ?_ edits m unique).2
  intro cause fiber
  have same := (interruptWithCause_maskLater cause fiber).1
  dsimp only [ControlWeights.omitted]
  simp only [same]
  split
  · exact Nat.le_refl _
  · exact Machine.WriterWeights.interrupt_weight_le (weightModel root q) cause fiber

/-- The countdown plan adds only a zero-weight cleanup and diagnostic event.
Consumer: native countdown evaluation before addressed observers are installed. -/
theorem countdown_plan_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool) (shape : ResumeAt root resume) :
    let out := countdownParkEdits (interpAt root m.completedExits table) m fiber targets resume failFast
    Debit root q m fiber ⟨out.1, out.2.1, yielding, .continue_, [], out.2.2.2⟩ := by
  have zero (exits : List ExitV) : current root q
      (countdownPark.resumePrim (interpAt root m.completedExits table) resume exits) = 0 := by
    cases resume
    case continueWith => exact shape.elim
    all_goals rfl
  unfold countdownParkEdits
  dsimp only
  split
  · unfold Debit frame
    simp only [zero, Nat.zero_add]
    change recorded q m + outside root q fiber.id m + _ ≤ recorded q m + outside root q fiber.id m + _
    omega
  · have cancelZero : name q ((interpAt root m.completedExits table).cancelName
        (interpAt root m.completedExits table).parkCancelName fiber.id m.nextToken) = 0 := rfl
    unfold Debit
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      runEvent, Nat.add_zero, outside_emit, frame, RunFiber.park, saved, cancelZero, Nat.zero_add]
    exact Nat.le_refl _

/-- Native countdown callbacks retain the existing saved source budget.
Consumer: awaitAll and awaitNewChildren native evaluator clauses. -/
theorem countdown_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (shape : ResumeAt root resume) :
    let out := countdownPark (interpAt root m.completedExits table) m fiber targets resume failFast
    Debit root q m fiber ⟨out.1, out.2.1, yielding, .continue_, [], []⟩ := by
  let out := countdownParkEdits (interpAt root m.completedExits table) m fiber targets resume failFast
  have debit := countdown_plan_debit root q table m fiber yielding targets resume failFast shape
  have sameFibers : out.1.fibers = m.fibers := by
    rw [Edits.countdown_word]
    exact Edits.run_keeps _ _ (fun edit member => edit.keeps_fibers
      (Edits.countdown_misses m fiber targets edit member)) m
  have off := outside_edits_le root q out.1 fiber.id out.2.2.2 (by rw [sameFibers]; exact unique)
  have trace := congrArg RunMachine.trace (RunMachine.applyFiberEdits_shape out.2.2.2 out.1).1
  unfold countdownPark Debit
  change recorded q (applyFiberEdits out.2.2.2 out.1).1 +
    outside root q fiber.id (applyFiberEdits out.2.2.2 out.1).1 + frame root q out.2.1.frame ≤ _
  have count : recorded q (applyFiberEdits out.2.2.2 out.1).1 = recorded q out.1 := by
    unfold recorded
    rw [trace]
  rw [count]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left off _) _) debit

/-- Native interruption metadata changes only discard an off-owner active reservation.
Consumer: actual interruptAs evaluation and scope links. -/
theorem interrupt_as_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (target who : FiberId)
    (_unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    Debit root q m fiber
      (evaluatePrim.interruptAs (interpAt root m.completedExits table) m fiber yielding target who) := by
  unfold evaluatePrim.interruptAs
  split
  · exact Nat.le_refl _
  · unfold Debit
    simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      runEvent, Nat.add_zero, outside_emit]
    exact Nat.le_refl _

/-- Closing a source-owned scope introduces only finalizer code outside the selected query.
Consumer: actual closeScope evaluation in the source-use invariant. -/
theorem close_scope_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (scope : Nat) (exit : ExitV)
    (clear : ClearFinalizers root q) (owned : ScopesAt root m.state.scopes) :
    Debit root q m fiber
      (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding (.closeScope scope exit)) := by
  cases step : storesCloseScope scope exit fiber.frame.interruptible m.state with
  | none =>
    have close : (interpAt root m.completedExits table).closeScope scope exit fiber.frame.interruptible fiber.id m.state = none := by
      change (storesCloseScope scope exit fiber.frame.interruptible m.state).map
        (fun result => (result.1, result.2.map embed)) = _
      rw [step]
      rfl
    simp only [evaluatePrim.withFiber, close]
    exact Nat.le_refl _
  | some next =>
    obtain ⟨state, program⟩ := next
    have close : (interpAt root m.completedExits table).closeScope scope exit fiber.frame.interruptible fiber.id m.state =
        some (state, program.map embed) := by
      change (storesCloseScope scope exit fiber.frame.interruptible m.state).map
        (fun result => (result.1, result.2.map embed)) = _
      rw [step]
      rfl
    have zero : ∀ code, program = some code → current root q (embed code) = 0 := by
      intro code same
      unfold storesCloseScope at step
      cases snapshot : scopeCloseSnapshot scope exit m.state with
      | none => rw [snapshot] at step; cases step
      | some result =>
        obtain ⟨after, strategy, order⟩ := result
        have slots := close_snapshot_at root scope exit m.state after strategy order owned snapshot
        simp only [snapshot, Option.pure_def] at step
        cases order with
        | nil => cases step; cases same
        | cons first rest =>
          cases rest with
          | nil =>
            cases step
            cases same
            have finZero := fin_program_zero root q clear first exit (slots.2.1 first (.head _))
            simpa only [embed, current, cata_prim, name, push, Nat.add_zero] using finZero
          | cons second tail =>
            cases step
            cases same
            change thunk root q (.store (.body (.closeWalk strategy (first :: second :: tail) exit))) = 0
            rfl
    cases program with
    | none =>
      simp only [evaluatePrim.withFiber, close, Option.map_none]
      unfold Debit frame
      dsimp only
      change recorded q m + outside root q fiber.id m + _ ≤ recorded q m + outside root q fiber.id m + _
      simp only [current, cata_prim]
      omega
    | some program =>
      have closing := zero program rfl
      simp only [evaluatePrim.withFiber, close, Option.map_some]
      unfold Debit frame
      dsimp only
      change recorded q m + outside root q fiber.id m + _ ≤ recorded q m + outside root q fiber.id m + _
      rw [closing]
      unfold FrameFiber.uninterruptible
      split
      all_goals simp only [List.map_cons, List.sum_cons, saved, Nat.zero_add]
      all_goals omega

/-- An actual interpreted fork spends the suspension reservation which produced it.
Consumer: actual Workers and Atomic history readers. -/
theorem interpreted_fork_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (suspended : EffThunk)
    (program : NCode) (options : Supervision.ForkOptions) (site : List Nat)
    (clear : ClearFinalizers root q) (held : FrameAt root fiber.frame)
    (selected : fiber.frame.current = .withFiber suspended)
    (found : (interpAt root m.completedExits table).withFiberOf suspended = some (.fork program options site)) :
    Debit root q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding (.fork program options site)) := by
  have owned := held.1
  rw [selected] at owned
  have carried := interp_action_le root q clear m.completedExits table suspended _ owned found
  apply fork_debit
  simpa only [selected, current, cata_prim, action] using carried

/-- An actual interpreted scoped fork spends its producing source suspension.
Consumer: the unchanged all-job-count Workers history. -/
theorem interpreted_fork_in_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (suspended : EffThunk)
    (program : NCode) (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat)
    (clear : ClearFinalizers root q) (held : FrameAt root fiber.frame)
    (selected : fiber.frame.current = .withFiber suspended)
    (found : (interpAt root m.completedExits table).withFiberOf suspended = some (.forkIn program options scope site)) :
    Debit root q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding (.forkIn program options scope site)) := by
  have owned := held.1
  rw [selected] at owned
  have carried := interp_action_le root q clear m.completedExits table suspended _ owned found
  apply fork_in_debit
  simpa only [selected, current, cata_prim, action] using carried

/-- The scope-link plan retains the source reservation and contributes no counted event.
Consumer: runIn evaluation and the eager scope-link debit. -/
theorem link_plan_debit (root : NativeEff) (q : List Nat) (table : RowTable) (m : NativeMachine)
    (owner target : FiberId) (scope : Nat) (mode : Supervision.ScopeMode)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    let out := linkScopeEdits (interpAt root m.completedExits table) m mode scope target who extra
    outside root q owner out.1 = outside root q owner m ∧ recorded q out.1 = recorded q m := by
  unfold linkScopeEdits
  repeat' split
  all_goals simp only [recorded_emit, outside_emit, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, runEvent, Nat.add_zero]
  all_goals aesop

/-- Scope links edit only observer metadata or discard an interrupted active program.
Consumer: actual runIn and fork link command accounting. -/
theorem link_debit (root : NativeEff) (q : List Nat) (table : RowTable) (m : NativeMachine)
    (owner target : FiberId) (scope : Nat) (mode : Supervision.ScopeMode)
    (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    let out := linkScope (interpAt root m.completedExits table) m mode scope target who extra
    outside root q owner out.1 ≤ outside root q owner m ∧ recorded q out.1 = recorded q m := by
  let interp := interpAt root m.completedExits table
  let plan := linkScopeEdits interp m mode scope target who extra
  have kept := link_plan_debit root q table m owner target scope mode who extra
  have sameFibers : plan.1.fibers = m.fibers := by
    rw [Edits.link_plan_word]
    exact Edits.run_keeps _ _ (fun edit member => edit.keeps_fibers
      (Edits.link_misses interp m mode scope target who edit member)) m
  have off := outside_edits_le root q plan.1 owner plan.2 (by rw [sameFibers]; exact unique)
  refine ⟨?_, ?_⟩
  · exact kept.1 ▸ off
  · change recorded q (applyFiberEdits plan.2 plan.1).1 = recorded q m
    have trace := congrArg RunMachine.trace (RunMachine.applyFiberEdits_shape plan.2 plan.1).1
    unfold recorded
    rw [trace]
    exact kept.2

/-- Removing observer rows leaves source reservations unchanged.
Consumer: cancellation cleanup action accounting. -/
theorem drop_outside (root : NativeEff) (q : List Nat) (m : NativeMachine) (owner : FiberId) (token : Nat) :
    outside root q owner {m with fibers := m.fibers.map fun g =>
      {g with observers := g.observers.filter fun
        | .resumeAwait _ t _ => t ≠ token
        | .countdown _ t => t ≠ token
        | _ => true}} = outside root q owner m := by
  unfold outside
  rw [List.map_map]
  rfl

/-- Every native action spends only the source reservation of its actual producer.
The application helper excludes source races and parallel scopes explicitly.
Consumer: complete native evaluator and unchanged Workers/Atomic history bounds. -/
theorem native_action_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (selected : NAction)
    (source : ActionAt root selected) (sequential : SequentialSource root)
    (raceFree : RaceFreeSource root) (clear : ClearFinalizers root q)
    (scopes : ScopesAt root m.state.scopes)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup)
    (carried : action root q selected ≤ current root q fiber.frame.current) :
    Debit root q m fiber (evaluatePrim.withFiber (interpAt root m.completedExits table) m fiber yielding selected) := by
  cases selected
  case fork program options site => exact fork_debit root q _ m fiber yielding program options site carried
  case forkIn program options scope site => exact fork_in_debit root q _ m fiber yielding program options scope site carried
  case forkScoped program options site => exact fork_scoped_debit root q _ m fiber yielding program options site carried
  case setInterruptible program flag => exact mask_debit root q _ m fiber yielding program flag carried
  case raceAll | raceAllFirst => exact False.elim (RaceFreeSource.not_race raceFree source.2)
  case closePar => exact False.elim (SequentialSource.not_parallel sequential source.2)
  case closeScope scope exit => exact close_scope_debit root q table m fiber yielding scope exit clear scopes
  case interruptAs target who => exact interrupt_as_debit root q table m fiber yielding target who unique
  case awaitAll targets => exact countdown_plan_debit root q table m fiber yielding targets .exitsValue false trivial
  case awaitAllFailFast targets => exact countdown_plan_debit root q table m fiber yielding targets .exitsValue true trivial
  case awaitNewChildren snapshot => exact countdown_plan_debit root q table m fiber yielding _ .void false trivial
  case runIn target scope =>
    have linked := link_plan_debit root q table m fiber.id target scope .fiberRunIn (some target) ReasonAnnotations.empty
    unfold Debit
    dsimp only [evaluatePrim.withFiber]
    rw [linked.2]
    simp only [frame, current, cata_prim, Nat.zero_add]
    exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_of_eq linked.1) _) _) (by omega)
  case dropObservers token =>
    unfold Debit
    dsimp only [evaluatePrim.withFiber]
    simp only [frame, current, cata_prim, Nat.zero_add]
    omega
  case interrupt target =>
    have zero : current root q ((interpAt root m.completedExits table).interruptAsCode target fiber.id) = 0 := rfl
    simp only [evaluatePrim.withFiber]
    apply replace_current_debit (yielding := yielding) (outcome := .continue_)
    rw [zero]
    exact Nat.zero_le _
  case interruptScoped target =>
    have zero : current root q ((interpAt root m.completedExits table).interruptCode target) = 0 := rfl
    simp only [evaluatePrim.withFiber]
    split
    · exact replace_current_debit root q m fiber yielding _ .continue_ (Nat.zero_le _)
    · apply replace_current_debit (yielding := yielding) (outcome := .continue_)
      rw [zero]
      exact Nat.zero_le _
  case setContext context =>
    unfold Debit
    dsimp only [evaluatePrim.withFiber]
    rw [recorded_emit]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, runEvent, Nat.add_zero,
      outside_emit, frame, current, cata_prim, Nat.zero_add]
    omega
  all_goals
    unfold Debit
    simp only [evaluatePrim.withFiber, FrameFiber.uninterruptible]
  all_goals repeat' split
  all_goals
    simp only [frame, current, cata_prim, saved, List.map_cons, List.sum_cons, Nat.zero_add]
  all_goals omega

end Effect4.Program.SourceScope.Opportunities
