import Test.Dogfood.Scenario.Atomic.Writer
import Effect4.Laws.Program.SourceOpportunities
import Effect4.Laws.Machine.FrameWeights
import Effect4.Laws.Machine.PrimWeights
import Effect4.Laws.Program.FinalizerRun

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: Atomic.Cleanup.log_debits.
The scalar projection reads existing code, names and source addresses.
A dormant finalizer carries no active note reservation.
The native finalizer start supplies that reservation separately.
No source program, runtime state or scenario premise is added.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterPhase
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Effect4.Program.SourceScope

/-- A reservation lies inside the selected running finalizer, before its one note. -/
def below (id : Nat) (path : List Nat) : Nat :=
  if (SourcePaths.requestPath id ++ [1]).isPrefixOf path then
    SourceScope.Opportunities.below (Writer.notePath id) path else 0

/-- The existing native note operation retains one literal-identity reservation. -/
def operation (id : Nat) : SyncOp → Nat
  | .refUpdate _ term env => if term == Store.noteAt id env.length then 1 else 0
  | _ => 0

/-- Existing synthetic program wrappers retain the active note operations they contain.
Consumer: stored callback and action interpretation in the writer history. -/
def program (id : Nat) : ProgName → Nat
  | .syncOp op => operation id op
  | .intoDeferred body _ | .intoBody body _ | .forkThen body _ _ | .forkOnly body _
  | .forkInScope body _ _ | .forkScopedOf body _ | .awaitAllNew body => program id body
  | .onExitOf body _ _ => program id body
  | .seqOf first second => program id first + program id second
  | _ => 0

/-- Stored callback names retain their future existing program slots. -/
def storeName (id : Nat) : Name → Nat
  | .seq next | .snapshotThen next => program id next
  | _ => 0

/-- Stored fork and mask actions retain their existing body programs. -/
def storeAction (id : Nat) : ActionName → Nat
  | .fork body _ | .forkIn body _ _ | .forkScoped body _ | .setInterruptible body _ => program id body
  | _ => 0

/-- A future native callback retains only its active finalizer child.
Dormant finalizer names supply their reservation at the actual start event. -/
def name (id : Nat) : EffName → Nat
  | .cont p | .caught p | .onValue p | .caughtError p => below id (p.path ++ [1])
  | .onCause p => below id (p.path ++ [2])
  | .scopeOpen p | .scopeProvide p _ | .scopeBody p _ => below id (p.path ++ [0])
  | .acquireCtx p | .acquireIn p _ | .forkScopedIn p => below id p.path
  | .acquired p _ _ | .releaseUnder p _ _ | .releaseBody p _ _ => below id (p.path ++ [1])
  | .store callback => storeName id callback
  | .gen p pc _ => below id (p.path ++ [0] ++ pc)
  | .loop p => below id p.path
  | .withWaiter base _ _ => name id base
  | .provideMask _ (.program p) | .updateThen _ (.program p) _ | .bodyThen (.program p) _ _ =>
    below id p.path
  | _ => 0

/-- A synchronous note carries its reservation until the actual store update consumes it. -/
def thunk (id : Nat) : EffThunk → Nat
  | .body p | .forkInAt p _ | .acquireMasked p _ | .act p | .releaseMasked p _ => below id p.path
  | .provideMasked _ (.program p) _ | .restoreRegion (.program p) _ => below id p.path
  | .op op | .store (.op op) => operation id op
  | .store (.body body) => program id body
  | .store (.act action) => storeAction id action
  | _ => 0

/-- Leaf weights for the shared generated native-code fold. -/
abbrev nativeWeights (id : Nat) : Machine.PrimWeights.Model EffName EffThunk where
  name := name id
  thunk := thunk id

/-- Active code counts its next note and future ordinary callbacks. -/
abbrev current (id : Nat) (code : NCode) : Nat :=
  cata_prim (Machine.PrimWeights.currentAlgebra (nativeWeights id)) code

/-- Saved code counts only its future callback, excluding its copied active body. -/
def saved (id : Nat) : NCode → Nat
  | .onSuccess _ callback | .onFailure _ callback | .onExit _ callback _ => name id callback
  | .onSuccessConst _ next => current id next
  | .onSuccessAndFailure _ success failure => name id success + name id failure
  | .iterator callback _ | .whileLoop callback _ | .asyncFinalizer callback => name id callback
  | _ => 0

/-- Interpreting each existing stored program transfers its entire active note reservation. -/
theorem program_exact (id : Nat) (body : ProgName) :
    current id (embed (progOf body)) = program id body := by
  fun_induction progOf body
  all_goals aesop (add norm simp [program, current, cata_prim, thunk, name, storeName, storeAction,
    embed, finProgram]) (add safe cases [FinalizerStrategy])

/-- Stored value callbacks spend only the reservation retained by their name. -/
theorem store_value_bound (id : Nat) (callback : Name) (value : Val) :
    current id (embed (Machine.contAOf callback value)) ≤ storeName id callback := by
  have folded (body : ProgName) :
      cata_prim (PrimWeights.currentAlgebra (nativeWeights id)) (embed (progOf body)) = program id body :=
    program_exact id body
  fun_cases Machine.contAOf callback value
  all_goals aesop (add norm simp [folded, current, cata_prim, thunk, name, storeName,
    storeAction, operation, embed, Prim.ofExit])

/-- Stored cause callbacks introduce no active note operation. -/
theorem store_cause_zero (id : Nat) (callback : Name) (cause : CauseV) :
    current id (embed (Machine.contEOf callback cause)) = 0 := by
  fun_cases Machine.contEOf callback cause
  all_goals aesop (add norm simp [current, cata_prim, name, embed, Prim.ofExit])

/-- An actual mask hook preserves the ordered saved-note reservation sum. -/
theorem ensure_saved (id : Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    ((code.ensure fiber).1.stack.map (saved id)).sum = (fiber.stack.map (saved id)).sum := by
  fun_cases Prim.ensure code fiber
  all_goals simp only [saved, List.map_cons, List.sum_cons, Nat.zero_add]

/-- An actual hook replacement carries no note reservation. -/
theorem ensure_answer_zero (id : Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (next : NCode)
    (selected : (code.ensure fiber).2 = some next) : current id next = 0 := by
  revert selected
  fun_cases Prim.ensure code fiber
  all_goals intro selected
  all_goals aesop (add norm simp [current, cata_prim])

/-- The shared scalar pop law applies to the active cleanup-note projection. -/
def model (id : Nat) : Machine.FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann where
  current := current id
  saved := saved id
  ensure_stack := fun code fiber => Nat.le_of_eq (ensure_saved id code fiber)
  ensure_replacement := ensure_answer_zero id

/-- Actual getCont retains the selected answer's reservation and the unconsumed stack. -/
theorem pop_bound (id : Nat) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    ((fiber.getCont demand skip cause).fiber.stack.map (saved id)).sum +
      Machine.FrameWeights.answer (model id) (fiber.getCont demand skip cause).answer ≤
        (fiber.stack.map (saved id)).sum :=
  Machine.FrameWeights.getCont_le (model id) fiber demand skip cause

/-- The dormant actual request finalizer holds no active cleanup-note reservation. -/
theorem dormant_zero (id : Nat) (point : Point) : name id (.fin point) = 0 := rfl

/-- The actual native cleanup note holds one reservation before it commits. -/
theorem note_one (id : Nat) (cell : RefKey) (env : List Val) :
    current id (.sync (.op (.refUpdate cell (Store.noteAt id env.length) env))) = 1 := by
  change (if Store.noteAt id env.length == Store.noteAt id env.length then 1 else 0) = 1
  rw [BEq.refl]
  rfl

/-- The native success produced after the note holds no unspent reservation. -/
theorem answered_zero (id : Nat) (value : Val) : current id (.success value) = 0 := rfl

/-- The actual cleanup note exchanges its active reservation for one committed log identity. -/
theorem note_consumes (id : Nat) (cell : RefKey) (env : List Val)
    (state next : Stores) (answer : Val)
    (written : syncOpStep (.refUpdate cell (Store.noteAt id env.length) env) state = some (next, answer)) :
    Writer.heapCount id next.refs + current id (.success answer) =
      Writer.heapCount id state.refs +
        current id (.sync (.op (.refUpdate cell (Store.noteAt id env.length) env))) := by
  letI : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq
  rw [answered_zero, note_one, Writer.note_heap_count id id cell env state next answer written]
  simp only [beq_self_eq_true, ↓reduceIte, Nat.add_zero]

/-- The read head's native operation never carries a cleanup-note reservation. -/
theorem read_operation_zero (id : Nat) (env : List Val) (value : Val) :
    (match NativeOp.syncOpOf .refGet env value with
      | some op => operation id op | none => 0) = 0 := by
  cases found : NativeOp.syncOpOf .refGet env value with
  | none => rfl
  | some op =>
    obtain ⟨key, same⟩ := Store.get_inv found
    rw [same]
    rfl

/-- Compiling a source read retains no note when its frontier address owns none. -/
theorem compile_read_zero (id : Nat) (point : Point) (request : Term)
    (excluded : below id point.path = 0) :
    current id (compileEff (.perform .refGet request) point) = 0 := by
  cases fuel : point.fuel with
  | zero => simp only [compileEff, fuel, frontier, current, cata_prim, thunk, excluded]
  | succ count =>
    simp only [compileEff, fuel, NativeOp.kind]
    cases evaluated : evalTerm point.env request with
    | none => simp only [badShape, current, cata_prim]
    | some value =>
      cases selected : NativeOp.syncOpOf .refGet point.env value with
      | none => simp only [selected, badShape, current, cata_prim]
      | some op =>
        have zero := read_operation_zero id point.env value
        rw [selected] at zero
        simpa only [selected, current, cata_prim, thunk] using zero

/-- The active address projection never contains more than one selected note. -/
theorem below_le_one (id : Nat) (path : List Nat) : below id path ≤ 1 := by
  unfold below Opportunities.below
  split
  · split <;> omega
  · omega

/-- The finalizer's initial window-read child excludes its following note. -/
theorem read_child_zero (id : Nat) (path : List Nat)
    (source : path = SourcePaths.requestPath id ++ [1]) : below id (path ++ [0]) = 0 := by
  have query : Writer.notePath id = (path ++ [1]) ++ [0] := by
    rw [source]
    simp only [Writer.notePath, List.append_assoc]
    rfl
  have right : Opportunities.below (Writer.notePath id) (path ++ [1]) = 1 := by
    rw [query]
    unfold Opportunities.below
    rw [List.isPrefixOf_iff_prefix.mpr (List.prefix_append (path ++ [1]) [0])]
    rfl
  have apart := Opportunities.siblings_le (Writer.notePath id) path 0 1 (by decide)
  have upper : Opportunities.below (Writer.notePath id) path ≤ 1 := by
    unfold Opportunities.below
    split <;> omega
  unfold below
  split
  · omega
  · rfl

/-- Each actual cleanup starts by reading the window before its one note. -/
def startsWithRead (root : NativeEff) (id : Nat) : Bool :=
  match Node.at_ (.eff root) (SourcePaths.requestPath id ++ [1]) with
  | some (.eff (.bind (.perform .refGet (.var 0)) _)) => true
  | _ => false

/-- The actual six finalizers retain the same one-note entry shape. -/
theorem entry_census :
    (Store.shopProgram.map fun root => requests.all (startsWithRead root)) = some true := by
  kernel_rfl

/-- Successful admission exposes the actual source entry for each cleanup identity. -/
theorem entry_at (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) :
    ∃ rest, Node.at_ (.eff built.program) (SourcePaths.requestPath id ++ [1]) =
      some (.eff (.bind (.perform .refGet (.var 0)) rest)) := by
  have program : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have checked := entry_census
  rw [program] at checked
  have selected := List.all_eq_true.mp (Option.some.inj checked) id member
  unfold startsWithRead at selected
  split at selected
  · next rest found => exact ⟨rest, found⟩
  · cases selected

/-- The exact native bind constructor retains its current child as existing code. -/
private theorem compile_bind (first rest : NativeEff) (point : Point) (fuel : Nat)
    (positive : point.fuel = fuel + 1) :
    compileEff (.bind first rest) point =
      .onSuccess (compileEff first (point.child 0)) (.cont point) := by
  rw [compileEff, positive]

/-- Starting the actual finalizer supplies at most one active note reservation.
The statement retains arbitrary captured environments and compile fuel. -/
theorem entry_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point)
    (source : point.path = SourcePaths.requestPath id ++ [1]) :
    current id (resolve built.program point) ≤ 1 := by
  obtain ⟨rest, found⟩ := entry_at built admitted id member
  have actual : Node.at_ (.eff built.program) point.path =
      some (.eff (.bind (.perform .refGet (.var 0)) rest)) := by rw [source]; exact found
  rw [SourceScope.resolve_at _ _ _ actual]
  cases fuel : point.fuel with
  | zero =>
    simp only [compileEff, fuel, frontier, current, cata_prim, thunk]
    exact below_le_one id point.path
  | succ count =>
    rw [compile_bind _ _ point count fuel, current, cata_prim]
    have excluded : below id (point.child 0).path = 0 := read_child_zero id point.path source
    change current id (compileEff (.perform .refGet (.var 0)) (point.child 0)) +
      name id (.cont point) ≤ 1
    rw [compile_read_zero id _ (.var 0) excluded]
    change 0 + below id (point.path ++ [1]) ≤ 1
    simpa only [Nat.zero_add] using below_le_one id (point.path ++ [1])

/-- A prefix first appears on one appended edge only when that edge completes the prefix. -/
private theorem entering_prefix (base path : List Nat) (edge : Nat)
    (entered : (base ++ [1]).isPrefixOf (path ++ [edge]) = true)
    (outside : (base ++ [1]).isPrefixOf path = false) : path = base ∧ edge = 1 := by
  have child := List.isPrefixOf_iff_prefix.mp entered
  have old : ¬ (base ++ [1]).IsPrefix path := by
    intro ownedPrefix
    rw [List.isPrefixOf_iff_prefix.mpr ownedPrefix] at outside
    cases outside
  have opposite : path.IsPrefix (base ++ [1]) :=
    (List.prefix_or_prefix_of_prefix child (List.prefix_append path [edge])).resolve_left old
  have lower := opposite.length_le
  have upper := child.length_le
  have strict : path.length < (base ++ [1]).length := by
    by_contra refused
    have equal := opposite.eq_of_length_le (by omega)
    subst path
    exact old (List.prefix_refl _)
  have length : (base ++ [1]).length = (path ++ [edge]).length := by
    simp only [List.length_append, List.length_singleton] at lower upper strict ⊢
    omega
  have same := child.eq_of_length length
  obtain ⟨paths, edges⟩ := List.append_singleton_inj.mp same
  exact ⟨paths.symm, edges.symm⟩

/-- An ordinary source edge transfers no more active note reservation than its parent.
Only the selected finalizer entry may activate a new reservation. -/
theorem child_le (id : Nat) (path : List Nat) (edge : Nat)
    (ordinary : path ≠ SourcePaths.requestPath id ∨ edge ≠ 1) :
    below id (path ++ [edge]) ≤ below id path := by
  have inherited := Opportunities.child_le (Writer.notePath id) path edge
  cases entered : (SourcePaths.requestPath id ++ [1]).isPrefixOf (path ++ [edge]) with
  | false => simp only [below, entered, Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_le _
  | true =>
    cases outside : (SourcePaths.requestPath id ++ [1]).isPrefixOf path with
    | true => simpa only [below, entered, outside, ↓reduceIte] using inherited
    | false =>
      obtain ⟨parent, child⟩ := entering_prefix _ _ _ entered outside
      rcases ordinary with different | different
      · exact (different parent).elim
      · exact (different child).elim

/-- The actual finalizer producer resolves child one with its captured exit value. -/
theorem program_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point)
    (source : point.path = SourcePaths.requestPath id) (view : List (FiberId × ExitV))
    (exit : ExitV) (program : NCode)
    (produced : (interpAt built.program view built.table).finalizerProgram (.fin point) exit = some program) :
    current id program ≤ 1 := by
  change some (resolve built.program ({point with completed := view}.childWith 1 (reifyExitVal exit))) =
    some program at produced
  cases produced
  apply entry_bound built admitted id member
  change point.path ++ [1] = SourcePaths.requestPath id ++ [1]
  rw [source]

/-- The native restoring wrapper adds no new cleanup-note reservation. -/
theorem restoring_count (id : Nat) (root : NativeEff) (table : RowTable)
    (view : List (FiberId × ExitV)) (exit : ExitV) (program : NCode) :
    current id (finalizerCode (interpAt root view table) exit program) = current id program := by
  cases exit <;> rfl

/-- The frame's live scalar projection reads its active code and ordered saved callbacks. -/
def frame (id : Nat) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Nat :=
  current id fiber.current + (fiber.stack.map (saved id)).sum

/-- Select the actual native continuation pop for its delivered exit. -/
def popFor (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV) :=
  match exit with
  | .success _ => fiber.getCont .contA false none
  | .failure cause => fiber.getCont .contE true (some cause)

/-- The actual selected finalizer pop retains every other saved note reservation. -/
theorem finalizer_pop_bound (id : Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV)
    (body : NCode) (point : Point) (flag : Bool)
    (selected : (popFor fiber exit).answer = .frame (.onExit body (.fin point) flag)) :
    ((popFor fiber exit).fiber.stack.map (saved id)).sum ≤ (fiber.stack.map (saved id)).sum := by
  cases exit with
  | success value =>
    have bound := pop_bound id fiber .contA false none
    change (fiber.getCont .contA false none).answer = _ at selected
    rw [selected] at bound
    simpa only [popFor, Machine.FrameWeights.answer, model, saved, name, Nat.add_zero] using bound
  | failure cause =>
    have bound := pop_bound id fiber .contE true (some cause)
    change (fiber.getCont .contE true (some cause)).answer = _ at selected
    rw [selected] at bound
    simpa only [popFor, Machine.FrameWeights.answer, model, saved, name, Nat.add_zero] using bound

/-- Starting an actual request finalizer issues one note reservation and records that start.
The native result retains the existing heap and unfinished evaluator state. -/
theorem native_start (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (machine : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (exit : ExitV) (body : NCode) (point : Point) (flag : Bool) (program : NCode)
    (source : point.path = SourcePaths.requestPath id)
    (selected : (popFor fiber.frame exit).answer = .frame (.onExit body (.fin point) flag))
    (produced : (interpAt built.program machine.completedExits built.table).finalizerProgram (.fin point)
      ((popFor fiber.frame exit).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (interpAt built.program machine.completedExits built.table)
      machine fiber yielding exit
    frame id next.fiber.frame ≤ frame id fiber.frame + 1 ∧
      next.machine.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath id)) =
        machine.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath id)) + 1 ∧
      next.machine.state.refs = machine.state.refs := by
  letI : LawfulBEq (List Nat) := @List.instLawfulBEq Nat _ Nat.instLawfulBEq
  letI : ReflBEq (List Nat) := @List.instReflBEq Nat _ Nat.instLawfulBEq.toReflBEq
  have reserve := program_bound built admitted id member point source machine.completedExits
    ((popFor fiber.frame exit).deliveredExit exit) program produced
  have savedBound := finalizer_pop_bound id fiber.frame exit body point flag selected
  have silent : (popFor fiber.frame exit).events.countP
      (Machine.FinalizerCredits.started (FinalizerRun.atPath (SourcePaths.requestPath id))) = 0 := by
    cases exit <;> exact Machine.FinalizerCredits.getCont_no_start _ _ _ _ _
  cases exit with
  | success value =>
    change (fiber.frame.getCont .contA false none).answer = _ at selected
    change (interpAt built.program machine.completedExits built.table).finalizerProgram (.fin point)
      ((fiber.frame.getCont .contA false none).deliveredExit (.success value)) = some program at produced
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [selected]
    dsimp only
    rw [produced]
    dsimp only
    refine ⟨?_, ?_, rfl⟩
    · simp only [frame, restoring_count]
      change current id program + ((popFor fiber.frame (.success value)).fiber.stack.map (saved id)).sum ≤ _
      omega
    · simp only [RunMachine.emit_trace, List.countP_append, List.countP_singleton,
        Machine.FinalizerCredits.frame_starts, Machine.FinalizerCredits.runStarted, FinalizerRun.atPath,
        source, beq_self_eq_true, ↓reduceIte]
      change _ + ((popFor fiber.frame (.success value)).events.countP
        (Machine.FinalizerCredits.started (FinalizerRun.atPath (SourcePaths.requestPath id))) + 1) = _
      rw [silent]
  | failure cause =>
    change (fiber.frame.getCont .contE true (some cause)).answer = _ at selected
    change (interpAt built.program machine.completedExits built.table).finalizerProgram (.fin point)
      ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) = some program at produced
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [selected]
    dsimp only
    rw [produced]
    dsimp only
    refine ⟨?_, ?_, rfl⟩
    · simp only [frame, restoring_count]
      change current id program + ((popFor fiber.frame (.failure cause)).fiber.stack.map (saved id)).sum ≤ _
      omega
    · simp only [RunMachine.emit_trace, List.countP_append, List.countP_singleton,
        Machine.FinalizerCredits.frame_starts, Machine.FinalizerCredits.runStarted, FinalizerRun.atPath,
        source, beq_self_eq_true, ↓reduceIte]
      change _ + ((popFor fiber.frame (.failure cause)).events.countP
        (Machine.FinalizerCredits.started (FinalizerRun.atPath (SourcePaths.requestPath id))) + 1) = _
      rw [silent]

end Test.Dogfood.Scenario.Atomic.WriterPhase
