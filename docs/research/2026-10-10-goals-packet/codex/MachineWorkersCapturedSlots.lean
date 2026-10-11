import MachineWorkersNativeSlots
import Effect4.Laws.Machine.ScopeFields

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual captured connection values serve the unchanged Workers.Assertions.logs_step.
Reach: both acquisition sites and the actual native acquired callback at a supplied source point.
Limit: the history producer must preserve the prefix and supply the connection answer class.
Consumer: a selected foreign finalizer resolves the correct released-reference writer.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace MachineWorkersCapturedSlots
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario MachineWorkersSlots MachineWorkersConnections MachineWorkersNativeSlots

/-- The foreign capture retains the exact connection slot and the existing lexical ownership.
Administrative finalizers carry no source connection slot. -/
abbrev CapturedSlots := MachineWorkersSlots.CapturedSlots

/-- The same scope-field census retains exact captures without constraining allocation strategy. -/
def scopeModel (total : Nat) : ScopeFields.Model where
  finalizer := CapturedSlots total
  strategy _ := True
  sequential := trivial
  closeChild := fun _ => trivial
  detach := fun _ _ => trivial

/-- Both actual acquisition addresses supply the head required by captured lexical ownership. -/
theorem acquisition_source (total identity : Nat) (identitySite : identity = 1 ∨ identity = 2) :
    SourceScope.AcquisitionAt (Programs.workersProgram total) (Programs.crewAcquire identity) := by
  have member : identity ∈ [1, 2] := by
    rcases identitySite with one | two
    · rw [one]
      exact List.mem_cons_self
    · rw [two]
      exact List.mem_cons_of_mem 1 List.mem_cons_self
  have head := Programs.workers_acquisition_sites total identity member
  unfold Programs.acquisitionAt at head
  split at head
  · rename_i acquire release found
    exact ⟨acquire, release, found⟩
  · cases head

/-- The actual acquired answer creates a capture with its own connection literal.
The stored capture reserves the later exit binder at its effective release destination. -/
theorem acquired_capture (total : Nat) (world : MachineWorkersSlots.World)
    (identity : Nat) (point : Point) (context : Ctx) (answer : Val)
    (identitySite : identity = 1 ∨ identity = 2)
    (path : point.path = Programs.crewAcquire identity)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings)
    (good : ValueAt world (.connection identity) answer) :
    CapturedSlots total (.foreign (point.capture answer context)) := by
  have source := acquisition_source total identity identitySite
  rw [← path] at source
  obtain ⟨acquire, release, found⟩ := source
  have captured := SourceScope.capture_at (Programs.workersProgram total) point answer context
    (SourceScope.next_of_at _ _ _ 1 2 found lexical rfl) ⟨acquire, release, found⟩
  refine ⟨captured, ?_⟩
  rw [good.2]
  rcases identitySite with one | two
  · subst identity
    refine Or.inl ⟨path, ?_⟩
    change point.env ++ [Val.nat 1] = bindings ++ [Val.nat 1]
    rw [acquisition_one_env total point path lexical leading]
  · subst identity
    obtain ⟨previous, environment⟩ := acquisition_two_env total point path lexical leading
    refine Or.inr ⟨previous, path, ?_⟩
    change point.env ++ [.nat 2] = bindings ++ [previous, .nat 2]
    rw [environment, List.append_assoc]
    rfl

/-- The actual saved acquired callback installs the capture proved by its incoming answer.
It leaves the older stack intact and emits the real popped-frame event. -/
theorem acquired_resume (total : Nat) (world : MachineWorkersSlots.World)
    (identity : Nat) (point : Point) (context : Ctx) (scope : Nat)
    (body : NCode) (answer : Val) (view : List (FiberId × ExitV)) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (identitySite : identity = 1 ∨ identity = 2)
    (path : point.path = Programs.crewAcquire identity)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings)
    (good : ValueAt world (.connection identity) answer)
    (noInterrupt : fiber.deferredInterrupt = false) :
    ({fiber with stack := .onSuccess body (.acquired point context scope) :: fiber.stack}).resumeValue
      (interpAt (Programs.workersProgram total) view table).toPrimInterp answer none =
      (.running {fiber with current := (.onSuccess
        (.sync (.op (.scopeAdd scope (.foreign (point.capture answer context)))))
        (.afterScopeAdd answer (.foreign (point.capture answer context))))},
        [.popped (.onSuccess body (.acquired point context scope))]) ∧
    CapturedSlots total (.foreign (point.capture answer context)) := by
  constructor
  · cases fiber with
    | mk current stack interruptible interrupted deferred =>
      change deferred = false at noInterrupt
      subst deferred
      rfl
  · exact acquired_capture total world identity point context answer identitySite path lexical leading good

/-- The actual registration operation retains the incoming literal in every surviving scope row.
The acquired producer supplies the new field; the shared scope census supplies all old rows. -/
theorem acquired_registration (total : Nat) (world : MachineWorkersSlots.World)
    (identity : Nat) (point : Point) (context : Ctx) (scope : Nat) (answer : Val)
    (state : Stores) (reply : Val)
    (identitySite : identity = 1 ∨ identity = 2)
    (path : point.path = Programs.crewAcquire identity)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings)
    (good : ValueAt world (.connection identity) answer)
    (owned : ScopeFields.ScopesAt (scopeModel total) world.state.scopes)
    (step : syncOpStep (.scopeAdd scope (.foreign (point.capture answer context))) world.state = some (state, reply)) :
    ScopeFields.ScopesAt (scopeModel total) state.scopes := by
  exact ScopeFields.sync_scopes_at (scopeModel total)
    (.scopeAdd scope (.foreign (point.capture answer context))) world.state state reply owned
    (acquired_capture total world identity point context answer identitySite path lexical leading good) step

/-- State-first close returns the exact retained captures before removing their registrations.
Consumer: every selected foreign finalizer uses selected_writer at its effective release destination. -/
theorem captured_close_order (total : Nat) (scope : Nat) (exit : ExitV)
    (state next : Stores) (strategy : FinalizerStrategy) (order : List FinName)
    (owned : ScopeFields.ScopesAt (scopeModel total) state.scopes)
    (closed : scopeCloseSnapshot scope exit state = some (next, strategy, order)) :
    ScopeFields.ScopesAt (scopeModel total) next.scopes ∧ ∀ fin ∈ order, CapturedSlots total fin := by
  have kept := ScopeFields.close_snapshot_at (scopeModel total) scope exit state next strategy order owned closed
  exact ⟨kept.1, kept.2.1⟩

/-- A selected first capture resolves the real release writer with its saved connection slot.
This consumes the capture predicate without reconstructing a raw acquisition Point. -/
theorem selected_writer (total : Nat) (capture : Capture) (exit : Val)
    (view : List (FiberId × ExitV)) (fuel : Nat)
    (slots : CapturedSlots total (.foreign capture)) (amount : capture.fuel = fuel + 2) :
    (resolve (Programs.workersProgram total) ((Point.ofCapture capture view).childWith 1 exit) =
      .sync (.op (.refUpdate ⟨1⟩ (MachineWorkersWriters.appendOne 7 (.var 5))
        (bindings ++ [.nat 1, exit])))) ∨
    ∃ previous, resolve (Programs.workersProgram total) ((Point.ofCapture capture view).childWith 1 exit) =
      .sync (.op (.refUpdate ⟨1⟩ (MachineWorkersWriters.appendOne 8 (.var 6))
        (bindings ++ [previous, .nat 2, exit]))) := by
  rcases slots.2 with ⟨path, environment⟩ | ⟨previous, path, environment⟩
  · apply Or.inl
    have found : Node.at_ (.eff (Programs.workersProgram total))
        ((Point.ofCapture capture view).childWith 1 exit).path =
        some (.eff (.perform (.refUpdateWith (MachineWorkersWriters.appendOne 7 (.var 5))) (.var 1))) := by
      change Node.at_ _ (capture.path ++ [1]) = _
      rw [path]
      exact MachineWorkersWriters.release_one total
    rw [Agreement.resolve_of_at found]
    rw [Agreement.compileEff_perform_sync _ _ (k := fuel) (by
      change capture.fuel - 1 = fuel + 1
      rw [amount]
      omega) rfl]
    change (match evalTerm (capture.env ++ [exit]) (.var 1) with
      | some value => match NativeOp.syncOpOf (.refUpdateWith (MachineWorkersWriters.appendOne 7 (.var 5)))
          (capture.env ++ [exit]) value with
        | some operation => Prim.sync (EffThunk.op operation)
        | none => badShape
      | none => badShape) = _
    rw [environment]
    kernel_rfl
  · refine Or.inr ⟨previous, ?_⟩
    have found : Node.at_ (.eff (Programs.workersProgram total))
        ((Point.ofCapture capture view).childWith 1 exit).path =
        some (.eff (.perform (.refUpdateWith (MachineWorkersWriters.appendOne 8 (.var 6))) (.var 1))) := by
      change Node.at_ _ (capture.path ++ [1]) = _
      rw [path]
      exact MachineWorkersWriters.release_two total
    rw [Agreement.resolve_of_at found]
    rw [Agreement.compileEff_perform_sync _ _ (k := fuel) (by
      change capture.fuel - 1 = fuel + 1
      rw [amount]
      omega) rfl]
    change (match evalTerm (capture.env ++ [exit]) (.var 1) with
      | some value => match NativeOp.syncOpOf (.refUpdateWith (MachineWorkersWriters.appendOne 8 (.var 6)))
          (capture.env ++ [exit]) value with
        | some operation => Prim.sync (EffThunk.op operation)
        | none => badShape
      | none => badShape) = _
    rw [environment]
    kernel_rfl

/-- A foreign capture returned by the actual close snapshot selects the retained release writer.
The close removes its stored registration before this effective destination runs. -/
theorem close_selected_writer (total : Nat) (scope : Nat) (closing : ExitV)
    (state next : Stores) (strategy : FinalizerStrategy) (order : List FinName)
    (capture : Capture) (exit : Val) (view : List (FiberId × ExitV)) (fuel : Nat)
    (owned : ScopeFields.ScopesAt (scopeModel total) state.scopes)
    (closed : scopeCloseSnapshot scope closing state = some (next, strategy, order))
    (selected : .foreign capture ∈ order) (amount : capture.fuel = fuel + 2) :
    (resolve (Programs.workersProgram total) ((Point.ofCapture capture view).childWith 1 exit) =
      .sync (.op (.refUpdate ⟨1⟩ (MachineWorkersWriters.appendOne 7 (.var 5))
        (bindings ++ [.nat 1, exit])))) ∨
    ∃ previous, resolve (Programs.workersProgram total) ((Point.ofCapture capture view).childWith 1 exit) =
      .sync (.op (.refUpdate ⟨1⟩ (MachineWorkersWriters.appendOne 8 (.var 6))
        (bindings ++ [previous, .nat 2, exit]))) := by
  exact selected_writer total capture exit view fuel
    ((captured_close_order total scope closing state next strategy order owned closed).2 _ selected) amount

end MachineWorkersCapturedSlots
