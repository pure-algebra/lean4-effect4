import Effect4.Laws.Program.SourceScope
import Effect4.Laws.Machine.PrimWeights
import Effect4.Laws.Machine.WriterWeights
import Effect4.Laws.Machine.StoredWeights
import Effect4.Laws.Program.ReleaseTrace
import Effect4.Laws.Program.PlaceFunding.FrameControl

/-!
Concept: scope-lifetime-finalization R11.
Question: a release's direct reference write consumes its recorded start.
Reach: one selected acquisition, release term, log reference and logged value.
Consumers: Workers.Assertions.logs_step and QueueWorkers.Assertions.logs_history.
The actual source census and acquired-value flow remain separate premises.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program

/-- A writer selects existing source, operation and observation fields. -/
structure Target where
  path : List Nat
  term : Term
  cell : Nat
  value : Val

/-- A selected acquisition issues the reservation when its release starts. -/
def selected (target : Target) (path : List Nat) : Nat := if path = target.path then 1 else 0

/-- The direct release body holds one pending write. -/
def leaf (target : Target) (path : List Nat) : Nat := if path = target.path ++ [1] then 1 else 0

/-- The selected source term identifies its write before its captured values are read. -/
def operation (target : Target) : SyncOp → Nat
  | .refUpdate _ term _ => if term == target.term then 1 else 0
  | _ => 0

/-- Stored wrappers use the same delayed-operation accounting as Atomic. -/
abbrev program (target : Target) := StoredWeights.program (operation target)
abbrev storeName (target : Target) := StoredWeights.name (operation target)
abbrev storeAction (target : Target) := StoredWeights.action (operation target)

/-- Ordinary callbacks retain their resolved child; release callbacks retain the selected write. -/
def name (target : Target) : EffName → Nat
  | .cont point | .caught point | .caughtError point | .onValue point => leaf target (point.path ++ [1])
  | .onCause point => leaf target (point.path ++ [2])
  | .scopeOpen point | .scopeProvide point _ | .scopeBody point _ => leaf target (point.path ++ [0])
  | .forkScopedIn point => leaf target point.path
  | .releaseUnder point _ _ | .releaseBody point _ _ => selected target point.path
  | .provideMask _ (.program point) | .updateThen _ (.program point) _ | .bodyThen (.program point) _ _ =>
    leaf target point.path
  | .store callback => storeName target callback
  | .withWaiter base _ _ => name target base
  | _ => 0

/-- The release-start success binder receives its callback reservation at the recorded push. -/
def successName (target : Target) : EffName → Nat
  | .releaseUnder _ _ _ => 0
  | callback => name target callback

abbrev savedSuccess (target : Target) := name target

/-- Only the selected direct release leaf and its native update hold a pending write. -/
def thunk (target : Target) : EffThunk → Nat
  | .body point | .releaseMasked point _ | .act point | .forkInAt point _ => leaf target point.path
  | .provideMasked _ (.program point) _ | .restoreRegion (.program point) _ => leaf target point.path
  | .op op | .store (.op op) => operation target op
  | .store (.body body) => program target body
  | .store (.act action) => storeAction target action
  | _ => 0

abbrev weights (target : Target) : PrimWeights.Model EffName EffThunk where
  name := name target
  thunk := thunk target
  successName := successName target

/-- Active and saved weights are two observations of one generated fold. -/
abbrev pair (target : Target) (code : NCode) : Nat × Nat :=
  cata_prim (PrimWeights.pairedAlgebra (weights target) (savedSuccess target)) code

abbrev current (target : Target) (code : NCode) : Nat := (pair target code).1
abbrev saved (target : Target) (code : NCode) : Nat := (pair target code).2

/-- The active projection agrees with the shared primitive weight fold. -/
theorem current_fold (target : Target) (code : NCode) :
    current target code = cata_prim (PrimWeights.currentAlgebra (weights target)) code :=
  PrimWeights.paired_current (weights target) (savedSuccess target) code

/-- Administrative masks insert only a saved frame with zero write weight. -/
theorem ensure_saved (target : Target) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    ((code.ensure fiber).1.stack.map (saved target)).sum =
      (fiber.stack.map (saved target)).sum := by
  fun_cases Prim.ensure code fiber
  all_goals simp only [saved, List.map_cons, List.sum_cons, Nat.zero_add]

/-- A hook's replacement is a failure and holds no pending write. -/
theorem ensure_answer (target : Target) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (next : NCode)
    (found : (code.ensure fiber).2 = some next) : current target next = 0 := by
  revert found
  fun_cases Prim.ensure code fiber
  all_goals intro found
  all_goals aesop (add norm simp [current, pair, cata_prim])

/-- The shared pop accounting reads both existing frame positions. -/
def model (target : Target) : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann where
  current := current target
  saved := saved target
  ensure_stack := fun code fiber => Nat.le_of_eq (ensure_saved target code fiber)
  ensure_replacement := ensure_answer target

abbrev frame (target : Target) := FrameWeights.frame (model target)

/-- A selected release push creates exactly the reservation recorded by its trace event. -/
theorem release_push (target : Target) (point : Point) (previous : Ctx) (exit : ExitV)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (body : NCode) (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) :
    let before := {fiber with current := .onSuccess body (.releaseUnder point previous exit)}
    let after := {fiber with
      current := body
      stack := .onSuccess body (.releaseUnder point previous exit) :: fiber.stack}
    before.step interp = (.running after, [.pushed before.current]) ∧
      frame target after = frame target before + selected target point.path := by
  constructor
  · rfl
  · simp only [frame, FrameWeights.frame, model, current, saved, pair,
      name, savedSuccess, successName, List.map_cons, List.sum_cons, Nat.add_zero]
    omega

/-- The release log is the selected reference, read independently of the assertion module. -/
def log (target : Target) (state : Stores) : List Val :=
  ((state.refs[target.cell]?).bind Val.asList?).getD []

/-- The writer ledger counts each committed target and each pending write. -/
def ledger (target : Target) : PlaceFunding.Ledger where
  fiber := fun fiber => frame target fiber.frame
  race := fun _ => 0
  state := fun state => (log target state).count target.value
  command := fun _ => 0
  task := fun _ => 0
  consumed := fun _ => 0
  produced := fun event => if ReleaseTrace.releaseAt target.path event then 1 else 0

/-- The writer projection assigns no pending reservation to queue or race storage. -/
theorem no_queue (target : Target) : PlaceFunding.NoQueue (ledger target) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Imported code has no pending selected log write. -/
abbrev Free (target : Target) (code : NCode) : Prop := current target code = 0

/-- Administrative row changes retain or discard the shared frame reservation. -/
theorem control (target : Target) : PlaceFunding.Control (ledger target) (Free target) :=
  PlaceFunding.Control.of_frame (ledger target) (model target) (fun _ => rfl)

/-- Trace events issue release credit and consume none. -/
theorem events (target : Target) : PlaceFunding.Events (ledger target) :=
  ⟨fun _ _ => Nat.zero_le _⟩

end Effect4.Program.ReleaseWriter
