import Test.Dogfood.Proofs.WorkersWriters
import Effect4.Laws.Machine.PrimWeights
import Effect4.Laws.Machine.WriterWeights
import Effect4.Laws.Program.ReleaseTrace
import Effect4.Laws.Program.PlaceFunding.FrameControl

/-!
Concept: scope-lifetime-finalization R11.
Question: the active release reservation serves Workers.Assertions.logs_step.
Reach: the actual primitive fold and saved stack, counted separately for each connection.
The release-start push issues its reservation; the reference write consumes it.
The answer-flow invariant still supplies each writer's actual captured identity.
These local equations establish no history bound or release progress alone.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.WorkersWriterWeights
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario

/-- The source acquisition identifies one release start. -/
def selected (identity : Nat) (path : List Nat) : Nat :=
  if path = Programs.crewAcquire identity then 1 else 0

/-- The pending release body names its direct log-update leaf. -/
def leaf (identity : Nat) (path : List Nat) : Nat :=
  if path = Programs.crewAcquire identity ++ [1] then 1 else 0

/-- The two source release terms identify their pending writes before their captured values are read. -/
def operation (identity : Nat) : SyncOp → Nat
  | .refUpdate _ term _ =>
    if (identity == 1 && term == WorkersWriters.appendOne 7 (.var 5)) ||
       (identity == 2 && term == WorkersWriters.appendOne 8 (.var 6)) then 1 else 0
  | _ => 0

/-- The post-context callback retains the release body until it is installed. -/
def name (identity : Nat) : EffName → Nat
  | .releaseBody point _ _ => selected identity point.path
  | _ => 0

/-- The saved release-start callback receives its reservation at the actual push. -/
def savedSuccess (identity : Nat) : EffName → Nat
  | .releaseUnder point _ _ => selected identity point.path
  | callback => name identity callback

/-- Only the selected direct release leaf and its native update hold a pending write. -/
def thunk (identity : Nat) : EffThunk → Nat
  | .body point | .releaseMasked point _ => leaf identity point.path
  | .op op | .store (.op op) => operation identity op
  | _ => 0

abbrev weights (identity : Nat) : PrimWeights.Model EffName EffThunk where
  name := name identity
  thunk := thunk identity

/-- Active and saved weights are two observations of one generated fold. -/
abbrev pair (identity : Nat) (code : NCode) : Nat × Nat :=
  cata_prim (PrimWeights.pairedAlgebra (weights identity) (savedSuccess identity)) code

abbrev current (identity : Nat) (code : NCode) : Nat := (pair identity code).1
abbrev saved (identity : Nat) (code : NCode) : Nat := (pair identity code).2

/-- The active projection agrees with the shared primitive weight fold. -/
theorem current_fold (identity : Nat) (code : NCode) :
    current identity code = cata_prim (PrimWeights.currentAlgebra (weights identity)) code :=
  PrimWeights.paired_current (weights identity) (savedSuccess identity) code

/-- Administrative masks insert only a saved frame with zero write weight. -/
theorem ensure_saved (identity : Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    ((code.ensure fiber).1.stack.map (saved identity)).sum =
      (fiber.stack.map (saved identity)).sum := by
  fun_cases Prim.ensure code fiber
  all_goals simp only [saved, List.map_cons, List.sum_cons, Nat.zero_add]

/-- A hook's replacement is a failure and holds no pending write. -/
theorem ensure_answer (identity : Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (next : NCode)
    (found : (code.ensure fiber).2 = some next) : current identity next = 0 := by
  revert found
  fun_cases Prim.ensure code fiber
  all_goals intro found
  all_goals aesop (add norm simp [current, pair, cata_prim])

/-- The shared pop accounting reads both existing frame positions. -/
def model (identity : Nat) : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann where
  current := current identity
  saved := saved identity
  ensure_stack := fun code fiber => Nat.le_of_eq (ensure_saved identity code fiber)
  ensure_replacement := ensure_answer identity

abbrev frame (identity : Nat) := FrameWeights.frame (model identity)

/-- A selected release push creates exactly the reservation recorded by its trace event. -/
theorem release_push (identity : Nat) (point : Point) (previous : Ctx) (exit : ExitV)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (body : NCode) (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) :
    let before := {fiber with current := .onSuccess body (.releaseUnder point previous exit)}
    let after := {fiber with
      current := body
      stack := .onSuccess body (.releaseUnder point previous exit) :: fiber.stack}
    before.step interp = (.running after, [.pushed before.current]) ∧
      frame identity after = frame identity before + selected identity point.path := by
  constructor
  · rfl
  · simp only [frame, FrameWeights.frame, model, current, saved, pair,
      name, savedSuccess, List.map_cons, List.sum_cons, Nat.add_zero]
    omega

/-- The release log is the second allocated reference, read independently of the assertion module. -/
def log (state : Stores) : List Val :=
  match (state.refs[1]? : Option Val) with
  | some (.list values) => values
  | _ => []

/-- The writer ledger counts each committed identity and each pending write. -/
def ledger (identity : Nat) : PlaceFunding.Ledger where
  fiber := fun fiber => frame identity fiber.frame
  race := fun _ => 0
  state := fun state => (log state).count (.nat identity)
  command := fun _ => 0
  task := fun _ => 0
  consumed := fun _ => 0
  produced := fun event => if ReleaseTrace.releaseAt (Programs.crewAcquire identity) event then 1 else 0

/-- The writer projection assigns no pending reservation to queue or race storage. -/
theorem no_queue (identity : Nat) : PlaceFunding.NoQueue (ledger identity) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Imported code has no pending selected log write. -/
abbrev Free (identity : Nat) (code : NCode) : Prop := current identity code = 0

/-- Administrative row changes retain or discard the shared frame reservation. -/
theorem control (identity : Nat) : PlaceFunding.Control (ledger identity) (Free identity) :=
  PlaceFunding.Control.of_frame (ledger identity) (model identity) (fun _ => rfl)

/-- Trace events issue release credit and consume none. -/
theorem events (identity : Nat) : PlaceFunding.Events (ledger identity) :=
  ⟨fun _ _ => Nat.zero_le _⟩

end Test.Dogfood.Proofs.WorkersWriterWeights
