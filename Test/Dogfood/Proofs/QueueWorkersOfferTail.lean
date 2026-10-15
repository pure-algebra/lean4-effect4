import Test.Dogfood.Proofs.QueueWorkersOfferSites
import Test.Dogfood.Proofs.QueueWorkersReadonlySource
import Effect4.Laws.Program.CodeClosure.Qualified.Stable

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, after the actual feeder offer commit.
The shared qualified fold retains the actual source operation and its full captured prefix.
A native consumer classifies its permitted withdrawal from that retained source witness.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersOfferTail
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario

/-- The actual continuation after the offer retains all original captured values. -/
def PointAt (bindings : List Val) (origin : List Nat) (point : Point) : Prop :=
  origin.IsPrefix point.path ∧ AnswerSlots.Prefix bindings point.env

/-- A retained writer names its actual source operation and captured environment. -/
def Writes (total : Nat) (bindings : List Val) (origin : List Nat) (op : SyncOp) : Prop :=
  ∃ point row request value, PointAt bindings origin point ∧
    Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.perform row request)) ∧
    evalTerm point.env request = some value ∧ row.syncOpOf point.env value = some op

/-- Ordinary callbacks preserve this source subtree and its complete captured prefix. -/
theorem transport (bindings : List Val) (origin : List Nat) :
    CodeClosure.Qualified.Transport (PointAt bindings origin) (AnswerSlots.Prefix bindings) where
  environment := fun held => held.2
  child := fun held _ => ⟨List.prefix_append_of_prefix held.1, held.2⟩
  childWith := fun held _ value => ⟨List.prefix_append_of_prefix held.1, held.2.append [value]⟩
  capture := fun held value _ => ⟨held.1, held.2.append [value]⟩

/-- The selected compiler operation supplies its own source witness to the existing leaf policy. -/
theorem operation (total : Nat) (bindings : List Val) (origin : List Nat)
    (point : Point) (row : NativeOp) (request : Term) (value : Val) (op : SyncOp)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.perform row request)))
    (held : PointAt bindings origin point) (reads : evalTerm point.env request = some value)
    (converted : row.syncOpOf point.env value = some op) :
    CodeClosure.Qualified.OpAt (PointAt bindings origin) (AnswerSlots.Prefix bindings)
      (Writes total bindings origin) op := by
  have writer : Writes total bindings origin op := ⟨point, row, request, value, held, found, reads, converted⟩
  generalize envEq : point.env = env at converted
  revert converted
  fun_cases NativeOp.syncOpOf row env value
  all_goals intro converted
  case case21 => cases converted
  all_goals cases converted
  all_goals aesop (add norm simp [CodeClosure.Qualified.OpAt])

/-- The actual tail uses the existing compiler and callback producer without another traversal. -/
theorem contract (total : Nat) (bindings : List Val) (origin : List Nat) :
    CodeClosure.Qualified.Contract (Programs.queueProgram total) (PointAt bindings origin)
      (AnswerSlots.Prefix bindings) (Writes total bindings origin) where
  compilation := CodeClosure.Qualified.compile_contract _ _ _ _ (transport bindings origin)
    (fun point row request value op found held reads converted =>
      operation total bindings origin point row request value op found held reads converted)
  child := (transport bindings origin).child
  childWith := (transport bindings origin).childWith
  capture := (transport bindings origin).capture

abbrev Code (total : Nat) (bindings : List Val) (origin : List Nat) :=
  CodeClosure.Qualified.CodeAt (PointAt bindings origin) (AnswerSlots.Prefix bindings) (Writes total bindings origin)

/-- The postcommit subtree has no assignment update operation. -/
def noUpdate : Node NativeOp → Bool
  | .eff (.perform (.refUpdateWith _) _) => false
  | _ => true

/-- The generated source addresses certify the actual feeder tail's writer exclusion. -/
theorem census (total : Nat) :
    (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.queueProgram total)) path).all (fun node =>
        if decide ((QueueWorkersOfferSites.path.dropLast ++ [1]).IsPrefix path) then noUpdate node else true)) = true := by
  kernel_rfl

/-- Every actual operation below the real offer continuation excludes assignment. -/
theorem below (total : Nat) (path : List Nat) (node : Node NativeOp)
    (inside : (QueueWorkersOfferSites.path.dropLast ++ [1]).IsPrefix path)
    (found : Node.at_ (.eff (Programs.queueProgram total)) path = some node) : noUpdate node = true := by
  have addressed : path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
    (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (census total) path addressed
  rw [found] at checked
  change (if decide ((QueueWorkersOfferSites.path.dropLast ++ [1]).IsPrefix path) then noUpdate node else true) = true at checked
  rw [if_pos (decide_eq_true inside)] at checked
  exact checked

/-- A broad postcommit callback cannot manufacture a worker assignment head. -/
theorem no_assignment (total : Nat) (bindings : List Val) (term : Term) (env : List Val) :
    ¬ Code total bindings (QueueWorkersOfferSites.path.dropLast ++ [1]) (.sync (.op (.refUpdate ⟨3⟩ term env))) := by
  intro owned
  change Writes total bindings (QueueWorkersOfferSites.path.dropLast ++ [1]) (.refUpdate ⟨3⟩ term env) at owned
  obtain ⟨point, row, request, value, held, found, _reads, converted⟩ := owned
  have quiet := below total point.path _ held.1 found
  generalize envEq : point.env = values at converted
  revert converted
  fun_cases NativeOp.syncOpOf row values value
  all_goals intro converted
  all_goals cases converted
  case case6 => cases quiet

/-- The real source entry retains the exact prefix used by the native withdrawal classifier. -/
theorem entry (total : Nat) (point : Point) :
    Code total point.env point.path (resolve (Programs.queueProgram total) point) :=
  CodeClosure.Qualified.resolve_at _ (SourceFragment.queue_fragment total) _ _ _
    (contract total point.env point.path) point ⟨List.prefix_refl _, List.take_length⟩

/-- The unit source family shares the common saved-frame implementation. -/
def laws (total : Nat) (bindings : List Val) (origin : List Nat) (table : RowTable) :=
  CodeClosure.Qualified.prefixLaws (Programs.queueProgram total) (SourceFragment.queue_fragment total) _ _ _
    (contract total bindings origin) (fun _ held _ => held) table
end Test.Dogfood.Proofs.QueueWorkersOfferTail
