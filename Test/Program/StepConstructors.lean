import Effect4.Modules.Step.Elab
import Effect4.Program.Native
import Effect4.Laws.Modules.Step

/-! Finite checks of the new Step constructors and their field-name notation.
The shared reading and typing laws own the general statements.
These controls cover construction order, refusal, and the identity interpretation boundary. -/

set_option autoImplicit false
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Modules

namespace Test.Program.StepConstructors

def fields : List (String × Bool × Ty) := [("count", false, .nat), ("ready", false, .bool)]

def made : Step [] (.record fields) := record_step% { ready := .bool true, count := .nat 7 }
#guard made.normal && made.canonical
#guard @BEq.beq (Nat × Bool × Unit) inferInstance (made.eval (Γ := []) Leaves.opaque ()) (7, (true, ()))

#guard match made.term (Input.source []) {} [] with
  | .ok t => evalTerm [] t == some (Effect4.Machine.Record.frame [("count", .nat 7), ("ready", .bool true)])
  | .error _ => false
#guard match made.term (Input.source []) {} [] with
  | .ok t => termTy nativeSignature [] t == some (.record fields)
  | .error _ => false

-- The named constructor accepts the ordinary schema type alias.
def recordTy : Ty := .record fields
def aliased : Step [] recordTy := record_step% { count := .nat 7, ready := .bool true }
example : Reads (aliased.term (Input.source [])) {} [] []
    (Effect4.Machine.Record.frame [("count", .nat 7), ("ready", .bool true)]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil aliased rfl
example : TypesEach nativeSignature (aliased.term (Input.source [])) {} [] [] recordTy :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil aliased rfl

def emptyRecord : Step [] (.record []) := record_step% {}
#guard emptyRecord.normal && emptyRecord.canonical

def listed : Step [] (.list .nat) := .cons (.nat 7) .nil
#guard listed.normal
#guard @BEq.beq (List Nat) inferInstance (listed.eval (Γ := []) Leaves.opaque ()) [7]
#guard match listed.term (Input.source []) {} [] with
  | .ok t => evalTerm [] t == some (.list [.nat 7]) && termTy nativeSignature [] t == some (.list .nat)
  | .error _ => false

def absent : Step [] (.option .bool) := .none
#guard absent.normal && absent.canonical
#guard match absent.term (Input.source []) {} [] with
  | .ok t => evalTerm [] t == some Effect4.Store.Val.none &&
    termTy nativeSignature [] t == some (.option .bool)
  | .error _ => false

-- A normal type variable is not a formed annotation outside a template.
#guard !(Step.nil : Step [] (.list (.var 0))).normal
#guard !(Step.none : Step [] (.option (.var 0))).normal

-- Comparison's total candidate is not a reading claim at malformed opaque values.
def same : Step [idTy, idTy] .bool := .sameDeferred (.var (.here _ _)) (.var (.there _ (.here _ _)))
#guard same.compares && !same.binds
#guard same.eval (Γ := [idTy, idTy]) Leaves.deferredKeys (⟨4⟩, (⟨4⟩, ()))
#guard !same.eval (Γ := [idTy, idTy]) Leaves.opaque (Effect4.Store.Val.unit, (Effect4.Store.Val.unit, ()))
example : same.IdentityFacts Leaves.deferredKeys := ⟨DeferredIdentity.deferredKeys⟩

/-- error: record_step%: the required field ready is missing -/
#guard_msgs in
example : Step [] (.record fields) := record_step% { count := .nat 7 }

/-- error: record_step%: the schema has no field extra -/
#guard_msgs in
example : Step [] (.record fields) := record_step% { count := .nat 7, ready := .bool true, extra := .unit }

/-- error: record_step%: the field count is supplied twice -/
#guard_msgs in
example : Step [] (.record fields) := record_step% { count := .nat 7, count := .nat 8, ready := .bool true }

/-- error: record_step%: the field maybe is optional; construction requires required fields -/
#guard_msgs in
example : Step [] (.record [("maybe", true, .nat)]) := record_step% { maybe := .nat 7 }

/-- error: record_step%: two fields of the schema are named count -/
#guard_msgs in
example : Step [] (.record [("count", false, .nat), ("count", false, .nat)]) :=
  record_step% { count := .nat 7 }

end Test.Program.StepConstructors
