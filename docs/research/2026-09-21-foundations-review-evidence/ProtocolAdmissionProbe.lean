import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Program.Typed.Contracts
import Effect4.Laws.Program.InterpR
import Effect4.Program.Checker

/-! Research controls for the foundations brief at 641a0fea. No proposed production definition
is assumed. Each theorem below states only the witnessed counterclaim or positive control. -/
set_option autoImplicit false
namespace FoundationsProtocolAdmissionProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-- A universe-zero certificate family may contain predicates; universe zero is not a
first-order syntax restriction. This family uses the actual reference signature. -/
def higherOrderCertificates : RSig.Op → Type := fun _ => Nat → Prop

def predicateCertificate : higherOrderCertificates (.inr .getId) := fun n => n = 0

theorem higherOrder_certificate_applies : predicateCertificate 0 := rfl

theorem not_every_type_is_closed : ¬ (∀ ty : Ty, ty.closed = true) := by
  intro h
  exact Bool.noConfusion (h (.var 0))

/-- Coarse shape admission alone does not imply that nested type arguments are closed. -/
theorem open_reference_type_shape_admitted :
    Val.hasTy (Val.cell ⟨0⟩) (.refOf (.var 0)) = true := rfl

theorem open_reference_type_not_closed : (Ty.refOf (.var 0)).closed = false := rfl

def oneSig : Effects.Signature.{0, 0} := ⟨Unit, fun _ => Unit⟩
def oneOrder : WorldOrder Unit := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩
def impossiblePost : Protocol Unit oneSig := ⟨fun _ _ => True, fun _ _ _ => False⟩
def inhabitedPost : Protocol Unit oneSig := ⟨fun _ _ => True, fun _ _ _ => True⟩
def oneRequest : Effects.Program oneSig Unit := .vis () (fun _ => .pure ())

/-- Generic protocol typing alone admits an operation even when no answer satisfies its
postcondition. It is not an operational progress or termination theorem. -/
theorem typed_at_false_with_impossible_post :
    Typed oneOrder impossiblePost () (fun _ _ => False) oneRequest := by
  exact .vis trivial (fun _ _ _ h => False.elim h)

theorem impossible_post_has_no_answer :
    ¬ ∃ w answer, impossiblePost.post w () answer := by
  rintro ⟨_, _, h⟩
  exact h

theorem inhabited_post_has_answer : ∃ w answer, inhabitedPost.post w () answer :=
  ⟨(), (), trivial⟩

theorem typed_at_true_with_inhabited_post :
    Typed oneOrder inhabitedPost () (fun _ _ => True) oneRequest := by
  exact .vis trivial (fun _ _ _ _ => .pure trivial)

theorem pure_false_rejected :
    ¬ Typed oneOrder impossiblePost () (fun _ _ => False) (.pure ()) := by
  intro h
  exact Typed.pure_inv h

def variableRoot : NativeEff := .succeed (.var 0)

theorem checker_accepts_static_nat_environment :
    Checker.check (nativeSignature []) [.nat] [] variableRoot = .ok (EffTy.pure .nat) := rfl

theorem runtime_environment_returns_bool :
    evalTerm [Val.bool false] (.var 0) = some (Val.bool false) := rfl

theorem runtime_bool_does_not_fit_static_nat :
    Val.hasTy (Val.bool false) .nat = false := rfl

theorem matching_runtime_environment_returns_nat :
    evalTerm [Val.nat 7] (.var 0) = some (Val.nat 7) := rfl

/-- Checker input environments also need closure if its output is claimed to be closed. -/
theorem unchecked_environment_produces_open_type :
    Checker.check (nativeSignature []) [.var 0] [] variableRoot =
      .ok (EffTy.pure (.var 0)) := rfl

def leafRoot : NativeEff := .succeed (.lit .unit)
def invalidPoint : Point := { path := [0], env := [], fuel := 1, tape := [] }

theorem checker_path_is_only_a_diagnostic_location :
    Checker.check (nativeSignature []) [] invalidPoint.path leafRoot =
      .ok (EffTy.pure .unit) := rfl

theorem immutable_point_can_name_no_node :
    Node.at_ (.eff leafRoot) invalidPoint.path = none := rfl

theorem missing_node_refuses_at_reference_interpreter :
    denoteAt leafRoot invalidPoint = .pure badShapeExit := rfl

theorem root_address_is_a_positive_control :
    Node.at_ (.eff leafRoot) [] = some (.eff leafRoot) := rfl

abbrev TypedWorld := Effect4.Program.Typed.World

def emptyWorld : TypedWorld :=
  ⟨⟨[], Stores.empty⟩, fun _ => none, fun _ => none, fun _ => none, fun _ _ => none⟩
/-- The landed exit observation checks handle shape, not allocation or nested declaration. -/
theorem forged_handle_exit_fits :
    Effect4.Program.Typed.Contracts.ExitFits emptyWorld (EffTy.pure (.refOf .nat))
      (.success (Val.cell ⟨99⟩)) := rfl

theorem forged_handle_does_not_exist :
    Handle.existsIn emptyWorld.toWorld (.cell ⟨99⟩) = false := rfl

theorem coarse_pure_forged_handle_is_typed (o : WorldOrder TypedWorld)
    (Ψ : Protocol TypedWorld RSig) :
    Typed o Ψ emptyWorld
      (fun w ex => Effect4.Program.Typed.Contracts.ExitFits w (EffTy.pure (.refOf .nat)) ex)
      (.pure (.success (Val.cell ⟨99⟩))) := .pure forged_handle_exit_fits

/-- Defects remain outside E. In particular the typing observation alone cannot exclude
this internal refusal defect, even at E = never. -/
theorem bad_shape_exit_fits (w : TypedWorld) (ty : EffTy) :
    Effect4.Program.Typed.Contracts.ExitFits w ty badShapeExit := rfl

theorem coarse_pure_bad_shape_is_typed (o : WorldOrder TypedWorld)
    (Ψ : Protocol TypedWorld RSig) (w : TypedWorld) (ty : EffTy) :
    Typed o Ψ w (fun w' ex => Effect4.Program.Typed.Contracts.ExitFits w' ty ex)
      (.pure badShapeExit) := .pure (bad_shape_exit_fits w ty)

def malformedWorld : TypedWorld :=
  { emptyWorld with state := { Stores.empty with refs := [Val.cell ⟨1⟩] } }

theorem empty_world_wf : emptyWorld.state.WF := Stores.empty_wf

/-- Existing declarations are all absent, so the world's conditional cell-preservation
clauses cannot reject a newly appended dangling value. -/
theorem malformed_extension : emptyWorld.le malformedWorld := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ h => h, ⟨by decide, Nat.le_refl _, fun _ h => h,
      Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩⟩
  · intro _ _ h
    cases h
  · intro _ _ h
    cases h
  · intro _ _ h
    cases h
  · constructor
    · intro _ _ h
      cases h.1
    · intro _ _ h
      cases h.1
  · intro _ _ _ h
    cases h

theorem malformed_extension_keeps_external_spellings :
    emptyWorld.state.externals.allocated = malformedWorld.state.externals.allocated := rfl

theorem malformed_world_not_wf : ¬ malformedWorld.state.WF := by
  intro h
  have bad := h.1 (Val.cell ⟨1⟩) (List.mem_cons_self)
  exact Bool.noConfusion bad

/-- Thus even the planned leHost refinement cannot by itself make the WF precondition
upward closed on arbitrary worlds. -/
theorem wf_not_monotone_even_with_equal_external_spellings :
    ¬ (∀ w w' : TypedWorld, w.le w' →
      w.state.externals.allocated = w'.state.externals.allocated →
      w.state.WF → w'.state.WF) := by
  intro h
  exact malformed_world_not_wf
    (h _ _ malformed_extension malformed_extension_keeps_external_spellings empty_world_wf)

def boolHeap : Stores := { Stores.empty with refs := [Val.bool false] }

theorem bool_allocation_succeeds :
    syncOpStep (.refMake (Val.bool false)) Stores.empty = some (boolHeap, Val.cell ⟨0⟩) := rfl

theorem bool_read_succeeds :
    syncOpStep (.refGet ⟨0⟩) boolHeap = some (boolHeap, Val.bool false) := rfl

theorem bool_heap_is_not_legacy_nat_heap : ¬ Effect4.Program.Stores.HeapNat boolHeap := by
  intro h
  exact Bool.noConfusion (h (Val.bool false) List.mem_cons_self)

#print axioms higherOrder_certificate_applies
#print axioms not_every_type_is_closed
#print axioms open_reference_type_shape_admitted
#print axioms typed_at_false_with_impossible_post
#print axioms impossible_post_has_no_answer
#print axioms inhabited_post_has_answer
#print axioms typed_at_true_with_inhabited_post
#print axioms pure_false_rejected
#print axioms checker_accepts_static_nat_environment
#print axioms runtime_environment_returns_bool
#print axioms runtime_bool_does_not_fit_static_nat
#print axioms matching_runtime_environment_returns_nat
#print axioms unchecked_environment_produces_open_type
#print axioms checker_path_is_only_a_diagnostic_location
#print axioms immutable_point_can_name_no_node
#print axioms missing_node_refuses_at_reference_interpreter
#print axioms root_address_is_a_positive_control
#print axioms forged_handle_exit_fits
#print axioms forged_handle_does_not_exist
#print axioms coarse_pure_forged_handle_is_typed
#print axioms bad_shape_exit_fits
#print axioms coarse_pure_bad_shape_is_typed
#print axioms malformed_extension
#print axioms malformed_world_not_wf
#print axioms wf_not_monotone_even_with_equal_external_spellings
#print axioms bool_allocation_succeeds
#print axioms bool_read_succeeds
#print axioms bool_heap_is_not_legacy_nat_heap
#print axioms open_reference_type_not_closed
#print axioms empty_world_wf
#print axioms malformed_extension_keeps_external_spellings
end FoundationsProtocolAdmissionProbe
