import Effect4.Laws.Program.Typed.Membership

/-!
# Verifier of seat TYPES (formal pass, 2026-10-01): the `handle` former is inhabited at every target

Research probe, outside every root; nothing imports it.

The seat's probe B (`InhabitedProbe.lean`) sets `inhabitedAlg.ty_handle _ := true` and proves the
fiber, cell and deferred formers inhabited in some world, but not the reserved/external `handle`
former, which `Fits` reads through `HandleFits` (`Laws/Program/Typed/Membership.lean:50-58`) and,
at the context spelling, through a context value (`:94-97`). If some target had no member,
`inhabited` would be unsound for admission in the complete direction (it would admit an empty
column). This probe closes that case: every target has a member in some world.

* `handle_inhabited` (proved): `∀ t, ∃ w v, Fits w v (.handle t)`, by the four internal spellings
  (`internalHandleTargets`, `Program/Typed.lean:12-13`) and the external allocation case.
-/

set_option autoImplicit false

namespace Research.TypesVerify.Handle

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

/-- One world that declares cell 0 at `nat`, deferred 0 at `(nat, nat)`, and has allocated one
external handle at target `t`. -/
def wAll (t : String) : Typed.World :=
  { initialWorld (EffTy.pure .unit) with
      state := { Stores.empty with externals := ⟨[], [t], none⟩ },
      «Π» := fun _ => some (.nat, .nat), Ρ := fun _ => some .nat }

theorem ref_inhabited (t : String) :
    Fits (wAll t) (Val.handle HandleKind.cell.byte 0) (.handle NativeOp.refTarget) :=
  ⟨rfl, .nat, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

theorem deferred_inhabited (t : String) :
    Fits (wAll t) (Val.handle HandleKind.promise.byte 0) (.handle NativeOp.deferredTarget) :=
  ⟨rfl, .nat, .nat, rfl, ⟨Ty.sub_refl _, Ty.sub_refl _⟩, ⟨Ty.sub_refl _, Ty.sub_refl _⟩⟩

theorem scope_inhabited (t : String) :
    Fits (wAll t) (Val.handle HandleKind.scope.byte 0) (.handle Ty.scopeTarget) :=
  (rfl : Ty.scopeTarget = Ty.scopeTarget)

theorem emptyCtx_keys : (Val.context emptyCtx).keys = [] := by decide

theorem context_inhabited (t : String) :
    Fits (wAll t) (Val.context emptyCtx) (.handle Ty.contextTarget) := by
  refine ⟨rfl, emptyCtx, ctxImage.ofVal_toVal emptyCtx, ?_, live_of_keys_nil emptyCtx_keys⟩
  intro key sv sty hget _
  have hnone : emptyCtx.services.getV key = none := rfl
  rw [hnone] at hget
  cases hget

theorem external_inhabited (t : String) (ht : externalHandleTarget t = true) :
    Fits (wAll t) (Val.handle HandleKind.external.byte 0) (.handle t) :=
  ⟨ht, rfl⟩

/-- **Every `handle` target has a member in some world (proved).** -/
theorem handle_inhabited (t : String) : ∃ (w : Typed.World) (v : Val), Fits w v (.handle t) := by
  cases hc : internalHandleTargets.contains t with
  | false =>
    have ht : externalHandleTarget t = true := by
      unfold externalHandleTarget
      rw [hc]
      rfl
    exact ⟨wAll t, _, external_inhabited t ht⟩
  | true =>
    have hm : t ∈ internalHandleTargets := List.contains_iff_mem.mp hc
    simp only [internalHandleTargets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact ⟨wAll NativeOp.refTarget, _, ref_inhabited NativeOp.refTarget⟩
    · exact ⟨wAll NativeOp.deferredTarget, _, deferred_inhabited NativeOp.deferredTarget⟩
    · exact ⟨wAll Ty.scopeTarget, _, scope_inhabited Ty.scopeTarget⟩
    · exact ⟨wAll Ty.contextTarget, _, context_inhabited Ty.contextTarget⟩

end Research.TypesVerify.Handle

#print axioms Research.TypesVerify.Handle.ref_inhabited
#print axioms Research.TypesVerify.Handle.deferred_inhabited
#print axioms Research.TypesVerify.Handle.scope_inhabited
#print axioms Research.TypesVerify.Handle.context_inhabited
#print axioms Research.TypesVerify.Handle.external_inhabited
#print axioms Research.TypesVerify.Handle.handle_inhabited
