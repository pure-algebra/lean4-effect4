import Effect4.Laws.Program.FinalizerNativeScoped
import Effect4.Laws.Program.FinalizerNativeScopeClosure
import Effect4.Laws.Program.PlaceFunding.Native

/-!
Concept: scope-lifetime-finalization R11.
Question: actual charged iterations retain and spend the full finalizer source annotation.
Consumer: the finalizer source command invariant.
The common iteration transfer retains real race and command places.
Complete history funding remains separate from these local results.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Loop-top interruption replaces only the current source by a terminal failure. -/
theorem charged_frame (q : List Nat) (fiber : SourceScope.SourceFiber) (held : TemplateFrame q fiber.frame) :
    TemplateFrame q (countOp (runloopTop fiber)).frame := by
  unfold countOp runloopTop
  split
  · exact ⟨⟨trivial, trivial, trivial⟩, held.2⟩
  · exact held

/-- Injected yielding retains its deferred source as the actual constant child. -/
theorem yield_template (q : List Nat) (code : NCode) (held : TemplateAt q code) :
    TemplateAt q (.onSuccessConst (.yieldNowWith 0) code) := by
  aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt])

/-- Full source accounting instantiates the common actual charged-iteration transfer. -/
theorem iteration_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : TemplateFrame q fiber.frame) (scopes : ScopesAt q machine.state.scopes)
    (unique : (machine.races.map Race.id).Nodup) :
    letI := evaluatorFor root table
    (ledger root q).IterDebit machine fiber (Machine.iteration (interpOf root table) machine fiber yielding) := by
  have charged := charged_frame q fiber held
  apply PlaceFunding.iteration_debit_at (events root q) (frameModel root q) (fun _ => rfl)
    (fun _ => by simp only [frameModel, current, cata_prim, Nat.zero_add]; exact Nat.le_refl _)
    root table machine fiber yielding
    (fun m f => TemplateFrame q f.frame ∧ ScopesAt q m.state.scopes ∧ (m.races.map Race.id).Nodup)
  · exact ⟨charged, scopes, unique⟩
  · exact ⟨⟨yield_template q _ charged.1, charged.2⟩, scopes, unique⟩
  · intro next row flag supplied
    exact native_debit root q table placed next row flag (template_frame_at q _ supplied.1)
      supplied.1.1 supplied.2.1 supplied.2.2

/-- The real charged iteration retains full templates at its returned frame and stored rows. -/
theorem iteration_frames (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : TemplateFrame q fiber.frame) (scopes : ScopesAt q machine.state.scopes)
    (rows : ∀ row ∈ machine.fibers, TemplateFrame q row.frame) :
    letI := evaluatorFor root table
    let next := Machine.iteration (interpOf root table) machine fiber yielding
    TemplateFrame q next.fiber.frame ∧ ∀ row ∈ next.machine.fibers, TemplateFrame q row.frame := by
  letI := evaluatorFor root table
  have charged := charged_frame q fiber held
  unfold Machine.iteration
  dsimp only
  cases injected : injectYield machine (countOp (runloopTop fiber)) yielding with
  | none =>
    exact ⟨native_frame root q table placed machine _ yielding charged scopes,
      native_rows root q table machine _ yielding charged rows⟩
  | some next =>
    unfold injectYield at injected
    split at injected
    · cases injected
      have wrapped : TemplateFrame q {(countOp (runloopTop fiber)).frame with
          current := Prim.onSuccessConst (Prim.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current} :=
        ⟨yield_template q _ charged.1, charged.2⟩
      exact ⟨native_frame root q table placed _ _ true wrapped scopes,
        native_rows root q table _ _ true wrapped rows⟩
    · cases injected

end Effect4.Program.FinalizerSource
