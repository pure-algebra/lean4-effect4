import Effect4.Laws.Program.FinalizerSource
import Effect4.Laws.Program.CodeClosure.Correlated

/-!
Concept: scope-lifetime-finalization R11.
Question: cancellation slots serve FinalizerRun.once_placed_outside_census.
Consumer: full source template closure and actual Async parking debit.
The existing correlated code fold retains zero source weight on cancellation callbacks.
The compiler and stored embedding supply this annotation through their existing contracts.
This local annotation establishes neither history funding nor progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Async parking may copy a cancellation name, whose actual source weight is zero. -/
@[aesop norm simp (rule_sets := [Effect4.CodeClosure])]
def AsyncSlot (q : List Nat) : NCode → Prop
  | .async _ _ cancel => ∀ callback ∈ cancel, SourceScope.Opportunities.name q callback = 0
  | _ => True

abbrev CancelsAt (q : List Nat) := CodeClosure.Correlated (AsyncSlot q)

/-- The existing indexed compiler supplies cancellation slots without another syntax walk. -/
theorem cancel_contract (root : NativeEff) (q : List Nat) :
    CodeClosure.IndexedCompileContract root Unit (fun _ _ => True) (fun _ => CancelsAt q) where
  failure _ _ := trivial
  success _ _ _ _ _ _ _ := trivial
  body _ _ _ _ _ := trivial
  pure _ _ _ _ _ := trivial
  act _ _ _ _ _ := trivial
  operation _ _ _ _ _ _ _ _ _ _ := trivial
  asynchronous := by
    intro point row request _ _ _
    fun_cases asyncRoute row request point
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [SourceScope.Opportunities.name, badShape])
  bind := by intros; exact ⟨(), trivial, fun _ held => ⟨held, trivial⟩⟩
  caught := by intros; exact ⟨(), trivial, fun _ held => ⟨held, trivial⟩⟩
  caughtError := by intros; exact ⟨(), trivial, fun _ held => ⟨held, trivial⟩⟩
  matched := by intros; exact ⟨(), trivial, fun _ held => ⟨held, trivial⟩⟩
  finalized := by intros; exact ⟨(), trivial, fun _ held => ⟨held, trivial⟩⟩
  exited := by
    intros
    refine ⟨(), trivial, ?_⟩
    intro body held
    cases body.asExit?
    · exact ⟨held, trivial⟩
    · trivial
  restored := by intros; trivial
  definitions := by intros; trivial
  yielding := by intros; trivial
  awaited := by
    intro point term mode id exit _ _ _ _ _
    cases exit <;> trivial
  parked := by intros; trivial
  forkScoped := by intros; exact ⟨trivial, trivial⟩
  acquire := by intros; exact ⟨trivial, trivial⟩
  service := by intros; exact ⟨trivial, trivial⟩
  provideService := by intros; exact ⟨trivial, trivial⟩
  context := by
    intros
    refine ⟨(), trivial, ?_⟩
    intro body _
    cases body.asExit? with
    | none => exact ⟨trivial, trivial⟩
    | some exit => cases exit <;> trivial

/-- Every actual source compilation has zero source weight in its cancellation slots. -/
theorem compile_cancels (root : NativeEff) (q : List Nat) (effect : NativeEff) (point : Point)
    (found : Node.at_ (.eff root) point.path = some (.eff effect)) :
    CancelsAt q (compileEff effect point) :=
  CodeClosure.indexed_compile_closure (cancel_contract root q) effect point () found True.intro

/-- Every stored cancellation name has zero source weight, by agreement of the existing folds. -/
theorem embed_cancels (q : List Nat) (body : Program) : CancelsAt q (embed body) := by
  let alg : PrimAlgebra Name Thunk Val Err Defect FiberId Ann Prop :=
    CodeClosure.roleAlg (fun _ => True) (fun _ => True) (fun _ => True)
  let stored : PrimHom alg := by
    refine ⟨(fun body => CancelsAt q (embed body)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; apply propext
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [embed, alg, CodeClosure.roleAlg, SourceScope.Opportunities.name])
  let truth : PrimHom alg := by
    refine ⟨(fun _ => True),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; apply propext
    all_goals aesop (add norm simp [alg, CodeClosure.roleAlg])
  have same := (hom_eq_cata_prim stored body).trans (hom_eq_cata_prim truth body).symm
  exact same.mpr True.intro

end Effect4.Program.FinalizerSource
