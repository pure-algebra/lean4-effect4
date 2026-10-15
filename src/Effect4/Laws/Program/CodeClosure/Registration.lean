import Effect4.Laws.Program.CodeClosure.Correlated
import Effect4.Laws.Program.CodeClosure.Compile

/-!
Concept: scope-lifetime-finalization R11.
Question: source compilation retains the exact registration template.
Consumer: full-source finalizer sequencing and its release custody.
The existing indexed compiler supplies the constructor correlation instance.
Stored names cannot mint a native registration callback.
These local facts establish no history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure
open Effect4 Effect4.Machine Effect4.Program

/-- The compiler creates ordinary callbacks; native acquisition creates registration later. -/
theorem registration_compile_contract (root : NativeEff) :
    IndexedCompileContract root Unit (fun _ _ => True) (fun _ => RegistrationCode) where
  failure _ _ := trivial
  success _ _ _ _ _ _ _ := trivial
  body _ _ _ _ _ := trivial
  pure _ _ _ _ _ := trivial
  act _ _ _ _ _ := trivial
  operation _ _ _ _ _ _ _ _ _ _ := trivial
  asynchronous := by
    intro point row request _ _ _
    unfold asyncRoute
    repeat' split
    all_goals aesop (add norm simp [Correlated, cata_prim, correlatedAlg, RegistrationBody, badShape])
  bind := by
    intros
    refine ⟨(), trivial, ?_⟩
    intro body held
    exact registration_success body _ held (by intro acquired fin same; cases same)
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
  forkScoped := by
    intros
    exact registration_success _ _ True.intro (by intro acquired fin same; cases same)
  acquire := by
    intros
    exact registration_success _ _ True.intro (by intro acquired fin same; cases same)
  service := by
    intros
    exact registration_success _ _ True.intro (by intro acquired fin same; cases same)
  provideService := by
    intros
    exact registration_success _ _ True.intro (by intro acquired fin same; cases same)
  context := by
    intros
    refine ⟨(), trivial, ?_⟩
    intro body _
    cases body.asExit? with
    | none => exact registration_success _ _ True.intro (by intro acquired fin same; cases same)
    | some exit => cases exit <;> trivial

/-- The registration template follows through the existing compiler induction. -/
theorem registration_compile (root : NativeEff) (effect : NativeEff) (point : Point)
    (found : Node.at_ (.eff root) point.path = some (.eff effect)) :
    RegistrationCode (compileEff effect point) :=
  indexed_compile_closure (registration_compile_contract root) effect point () found True.intro

/-- Resolution retains the registration template at every actual source node. -/
theorem registration_resolve (root : NativeEff) (point : Point) : RegistrationCode (resolve root point) := by
  unfold resolve
  split
  · exact registration_compile root _ point ‹_›
  · trivial

/-- Stored code has no native registration callback, by agreement of its existing folds. -/
theorem registration_embed (body : Program) : RegistrationCode (embed body) := by
  let alg : PrimAlgebra Name Thunk Val Err Defect FiberId Ann Prop :=
    roleAlg (fun _ => True) (fun _ => True) (fun _ => True)
  let stored : PrimHom alg := by
    refine ⟨(fun body => RegistrationCode (embed body)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; apply propext
    all_goals aesop (add norm simp [Correlated, cata_prim, correlatedAlg, RegistrationBody, embed, alg, roleAlg])
  let truth : PrimHom alg := by
    refine ⟨(fun _ => True),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; apply propext
    all_goals aesop (add norm simp [alg, roleAlg])
  have same := (hom_eq_cata_prim stored body).trans (hom_eq_cata_prim truth body).symm
  exact same.mpr True.intro

end Effect4.Program.CodeClosure
