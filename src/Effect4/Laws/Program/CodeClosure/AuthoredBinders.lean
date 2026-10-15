import Effect4.Laws.Program.CodeClosure.Correlated
import Effect4.Laws.Program.CodeClosure.Compile
import Effect4.Laws.Program.CodeClosure.Qualified.Callbacks

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, at the actual worker binder and feeder entry push.
The existing correlated fold retains the actual compiled body beside its source callback.
This source certificate establishes neither custody nor command-history preservation.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.AuthoredBinders
open Effect4 Effect4.Machine Effect4.Program

/-- A source success callback keeps the actual first child compiled at that same source point. -/
def Body (root : NativeEff) : NCode → Prop
  | .onSuccess body callback => ∀ point, callback = .cont point →
      ∃ first rest, Node.at_ (.eff root) point.path = some (.eff (.bind first rest)) ∧
        body = compileEff first (point.child 0)
  | _ => True

abbrev Code (root : NativeEff) := Correlated (Body root)

/-- The actual constructor builder reads the equality supplied by the existing compiler induction. -/
theorem compile_contract (root : NativeEff) :
    ActualIndexedCompileContract root Unit (fun _ _ => True) (fun _ => Code root) where
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
    all_goals aesop (add norm simp [Correlated, cata_prim, correlatedAlg, Body, badShape])
  bind := by
    intro point first rest _ found _
    refine ⟨(), trivial, ?_⟩
    intro body actual held
    refine ⟨held, ?_⟩
    intro samePoint same
    cases same
    rw [correlated_rebuild]
    exact ⟨first, rest, found, actual⟩
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
    refine ⟨True.intro, ?_⟩
    intro point same
    cases same
  acquire := by
    intros
    refine ⟨True.intro, ?_⟩
    intro point same
    cases same
  service := by
    intros
    refine ⟨True.intro, ?_⟩
    intro point same
    cases same
  provideService := by
    intros
    refine ⟨True.intro, ?_⟩
    intro point same
    cases same
  context := by
    intros
    refine ⟨(), trivial, ?_⟩
    intro body _
    cases body.asExit? with
    | none =>
      refine ⟨True.intro, ?_⟩
      intro point same
      cases same
    | some exit => cases exit <;> trivial

/-- The sole compiler induction retains the actual source body, for every authored node. -/
theorem compile (root : NativeEff) (effect : NativeEff) (point : Point)
    (found : Node.at_ (.eff root) point.path = some (.eff effect)) : Code root (compileEff effect point) :=
  actual_indexed_compile_closure (compile_contract root) effect point () found True.intro

/-- Actual source resolution retains the same body and callback point. -/
theorem resolve (root : NativeEff) (point : Point) : Code root (Effect4.Program.resolve root point) := by
  unfold Effect4.Program.resolve
  split
  · exact compile root _ point ‹_›
  · trivial

/-- Stored names cannot introduce native source continuation points. -/
theorem embed (root : NativeEff) (body : Program) : Code root (Effect4.Program.embed body) := by
  let alg : PrimAlgebra Name Thunk Val Err Defect FiberId Ann Prop :=
    roleAlg (fun _ => True) (fun _ => True) (fun _ => True)
  let stored : PrimHom alg := by
    refine ⟨(fun body => Code root (Effect4.Program.embed body)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; apply propext
    all_goals aesop (add norm simp [Correlated, cata_prim, correlatedAlg, Body, Effect4.Program.embed, alg, roleAlg])
  let truth : PrimHom alg := by
    refine ⟨(fun _ => True),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; apply propext
    all_goals aesop (add norm simp [alg, roleAlg])
  have same := (hom_eq_cata_prim stored body).trans (hom_eq_cata_prim truth body).symm
  exact same.mpr True.intro

/-- Broad direct-source leaves supply the existing native callback contract. -/
theorem broad_contract (root : NativeEff) :
    Qualified.Contract root (fun _ => True) (fun _ => True) (fun _ => True) := by
  have transport : Qualified.Transport (fun _ => True) (fun _ => True) :=
    ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ => trivial⟩
  have operations : ∀ op, Qualified.OpAt (fun _ => True) (fun _ => True) (fun _ => True) op := by
    intro op
    cases op
    case scopeAdd scope fin => cases fin <;> trivial
    all_goals trivial
  exact { compilation := Qualified.compile_contract root _ _ _ transport
            (fun _ _ _ _ op _ _ _ _ => operations op)
          child := fun _ _ => trivial
          childWith := fun _ _ _ => trivial
          capture := fun _ _ _ => trivial }

/-- Native builders preserve authored correlations without fabricating a source continuation. -/
theorem builders (root : NativeEff) :
    Qualified.ValueBuilders (fun _ => True) (fun _ => True) (fun _ => True) (Code root) where
  success _ := trivial
  failure _ := trivial
  sync _ _ := trivial
  suspend _ _ := trivial
  withFiber _ _ := trivial
  onSuccess _ name held _ native := by
    refine ⟨held, ?_⟩
    intro point same
    exact False.elim (native point same)
  onSuccessConst _ _ first next := ⟨first, next, trivial⟩
  onFailure _ _ held _ := ⟨held, trivial⟩
  onSuccessAndFailure _ _ _ held _ _ := ⟨held, trivial⟩
  onExit _ _ _ held _ := ⟨held, trivial⟩
  exitFrame _ held := ⟨held, trivial⟩
  setInterruptible _ := trivial
  iterator _ _ _ := trivial
  whileLoop _ _ _ := trivial
  async _ _ _ _ _ := trivial
  asyncFinalizer _ _ := trivial

/-- Actual compiler and stored leaves instantiate the shared callback producer. -/
theorem leaves (root : NativeEff) :
    Qualified.ValueLeaves root (fun _ => True) (fun _ => True) (fun _ => True) (Code root) where
  argument p index value _ := resolve root (p.childWith index value)
  child p index _ := resolve root (p.child index)
  region := by
    intro region held
    cases region
    case program point => exact resolve root point
    all_goals exact held.elim
  stored name value _ := embed root (Effect4.Machine.contAOf name value)
  finalizer fin exit _ := embed root (finProgram fin exit)

/-- The existing value-callback walk retains actual authored binder bodies. -/
theorem value_callback (root : NativeEff) (name : EffName) (value : Val)
    (owned : Qualified.NameAt (fun _ => True) (fun _ => True) (fun _ => True) name) :
    Code root (contAOf root name value) :=
  Qualified.contA_with root _ _ _ (broad_contract root) (Code root) (builders root) (leaves root) name value owned

/-- The actual native push exposes the existing source binder and its real compiled first child. -/
theorem body (root : NativeEff) (point : Point) (firstCode : NCode)
    (held : Code root (.onSuccess firstCode (.cont point))) :
    ∃ first rest, Node.at_ (.eff root) point.path = some (.eff (.bind first rest)) ∧
      firstCode = compileEff first (point.child 0) := by
  have actual := held.2 point rfl
  rw [correlated_rebuild] at actual
  exact actual
end Effect4.Program.CodeClosure.AuthoredBinders
