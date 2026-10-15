import Effect4.Laws.Program.AnswerSlots.TypedHead
import Effect4.Laws.Machine.AnswerFlowEmbedding
import Effect4.Laws.Machine.AnswerFlowViewsRefined

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the two crews share one initialization protocol and the checked protected stable graph.
Reach: certified leading reference allocations, one gate allocation and future store growth.
Limit: the native evaluator, exclusivity and guarded command history remain separate producers.
Consumer: initialized Workers and QueueWorkers cleanup history.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The stable source certificate joins the actual reference and gate initialization shapes. -/
structure Spec extends Typed.Spec where
  initialization : Initialization root
  bindings_eq : initialization.bindings = bindings
  gateValue : Ty
  gateError : Ty
  gate_head : ∃ tail, Node.at_ (.eff root) (List.replicate initialization.width 1) =
    some (.eff (.bind (.perform (.deferredMakeOf gateValue gateError) (.lit .unit)) tail))
  gate_next : bindings.take initialization.width ++ [.promise ⟨0⟩] = bindings

/-- Each frame reads its actual owner and shared native store. -/
structure World where
  owner : FiberId
  state : Stores

/-- Transient allocation and ignored yield answers coexist with protected stable answer classes. -/
inductive Kind
  | stable (kind : Typed.Kind)
  | allocated (index : Nat)
  | gate
  | yielded (refs deferred : Nat)

def Ready (spec : Spec) (world : World) : Prop :=
  spec.initialization.width ≤ world.state.refs.length ∧ 1 ≤ world.state.deferreds.cells.length

instance (spec : Spec) (world : World) : Decidable (Ready spec world) := by
  unfold Ready
  infer_instance

def Phase (spec : Spec) (world : World) : Prop := world.owner = ⟨0⟩ ∨ Ready spec world

def Future (first last : World) : Prop :=
  first.owner = last.owner ∧ first.state.refs.length ≤ last.state.refs.length ∧
    first.state.deferreds.cells.length ≤ last.state.deferreds.cells.length

/-- Initialization retains its exact source environment and current allocation counts. -/
def RootStage (spec : Spec) (world : World) (index : Nat) (point : Point) : Prop :=
  index ≤ spec.initialization.width ∧ world.owner = ⟨0⟩ ∧ point.path = List.replicate index 1 ∧
    point.env = spec.bindings.take index ∧ world.state.refs.length = index ∧
    world.state.deferreds.cells.length = 0 ∧ SourceScope.At spec.root point

/-- An allocation class describes the actual returned key and post-operation store lengths. -/
def ValueAt (spec : Spec) (world : World) : Kind → Val → Prop
  | .stable kind, value => Ready spec world ∧ Typed.ValueAt kind value
  | .allocated index, value => Phase spec world ∧ value = .cell ⟨index⟩ ∧
      world.state.refs.length = index + 1 ∧ world.state.deferreds.cells.length = 0
  | .gate, value => value = .promise ⟨0⟩ ∧ Ready spec world
  | .yielded refs deferred, _ => Phase spec world ∧
      world.state.refs.length = refs ∧ world.state.deferreds.cells.length = deferred ∧ ¬ Ready spec world

/-- The existing native code carries transient initialization or protected stable source evidence. -/
inductive CodeAt (spec : Spec) : World → Kind → NCode → Prop
  | success {world kind value} (good : ValueAt spec world kind value) : CodeAt spec world kind (.success value)
  | failure {world kind cause} (phase : Phase spec world) : CodeAt spec world kind (.failure cause)
  | initial {world index point} (stage : RootStage spec world index point) :
      CodeAt spec world (.stable .root) (resolve spec.root point)
  | allocating {world index point} (small : index < spec.initialization.width)
      (stage : RootStage spec world index point) :
      CodeAt spec world (.allocated index) (.sync (.op (.refMake (spec.initialization.initial index))))
  | gateAllocating {world point} (stage : RootStage spec world spec.initialization.width point) :
      CodeAt spec world .gate (.sync (.op .deferredMake))
  | stable {world kind program} (ready : Ready spec world) (owned : Typed.CodeAt spec.toSpec kind program) :
      CodeAt spec world (.stable kind) program
  | frontier {world kind point} (zero : point.fuel = 0) (phase : Phase spec world) :
      CodeAt spec world kind (Effect4.Program.frontier point)
  | yielding {world priority refs deferred} (phase : Phase spec world)
      (refsEq : world.state.refs.length = refs) (deferredEq : world.state.deferreds.cells.length = deferred)
      (pending : ¬ Ready spec world) :
      CodeAt spec world (.yielded refs deferred) (.yieldNowWith priority)
  | reading {world refs deferred cell} (phase : Phase spec world)
      (refsEq : world.state.refs.length = refs) (deferredEq : world.state.deferreds.cells.length = deferred)
      (pending : ¬ Ready spec world) :
      CodeAt spec world (.yielded refs deferred) (.sync (.store (.op (.refGet cell))))
  | bound {world input output body name} (first : CodeAt spec world input body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
        ValueAt spec nextWorld input answer → CodeAt spec nextWorld output
          ((interpAt spec.root view spec.table).contA name answer)) :
      CodeAt spec world output (.onSuccess body name)
  | yieldThen {world kind priority next} (phase : Phase spec world) (owned : CodeAt spec world kind next) :
      CodeAt spec world kind (.onSuccessConst (.yieldNowWith priority) next)

/-- Readiness remains true when reference and deferred stores grow. -/
theorem ready_future (spec : Spec) (first last : World) (future : Future first last) (ready : Ready spec first) :
    Ready spec last := ⟨Nat.le_trans ready.1 future.2.1, Nat.le_trans ready.2 future.2.2⟩

/-- An existing frame remains the root initializer or belongs to the ready stable phase. -/
theorem phase_future (spec : Spec) (first last : World) (future : Future first last) (phase : Phase spec first) :
    Phase spec last := by
  rcases phase with owner | ready
  · exact .inl (future.1.symm.trans owner)
  · exact .inr (ready_future spec first last future ready)

/-- The initialized model uses the actual installed native finalizer and restore wrapper. -/
def model (spec : Spec) (completed : List (FiberId × ExitV)) :
    AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)
      World Kind where
  future := Future
  future_refl _ := ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩
  future_trans _ _ _ first last :=
    ⟨first.1.trans last.1, Nat.le_trans first.2.1 last.2.1, Nat.le_trans first.2.2 last.2.2⟩
  value := ValueAt spec
  cause world _ _ := Phase spec world
  code := CodeAt spec
  finalizer := fun _ name exit => ((interpAt spec.root completed spec.table).finalizerProgram name exit).map
    (finalizerCode (interpAt spec.root completed spec.table) exit)
  success := fun _ _ _ good => .success good
  failure := fun _ _ _ good => .failure good

/-- The ready phase embeds the checked stable graph without rebuilding its callbacks or recursive edges. -/
theorem embedding (spec : Spec) (completed : List (FiberId × ExitV)) :
    AnswerFlow.FamilyEmbedding (Typed.model spec.toSpec completed) (model spec completed)
      (fun _ => ()) Kind.stable (Ready spec) where
  ready_future := ready_future spec
  future := fun _ _ _ _ => trivial
  value_read := fun _ _ _ _ good => good.2
  value_write := fun _ _ _ ready good => ⟨ready, good⟩
  cause_read := fun _ _ _ _ _ => trivial
  cause_write := fun _ _ _ ready _ => .inr ready
  code := fun _ _ _ ready good => .stable ready good
  finalizer := fun _ _ _ _ => rfl

/-- Initializer callbacks retain their same answer endpoints at every completed-fiber view. -/
def ScopedExitTag (spec : Spec) (world : World) (input output : Kind) (frame : NCode) : Prop :=
  ∀ body previous scope flag, frame = .onExit body (.scopedExit previous scope) flag →
    input = .stable .root ∧ output = .stable .root ∧ Ready spec world

def Semantic (spec : Spec) (world : World) (input output : Kind) (frame : NCode) : Prop :=
  AnswerFlow.ViewSavedAt (fun view => model spec view)
    (fun view => (interpAt spec.root view spec.table).toPrimInterp) world input output frame ∧
      ScopedExitTag spec world input output frame

/-- Initialization and stable saved edges retain uniform callbacks under actual view changes. -/
def Edge (spec : Spec) (_completed : List (FiberId × ExitV)) :=
  AnswerFlow.EmbeddedEdgeOver (fun (_ : World) => ()) Kind.stable (Ready spec)
    (Semantic spec) (Typed.Edge spec.toSpec [])

/-- Native scoped cleanup reads the actual source-generated stable endpoint and ready phase. -/
theorem scoped_edge (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool)
    (held : Edge spec view world input output (.onExit body (.scopedExit previous scope) flag)) :
    input = .stable .root ∧ output = .stable .root ∧ Ready spec world := by
  generalize same : Prim.onExit body (.scopedExit previous scope) flag = frame at held
  cases held with
  | saved owned => exact owned.2 body previous scope flag same.symm
  | mapped ready owned =>
    cases same
    obtain ⟨rfl, rfl⟩ := Typed.scoped_edge spec.toSpec [] () _ _ body previous scope flag owned
    exact ⟨rfl, rfl, ready⟩

/-- The actual view projects both uniform initializer and stable saved families. -/
theorem family (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV)) :
    AnswerFlow.SavedFamily (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp (Edge spec completed) :=
  AnswerFlow.FamilyEmbedding.family_over (interpAt spec.root completed spec.table).toPrimInterp
    (embedding spec completed) (Semantic spec) (Typed.Edge spec.toSpec completed)
    (AnswerFlow.ViewSavedAt.refined_family (fun view => model spec view)
      (fun view => (interpAt spec.root view spec.table).toPrimInterp) (Semantic spec)
      (fun _ _ _ _ held => held.1) completed)
    (Typed.family spec.toSpec fragment completed)
end Effect4.Program.AnswerSlots.Initialized
