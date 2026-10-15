import Effect4.Laws.Program.AnswerSlots.Stable
import Effect4.Laws.Program.AnswerSlots.InitializationProtocol
import Effect4.Laws.Machine.AnswerFlowEmbedding
import Effect4.Laws.Machine.AnswerFlowViews

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: one reference prefix and optional gate enter any certified stable source model.
Reach: certificates over the existing source, actual returned keys and uniform saved frames.
Limit: native action, scoped, park and admitted command producers remain separate.
Consumer: the crew, Atomic and Timeout initialized history instances.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- A gate certificate describes the actual source binder after the reference prefix. -/
structure Gate (root : NativeEff) (width : Nat) (bindings : List Val) where
  valueType : Ty
  errorType : Ty
  head : ∃ tail, Node.at_ (.eff root) (List.replicate width 1) =
    some (.eff (.bind (.perform (.deferredMakeOf valueType errorType) (.lit .unit)) tail))
  next : bindings.take width ++ [.promise ⟨0⟩] = bindings

/-- The initializer certificate is independent of the stable source's value and callback classes. -/
structure Spec where
  stable : StableSpec
  initialization : Initialization stable.root
  positive : 0 < initialization.width
  gate : Option (Gate stable.root initialization.width initialization.bindings)
  noGate : gate = none → initialization.bindings.take initialization.width = initialization.bindings
  laws : SourceScope.Fragment stable.root → StableLaws stable
  root_value : ∀ value, stable.value stable.rootKind value
  yield_code : ∀ priority, stable.code stable.rootKind (.yieldNowWith priority)
  sync_value : ∀ kind thunk value, stable.code kind (.sync thunk) → stable.value kind value
  entry : ∀ (_fragment : SourceScope.Fragment stable.root) (point : Point),
    SourceScope.At stable.root point → Prefix initialization.bindings point.env →
    point.path = List.replicate (initialization.width + (if gate.isSome then 1 else 0)) 1 →
    stable.code stable.rootKind (resolve stable.root point)

def Spec.root (spec : Spec) : NativeEff := spec.stable.root
def Spec.table (spec : Spec) : RowTable := spec.stable.table
def Spec.bindings (spec : Spec) : List Val := spec.initialization.bindings
def Spec.gateNeed (spec : Spec) : Nat := if spec.gate.isSome then 1 else 0

structure World where
  owner : FiberId
  state : Stores

inductive Kind (StableKind : Type)
  | stable (kind : StableKind)
  | allocated (index : Nat)
  | gate
  | yielded (refs deferred : Nat)

def Ready (spec : Spec) (world : World) : Prop :=
  spec.initialization.width ≤ world.state.refs.length ∧ spec.gateNeed ≤ world.state.deferreds.cells.length

instance (spec : Spec) (world : World) : Decidable (Ready spec world) := by
  unfold Ready
  infer_instance

def Phase (spec : Spec) (world : World) : Prop := world.owner = ⟨0⟩ ∨ Ready spec world

def Future (first last : World) : Prop :=
  first.owner = last.owner ∧ first.state.refs.length ≤ last.state.refs.length ∧
    first.state.deferreds.cells.length ≤ last.state.deferreds.cells.length

def RootStage (spec : Spec) (world : World) (index : Nat) (point : Point) : Prop :=
  index ≤ spec.initialization.width ∧ world.owner = ⟨0⟩ ∧ point.path = List.replicate index 1 ∧
    point.env = spec.bindings.take index ∧ world.state.refs.length = index ∧
    world.state.deferreds.cells.length = 0 ∧ SourceScope.At spec.root point

def Active (spec : Spec) (index : Nat) : Prop := index < spec.initialization.width ∨ spec.gate.isSome = true

def ValueAt (spec : Spec) (world : World) : Kind spec.stable.Kind → Val → Prop
  | .stable kind, value => Phase spec world ∧ spec.stable.value kind value
  | .allocated index, value => Phase spec world ∧ value = .cell ⟨index⟩ ∧
      world.state.refs.length = index + 1 ∧ world.state.deferreds.cells.length = 0
  | .gate, value => value = .promise ⟨0⟩ ∧ Ready spec world
  | .yielded refs deferred, value => Phase spec world ∧ value = .unit ∧
      world.state.refs.length = refs ∧ world.state.deferreds.cells.length = deferred ∧ ¬ Ready spec world

inductive CodeAt (spec : Spec) : World → Kind spec.stable.Kind → NCode → Prop
  | success {world kind value} (good : ValueAt spec world kind value) : CodeAt spec world kind (.success value)
  | failure {world kind cause} (phase : Phase spec world) : CodeAt spec world kind (.failure cause)
  | initial {world index point} (stage : RootStage spec world index point) (active : Active spec index) :
      CodeAt spec world (.stable spec.stable.rootKind) (resolve spec.root point)
  | allocating {world index point} (small : index < spec.initialization.width)
      (stage : RootStage spec world index point) :
      CodeAt spec world (.allocated index) (.sync (.op (.refMake (spec.initialization.initial index))))
  | gateAllocating {world point} (stage : RootStage spec world spec.initialization.width point)
      (available : spec.gate.isSome = true) : CodeAt spec world .gate (.sync (.op .deferredMake))
  | stable {world kind program} (ready : Ready spec world) (owned : spec.stable.code kind program) :
      CodeAt spec world (.stable kind) program
  | frontier {world kind point} (zero : point.fuel = 0) (phase : Phase spec world) :
      CodeAt spec world kind (Effect4.Program.frontier point)
  | yielding {world priority refs deferred} (phase : Phase spec world)
      (refsEq : world.state.refs.length = refs) (deferredEq : world.state.deferreds.cells.length = deferred)
      (pending : ¬ Ready spec world) :
      CodeAt spec world (.yielded refs deferred) (.yieldNowWith priority)
  | bound {world input output body name} (first : CodeAt spec world input body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
        ValueAt spec nextWorld input answer → CodeAt spec nextWorld output
          ((interpAt spec.root view spec.table).contA name answer)) :
      CodeAt spec world output (.onSuccess body name)
  | yieldThen {world kind priority next} (phase : Phase spec world) (owned : CodeAt spec world kind next) :
      CodeAt spec world kind (.onSuccessConst (.yieldNowWith priority) next)

theorem ready_future (spec : Spec) (first last : World) (future : Future first last) (ready : Ready spec first) :
    Ready spec last := ⟨Nat.le_trans ready.1 future.2.1, Nat.le_trans ready.2 future.2.2⟩

theorem phase_future (spec : Spec) (first last : World) (future : Future first last) (phase : Phase spec first) :
    Phase spec last := by
  rcases phase with owner | ready
  · exact .inl (future.1.symm.trans owner)
  · exact .inr (ready_future spec first last future ready)

def model (spec : Spec) (completed : List (FiberId × ExitV)) :
    AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)
      World (Kind spec.stable.Kind) where
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

theorem embedding (spec : Spec) (completed : List (FiberId × ExitV)) :
    AnswerFlow.FamilyEmbedding (spec.stable.model completed) (model spec completed)
      (fun _ => ()) Kind.stable (Ready spec) where
  ready_future := ready_future spec
  future := fun _ _ _ _ => trivial
  value_read := fun _ _ _ _ good => good.2
  value_write := fun _ _ _ ready good => ⟨.inr ready, good⟩
  cause_read := fun _ _ _ _ _ => trivial
  cause_write := fun _ _ _ ready _ => .inr ready
  code := fun _ _ _ ready good => .stable ready good
  finalizer := fun _ _ _ _ => rfl

def Semantic (spec : Spec) :=
  AnswerFlow.ViewSavedAt (fun view => model spec view)
    (fun view => (interpAt spec.root view spec.table).toPrimInterp)

def Edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) :=
  AnswerFlow.EmbeddedEdgeOver (fun (_ : World) => ()) Kind.stable (Ready spec)
    (Semantic spec) (spec.laws fragment).Edge

theorem family (spec : Spec) (fragment : SourceScope.Fragment spec.root) (completed : List (FiberId × ExitV)) :
    AnswerFlow.SavedFamily (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp (Edge spec fragment) :=
  AnswerFlow.FamilyEmbedding.family_over (interpAt spec.root completed spec.table).toPrimInterp
    (embedding spec completed) (Semantic spec) (spec.laws fragment).Edge
    (AnswerFlow.ViewSavedAt.family (fun view => model spec view)
      (fun view => (interpAt spec.root view spec.table).toPrimInterp) completed)
    ((spec.laws fragment).family completed)
end Effect4.Program.AnswerSlots.AllocationAdapter
