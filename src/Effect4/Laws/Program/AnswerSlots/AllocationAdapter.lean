import Effect4.Laws.Program.AnswerSlots.Stable
import Effect4.Laws.Program.AnswerSlots.InitializationExact
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
  entered : Bool := false

inductive Kind (StableKind : Type)
  | stable (kind : StableKind)
  | allocated (index : Nat)
  | gate
  | yielded (refs deferred : Nat)

def Ready (spec : Spec) (world : World) : Prop :=
  world.entered = true ∧ spec.initialization.width ≤ world.state.refs.length ∧
    spec.gateNeed ≤ world.state.deferreds.cells.length

instance (spec : Spec) (world : World) : Decidable (Ready spec world) := by
  unfold Ready
  infer_instance

def Phase (spec : Spec) (world : World) : Prop := world.owner = ⟨0⟩ ∨ Ready spec world

/-- The independent entry flag advances only when an actual entry marker is consumed. -/
structure Future (first last : World) : Prop where
  owner : first.owner = last.owner
  refs : first.state.refs.length ≤ last.state.refs.length
  deferreds : first.state.deferreds.cells.length ≤ last.state.deferreds.cells.length
  entered : first.entered = true → last.entered = true

/-- Exact pending heap contents remain independent of the code retained after an interruption. -/
def HeapPrefix (spec : Spec) (state : Stores) : Prop :=
  state.refs = Initialization.values spec.initialization state.refs.length ∧
    state.refs.length ≤ spec.initialization.width ∧ state.deferreds.cells.length ≤ spec.gateNeed

/-- A live allocation stage retains the actual root point and exact initial heap. -/
structure RootStage (spec : Spec) (world : World) (index : Nat) (point : Point) : Prop where
  owner : world.owner = ⟨0⟩
  stage : Initialization.ExactStage spec.initialization index point world.state.refs
  deferreds : world.state.deferreds.cells.length = 0
  pending : world.entered = false

/-- Entry retains the actual continuation point and completed initial reference heap. -/
structure Entry (spec : Spec) (world : World) (point : Point) : Prop where
  owner : world.owner = ⟨0⟩
  source : SourceScope.At spec.root point
  path : point.path = List.replicate (spec.initialization.width + spec.gateNeed) 1
  env : point.env = spec.bindings
  contents : world.state.refs = Initialization.values spec.initialization spec.initialization.width
  cells : spec.initialization.width ≤ world.state.refs.length ∧
    spec.gateNeed ≤ world.state.deferreds.cells.length
  pending : world.entered = false

def Active (spec : Spec) (index : Nat) : Prop := index < spec.initialization.width ∨ spec.gate.isSome = true

def ValueAt (spec : Spec) (world : World) : Kind spec.stable.Kind → Val → Prop
  | .stable kind, value => Ready spec world ∧ spec.stable.value kind value
  | .allocated index, value => Phase spec world ∧ value = .cell ⟨index⟩ ∧
      world.state.refs.length = index + 1 ∧ world.state.deferreds.cells.length = 0 ∧
      world.state.refs = Initialization.values spec.initialization (index + 1) ∧ world.entered = false
  | .gate, value => Phase spec world ∧ value = .promise ⟨0⟩ ∧
      (spec.initialization.width ≤ world.state.refs.length ∧ spec.gateNeed ≤ world.state.deferreds.cells.length) ∧
      world.state.refs = Initialization.values spec.initialization spec.initialization.width ∧ world.entered = false
  | .yielded refs deferred, _ => Phase spec world ∧
      world.state.refs.length = refs ∧ world.state.deferreds.cells.length = deferred ∧ ¬ Ready spec world ∧
      world.state.refs = Initialization.values spec.initialization refs ∧ world.entered = false

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
  | entered {world point} (fragment : SourceScope.Fragment spec.root) (entry : Entry spec world point) :
      CodeAt spec world (.stable spec.stable.rootKind) (resolve spec.root point)
  | stable {world kind program} (ready : Ready spec world) (owned : spec.stable.code kind program) :
      CodeAt spec world (.stable kind) program
  | frontier {world kind point} (zero : point.fuel = 0) (phase : Phase spec world) :
      CodeAt spec world kind (Effect4.Program.frontier point)
  | yielding {world priority refs deferred} (phase : Phase spec world)
      (refsEq : world.state.refs.length = refs) (deferredEq : world.state.deferreds.cells.length = deferred)
      (pending : ¬ Ready spec world)
      (contents : world.state.refs = Initialization.values spec.initialization refs)
      (entered : world.entered = false) :
      CodeAt spec world (.yielded refs deferred) (.yieldNowWith priority)
  | reading {world refs deferred cell} (phase : Phase spec world)
      (refsEq : world.state.refs.length = refs) (deferredEq : world.state.deferreds.cells.length = deferred)
      (pending : ¬ Ready spec world)
      (contents : world.state.refs = Initialization.values spec.initialization refs)
      (entered : world.entered = false) :
      CodeAt spec world (.yielded refs deferred) (.sync (.store (.op (.refGet cell))))
  | bound {world input output body name} (first : CodeAt spec world input body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
        ValueAt spec nextWorld input answer → CodeAt spec nextWorld output
          ((interpAt spec.root view spec.table).contA name answer)) :
      CodeAt spec world output (.onSuccess body name)
  | yieldThen {world kind priority next} (phase : Phase spec world) (owned : CodeAt spec world kind next)
      (pending : ¬ Ready spec world → world.entered = false ∧
        world.state.refs = Initialization.values spec.initialization world.state.refs.length) :
      CodeAt spec world kind (.onSuccessConst (.yieldNowWith priority) next)

theorem ready_future (spec : Spec) (first last : World) (future : Future first last) (ready : Ready spec first) :
    Ready spec last := ⟨future.entered ready.1, Nat.le_trans ready.2.1 future.refs, Nat.le_trans ready.2.2 future.deferreds⟩

theorem phase_future (spec : Spec) (first last : World) (future : Future first last) (phase : Phase spec first) :
    Phase spec last := by
  rcases phase with owner | ready
  · exact .inl (future.owner.symm.trans owner)
  · exact .inr (ready_future spec first last future ready)

def model (spec : Spec) (completed : List (FiberId × ExitV)) :
    AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)
      World (Kind spec.stable.Kind) where
  future := Future
  future_refl _ := ⟨rfl, Nat.le_refl _, Nat.le_refl _, fun held => held⟩
  future_trans _ _ _ first last :=
    ⟨first.owner.trans last.owner, Nat.le_trans first.refs last.refs,
      Nat.le_trans first.deferreds last.deferreds, fun held => last.entered (first.entered held)⟩
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
  value_write := fun _ _ _ ready good => ⟨ready, good⟩
  cause_read := fun _ _ _ _ _ => trivial
  cause_write := fun _ _ _ ready _ => .inr ready
  code := fun _ _ _ ready good => .stable ready good
  finalizer := fun _ _ _ _ => rfl

def UniformSaved (spec : Spec) :=
  AnswerFlow.ViewSavedAt (fun view => model spec view)
    (fun view => (interpAt spec.root view spec.table).toPrimInterp)

/-- Prefix saved edges retain their actual allocation point until entry is exposed. -/
inductive Semantic (spec : Spec) : World → Kind spec.stable.Kind → Kind spec.stable.Kind → NCode → Prop
  | saved {world input output frame} (held : UniformSaved spec world input output frame)
      (scopeReady : ∀ body previous scope flag, frame = .onExit body (.scopedExit previous scope) flag → Ready spec world) :
      Semantic spec world input output frame
  | allocation {world} (captured : World) (index : Nat) (point : Point) (body : NCode)
      (small : index < spec.initialization.width) (stage : RootStage spec captured index point)
      (reached : Future captured world) :
      Semantic spec world (.allocated index) (.stable spec.stable.rootKind) (.onSuccess body (.cont point))
  | gate {world} (captured : World) (point : Point) (body : NCode)
      (stage : RootStage spec captured spec.initialization.width point)
      (gate : Gate spec.root spec.initialization.width spec.bindings) (present : spec.gate = some gate)
      (reached : Future captured world) :
      Semantic spec world .gate (.stable spec.stable.rootKind) (.onSuccess body (.cont point))

def Edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) :=
  AnswerFlow.EmbeddedEdgeOver (fun (_ : World) => ()) Kind.stable (Ready spec)
    (Semantic spec) (spec.laws fragment).Edge

end Effect4.Program.AnswerSlots.AllocationAdapter
