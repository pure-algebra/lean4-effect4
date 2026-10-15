import Test.Dogfood.Scenario.Atomic.DaemonSource
import Effect4.Laws.Machine.AnswerFlowRecursiveFamily

/-!
Concept: store-typing R4.
Consumer: the Atomic daemon native iteration and actual command/history invariant.
The daemon retains its actual loop point and the captured window cell through every sleep.
Only its named refill primitive changes the shop heap.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

def LoopPoint (root : NativeEff) (point : Point) : Prop :=
  Node.at_ (.eff root) point.path = some (.eff DaemonSource.program) ∧
    point.env.length = 3 ∧ StageRequest.Cells point.env

def BodyPoint (root : NativeEff) (point : Point) : Prop :=
  Node.at_ (.eff root) point.path = some (.eff DaemonSource.body) ∧
    point.env.length = 4 ∧ StageRequest.Cells point.env

def UpdatePoint (root : NativeEff) (point : Point) : Prop :=
  Node.at_ (.eff root) point.path = some (.eff (.perform (.refUpdateWith (Store.refillAt 5)) (.var 0))) ∧
    point.env.length = 5 ∧ StageRequest.Cells point.env

/-- Daemon current code retains its finite source heads and actual recursive loop name. -/
inductive CodeAt (root : NativeEff) (table : RowTable) : NCode → Prop
  | success (value : Val) : CodeAt root table (.success value)
  | failure (cause : CauseV) : CodeAt root table (.failure cause)
  | entry {point} (held : LoopPoint root point) : CodeAt root table (resolve root point)
  | body {point} (held : BodyPoint root point) : CodeAt root table (resolve root point)
  | update {point} (held : UpdatePoint root point) : CodeAt root table (resolve root point)
  | loop {point} (held : LoopPoint root point) (cursor : Val) : CodeAt root table (.whileLoop (.loop point) cursor)
  | frontier {point} (zero : point.fuel = 0) : CodeAt root table (Effect4.Program.frontier point)
  | sleep : CodeAt root table (.async (.store (.registerSleep 1000)) true (some (.store .cancelSleep)))
  | refill {env} (length : env.length = 5) : CodeAt root table (.sync (.op (.refUpdate ⟨0⟩ (Store.refillAt 5) env)))
  | cancelClock (waiter : FiberId) (token : Nat) : CodeAt root table (.sync (.store (.op (.sleepCancel waiter token))))
  | join (target : FiberId) (mode : Supervision.ObserverMode) :
      CodeAt root table (.suspend (.park (.join target mode)))
  | awaitAll (targets : List FiberId) : CodeAt root table (.suspend (.park (.awaitAll targets)))
  | interruptAll (targets : List FiberId) (who : Option FiberId) :
      CodeAt root table (.withFiber (.store (.act (.interruptAll targets who))))
  | dropObservers (token : Nat) : CodeAt root table (.withFiber (.store (.act (.dropObservers token))))
  | constant {first next} (held : CodeAt root table first) (continuation : CodeAt root table next) :
      CodeAt root table (.onSuccessConst first next)
  | pause (priority : Nat) : CodeAt root table (.yieldNowWith priority)
  | bound {first name} (held : CodeAt root table first)
      (callback : ∀ view value, CodeAt root table ((interpAt root view table).contA name value)) :
      CodeAt root table (.onSuccess first name)

/-- Daemon answers carry no request stage; the same world still owns every shop heap write. -/
def model (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect)
      (ι := FiberId) (α := Ann) StageWorld.World Unit where
  future := Future
  future_refl world := order.refl world
  future_trans _ _ _ one two := order.trans one two
  value := fun _ _ _ => True
  cause := fun _ _ _ => True
  code := fun _ _ => CodeAt root table
  finalizer := fun _ name exit => ((interpAt root view table).finalizerProgram name exit).map
    (finalizerCode (interpAt root view table) exit)
  success := fun _ _ value _ => .success value
  failure := fun _ _ cause _ => .failure cause

def LoopAt (root : NativeEff) (_world : StageWorld.World) : EffName → Prop
  | .loop point => LoopPoint root point
  | _ => False

structure Semantic (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (input output : Unit) (frame : NCode) : Prop where
  held : ViewSavedAt (model root table) (fun view => (interpAt root view table).toPrimInterp) world input output frame
  noScoped : ∀ body previous scope flag, frame ≠ .onExit body (.scopedExit previous scope) flag

def Edge (root : NativeEff) (table : RowTable) :=
  RecursiveFamilyEdge (Semantic root table) () (LoopAt root) (fun _ _ => False)

/-- The actual loop body keeps the same three captured cells and appends only its cursor. -/
theorem loop_body (root : NativeEff) (point : Point) (held : LoopPoint root point) (cursor : Val) :
    BodyPoint root (point.childWith 0 cursor) := by
  refine ⟨Agreement.at_child held.1 0, ?_, ?_⟩
  · change (point.env ++ [cursor]).length = 4
    rw [List.length_append, held.2.1]
    rfl
  · exact AnswerSlots.Prefix.append held.2.2 [cursor]

/-- The actual daemon body answer enters its one refill operation with the same captured cell. -/
theorem body_update (root : NativeEff) (point : Point) (held : BodyPoint root point) (value : Val) :
    UpdatePoint root (point.childWith 1 value) := by
  refine ⟨Agreement.at_child held.1 1, ?_, ?_⟩
  · change (point.env ++ [value]).length = 5
    rw [List.length_append, held.2.1]
    rfl
  · exact AnswerSlots.Prefix.append held.2.2 [value]
/-- The daemon test always enters its one body at the actual cursor. -/
theorem loop_next (root : NativeEff) (point : Point) (held : LoopPoint root point) (cursor : Val) :
    loopNextAt root point cursor = .continue cursor (resolve root (point.childWith 0 cursor)) := by
  simp only [loopNextAt, loopAt, held.1, DaemonSource.program, evalTerm, Lit.toVal]

/-- The daemon step retains its cursor after the actual body answer. -/
theorem loop_resume (root : NativeEff) (point : Point) (held : LoopPoint root point) (cursor answer : Val) :
    loopResumeAt root point cursor answer = .continue cursor (resolve root (point.childWith 0 cursor)) := by
  have selected : (point.env ++ [cursor, answer])[3]? = some cursor := by
    rw [← held.2.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  simp only [loopResumeAt, loopAt, held.1, DaemonSource.program, evalTerm, selected]
  exact loop_next root point held cursor

/-- Existing recursive hooks supply the daemon loop's actual body without unrolling its iterations. -/
theorem hooks (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    RecursiveHooks (model root table view) (interpAt root view table).toPrimInterp ()
      (LoopAt root) (fun _ _ => False) := by
  constructor
  · intro before after future name held
    exact held
  · intro before after future name held
    exact held
  · intro world name cursor answer held
    cases name
    all_goals dsimp only [LoopAt] at held
    all_goals cases held
    case loop.intro point found rest =>
      obtain ⟨length, cells⟩ := rest
      change RecursiveLoopResult (model root table view) () world
        (loopResumeAt root { point with completed := view } cursor answer)
      rw [loop_resume root { point with completed := view } ⟨found, length, cells⟩ cursor answer]
      exact CodeAt.body (loop_body root { point with completed := view } ⟨found, length, cells⟩ cursor)
  · intro world name answer impossible
    cases impossible

/-- The daemon saved family reuses the shared semantic and recursive callback algebra. -/
theorem family (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    SavedFamily (model root table view) (interpAt root view table).toPrimInterp (Edge root table) :=
  recursive_family_of (model root table view) (interpAt root view table).toPrimInterp
    (Semantic root table) () (LoopAt root) (fun _ _ => False)
    (ViewSavedAt.refined_family (model root table) (fun current => (interpAt root current table).toPrimInterp)
      (Semantic root table) (fun _ _ _ _ held => held.held) view)
    (hooks root table view)
end Test.Dogfood.Scenario.Atomic.DaemonGraph
