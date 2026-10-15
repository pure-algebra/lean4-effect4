import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Program.Interference
import Effect4.Laws.Program.Guard.Command

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Question: the crew answer-flow histories read a parked current head without a new queue invariant.
Reach: the existing native evaluator and actual parked fibers.
The predicate observes existing current code and parked status, independently of stores and values.
Consumer: Initialized.Waits follows from this shape and the initialized current-code certificate.
This shape establishes no answer class, progress or host agreement on its own.
-/
set_option autoImplicit false
namespace Effect4.Program.ParkedShape
open Effect4 Effect4.Machine Effect4.Program
abbrev Fiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- Native parks leave a void yield result, a registration, or an explicit fiber action or await. -/
inductive Head : NCode → Prop
  | yielded : Head (.success .unit)
  | async (register : EffName) (signal : Bool) (cancel : Option EffName) : Head (.async register signal cancel)
  | action (thunk : EffThunk) : Head (.withFiber thunk)
  | park (kind : ParkKind) : Head (.suspend (.park kind))
  | storedPark (kind : ParkKind) : Head (.suspend (.store (.park kind)))

/-- Only a parked fiber owes a park-head observation. -/
def HeldWith (head : NCode → Prop) (fiber : Fiber) : Prop := fiber.parked ≠ .notParked → head fiber.frame.current

/-- The original parked-head observation is the broad head instance. -/
def Held (fiber : Fiber) : Prop := HeldWith Head fiber

/-- Every supplied parked-head observation holds for an unparked actor. -/
theorem unparked_with {head : NCode → Prop} {fiber : Fiber} (active : fiber.parked = .notParked) :
    HeldWith head fiber := fun parked => False.elim (parked active)

def Configuration (machine : NativeMachine) : Prop := ∀ fiber ∈ machine.fibers, Held fiber

theorem unparked {fiber : Fiber} (active : fiber.parked = .notParked) : Held fiber :=
  fun parked => False.elim (parked active)

theorem fields_with {head : NCode → Prop} {first last : Fiber} (held : HeldWith head first)
    (parked : last.parked = first.parked) (current : last.frame.current = first.frame.current) : HeldWith head last := by
  intro pending
  rw [current]
  exact held (fun empty => pending (parked.trans empty))

/-- An actual retained token keeps the original current code and saved suffix.
Consumer: Atomic and Timeout matching-token reply admission. -/
theorem interruption_park_origin (cause : CauseV) (fiber : Fiber)
    (token : Nat) (parked : (interruptWithCause cause fiber).1.parked = .withGuard token) :
    fiber.parked = .withGuard token ∧
    (interruptWithCause cause fiber).1.frame.current = fiber.frame.current ∧
    (interruptWithCause cause fiber).1.frame.stack = fiber.frame.stack := by
  unfold interruptWithCause at parked ⊢
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore] at parked ⊢
  split
  · rename_i exited
    simp only [exited, ↓reduceIte] at parked
    exact ⟨parked, rfl, rfl⟩
  · rename_i exited
    simp only [exited] at parked
    split
    · rename_i enabled
      simp only [enabled, ↓reduceIte] at parked
      split
      · rename_i running
        simp only [running, ↓reduceIte] at parked
        exact ⟨parked, rfl, rfl⟩
      · rename_i running
        simp only [running] at parked
        cases parked
    · rename_i enabled
      simp only [enabled] at parked
      exact ⟨parked, rfl, rfl⟩

/-- Interrupt recording retains the parked head or removes the park before replacing it. -/
theorem interruption_with (head : NCode → Prop) (cause : CauseV) (fiber : Fiber) (held : HeldWith head fiber) :
    HeldWith head (interruptWithCause cause fiber).1 := by
  intro pending
  cases parked : (interruptWithCause cause fiber).1.parked with
  | notParked => exact False.elim (pending parked)
  | withGuard token =>
    have origin := interruption_park_origin cause fiber token parked
    rw [origin.2.1]
    exact held (by rw [origin.1]; intro wrong; cases wrong)

/-- Other-fiber edits cannot mint a parked token or replace its saved continuation.
Consumer: matching-token admission at old reserved keys. -/
theorem edit_park_origin {first last : Fiber} (word : Moves.OtherEdit first last)
    (token : Nat) (parked : last.parked = .withGuard token) :
    first.parked = .withGuard token ∧ last.frame.current = first.frame.current ∧
    last.frame.stack = first.frame.stack := by
  cases word with
  | observe => exact ⟨parked, rfl, rfl⟩
  | filterObservers => exact ⟨parked, rfl, rfl⟩
  | interruptCause cause => exact interruption_park_origin cause _ token parked

/-- The existing edit word transports an actual token back to its original continuation. -/
theorem edits_park_origin {first last : Fiber} (word : Moves.OtherEdits first last)
    (token : Nat) (parked : last.parked = .withGuard token) :
    first.parked = .withGuard token ∧ last.frame.current = first.frame.current ∧
    last.frame.stack = first.frame.stack := by
  induction word with
  | refl => exact ⟨parked, rfl, rfl⟩
  | tail prior next ih =>
    have final := edit_park_origin next token parked
    have initial := ih final.1
    exact ⟨initial.1, final.2.1.trans initial.2.1, final.2.2.trans initial.2.2⟩

/-- A parked row in an actual interference result comes from an old parked row.
Consumer: old queued, detached and stored replies retain their matching continuation. -/
theorem interferes_park_origin {first last : NativeMachine}
    (word : Moves.Interferes first last) (fiber : Fiber) (member : fiber ∈ last.fibers)
    (token : Nat) (parked : fiber.parked = .withGuard token) :
    ∃ old ∈ first.fibers, fiber.id = old.id ∧ old.parked = .withGuard token ∧
      fiber.frame.current = old.frame.current ∧ fiber.frame.stack = old.frame.stack := by
  rcases word.fibers fiber member with ⟨old, inside, changed⟩ | ⟨_, program, flag, budget, context, changed⟩
  · have origin := edits_park_origin changed token parked
    exact ⟨old, inside, changed.id, origin⟩
  · have origin := edits_park_origin changed token parked
    cases origin.1

/-- Existing other-fiber edits retain the parked-head observation. -/
theorem edit_with {head : NCode → Prop} {first last : Fiber} (word : Moves.OtherEdit first last) (held : HeldWith head first) : HeldWith head last := by
  cases word with
  | observe => exact held
  | filterObservers => exact held
  | interruptCause cause => exact interruption_with head cause _ held

theorem edits_with {head : NCode → Prop} {first last : Fiber} (word : Moves.OtherEdits first last) (held : HeldWith head first) : HeldWith head last := by
  induction word with
  | refl => exact held
  | tail prior next ih => exact edit_with next ih

/-- The existing interference witness retains old parked heads; every birth starts unparked. -/
theorem interferes_with {head : NCode → Prop} {first last : NativeMachine} (word : Moves.Interferes first last)
    (held : ∀ fiber ∈ first.fibers, HeldWith head fiber) : ∀ fiber ∈ last.fibers, HeldWith head fiber := by
  intro fiber member
  rcases word.fibers fiber member with ⟨old, inside, changed⟩ | ⟨_, program, flag, budget, context, changed⟩
  · exact edits_with changed (held old inside)
  · exact edits_with changed (unparked_with rfl)

/-- The broad observation retains its field-transport interface. -/
theorem fields {first last : Fiber} (held : Held first)
    (parked : last.parked = first.parked) (current : last.frame.current = first.frame.current) : Held last :=
  fields_with held parked current

/-- The broad observation retains its actual interruption interface. -/
theorem interruption (cause : CauseV) (fiber : Fiber) (held : Held fiber) :
    Held (interruptWithCause cause fiber).1 := interruption_with Head cause fiber held

/-- The broad observation retains its actual edit interface. -/
theorem edit {first last : Fiber} (word : Moves.OtherEdit first last) (held : Held first) : Held last :=
  edit_with word held

/-- The broad observation retains its actual edit-word interface. -/
theorem edits {first last : Fiber} (word : Moves.OtherEdits first last) (held : Held first) : Held last :=
  edits_with word held

/-- The broad observation retains its actual interference interface. -/
theorem interferes {first last : NativeMachine} (word : Moves.Interferes first last)
    (held : Configuration first) : Configuration last := interferes_with word held

/-- Pure frame evaluation changes no parked status. -/
theorem step_frame_with (head : NCode → Prop) (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) : HeldWith head (evaluatePrim.stepFrame interp machine fiber yielding).fiber := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact unparked_with active

/-- Finalizer interception either runs a pure frame step or retains the original unparked status. -/
theorem finalizer_with (head : NCode → Prop) (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (exit : ExitV) (active : fiber.parked = .notParked) :
    HeldWith head (evaluatePrim.finalizerOr interp machine fiber yielding exit).fiber := by
  unfold evaluatePrim.finalizerOr
  repeat' split
  all_goals aesop (add safe apply [step_frame_with], unsafe apply [unparked_with])

/-- A countdown either answers without a park or retains the original await head. -/
theorem countdown_with (head : NCode → Prop) (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (active : fiber.parked = .notParked) (currentHead : head fiber.frame.current) :
    HeldWith head (countdownParkEdits interp machine fiber targets resume failFast).2.1 := by
  unfold countdownParkEdits
  dsimp only
  split
  · exact unparked_with active
  · exact fun _ => currentHead

/-- The broad frame-step observation specializes the supplied-head producer. -/
theorem step_frame (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) : Held (evaluatePrim.stepFrame interp machine fiber yielding).fiber :=
  step_frame_with Head interp machine fiber yielding active

/-- The broad finalizer observation specializes the supplied-head producer. -/
theorem finalizer (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (exit : ExitV) (active : fiber.parked = .notParked) :
    Held (evaluatePrim.finalizerOr interp machine fiber yielding exit).fiber :=
  finalizer_with Head interp machine fiber yielding exit active

/-- The broad countdown observation specializes the supplied-head producer. -/
theorem countdown (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (active : fiber.parked = .notParked) (head : Head fiber.frame.current) :
    Held (countdownParkEdits interp machine fiber targets resume failFast).2.1 :=
  countdown_with Head interp machine fiber targets resume failFast active head

/-- Action entry can park only an await action; all other actions retain the unparked status. -/
theorem action (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (machine : NativeMachine) (fiber : Fiber) (yielding : Bool) (action : NAction)
    (active : fiber.parked = .notParked) (head : Head fiber.frame.current) :
    Held (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action).fiber := by
  cases action
  case fork body options site =>
    cases options with
    | mk immediate daemon mode =>
      cases daemon <;> cases immediate
      all_goals exact unparked active
  case forkIn body options scope site =>
    cases options with
    | mk immediate daemon mode =>
      cases immediate
      all_goals exact unparked active
  case forkScoped body options site =>
    simp only [evaluatePrim.withFiber]
    split
    · cases options with
      | mk immediate daemon mode =>
        cases immediate
        all_goals exact unparked active
    · exact unparked active
  case interruptAs target owner =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split <;> exact unparked active
  case awaitAll targets =>
    exact countdown (interpAt root view table) machine fiber targets .exitsValue false active head
  case awaitAllFailFast targets =>
    exact countdown (interpAt root view table) machine fiber targets .exitsValue true active head
  case awaitNewChildren snapshot =>
    exact countdown (interpAt root view table) machine fiber _ .void false active head
  case setInterruptible body flag =>
    cases flag <;> exact unparked active
  case ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case runIn target scope => exact unparked active
  case interrupt target => exact unparked active
  case interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case interruptAll targets owner => exact unparked active
  case snapshotChildren => exact unparked active
  case raceAll bodies site => exact unparked active
  case raceAllFirst bodies site => exact unparked active
  case setContext context => exact unparked active
  case getContext => exact unparked active
  case getId => exact unparked active
  case closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case closePar programs => exact unparked active
  case refuse cause => exact unparked active
  case dropObservers token => exact unparked active
  case cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case getInterruptible => exact unparked active

/-- The native park decoder exposes an explicit park in the existing code. -/
theorem park_head_with (head : NCode → Prop)
    (parkCase : ∀ kind, head (.suspend (.park kind)))
    (storedCase : ∀ kind, head (.suspend (.store (.park kind)))) (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (program : NCode) (park : (interpAt root view table).parkOf program ≠ none) : head program := by
  cases program
  case suspend thunk =>
    cases thunk
    case park kind => exact parkCase kind
    case store thunk =>
      cases thunk
      case park kind => exact storedCase kind
      all_goals exact (park rfl).elim
    all_goals exact (park rfl).elim
  all_goals exact (park rfl).elim

/-- The shared primitive classification supplies each actual parked head. -/
theorem primitive_with (head : NCode → Prop)
    (yielded : head (.success .unit))
    (asynchronous : ∀ register signal cancel, head (.async register signal cancel))
    (parkCase : ∀ kind, head (.suspend (.park kind)))
    (storedCase : ∀ kind, head (.suspend (.store (.park kind)))) (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked)
    (actions : ∀ thunk chosen, fiber.frame.current = .withFiber thunk →
      (interpAt root view table).parkOf fiber.frame.current = none →
      (interpAt root view table).withFiberOf thunk = some chosen →
      HeldWith head (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding chosen).fiber) :
    HeldWith head (evaluatePrim (interpAt root view table) machine fiber yielding).fiber := by
  have producer := Moves.evaluatePrim_producer (interpAt root view table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt root view table) machine fiber yielding = result at producer ⊢
  cases producer with
  | step => exact step_frame_with head _ _ _ _ active
  | finalizer exit current => exact finalizer_with head _ _ _ _ exit active
  | action thunk chosen current unparked found =>
    exact actions thunk chosen current unparked found
  | sync | fallback | asyncImmediate | rejectedPark | joinMissing | joinExited => exact unparked_with active
  | yieldNow => exact fun _ => yielded
  | asyncParked register signal cancel state current registered =>
    dsimp only
    split <;> exact fun _ => current ▸ asynchronous register signal cancel
  | racePark race park =>
    unfold registerRace
    split <;> exact unparked_with active
  | countdownPark targets next returned parked edits park counted =>
    have result := countdown_with head (interpAt root view table) machine fiber targets .exitsValue false active
      (park_head_with head parkCase storedCase root view table fiber.frame.current (by rw [park]; intro wrong; cases wrong))
    rw [counted] at result
    exact result
  | joinWaiting target mode other park found live =>
    exact fun _ => park_head_with head parkCase storedCase root view table fiber.frame.current (by rw [park]; intro wrong; cases wrong)

/-- The native decoder's broad head instance retains the old interface. -/
theorem park_head (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (program : NCode) (park : (interpAt root view table).parkOf program ≠ none) : Head program :=
  park_head_with Head Head.park Head.storedPark root view table program park

/-- The broad native observation specializes the single supplied-head primitive producer. -/
theorem primitive (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) :
    Held (evaluatePrim (interpAt root view table) machine fiber yielding).fiber := by
  apply primitive_with Head Head.yielded Head.async Head.park Head.storedPark root view table machine fiber yielding active
  intro thunk chosen current unparked found
  exact action root view table machine fiber yielding chosen active (current ▸ Head.action thunk)

/-- Scoped exit changes the frame and context while retaining the old unparked status. -/
theorem scoped_exit (root : NativeEff) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (exit : ExitV) (active : fiber.parked = .notParked) :
    Held (exitScoped root machine fiber yielding exit).fiber := by
  unfold exitScoped
  repeat' split
  all_goals aesop (add safe apply [primitive], unsafe apply [unparked])

/-- Native scoped dispatch and primitive evaluation share the same parked-head observation. -/
theorem native (root : NativeEff) (table : RowTable) (machine : NativeMachine) (fiber : Fiber)
    (yielding : Bool) (active : fiber.parked = .notParked) :
    Held (evaluateNative root machine fiber yielding table).fiber := by
  unfold evaluateNative
  split
  · split
    · exact unparked active
    · exact primitive root machine.completedExits table machine fiber yielding active
  · exact scoped_exit root machine fiber yielding _ active
  · exact scoped_exit root machine fiber yielding _ active
  · exact primitive root machine.completedExits table machine fiber yielding active

/-- The counted iteration keeps its input park absent before actual evaluation. -/
theorem iteration (root : NativeEff) (table : RowTable) (machine : NativeMachine) (fiber : Fiber)
    (yielding : Bool) (active : fiber.parked = .notParked) :
    Held (Machine.iteration (evaluator := evaluatorFor root table) (interpOf root table)
      machine fiber yielding).fiber := by
  have top : (countOp (runloopTop fiber)).parked = .notParked := by
    unfold countOp runloopTop
    split <;> exact active
  unfold Machine.iteration
  dsimp only
  split
  · rename_i result injected
    unfold injectYield at injected
    split at injected
    · cases injected
      exact native root table _ _ _ top
    · cases injected
  · exact native root table _ _ _ top

end Effect4.Program.ParkedShape
