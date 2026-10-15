import Test.Dogfood.Scenario.Atomic.RootSpawn
import Test.Dogfood.Scenario.Atomic.DaemonPrimitive

/-!
Concept: store-typing R4.
Consumer: actual root native primitive, timer and fork results in `Atomic.Store.shop_stages`.
One finite source census classifies the root's outer entries before native dispatch.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Every real root source entry is a live frontier, its next binder, or its final window read. -/
theorem entry_form (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (point : Point) (held : PointAt built.program world point) :
    (point.fuel = 0 ∧ resolve built.program point = frontier point) ∨
      (∃ first name, resolve built.program point = .onSuccess first name) ∨
        resolve built.program point = .sync (.op (.refGet ⟨0⟩)) := by
  have bindForm (first rest : NativeEff)
      (found : Node.at_ (.eff built.program) point.path = some (.eff (.bind first rest))) :
      (point.fuel = 0 ∧ resolve built.program point = frontier point) ∨
        (∃ body name, resolve built.program point = .onSuccess body name) ∨
          resolve built.program point = .sync (.op (.refGet ⟨0⟩)) := by
    rw [SourceScope.resolve_at _ _ _ found]
    cases amount : point.fuel with
    | zero => exact .inl ⟨rfl, Agreement.compileEff_at_zero _ amount⟩
    | succ fuel =>
      rw [Agreement.compileEff_bind _ _ amount]
      exact .inr (.inl ⟨_, _, rfl⟩)
  obtain fork | wait | sleep | interrupt | read :=
    RootSource.forms built accepted point.env.length held.2.2.1 held.2.2.2.1
  · obtain ⟨body, options, rest, position, found⟩ := fork
    rw [← held.2.1.2] at found
    exact bindForm _ _ found
  · obtain ⟨slot, rest, position, found⟩ := wait
    rw [← held.2.1.2] at found
    exact bindForm _ _ found
  · obtain ⟨rest, position, found⟩ := sleep
    rw [← held.2.1.2] at found
    exact bindForm _ _ found
  · obtain ⟨rest, position, found⟩ := interrupt
    rw [← held.2.1.2] at found
    exact bindForm _ _ found
  · obtain ⟨position, found⟩ := read
    rw [← held.2.1.2] at found
    have captured : point.env[0]? = some (.cell ⟨0⟩) :=
      held.2.1.1 0 _ rfl (by have lower := held.2.2.1; omega)
    rw [SourceScope.resolve_at _ _ _ found]
    cases amount : point.fuel with
    | zero => exact .inl ⟨rfl, Agreement.compileEff_at_zero _ amount⟩
    | succ fuel =>
      apply Or.inr
      apply Or.inr
      simp only [compileEff, amount, evalTerm, captured]
      rfl

/-- Actual root synchronous code is its final read or an ignored daemon administrative primitive. -/
theorem sync_shape (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (kind : StageWorld.Kind) (thunk : EffThunk)
    (held : CodeAt built.program built.table world kind (.sync thunk)) :
    (kind = .ordinary ∧ (thunk = .op (.refGet ⟨0⟩) ∨ DaemonGraph.SyncAt thunk)) ∨
      ∃ cell, thunk = .store (.op (.refGet cell)) ∧ ∀ value, ValueAt world kind value := by
  generalize equal : Prim.sync thunk = code at held
  cases held with
  | ignored owned => exact .inl ⟨rfl, .inr (DaemonGraph.sync_shape _ _ _ owned thunk equal.symm)⟩
  | entry owned =>
    rcases entry_form built accepted world _ owned with ⟨zero, form⟩ | ⟨first, name, form⟩ | form
    · rw [form] at equal
      cases equal
    · rw [form] at equal
      cases equal
    · rw [form] at equal
      cases equal
      exact .inl ⟨rfl, .inl rfl⟩
  | readReply cell owned values => cases equal; exact .inr ⟨cell, rfl, values⟩
  | read => cases equal; exact .inl ⟨rfl, .inl rfl⟩
  | success good => cases equal
  | failure => cases equal
  | frontier zero => cases equal
  | action owned => cases equal
  | await counter ignored => cases equal
  | sleep counter ignored => cases equal
  | interrupting counter ignored => cases equal
  | join target mode counter => cases equal
  | awaitAll targets counter => cases equal
  | pause => cases equal
  | pausing owned next => cases equal
  | bound owned first callback => cases equal

/-- Actual root synchronous evaluation retains the same heap and supplies its ignored answer class. -/
theorem sync_heap (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (kind : StageWorld.Kind) (thunk : EffThunk) (state : Stores)
    (held : CodeAt built.program built.table world kind (.sync thunk)) (heap : HeapAt world state)
    (after : Stores) (answer : Val)
    (ran : (interpOf built.program built.table).syncState thunk state = some (after, answer)) :
    HeapAt world after ∧ ValueAt world kind answer := by
  rcases sync_shape built accepted world kind thunk held with ⟨rfl, read | administrative⟩ | ⟨cell, rfl, values⟩
  · subst thunk
    obtain ⟨used, ids, log, refs, counts, length, owned, cleaned⟩ := heap.witness
    have allocated : 0 < state.refs.length := by rw [refs]; exact Nat.zero_lt_succ 2
    change syncOpStep (.refGet ⟨0⟩) state = some (after, answer) at ran
    rw [syncOpStep_refGet_allocated allocated] at ran
    cases ran
    exact ⟨heap, True.intro⟩
  · exact ⟨DaemonGraph.sync_heap built.program built.table world state thunk (by
        cases administrative with
        | refill env length => exact .refill length
        | readReply cell => exact .readReply cell
        | cancel waiter token => exact .cancelClock waiter token) heap after answer ran, True.intro⟩
  · change syncOpStep (.refGet cell) state = some (after, answer) at ran
    cases peek : refPeek state.refs cell with
    | none => simp only [syncOpStep, refStep, peek, Option.map_none] at ran; cases ran
    | some value =>
      simp only [syncOpStep, refStep, peek, Option.map_some] at ran
      cases ran
      exact ⟨heap, values _⟩

/-- Every actual root asynchronous operation is a timer whose answer is ignored at its captured counter. -/
theorem async_shape (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (kind : StageWorld.Kind) (name : EffName) (signal : Bool) (cancel : Option EffName)
    (held : CodeAt built.program built.table world kind (.async name signal cancel)) :
    ∃ millis, name = .store (.registerSleep millis) ∧ signal = true ∧ cancel = some (.store .cancelSleep) ∧
      Owns kind ∧ ∀ value, ValueAt world kind value := by
  generalize equal : Prim.async name signal cancel = code at held
  cases held with
  | ignored owned =>
    obtain ⟨sameName, sameSignal, sameCancel⟩ := DaemonGraph.async_shape _ _ name signal cancel (equal.symm ▸ owned)
    exact ⟨1000, sameName, sameSignal, sameCancel, True.intro, fun _ => True.intro⟩
  | entry owned =>
    rcases entry_form built accepted world _ owned with ⟨zero, form⟩ | ⟨first, next, form⟩ | form
    all_goals rw [form] at equal
    all_goals cases equal
  | sleep counter ignored =>
    cases equal
    exact ⟨_, rfl, rfl, rfl, True.intro, fun value => ignored_answer world _ value counter ignored⟩
  | success good => cases equal
  | failure => cases equal
  | frontier zero => cases equal
  | action owned => cases equal
  | await counter ignored => cases equal
  | interrupting counter ignored => cases equal
  | readReply cell owned values => cases equal
  | read => cases equal
  | join target mode counter => cases equal
  | awaitAll targets counter => cases equal
  | pause => cases equal
  | pausing owned next => cases equal
  | bound owned first callback => cases equal

/-- Every actual root park joins or awaits fibers and ignores its answer at the captured counter. -/
theorem park_shape (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (view : List (FiberId × ExitV)) (kind : StageWorld.Kind) (code : NCode)
    (held : CodeAt built.program built.table world kind code) (park : Except CauseV ParkKind)
    (actual : (interpAt built.program view built.table).parkOf code = some park) :
    ((∃ target mode, park = .ok (.join target mode)) ∨ (∃ targets, park = .ok (.awaitAll targets))) ∧
      Owns kind ∧ ∀ value, ValueAt world kind value := by
  cases held with
  | ignored owned =>
    exact ⟨DaemonGraph.park_shape _ _ view _ owned park actual, True.intro, fun _ => True.intro⟩
  | entry owned =>
    rcases entry_form built accepted world _ owned with ⟨zero, form⟩ | ⟨first, next, form⟩ | form
    all_goals rw [form] at actual
    all_goals cases actual
  | await counter ignored =>
    cases actual
    exact ⟨.inl ⟨_, .awaitValue, rfl⟩, True.intro, fun value => ignored_answer world _ value counter ignored⟩
  | join target mode captured =>
    cases actual
    exact ⟨.inl ⟨target, mode, rfl⟩, True.intro, fun _ => captured⟩
  | awaitAll targets captured =>
    cases actual
    exact ⟨.inr ⟨targets, rfl⟩, True.intro, fun _ => captured⟩
  | success good => cases actual
  | failure => cases actual
  | frontier zero => cases actual
  | action owned => cases actual
  | sleep counter ignored => cases actual
  | interrupting counter ignored => cases actual
  | readReply cell owned values => cases actual
  | read => cases actual
  | pause => cases actual
  | pausing owned next => cases actual
  | bound owned first callback => cases actual

/-- An actual root scheduler yield retains its captured allocation counter in the unit answer. -/
theorem yield_value (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (kind : StageWorld.Kind) (priority : Nat)
    (held : CodeAt built.program built.table world kind (.yieldNowWith priority)) :
    ValueAt world kind .unit := by
  generalize equal : Prim.yieldNowWith priority = code at held
  cases held with
  | ignored owned => exact True.intro
  | entry owned =>
    rcases entry_form built accepted world _ owned with ⟨zero, form⟩ | ⟨first, next, form⟩ | form
    all_goals rw [form] at equal
    all_goals cases equal
  | pause => exact rfl
  | success good => cases equal
  | failure => cases equal
  | frontier zero => cases equal
  | action owned => cases equal
  | await counter ignored => cases equal
  | sleep counter ignored => cases equal
  | interrupting counter ignored => cases equal
  | readReply cell owned values => cases equal
  | read => cases equal
  | join target mode counter => cases equal
  | awaitAll targets counter => cases equal
  | pausing owned next => cases equal
  | bound owned first callback => cases equal

/-- No actual root bind body is an authored scoped block. -/
theorem body_not_scoped (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (point : Point) (held : PointAt built.program world point) (body : NativeEff) :
    Node.at_ (.eff built.program) (point.child 0).path ≠ some (.eff (.scoped body)) := by
  intro chosen
  obtain fork | wait | sleep | interrupt | read :=
    RootSource.forms built accepted point.env.length held.2.2.1 held.2.2.2.1
  · obtain ⟨program, options, rest, position, found⟩ := fork
    rw [← held.2.1.2] at found
    rw [Agreement.at_child found 0] at chosen
    cases chosen
  · obtain ⟨slot, rest, position, found⟩ := wait
    rw [← held.2.1.2] at found
    rw [Agreement.at_child found 0] at chosen
    cases chosen
  · obtain ⟨rest, position, found⟩ := sleep
    rw [← held.2.1.2] at found
    rw [Agreement.at_child found 0] at chosen
    cases chosen
  · obtain ⟨rest, position, found⟩ := interrupt
    rw [← held.2.1.2] at found
    rw [Agreement.at_child found 0] at chosen
    cases chosen
  · obtain ⟨position, found⟩ := read
    rw [← held.2.1.2] at found
    rw [Agreement.at_child found 0] at chosen
    cases chosen

/-- Actual root action annotations exclude scoped entry at the dispatcher source point. -/
theorem action_not_scoped (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (kind : StageWorld.Kind) (point : Point)
    (held : CodeAt built.program built.table world kind (.withFiber (.act point))) (body : NativeEff) :
    Node.at_ (.eff built.program) point.path ≠ some (.eff (.scoped body)) := by
  generalize equal : (Prim.withFiber (EffThunk.act point) : NCode) = code at held
  cases held with
  | ignored owned =>
    rcases DaemonGraph.action_shape built.program built.table (.act point) (equal.symm ▸ owned) with
      ⟨targets, who, wrong⟩ | ⟨token, wrong⟩
    all_goals cases wrong
  | action owned =>
    cases equal
    exact body_not_scoped built accepted world _ owned body
  | entry owned =>
    rcases entry_form built accepted world _ owned with ⟨zero, form⟩ | ⟨first, next, form⟩ | form
    all_goals rw [form] at equal
    all_goals cases equal
  | success good => cases equal
  | failure => cases equal
  | frontier zero => cases equal
  | await counter ignored => cases equal
  | sleep counter ignored => cases equal
  | interrupting counter ignored => cases equal
  | readReply cell owned values => cases equal
  | read => cases equal
  | join target mode counter => cases equal
  | awaitAll targets counter => cases equal
  | pause => cases equal
  | pausing owned next => cases equal
  | bound owned first callback => cases equal

end Test.Dogfood.Scenario.Atomic.RootGraph
