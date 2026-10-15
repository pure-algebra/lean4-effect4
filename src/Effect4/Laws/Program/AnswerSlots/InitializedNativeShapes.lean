import Effect4.Laws.Program.AnswerSlots.InitializedNativeExit

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native asynchronous and fiber-action heads belong to the initialized stable source.
Reach: the actual allocation prefix, protected current code and arbitrary source budgets.
Limit: this classifies native heads; their operation and command producers remain separate.
Consumer: initialized native parks and the shared native action closure for crew log histories.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Initializer source resolution exposes only a binder, a live frontier or a shape failure. -/
theorem initial_shape (spec : Spec) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) :
    (∃ body name, resolve spec.root point = .onSuccess body name) ∨
    resolve spec.root point = frontier point ∨
    (∃ cause, resolve spec.root point = .failure cause) := by
  cases amount : point.fuel with
  | zero =>
    unfold resolve
    split
    · rw [Agreement.compileEff_at_zero _ amount]
      exact .inr (.inl rfl)
    · exact .inr (.inr ⟨_, rfl⟩)
  | succ fuel =>
    by_cases small : index < spec.initialization.width
    · rw [spec.initialization.compile index point fuel small stage.2.2.1 amount]
      exact .inl ⟨_, _, rfl⟩
    · have bound := stage.1
      have last : index = spec.initialization.width := by omega
      subst index
      obtain ⟨tail, found⟩ := spec.gate_head
      rw [← stage.2.2.1] at found
      rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount]
      exact .inl ⟨_, _, rfl⟩

/-- Native action and asynchronous heads cannot be initializer binders or administrative frontiers. -/
theorem stable_shape (spec : Spec) (world : World) (kind : Kind) (program : NCode)
    (owned : CodeAt spec world kind program)
    (notSuccess : ∀ value, program ≠ .success value)
    (notFailure : ∀ cause, program ≠ .failure cause)
    (notSync : ∀ thunk, program ≠ .sync thunk)
    (notBind : ∀ body name, program ≠ .onSuccess body name)
    (notFrontier : ∀ point, program ≠ frontier point)
    (notYield : ∀ priority, program ≠ .yieldNowWith priority)
    (notConstant : ∀ body next, program ≠ .onSuccessConst body next) :
    ∃ stableKind, kind = .stable stableKind ∧ Ready spec world ∧ Typed.CodeAt spec.toSpec stableKind program := by
  cases owned with
  | success good => exact (notSuccess _ rfl).elim
  | failure phase => exact (notFailure _ rfl).elim
  | initial stage =>
    rcases initial_shape spec world _ _ stage with ⟨body, name, same⟩ | same | ⟨cause, same⟩
    · exact (notBind body name same).elim
    · exact (notFrontier _ same).elim
    · exact (notFailure cause same).elim
  | allocating small stage | gateAllocating stage | reading phase refs deferred pending => exact (notSync _ rfl).elim
  | stable ready held => exact ⟨_, rfl, ready, held⟩
  | frontier zero phase => exact (notFrontier _ rfl).elim
  | yielding phase refs deferred pending => exact (notYield _ rfl).elim
  | bound first callback => exact (notBind _ _ rfl).elim
  | yieldThen phase held => exact (notConstant _ _ rfl).elim

/-- An actual native fiber action runs at the broad stable input class after initialization. -/
theorem action_shape (spec : Spec) (world : World) (kind : Kind) (thunk : EffThunk)
    (owned : CodeAt spec world kind (.withFiber thunk)) :
    kind = .stable .root ∧ Ready spec world ∧ Typed.ThunkAt spec.toSpec thunk := by
  obtain ⟨stableKind, rfl, ready, held⟩ := stable_shape spec world kind (.withFiber thunk) owned
    (by intro value same; cases same) (by intro cause same; cases same)
    (by intro op same; cases same) (by intro body name same; cases same)
    (by intro body same; cases same) (by intro priority same; cases same)
    (by intro body next same; cases same)
  exact ⟨congrArg Kind.stable held.1, ready, held.2⟩

/-- An actual asynchronous registration uses the broad stable result class after initialization. -/
theorem async_shape (spec : Spec) (world : World) (kind : Kind) (register : EffName)
    (signal : Bool) (cancel : Option EffName) (owned : CodeAt spec world kind (.async register signal cancel)) :
    kind = .stable .root ∧ Ready spec world := by
  obtain ⟨stableKind, rfl, ready, held⟩ := stable_shape spec world kind (.async register signal cancel) owned
    (by intro value same; cases same) (by intro cause same; cases same)
    (by intro op same; cases same) (by intro body name same; cases same)
    (by intro body same; cases same) (by intro priority same; cases same)
    (by intro body next same; cases same)
  exact ⟨congrArg Kind.stable held.1, ready⟩
/-- Native park classification forces the broad stable input class after initialization. -/
theorem park_shape (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (kind : Kind) (program : NCode) (owned : CodeAt spec world kind program)
    (park : (interpAt spec.root completed spec.table).parkOf program ≠ none) :
    kind = .stable .root ∧ Ready spec world := by
  obtain ⟨stableKind, rfl, ready, held⟩ := stable_shape spec world kind program owned
    (by intro value same; rw [same] at park; exact (park rfl).elim)
    (by intro cause same; rw [same] at park; exact (park rfl).elim)
    (by intro op same; rw [same] at park; exact (park rfl).elim)
    (by intro body name same; rw [same] at park; exact (park rfl).elim)
    (by intro point same; rw [same] at park; exact (park rfl).elim)
    (by intro priority same; rw [same] at park; exact (park rfl).elim)
    (by intro body next same; rw [same] at park; exact (park rfl).elim)
  cases program
  case suspend thunk =>
    cases thunk
    case body point => exact (park rfl).elim
    all_goals exact ⟨congrArg Kind.stable held.1, ready⟩
  all_goals exact (park rfl).elim
end Effect4.Program.AnswerSlots.Initialized
