import Test.Dogfood.Scenario.Atomic.StageRequest

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the request finalizer entry of `Atomic.Store.shop_stages`.
The actual finalizer reads one window, appends one note and finishes with pure unit binders.
Its captured read carries the positive decision count into the later note operation.
The native mask and command invariant remain separate producer obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageCleanup
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open StageWorld

def path (id : Nat) : List Nat := SourcePaths.requestPath id ++ [1]

/-- The finalizer shape retains the literal request identity and its actual captured-read binder. -/
def site (root : NativeEff) (id : Nat) : Bool :=
  match SourceScope.levelAt (.eff root) 0 (path id), Node.at_ (.eff root) (path id) with
  | some level, some (.eff (.bind (.perform .refGet (.var 0))
      (.bind (.perform (.refUpdateWith term) (.var 2))
        (.bind (.succeed (.lit .unit)) (.succeed (.lit .unit)))))) =>
      term == Store.noteAt id (level + 1)
  | _, _ => false

/-- All six actual finalizers preserve this read, note and pure-tail source shape. -/
theorem source_census :
    (Store.shopProgram.map fun root => requests.all (site root)) = some true := by
  kernel_rfl

/-- The source reader recovers the real finalizer body and its lexical note term. -/
theorem source_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) :
    ∃ level, SourceScope.levelAt (.eff built.program) 0 (path id) = some level ∧
      Node.at_ (.eff built.program) (path id) = some (.eff
        (.bind (.perform .refGet (.var 0))
          (.bind (.perform (.refUpdateWith (Store.noteAt id (level + 1))) (.var 2))
            (.bind (.succeed (.lit .unit)) (.succeed (.lit .unit)))))) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have census := source_census
  rw [source] at census
  have selected := List.all_eq_true.mp (Option.some.inj census) id member
  unfold site at selected
  split at selected
  · rename_i level term lexical found
    have same := beq_iff_eq.mp selected
    subst term
    exact ⟨level, lexical, found⟩
  · cases selected

/-- Both native finalizer wrappers consume the same successful cleanup unit evidence. -/
def UnitKind (id : Nat) (kind : StageWorld.Kind) : Prop := kind = .note id ∨ kind = .cleanup id

theorem unit_owns (id : Nat) (kind : StageWorld.Kind) (shape : UnitKind id kind) : StageGraph.Owns id kind := by
  rcases shape with rfl | rfl <;> rfl

theorem unit_value (world : StageWorld.World) (id : Nat) (kind : StageWorld.Kind) (shape : UnitKind id kind)
    (answer : Val) (good : ValueAt world kind answer) : answer = .unit := by
  rcases shape with rfl | rfl <;> exact good.1

/-- A literal unit at the real source point retains the supplied successful cleanup class. -/
theorem unit_code (root : NativeEff) (table : RowTable) (id : Nat) (world : StageWorld.World)
    (kind : StageWorld.Kind) (point : Point)
    (found : Node.at_ (.eff root) point.path = some (.eff (.succeed (.lit .unit))))
    (good : ValueAt world kind .unit) : StageGraph.CodeAt root table id world kind (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    simp only [compileEff, amount, evalTerm]
    exact .success good

/-- The actual pure cleanup tail carries its completed note through the real unit callback. -/
theorem pure_tail_code (root : NativeEff) (table : RowTable) (id : Nat) (world : StageWorld.World)
    (kind : StageWorld.Kind) (shape : UnitKind id kind) (point : Point)
    (found : Node.at_ (.eff root) point.path =
      some (.eff (.bind (.succeed (.lit .unit)) (.succeed (.lit .unit)))))
    (good : ValueAt world kind .unit) : StageGraph.CodeAt root table id world kind (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_bind _ _ amount]
    apply StageGraph.CodeAt.bound (unit_owns id kind shape)
    · rw [← SourceScope.resolve_at root (point.child 0) _ (Agreement.at_child found 0)]
      exact unit_code root table id world kind _ (Agreement.at_child found 0) good
    · intro nextWorld future view answer value
      have same := unit_value nextWorld id kind shape answer value
      subst answer
      change StageGraph.CodeAt root table id nextWorld kind
        (resolve root (({point with completed := view} : Point).childWith 1 .unit))
      exact unit_code root table id nextWorld kind _ (Agreement.at_childWith found 1 .unit) value
    · intro nextWorld future cause value
      exact value


/-- The actual note binder carries its captured count into the completed pure cleanup tail. -/
theorem note_tail_code (root : NativeEff) (table : RowTable) (id : Nat) (world : StageWorld.World)
    (kind : StageWorld.Kind) (shape : UnitKind id kind) (point : Point) (env : List Val)
    (used admitted rejected : Nat)
    (environment : point.env = env ++ [Test.Dogfood.P4RateLimiter.windowVal used admitted rejected])
    (captured : point.env[2]? = some (.cell ⟨2⟩))
    (positive : world.stages id = .deposited → 1 ≤ admitted + rejected)
    (found : Node.at_ (.eff root) point.path = some (.eff
      (.bind (.perform (.refUpdateWith (Store.noteAt id point.env.length)) (.var 2))
        (.bind (.succeed (.lit .unit)) (.succeed (.lit .unit)))))) :
    StageGraph.CodeAt root table id world kind (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_bind _ _ amount]
    apply StageGraph.CodeAt.bound (show StageGraph.Owns id (.note id) from rfl)
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ available =>
        have handle : (point.child 0).env[2]? = some (.cell ⟨2⟩) := captured
        simp only [compileEff, childFuel, evalTerm, handle]
        change StageGraph.CodeAt root table id world (.note id)
          (.sync (.op (.refUpdate ⟨2⟩ (Store.noteAt id point.env.length) point.env)))
        rw [environment]
        simp only [List.length_append, List.length_singleton]
        exact .note positive
    · intro nextWorld future view answer value
      have same : answer = .unit := value.1
      subst answer
      change StageGraph.CodeAt root table id nextWorld kind
        (resolve root (({point with completed := view} : Point).childWith 1 .unit))
      apply pure_tail_code root table id nextWorld kind shape
        (({point with completed := view} : Point).childWith 1 .unit) (Agreement.at_childWith found 1 .unit)
      rcases shape with rfl | rfl <;> exact value
    · intro nextWorld future cause value
      rcases shape with rfl | rfl
      · exact value
      · intro reason member typed
        exact False.elim (value.1 reason member typed)


/-- The actual finalizer source carries its window read into one note and the real pure suffix. -/
theorem cleanup_code (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (located : point.path = path id)
    (sourceOwned : SourceScope.At built.program point) (cells : StageRequest.Cells point.env)
    (world : StageWorld.World) (kind : StageWorld.Kind) (shape : UnitKind id kind) :
    StageGraph.CodeAt built.program built.table id world kind (resolve built.program point) := by
  obtain ⟨level, lexical, found⟩ := source_at built accepted id member
  rw [← located] at lexical found
  have same : level = point.env.length := Option.some.inj (lexical.symm.trans sourceOwned)
  subst level
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_bind _ _ amount]
    apply StageGraph.CodeAt.bound (show StageGraph.Owns id (.seen id) from rfl)
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ available =>
        have handle : (point.child 0).env[0]? = some (.cell ⟨0⟩) := cells.read 0 (by decide)
        simp only [compileEff, childFuel, evalTerm, handle]
        exact .reading
    · intro nextWorld future view answer value
      obtain ⟨used, admitted, rejected, rfl, positive⟩ := value
      let refreshed : Point := {point with completed := view}
      let next := refreshed.childWith 1 (Test.Dogfood.P4RateLimiter.windowVal used admitted rejected)
      have prefixHeld : StageRequest.Cells next.env := AnswerSlots.childWith cells 1 _
      have node : Node.at_ (.eff built.program) next.path = some (.eff
          (.bind (.perform (.refUpdateWith (Store.noteAt id (point.env.length + 1))) (.var 2))
            (.bind (.succeed (.lit .unit)) (.succeed (.lit .unit))))) := Agreement.at_childWith found 1 (Test.Dogfood.P4RateLimiter.windowVal used admitted rejected)
      have length : next.env.length = point.env.length + 1 := by
        simp only [next, refreshed, Point.childWith, List.length_append, List.length_singleton]
      change StageGraph.CodeAt built.program built.table id nextWorld kind (resolve built.program next)
      apply note_tail_code built.program built.table id nextWorld kind shape next point.env used admitted rejected rfl
        (prefixHeld.read 2 (by decide)) positive
      rw [length]
      exact node
    · intro nextWorld future cause value
      rcases shape with rfl | rfl
      · exact value
      · intro reason member typed
        exact False.elim (value.1 reason member typed)

end Test.Dogfood.Scenario.Atomic.StageCleanup
