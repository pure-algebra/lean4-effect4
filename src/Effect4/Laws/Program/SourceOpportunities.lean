import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Program.Placement
import Effect4.Laws.Machine.PrimWeights

/-!
Concept: scope-lifetime-finalization R11.
Question: ordered source opportunity accounting for FinalizerRun.once_placed_pushes_once
and Workers.Assertions.registrations_step.
The projections inspect existing source paths, current code and saved callbacks.
A saved frame excludes its copied body and its already recorded push.
Compiler bounds initialize the count; they do not establish command preservation or history uniqueness.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Program Effect4.Machine

/-- One selected source occurrence remains beneath an unexecuted source address. -/
def below (q path : List Nat) : Nat := if path.isPrefixOf q then 1 else 0

/-- The selected source occurrence is the current registration site. -/
def here (q path : List Nat) : Nat := if path = q then 1 else 0

/-- A captured release resolves child one after the acquisition has already registered. -/
def fin (q : List Nat) : FinName → Nat
  | .foreign capture => below q (capture.path ++ [1])
  | _ => 0


/-- The selected source lies outside every authored finalizer child.
The walk is the existing generated address census, not a new source traversal. -/
def ClearFinalizers (root : NativeEff) (q : List Nat) : Prop :=
  (Node.addresses (.eff root)).all (fun path =>
    (Node.at_ (.eff root) path).all (fun node => match node with
      | .eff (.acquireRelease _ _) | .eff (.onExit _ _) => !(path ++ [1]).isPrefixOf q
      | _ => true)) = true

/-- A source acquisition's release child cannot contain an application-selected source.
Consumer: captured-finalizer opportunity elimination. -/
theorem acquisition_clear (root : NativeEff) (q path : List Nat) (clear : ClearFinalizers root q)
    (source : AcquisitionAt root path) : below q (path ++ [1]) = 0 := by
  obtain ⟨acquire, release, found⟩ := source
  have member : path ∈ Node.addresses (.eff root) :=
    (mem_addresses_iff (.eff root) path).mpr (by rw [found]; rfl)
  have census := List.all_eq_true.mp clear path member
  rw [found] at census
  cases prefixed : (path ++ [1]).isPrefixOf q
  · simp only [below, prefixed, Bool.false_eq_true, ↓reduceIte]
  · simp only [Option.all_some, prefixed, Bool.not_true, Bool.false_eq_true] at census

/-- A source onExit callback's child cannot contain an application-selected source.
Consumer: saved finalizer opportunity elimination. -/
theorem exit_clear (root : NativeEff) (q path : List Nat) (clear : ClearFinalizers root q)
    (source : ExitAt root path) : below q (path ++ [1]) = 0 := by
  obtain ⟨body, finalizer, found⟩ := source
  have member : path ∈ Node.addresses (.eff root) :=
    (mem_addresses_iff (.eff root) path).mpr (by rw [found]; rfl)
  have census := List.all_eq_true.mp clear path member
  rw [found] at census
  cases prefixed : (path ++ [1]).isPrefixOf q
  · simp only [below, prefixed, Bool.false_eq_true, ↓reduceIte]
  · simp only [Option.all_some, prefixed, Bool.not_true, Bool.false_eq_true] at census

/-- Actual captured releases have no selected opportunity in these application sources.
Consumer: stored names, scope entries and close programs of the source-use invariant. -/
theorem captured_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (captured : FinName) (owned : FinAt root captured) : fin q captured = 0 := by
  cases captured
  case foreign capture => exact acquisition_clear root q capture.path clear owned.2
  all_goals rfl

/-- Delayed native callbacks retain their future child, rather than the copied body. -/
def name (q : List Nat) : EffName → Nat
  | .cont p | .caught p | .onValue p | .fin p | .caughtError p => below q (p.path ++ [1])
  | .onCause p => below q (p.path ++ [2])
  | .scopeOpen p | .scopeProvide p _ | .scopeBody p _ => below q (p.path ++ [0])
  | .acquireCtx p | .acquireIn p _ | .forkScopedIn p => below q p.path
  | .acquired p _ _ => here q p.path + below q (p.path ++ [1])
  | .afterScopeAdd _ captured => fin q captured
  | .releaseUnder p _ _ | .releaseBody p _ _ => below q (p.path ++ [1])
  | .gen p pc _ => below q (p.path ++ [0] ++ pc)
  | .loop p => below q p.path
  | .withWaiter base _ _ => name q base
  | .provideMask _ (.program p) | .updateThen _ (.program p) _ | .bodyThen (.program p) _ _ =>
    below q p.path
  | _ => 0


/-- Actual authored finalizer callbacks have no application-selected future opportunity.
Consumer: native finalizer invocation and frame-pop source debit. -/
theorem finalizer_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (p : Point) (owned : NameAt root (.fin p)) : name q (.fin p) = 0 :=
  exit_clear root q p.path clear owned.2

/-- Native source thunks retain the syntax they have not yet interpreted. -/
def thunk (root : NativeEff) (q : List Nat) : EffThunk → Nat
  | .body p | .forkInAt p _ | .acquireMasked p _ => below q p.path
  | .act p => match Node.at_ (.eff root) p.path with
      | some (.eff (.withFiber (.forkScoped _ _))) => 0
      | _ => below q p.path
  | .releaseMasked p _ => below q p.path
  | .store (.foreign capture _) => fin q (.foreign capture)
  | .provideMasked _ (.program p) _ | .restoreRegion (.program p) _ => below q p.path
  | _ => 0

/-- A registration push spends this selected source opportunity. -/
def push (q : List Nat) : NCode → Nat
  | .onExit _ (.fin p) _ => here q p.path
  | .onSuccess _ (.afterScopeAdd _ (.foreign capture)) => here q capture.path
  | _ => 0

/-- Leaf reservations and recorded pushes instantiate the shared native-code fold. -/
abbrev nativeWeights (root : NativeEff) (q : List Nat) : Machine.PrimWeights.Model EffName EffThunk where
  name := name q
  thunk := thunk root q
  successPush callback := push q (.onSuccess (.success .unit) callback)
  exitPush callback flag := push q (.onExit (.success .unit) callback flag)

/-- Active code includes its body, future callback and not-yet-recorded registration. -/
abbrev current (root : NativeEff) (q : List Nat) (code : NCode) : Nat :=
  cata_prim (Machine.PrimWeights.currentAlgebra (nativeWeights root q)) code

/-- A saved frame's body is already active elsewhere; its push has already been recorded. -/
def saved (root : NativeEff) (q : List Nat) : NCode → Nat
  | .onSuccess _ callback | .onFailure _ callback | .onExit _ callback _ => name q callback
  | .onSuccessConst _ next => current root q next
  | .onSuccessAndFailure _ success failure => name q success + name q failure
  | .iterator callback _ | .whileLoop callback _ | .asyncFinalizer callback => name q callback
  | _ => 0

/-- A child reserves no more than its parent source occurrence.
Consumer: compiler opportunity initialization. -/
theorem child_le (q path : List Nat) (i : Nat) : below q (path ++ [i]) ≤ below q path := by
  have inherited : (path ++ [i]).isPrefixOf q = true → path.isPrefixOf q = true := by
    intro child
    exact List.isPrefixOf_iff_prefix.mpr
      (List.IsPrefix.trans (List.prefix_append path [i]) (List.isPrefixOf_iff_prefix.mp child))
  unfold below
  split
  · rw [inherited (by assumption)]
    exact Nat.le_refl 1
  · exact Nat.zero_le _

/-- Distinct callback children cannot both contain the selected occurrence.
Consumer: compiler opportunity initialization. -/
theorem siblings_le (q path : List Nat) (a b : Nat) (different : a ≠ b) :
    below q (path ++ [a]) + below q (path ++ [b]) ≤ below q path := by
  have apart : ¬ ((path ++ [a]).isPrefixOf q = true ∧ (path ++ [b]).isPrefixOf q = true) := by
    intro both
    have ordered := List.prefix_or_prefix_of_prefix
      (List.isPrefixOf_iff_prefix.mp both.1) (List.isPrefixOf_iff_prefix.mp both.2)
    rw [List.prefix_append_right_inj path, List.prefix_append_right_inj path] at ordered
    rcases ordered with left | right
    · exact different (List.cons_prefix_cons.mp left).1
    · exact different (List.cons_prefix_cons.mp right).1.symm
  by_cases first : (path ++ [a]).isPrefixOf q = true
  · by_cases second : (path ++ [b]).isPrefixOf q = true
    · exact False.elim (apart ⟨first, second⟩)
    · simpa only [below, second, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using child_le q path a
  · simpa only [below, first, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using child_le q path b

/-- A selected parent registration and its callback child are distinct opportunities.
Consumer: acquisition producer transfer and compiler initialization. -/
theorem parent_child_le (q path : List Nat) (i : Nat) :
    here q path + below q (path ++ [i]) ≤ below q path := by
  by_cases equal : path = q
  · subst q
    have shorter : (path ++ [i]).isPrefixOf path = false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      have bound := (List.isPrefixOf_iff_prefix.mp yes).length_le
      simp only [List.length_append, List.length_singleton] at bound
      omega
    simp only [here, below, shorter, Bool.false_eq_true, ↓reduceIte]
    have self : path.isPrefixOf path = true := List.isPrefixOf_iff_prefix.mpr (List.prefix_refl path)
    rw [self]
    exact Nat.le_refl 1
  · simp only [here, equal, ↓reduceIte, Nat.zero_add]
    exact child_le q path i


/-- Asynchronous source routes introduce no future source registration.
Consumer: compiler opportunity initialization. -/
theorem async_zero (root : NativeEff) (q : List Nat) (op : NativeOp) (request : Term) (p : Point) :
    current root q (asyncRoute op request p) = 0 := by
  unfold asyncRoute
  repeat' split
  all_goals rfl

/-- `child_le` at a point's child: a provider region's body is its child 0. A step of
`compile_le`. -/
theorem child_point_le (q : List Nat) (p : Point) (i : Nat) :
    below q (p.child i).path ≤ below q p.path :=
  child_le q p.path i

/-- Compiling a source occurrence reserves at most its selected descendant opportunity.
Consumer: load initialization and actual scenario opportunity readers. -/
theorem compile_le (root : NativeEff) (q : List Nat) (e : NativeEff) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) :
    current root q (compileEff e p) ≤ below q p.path := by
  have foldedAsync (op : NativeOp) (request : Term) (point : Point) :
      cata_prim (PrimWeights.currentAlgebra (nativeWeights root q)) (asyncRoute op request point) = 0 :=
    async_zero root q op request point
  revert found
  fun_induction compileEff e p
  all_goals intro found
  case case13 p n hf op request kind value valueFound operation operationFound notExternal notCall notParam =>
    simp only [kind, valueFound, operationFound, current, cata_prim, thunk]
    exact Nat.zero_le _
  case case18 p n hf first rest ih =>
    change current root q (compileEff first (p.child 0)) + below q (p.path ++ [1]) + 0 ≤ below q p.path
    have split := siblings_le q p.path 0 1 (by decide)
    have ih := ih (Agreement.at_child found 0)
    change current root q (compileEff first (p.child 0)) ≤ below q (p.path ++ [0]) at ih
    omega
  case case20 p n hf body handler ih =>
    change current root q (compileEff body (p.child 0)) + below q (p.path ++ [1]) ≤ below q p.path
    have split := siblings_le q p.path 0 1 (by decide)
    have ih := ih (Agreement.at_child found 0)
    change current root q (compileEff body (p.child 0)) ≤ below q (p.path ++ [0]) at ih
    omega
  case case21 p n hf test body handler ih =>
    change current root q (compileEff body (p.child 0)) + below q (p.path ++ [1]) ≤ below q p.path
    have split := siblings_le q p.path 0 1 (by decide)
    have ih := ih (Agreement.at_child found 0)
    change current root q (compileEff body (p.child 0)) ≤ below q (p.path ++ [0]) at ih
    omega
  case case22 p n hf body success failure ih =>
    change current root q (compileEff body (p.child 0)) + below q (p.path ++ [1]) +
      below q (p.path ++ [2]) ≤ below q p.path
    have ih := ih (Agreement.at_child found 0)
    change current root q (compileEff body (p.child 0)) ≤ below q (p.path ++ [0]) at ih
    have split01 := siblings_le q p.path 0 1 (by decide)
    have split02 := siblings_le q p.path 0 2 (by decide)
    have split12 := siblings_le q p.path 1 2 (by decide)
    have parentBound : below q p.path ≤ 1 := by unfold below; split <;> omega
    omega
  case case23 p n hf body finalizer ih =>
    change current root q (compileEff body (p.child 0)) + below q (p.path ++ [1]) + here q p.path ≤ below q p.path
    have split := siblings_le q p.path 0 1 (by decide)
    have parent0 := parent_child_le q p.path 0
    have parent1 := parent_child_le q p.path 1
    have ih := ih (Agreement.at_child found 0)
    change current root q (compileEff body (p.child 0)) ≤ below q (p.path ++ [0]) at ih
    have parentBound : below q p.path ≤ 1 := by unfold below; split <;> omega
    omega
  case case25 p n hf body noExit ih =>
    exact Nat.le_trans (ih (Agreement.at_child found 0)) (child_le q p.path 0)
  case case46 p n hf saved body mask ih =>
    exact Nat.le_trans (ih (Agreement.at_child found 0)) (child_le q p.path 0)
  case case48 p n hf definitions declarations body exports ih =>
    exact Nat.le_trans (ih (Agreement.at_child found 1)) (child_le q p.path 1)
  case case34 p n hf body options =>
    simp only [current, cata_prim, thunk, name, push, found, Nat.zero_add, Nat.add_zero]
    exact Nat.le_refl _
  case case40 p n hf key value body v term =>
    simp only [updateContextAt, current, cata_prim, thunk, name, push, Nat.zero_add, Nat.add_zero]
    exact child_le q p.path 0
  all_goals aesop (add norm simp [current, cata_prim, thunk, name, push, frontier, badShape,
    Prim.ofExit, updateContextAt, found, foldedAsync]) (add safe apply [child_le, child_point_le])


/-- Resolving an existing source point retains the compiler's opportunity bound.
Consumer: actual Atomic and Workers initial source readers. -/
theorem resolve_le (root : NativeEff) (q : List Nat) (p : Point) :
    current root q (resolve root p) ≤ below q p.path := by
  unfold resolve
  split
  · exact compile_le root q _ p (by assumption)
  · exact Nat.zero_le _


/-- A source child cannot return to its parent's selected registration address.
Consumer: actual acquisition and finalizer response equations. -/
theorem child_self_zero (path : List Nat) (i : Nat) : below path (path ++ [i]) = 0 := by
  have noPrefix : (path ++ [i]).isPrefixOf path = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    have length := (List.isPrefixOf_iff_prefix.mp yes).length_le
    simp only [List.length_append, List.length_singleton] at length
    omega
  simp only [below, noPrefix, Bool.false_eq_true, ↓reduceIte]

/-- A captured release cannot revisit its acquisition's own source address.
Consumer: the actual Workers registration producer. -/
theorem fin_self_zero (p : Point) (acquired : Val) (context : Ctx) :
    fin p.path (.foreign (p.capture acquired context)) = 0 := by
  exact child_self_zero p.path 1

/-- The frame projection counts active execution separately from saved future callbacks. -/
def frame (root : NativeEff) (q : List Nat)
    (f : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Nat :=
  current root q f.current + (f.stack.map (saved root q)).sum

/-- Actual push events spend their selected source opportunity. -/
def event (q : List Nat) : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .pushed code => push q code
  | _ => 0

/-- An actual onExit push records the opportunity and excludes the body's saved copy.
Consumer: actual Atomic source-use reader. -/
theorem exit_push (root : NativeEff) (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (f : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (body : NCode)
    (p : Point) (flag : Bool) :
    frame root q {f with current := body, stack := .onExit body (.fin p) flag :: f.stack} +
      event q (.pushed (.onExit body (.fin p) flag)) =
      frame root q {f with current := .onExit body (.fin p) flag} ∧
    ({f with current := .onExit body (.fin p) flag}).step interp =
      (.running {f with current := body, stack := .onExit body (.fin p) flag :: f.stack},
        [.pushed (.onExit body (.fin p) flag)]) := by
  refine ⟨?_, FrameFiber.step_onExit interp f body (.fin p) flag⟩
  simp only [frame, current, cata_prim, saved, event, push, List.map_cons, List.sum_cons]
  omega

/-- An actual acquisition registration push consumes its source opportunity.
Consumer: actual Workers source-use reader. -/
theorem registration_push (root : NativeEff) (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (f : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (scope : Nat)
    (acquired : Val) (capture : Capture) :
    let body : NCode := .sync (.op (.scopeAdd scope (.foreign capture)))
    let callback : EffName := .afterScopeAdd acquired (.foreign capture)
    frame root q {f with current := body, stack := .onSuccess body callback :: f.stack} +
      event q (.pushed (.onSuccess body callback)) =
      frame root q {f with current := .onSuccess body callback} ∧
    ({f with current := .onSuccess body callback}).step interp =
      (.running {f with current := body, stack := .onSuccess body callback :: f.stack},
        [.pushed (.onSuccess body callback)]) := by
  dsimp only
  refine ⟨?_, FrameFiber.step_onSuccess interp f _ _⟩
  simp only [frame, current, cata_prim, saved, event, push, List.map_cons, List.sum_cons]
  omega


/-- The actual acquisition child cannot reserve another visit to the acquisition point.
Consumer: Workers acquisition-to-registration source flow. -/
theorem acquired_child_zero (root : NativeEff) (p : Point) :
    current root p.path (resolve root (p.child 0)) = 0 := by
  have bound := resolve_le root p.path (p.child 0)
  change current root p.path (resolve root (p.child 0)) ≤ below p.path (p.path ++ [0]) at bound
  rw [child_self_zero] at bound
  exact Nat.le_zero.mp bound

/-- A successful acquisition retains exactly one future registration opportunity.
Consumer: Workers acquisition-to-registration source flow. -/
theorem acquire_in_one (root : NativeEff) (p : Point) (context : Ctx) (scope : Nat) :
    current root p.path (contAOf root (.acquireIn p context) (.scopeHandle scope)) = 1 := by
  change current root p.path (resolve root (p.child 0)) +
    (here p.path p.path + below p.path (p.path ++ [1])) + 0 = 1
  simp only [acquired_child_zero, child_self_zero, here, ↓reduceIte, Nat.zero_add, Nat.add_zero]

/-- Acquiring a value turns its one opportunity into the matching registration template.
Consumer: Workers registration push debit. -/
theorem acquired_one (root : NativeEff) (p : Point) (context : Ctx) (scope : Nat) (acquired : Val) :
    current root p.path (contAOf root (.acquired p context scope) acquired) = 1 := by
  simp only [contAOf, current, cata_prim, thunk, name, push, fin_self_zero, Nat.zero_add]
  simp only [here, Point.capture, ↓reduceIte]

/-- Every response to that exact registration resolves no second acquisition opportunity.
Consumer: Workers registration response debit. -/
theorem response_zero (root : NativeEff) (p : Point) (context : Ctx) (acquired answer : Val) :
    current root p.path (contAOf root (.afterScopeAdd acquired (.foreign (p.capture acquired context))) answer) = 0 := by
  unfold contAOf
  split
  · rfl
  · split
    · simp only [finProgram, embed, current, cata_prim, thunk, name, push, fin_self_zero, Nat.add_zero]
    · rfl


/-- The impending selected push is part of its active source opportunity.
Consumer: actual Atomic source initialization. -/
theorem push_le_current (root : NativeEff) (q : List Nat) (code : NCode) :
    push q code ≤ current root q code := by
  fun_cases push q code
  case case1 => exact Nat.le_add_left _ _
  case case2 => exact Nat.le_add_left _ _
  case case3 => exact Nat.zero_le _

end Effect4.Program.SourceScope.Opportunities
