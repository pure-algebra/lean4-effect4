import Effect4.Laws.Program.FinalizerSource
import Effect4.Laws.Program.FinalizerPlaces

/-!
Concept: scope-lifetime-finalization, R11.
Question: delayed layer-body reservations of `once_placed_outside_census`.
Consumer: the unrestricted source callback and compiler bound.
The projection reads only existing provide-layer callbacks.
The generated primitive fold combines it with source and custody-transfer reservations.
These algebra and compiler facts establish no whole-history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Pointwise addition combines two readings of the existing primitive signature. -/
def addWeights (first second : PrimWeights.Model EffName EffThunk) :
    PrimWeights.Model EffName EffThunk where
  name callback := first.name callback + second.name callback
  thunk suspended := first.thunk suspended + second.thunk suspended
  successPush callback := first.successPush callback + second.successPush callback
  exitPush callback flag := first.exitPush callback flag + second.exitPush callback flag

/-- Signature equations make the sum of two folds a homomorphism of the combined algebra. -/
private def addHom (first second : PrimWeights.Model EffName EffThunk) :
    PrimHom (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)
      (PrimWeights.currentAlgebra (addWeights first second)) where
  f_prim code := cata_prim (PrimWeights.currentAlgebra first) code +
    cata_prim (PrimWeights.currentAlgebra second) code
  h_prim_success := fun _ => rfl
  h_prim_failure := fun _ => rfl
  h_prim_sync := fun _ => rfl
  h_prim_suspend := fun _ => rfl
  h_prim_withFiber := fun _ => rfl
  h_prim_yieldableError := fun _ => rfl
  h_prim_iterator := fun _ _ => rfl
  h_prim_onSuccess := by intros; dsimp only [cata_prim, addWeights]; omega
  h_prim_onSuccessConst := by intros; dsimp only [cata_prim, addWeights]; omega
  h_prim_onFailure := by intros; dsimp only [cata_prim, addWeights]; omega
  h_prim_onSuccessAndFailure := by intros; dsimp only [cata_prim, addWeights]; omega
  h_prim_exitFrame := fun _ => rfl
  h_prim_onExit := by intros; dsimp only [cata_prim, addWeights]; omega
  h_prim_setInterruptible := fun _ => rfl
  h_prim_whileLoop := fun _ _ => rfl
  h_prim_yieldNowWith := fun _ => rfl
  h_prim_async := by
    intro register signal cancel
    cases cancel <;> rfl
  h_prim_asyncFinalizer := fun _ => rfl

/-- Fold agreement follows from the generated homomorphism theorem. -/
theorem current_add (first second : PrimWeights.Model EffName EffThunk) (code : NCode) :
    cata_prim (PrimWeights.currentAlgebra (addWeights first second)) code =
      cata_prim (PrimWeights.currentAlgebra first) code +
        cata_prim (PrimWeights.currentAlgebra second) code :=
  (hom_eq_cata_prim (addHom first second) code).symm

/-- A provide-layer callback retains the user's body while the layer itself builds. -/
def layerBodyName (q : List Nat) : EffName → Nat
  | .provideLayerWith point | .provideLayerBody point =>
      SourceScope.Opportunities.below q (point.path ++ [1])
  | _ => 0

abbrev layerBodyWeights (q : List Nat) : PrimWeights.Model EffName EffThunk where
  name := layerBodyName q
  thunk := fun _ => 0

abbrev layerBodyCurrent (q : List Nat) (code : NCode) : Nat :=
  cata_prim (PrimWeights.currentAlgebra (layerBodyWeights q)) code

/-- An asynchronous source operation introduces no provide-layer callback. -/
theorem async_layerBody_zero (q : List Nat) (op : NativeOp) (request : Term) (point : Point) :
    layerBodyCurrent q (asyncRoute op request point) = 0 := by
  unfold asyncRoute
  repeat' split
  all_goals rfl

/-- Compilation introduces the layer-body reservation only when its suspension later opens. -/
theorem compile_layerBody_zero (q : List Nat) (program : NativeEff) (point : Point) :
    layerBodyCurrent q (compileEff program point) = 0 := by
  have asyncZero (op : NativeOp) (request : Term) (point : Point) :
      cata_prim (PrimWeights.currentAlgebra (layerBodyWeights q)) (asyncRoute op request point) = 0 :=
    async_layerBody_zero q op request point
  fun_induction compileEff program point
  all_goals aesop (add norm simp [layerBodyCurrent, cata_prim, layerBodyName,
    frontier, badShape, Prim.ofExit, updateContextAt, asyncZero])

/-- The full source reading adds delayed layer-body reservations through the same generated fold. -/
abbrev fullWeights (root : NativeEff) (q : List Nat) :=
  addWeights (nativeWeights root q) (layerBodyWeights q)

abbrev fullCurrent (root : NativeEff) (q : List Nat) (code : NCode) : Nat :=
  cata_prim (PrimWeights.currentAlgebra (fullWeights root q)) code

/-- Every compiled source retains the existing selected-source bound, including delayed layer bodies. -/
theorem compile_full_le (root : NativeEff) (q : List Nat) (program : NativeEff) (point : Point)
    (found : Node.at_ (.eff root) point.path = some (.eff program)) :
    fullCurrent root q (compileEff program point) ≤ SourceScope.Opportunities.below q point.path := by
  unfold fullCurrent fullWeights
  rw [current_add]
  change current root q (compileEff program point) + layerBodyCurrent q (compileEff program point) ≤ _
  rw [compile_layerBody_zero, Nat.add_zero]
  exact Nat.le_trans (current_le root q _) (SourceScope.Opportunities.compile_le root q program point found)

/-- The shared paired fold computes the full saved reading with delayed layer bodies. -/
abbrev fullSaved (root : NativeEff) (q : List Nat) (code : NCode) : Nat :=
  (cata_prim (PrimWeights.pairedAlgebra (fullWeights root q)
    (savedSuccess q (fullWeights root q).name)) code).2

/-- Native administrative hooks retain the full saved source and layer-body reading. -/
theorem full_ensure_saved (root : NativeEff) (q : List Nat) (code : NCode) (fiber : SourceFrame) :
    ((code.ensure fiber).1.stack.map (fullSaved root q)).sum =
      (fiber.stack.map (fullSaved root q)).sum := by
  fun_cases Prim.ensure code fiber
  all_goals simp only [fullSaved, List.map_cons, List.sum_cons, Nat.zero_add]

/-- Administrative replacement hooks carry no source or delayed layer body. -/
theorem full_ensure_zero (root : NativeEff) (q : List Nat) (code : NCode)
    (fiber : SourceFrame) (next : NCode) (found : (code.ensure fiber).2 = some next) :
    fullCurrent root q next = 0 := by
  revert found
  fun_cases Prim.ensure code fiber
  all_goals intro found
  all_goals aesop (add norm simp [fullCurrent, cata_prim])

/-- The complete source and delayed-body reading uses the existing generic frame model. -/
def fullFrameModel (root : NativeEff) (q : List Nat) : FinalizerPlaces.SourceModel where
  current := fullCurrent root q
  saved := fullSaved root q
  ensure_stack := fun code fiber => Nat.le_of_eq (full_ensure_saved root q code fiber)
  ensure_replacement := full_ensure_zero root q

/-- Existing frame, race, queue and snapshot places share the full source reading. -/
abbrev fullLedger (root : NativeEff) (q : List Nat) :=
  FinalizerPlaces.ledger (fullFrameModel root q) (consumedFrame q) (producedFrame q)

/-- Actual race launch conserves the full source reading, including delayed layer bodies. -/
theorem full_launch_balance (root : NativeEff) (table : RowTable) (q : List Nat)
    (machine : NativeMachine) (raceId : Nat) (rest : List FinalizerPlaces.SourceCommand)
    (snapshot : List FinalizerPlaces.SourceTask) (unique : (machine.races.map Race.id).Nodup) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) machine (.launch raceId) rest
    (fullLedger root q).Balanced machine (.launch raceId :: rest) snapshot out.1 out.2 snapshot :=
  FinalizerPlaces.launch_balance root table (fullFrameModel root q)
    (consumedFrame q) (producedFrame q) machine raceId rest snapshot unique

/-- The full source reading starts with at most one reservation at every compilation budget. -/
theorem full_load_funded (root : NativeEff) (q : List Nat) (fuel : Nat) :
    (fullLedger root q).Funded 1 (Api.load root fuel) [] [] := by
  have compiled := compile_full_le root q root (rootPoint fuel) (by rfl)
  change fullCurrent root q (compileEff root (rootPoint fuel)) ≤ 1 at compiled
  simpa only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued,
    fullLedger, FinalizerPlaces.ledger, fullFrameModel, FrameWeights.frame, FiberSum.total,
    Api.load, RunMachine.empty, RunFiber.make, FrameFiber.start,
    List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.zero_add, Nat.add_zero,
    Api.compile, compile] using compiled

/-- Opening a provide-layer callback retains the user's body during either layer-build route. -/
theorem provide_layer_with_le (root : NativeEff) (q : List Nat) (point : Point) (value : Val) :
    fullCurrent root q (contAOf root (.provideLayerWith point) value) ≤
      (fullWeights root q).name (.provideLayerWith point) := by
  unfold contAOf provideLayerWithK
  repeat' split
  all_goals aesop (add norm simp [fullCurrent, cata_prim, fullWeights, addWeights,
    layerBodyWeights, nativeWeights, layerBodyName, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, badShape]) (add safe cases [Bool])

/-- The built layer hands the saved reservation to the user's actual child-one region. -/
theorem provide_layer_body_le (root : NativeEff) (q : List Nat) (point : Point) (value : Val) :
    fullCurrent root q (contAOf root (.provideLayerBody point) value) ≤
      (fullWeights root q).name (.provideLayerBody point) := by
  unfold contAOf provideLayerBodyK
  repeat' split
  all_goals aesop (add norm simp [fullCurrent, cata_prim, fullWeights, addWeights,
    layerBodyWeights, nativeWeights, layerBodyName, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, badShape,
    updateContextAt, Prim.ofExit, Point.child]) (add safe cases [Exit])

/-- Every actual resolution retains the full source bound at its existing address. -/
theorem full_resolve_le (root : NativeEff) (q : List Nat) (point : Point) :
    fullCurrent root q (resolve root point) ≤ SourceScope.Opportunities.below q point.path := by
  unfold resolve
  split
  · exact compile_full_le root q _ point (by assumption)
  · exact Nat.zero_le _

/-- A root-definition redirect cannot expose a once-placed selected source.
The point's request value, environment, parameter stack and call identity remain arbitrary. -/
theorem definition_full_zero (root : NativeEff) (q : List Nat) (point : Point)
    (index : Nat) (path : List Nat) (body : defBodyPath root index = some path)
    (address : point.path = path) (placed : OncePlaced (.eff root) q = true) :
    fullCurrent root q (resolve root point) = 0 := by
  cases root
  case defs decls bodies main layers =>
    change (if index < bodies.toList.length then
      some (0 :: List.replicate index 1 ++ [0]) else none) = some path at body
    split at body
    · have path_eq := Option.some.inj body
      have bounded := full_resolve_le (.defs decls bodies main layers) q point
      rw [address, ← path_eq, List.cons_append,
        FinalizerPlacement.definition_body_zero decls bodies main layers q _ placed] at bounded
      exact Nat.eq_zero_of_le_zero bounded
    · cases body
  all_goals cases body

/-- Every stored argument site remains below its argument-list source reservation.
Consumer: parameter redirects in the outside-census finalizer proof. -/
theorem argument_site_le (q path : List Nat) (env : List Val)
    (args : Effs NativeOp) (site : ArgSite) (member : site ∈ argSitesAt path env args) :
    SourceScope.Opportunities.below q site.path ≤ SourceScope.Opportunities.below q path := by
  fun_induction argSitesAt path env args
  case case1 => cases member
  case case2 path head rest ih =>
    simp only [List.mem_cons] at member
    cases member with
    | inl equal =>
      cases equal
      exact SourceScope.Opportunities.child_le q path 0
    | inr tail =>
      exact Nat.le_trans (ih tail) (SourceScope.Opportunities.child_le q path 1)

/-- Passed programs cannot contain a selected once-placed source.
Consumer: the parameter-stack annotation created by actual invocation redirects. -/
theorem invocation_argument_zero (root : NativeEff) (q : List Nat) (point : Point)
    (callee : Nat) (request : Term) (args : Effs NativeOp)
    (found : Node.at_ (.eff root) point.path = some (.eff (.invoke callee request args)))
    (placed : OncePlaced (.eff root) q = true) (site : ArgSite)
    (member : site ∈ argSitesAt (point.path ++ [0]) point.env args) :
    SourceScope.Opportunities.below q site.path = 0 := by
  have bounded := argument_site_le q (point.path ++ [0]) point.env args site member
  rw [FinalizerPlacement.forbidden_child_zero (.eff root)
    (.eff (.invoke callee request args)) q point.path 0 found rfl placed] at bounded
  exact Nat.eq_zero_of_le_zero bounded

/-- A call stack records only passed programs outside the selected source.
Consumer: full-source parameter redirects, which restore an older argument site. -/
def ParamsClear (q : List Nat) (params : List (List ArgSite)) : Prop :=
  ∀ sites ∈ params, ∀ site ∈ sites, SourceScope.Opportunities.below q site.path = 0

/-- Invocation records a clear argument frame while retaining every older frame.
Consumer: the parameter-stack part of the full native ownership invariant. -/
theorem invocation_params_clear (root : NativeEff) (q : List Nat) (point : Point)
    (callee : Nat) (request : Term) (args : Effs NativeOp)
    (found : Node.at_ (.eff root) point.path = some (.eff (.invoke callee request args)))
    (placed : OncePlaced (.eff root) q = true) (old : ParamsClear q point.params) :
    ParamsClear q (argSitesAt (point.path ++ [0]) point.env args :: point.params) := by
  intro sites member site selected
  cases member with
  | head => exact invocation_argument_zero root q point callee request args found placed site selected
  | tail _ member => exact old sites member site selected

/-- Returning to a stored parameter site exposes no selected source, at any restored environment.
Consumer: the actual parameter-suspension redirect of the full source debit. -/
theorem parameter_resolve_zero (root : NativeEff) (q : List Nat) (point : Point)
    (sites : List ArgSite) (rest : List (List ArgSite)) (site : ArgSite)
    (stack : point.params = sites :: rest) (clear : ParamsClear q point.params)
    (selected : site ∈ sites) (value : Val) :
    fullCurrent root q (resolve root
      { point.redirect site.path with env := site.env ++ [value], params := rest, call := point.call.tail }) = 0 := by
  have zero := clear sites (by rw [stack]; exact List.mem_cons_self) site selected
  have bounded := full_resolve_le root q
    { point.redirect site.path with env := site.env ++ [value], params := rest, call := point.call.tail }
  change fullCurrent root q _ ≤ SourceScope.Opportunities.below q site.path at bounded
  rw [zero] at bounded
  exact Nat.eq_zero_of_le_zero bounded

end Effect4.Program.FinalizerSource
