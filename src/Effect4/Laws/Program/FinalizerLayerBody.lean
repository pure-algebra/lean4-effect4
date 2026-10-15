import Effect4.Laws.Program.FinalizerSource

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

/-- Opening a provide-layer callback retains the user's body during either layer-build route. -/
theorem provide_layer_with_le (root : NativeEff) (q : List Nat) (point : Point) (value : Val) :
    current root q (contAOf root (.provideLayerWith point) value) ≤
      (nativeWeights root q).name (.provideLayerWith point) := by
  unfold contAOf provideLayerWithK
  repeat' split
  all_goals aesop (add norm simp [current, cata_prim, nativeWeights, name,
    name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, badShape]) (add safe cases [Bool])

/-- The built layer hands the saved reservation to the user's actual child-one region. -/
theorem provide_layer_body_le (root : NativeEff) (q : List Nat) (point : Point) (value : Val) :
    current root q (contAOf root (.provideLayerBody point) value) ≤
      (nativeWeights root q).name (.provideLayerBody point) := by
  unfold contAOf provideLayerBodyK
  repeat' split
  all_goals aesop (add norm simp [current, cata_prim, nativeWeights, name,
    name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, badShape,
    updateContextAt, Prim.ofExit, Point.child]) (add safe cases [Exit])

/-- A root-definition redirect cannot expose a once-placed selected source.
The point's request value, environment, parameter stack and call identity remain arbitrary. -/
theorem definition_full_zero (root : NativeEff) (q : List Nat) (point : Point)
    (index : Nat) (path : List Nat) (body : defBodyPath root index = some path)
    (address : point.path = path) (placed : OncePlaced (.eff root) q = true) :
    current root q (resolve root point) = 0 := by
  cases root
  case defs decls bodies main layers =>
    change (if index < bodies.toList.length then
      some (0 :: List.replicate index 1 ++ [0]) else none) = some path at body
    split at body
    · have path_eq := Option.some.inj body
      have bounded := resolve_le (.defs decls bodies main layers) q point
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
    current root q (resolve root
      { point.redirect site.path with env := site.env ++ [value], params := rest, call := point.call.tail }) = 0 := by
  have zero := clear sites (by rw [stack]; exact List.mem_cons_self) site selected
  have bounded := resolve_le root q
    { point.redirect site.path with env := site.env ++ [value], params := rest, call := point.call.tail }
  change current root q _ ≤ SourceScope.Opportunities.below q site.path at bounded
  rw [zero] at bounded
  exact Nat.eq_zero_of_le_zero bounded

end Effect4.Program.FinalizerSource
