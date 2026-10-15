import Effect4.Laws.Program.AnswerSlots.TypedPoints

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual saved value and cause callbacks retain protected source entry.
Reach: the direct lexical fragment and the actual native callback definitions.
Limit: the joint machine and queue history remains a separate producer.
Consumer: the protected saved family and the two crews' cleanup history claims.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- Source regions execute only their certified existing program points. -/
theorem region_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (region : Region) (owned : RegionAt spec region) : CodeAt spec .root (regionCode spec.root region) := by
  cases region with
  | program point => exact resolve_source spec fragment point owned
  | build _ _ _ | buildAdding _ _ _ | construct _ _ => exact owned.elim

/-- Stored failure callbacks expose only completed native exits. -/
theorem store_contE_at (spec : Spec) (name : Name) (cause : CauseV) :
    CodeAt spec .root (embed (Effect4.Machine.contEOf name cause)) := by
  fun_cases Effect4.Machine.contEOf name cause
  all_goals aesop (add norm simp [CodeAt, ValueAt, embed, Prim.ofExit])

/-- A stable cause callback enters its actual ordinary source handler. -/
theorem contE_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (name : EffName) (cause : CauseV) (owned : OrdinaryName spec name) :
    CodeAt spec .root (contEOf spec.root name cause) := by
  revert owned
  fun_cases contEOf spec.root name cause
  case case1 =>
    intro owned
    exact resolve_source spec fragment _ (caught_source spec _ _ owned)
  case case2 =>
    intro owned
    exact resolve_source spec fragment _ (caughtError_source spec _ _ owned)
  all_goals intro owned
  all_goals aesop (add norm simp [CodeAt, ValueAt, OrdinaryName, ProtectedName,
    SourceScope.NameAt, AnswerSlots.NameAt, Prim.ofExit, store_contE_at]) (add safe apply [(resolve_source spec fragment), caught_source, caughtError_source,
      argument_source])

/-- A stable value callback retains protected acquisitions and captured releases. -/
theorem contA_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (name : EffName) (value : Val) (owned : OrdinaryName spec name) :
    CodeAt spec .root (contAOf spec.root name value) := by
  revert owned
  fun_cases contAOf spec.root name value
  case case1 =>
    intro owned
    exact resolve_source spec fragment _ (cont_source spec _ _ owned)
  case case2 =>
    intro owned
    exact resolve_source spec fragment _ (value_source spec _ _ owned)
  case case18 =>
    intro owned
    exact acquireIn_callback spec fragment _ _ _ owned
  case case26 point exit previous =>
    intro owned
    have release := release_source spec point exit owned.1.1 owned.2.2
    exact ⟨rfl, release.1, release.2.1, release⟩
  all_goals intro owned
  all_goals aesop (add norm simp [CodeAt, ValueAt, ThunkAt, NameAt, OrdinaryName, ProtectedName,
    StoreNameAt, FinAt, OpAt, RegionAt, SourceScope.NameAt, SourceScope.ThunkAt, SourceScope.OpAt,
    AnswerSlots.NameAt, AnswerSlots.ThunkAt, AnswerSlots.OpAt, Prim.ofExit, badShape]) (add norm unfold [updateThenK, addCurrentMemoMapK, combineWithK, mergeContextsK, serviceLookupK, bindServiceK]) (add safe apply [(resolve_source spec fragment), (region_at spec fragment), store_contA_at,
      finProgram_at, (acquireIn_callback spec fragment), cont_source, value_source, zero_source,
      release_source])
end Effect4.Program.AnswerSlots.Typed
