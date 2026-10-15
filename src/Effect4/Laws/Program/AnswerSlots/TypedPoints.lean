import Effect4.Laws.Program.AnswerSlots.TypedStored

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: real callback edges retain protected source entry.
Reach: the existing callback source constructors and certified capture.
Limit: no command history invariant follows from local source transport.
Consumer: the protected saved callback and thunk family.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- An ordinary callback argument retains its actual source, leading bindings and entry permission. -/
theorem argument_source (spec : Spec) (point : Point) (index : Nat) (value : Val)
    (next : SourceScope.NextAt spec.root point index 1) (slots : Prefix spec.bindings point.env)
    (edge : index ≠ 1 ∨ ¬ SourceScope.AcquisitionAt spec.root point.path) :
    SourcePoint spec (point.childWith index value) :=
  ⟨SourceScope.childWith_at spec.root point index value next, childWith slots index value,
    .inl (childWith_ordinary spec.root spec.acquisitions (sites spec) point index value edge)⟩

/-- A zero child retains its actual source and cannot enter a release child. -/
theorem zero_source (spec : Spec) (point : Point)
    (next : SourceScope.NextAt spec.root point 0 0) (slots : Prefix spec.bindings point.env) :
    SourcePoint spec (point.child 0) :=
  ⟨SourceScope.child_at spec.root point 0 next, slots, .inl (ordinary_zero spec point)⟩

/-- A real source bind callback enters its own continuation with an ordinary answer. -/
theorem cont_source (spec : Spec) (point : Point) (value : Val)
    (named : OrdinaryName spec (.cont point)) : SourcePoint spec (point.childWith 1 value) :=
  ⟨SourceScope.childWith_at spec.root point 1 value named.1.1,
    childWith named.2.1 1 value,
    .inl (cont_ordinary spec.root spec.acquisitions (sites spec) point value named.1)⟩

/-- A real source match callback cannot enter an acquisition's release. -/
theorem value_source (spec : Spec) (point : Point) (value : Val)
    (named : OrdinaryName spec (.onValue point)) : SourcePoint spec (point.childWith 1 value) := by
  obtain ⟨next, body, success, failure, found⟩ := named.1
  apply argument_source spec point 1 value next named.2.1
  exact .inr (not_acquisition spec.root point _ found (fun _ _ wrong => nomatch wrong))

/-- A real source failure callback cannot enter an acquisition's release. -/
theorem caught_source (spec : Spec) (point : Point) (value : Val)
    (named : OrdinaryName spec (.caught point)) : SourcePoint spec (point.childWith 1 value) := by
  obtain ⟨next, body, handler, found⟩ := named.1
  apply argument_source spec point 1 value next named.2.1
  exact .inr (not_acquisition spec.root point _ found (fun _ _ wrong => nomatch wrong))

/-- A real source selective failure callback cannot enter an acquisition's release. -/
theorem caughtError_source (spec : Spec) (point : Point) (value : Val)
    (named : OrdinaryName spec (.caughtError point)) : SourcePoint spec (point.childWith 1 value) := by
  obtain ⟨next, test, body, handler, found⟩ := named.1
  apply argument_source spec point 1 value next named.2.1
  exact .inr (not_acquisition spec.root point _ found (fun _ _ wrong => nomatch wrong))

/-- An authored onExit callback enters its own finalizer with its closing exit. -/
theorem fin_source (spec : Spec) (point : Point) (value : Val)
    (named : OrdinaryName spec (.fin point)) : SourcePoint spec (point.childWith 1 value) := by
  obtain ⟨next, body, finalizer, found⟩ := named.1
  apply argument_source spec point 1 value next named.2.1
  exact .inr (not_acquisition spec.root point _ found (fun _ _ wrong => nomatch wrong))

/-- The captured release appends its closing exit after its already protected acquired answer. -/
theorem release_source (spec : Spec) (point : Point) (exit : ExitV)
    (next : SourceScope.NextAt spec.root point 1 1) (capture : CapturedPoint spec point) :
    ReleasePoint spec (point.childWith 1 (reifyExitVal exit)) := by
  obtain ⟨slots, identity, member, path, value⟩ := capture
  refine ⟨SourceScope.childWith_at spec.root point 1 _ next, childWith slots 1 _,
    identity, member, ?_, ?_⟩
  · exact congrArg (fun p => p ++ [1]) path
  · change (point.env ++ [reifyExitVal exit])[spec.acquiredIndex identity]? = some (.nat identity)
    exact List.getElem?_append_left (List.getElem?_eq_some_iff.mp value).1 |>.trans value
end Effect4.Program.AnswerSlots.Typed
