import Effect4.Laws.Program.AnswerSlots.TypedCompile

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the actual acquisition return supplies the protected captured identity.
Reach: certified acquisition sites, arbitrary callback views, source fuel and native row tables.
Limit: the dynamic history producer supplies the current typed code and source prefix.
Consumer: the protected saved acquisition edge and the scope-store registration invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- An actual literal source return retains its connection class, including a live fuel frontier. -/
theorem literal_code (spec : Spec) (point : Point) (identity : Nat)
    (source : SourcePoint spec point)
    (found : Node.at_ (.eff spec.root) point.path = some (.eff (.succeed (.lit (.nat identity))))) :
    CodeAt spec (.connection identity) (resolve spec.root point) := by
  rw [Agreement.resolve_of_at found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .inl ⟨amount, source⟩
  | succ fuel =>
    rw [Agreement.compileEff_succeed _ amount]
    rfl

/-- A note's real source continuation returns its acquisition's literal identity. -/
theorem acquisition_return (spec : Spec) (view : List (FiberId × ExitV)) (table : RowTable)
    (identity : Nat) (point : Point) (answer : Val)
    (edge : NameAt spec .root (.connection identity) (.cont point)) :
    CodeAt spec (.connection identity)
      ((interpAt spec.root view table).contA (.cont point) answer) := by
  obtain ⟨member, named, source, path⟩ := edge
  obtain ⟨note, body⟩ := spec.acquisitionBody identity member
  have atBody : Node.at_ (.eff spec.root) point.path =
      some (.eff (.bind note (.succeed (.lit (.nat identity))))) := by rw [path]; exact body
  change CodeAt spec (.connection identity) (resolve spec.root ({point with completed := view}.childWith 1 answer))
  apply literal_code spec
  · exact ⟨SourceScope.childWith_at spec.root _ 1 answer named.1,
      childWith source.2.1 1 answer, .inl
        (cont_ordinary spec.root spec.acquisitions (sites spec) _ answer named)⟩
  · exact Agreement.at_child atBody 1

/-- The source's lexical level fixes the actual position of its acquisition answer. -/
theorem acquired_length (spec : Spec) (identity : Nat) (point : Point)
    (member : identity ∈ spec.identities) (source : SourceScope.At spec.root point)
    (path : point.path = spec.acquirePath identity) : point.env.length = spec.acquiredIndex identity := by
  change SourceScope.levelAt (.eff spec.root) 0 point.path = some point.env.length at source
  rw [path, spec.acquisitionLevel identity member] at source
  exact (Option.some.inj source).symm

/-- Capturing the protected literal gives the exact source, prefix and acquired slot certificate. -/
theorem captured_at (spec : Spec) (identity : Nat) (point : Point) (ctx : Ctx) (scope : Nat)
    (edge : NameAt spec (.connection identity) .root (.acquired point ctx scope)) :
    FinAt spec (.foreign (point.capture (.nat identity) ctx)) := by
  obtain ⟨member, named, source, path⟩ := edge
  refine ⟨SourceScope.capture_at spec.root point (.nat identity) ctx named.1 named.2, ?_⟩
  refine ⟨capture source.2.1 (.nat identity) ctx, identity, member, path, ?_⟩
  change (point.env ++ [.nat identity])[spec.acquiredIndex identity]? = some (.nat identity)
  rw [← acquired_length spec identity point member source.1 path]
  exact List.getElem?_concat_length

/-- The protected acquired callback registers its certified finalizer in the actual native code. -/
theorem acquired_callback (spec : Spec) (view : List (FiberId × ExitV)) (table : RowTable)
    (identity : Nat) (point : Point) (ctx : Ctx) (scope : Nat) (answer : Val)
    (edge : NameAt spec (.connection identity) .root (.acquired point ctx scope))
    (good : ValueAt (.connection identity) answer) :
    CodeAt spec .root ((interpAt spec.root view table).contA (.acquired point ctx scope) answer) := by
  change answer = .nat identity at good
  subst answer
  have captured := captured_at spec identity point ctx scope edge
  change CodeAt spec .root
    (.onSuccess (.sync (.op (.scopeAdd scope (.foreign (point.capture (.nat identity) ctx)))))
      (.afterScopeAdd (.nat identity) (.foreign (point.capture (.nat identity) ctx))))
  refine ⟨.root, ⟨rfl, captured.1, captured.2.1, captured⟩, ?_⟩
  exact ⟨captured.1, captured.2.1, captured⟩
end Effect4.Program.AnswerSlots.Typed
