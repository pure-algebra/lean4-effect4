import Effect4.Laws.Program.CodeClosure.Configuration
import Effect4.Laws.Program.Interference

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: both source configuration instances through actual settlement and observer words.
The existing structural edit relation transports the supplied code annotation.
The only new current code is a failure licensed by the supplied predicate.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Configuration
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- A fresh cause updates metadata or installs a failure, retaining all source captures. -/
theorem interrupt_cause_at (model : Model) (failure : ∀ cause, model.code (.failure cause)) (cause : CauseV)
    (fiber : SourceFiber) (held : FiberAt model fiber) :
    FiberAt model (interruptWithCause cause fiber).1 := by
  unfold interruptWithCause
  dsimp only
  repeat' split
  all_goals aesop (add safe constructors [FiberAt]) (add norm simp [FrameAt]) (add safe apply [failure]) (add safe cases [FiberAt])

/-- Source ownership is an instance of the shared structural edit word. -/
theorem fiber_other_edits_at (model : Model) (failure : ∀ cause, model.code (.failure cause)) {before after : SourceFiber}
    (edits : Moves.OtherEdits before after) (held : FiberAt model before) : FiberAt model after := by
  induction edits with
  | refl => exact held
  | tail _ edit ih =>
    cases edit with
    | observe => exact ⟨ih.frame, ih.pending, ih.dispatcher⟩
    | filterObservers => exact ⟨ih.frame, ih.pending, ih.dispatcher⟩
    | interruptCause cause => exact interrupt_cause_at model failure cause _ ih

/-- The native message word retains source ownership and creates only evaluation commands.
Consumer: settlement and the eager countdown and scope-link adapters. -/
theorem fiber_edits_at (model : Model) (failure : ∀ cause, model.code (.failure cause)) (edits : List (FiberEdit Err Defect FiberId Ann))
    (m : NativeMachine) (held : ConfigurationAt model m) :
    ConfigurationAt model (applyFiberEdits edits m).1 ∧ CommandsAt model (applyFiberEdits edits m).2 := by
  have shape := RunMachine.applyFiberEdits_shape edits m
  have counter := congrArg (fun machine : NativeMachine => machine.nextId) shape.1
  obtain ⟨born, rows⟩ := (Moves.InterferesWithLookup.fiberEdits edits m).backward.births
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro fiber member
    rcases rows fiber member with ⟨before, present, edits⟩ | ⟨lower, upper, _⟩
    · exact fiber_other_edits_at model failure edits (held.fibers before present)
    · exact False.elim ((Nat.not_lt_of_ge lower) (counter ▸ upper))
  · simpa only [congrArg (fun machine : NativeMachine => machine.races) shape.1] using held.races
  · simpa only [congrArg (fun machine : NativeMachine => machine.state) shape.1] using held.scopes
  · intro command member
    obtain ⟨target, same⟩ := shape.2 command member
    subst command
    trivial

/-- A queued scope link retains the configuration before its addressed message. -/
theorem link_edits_at (model : Model) (root : NativeEff) (completed) (table : RowTable)
    (link : ∀ mode scope fiber (state next : Stores) key, model.scopes state.scopes →
      (interpAt root completed table).scopeLinkFiber mode scope fiber state = some (next, key) →
      model.scopes next.scopes) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (owned : ConfigurationAt model m) :
    ConfigurationAt model (linkScopeEdits (interpAt root completed table) m mode scope target who extra).1 := by
  unfold linkScopeEdits
  split
  · exact configuration_halt model m _ owned
  · split
    · exact configuration_halt model m _ owned
    · exact configuration_emit model m _ owned
  · split
    · exact configuration_halt model m _ owned
    · split
      · exact owned
      · split
        · exact configuration_halt model m _ owned
        · rename_i state key found
          exact configuration_emit model _ _ (configuration_store model m state owned
            (link mode scope target m.state state key owned.scopes found))

/-- Actual linking applies the same source-preserving addressed word. -/
theorem link_at (model : Model) (root : NativeEff) (completed) (table : RowTable)
    (failure : ∀ cause, model.code (.failure cause))
    (link : ∀ mode scope fiber (state next : Stores) key, model.scopes state.scopes →
      (interpAt root completed table).scopeLinkFiber mode scope fiber state = some (next, key) →
      model.scopes next.scopes) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (owned : ConfigurationAt model m) :
    ConfigurationAt model (linkScope (interpAt root completed table) m mode scope target who extra).1 ∧
      CommandsAt model (linkScope (interpAt root completed table) m mode scope target who extra).2 :=
  fiber_edits_at model failure _ _ (link_edits_at model root completed table link m mode scope target who extra owned)

end Effect4.Program.CodeClosure.Configuration
