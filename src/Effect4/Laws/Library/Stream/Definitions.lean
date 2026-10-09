import Effect4.Library.Stream.Definitions
import Effect4.Laws.Auto.Semantics

/-!
# Declaration relationships of accepted stream sources

Placement: `stream-source-declarations`, compatibility, `store-typing`, R4.
The consumer is the definition-backed source used by Channel transformations.
The plan is `docs/research/2026-10-09-channel-transforms-plan.md`.
Acceptance relates the protocol, state requests and unit close answer to their supplied declarations.
The invocations come from those same declarations.
Applying this law to an installed module requires matching declarations at the invocation names.
This establishes neither body typing nor nonempty batches, execution, finalization or host behavior.
-/

set_option autoImplicit false
namespace Effect4.Stream
open Effect4.Program Effect4.Program.Authoring

/-- An accepted adapter derives its metadata and invocations from the same declarations.
Equality of normalized columns does not establish admission of any definition body. -/
@[semantics "store-typing" (requirement := R4)]
theorem Source.fromDefinitions_declarations
    {opened pull close : DefSrc NativeOp} {arguments : List TermSrc} {source : Source}
    (accepted : Source.fromDefinitions opened pull close arguments = .ok source) :
    pull.answer.normalize = (Program.Stream.pulledTy source.elem source.done).normalize ∧
    opened.answer.normalize = pull.decl.request.normalize ∧
    close.decl.request.normalize = pull.decl.request.normalize ∧
    close.answer.normalize = .unit ∧
    source.opened = Def.invoke opened.name arguments ∧
    (∀ state, source.pull state = Def.invoke pull.name [state]) ∧
    (∀ state, source.close state = Def.invoke close.name [state]) := by
  unfold Source.fromDefinitions at accepted
  split at accepted
  next elem done _ _ =>
    split at accepted
    next protocol =>
      split at accepted
      next openedState =>
        split at accepted
        next closeState =>
          split at accepted
          next closeAnswer =>
            cases accepted
            exact ⟨protocol, openedState, closeState, closeAnswer, rfl, fun _ => rfl, fun _ => rfl⟩
          next => cases accepted
        next => cases accepted
      next => cases accepted
    next => cases accepted
  next => cases accepted

end Effect4.Stream
