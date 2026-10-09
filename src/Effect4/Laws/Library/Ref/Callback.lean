import Effect4.Laws.Step.Callback
import Effect4.Laws.Step.Store
import Effect4.Laws.Library.Ref.Operations

/-!
# Ref callbacks connect a stored step to an independent transition

Placement: `translation-simulation`, proposed claim `ref-steps-agree`, role simulation, R10.
The typing connector serves `step-language-typed` and `fold-typed-atomic-update`, under R4.
The catalogue plan records these obligations before their proofs.

A caller supplies an independent transition and proves the step's value equation.
The connector supplies its captured reading, native operation, and one-cell agreement.
The typing connector needs typed captures at the caller's scope, with no stability premise.
Consumers are the Ref acceptance programs and the later module callbacks.

Reach: one allocated cell, a pure step, aligned scopes, and the stated reading or typing premises.
Membership, allocation, host execution, scheduling, and whole-run agreement remain separate claims.
-/

set_option autoImplicit false
namespace Effect4.Ref
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules Effect4.Schema Effect4.Schema.Model

/-- A step that computes an independent transition implements one native Ref.modify.
This consumes the shared callback reading law and the independent Ref operation law. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem modify_callback_agrees {L : Leaves} {C B : Ty} {Γ : List Ty}
    (body : Step (C :: Γ) (.prod B C))
    (captures : {t : Ty} → Input Γ t → TermSrc) (vs : Inputs L Γ)
    (transition : CarrierAt L C → CarrierAt L B × CarrierAt L C)
    (cell : CarrierAt L C) {env : Env} {path : List Nat} {vals : List Val}
    {receiver : TermSrc} {q : RefKey} {stores : Stores}
    (depth : vals.length = env.names.length)
    (inputs : ∀ {t : Ty} (x : Input Γ t),
      Reads (captures x) env path vals ((imageAt L t).toVal (x.get vs)))
    (reference : Reads receiver env path vals (Val.cell q))
    (held : refPeek stores.refs q = some ((imageAt L C).toVal cell))
    (canonical : body.canonical = true)
    (meaning : body.eval (Γ := C :: Γ) L (cell, vs) = transition cell)
    (identity : body.IdentityFacts L := by trivial) :
    ∃ term request,
      Step.callback body captures (Authoring.Ref.modifyWith receiver) env path =
        .ok (.perform (.refModifyWith term) request) ∧
      evalTerm vals request = some (Val.cell q) ∧
      syncOpStep (.refModify q term vals) stores =
        some (resultStores (imageAt L C) (Model.modify transition cell) q stores,
          (imageAt L B).toVal (Model.modify transition cell).reply) := by
  obtain ⟨request, requestTree, requestValue⟩ := reference
  have reads := Step.callback_term_reads body depth inputs (env.mint "current") cell
    (reads_minted_last depth path "current" _) canonical identity
  rw [meaning] at reads
  obtain ⟨term, termTree, termValue⟩ := reads
  refine ⟨term, request, ?_, requestValue, ?_⟩
  · change (body.term (Step.callbackSources captures env path (minted (env.mint "current")))
      (env.push [env.mint "current"]) path >>= fun f => receiver env path >>= fun r =>
        Except.ok (Eff.perform (NativeOp.refModifyWith f) r)) = _
    rw [termTree, requestTree]
    rfl
  · exact modify_agrees (imageAt L C) (imageAt L B) cell held transition term vals termValue

/-- Typed captures at the caller's scope suffice for a typed Ref.modify callback.
The source connector supplies stability by freezing and relocation. -/
@[semantics "store-typing" (requirement := R4)]
theorem modify_callback_answers {table : RowTable} {C B : Ty} {Γ : List Ty}
    (body : Step (C :: Γ) (.prod B C))
    (captures : {t : Ty} → Input Γ t → TermSrc)
    {receiver : TermSrc} {s : TypedScope}
    (normalC : C.normalize = C) (formedC : NodesFormed C)
    (normalB : B.normalize = B) (formedB : NodesFormed B)
    (reference : Typed (nativeSignature table) receiver s (.refOf C))
    (inputs : ∀ {t : Ty} (x : Input Γ t), Typed (nativeSignature table) (captures x) s t)
    (facts : body.Facts) :
    Answers (nativeSignature table)
      (Step.callback body captures (Authoring.Ref.modifyWith receiver)) s B := by
  let callback : TermSrc → TermSrc := fun current env path =>
    body.term (Step.callbackSources captures s.env path current) env path
  have checked := answers_refModifyWith normalC formedC normalB formedB reference
    (f := callback) (fun current typed path =>
      Step.callback_term_types (nativeSignature table) rfl body s.depth
        (fun x => inputs x path) (s.env.mint "current") (typed path) facts)
  intro path
  exact checked path

end Effect4.Ref
