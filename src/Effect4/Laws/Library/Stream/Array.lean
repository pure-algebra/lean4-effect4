import Effect4.Library.Stream.ArrayModel
import Effect4.Library.Stream.ArrayDefs
import Effect4.Laws.Library.Ref.Callback

/-!
# Array extraction agrees with its independent transition

Placement: claim `stream-array-step-agreement`, role simulation, `translation-simulation`, R10.
The observation retains the extracted batch and next pending cell image.
The reach is one allocated cell with aligned scope, receiver reading and cell-image premises.
`arrayStep_eval` supplies the value equation to the shared Ref callback agreement.
`arrayBatch_answers` serves `step-language-typed`, concept `store-typing`, R4.
Its consumer is `arrayBatch`, which supplies `arrayPull` and the existing Stream consumers.
The laws establish no whole pull, run, schedule, finalization, host, codec or allocation correspondence.
-/

set_option autoImplicit false
namespace Effect4.Stream
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules Effect4.Schema Effect4.Schema.Model

/-- The array step retains the batch and clears the pending list. -/
theorem arrayStep_eval (A : Ty) (L : Leaves) (pending : List (CarrierAt L A)) :
    (arrayStep A).eval (Γ := [.list A]) L (pending, ()) = ArrayModel.pull pending := rfl

/-- One allocated cell step agrees with the independent batch extraction transition. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem arrayStep_agrees (A : Ty) (L : Leaves) (pending : List (CarrierAt L A))
    {env : Env} {path : List Nat} {vals : List Val} {receiver : TermSrc}
    {q : RefKey} {stores : Stores}
    (depth : vals.length = env.names.length)
    (reference : Reads receiver env path vals (Val.cell q))
    (held : refPeek stores.refs q = some ((imageAt L (.list A)).toVal pending)) :
    ∃ term request,
      arrayBatch A receiver env path = .ok (.perform (.refModifyWith term) request) ∧
      evalTerm vals request = some (Val.cell q) ∧
      syncOpStep (.refModify q term vals) stores =
        some (Ref.resultStores (imageAt L (.list A)) (Ref.Model.modify ArrayModel.pull pending) q stores,
          (imageAt L (.list A)).toVal (Ref.Model.modify ArrayModel.pull pending).reply) :=
  Ref.modify_callback_agrees (arrayStep A) arrayCaptures () ArrayModel.pull pending
    depth (fun x => nomatch x) reference held rfl (arrayStep_eval A L pending)

/-- A typed array cell supplies the extracted batch's declared type. -/
@[semantics "store-typing" (requirement := R4)]
theorem arrayBatch_answers {table : RowTable} (A : Ty) {receiver : TermSrc} {s : TypedScope}
    (normal : (Ty.list A).normalize = .list A) (formed : NodesFormed (.list A))
    (reference : Typed (nativeSignature table) receiver s (.refOf (.list A))) :
    Answers (nativeSignature table) (arrayBatch A receiver) s (.list A) :=
  Ref.modify_callback_answers (arrayStep A) arrayCaptures normal formed normal formed
    reference (fun x => nomatch x) (by trivial)

end Effect4.Stream
