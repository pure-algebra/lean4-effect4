import Effect4.Library.PubSub.Data
import Effect4.Step.Elab.Inputs
import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Step.Lists
import Effect4.Laws.Step

/-! Value equations for pubsub-single-steps-agree, Translation Simulation, R10.
The source reading laws consume each equation. These equations cover arbitrary model data.
The latest-source interpretation separately needs Model.Live and fresh registration names.
They establish no runtime identity, delivery, scope, progress, or backpressure claim. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Effect4.PubSub
open Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules

abbrev encoded (s : Model.State) := Model.State.modeledToC s
abbrev named (s : Model.State) (id : Nat) : Inputs Leaves.refused Data.NamedInputs.types :=
  input_values% (Data.NamedInputs) (Leaves.refused) {cell := encoded s, id := id}
abbrev publishing (s : Model.State) (message : Nat) : Inputs Leaves.refused Data.PublishInputs.types :=
  input_values% (Data.PublishInputs) (Leaves.refused) {cell := encoded s, message := message}

namespace Model

/-- Helper of pubsub-single-steps-agree; initial_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem initial_eval : Data.initial.eval (Γ := []) Leaves.refused () = encoded initial := rfl

/-- Helper of pubsub-single-steps-agree; subscribe_reads retains the fresh-name premise. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem subscribe_eval (s : State) (id : Nat) (_fresh : Fresh s id) :
    Data.subscribe.eval Leaves.refused (named s id) = ((), encoded (subscribe s id).2) := by
  change ((), (s.publisherIndex, (s.remaining, (s.subscribers.map Subscriber.modeledToC ++ [Subscriber.modeledToC ⟨id, s.publisherIndex⟩], (s.value.map (fun x => x), ()))))) =
    ((), (s.publisherIndex, (s.remaining, ((s.subscribers ++ [Subscriber.mk id s.publisherIndex]).map Subscriber.modeledToC, (s.value.map (fun x => x), ())))))
  rw [List.map_append]
  rfl

/-- Helper of pubsub-single-steps-agree; tryPublish_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem tryPublish_eval (s : State) (message : Nat) :
    Data.tryPublish.eval Leaves.refused (publishing s message) =
      ((tryPublish s message).1, encoded (tryPublish s message).2) := by
  change (if !(decide (s.remaining = 0)) then (false, encoded s) else
    if decide ((s.subscribers.map Subscriber.modeledToC).length = 0) then (true, encoded s) else
    (true, encoded { s with value := some message, remaining := (s.subscribers.map Subscriber.modeledToC).length, publisherIndex := s.publisherIndex + 1 })) = _
  rw [List.length_map]
  unfold tryPublish
  simp only [bne_eq, Bool.beq_eq_decide_eq]
  cases h : decide (s.remaining = 0) <;> cases subs : s.subscribers <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.isEmpty, List.length_cons, List.length_nil, Nat.succ_ne_zero, decide_false, decide_true]

/-- Helper of poll_eval and unsubscribe_eval, on the registered claim's path. -/
theorem unread_eval (s : State) (id : Nat) :
    (Data.unread (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) = unread s id := by
  unfold Data.unread
  rw [Step.Lists.eval_any]
  change (s.subscribers.map Subscriber.modeledToC).any (fun (sub : Nat × Nat × Unit) =>
    decide (sub.2.1 = id) && !decide (sub.1 = s.publisherIndex)) = _
  rw [List.any_map]
  unfold unread
  simp only [bne_eq, Bool.beq_eq_decide_eq]
  rfl

/-- Helper of poll_eval; the existing map fold updates only the selected logical name. -/
theorem markRead_eval (s : State) (id : Nat) :
    (Data.markRead (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) =
      (s.subscribers.map (fun sub => if sub.id == id then { sub with cursor := s.publisherIndex } else sub)).map Subscriber.modeledToC := by
  unfold Data.markRead
  rw [Step.Lists.eval_map]
  change (s.subscribers.map Subscriber.modeledToC).map (fun sub =>
    if decide (sub.2.1 = id) then (s.publisherIndex, sub.2) else sub) = _
  rw [List.map_map, List.map_map]
  apply congrArg (fun f => s.subscribers.map f)
  funext sub
  simp only [Bool.beq_eq_decide_eq]
  change (if decide (sub.id = id) then Subscriber.modeledToC { sub with cursor := s.publisherIndex } else Subscriber.modeledToC sub) = _
  change (if decide (sub.id = id) then Subscriber.modeledToC { sub with cursor := s.publisherIndex } else Subscriber.modeledToC sub) =
    Subscriber.modeledToC (if decide (sub.id = id) then { sub with cursor := s.publisherIndex } else sub)
  cases decide (sub.id = id) <;> rfl

/-- Helper of pubsub-single-steps-agree; poll_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem poll_eval (s : State) (id : Nat) :
    Data.poll.eval Leaves.refused (named s id) = ((poll s id).1, encoded (poll s id).2) := by
  unfold Data.poll
  change (if decide (s.remaining = 0) || !(Data.unread (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) then
    (none, encoded s) else (s.value.map (fun x => x),
      (s.publisherIndex, (s.remaining - 1,
        ((Data.markRead (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id),
          ((if decide (s.remaining - 1 = 0) then none else s.value.map (fun x => x)), ())))))) = _
  rw [unread_eval, markRead_eval]
  unfold poll
  simp only [Bool.beq_eq_decide_eq]
  split
  · rfl
  · cases s.value <;> split <;> rfl

/-- Helpers of unsubscribe_eval; existing any and removal folds share the named inputs. -/
theorem registered_eval (s : State) (id : Nat) :
    (Data.registered (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) =
      s.subscribers.any (fun sub => sub.id == id) := by
  unfold Data.registered
  rw [Step.Lists.eval_any]
  change (s.subscribers.map Subscriber.modeledToC).any (fun (sub : Nat × Nat × Unit) => decide (sub.2.1 = id)) = _
  rw [List.any_map]
  simp only [Bool.beq_eq_decide_eq]
  rfl

/-- Helper of unsubscribe_eval; remove only the selected logical registration. -/
theorem remove_eval (s : State) (id : Nat) :
    (Data.remove (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) =
      (s.subscribers.filter (fun sub => sub.id != id)).map Subscriber.modeledToC := by
  unfold Data.remove
  rw [Step.Lists.eval_removeBy]
  change (s.subscribers.map Subscriber.modeledToC).filter (fun (sub : Nat × Nat × Unit) => !decide (sub.2.1 = id)) = _
  rw [List.filter_map]
  simp only [bne_eq, Bool.beq_eq_decide_eq]
  rfl

/-- Helper of pubsub-single-steps-agree; unsubscribe_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem unsubscribe_eval (s : State) (id : Nat) :
    Data.unsubscribe.eval Leaves.refused (named s id) = ((), encoded (unsubscribe s id).2) := by
  unfold Data.unsubscribe
  change (if !(Data.registered (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) then
    ((), encoded s) else ((), (s.publisherIndex,
      ((if !decide (s.remaining = 0) && (Data.unread (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) then s.remaining - 1 else s.remaining),
        ((Data.remove (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id),
          ((if decide ((if !decide (s.remaining = 0) && (Data.unread (.var (.there .nat (.here cellTy []))) (.var (.here .nat [cellTy]))).eval Leaves.refused (named s id) then s.remaining - 1 else s.remaining) = 0) then none else s.value.map (fun x => x)), ())))))) = _
  rw [unread_eval, registered_eval, remove_eval]
  unfold unsubscribe
  simp only [bne_eq, Bool.beq_eq_decide_eq]
  split
  · rfl
  · split <;> split <;> rfl

/-- Helper of pubsub-single-steps-agree; slide_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem slide_eval (s : State) :
    Data.slide.eval (Γ := Data.CellInputs.types) Leaves.refused (encoded s, ()) = ((), encoded (slide s).2) := by
  change (if decide (s.remaining = 0) then ((), encoded s) else ((), encoded { s with remaining := 0, value := none })) = _
  unfold slide
  simp only [Bool.beq_eq_decide_eq]
  split <;> rfl

end Model
end Effect4.PubSub
