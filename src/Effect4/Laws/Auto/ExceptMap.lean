/-!
# Laws.Auto.ExceptMap — moving an `Except`'s error, and its value, through a computation

`Except.mapError f` changes a computation's error and keeps its value; `Except.map g` changes
its value and keeps its error. These facts push each through the connectives of a checker:
bind, pure, throw and a conditional. They name `Except` only, so they stand here, beside the
inversion lemmas (`Laws/Auto/Inversion.lean`), and not in a consumer.

Their consumer is the checker's base law (`Checker.check_rebase`,
`Laws/Program/Typing/Rebase.lean`), a step of the claim `checker-base-natural`.
-/

set_option autoImplicit false

namespace Effect4.Laws.Auto.ExceptMap

variable {ε α β : Type} (f : ε → ε)

theorem mapError_bind (m : Except ε α) (k : α → Except ε β) :
    (m >>= k).mapError f = m.mapError f >>= fun a => (k a).mapError f := by
  cases m <;> rfl

theorem mapError_pure (a : α) : (pure a : Except ε α).mapError f = pure a := rfl

theorem mapError_throw (e : ε) : (throw e : Except ε α).mapError f = throw (f e) := rfl

theorem mapError_ite (c : Prop) [Decidable c] (a b : Except ε α) :
    (if c then a else b).mapError f = if c then a.mapError f else b.mapError f := by
  split <;> rfl

/-- A loop over a list moves the error through each step: a checker's `for` over a row's keys. -/
theorem mapError_forIn {γ : Type} (xs : List γ) (b : β) (body : γ → β → Except ε (ForInStep β)) :
    (forIn xs b body).mapError f = forIn xs b fun x s => (body x s).mapError f := by
  induction xs generalizing b with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.forIn_cons]
    cases body x b with
    | error e => rfl
    | ok step =>
      cases step with
      | done c => rfl
      | yield c => exact ih c

theorem mapError_map_bind {γ : Type} (m : Except ε α) (g : α → β) (k : β → Except ε γ) :
    (m.map g).mapError f >>= k = m.mapError f >>= fun a => k (g a) := by
  cases m <;> rfl

theorem map_bind (g : β → α) {γ : Type} (m : Except ε γ) (k : γ → Except ε β) :
    (m >>= k).map g = m >>= fun a => (k a).map g := by
  cases m <;> rfl

theorem map_pure (g : α → β) (a : α) : (pure a : Except ε α).map g = pure (g a) := rfl

theorem map_throw (g : α → β) (e : ε) : (throw e : Except ε α).map g = throw e := rfl

theorem map_ite (g : α → β) (c : Prop) [Decidable c] (a b : Except ε α) :
    (if c then a else b).map g = if c then a.map g else b.map g := by
  split <;> rfl

end Effect4.Laws.Auto.ExceptMap
