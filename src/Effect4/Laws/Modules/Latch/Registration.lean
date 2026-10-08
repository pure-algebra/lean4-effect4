import Effect4.Modules.Latch.Registration
import Effect4.Laws.Modules.Latch.Steps
import Effect4.Laws.Modules.Step.Scope
import Effect4.Laws.Modules.Step.Lists

/-!
# Latch initial construction, registration, and first-match withdrawal

Placement: translation-simulation, claim latch-registration-agrees, requirement R10.
The value equations connect the independent model to Step's shared reading theorem.
The typing and scope corollaries serve store-typing and initial-algebras-folds, requirement R4.
Withdrawal assumes an injective handle table and a value scope of the declared length.
Registration reads the identity and hint supplied by that table.
These statements cover pure transitions, including duplicate registrations.
They establish no wrapper interruption delivery, posted flush, liveness, or host execution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Effect4.Latch.Model
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Schema
open Effect4.Schema.Model Effect4.Modules

/-- Deferred keys are the two fields of each registration in the comparison interpretation. -/
abbrev WaiterKeys := DeferredKey × DeferredKey × Unit

def waiterKeys (tb : Table) (id : Nat) : WaiterKeys := (tb.hint id, (tb.handle id, ()))

/-- The independent state encoded at the deferred-key interpretation. -/
def cellKeys (tb : Table) (s : State) : CarrierAt Leaves.deferredKeys cellTy :=
  (s.isOpen, (s.pending.map (waiterKeys tb), (s.scheduled, (s.waiters.map (waiterKeys tb), ()))))

/-- Changing the leaf carrier retains the existing cell encoding. -/
theorem cellKeys_image (tb : Table) (s : State) :
    (imageAt Leaves.deferredKeys cellTy).toVal (cellKeys tb s) = cellVal tb s := by
  have batch (xs : List Nat) :
      (imageAt Leaves.deferredKeys (.list waiterTy)).toVal (xs.map (waiterKeys tb)) =
        (imageAt Leaves.opaque (.list waiterTy)).toVal (xs.map (waiterC tb)) := by
    change Val.list ((xs.map (waiterKeys tb)).map (imageAt Leaves.deferredKeys waiterTy).toVal) =
      Val.list ((xs.map (waiterC tb)).map (imageAt Leaves.opaque waiterTy).toVal)
    induction xs with
    | nil => rfl
    | cons id xs ih =>
      change Val.list ((imageAt Leaves.deferredKeys waiterTy).toVal (waiterKeys tb id) :: _) = _
      change Val.list ((imageAt Leaves.opaque waiterTy).toVal (waiterC tb id) :: _) = _
      exact congrArg (fun value => match value with
        | Val.list rest => Val.list ((imageAt Leaves.opaque waiterTy).toVal (waiterC tb id) :: rest)
        | _ => value) ih
  change Val.ctor 0 [.list [.str "open", .str "pending", .str "scheduled", .str "waiters"],
    .list [.bool s.isOpen,
      (imageAt Leaves.deferredKeys (.list waiterTy)).toVal (s.pending.map (waiterKeys tb)),
      .bool s.scheduled,
      (imageAt Leaves.deferredKeys (.list waiterTy)).toVal (s.waiters.map (waiterKeys tb))]] = _
  rw [batch, batch]
  rfl

/-- The common first-match operation removes exactly the model's first matching identity. -/
theorem removeFirst_eval {Γ : List Ty} (tb : Table) (injective : tb.Injective) (id : Nat)
    (xs : List Nat) (values : Inputs Leaves.deferredKeys Γ) (identity : Input Γ idTy)
    (held : identity.get values = tb.handle id) (source : Step Γ (.list waiterTy))
    (items : source.eval Leaves.deferredKeys values = xs.map (waiterKeys tb)) :
    (Data.removeFirst (.var identity) source).eval Leaves.deferredKeys values =
      (xs.contains id, (xs.erase id).map (waiterKeys tb)) := by
  unfold Data.removeFirst
  rw [Step.Lists.eval_removeFirst]
  change ((source.eval Leaves.deferredKeys values).any
      (fun (item : WaiterKeys) => decide (item.2.1 = identity.get values)),
    (source.eval Leaves.deferredKeys values).eraseP
      (fun (item : WaiterKeys) => decide (item.2.1 = identity.get values))) = _
  rw [items, held, List.any_map, List.eraseP_map]
  have predicate : (fun (item : WaiterKeys) => decide (item.2.1 = tb.handle id)) ∘ waiterKeys tb =
      (fun w => id == w) := by
    funext w
    change decide (tb.handle w = tb.handle id) = (id == w)
    rw [injective.decides w id, Bool.beq_eq_decide_eq]
    by_cases same : w = id
    · subst w; rfl
    · rw [decide_eq_false same, decide_eq_false (Ne.symm same)]
  rw [predicate, ← List.contains_eq_any_beq, ← List.erase_eq_eraseP]

/-- Registration inputs at the comparison interpretation. -/
abbrev awaitInputs (tb : Table) (s : State) (id : Nat) :
    Inputs Leaves.deferredKeys [idTy, idTy, cellTy] :=
  (tb.handle id, (tb.hint id, (cellKeys tb s, ())))

/-- Withdrawal inputs at the comparison interpretation. -/
abbrev withdrawInputs (tb : Table) (s : State) (id : Nat) :
    Inputs Leaves.deferredKeys [idTy, cellTy] := (tb.handle id, (cellKeys tb s, ()))

/-- Initial construction computes the independently declared initial state. -/
theorem initial_eval (tb : Table) (isOpen : Bool) :
    Data.initial.eval (Γ := [.bool]) Leaves.deferredKeys (isOpen, ()) = cellKeys tb (initial isOpen) := rfl

/-- Registration leaves an open cell alone, or appends one waiter to a closed cell. -/
theorem await_eval (tb : Table) (s : State) (id : Nat) :
    Data.awaitLatch.eval (Γ := [idTy, idTy, cellTy]) Leaves.deferredKeys (awaitInputs tb s id) =
      ((awaitLatch s id).2, cellKeys tb (awaitLatch s id).1) := by
  obtain ⟨opened, waiters, pending, scheduled⟩ := s
  cases opened
  · change (false, (false, (pending.map (waiterKeys tb),
        (scheduled, (waiters.map (waiterKeys tb) ++ [waiterKeys tb id], ()))))) =
      (false, (false, (pending.map (waiterKeys tb),
        (scheduled, ((waiters ++ [id]).map (waiterKeys tb), ())))))
    rw [List.map_append]
    rfl
  · rfl

/-- Withdrawal searches the live waiters before the attached scheduled batch. -/
theorem withdraw_eval (tb : Table) (injective : tb.Injective) (s : State) (id : Nat) :
    Data.withdraw.eval (Γ := [idTy, cellTy]) Leaves.deferredKeys (withdrawInputs tb s id) =
      ((), cellKeys tb (withdraw s id).1) := by
  let live := Data.removeFirst (Step.var (.here idTy [cellTy]))
    (.get (.var (.there _ (.here _ _))) Data.waitersF)
  let batch := Data.removeFirst (Step.var (.here idTy [cellTy]))
    (.get (.var (.there _ (.here _ _))) Data.pendingF)
  have waiters : live.eval Leaves.deferredKeys (withdrawInputs tb s id) =
      (s.waiters.contains id, (s.waiters.erase id).map (waiterKeys tb)) :=
    removeFirst_eval tb injective id s.waiters
      (withdrawInputs tb s id) (.here _ _) rfl _ rfl
  have pending : batch.eval Leaves.deferredKeys (withdrawInputs tb s id) =
      (s.pending.contains id, (s.pending.erase id).map (waiterKeys tb)) :=
    removeFirst_eval tb injective id s.pending
      (withdrawInputs tb s id) (.here _ _) rfl _ rfl
  dsimp only [Data.withdraw]
  rw [Step.eval_ite, Step.eval_ite]
  change (bif (live.eval Leaves.deferredKeys (withdrawInputs tb s id)).1 then
    ((), (s.isOpen, (s.pending.map (waiterKeys tb),
      (s.scheduled, ((live.eval Leaves.deferredKeys (withdrawInputs tb s id)).2, ())))))
    else bif s.scheduled then
      ((), (s.isOpen, ((batch.eval Leaves.deferredKeys (withdrawInputs tb s id)).2,
        (s.scheduled, (s.waiters.map (waiterKeys tb), ())))))
    else ((), cellKeys tb s)) = _
  rw [waiters, pending]
  unfold withdraw
  cases hw : s.waiters.contains id <;> cases hs : s.scheduled <;> rfl

/-- Initial construction reads the independent initial state at every caller scope. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem initialStep_agrees (tb : Table) (isOpen : Bool) {flag : TermSrc} {env : Env}
    {path : List Nat} {vals : List Val} (readsFlag : Reads flag env path vals (.bool isOpen)) :
    Reads (Latch.initialStep flag) env path vals (cellVal tb (initial isOpen)) := by
  have reads := Step.sound (Γ := [.bool]) Leaves.deferredKeys (isOpen, ())
    (Input.reads_cons readsFlag Input.reads_nil) Data.initial rfl
  rw [initial_eval tb, cellKeys_image] at reads
  exact reads

/-- Await registration reads the immediate-answer flag and the independently specified cell. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem awaitStep_agrees (tb : Table) (s : State) (id : Nat) {idSrc hintSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val}
    (readsId : Reads idSrc env path vals (.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (.promise (tb.hint id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb s)) :
    Reads (Latch.awaitStep idSrc hintSrc cellSrc) env path vals
      (Val.tuple [.bool (awaitLatch s id).2, cellVal tb (awaitLatch s id).1]) := by
  have cell : Reads cellSrc env path vals ((imageAt Leaves.deferredKeys cellTy).toVal (cellKeys tb s)) :=
    (cellKeys_image tb s).symm ▸ readsCell
  have reads := Step.sound Leaves.deferredKeys (awaitInputs tb s id)
    (Input.reads_cons readsId (Input.reads_cons readsHint (Input.reads_cons cell Input.reads_nil)))
    Data.awaitLatch rfl
  rw [await_eval] at reads
  change Reads _ _ _ _ (Val.tuple [.bool (awaitLatch s id).2,
    (imageAt Leaves.deferredKeys cellTy).toVal (cellKeys tb (awaitLatch s id).1)]) at reads
  rw [cellKeys_image] at reads
  exact reads

/-- Withdrawal erases one registration, preserving waiter priority and the scheduled flag. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdrawStep_agrees (tb : Table) (injective : tb.Injective) (s : State) (id : Nat)
    {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsId : Reads idSrc env path vals (.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb s)) (scope : vals.length = env.names.length) :
    Reads (Latch.withdrawStep idSrc cellSrc) env path vals
      (Val.tuple [.unit, cellVal tb (withdraw s id).1]) := by
  have cell : Reads cellSrc env path vals ((imageAt Leaves.deferredKeys cellTy).toVal (cellKeys tb s)) :=
    (cellKeys_image tb s).symm ▸ readsCell
  have reads := Step.sound Leaves.deferredKeys (withdrawInputs tb s id)
    (Input.reads_cons readsId (Input.reads_cons cell Input.reads_nil)) Data.withdraw rfl
    (Step.scope_of_alignment Data.withdraw scope) ⟨DeferredIdentity.deferredKeys⟩
  rw [withdraw_eval tb injective] at reads
  change Reads _ _ _ _ (Val.tuple [.unit,
    (imageAt Leaves.deferredKeys cellTy).toVal (cellKeys tb (withdraw s id).1)]) at reads
  rw [cellKeys_image] at reads
  exact reads

/-- The three pure registration transitions agree with the independent model. -/
structure RegistrationAgree : Prop where
  initial : ∀ (tb : Table) (isOpen : Bool) {flag : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val}, Reads flag env path vals (.bool isOpen) →
      Reads (Latch.initialStep flag) env path vals (cellVal tb (Model.initial isOpen))
  await : ∀ (tb : Table) (s : State) (id : Nat) {idSrc hintSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val},
    Reads idSrc env path vals (.promise (tb.handle id)) →
    Reads hintSrc env path vals (.promise (tb.hint id)) →
    Reads cellSrc env path vals (cellVal tb s) →
      Reads (Latch.awaitStep idSrc hintSrc cellSrc) env path vals
        (Val.tuple [.bool (awaitLatch s id).2, cellVal tb (awaitLatch s id).1])
  withdraw : ∀ (tb : Table), tb.Injective → ∀ (s : State) (id : Nat) {idSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val},
    Reads idSrc env path vals (.promise (tb.handle id)) →
    Reads cellSrc env path vals (cellVal tb s) → vals.length = env.names.length →
      Reads (Latch.withdrawStep idSrc cellSrc) env path vals
        (Val.tuple [.unit, cellVal tb (Model.withdraw s id).1])

/-- Claim latch-registration-agrees: initial construction, registration, and first-match cleanup. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem latch_registration_agrees : RegistrationAgree where
  initial := initialStep_agrees
  await := awaitStep_agrees
  withdraw := withdrawStep_agrees

section Typed
variable {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
  {env : Env} {path : List Nat} {types : List Ty}
include atoms

/-- The checked construction rule supplies the initial cell type. -/
@[semantics "store-typing" (requirement := R4)]
theorem initialStep_types {flag : TermSrc} (h : TypesEach sig flag env path types .bool) :
    TypesEach sig (Latch.initialStep flag) env path types cellTy :=
  Step.typed_of_normal sig atoms (Input.types_cons h Input.types_nil) Data.initial rfl

/-- Registration inherits the shared record construction and update typing. -/
@[semantics "store-typing" (requirement := R4)]
theorem awaitStep_types {idSrc hintSrc cellSrc : TermSrc}
    (id : TypesEach sig idSrc env path types idTy) (hint : TypesEach sig hintSrc env path types idTy)
    (cell : TypesEach sig cellSrc env path types cellTy) :
    TypesEach sig (Latch.awaitStep idSrc hintSrc cellSrc) env path types (.prod .bool cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons id (Input.types_cons hint
    (Input.types_cons cell Input.types_nil))) Data.awaitLatch rfl

/-- Withdrawal inherits fold typing at a scope aligned with the caller's type list. -/
@[semantics "store-typing" (requirement := R4)]
theorem withdrawStep_types {idSrc cellSrc : TermSrc}
    (id : TypesEach sig idSrc env path types idTy) (cell : TypesEach sig cellSrc env path types cellTy)
    (scope : types.length = env.names.length) :
    TypesEach sig (Latch.withdrawStep idSrc cellSrc) env path types (.prod .unit cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons id (Input.types_cons cell Input.types_nil))
    Data.withdraw rfl (Step.scope_of_alignment Data.withdraw scope)
end Typed

/-- Initial construction keeps the caller's term scope. -/
theorem initialStep_scoped {flag : TermSrc} (h : flag.Scoped) : (Latch.initialStep flag).Scoped :=
  Step.«scoped» Data.initial (Input.source_scoped (TermSrc.Scoped_cons h TermSrc.Scoped_nil))

/-- Registration keeps each caller input at its declared scope. -/
theorem awaitStep_scoped {id hint cell : TermSrc} (hi : id.Scoped) (hh : hint.Scoped) (hc : cell.Scoped) :
    (Latch.awaitStep id hint cell).Scoped :=
  Step.«scoped» Data.awaitLatch (Input.source_scoped
    (TermSrc.Scoped_cons hi (TermSrc.Scoped_cons hh (TermSrc.Scoped_cons hc TermSrc.Scoped_nil))))

/-- Withdrawal derives the scope of its captured inputs through the shared fold rule. -/
theorem withdrawStep_scoped {id cell : TermSrc} (hi : id.Scoped) (hc : cell.Scoped) :
    (Latch.withdrawStep id cell).Scoped :=
  Step.«scoped» Data.withdraw (Input.source_scoped
    (TermSrc.Scoped_cons hi (TermSrc.Scoped_cons hc TermSrc.Scoped_nil)))

end Effect4.Latch.Model
