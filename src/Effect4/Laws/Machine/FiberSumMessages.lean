import Effect4.Laws.Machine.FiberSum
import Effect4.Laws.Machine.EditWords

/-!
Concept: reactive-scheduling and scope-lifetime-finalization, R11.
Question: deferred messages retain the accounting bound at settlement.
Consumers: WriterWeights.settle_bound and ReleaseCustody.settle_funded.
Reach: unique stored identities, observer-neutral weights, and nonincreasing interruption weights.
The actual edit path supplies current lookup premises. No evaluator debit or progress follows.
-/
set_option autoImplicit false
namespace Effect4.Machine.FiberSum
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (w : RunFiber ν σ β ε δ ι α χ → Nat)

/-- A message keeps identities and cannot raise a weight satisfying its two local laws. -/
theorem fiberEdit_le
    (observers : ∀ f entries, w {f with observers := entries} = w f)
    (interrupts : ∀ cause f, w (interruptWithCause cause f).1 ≤ w f)
    (edit : FiberEdit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) :
    (applyFiberEdit edit m).1.fibers.map RunFiber.id = m.fibers.map RunFiber.id ∧
      total w (applyFiberEdit edit m).1 ≤ total w m := by
  cases edit with
  | observe target observer =>
    simp only [applyFiberEdit, RunMachine.modify]
    split
    · exact ⟨rfl, Nat.le_refl _⟩
    · next old found =>
      refine ⟨RunMachine.update_keeps_ids _ _, ?_⟩
      exact update_debit w m old {old with observers := old.observers ++ [observer]}
        rfl unique (RunMachine.mem_of_fiber? found) 0
        (by rw [observers, Nat.add_zero]; exact Nat.le_refl _)
  | dropToken token =>
    refine ⟨?_, ?_⟩
    · simp only [applyFiberEdit, List.map_map, Function.comp_def]
    · exact Nat.le_of_eq (total_map w m _ (fun f => observers f _))
  | interrupt target cause =>
    simp only [applyFiberEdit]
    split
    · exact ⟨rfl, Nat.le_refl _⟩
    · next old found =>
      exact ⟨RunMachine.update_keeps_ids _ _,
        update_debit w m old (interruptWithCause cause old).1
          (interruptWithCause_maskLater cause old).1 unique (RunMachine.mem_of_fiber? found) 0
          (by simpa only [Nat.add_zero] using interrupts cause old)⟩

/-- The shared actual-prefix word lifts the local weight laws over all deferred messages. -/
theorem fiberEdits_le
    (observers : ∀ f entries, w {f with observers := entries} = w f)
    (interrupts : ∀ cause f, w (interruptWithCause cause f).1 ≤ w f)
    (edits : List (FiberEdit ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) :
    (applyFiberEdits edits m).1.fibers.map RunFiber.id = m.fibers.map RunFiber.id ∧
      total w (applyFiberEdits edits m).1 ≤ total w m := by
  let Edge (before after : RunMachine ν σ β ε δ ι α χ St)
      (edit : Edit ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α)
        (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α)) : Prop :=
    after = edit.apply before ∧
      ((before.fibers.map RunFiber.id).Nodup →
        after.fibers.map RunFiber.id = before.fibers.map RunFiber.id ∧ total w after ≤ total w before)
  have localPath (message : FiberEdit ε δ ι α) (held : RunMachine ν σ β ε δ ι α χ St) :
      Effect4.Contracts.Path Edge held (applyFiberEdit message held).1 (Edits.fiberWord message held) := by
    have kept := fiberEdit_le w observers interrupts message held
    cases message with
    | observe target observer => exact .cons ⟨rfl, kept⟩ (.nil _)
    | dropToken token => exact .cons ⟨rfl, kept⟩ (.nil _)
    | interrupt target cause =>
      cases found : held.fiber? target with
      | none => simp only [Edits.fiberWord, applyFiberEdit, found]; exact .nil _
      | some old =>
        simp only [Edits.fiberWord, applyFiberEdit, found] at kept ⊢
        exact .cons ⟨rfl, kept⟩ (.nil _)
  have path := Edits.fiberWords_path edits (fun message _ held => localPath message held) m
  rw [Edits.fiber_words]
  apply Edits.run_preserves_at (Edge := Edge) (fun _ _ _ edge => edge.1)
    (fun held => held.fibers.map RunFiber.id = m.fibers.map RunFiber.id ∧ total w held ≤ total w m)
    (fun before after edit edge initial => ?_) path ⟨rfl, Nat.le_refl _⟩
  have step := edge.2 (by rw [initial.1]; exact unique)
  exact ⟨step.1.trans initial.1, Nat.le_trans step.2 initial.2⟩

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Two replacements of the same identity and weight give the same table total. -/
theorem total_update_congr (m : RunMachine ν σ β ε δ ι α χ St)
    (first last : RunFiber ν σ β ε δ ι α χ) (key : first.id = last.id)
    (weight : w first = w last) : total w (m.update first) = total w (m.update last) := by
  simp only [total, RunMachine.update, List.map_map, Function.comp_def, key]
  congr 1
  apply List.map_congr_left
  intro fiber _
  split
  · exact weight
  · rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The disposition changes no fiber weight beyond installing the returned owner. -/
theorem settleOutcome_total
    (stopped : ∀ f, w {f with running := false} = w f)
    (unparked : ∀ f, w {f with parked := .notParked, pending := []} = w f)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) (it : Iter ν σ β ε δ ι α χ St) :
    total w (settleOutcome id rest it).1 = total w (it.machine.update it.fiber) := by
  cases outcome : it.outcome <;> simp only [settleOutcome, outcome]
  case parked =>
    split
    · exact total_update_congr w _ _ _ rfl (unparked _)
    · exact total_update_congr w _ _ _ rfl (stopped _)
  case stuck => exact total_update_congr w _ _ _ rfl (stopped _)

/-- Settlement cannot raise the installed table weight when its messages cannot raise it. -/
theorem settle_le
    (observers : ∀ f entries, w {f with observers := entries} = w f)
    (interrupts : ∀ cause f, w (interruptWithCause cause f).1 ≤ w f)
    (stopped : ∀ f, w {f with running := false} = w f)
    (unparked : ∀ f, w {f with parked := .notParked, pending := []} = w f)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) (it : Iter ν σ β ε δ ι α χ St)
    (unique : (it.machine.fibers.map RunFiber.id).Nodup) :
    total w (settle id rest it).1 ≤ total w (it.machine.update it.fiber) := by
  unfold settle
  split
  · exact Nat.le_of_eq (settleOutcome_total w stopped unparked id rest it)
  · have installedUnique : ((it.machine.update it.fiber).fibers.map RunFiber.id).Nodup := by
      have keys : (it.machine.update it.fiber).fibers.map RunFiber.id =
          it.machine.fibers.map RunFiber.id := RunMachine.update_keeps_ids it.fiber it.machine
      rw [keys]
      exact unique
    have changed := fiberEdits_le w observers interrupts it.edits
      (it.machine.update it.fiber) installedUnique
    dsimp only
    split
    · exact changed.2
    · next owner found =>
      rw [settleOutcome_total w stopped unparked]
      have heldUnique : ((applyFiberEdits it.edits (it.machine.update it.fiber)).1.fibers.map
          RunFiber.id).Nodup := by rw [changed.1]; exact installedUnique
      have stored := update_debit w _ owner owner rfl heldUnique (RunMachine.mem_of_fiber? found)
        0 (Nat.le_refl _)
      exact Nat.le_trans stored changed.2

omit w in
/-- Settlement changes neither the store, the races, nor the trace.
Consumers: the shared writer and release ledgers retain their nonfiber terms. -/
theorem settle_fields (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α))
    (it : Iter ν σ β ε δ ι α χ St) :
    ((settle id rest it).1.state, (settle id rest it).1.races, (settle id rest it).1.trace) =
      (it.machine.state, it.machine.races, it.machine.trace) := by
  apply Edits.settle_keeps (fun held : RunMachine ν σ β ε δ ι α χ St =>
      (held.state, held.races, held.trace))
    (fun _ _ => rfl) (fun _ _ => rfl) _ (fun _ _ => rfl)
  intro target observer held
  simp only [Edit.apply, RunMachine.modify]
  split <;> rfl

omit w in
/-- Settlement adds only scheduler commands of zero weight and may discard pending commands.
Consumer: release custody retains its queued-work term beside the shared table bound. -/
theorem settle_commands_le (weight : Cmd ν σ β ε δ ι α → Nat)
    (evaluateZero : ∀ id, weight (.evaluate id) = 0)
    (loopZero : ∀ id yielding, weight (.loop id yielding) = 0)
    (deliverZero : ∀ id yielding, weight (.deliver id yielding) = 0)
    (finishZero : ∀ id exit, weight (.finish id exit) = 0)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) (it : Iter ν σ β ε δ ι α χ St) :
    ((settle id rest it).2.map weight).sum ≤ ((it.nested ++ rest).map weight).sum := by
  have padding (nested : List (Cmd ν σ β ε δ ι α)) (command : Cmd ν σ β ε δ ι α)
      (zero : weight command = 0) :
      ((nested ++ [command] ++ rest).map weight).sum = ((nested ++ rest).map weight).sum := by
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, zero, Nat.add_zero]
  have disposition (next : Iter ν σ β ε δ ι α χ St) :
      ((settleOutcome id rest next).2.map weight).sum ≤ ((next.nested ++ rest).map weight).sum := by
    cases outcome : next.outcome <;> simp only [settleOutcome, outcome]
    case continue_ => exact Nat.le_of_eq (padding next.nested _ (loopZero id next.yielding))
    case answered => exact Nat.le_of_eq (padding next.nested _ (deliverZero id next.yielding))
    case finished exit => exact Nat.le_of_eq (padding next.nested _ (finishZero id exit))
    case commands => exact Nat.le_refl _
    case stuck why => exact Nat.zero_le _
    case parked =>
      split
      · exact Nat.le_of_eq (padding next.nested _ (loopZero id next.yielding))
      · exact Nat.le_refl _
  unfold settle
  split
  · exact disposition it
  · have commands := (RunMachine.applyFiberEdits_shape it.edits (it.machine.update it.fiber)).2
    have zero : ((applyFiberEdits it.edits (it.machine.update it.fiber)).2.map weight).sum = 0 := by
      have zeroes : (applyFiberEdits it.edits (it.machine.update it.fiber)).2.map weight =
          List.replicate (applyFiberEdits it.edits (it.machine.update it.fiber)).2.length 0 := by
        apply List.map_eq_replicate_iff.mpr
        intro command member
        obtain ⟨target, rfl⟩ := commands command member
        exact evaluateZero target
      rw [zeroes, List.sum_replicate_nat, Nat.mul_zero]
    dsimp only
    split
    · exact Nat.zero_le _
    · next owner found =>
      have bounded := disposition {it with
        machine := (applyFiberEdits it.edits (it.machine.update it.fiber)).1
        fiber := owner
        nested := (applyFiberEdits it.edits (it.machine.update it.fiber)).2 ++ it.nested
        edits := []}
      simpa only [List.map_append, List.sum_append, zero, Nat.zero_add] using bounded

end Effect4.Machine.FiberSum
