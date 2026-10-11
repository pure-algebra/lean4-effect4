import Effect4.Laws.Library.Queue.Steps

/-!
# Queue model job conservation

Concept: translation-simulation R10, the model half of proposed `queue-expansion-agrees`.
Consumer: the QueueWorkers conservation assertion's `jobs_step` obligation.
Reach: first-profile model states, single-message offers, bounds one and one, poll and withdrawals.
These laws account for buffered and pending jobs, including the jobs removed by an offer withdrawal.
They establish no machine-to-model connection, wrapper delivery, progress or outside-host behavior.
Decisions rows 233, 255 and 275 bound this fragment.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

/-- Buffered jobs followed by the jobs of pending offers. -/
def stateJobs (s : State) : List Nat := s.messages ++ s.offers.flatMap (·.rest)

/-- The accept pass keeps the jobs: the offers that fit move from pending to buffered. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem stateJobs_afterAccept (c : Nat) (s : State) : stateJobs (afterAccept c s) = stateJobs s := by
  show s.messages ++ (s.offers.take (fitCount c s)).flatMap (·.rest) ++
      (s.offers.drop (fitCount c s)).flatMap (·.rest) = s.messages ++ s.offers.flatMap (·.rest)
  rw [List.append_assoc, ← List.flatMap_append, List.take_append_drop]

/-- **A take at the bounds one and one consumes its job, or it waits and keeps every job.** -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_jobs {s : State} (h : FirstProfile s) (id : Nat) :
    (∃ m, (take s ⟨id, 1, 1⟩).2.1 = .got [m] ∧
        stateJobs s = m :: stateJobs (take s ⟨id, 1, 1⟩).1) ∨
      ((take s ⟨id, 1, 1⟩).2.1 = .wait ∧ stateJobs (take s ⟨id, 1, 1⟩).1 = stateJobs s) := by
  obtain ⟨c, capacity⟩ := h.positive
  cases hc : (ready s 1 && (earlier s id).isEmpty) with
  | true =>
    rw [Bool.and_eq_true] at hc
    obtain ⟨ready1, turn⟩ := hc
    rw [ready_profile h] at ready1
    cases buffered : s.messages with
    | nil =>
      rw [buffered] at ready1
      exact Bool.noConfusion ready1
    | cons m ms =>
      rw [take_consumes h capacity id buffered turn]
      refine .inl ⟨m, rfl, ?_⟩
      rw [stateJobs_afterAccept]
      show s.messages ++ s.offers.flatMap (·.rest) = m :: (ms ++ s.offers.flatMap (·.rest))
      rw [buffered]
      rfl
  | false =>
    refine .inr ?_
    rw [take_eq h id, hc, if_neg Bool.false_ne_true]
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

/-- **An offer of one job adds that job**, accepted or pending. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem offer_jobs {s : State} (h : FirstProfile s) (id a : Nat) :
    stateJobs (offer s id a).1 = stateJobs s ++ [a] := by
  obtain ⟨c, capacity⟩ := h.positive
  cases ho : s.offers with
  | cons o os =>
    rw [offer_behind h id a (by rw [ho]; exact List.cons_ne_nil o os)]
    show s.messages ++ (s.offers ++ [(⟨id, false, [a]⟩ : Offer)]).flatMap (·.rest) =
      s.messages ++ s.offers.flatMap (·.rest) ++ [a]
    rw [List.flatMap_append, List.append_assoc]
    rfl
  | nil =>
    cases hfree : decide (s.messages.length < c + 1) with
    | true =>
      rw [offer_room h capacity id a ho (of_decide_eq_true hfree)]
      show s.messages ++ [a] ++ s.offers.flatMap (·.rest) =
        s.messages ++ s.offers.flatMap (·.rest) ++ [a]
      rw [ho, List.flatMap_nil, List.append_nil, List.append_nil]
    | false =>
      rw [offer_full h capacity id a ho (of_decide_eq_false hfree)]
      show s.messages ++ (s.offers ++ [(⟨id, false, [a]⟩ : Offer)]).flatMap (·.rest) =
        s.messages ++ s.offers.flatMap (·.rest) ++ [a]
      rw [ho, List.nil_append, List.flatMap_nil, List.append_nil]
      rfl

/-- **A poll consumes one job, or it changes nothing.** -/
@[semantics "translation-simulation" (requirement := R10)]
theorem poll_jobs {s : State} (h : FirstProfile s) :
    ((poll s).2.1 = none ∧ stateJobs (poll s).1 = stateJobs s) ∨
      ∃ m, (poll s).2.1 = some m ∧ stateJobs s = m :: stateJobs (poll s).1 := by
  obtain ⟨c, capacity⟩ := h.positive
  cases hm : s.messages with
  | nil =>
    rw [poll_idle h (.inl hm)]
    exact .inl ⟨rfl, rfl⟩
  | cons m ms =>
    cases ht : s.takers with
    | cons t ts =>
      rw [poll_idle h (.inr (by rw [ht]; exact List.cons_ne_nil t ts))]
      exact .inl ⟨rfl, rfl⟩
    | nil =>
      rw [poll_consumes h capacity hm ht]
      refine .inr ⟨m, rfl, ?_⟩
      rw [stateJobs_afterAccept]
      show s.messages ++ s.offers.flatMap (·.rest) = m :: (ms ++ s.offers.flatMap (·.rest))
      rw [hm]
      rfl

/-- **A take's withdrawal keeps every job.** -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdrawTake_jobs (s : State) (id : Nat) :
    stateJobs (withdrawTake s id).1 = stateJobs s := rfl

/-- The jobs of a list of offers, split by a test. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem flatMap_split (p : Offer → Bool) : ∀ (l : List Offer),
    (l.flatMap (·.rest)).Perm
      ((l.filter p).flatMap (·.rest) ++ (l.filter (fun o => !p o)).flatMap (·.rest))
  | [] => List.Perm.refl _
  | o :: os => by
    have rest := flatMap_split p os
    cases hp : p o with
    | true =>
      have first : (o :: os).filter p = o :: os.filter p := List.filter_cons_of_pos hp
      have second : (o :: os).filter (fun o => !p o) = os.filter (fun o => !p o) :=
        List.filter_cons_of_neg (by
          show ¬ ((!p o) = true)
          rw [hp]
          exact Bool.false_ne_true)
      rw [first, second, List.flatMap_cons, List.flatMap_cons, List.append_assoc]
      exact rest.append_left o.rest
    | false =>
      have first : (o :: os).filter p = os.filter p :=
        List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)
      have second : (o :: os).filter (fun o => !p o) = o :: os.filter (fun o => !p o) :=
        List.filter_cons_of_pos (by
          show (!p o) = true
          rw [hp]
          rfl)
      rw [first, second, List.flatMap_cons, List.flatMap_cons]
      refine (rest.append_left o.rest).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

/-- **An offer's withdrawal removes the jobs of the withdrawn offer, and no other.** In the
crew the withdrawn offer is the feeder's, with one job, or nothing where a step accepted it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdrawOffer_jobs {s : State} (h : FirstProfile s) (id : Nat) :
    (stateJobs s).Perm (stateJobs (withdrawOffer s id).1 ++
      (s.offers.filter (fun o => !(o.id != id))).flatMap (·.rest)) := by
  rw [withdrawOffer_opened h.opened id]
  show (s.messages ++ s.offers.flatMap (·.rest)).Perm
    (s.messages ++ (s.offers.filter (fun o => o.id != id)).flatMap (·.rest) ++
      (s.offers.filter (fun o => !(o.id != id))).flatMap (·.rest))
  rw [List.append_assoc]
  exact (flatMap_split (fun o => o.id != id) s.offers).append_left s.messages


end Effect4.Queue.Model
