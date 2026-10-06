import Effect4.Laws.Modules.Queue.Profile
import Effect4.Laws.Modules.Queue.Capacity
import Effect4.Laws.Auto.Semantics

/-!
# The Queue model's run invariant on the first profile (decisions rows 219, 233, 255 and 275)

`first_step_inv`: one step of the model (`src/Effect4/Laws/Modules/Queue/Model.lean`) by a first
operation keeps `FirstRunInv`, from every run that holds it. `FirstRunInv` is the first profile
with the three properties of the state and the run's two flags. `first_run_inv` is the same for a
list of operations. `first_run_flags` starts it at the empty queue: both flags hold after every
such list. No term, no cell and no machine occurs in this file.

Placement. Concept `reactive-scheduling`: preservation of an explicit state invariant.
Requirement R12, as the model's half of the proposed claims `wait-registration-no-gap` and
`waiting-request-obligation-preserved`. Consumer: the run-level law of the Queue's wrapper
(decisions row 275, point 2). Reach: the model's `step` at `Fault.none`, for each first operation
(`firstOp`) whose request keeps `Requested`, from every run of the invariant. The statements
establish nothing about a program or the machine, no delivery of a signal, no liveness and no
fairness. `signalled` records that a step named a request, not that the request ran again.

The invariant is Codex's, from its review of the brief:
`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-1336-qinv-pool-maskpop/next/review.md`.
A flag is a run's history, and `FirstProfile` leaves the buffer free. So no part of the invariant
gives another, and the five witnesses of that review are the battery's red controls.

The proof has three layers. `step_state` carries `first_profile_closed` and
`positive_suspend_step_capacity` to a run with any history. `Flags` is what the two flags ask of
one step beside the bound, and each operation of the model has one lemma that states it.
`bump_inv` joins such a step to a run. The design is
`docs/research/2026-10-06-seat-QINV-design.md`. The pinned axiom and plan outputs and the finite
controls are in `Test/Program/QueueInvariant.lean`.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

/-! ## The invariant -/

/-- **The run invariant of the first profile.** The state is of the profile. It has the three
properties that the flag `ok` reads: `within`, `tidy`, and `quiet` at the run's own `signalled`.
Both flags of the run hold. -/
structure FirstRunInv (r : Run) : Prop where
  profile : FirstProfile r.s
  within : within r.s = true
  tidy : tidy r.s = true
  quiet : quiet r.s r.signalled = true
  ok : r.ok = true
  named : r.named = true

/-- The invariant decides, as the conjunction of its six parts. -/
instance (r : Run) : Decidable (FirstRunInv r) :=
  decidable_of_iff
    (FirstProfile r.s ∧ within r.s = true ∧ tidy r.s = true ∧ quiet r.s r.signalled = true ∧
      r.ok = true ∧ r.named = true)
    ⟨fun ⟨profile, within, tidy, quiet, ok, named⟩ => ⟨profile, within, tidy, quiet, ok, named⟩,
      fun h => ⟨h.profile, h.within, h.tidy, h.quiet, h.ok, h.named⟩⟩

/-! ## The run's projection

Steps of `first_step_inv`: they carry the profile's closure and the capacity statement from a
run with a default history to any run. -/

/-- A step's next state reads the run's state alone: a history changes no state. -/
theorem step_state (fault : Fault) (r : Run) (op : Op) :
    (step fault r op).s = (step fault { s := r.s } op).s := by
  cases op with
  | offer id a =>
    simp only [step]
    split <;> rfl
  | offerAll id ms =>
    simp only [step]
    split <;> rfl
  | _ => rfl

/-- One step keeps the buffer inside its capacity (`positive_suspend_step_capacity`). -/
theorem step_within {r : Run} (h : FirstProfile r.s) (bound : within r.s = true) (op : Op) :
    within (step .none r op).s = true := by
  obtain ⟨c, capacity⟩ := h.positive
  have inside : r.s.messages.length ≤ c + 1 := by
    unfold within at bound
    rw [capacity] at bound
    exact of_decide_eq_true bound
  have next :=
    positive_suspend_step_capacity (c + 1) r.s op (Nat.succ_pos c) capacity h.suspend inside
  rw [step_state]
  unfold within
  rw [next.1]
  exact decide_eq_true next.2.2

/-! ## `quiet` is the wake, read back

Steps of `bump_inv`. Neither asks a premise of the state. -/

/-- Each signal of a wake asks its request to run again. -/
theorem wake_again (s : State) : ∀ g ∈ wake s, g.note = .again := by
  intro g named
  unfold wake at named
  rcases List.mem_append.mp named with taker | peeker
  · split at taker
    · split at taker
      · rw [List.mem_singleton.mp taker]
      · exact absurd taker List.not_mem_nil
    · exact absurd taker List.not_mem_nil
  · split at peeker
    · obtain ⟨id, _, rfl⟩ := List.mem_map.mp peeker
      rfl
    · exact absurd peeker List.not_mem_nil

/-- **A state is quiet exactly when each request that its wake names is signalled.** -/
theorem quiet_iff_wake (s : State) (signalled : List Nat) :
    quiet s signalled = true ↔ ∀ g ∈ wake s, g.id ∈ signalled := by
  unfold quiet wake
  rw [Bool.and_eq_true, List.forall_mem_append]
  refine and_congr ?_ ?_
  · cases s.takers with
    | nil => exact ⟨fun _ _ member => absurd member List.not_mem_nil, fun _ => rfl⟩
    | cons t ts =>
      dsimp only
      cases ready s t.min with
      | false => exact ⟨fun _ _ member => absurd member List.not_mem_nil, fun _ => rfl⟩
      | true =>
        show (false || signalled.contains t.id) = true ↔
          ∀ g ∈ [(⟨t.id, .again⟩ : Signal)], g.id ∈ signalled
        rw [Bool.false_or, List.contains_iff_mem, List.forall_mem_singleton]
  · cases front s with
    | none => exact ⟨fun _ _ member => absurd member List.not_mem_nil, fun _ => rfl⟩
    | some m =>
      show (false || s.peekers.all signalled.contains) = true ↔
        ∀ g ∈ s.peekers.map (fun id => (⟨id, .again⟩ : Signal)), g.id ∈ signalled
      rw [Bool.false_or, List.all_eq_true, List.forall_mem_map]
      exact forall_congr' fun id => imp_congr_right fun _ => List.contains_iff_mem

/-! ## What the two flags ask of one step -/

/-- No offer is pending, or no room is left: no pending offer can enter. It is what `tidy` says
of an opened queue. -/
abbrev Spent (s : State) : Prop := s.offers = [] ∨ room s = some 0

/-- **What the two flags ask of one step, beside the buffer's bound.** `own` is the step's own
request, as `bump` reads it.

* `spent`: no pending offer can enter the next state, so it is tidy.
* `woken`: a signal of the step names each request of the next wake. Otherwise the old wake
  named the request, and it is not the step's own.
* `accounted`: each request that waited still waits, is the step's own, or is named by a
  signal. -/
structure Flags (before : State) (own : Option Nat) (after : State) (signals : List Signal) :
    Prop where
  spent : Spent after
  woken : ∀ g ∈ wake after, g ∈ signals ∨ (g ∈ wake before ∧ own ≠ some g.id)
  accounted : accounted before after own signals = true

/-- `tidy` of an opened queue, as a proposition. -/
theorem tidy_iff {s : State} (opened : s.phase = .opened) : tidy s = true ↔ Spent s := by
  unfold tidy
  rw [opened]
  show (true && (s.offers.isEmpty || room s == some 0)) = true ↔ _
  rw [Bool.true_and, Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq]

/-- **A step that keeps the profile, the bound and `Flags` joins a run of the invariant.** A
step of `first_step_inv`, its one consumer. The run that `bump` builds is quiet. The step names a
request of the next wake again, or the request stays signalled: it is not the step's own. -/
theorem bump_inv {r : Run} (h : FirstRunInv r) {s : State} {own : Option Nat}
    {signals : List Signal} (profile : FirstProfile s) (bound : within s = true)
    (flags : Flags r.s own s signals) : FirstRunInv (bump r s own signals) := by
  have tidy' : tidy s = true := (tidy_iff profile.opened).mpr flags.spent
  have quiet' : quiet s (bump r s own signals).signalled = true := by
    refine (quiet_iff_wake s _).mpr fun g woken => ?_
    rcases flags.woken g woken with posted | ⟨before, other⟩
    · exact List.mem_append_right _ (List.mem_map.mpr
        ⟨g, List.mem_filter.mpr ⟨posted, beq_iff_eq.mpr (wake_again s g woken)⟩, rfl⟩)
    · have was : g.id ∈ r.signalled := (quiet_iff_wake r.s r.signalled).mp h.quiet g before
      refine List.mem_append_left _ ?_
      cases own with
      | none => exact was
      | some id =>
        exact List.mem_filter.mpr ⟨was, bne_iff_ne.mpr fun same => other (by rw [same])⟩
  exact
    { profile := profile
      within := bound
      tidy := tidy'
      quiet := quiet'
      ok := by
        show (r.ok && within s && tidy s && quiet s (bump r s own signals).signalled) = true
        rw [h.ok, bound, tidy', quiet']
        rfl
      named := by
        show (r.named && accounted r.s s own signals) = true
        rw [h.named, flags.accounted]
        rfl }

/-! ## `accounted`

Steps of the five `Flags` lemmas of the operations. The first three ask no premise of a state:
requests are accounted along a chain of states, and the signals append. -/

/-- `accounted`, as a proposition. -/
theorem accounted_iff {before after : State} {own : Option Nat} {signals : List Signal} :
    accounted before after own signals = true ↔
      ∀ id ∈ waiting before, id ∈ waiting after ∨ own = some id ∨ ∃ g ∈ signals, g.id = id := by
  unfold accounted
  rw [List.all_eq_true]
  refine forall_congr' fun id => imp_congr_right fun _ => ?_
  rw [Bool.or_eq_true, Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq, List.any_eq_true,
    or_assoc]
  exact or_congr_right (or_congr_right (exists_congr fun g => and_congr_right fun _ => beq_iff_eq))

/-- A state accounts for its own requests, whatever the signals. -/
theorem accounted_refl (s : State) (own : Option Nat) (signals : List Signal) :
    accounted s s own signals = true :=
  accounted_iff.mpr fun _ waits => .inl waits

/-- Two steps account for what each accounts for, and their signals append. -/
theorem accounted_trans {a b c : State} {own : Option Nat} {first second : List Signal}
    (ab : accounted a b own first = true) (bc : accounted b c own second = true) :
    accounted a c own (first ++ second) = true := by
  refine accounted_iff.mpr fun id waits => ?_
  rcases accounted_iff.mp ab id waits with stays | mine | ⟨g, posted, same⟩
  · rcases accounted_iff.mp bc id stays with stays | mine | ⟨g, posted, same⟩
    · exact .inl stays
    · exact .inr (.inl mine)
    · exact .inr (.inr ⟨g, List.mem_append_right _ posted, same⟩)
  · exact .inr (.inl mine)
  · exact .inr (.inr ⟨g, List.mem_append_left _ posted, same⟩)

/-- From a profile state only takers and offers wait: requests are accounted list by list. Each
taker and each offer stays, is the step's own, or is named by a signal. -/
theorem accounted_of {before after : State} (h : FirstProfile before) {own : Option Nat}
    {signals : List Signal}
    (takers : ∀ t ∈ before.takers,
      t ∈ after.takers ∨ own = some t.id ∨ ∃ g ∈ signals, g.id = t.id)
    (offers : ∀ o ∈ before.offers,
      o ∈ after.offers ∨ own = some o.id ∨ ∃ g ∈ signals, g.id = o.id) :
    accounted before after own signals = true := by
  refine accounted_iff.mpr fun id waits => ?_
  unfold waiting at waits
  rw [h.peekers, h.awaiters, List.append_nil, List.append_nil] at waits
  rcases List.mem_append.mp waits with taker | offer
  · obtain ⟨t, stored, rfl⟩ := List.mem_map.mp taker
    exact (takers t stored).imp_left fun stays =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨t, stays, rfl⟩)))
  · obtain ⟨o, pending, rfl⟩ := List.mem_map.mp offer
    exact (offers o pending).imp_left fun stays =>
      List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, stays, rfl⟩))

/-! ## The accept pass spends the room

Steps of `afterConsume_flags` and of `offer_flags`. `acceptLoop_spent` asks no premise of the
offers: it is the other half of `acceptLoop_length_le`
(`src/Effect4/Laws/Modules/Queue/Capacity.lean`). -/

/-- The room of a bounded queue. -/
theorem room_eq {s : State} {c : Nat} (capacity : s.capacity = some c) :
    room s = some (c - s.messages.length) := by
  unfold room
  rw [capacity]
  rfl

/-- **After the accept pass no offer is pending, or the finite room is spent.** -/
theorem acceptLoop_spent (r : Nat) (ms : List Nat) (os : List Offer) :
    (acceptLoop (some r) ms os).2.1 = [] ∨
      (acceptLoop (some r) ms os).1.length = ms.length + r := by
  induction os generalizing r ms with
  | nil => exact .inl (by rw [acceptLoop])
  | cons o os ih =>
    rw [acceptLoop]
    by_cases hr : (some r : Option Nat) = some 0
    · rw [if_pos hr]
      cases hr
      exact .inr rfl
    · rw [if_neg hr]
      dsimp only
      have least : fit (some r) o.rest.length = min r o.rest.length := rfl
      by_cases hl : (List.drop (fit (some r) o.rest.length) o.rest).isEmpty = true
      · rw [if_pos hl]
        dsimp only [Option.map_some]
        rcases ih (r - fit (some r) o.rest.length)
          (ms ++ o.rest.take (fit (some r) o.rest.length)) with drained | full
        · exact .inl drained
        · refine .inr ?_
          rw [full, List.length_append, List.length_take, least]
          omega
      · rw [if_neg hl]
        refine .inr ?_
        have more : fit (some r) o.rest.length < o.rest.length :=
          Nat.lt_of_not_le fun le => hl (List.isEmpty_iff.mpr (List.drop_eq_nil_iff.mpr le))
        show (ms ++ o.rest.take (fit (some r) o.rest.length)).length = ms.length + r
        rw [List.length_append, List.length_take]
        rw [least] at more ⊢
        omega

/-- The accept pass of a bounded queue leaves it spent. -/
theorem accept_spent {s : State} {c : Nat} (capacity : s.capacity = some c) :
    Spent (accept s).1 := by
  show (acceptLoop (room s) s.messages s.offers).2.1 = [] ∨
    s.capacity.map (· - (acceptLoop (room s) s.messages s.offers).1.length) = some 0
  rw [room_eq capacity, capacity]
  rcases acceptLoop_spent (c - s.messages.length) s.messages s.offers with drained | full
  · exact .inl drained
  · refine .inr ?_
    rw [full]
    show some (c - (s.messages.length + (c - s.messages.length))) = some 0
    exact congrArg some (by omega)

/-- A bounded queue that has no room has the room zero. -/
theorem room_of_full {s : State} {c : Nat} (capacity : s.capacity = some c)
    (full : ¬ hasRoom s = true) : room s = some 0 := by
  unfold hasRoom at full
  rw [room_eq capacity] at full ⊢
  exact congrArg some (Nat.eq_zero_of_not_pos fun positive => full (decide_eq_true positive))

/-! ## The model's parts on the profile

Steps of the five `Flags` lemmas of the operations. -/

/-- A queue that is not closing does not settle. -/
theorem settle_idle {s : State} (notClosing : ∀ e, s.phase ≠ .closing e) :
    settle s = (s, []) := by
  fun_cases settle s
  · next e closing _ => exact absurd closing (notClosing e)
  · next e closing _ => exact absurd closing (notClosing e)
  · rfl

/-- In an opened queue a consuming step's tail is the accept pass and the wake. -/
theorem afterConsume_opened {s : State} (opened : s.phase = .opened) :
    afterConsume s = ((accept s).1, (accept s).2 ++ wake (accept s).1) := by
  have idle : settle (accept s).1 = ((accept s).1, []) :=
    settle_idle fun e closing => Phase.noConfusion (opened.symm.trans closing)
  show ((settle (accept s).1).1,
    (accept s).2 ++ (settle (accept s).1).2 ++ wake (settle (accept s).1).1) = _
  rw [idle, List.append_nil]

/-- A taker that leaves is the step's own request. -/
theorem removeTaker_accounted {s : State} (h : FirstProfile s) (id : Nat)
    (signals : List Signal) : accounted s (removeTaker s id) (some id) signals = true :=
  accounted_of h
    (fun t stored => by
      by_cases same : t.id = id
      · exact .inr (.inl (by rw [same]))
      · exact .inl (List.mem_filter.mpr ⟨stored, bne_iff_ne.mpr same⟩))
    fun _ pending => .inl pending

/-- The accept pass accounts for each offer: it stays pending, or its answer is a signal
(`acceptLoop_single`). -/
theorem accept_accounted {s : State} (h : FirstProfile s) (own : Option Nat) :
    accounted s (accept s).1 own (accept s).2 = true := by
  refine accounted_of h (fun _ stored => .inl stored) fun o pending => ?_
  show o ∈ (acceptLoop (room s) s.messages s.offers).2.1 ∨ own = some o.id ∨
    ∃ g ∈ (acceptLoop (room s) s.messages s.offers).2.2, g.id = o.id
  rw [acceptLoop_single (room s) s.messages s.offers h.offers]
  rw [← List.take_append_drop (fit (room s) s.offers.length) s.offers] at pending
  rcases List.mem_append.mp pending with enters | stays
  · exact .inr (.inr ⟨⟨o.id, .offered true⟩, List.mem_map.mpr ⟨o, enters, rfl⟩, rfl⟩)
  · exact .inl stays

/-- **A consuming step's tail keeps the flags**, after any step that accounts for its
requests. The tail leaves the queue spent, and its signals end with the wake. -/
theorem afterConsume_flags {s p : State} {own : Option Nat} {first : List Signal}
    (h : FirstProfile p) (before : accounted s p own first = true) :
    Flags s own (afterConsume p).1 (first ++ (afterConsume p).2) := by
  obtain ⟨c, capacity⟩ := h.positive
  have tail : accounted p (accept p).1 own ((accept p).2 ++ wake (accept p).1) = true :=
    accounted_trans (accept_accounted h own) (accounted_refl (accept p).1 own (wake (accept p).1))
  rw [afterConsume_opened h.opened]
  exact
    { spent := accept_spent capacity
      woken := fun _ woken => .inl (List.mem_append_right _ (List.mem_append_right _ woken))
      accounted := accounted_trans before tail }

/-- The consuming arm of `take` and of `poll`: a pull from the buffer, then the tail. A request
at the minimum one is ready only where a message is buffered (`ready_profile`). -/
theorem consume_flags {s p : State} {own : Option Nat} (h : FirstProfile p)
    (ready1 : ready p 1 = true) (max : Nat) (before : accounted s p own [] = true) :
    Flags s own (afterConsume (pull p max).2.1).1
      ((pull p max).2.2 ++ (afterConsume (pull p max).2.1).2) := by
  have pulled : pull p max =
      (p.messages.take max, { p with messages := p.messages.drop max }, []) := by
    rw [ready_profile h] at ready1
    unfold pull
    cases empty : p.messages.isEmpty with
    | false => rfl
    | true =>
      rw [empty] at ready1
      exact absurd ready1 Bool.false_ne_true
  rw [pulled]
  exact afterConsume_flags
    (h.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) (List.Sublist.refl _)) before

/-- **A take that waits is not owed a signal.** Where a take at the bounds one and one is not
served, the wake does not name the take's own request. The take's enrolment changes no wake. So
the step may drop the request from `signalled`, as `bump` does. The model's half of
`wait-registration-no-gap`. -/
theorem wake_blocked {s : State} (h : FirstProfile s) {id : Nat}
    (blocked : ¬ (ready s 1 && (earlier s id).isEmpty) = true) :
    (∀ g ∈ wake s, some id ≠ some g.id) ∧
      wake { s with takers := s.takers ++ [⟨id, 1, 1⟩] } = wake s := by
  rw [ready_profile h] at blocked
  unfold earlier at blocked
  cases held : s.takers with
  | nil =>
    rw [held] at blocked
    have empty : s.messages.isEmpty = true := by
      cases buffered : s.messages.isEmpty with
      | true => rfl
      | false =>
        rw [buffered] at blocked
        exact absurd rfl blocked
    constructor
    · intro g named
      rw [wake_profile h, held] at named
      exact absurd named List.not_mem_nil
    · have idle : ready s 1 = false := by
        rw [ready_profile h, empty]
        rfl
      unfold wake
      rw [held]
      show (if ready s 1 = true then [(⟨id, .again⟩ : Signal)] else []) ++ _ = [] ++ _
      rw [idle]
      rfl
  | cons t ts =>
    rw [held] at blocked
    constructor
    · intro g named same
      rw [wake_profile h, held] at named
      cases buffered : s.messages.isEmpty with
      | true =>
        rw [buffered] at named
        exact absurd named List.not_mem_nil
      | false =>
        rw [buffered] at named blocked
        obtain rfl : g = ⟨t.id, .again⟩ := List.mem_singleton.mp named
        have mine : id = t.id := Option.some.inj same
        apply blocked
        rw [List.takeWhile_cons, mine, bne_self_eq_false]
        rfl
    · unfold wake
      rw [held]
      rfl

/-- A step that changes no state, posts no signal and is no request's own. -/
theorem idle_flags {s : State} (spent : Spent s) : Flags s none s [] :=
  { spent := spent
    woken := fun _ woken => .inr ⟨woken, nofun⟩
    accounted := accounted_refl s none [] }

/-- On the profile an offer waits behind the pending offers exactly where one is pending. -/
theorem behind_iff {s : State} (h : FirstProfile s) :
    (s.strategy == .suspend && !s.offers.isEmpty) = true ↔ s.offers ≠ [] := by
  rw [h.suspend]
  cases s.offers with
  | nil => exact ⟨fun behind => absurd behind Bool.false_ne_true, fun pending => absurd rfl pending⟩
  | cons o os => exact ⟨fun _ => List.cons_ne_nil o os, fun _ => rfl⟩

/-! ## The first operations

One lemma for each operation of the model: it keeps `Flags`, from a spent profile state. Each is
a step of `first_step_inv`, its one consumer, and takes its cases from the operation's own
definition. -/

/-- A take at the bounds one and one. Served, it consumes. Not served, it waits: enrolled
already, or enrolling now (`wake_blocked`). -/
theorem take_flags {s : State} (h : FirstProfile s) (spent : Spent s) (id : Nat) :
    Flags s (some id) (take s ⟨id, 1, 1⟩).1 (take s ⟨id, 1, 1⟩).2.2 := by
  fun_cases take s ⟨id, 1, 1⟩
  · next e done => cases h.opened.symm.trans done
  · next zero _ => exact absurd zero Bool.false_ne_true
  · next _ served _ _ _ =>
    exact consume_flags (removeTaker_profile id h) (Bool.and_eq_true_iff.mp served).1 1
      (removeTaker_accounted h id [])
  · next _ blocked _ _ =>
    exact
      { spent := spent
        woken := fun g woken => .inr ⟨woken, (wake_blocked h blocked).1 g woken⟩
        accounted := accounted_refl s (some id) [] }
  · next _ blocked _ _ =>
    exact
      { spent := spent
        woken := fun g woken =>
          have before : g ∈ wake s := (wake_blocked h blocked).2 ▸ woken
          .inr ⟨before, (wake_blocked h blocked).1 g before⟩
        accounted := accounted_of h (fun _ stored => .inl (List.mem_append_left _ stored))
          fun _ pending => .inl pending }

/-- An offer of one message. It waits behind a pending offer, it enters the room, or it pends
where no room is left. The other arms are not this profile's. -/
theorem offer_flags {s : State} (h : FirstProfile s) (spent : Spent s) (id a : Nat)
    (new : ∀ o ∈ s.offers, o.id ≠ id) (foreign : ∀ t ∈ s.takers, t.id ≠ id) :
    Flags s none (offer s id a).1 (offer s id a).2.2 := by
  have pend := h.pend id a new foreign
  obtain ⟨c, capacity⟩ := h.positive
  fun_cases offer s id a
  · exact idle_flags spent
  · next _ behind =>
    exact
      { spent := .inr (spent.resolve_left ((behind_iff h).mp behind))
        woken := fun _ woken =>
          .inr ⟨((wake_profile pend).trans (wake_profile h).symm) ▸ woken, nofun⟩
        accounted := accounted_of h (fun _ stored => .inl stored)
          fun _ pending => .inl (List.mem_append_left _ pending) }
  · next _ alone _ _ =>
    exact
      { spent := .inl (Decidable.of_not_not (mt (behind_iff h).mpr alone))
        woken := fun _ woken => .inl woken
        accounted := accounted_refl s none _ }
  · exact idle_flags spent
  · next _ _ _ sliding _ => exact absurd (h.suspend.symm.trans sliding) (by decide)
  · next _ _ full _ _ =>
    exact
      { spent := .inr (room_of_full capacity full)
        woken := fun _ woken => .inl woken
        accounted := accounted_of h (fun _ stored => .inl stored)
          fun _ pending => .inl (List.mem_append_left _ pending) }

/-- A poll. It answers nothing and changes nothing, or it consumes. -/
theorem poll_flags {s : State} (h : FirstProfile s) (spent : Spent s) :
    Flags s none (poll s).1 (poll s).2.2 := by
  fun_cases poll s
  · exact idle_flags spent
  · next served _ _ =>
    have ready1 : ready s 1 = true := by
      cases unready : ready s 1 with
      | true => rfl
      | false =>
        rw [unready] at served
        exact absurd (by rw [Bool.not_false, Bool.or_true, Bool.true_or]) served
    exact consume_flags h ready1 1 (accounted_refl s none [])

/-- A taker's withdrawal. The taker is the step's own request, and the signals are the wake. -/
theorem withdrawTake_flags {s : State} (h : FirstProfile s) (spent : Spent s) (id : Nat) :
    Flags s (some id) (withdrawTake s id).1 (withdrawTake s id).2 :=
  { spent := spent
    woken := fun _ woken => .inl woken
    accounted := removeTaker_accounted h id _ }

/-- An offer's withdrawal. It frees no room, so no pending offer enters. -/
theorem withdrawOffer_flags {s : State} (h : FirstProfile s) (spent : Spent s) (id : Nat) :
    Flags s (some id) (withdrawOffer s id).1 (withdrawOffer s id).2 := by
  fun_cases withdrawOffer s id
  · next done =>
    unfold isDone at done
    rw [h.opened] at done
    exact absurd done Bool.false_ne_true
  · next _ d =>
    have idle : d = ({ s with offers := s.offers.filter (fun o => o.id != id) }, []) :=
      settle_idle fun e closing => Phase.noConfusion (h.opened.symm.trans closing)
    rw [idle]
    exact
      { spent := spent.imp_left fun empty => by
          show s.offers.filter _ = []
          rw [empty, List.filter_nil]
        woken := fun _ woken => .inl (List.mem_append_right _ woken)
        accounted := accounted_of h (fun _ stored => .inl stored) fun o pending => by
          by_cases same : o.id = id
          · exact .inr (.inl (by rw [same]))
          · exact .inl (List.mem_filter.mpr ⟨pending, bne_iff_ne.mpr same⟩) }

/-! ## The step law -/

/-- **One step of a first operation keeps the run invariant.** From every run of the invariant,
the model's step by a first operation whose request keeps `Requested` leaves a run of the
invariant. So the step keeps both flags. After it no taker stands ready without a signal. Each
request that waited still waits, is the step's own, or is named by a signal.

It is the model's half of `wait-registration-no-gap` and of
`waiting-request-obligation-preserved`. Consumer: `first_run_inv`, and then the run-level law of
the Queue's wrapper. The statement is of the model alone: no program, no delivery of a signal, no
liveness and no fairness. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem first_step_inv (r : Run) (op : Op) (h : FirstRunInv r)
    (first : firstOp op = true) (requested : Requested r.s op) :
    FirstRunInv (step .none r op) := by
  have profile : FirstProfile (step .none r op).s :=
    step_state .none r op ▸ first_profile_closed r.s op h.profile first requested
  have bound := step_within h.profile h.within op
  have spent : Spent r.s := (tidy_iff h.profile.opened).mp h.tidy
  cases op with
  | take id min max =>
    have both : (min == 1 && max == 1) = true := first
    rw [Bool.and_eq_true] at both
    obtain ⟨rfl, rfl⟩ : min = 1 ∧ max = 1 :=
      ⟨of_decide_eq_true both.1, of_decide_eq_true both.2⟩
    exact bump_inv h profile bound (take_flags h.profile spent id)
  | offer id a =>
    by_cases pending : (r.s.offers.any fun o => o.id == id) = true
    · have same : step .none r (.offer id a) = r := if_pos pending
      rw [same]
      exact h
    · have next : step .none r (.offer id a) =
          bump r (offer r.s id a).1 none (offer r.s id a).2.2 := if_neg pending
      rw [next] at profile bound ⊢
      refine bump_inv h profile bound
        (offer_flags h.profile spent id a (fun o stored same => pending ?_) requested)
      exact List.any_eq_true.mpr ⟨o, stored, decide_eq_true same⟩
  | poll => exact bump_inv h profile bound (poll_flags h.profile spent)
  | dropTake id => exact bump_inv h profile bound (withdrawTake_flags h.profile spent id)
  | dropOffer id => exact bump_inv h profile bound (withdrawOffer_flags h.profile spent id)
  | _ => exact absurd first Bool.false_ne_true

/-! ## The run law -/

/-- The premises of a list of operations, each at the run that the operations before it leave:
a first operation, whose request keeps `Requested`. A premise at the first run alone says
nothing of a later step. -/
def FirstOps (r : Run) : List Op → Prop
  | [] => True
  | op :: ops => firstOp op = true ∧ Requested r.s op ∧ FirstOps (step .none r op) ops

/-- A request's premise decides. -/
instance (s : State) (op : Op) : Decidable (Requested s op) := by
  cases op <;> unfold Requested <;> infer_instance

/-- The premises of a list decide, so a guard reads the run law's own premise. -/
instance FirstOps.decidable : (r : Run) → (ops : List Op) → Decidable (FirstOps r ops)
  | _, [] => .isTrue trivial
  | r, op :: ops =>
    have := FirstOps.decidable (step .none r op) ops
    inferInstanceAs
      (Decidable (firstOp op = true ∧ Requested r.s op ∧ FirstOps (step .none r op) ops))

/-- **A list of first operations keeps the run invariant.** By induction over the list, with
`first_step_inv` at each step. It establishes what `first_step_inv` does, and no more. Consumer:
`first_run_flags`, and then the run-level law of the Queue's wrapper. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem first_run_inv (r : Run) (ops : List Op) (h : FirstRunInv r) (first : FirstOps r ops) :
    FirstRunInv (ops.foldl (step .none) r) := by
  induction ops generalizing r with
  | nil => exact h
  | cons op ops ih =>
    exact ih (step .none r op) (first_step_inv r op h first.1 first.2.1) first.2.2

/-- The empty queue of a positive capacity holds the invariant. -/
theorem empty_inv (c : Nat) : FirstRunInv { s := { capacity := some (c + 1) } } :=
  { profile := empty_profile c
    within := decide_eq_true (Nat.zero_le (c + 1))
    tidy := rfl
    quiet := rfl
    ok := rfl
    named := rfl }

/-- **From the empty queue both flags hold after every list of first operations.** The model's
bounded exploration holds both flags to a fixed depth, over more operations. This statement
holds them at every length, on the first profile. Consumer: the run-level law of the Queue's
wrapper. It says nothing of `close` or `shutdown`, and nothing of a delivery. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem first_run_flags (c : Nat) (ops : List Op)
    (first : FirstOps { s := { capacity := some (c + 1) } } ops) :
    (ops.foldl (step .none) { s := { capacity := some (c + 1) } }).ok = true ∧
      (ops.foldl (step .none) { s := { capacity := some (c + 1) } }).named = true :=
  have last := first_run_inv _ ops (empty_inv c) first
  ⟨last.ok, last.named⟩

end Effect4.Queue.Model
