import Test.Program.QueueModel
import ProofGraph.Plan
import Effect4.Laws.Auto.Semantics

/-!
# The Queue's first profile: its states, and their closure (decisions rows 219, 233)

`FirstProfile` is the predicate that the step goals of the Queue's first slice quantify over: an
opened queue of a positive capacity under `suspend`, whose waiting requests are those the first
operations leave. `first_profile_closed` is proved here: each first operation of the model
(`Test/Program/QueueModel.lean`) keeps the predicate, when its request keeps the step's premise.
No term, no cell and no machine occurs in this file.

Placement. Concept `reactive-scheduling`: preservation of an explicit state invariant.
Requirement R10, as a helper of the proposed claim `queue-expansion-agrees`, on the side of its
abstract client. Consumer: each step goal of the refinement from the Queue's `Ref.modify` term to
the abstract step, along a run. Reach: the model's `take` at the bounds one and one, `offer`,
`poll` and the two withdrawals. The statements establish no agreement of a term with the model,
no typed store preservation, no signal delivery, no order of service and no liveness.

The model's `within` and `tidy` are no part of the predicate: `within` is the capacity
statement's (`Test/Program/QueueCapacity.lean`). The design is
`docs/research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md`, F3. Codex's review
asked for the closed predicate before the step goals are stated.
-/

namespace Test.Program.QueueProfile
open QueueContract

/-- The states of the first profile: an opened queue of a positive capacity under `suspend`,
whose waiting requests are those the first operations leave. -/
structure FirstProfile (s : State) : Prop where
  opened : s.phase = .opened
  suspend : s.strategy = .suspend
  positive : ∃ c, s.capacity = some (c + 1)
  /-- Each stored taker has the bounds one and one. -/
  takers : ∀ t ∈ s.takers, t.min = 1 ∧ t.max = 1
  /-- Each pending offer is no batch, and holds one message. -/
  offers : ∀ o ∈ s.offers, o.batch = false ∧ o.rest.length = 1
  peekers : s.peekers = []
  awaiters : s.awaiters = []
  /-- No two waiting requests share an identity: among the takers, among the offers, and across
  the two. -/
  takersDistinct : (s.takers.map (·.id)).Nodup
  offersDistinct : (s.offers.map (·.id)).Nodup
  apart : ∀ t ∈ s.takers, ∀ o ∈ s.offers, t.id ≠ o.id

/-! ## Three ways a first operation changes a state -/

/-- A state with the same configuration, and with waiting requests that are sublists of a
profile state's, is of the profile. The buffer is free. -/
theorem FirstProfile.shrink {s s' : State} (h : FirstProfile s)
    (phase : s'.phase = s.phase) (strategy : s'.strategy = s.strategy)
    (capacity : s'.capacity = s.capacity) (peekers : s'.peekers = s.peekers)
    (awaiters : s'.awaiters = s.awaiters)
    (takers : s'.takers.Sublist s.takers) (offers : s'.offers.Sublist s.offers) :
    FirstProfile s' where
  opened := phase.trans h.opened
  suspend := strategy.trans h.suspend
  positive := capacity ▸ h.positive
  takers := fun t ht => h.takers t (takers.subset ht)
  offers := fun o ho => h.offers o (offers.subset ho)
  peekers := peekers.trans h.peekers
  awaiters := awaiters.trans h.awaiters
  takersDistinct := h.takersDistinct.sublist (takers.map _)
  offersDistinct := h.offersDistinct.sublist (offers.map _)
  apart := fun t ht o ho => h.apart t (takers.subset ht) o (offers.subset ho)

/-- A fresh taker with the bounds one and one enrols behind the others. -/
theorem FirstProfile.enrol {s : State} (h : FirstProfile s) (id : Nat)
    (new : ∀ t ∈ s.takers, t.id ≠ id) (foreign : ∀ o ∈ s.offers, o.id ≠ id) :
    FirstProfile { s with takers := s.takers ++ [⟨id, 1, 1⟩] } where
  opened := h.opened
  suspend := h.suspend
  positive := h.positive
  takers := fun t ht => by
    rcases List.mem_append.mp ht with old | this
    · exact h.takers t old
    · rw [List.mem_singleton.mp this]
      exact ⟨rfl, rfl⟩
  offers := h.offers
  peekers := h.peekers
  awaiters := h.awaiters
  takersDistinct := by
    show ((s.takers ++ [(⟨id, 1, 1⟩ : Taker)]).map (·.id)).Nodup
    rw [List.map_append]
    refine List.pairwise_append.mpr ⟨h.takersDistinct, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_singleton.mp hb]
    exact new t ht
  offersDistinct := h.offersDistinct
  apart := fun t ht o ho => by
    rcases List.mem_append.mp ht with old | this
    · exact h.apart t old o ho
    · rw [List.mem_singleton.mp this]
      exact fun eq => foreign o ho eq.symm

/-- A fresh single offer waits behind the others. -/
theorem FirstProfile.pend {s : State} (h : FirstProfile s) (id a : Nat)
    (new : ∀ o ∈ s.offers, o.id ≠ id) (foreign : ∀ t ∈ s.takers, t.id ≠ id) :
    FirstProfile { s with offers := s.offers ++ [⟨id, false, [a]⟩] } where
  opened := h.opened
  suspend := h.suspend
  positive := h.positive
  takers := h.takers
  offers := fun o ho => by
    rcases List.mem_append.mp ho with old | this
    · exact h.offers o old
    · rw [List.mem_singleton.mp this]
      exact ⟨rfl, rfl⟩
  peekers := h.peekers
  awaiters := h.awaiters
  takersDistinct := h.takersDistinct
  offersDistinct := by
    show ((s.offers ++ [(⟨id, false, [a]⟩ : Offer)]).map (·.id)).Nodup
    rw [List.map_append]
    refine List.pairwise_append.mpr ⟨h.offersDistinct, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hy]
    exact new o ho
  apart := fun t ht o ho => by
    rcases List.mem_append.mp ho with old | this
    · exact h.apart t ht o old
    · rw [List.mem_singleton.mp this]
      exact foreign t ht

/-! ## The model's parts

`acceptLoop_single` and `wake_profile` give two parts in closed form. They are steps of the step
goals: the signals of a first-profile step are the answers of the offers that entered, and then
the wake of at most one taker. -/

/-- A single offer's answer is that it was accepted. -/
theorem answerOf_single {o : Offer} (plain : o.batch = false) :
    answerOf o [] = .offered true := by
  unfold answerOf
  rw [plain]
  rfl

/-- One more single offer fits, where a place is free. -/
theorem fit_succ {room : Option Nat} (n : Nat) (free : room ≠ some 0) :
    fit room (n + 1) = fit (room.map (· - 1)) n + 1 := by
  cases room with
  | none => rfl
  | some r =>
    cases r with
    | zero => exact absurd rfl free
    | succ r =>
      show Nat.min (r + 1) (n + 1) = Nat.min (r + 1 - 1) n + 1
      rw [Nat.add_sub_cancel]
      exact Nat.succ_min_succ r n

/-- What `acceptLoop` answers on single offers: as many as fit enter, in arrival order. The
buffer gains their messages, the others stay pending, and each that entered is answered. -/
def entered (room : Option Nat) (ms : List Nat) (os : List Offer) :
    List Nat × List Offer × List Signal :=
  (ms ++ (os.take (fit room os.length)).flatMap (·.rest), os.drop (fit room os.length),
    (os.take (fit room os.length)).map fun o => ⟨o.id, .offered true⟩)

/-- **Single offers enter in arrival order, as many as fit.** A step of the take's and the
poll's step goals: it names the offers that a consuming step accepts, and their answers. -/
theorem acceptLoop_single (room : Option Nat) (ms : List Nat) (os : List Offer)
    (single : ∀ o ∈ os, o.batch = false ∧ o.rest.length = 1) :
    acceptLoop room ms os = entered room ms os := by
  unfold entered
  induction os generalizing room ms with
  | nil =>
    rw [acceptLoop]
    simp only [List.take_nil, List.drop_nil, List.flatMap_nil, List.map_nil, List.append_nil]
  | cons o os ih =>
    rw [acceptLoop]
    by_cases hr : room = some 0
    · rw [if_pos hr, hr]
      have none_fit : fit (some 0) (o :: os).length = 0 := Nat.zero_min _
      rw [none_fit]
      simp only [List.take_zero, List.drop_zero, List.flatMap_nil, List.map_nil, List.append_nil]
    · rw [if_neg hr]
      dsimp only
      obtain ⟨plain, one⟩ := single o (List.mem_cons_self ..)
      have fits : fit room o.rest.length = 1 := by
        rw [one]
        cases room with
        | none => rfl
        | some r =>
          have positive : 1 ≤ r := Nat.pos_of_ne_zero fun zero => hr (by rw [zero])
          exact Nat.min_eq_right positive
      have whole : o.rest.take 1 = o.rest := List.take_of_length_le (Nat.le_of_eq one)
      have spent : (o.rest.drop 1).isEmpty = true := by
        rw [List.drop_eq_nil_of_le (Nat.le_of_eq one)]
        rfl
      rw [fits, if_pos spent, whole, ih _ _ fun x hx => single x (List.mem_cons_of_mem _ hx)]
      have count : fit room (o :: os).length = fit (room.map (· - 1)) os.length + 1 :=
        fit_succ os.length hr
      rw [count, List.take_succ_cons, List.drop_succ_cons, List.flatMap_cons, List.map_cons,
        answerOf_single plain, List.append_assoc]

/-- What stays pending is a suffix of the pending offers. -/
theorem acceptLoop_suffix (room : Option Nat) (ms : List Nat) (os : List Offer)
    (single : ∀ o ∈ os, o.batch = false ∧ o.rest.length = 1) :
    (acceptLoop room ms os).2.1 <:+ os := by
  rw [acceptLoop_single room ms os single]
  exact List.drop_suffix _ _

/-- In a profile state a take at the minimum one is served exactly when a message is buffered. -/
theorem ready_profile {s : State} (h : FirstProfile s) : ready s 1 = !s.messages.isEmpty := by
  obtain ⟨c, capacity⟩ := h.positive
  have open_ : isClosing s = false := by unfold isClosing; rw [h.opened]
  have no_rendezvous : rendezvous s = false := by
    unfold rendezvous
    rw [capacity]
    rfl
  have least : threshold s 1 = 1 := by
    unfold threshold
    rw [open_, capacity]
    exact Nat.min_eq_left (Nat.succ_le_succ (Nat.zero_le c))
  unfold ready
  rw [no_rendezvous, least, Bool.or_false]
  cases s.messages with
  | nil => rfl
  | cons m ms => rfl

/-- **In a profile state the model wakes the earliest taker, when a message is buffered.** A
step of every step goal: it names the one taker that a step may notify, and no peeker. -/
theorem wake_profile {s : State} (h : FirstProfile s) :
    wake s = match s.takers with
      | t :: _ => if s.messages.isEmpty then [] else [⟨t.id, .again⟩]
      | [] => [] := by
  unfold wake
  rw [h.peekers]
  have ready_one := ready_profile h
  have bounds := h.takers
  revert bounds
  cases s.takers with
  | nil =>
    intro _
    simp only [List.map_nil, ite_self, List.append_nil]
  | cons t ts =>
    intro bounds
    have least : t.min = 1 := (bounds t (List.mem_cons_self ..)).1
    simp only [List.map_nil, ite_self, List.append_nil]
    rw [least, ready_one]
    cases s.messages with
    | nil => rfl
    | cons m ms => rfl

theorem settle_profile {s : State} (h : FirstProfile s) : FirstProfile (settle s).1 := by
  unfold settle
  split
  · next e closing => cases h.opened.symm.trans closing
  · exact h

theorem accept_profile {s : State} (h : FirstProfile s) : FirstProfile (accept s).1 :=
  h.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _)
    (acceptLoop_suffix (room s) s.messages s.offers h.offers).sublist

theorem afterConsume_profile {s : State} (h : FirstProfile s) :
    FirstProfile (afterConsume s).1 :=
  settle_profile (accept_profile h)

theorem removeTaker_profile {s : State} (id : Nat) (h : FirstProfile s) :
    FirstProfile (removeTaker s id) :=
  h.shrink rfl rfl rfl rfl rfl List.filter_sublist (List.Sublist.refl _)

theorem pull_profile {s : State} (max : Nat) (h : FirstProfile s) :
    FirstProfile (pull s max).2.1 := by
  unfold pull
  split
  · split
    · next o rest pending =>
      have tail : rest.Sublist s.offers := pending ▸ List.sublist_cons_self o rest
      split
      · next m more first =>
        split
        · exact h.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) tail
        · next more_left =>
          have one := (h.offers o (pending ▸ List.mem_cons_self ..)).2
          rw [first] at one
          have none_left : more = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj one)
          rw [none_left] at more_left
          exact absurd rfl more_left
      · exact h.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) tail
    · exact h
  · exact h.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) (List.Sublist.refl _)

/-! ## The first operations -/

/-- A take at the bounds one and one. Its request is its own waiting taker, or it names no
pending offer. -/
theorem take_profile {s : State} (h : FirstProfile s) (id : Nat)
    (foreign : ∀ o ∈ s.offers, o.id ≠ id) : FirstProfile (take s ⟨id, 1, 1⟩).1 := by
  unfold take
  split
  · next e done => cases h.opened.symm.trans done
  · split
    · exact h
    · split
      · exact afterConsume_profile (pull_profile 1 (removeTaker_profile id h))
      · split
        · exact h
        · next notEnrolled =>
          refine h.enrol id (fun t ht same => notEnrolled ?_) foreign
          exact List.any_eq_true.mpr ⟨t, ht, decide_eq_true same⟩

/-- An offer of one message. Its request names no waiting request. -/
theorem offer_profile {s : State} (h : FirstProfile s) (id a : Nat)
    (new : ∀ o ∈ s.offers, o.id ≠ id) (foreign : ∀ t ∈ s.takers, t.id ≠ id) :
    FirstProfile (offer s id a).1 := by
  unfold offer
  split
  · exact h
  · split
    · exact h.pend id a new foreign
    · split
      · exact h.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) (List.Sublist.refl _)
      · split
        · exact h
        · next sliding => exact absurd (h.suspend.symm.trans sliding) (by decide)
        · exact h.pend id a new foreign

theorem poll_profile {s : State} (h : FirstProfile s) : FirstProfile (poll s).1 := by
  unfold poll
  split
  · exact h
  · exact afterConsume_profile (pull_profile 1 h)

theorem withdrawTake_profile {s : State} (h : FirstProfile s) (id : Nat) :
    FirstProfile (withdrawTake s id).1 :=
  removeTaker_profile id h

theorem withdrawOffer_profile {s : State} (h : FirstProfile s) (id : Nat) :
    FirstProfile (withdrawOffer s id).1 := by
  unfold withdrawOffer
  split
  · exact h
  · exact settle_profile
      (h.shrink (s' := { s with offers := s.offers.filter (fun o => o.id != id) })
        rfl rfl rfl rfl rfl (List.Sublist.refl _) List.filter_sublist)

/-! ## The closure, over the model's own operations -/

/-- The first operations: a take at the bounds one and one, an offer of one message, a poll, and
the two withdrawals. -/
def first : Op → Bool
  | .take _ min max => min == 1 && max == 1
  | .offer .. | .poll | .dropTake _ | .dropOffer _ => true
  | _ => false

/-- A request's premise. A take's request names no pending offer: it is fresh, or it is its own
waiting taker. An offer's request names no waiting taker. The model's `step` itself passes an
offer whose request waits already. -/
def Requested (s : State) : Op → Prop
  | .take id _ _ => ∀ o ∈ s.offers, o.id ≠ id
  | .offer id _ => ∀ t ∈ s.takers, t.id ≠ id
  | _ => True

/-- **The first profile is closed.** Each first operation of the model leaves a state of the
profile, when its request keeps the premise. Consumer: each step goal of the Queue's
term-to-model refinement, along a run. No wrapper or host claim. -/
@[semantics "reactive-scheduling" (requirement := R10)]
theorem first_profile_closed (s : State) (op : Op) (h : FirstProfile s)
    (isFirst : first op = true) (requested : Requested s op) :
    FirstProfile (step .none { s := s } op).s := by
  cases op with
  | take id min max =>
    have both : (min == 1 && max == 1) = true := isFirst
    rw [Bool.and_eq_true] at both
    obtain ⟨rfl, rfl⟩ : min = 1 ∧ max = 1 :=
      ⟨of_decide_eq_true both.1, of_decide_eq_true both.2⟩
    exact take_profile h id requested
  | offer id a =>
    simp only [step]
    split
    · exact h
    · next notPending =>
      refine offer_profile h id a (fun o ho same => notPending ?_) requested
      exact List.any_eq_true.mpr ⟨o, ho, decide_eq_true same⟩
  | poll => exact poll_profile h
  | dropTake id => exact withdrawTake_profile h id
  | dropOffer id => exact withdrawOffer_profile h id
  | peek id => exact absurd isFirst Bool.false_ne_true
  | offerAll id ms => exact absurd isFirst Bool.false_ne_true
  | clear => exact absurd isFirst Bool.false_ne_true
  | close e => exact absurd isFirst Bool.false_ne_true
  | shutdown => exact absurd isFirst Bool.false_ne_true
  | await id => exact absurd isFirst Bool.false_ne_true
  | dropPeek id => exact absurd isFirst Bool.false_ne_true
  | dropAwait id => exact absurd isFirst Bool.false_ne_true

/-- The model's own word for the identities: in a profile state no two waiting requests share
one. -/
theorem waiting_nodup {s : State} (h : FirstProfile s) : (waiting s).Nodup := by
  unfold waiting
  rw [h.peekers, h.awaiters, List.append_nil, List.append_nil]
  refine List.pairwise_append.mpr ⟨h.takersDistinct, h.offersDistinct, ?_⟩
  intro a ha b hb
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hb
  exact h.apart t ht o ho

/-- The empty queue of a positive capacity is of the profile. -/
theorem empty_profile (c : Nat) : FirstProfile { capacity := some (c + 1) } where
  opened := rfl
  suspend := rfl
  positive := ⟨c, rfl⟩
  takers := fun _ ht => absurd ht List.not_mem_nil
  offers := fun _ ho => absurd ho List.not_mem_nil
  peekers := rfl
  awaiters := rfl
  takersDistinct := List.Pairwise.nil
  offersDistinct := List.Pairwise.nil
  apart := fun _ ht => absurd ht List.not_mem_nil

/-- info: 'Test.Program.QueueProfile.first_profile_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms first_profile_closed

/--
info: Test.Program.QueueProfile.first_profile_closed: proved; nearest []; 29 lemmas, 72 definitions
next goals: 0
-/
#guard_msgs in
#plan_status first_profile_closed

/-! ## The predicate decides -/

instance (s : State) : Decidable (FirstProfile s) :=
  match capacity : s.capacity with
  | some (c + 1) =>
    if rest : s.phase = .opened ∧ s.strategy = .suspend ∧
        (∀ t ∈ s.takers, t.min = 1 ∧ t.max = 1) ∧
        (∀ o ∈ s.offers, o.batch = false ∧ o.rest.length = 1) ∧
        s.peekers = [] ∧ s.awaiters = [] ∧
        (s.takers.map (·.id)).Nodup ∧ (s.offers.map (·.id)).Nodup ∧
        (∀ t ∈ s.takers, ∀ o ∈ s.offers, t.id ≠ o.id) then
      isTrue
        { opened := rest.1
          suspend := rest.2.1
          positive := ⟨c, capacity⟩
          takers := rest.2.2.1
          offers := rest.2.2.2.1
          peekers := rest.2.2.2.2.1
          awaiters := rest.2.2.2.2.2.1
          takersDistinct := rest.2.2.2.2.2.2.1
          offersDistinct := rest.2.2.2.2.2.2.2.1
          apart := rest.2.2.2.2.2.2.2.2 }
    else
      isFalse fun h => rest ⟨h.opened, h.suspend, h.takers, h.offers, h.peekers, h.awaiters,
        h.takersDistinct, h.offersDistinct, h.apart⟩
  | some 0 => isFalse fun h => by
    obtain ⟨c, positive⟩ := h.positive
    rw [capacity] at positive
    cases positive
  | none => isFalse fun h => by
    obtain ⟨c, positive⟩ := h.positive
    rw [capacity] at positive
    cases positive

/-! ## Controls: finite checks, one input each -/

/-- The profile on one state, as a Boolean. -/
def inProfile (s : State) : Bool := decide (FirstProfile s)

def T (id : Nat) : Taker := ⟨id, 1, 1⟩

-- The empty queue, and a state that the first operations reach.
#guard inProfile { capacity := some 2 }
#guard inProfile
  { capacity := some 1, messages := [1], takers := [T 1, T 2], offers := [⟨101, false, [2]⟩] }
-- Red controls, one for each condition. The phase, the strategy, the capacity.
#guard !inProfile { capacity := some 2, phase := .closing .ended }
#guard !inProfile { capacity := some 2, strategy := .sliding }
#guard !inProfile { capacity := some 0 }
#guard !inProfile {}
-- A stored taker with other bounds; a batch; an offer of two messages.
#guard !inProfile { capacity := some 2, takers := [⟨1, 2, 2⟩] }
#guard !inProfile { capacity := some 2, offers := [⟨7, true, [1]⟩] }
#guard !inProfile { capacity := some 2, offers := [⟨7, false, [1, 2]⟩] }
-- A peeker (Codex's witness: the model wakes it, and the cell's step names no peeker); an awaiter.
#guard !inProfile { capacity := some 2, takers := [T 1], peekers := [2] }
#guard !inProfile { capacity := some 2, awaiters := [3] }
-- One identity for two requests: two takers, and a taker with an offer.
#guard !inProfile { capacity := some 2, takers := [T 1, T 1] }
#guard !inProfile { capacity := some 2, takers := [T 1], offers := [⟨1, false, [5]⟩] }

/-- One step of the model from a state. -/
def next (s : State) (op : Op) : State := (step .none { s := s } op).s

def full : State := { capacity := some 1, messages := [1], takers := [T 1] }

-- The closed form of the accept pass: two of three single offers enter two free places.
#guard acceptLoop (some 2) [1] [⟨7, false, [5]⟩, ⟨8, false, [6]⟩, ⟨9, false, [7]⟩] =
  ([1, 5, 6], [⟨9, false, [7]⟩], [⟨7, .offered true⟩, ⟨8, .offered true⟩])
-- Red control of its premise: a batch enters in part, and the closed form says otherwise.
#guard acceptLoop (some 1) [1] [⟨7, true, [9, 8]⟩] !=
  entered (some 1) [1] [⟨7, true, [9, 8]⟩]
-- The wake: the earliest taker behind a message, and nobody at an empty buffer.
#guard wake full = [⟨1, .again⟩] && wake { full with messages := [] } = []
-- Red control of its premise: with a peeker the model wakes two requests.
#guard wake { full with peekers := [2] } = [⟨1, .again⟩, ⟨2, .again⟩]

-- Each first operation keeps the profile on one input.
#guard inProfile full && inProfile (next full (.take 1 1 1)) && inProfile (next full (.take 2 1 1))
#guard inProfile (next full (.offer 100 5)) && inProfile (next full .poll)
#guard inProfile (next full (.dropTake 1)) && inProfile (next full (.dropOffer 100))
-- Red control of the request's premise: an offer by a waiting taker's identity leaves the profile.
#guard !inProfile (next full (.offer 1 5))
-- Red controls of the first operations: a peek and a batch each leave the profile.
#guard !inProfile (next { capacity := some 1 } (.peek 2))
#guard !inProfile (next full (.offerAll 100 [5, 6]))

end Test.Program.QueueProfile
