import Effect4.Laws.Api.Runner
import Test.Dogfood.Scenario.QueueWorkers.Model
import Effect4.Laws.Library.Queue.Invariant
import Effect4.Laws.Library.Queue.Conservation

/-!
# Queue ledger readings

Concept: translation-simulation, R10, and reactive-scheduling, R12.
These helpers serve the queue scenario's conservation and settled-state clauses.
The consumer is the command-boundary assertion module.
The ledger records the model queue, fed jobs, assignments, custody and loss.
Each reading assumes the ledger matches the actual observation.
It establishes no machine-to-model connection, delivery, progress or host behaviour.
Decisions rows 254 and 275 bound the scenario fragment.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.QueueWorkers.Accounting

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.QueueWorkers
open Effect4.Api.HostSession (Key Phase)
open Effect4.Api.Runner (Command)

/-- The jobs that a model state of the Queue holds: the buffered ones, then the pending ones. -/
abbrev stateJobs := Queue.Model.stateJobs

/-- The view of a model state's cell, as the observation reads it (`queueView`): the capacity,
the buffer, each pending offer's flag and jobs, and the count of the waiting takers. -/
def viewOf (q : Queue.Model.State) : QueueView :=
  ⟨q.capacity.getD 0, q.messages.map Val.nat,
    q.offers.map (fun o => (o.batch, o.rest.map Val.nat)), q.takers.length⟩

/-- **What the invariant knows of a crew run**, as data. A job is a natural number that reaches the feeder offer continuation. -/
structure Ledger where
  /-- The queue's model run, once the root made the cell. -/
  queue : Option Queue.Model.Run
  /-- The resolved jobs entering feeder offers, in the order of those source entries. -/
  fed : List Nat
  /-- The assignment: each noted job with its worker, in order. -/
  assigned : List (Nat × Nat)
  /-- The job that the root's poll took, once the root answered it. -/
  leftover : List Nat
  /-- The jobs that a crew member received and has not yet stored. -/
  custody : List Nat
  /-- The jobs that left with no holder: a withdrawn offer's, or a dead holder's. -/
  lost : List Nat

/-- The jobs of the ledger's cell. -/
def Ledger.cellJobs (a : Ledger) : List Nat :=
  match a.queue with
  | none => []
  | some r => stateJobs r.s

/-- The held jobs that the ledger reads: the cell's, the assigned ones and the leftover. -/
def Ledger.heldJobs (a : Ledger) : List Nat :=
  a.cellJobs ++ a.assigned.map Prod.fst ++ a.leftover

/-- **The ledger's conservation.** Every fed job is held, in custody, or lost, as many times as it
was fed. -/
def Ledger.Conserved (a : Ledger) : Prop := a.fed.Perm (a.heldJobs ++ a.custody ++ a.lost)

/-- The queue's reading of a ledger. -/
def Ledger.queueCell (a : Ledger) : QueueCell :=
  match a.queue with
  | none => .unmade
  | some r => .holds (viewOf r.s)

/-- **What an observation shows of a ledger**: the queue's cell, the assignment, the fed jobs and
the root's leftover. -/
structure Ledger.Shows (a : Ledger) (o : Observation) : Prop where
  queue : o.queue = a.queueCell
  assignment : o.assignment = a.assigned.map (fun e => gave e.1 e.2)
  fed : o.fed = a.fed.map Val.nat
  leftover : o.leftover = a.leftover.map Val.nat

/-- The assigned jobs, read back. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem filterMap_gave : ∀ (l : List (Nat × Nat)),
    (l.map (fun e => gave e.1 e.2)).filterMap jobOf = (l.map Prod.fst).map Val.nat
  | [] => rfl
  | e :: rest => by
    rw [List.map_cons, List.filterMap_cons, filterMap_gave rest]
    rfl

/-- The pending jobs of a view, read back. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem flatMap_offers : ∀ (os : List Queue.Model.Offer),
    (os.map (fun o => (o.batch, o.rest.map Val.nat))).flatMap (·.2) =
      (os.flatMap (·.rest)).map Val.nat
  | [] => rfl
  | o :: rest => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, flatMap_offers rest, List.map_append]

/-- **The held jobs of an observation are the ledger's.** -/
@[semantics "translation-simulation" (requirement := R10)]
theorem held_of_shows {a : Ledger} {o : Observation} (h : a.Shows o) :
    o.held = a.heldJobs.map Val.nat := by
  unfold Observation.held Ledger.heldJobs
  rw [h.queue, h.assignment, h.leftover, filterMap_gave, List.map_append, List.map_append]
  unfold Ledger.queueCell Ledger.cellJobs
  cases a.queue with
  | none => rfl
  | some r =>
    show r.s.messages.map Val.nat ++
        (r.s.offers.map (fun o => (o.batch, o.rest.map Val.nat))).flatMap (·.2) ++ _ ++ _ = _
    unfold stateJobs Queue.Model.stateJobs
    rw [flatMap_offers, List.map_append]

/-- A conserving ledger's fed jobs are its held ones, then the rest. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem fed_perm {a : Ledger} (conserved : a.Conserved) :
    (a.fed.map Val.nat).Perm (a.heldJobs.map Val.nat ++ (a.custody ++ a.lost).map Val.nat) := by
  have perm := conserved.map Val.nat
  rw [List.append_assoc, List.map_append] at perm
  exact perm

/-- **No job is held more often than it was fed**, on a ledger that the observation shows and
that conserves. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem heldWithin_of_ledger {a : Ledger} {o : Observation} (shows : a.Shows o)
    (conserved : a.Conserved) : o.heldWithin = true := by
  unfold Observation.heldWithin
  rw [List.all_eq_true]
  intro job _
  rw [held_of_shows shows, shows.fed, (fed_perm conserved).count_eq, List.count_append]
  exact decide_eq_true (Nat.le_add_right _ _)

/-- **The fed jobs are no more than the held ones, but for the lost ones**, on a ledger with no
custody. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem accounted_of_ledger {a : Ledger} {o : Observation} (shows : a.Shows o)
    (conserved : a.Conserved) (custody : a.custody = [])
    (lost : a.lost.length ≤ (if o.live 3 then 0 else 1)) : o.accounted = true := by
  unfold Observation.accounted
  apply decide_eq_true
  rw [shows.fed, held_of_shows shows, List.length_map, List.length_map, conserved.length_eq,
    List.length_append, List.length_append, custody, List.length_nil, Nat.add_zero]
  exact Nat.add_le_add_left lost _

/-- The queue's facts at rest, against an observation: the model's run invariant, no request
left signalled, the scenario's capacity, the waiting takers as the idle workers, and one pending
offer exactly where the feeder is idle. -/
structure QueueAtRest (o : Observation) (r : Queue.Model.Run) : Prop where
  inv : Queue.Model.FirstRunInv r
  signalled : r.signalled = []
  capacity : r.s.capacity = some capacity
  takers : r.s.takers.length = ([1, 2].filter o.idle).length
  offers : r.s.offers.length = (if o.idle 3 then 1 else 0)

/-- The queue's facts at rest of a ledger: with no cell, no member is idle. -/
def Ledger.RestQueue (a : Ledger) (o : Observation) : Prop :=
  match a.queue with
  | none => ([1, 2].filter o.idle).length = 0 ∧ o.idle 3 = false
  | some r => QueueAtRest o r

/-- A quiet profile state with no signalled request has no waiting taker beside a message. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem quiet_nil {s : Queue.Model.State} (h : Queue.Model.FirstProfile s)
    (quiet : Queue.Model.quiet s [] = true) : s.messages = [] ∨ s.takers = [] := by
  unfold Queue.Model.quiet at quiet
  rw [Bool.and_eq_true] at quiet
  cases ht : s.takers with
  | nil => exact .inr rfl
  | cons t ts =>
    have first : (!Queue.Model.ready s t.min || ([] : List Nat).contains t.id) = true := by
      have head := quiet.1
      rw [ht] at head
      exact head
    have unready : Queue.Model.ready s t.min = false := by
      cases hr : Queue.Model.ready s t.min with
      | false => rfl
      | true =>
        rw [hr] at first
        exact absurd first Bool.false_ne_true
    have least : t.min = 1 := (h.takers t (ht ▸ List.mem_cons_self)).1
    rw [least, Queue.Model.ready_profile h] at unready
    cases he : s.messages.isEmpty with
    | true => exact .inl (List.isEmpty_iff.mp he)
    | false =>
      rw [he] at unready
      exact Bool.noConfusion unready

/-- A tidy profile state within capacity one is spent: no offer pends, or the buffer is full. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem spent_one {s : Queue.Model.State} (h : Queue.Model.FirstProfile s)
    (one : s.capacity = some 1) (tidy : Queue.Model.tidy s = true)
    (within : Queue.Model.within s = true) : s.offers = [] ∨ s.messages.length = 1 := by
  have bound : s.messages.length ≤ 1 := by
    unfold Queue.Model.within at within
    rw [one] at within
    exact of_decide_eq_true within
  rcases (Queue.Model.tidy_iff h.opened).mp tidy with none | full
  · exact .inl none
  · rw [Queue.Model.room_eq one] at full
    have zero : 1 - s.messages.length = 0 := Option.some.inj full
    exact .inr (by omega)

/-- A model state's buffer within capacity one. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem within_one {s : Queue.Model.State} (one : s.capacity = some 1)
    (within : Queue.Model.within s = true) : s.messages.length ≤ 1 := by
  unfold Queue.Model.within at within
  rw [one] at within
  exact of_decide_eq_true within

/-- **The queue is settled**, read from a view's seven parts. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem settled_of_view {o : Observation} {q : QueueView} (hview : o.queue.view = some q)
    (cap : q.capacity = capacity)
    (offers : ∀ offer ∈ q.offers, offer.1 = false ∧ offer.2.length = 1)
    (takers : q.takers = ([1, 2].filter o.idle).length)
    (pending : q.offers.length = (if o.idle 3 then 1 else 0))
    (quiet : q.buffered = [] ∨ q.takers = 0)
    (full : q.offers = [] ∨ q.buffered.length = q.capacity)
    (within : q.buffered.length ≤ q.capacity) : o.settled = true := by
  unfold Observation.settled
  rw [hview]
  have hA : (q.capacity == capacity) = true := beq_iff_eq.mpr cap
  have hB : q.offers.all (fun offer => !offer.1 && offer.2.length == 1) = true := by
    rw [List.all_eq_true]
    intro offer member
    obtain ⟨plain, one⟩ := offers offer member
    rw [plain, one]
    rfl
  have hC : (q.takers == ([1, 2].filter o.idle).length) = true := beq_iff_eq.mpr takers
  have hD : (q.offers.length == (if o.idle 3 then 1 else 0)) = true := beq_iff_eq.mpr pending
  have hE : (q.buffered.isEmpty || q.takers == 0) = true := by
    rcases quiet with empty | none
    · rw [empty]
      rfl
    · rw [none, Bool.or_eq_true]
      exact .inr rfl
  have hF : (q.offers.isEmpty || q.buffered.length == q.capacity) = true := by
    rcases full with empty | buffered
    · rw [empty]
      rfl
    · rw [Bool.or_eq_true]
      exact .inr (beq_iff_eq.mpr buffered)
  have hG : decide (q.buffered.length ≤ q.capacity) = true := decide_eq_true within
  show (q.capacity == capacity && q.offers.all (fun offer => !offer.1 && offer.2.length == 1) &&
      q.takers == ([1, 2].filter o.idle).length &&
      q.offers.length == (if o.idle 3 then 1 else 0) &&
      (q.buffered.isEmpty || q.takers == 0) &&
      (q.offers.isEmpty || q.buffered.length == q.capacity) &&
      decide (q.buffered.length ≤ q.capacity)) = true
  rw [hA, hB, hC, hD, hE, hF, hG]
  rfl

/-- **At rest the queue is settled**, on a ledger that the observation shows, with the queue's
facts at rest. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem settled_of_ledger {a : Ledger} {o : Observation} (shows : a.Shows o)
    (rest : a.RestQueue o) : o.settled = true := by
  unfold Ledger.RestQueue at rest
  cases hq : a.queue with
  | none =>
    rw [hq] at rest
    have hview : o.queue.view = some ⟨capacity, [], [], 0⟩ := by
      rw [shows.queue]
      unfold Ledger.queueCell
      rw [hq]
      rfl
    refine settled_of_view hview rfl (fun _ member => absurd member List.not_mem_nil)
      rest.1.symm ?_ (.inl rfl) (.inl rfl) (Nat.zero_le _)
    rw [rest.2]
    rfl
  | some r =>
    rw [hq] at rest
    have hview : o.queue.view = some (viewOf r.s) := by
      rw [shows.queue]
      unfold Ledger.queueCell
      rw [hq]
      rfl
    have profile := rest.inv.profile
    have quiet : Queue.Model.quiet r.s [] = true := rest.signalled ▸ rest.inv.quiet
    refine settled_of_view hview ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · show r.s.capacity.getD 0 = capacity
      rw [rest.capacity]
      rfl
    · intro offer member
      obtain ⟨o', stored, rfl⟩ := List.mem_map.mp member
      obtain ⟨plain, one⟩ := profile.offers o' stored
      exact ⟨plain, by rw [List.length_map, one]⟩
    · exact rest.takers
    · show (r.s.offers.map _).length = _
      rw [List.length_map]
      exact rest.offers
    · rcases quiet_nil profile quiet with empty | none
      · exact .inl (by show r.s.messages.map Val.nat = []; rw [empty]; rfl)
      · exact .inr (by show r.s.takers.length = 0; rw [none]; rfl)
    · rcases spent_one profile rest.capacity rest.inv.tidy rest.inv.within with none | full
      · exact .inl (by show r.s.offers.map _ = []; rw [none]; rfl)
      · refine .inr ?_
        show (r.s.messages.map Val.nat).length = r.s.capacity.getD 0
        rw [List.length_map, full, rest.capacity]
        rfl
    · show (r.s.messages.map Val.nat).length ≤ r.s.capacity.getD 0
      rw [List.length_map, rest.capacity]
      exact within_one rest.capacity rest.inv.within


@[semantics "translation-simulation" (requirement := R10)]
theorem exit_eq (s : Run) : s.exit = (s.machine.fiber? Api.root).bind RunFiber.exit := by
  show (Api.HostSession.inspect s.session).exit = _
  unfold Api.HostSession.inspect
  cases hst : s.session.machine.stuck with
  | some why =>
    simp only [replayEval, hst]
    rfl
  | none =>
    cases hfin : s.session.machine.finished with
    | true =>
      simp only [replayEval, hst, hfin]
      rfl
    | false =>
      simp only [replayEval, hst, hfin, Bool.false_eq_true, if_false]
      rfl

/-- The opened run's root has not exited. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem opened_exit (fuel : Nat) (b : Api.Built) : (openedAt fuel b).exit = none := by
  rw [exit_eq]
  rfl

/-- The empty ledger. -/
def Ledger.empty : Ledger := ⟨none, [], [], [], [], []⟩

/-- **The ledger at the opened run**: nothing made, nothing fed, nothing held. It is the ledger's
part of the frame's start. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem ledger_opened (fuel : Nat) (b : Api.Built) :
    Ledger.empty.Shows (observe (openedAt fuel b)) ∧ Ledger.empty.Conserved := by
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, List.Perm.refl _⟩
  unfold Observation.leftover observe
  rw [opened_exit]
  rfl

/-- The value of an accepted reply receipt at a key, as `fedOf` reads it. -/
def submitValue (key : Key) : Command × Phase → Option Val
  | (.submit reply, .preflight) =>
    if reply.key == key then
      match reply.completion with
      | .ofExit (.success value) => some value
      | _ => none
    else none
  | _ => none

/-- The fed job of one row, as `fedOf` reads it. -/
def appliedValue (rs : List (Command × Phase)) (seen : Key → Option Test.Dogfood.Scenario.Seen) :
    Command × Phase → Option Val
  | (.apply key, .applied) =>
    match seen key with
    | some call => if call.row == "Jobs.take" then rs.findSome? (submitValue key) else none
    | none => none
  | _ => none

/-- `fedOf`, with its two readers named. -/
theorem originalFedOf_eq (s : Run) :
    Original.fedOf s = (Test.Dogfood.Scenario.rows s).filterMap
      (appliedValue (Test.Dogfood.Scenario.rows s) (Test.Dogfood.Scenario.seenAt s)) := rfl

/-- Playing one row appends it, with its verdict, to the run's rows. -/
theorem rows_step (s : Run) (c : Command) (hlen : s.journal.length = s.phases.length) :
    Test.Dogfood.Scenario.rows (s.step c) =
      Test.Dogfood.Scenario.rows s ++ [(c, (Api.Runner.result s.runner c).phase)] := by
  show (s.journal ++ [c]).zip (s.phases ++ [(Api.Runner.result s.runner c).phase]) = _
  rw [List.zip_append hlen]
  rfl

/-- A refused row keeps the machine (`Api.Runner.step_refused`: it keeps the session). -/
theorem machine_refused (s : Run) (c : Command) (why : Api.HostSession.Refusal)
    (h : (Api.Runner.result s.runner c).phase = .refused why) :
    (s.step c).machine = s.machine := by
  have kept := Api.Runner.step_refused s.runner c why h
  show (Api.Runner.step s.runner c).1.session.machine = s.session.machine
  rw [kept]
  rfl

/-- A refused row binds no call. -/
theorem bound_refused (s : Run) (c : Command) (why : Api.HostSession.Refusal)
    (hlen : s.journal.length = s.phases.length)
    (h : (Api.Runner.result s.runner c).phase = .refused why) :
    Test.Dogfood.Scenario.bound (s.step c) = Test.Dogfood.Scenario.bound s := by
  unfold Test.Dogfood.Scenario.bound
  rw [rows_step s c hlen, h, List.filterMap_append]
  cases c <;> simp only [List.filterMap_cons, List.filterMap_nil, List.append_nil]

/-- A refused row changes no call that the host holds or held. -/
theorem seenAt_refused (s : Run) (c : Command) (why : Api.HostSession.Refusal)
    (hlen : s.journal.length = s.phases.length)
    (h : (Api.Runner.result s.runner c).phase = .refused why) :
    Test.Dogfood.Scenario.seenAt (s.step c) = Test.Dogfood.Scenario.seenAt s := by
  funext key
  show ((Test.Dogfood.Scenario.bound (s.step c)).filterMap
      (Test.Dogfood.Scenario.seenOf (s.step c))).find? (·.key == key) =
    ((Test.Dogfood.Scenario.bound s).filterMap (Test.Dogfood.Scenario.seenOf s)).find? (·.key == key)
  rw [bound_refused s c why hlen h]
  rfl

/-- A refused row's receipt reads no value. -/
theorem submitValue_refused (key : Key) (c : Command) (why : Api.HostSession.Refusal) :
    [(c, Phase.refused why)].findSome? (submitValue key) = none := by
  cases c <;> rfl

/-- A refused row changes no row's fed job. -/
theorem appliedValue_refused (rs : List (Command × Phase))
    (seen : Key → Option Test.Dogfood.Scenario.Seen) (c : Command)
    (why : Api.HostSession.Refusal) (row : Command × Phase) :
    appliedValue (rs ++ [(c, .refused why)]) seen row = appliedValue rs seen row := by
  rcases row with ⟨cmd, phase⟩
  cases cmd with
  | apply key =>
    cases phase with
    | applied =>
      show (match seen key with
          | some call =>
            if call.row == "Jobs.take" then
              (rs ++ [(c, Phase.refused why)]).findSome? (submitValue key) else none
          | none => none) =
        (match seen key with
          | some call => if call.row == "Jobs.take" then rs.findSome? (submitValue key) else none
          | none => none)
      rw [List.findSome?_append, submitValue_refused, Option.or_none]
    | bound => rfl
    | preflight => rfl
    | progressed => rfl
    | frontier => rfl
    | refused _ => rfl
  | bind _ _ => rfl
  | submit _ => rfl
  | control _ => rfl

/-- **A refused row feeds nothing.** General in its proof: it reads only the journal's lookups. -/
theorem originalFedOf_refused (s : Run) (c : Command) (why : Api.HostSession.Refusal)
    (hlen : s.journal.length = s.phases.length)
    (h : (Api.Runner.result s.runner c).phase = .refused why) :
    Original.fedOf (s.step c) = Original.fedOf s := by
  rw [originalFedOf_eq, originalFedOf_eq, seenAt_refused s c why hlen h, rows_step s c hlen, h,
    List.filterMap_append]
  have same : appliedValue (Test.Dogfood.Scenario.rows s ++ [(c, .refused why)])
      (Test.Dogfood.Scenario.seenAt s) =
      appliedValue (Test.Dogfood.Scenario.rows s) (Test.Dogfood.Scenario.seenAt s) :=
    funext (appliedValue_refused _ _ c why)
  have none : [(c, Phase.refused why)].filterMap
      (appliedValue (Test.Dogfood.Scenario.rows s) (Test.Dogfood.Scenario.seenAt s)) = [] := by
    cases c <;> rfl
  rw [same, none, List.append_nil]

/-- A refused row reaches no new offer continuation. -/
theorem fedOf_refused (s : Run) (c : Command) (why : Api.HostSession.Refusal)
    (_hlen : s.journal.length = s.phases.length)
    (refused : (Api.Runner.result s.runner c).phase = .refused why) :
    fedOf (s.step c) = fedOf s := by
  unfold fedOf
  rw [machine_refused s c why refused]

/-- **A refused row keeps what the observation shows of a ledger.** One row of the invariant's
step, proved outright: the session, so the machine, stays, and the fed jobs stay. -/
theorem shows_refused {a : Ledger} (s : Run) (c : Command) (why : Api.HostSession.Refusal)
    (hlen : s.journal.length = s.phases.length)
    (h : (Api.Runner.result s.runner c).phase = .refused why)
    (shows : a.Shows (observe s)) : a.Shows (observe (s.step c)) := by
  have machine : (s.step c).machine = s.machine := machine_refused s c why h
  have exit : (s.step c).exit = s.exit := by rw [exit_eq, exit_eq, machine]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← shows.queue]
    show queueCell ((s.step c).machine.state.refs[0]?) = queueCell (s.machine.state.refs[0]?)
    rw [machine]
  · rw [← shows.assignment]
    show entries ((s.step c).machine.state.refs[3]?) = entries (s.machine.state.refs[3]?)
    rw [machine]
  · rw [← shows.fed]
    exact fedOf_refused s c why hlen h
  · rw [← shows.leftover]
    unfold Observation.leftover observe
    rw [exit]


end Test.Dogfood.Scenario.QueueWorkers.Accounting
