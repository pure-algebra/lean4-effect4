import Test.Dogfood.Scenario.QueueWorkers
import Effect4.Laws.Library.Queue.Invariant
import Effect4.Laws.Library.Queue.Steps
import ProofGraph.Axioms
import ProofGraph.GoalTag

/-!
# The queue-run probe: the three Queue goals of `crew`, modulo their planned parts

Packet `docs/research/2026-10-10-goals-packet/queue-run/README.md`. The family's goals stand in
`Test/Dogfood/Scenario/QueueWorkers.lean`: `held_within_fed`, `fed_accounted` and `queue_settled`.
This file restates each goal's proposition (`HeldWithinFed`, `FedAccounted`, `QueueSettled`) and
proves it modulo planned goals. It edits no file of the tree.

* **Section 1, the frame.** A run invariant that every row the tape reads keeps holds at the end of
  a funded script (`RowKeeps`, `play_keeps`, `scenario_keeps`). A script of host acts plays host
  rows only (`hostAct_scriptRows`). General: any program, any invariant. Proved.
* **Section 2, the ledger.** What the invariant knows of a crew run, as data (`Ledger`), what the
  run shows of it (`Ledger.Shows`), and its conservation of jobs (`Ledger.Conserved`). The three
  readings of the observation follow from them (`heldWithin_of_ledger`, `accounted_of_ledger`,
  `settled_of_ledger`). Proved.
* **Section 3, the planned parts.** The crew's simulation, as the obligations of an invariant:
  its start, its step over every row the tape reads, and its readings (`CrewSimulation`,
  `CrewHostSimulation`). Planned goals.
* **Section 4, the goals.** Each goal's proposition from the frame, the ledger and the planned
  parts.

Placement of every declaration is in the packet's README, section by section.
-/

set_option autoImplicit false

namespace QueueRunPacket

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase)
open Effect4.Api.Runner (Command)
open Test.Dogfood.Scenario (Move)

/-! ## 1. The frame -/

/-- Whether the tape reads one row at a run: the row ends at no frontier, and its decision, if
any, is taken at a live machine with enough command fuel. It is `tapeFrom`'s own test
(`src/Effect4/Run/Tape.lean`). -/
def rowReads (s : Run) (c : Command) : Bool :=
  !((Api.Runner.result s.runner c).phase == Phase.frontier) &&
    (Run.decisionOf s c (Api.Runner.result s.runner c).phase).all (Run.readsOn s)

/-- **A run invariant kept by every allowed row that the tape reads.** -/
def RowKeeps (allowed : Command → Prop) (I : Run → Prop) : Prop :=
  ∀ s c, allowed c → rowReads s c = true → I s → I (s.step c)

/-- A tape that reads every row reads the first one, and the rest from the run after it. -/
theorem tapeFrom_read_cons (s : Run) (c : Command) (rest : List Command)
    (h : (Run.tapeFrom s (c :: rest)).2 = []) :
    rowReads s c = true ∧ (Run.tapeFrom (s.step c) rest).2 = [] := by
  cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
  | true =>
    rw [Run.tapeFrom_frontier s c rest hfront] at h
    exact absurd h (List.cons_ne_nil c rest)
  | false =>
    cases hdec : Run.decisionOf s c (Api.Runner.result s.runner c).phase with
    | none =>
      rw [Run.tapeFrom_skip s c rest hfront hdec] at h
      refine ⟨?_, h⟩
      unfold rowReads
      rw [hfront, hdec]
      rfl
    | some d =>
      cases hreads : Run.readsOn s d with
      | false =>
        rw [Run.tapeFrom_stop s c rest d hfront hdec hreads] at h
        exact absurd h (List.cons_ne_nil c rest)
      | true =>
        rw [Run.tapeFrom_take s c rest d hfront hdec hreads] at h
        refine ⟨?_, h⟩
        unfold rowReads
        rw [hfront, hdec]
        exact hreads

/-- **Rows that the tape reads to the end keep a kept invariant.** -/
theorem play_keeps {allowed : Command → Prop} {I : Run → Prop} (keeps : RowKeeps allowed I) :
    ∀ (rows : List Command) (s : Run), (∀ c ∈ rows, allowed c) →
      (Run.tapeFrom s rows).2 = [] → I s → I (s.play rows)
  | [], s, _, _, h => by
    rw [Run.play_nil]
    exact h
  | c :: rest, s, hall, hread, h => by
    obtain ⟨hc, hrest⟩ := tapeFrom_read_cons s c rest hread
    rw [Run.play_cons]
    exact play_keeps keeps rest (s.step c) (fun c' hc' => hall c' (List.mem_cons_of_mem c hc'))
      hrest (keeps s c (hall c List.mem_cons_self) hc h)

/-- The rows a script plays from a run, move by move. -/
def scriptRows : Run → List Move → List Command
  | _, [] => []
  | s, m :: ms => m.rows s ++ scriptRows (Test.Dogfood.Scenario.step s m) ms

/-- A script's run is its rows' run. -/
theorem play_scriptRows : ∀ (s : Run) (moves : List Move),
    Test.Dogfood.Scenario.play s moves = s.play (scriptRows s moves)
  | s, [] => (Run.play_nil s).symm
  | s, m :: ms => by
    show Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.step s m) ms = _
    rw [play_scriptRows (Test.Dogfood.Scenario.step s m) ms, scriptRows, Run.play_append]
    rfl

/-- Playing rows appends them to the journal. -/
theorem journal_play : ∀ (s : Run) (rows : List Command), (s.play rows).journal = s.journal ++ rows
  | s, [] => by rw [Run.play_nil, List.append_nil]
  | s, c :: rest => by
    rw [Run.play_cons, journal_play (s.step c) rest, Run.step_journal, List.append_assoc]
    rfl

open Test.Dogfood.Scenario.QueueWorkers in
/-- The fresh open of a script's run is the run that the script started from. -/
theorem openedOf_play (fuel : Nat) (b : Api.Built) (moves : List Move) :
    Run.openedOf (Test.Dogfood.Scenario.play (openedAt fuel b) moves) = openedAt fuel b := by
  obtain ⟨hb, hi, hf, hp⟩ := Test.Dogfood.Scenario.play_opened (openedAt fuel b) moves
  unfold Run.openedOf
  rw [hb, hi, hf, hp]
  rfl

open Test.Dogfood.Scenario.QueueWorkers in
/-- A funded script's rows are read to the end from the run it started from. -/
theorem funded_rows (fuel : Nat) (b : Api.Built) (moves : List Move)
    (h : Run.funded (Test.Dogfood.Scenario.play (openedAt fuel b) moves) = true) :
    (Run.tapeFrom (openedAt fuel b) (scriptRows (openedAt fuel b) moves)).2 = [] := by
  unfold Run.funded at h
  rw [openedOf_play, play_scriptRows, journal_play] at h
  exact List.isEmpty_iff.mp h

open Test.Dogfood.Scenario.QueueWorkers in
/-- **The frame of a scenario goal.** An invariant that holds at the opened run, and that every
allowed row the tape reads keeps, holds at the end of every funded script whose rows are
allowed. -/
theorem scenario_keeps {allowed : Command → Prop} {I : Run → Prop} (keeps : RowKeeps allowed I)
    (fuel : Nat) (b : Api.Built) (moves : List Move)
    (rowsAllowed : ∀ c ∈ scriptRows (openedAt fuel b) moves, allowed c)
    (start : I (openedAt fuel b))
    (h : Run.funded (Test.Dogfood.Scenario.play (openedAt fuel b) moves) = true) :
    I (Test.Dogfood.Scenario.play (openedAt fuel b) moves) := by
  rw [play_scriptRows]
  exact play_keeps keeps _ _ rowsAllowed (funded_rows fuel b moves h) start

/-! ### The frame of a goal with no budget premise

A goal that does not assume `funded` reads its invariant after every row, cut or not. The frame
is the same induction with no reads premise. A frame of this kind gives the other. -/

/-- **A run invariant kept by every allowed row**, read or not. -/
def RowKeepsAll (allowed : Command → Prop) (I : Run → Prop) : Prop :=
  ∀ s c, allowed c → I s → I (s.step c)

/-- An invariant kept by every row is kept by every row that the tape reads. -/
theorem RowKeepsAll.reads {allowed : Command → Prop} {I : Run → Prop}
    (h : RowKeepsAll allowed I) : RowKeeps allowed I :=
  fun s c ha _ hi => h s c ha hi

/-- **Rows keep an invariant that every allowed row keeps.** -/
theorem play_keepsAll {allowed : Command → Prop} {I : Run → Prop} (keeps : RowKeepsAll allowed I) :
    ∀ (rows : List Command) (s : Run), (∀ c ∈ rows, allowed c) → I s → I (s.play rows)
  | [], s, _, h => by
    rw [Run.play_nil]
    exact h
  | c :: rest, s, hall, h => by
    rw [Run.play_cons]
    exact play_keepsAll keeps rest (s.step c) (fun c' hc' => hall c' (List.mem_cons_of_mem c hc'))
      (keeps s c (hall c List.mem_cons_self) h)

/-- **The frame of a scenario goal with no budget premise.** -/
theorem scenario_keepsAll {allowed : Command → Prop} {I : Run → Prop}
    (keeps : RowKeepsAll allowed I) (start : Run) (moves : List Move)
    (rowsAllowed : ∀ c ∈ scriptRows start moves, allowed c) (h : I start) :
    I (Test.Dogfood.Scenario.play start moves) := by
  rw [play_scriptRows]
  exact play_keepsAll keeps _ _ rowsAllowed h

/-! ### Host rows -/

/-- The rows that a host act plays: a held call, a reply receipt of a completion, a reply
application, the root's start, a flush, a clock step and an interruption with no interruptor. -/
def HostRow : Command → Prop
  | .bind _ _ => True
  | .submit reply => ∃ e, reply.completion = .ofExit e
  | .apply _ => True
  | .control (.evaluate fiber) => fiber = Api.root
  | .control .flush => True
  | .control (.advance _) => True
  | .control (.interruptFrom none _ _) => True
  | .control _ => False

open Test.Dogfood.Scenario.QueueWorkers in
/-- A host act plays host rows only. -/
theorem hostAct_rows (s : Run) (m : Move) (h : Move.hostAct m = true) :
    ∀ c ∈ m.rows s, HostRow c := by
  intro c hc
  cases m with
  | control d =>
    rw [List.mem_singleton.mp hc]
    cases d with
    | evaluate fiber => exact beq_iff_eq.mp h
    | flush => trivial
    | advance _ => trivial
    | interruptFrom who annotations target =>
      cases who with
      | none => trivial
      | some _ => exact absurd h Bool.false_ne_true
    | fire _ => exact absurd h Bool.false_ne_true
    | yieldVerdict _ _ => exact absurd h Bool.false_ne_true
    | answerAsync _ _ _ => exact absurd h Bool.false_ne_true
    | installMiddleware => exact absurd h Bool.false_ne_true
  | hold sel =>
    simp only [Move.rows] at hc
    split at hc
    · exact absurd hc List.not_mem_nil
    · split at hc
      · exact absurd hc List.not_mem_nil
      · rw [List.mem_singleton.mp hc]
        trivial
  | receive sel completion =>
    cases completion with
    | ofExit e =>
      simp only [Move.rows] at hc
      split at hc
      · exact absurd hc List.not_mem_nil
      · split at hc
        · rw [List.mem_singleton.mp hc]
          exact ⟨e, rfl⟩
        · unfold Rows.receive at hc
          split at hc
          · exact absurd hc List.not_mem_nil
          · rcases List.mem_cons.mp hc with rfl | hc
            · trivial
            · rw [List.mem_singleton.mp hc]
              exact ⟨e, rfl⟩
    | ofRefGet _ => exact absurd h Bool.false_ne_true
  | apply sel =>
    simp only [Move.rows] at hc
    split at hc
    · exact absurd hc List.not_mem_nil
    · rw [List.mem_singleton.mp hc]
      trivial
  | row _ => exact absurd h Bool.false_ne_true

open Test.Dogfood.Scenario.QueueWorkers in
/-- A script of host acts plays host rows only. -/
theorem hostAct_scriptRows : ∀ (s : Run) (moves : List Move), moves.all Move.hostAct = true →
    ∀ c ∈ scriptRows s moves, HostRow c
  | _, [], _, c, hc => absurd hc List.not_mem_nil
  | s, m :: ms, h, c, hc => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_append.mp hc with here | later
    · exact hostAct_rows s m h.1 c here
    · exact hostAct_scriptRows (Test.Dogfood.Scenario.step s m) ms h.2 c later

/-! ## 2. The ledger -/

open Test.Dogfood.Scenario.QueueWorkers

/-- The jobs that a model state of the Queue holds: the buffered ones, then the pending ones. -/
def stateJobs (q : Queue.Model.State) : List Nat := q.messages ++ q.offers.flatMap (·.rest)

/-- The view of a model state's cell, as the observation reads it (`queueView`): the capacity,
the buffer, each pending offer's flag and jobs, and the count of the waiting takers. -/
def viewOf (q : Queue.Model.State) : QueueView :=
  ⟨q.capacity.getD 0, q.messages.map Val.nat,
    q.offers.map (fun o => (o.batch, o.rest.map Val.nat)), q.takers.length⟩

/-- **What the invariant knows of a crew run**, as data. A job is the number that the host fed
(`Jobs.take` answers `.nat`, and the session admits no other answer). -/
structure Ledger where
  /-- The queue's model run, once the root made the cell. -/
  queue : Option Queue.Model.Run
  /-- The jobs that the host fed, in the order of the reply applications. -/
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
theorem filterMap_gave : ∀ (l : List (Nat × Nat)),
    (l.map (fun e => gave e.1 e.2)).filterMap jobOf = (l.map Prod.fst).map Val.nat
  | [] => rfl
  | e :: rest => by
    rw [List.map_cons, List.filterMap_cons, filterMap_gave rest]
    rfl

/-- The pending jobs of a view, read back. -/
theorem flatMap_offers : ∀ (os : List Queue.Model.Offer),
    (os.map (fun o => (o.batch, o.rest.map Val.nat))).flatMap (·.2) =
      (os.flatMap (·.rest)).map Val.nat
  | [] => rfl
  | o :: rest => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, flatMap_offers rest, List.map_append]

/-- **The held jobs of an observation are the ledger's.** -/
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
    unfold stateJobs
    rw [flatMap_offers, List.map_append]

/-- A conserving ledger's fed jobs are its held ones, then the rest. -/
theorem fed_perm {a : Ledger} (conserved : a.Conserved) :
    (a.fed.map Val.nat).Perm (a.heldJobs.map Val.nat ++ (a.custody ++ a.lost).map Val.nat) := by
  have perm := conserved.map Val.nat
  rw [List.append_assoc, List.map_append] at perm
  exact perm

/-- **No job is held more often than it was fed**, on a ledger that the observation shows and
that conserves. -/
theorem heldWithin_of_ledger {a : Ledger} {o : Observation} (shows : a.Shows o)
    (conserved : a.Conserved) : o.heldWithin = true := by
  unfold Observation.heldWithin
  rw [List.all_eq_true]
  intro job _
  rw [held_of_shows shows, shows.fed, (fed_perm conserved).count_eq, List.count_append]
  exact decide_eq_true (Nat.le_add_right _ _)

/-- **The fed jobs are no more than the held ones, but for the lost ones**, on a ledger with no
custody. -/
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
theorem within_one {s : Queue.Model.State} (one : s.capacity = some 1)
    (within : Queue.Model.within s = true) : s.messages.length ≤ 1 := by
  unfold Queue.Model.within at within
  rw [one] at within
  exact of_decide_eq_true within

/-- **The queue is settled**, read from a view's seven parts. -/
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

/-! ### The model's conservation of jobs, one first operation at a time

The ledger's step reads one of these at each step of the queue's cell. A take that consumes
removes its job, an offer adds its job, a poll that consumes removes its job, a take's withdrawal
keeps every job, and an offer's withdrawal removes the jobs of the withdrawn offer and no other.
Model only: the closed forms of `src/Effect4/Laws/Library/Queue/Steps.lean`. -/

section Conservation

open Queue.Model

/-- The accept pass keeps the jobs: the offers that fit move from pending to buffered. -/
theorem stateJobs_afterAccept (c : Nat) (s : State) : stateJobs (afterAccept c s) = stateJobs s := by
  show s.messages ++ (s.offers.take (fitCount c s)).flatMap (·.rest) ++
      (s.offers.drop (fitCount c s)).flatMap (·.rest) = s.messages ++ s.offers.flatMap (·.rest)
  rw [List.append_assoc, ← List.flatMap_append, List.take_append_drop]

/-- **A take at the bounds one and one consumes its job, or it waits and keeps every job.** -/
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
theorem withdrawTake_jobs (s : State) (id : Nat) :
    stateJobs (withdrawTake s id).1 = stateJobs s := rfl

/-- The jobs of a list of offers, split by a test. -/
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
theorem withdrawOffer_jobs {s : State} (h : FirstProfile s) (id : Nat) :
    (stateJobs s).Perm (stateJobs (withdrawOffer s id).1 ++
      (s.offers.filter (fun o => !(o.id != id))).flatMap (·.rest)) := by
  rw [withdrawOffer_opened h.opened id]
  show (s.messages ++ s.offers.flatMap (·.rest)).Perm
    (s.messages ++ (s.offers.filter (fun o => o.id != id)).flatMap (·.rest) ++
      (s.offers.filter (fun o => !(o.id != id))).flatMap (·.rest))
  rw [List.append_assoc]
  exact (flatMap_split (fun o => o.id != id) s.offers).append_left s.messages

end Conservation

/-! ### Cases of the invariant proved outright

The frame's start, and one row: a refused row. Each shows that the route reads the run as the
planned invariant will. -/

/-- **The root's exit is the machine's**: a frontier reading with no tape keeps the machine.
General: any run. -/
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
theorem opened_exit (fuel : Nat) (b : Api.Built) : (openedAt fuel b).exit = none := by
  rw [exit_eq]
  rfl

/-- The empty ledger. -/
def Ledger.empty : Ledger := ⟨none, [], [], [], [], []⟩

/-- **The ledger at the opened run**: nothing made, nothing fed, nothing held. It is the ledger's
part of the frame's start. -/
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
theorem fedOf_eq (s : Run) :
    fedOf s = (Test.Dogfood.Scenario.rows s).filterMap
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
theorem fedOf_refused (s : Run) (c : Command) (why : Api.HostSession.Refusal)
    (hlen : s.journal.length = s.phases.length)
    (h : (Api.Runner.result s.runner c).phase = .refused why) :
    fedOf (s.step c) = fedOf s := by
  rw [fedOf_eq, fedOf_eq, seenAt_refused s c why hlen h, rows_step s c hlen, h,
    List.filterMap_append]
  have same : appliedValue (Test.Dogfood.Scenario.rows s ++ [(c, .refused why)])
      (Test.Dogfood.Scenario.seenAt s) =
      appliedValue (Test.Dogfood.Scenario.rows s) (Test.Dogfood.Scenario.seenAt s) :=
    funext (appliedValue_refused _ _ c why)
  have none : [(c, Phase.refused why)].filterMap
      (appliedValue (Test.Dogfood.Scenario.rows s) (Test.Dogfood.Scenario.seenAt s)) = [] := by
    cases c <;> rfl
  rw [same, none, List.append_nil]

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

/-! ## 3. The planned parts

Each structure below is the brief's frame for one invariant: it holds at the opened run, every
allowed row that the tape reads keeps it, and each run that holds it shows a ledger. The README
gives the invariant that each planned goal names: the stage table, the stores and the session's
facts, with the lemmas that prove its step. -/

/-- **The crew's invariant over every script**, as its three obligations. -/
structure CrewInvariant (total : Nat) (I : Run → Prop) : Prop where
  start : ∀ fuel b, Effect4.Api.Author.build (crew total) = .ok b → I (openedAt fuel b)
  step : RowKeeps (fun _ => True) I
  ledger : ∀ s, I s → ∃ a : Ledger, a.Shows (observe s) ∧ a.Conserved

/-- **The crew's invariant over host acts**, with what it gives at rest. -/
structure CrewHostInvariant (total : Nat) (I : Run → Prop) : Prop where
  start : ∀ fuel b, Effect4.Api.Author.build (crew total) = .ok b → I (openedAt fuel b)
  step : RowKeeps HostRow I
  rest : ∀ s, I s → Run.atRest s = true →
    ∃ a : Ledger, a.Shows (observe s) ∧ a.Conserved ∧ a.custody = [] ∧
      a.lost.length ≤ (if (observe s).live 3 then 0 else 1) ∧ a.RestQueue (observe s)

/-- **Planned: the crew's invariant over every script exists.** The README's section 3 names it:
the stage table of every fiber (the 36 shapes of the census), the stores and the session's
facts. Concept `translation-simulation`, R10; the general parts are the instances of
`queue-expansion-agrees` and `waiting-request-obligation-preserved` that the README lists. -/
proof_goal crew_invariant (total : Nat) : ∃ I, CrewInvariant total I

/-- **Planned: the crew's invariant over host acts exists.** The README's section 3: the twelve
host shapes, at most one transit per segment, and the queue's model run with its flags.
Concept `reactive-scheduling`, R12; the instances of `wait-registration-no-gap` and of the
delivery clause of `waiting-request-obligation-preserved`. -/
proof_goal crew_host_invariant (total : Nat) : ∃ I, CrewHostInvariant total I

/-! ## 4. The goals, modulo the planned parts -/

/-- `held_within_fed`, modulo `crew_invariant`. -/
theorem held_within_fed_probe : HeldWithinFed := by
  intro total fuel b moves hb hf
  obtain ⟨I, inv⟩ := crew_invariant total
  obtain ⟨a, shows, conserved⟩ := inv.ledger _
    (scenario_keeps inv.step fuel b moves (fun _ _ => trivial) (inv.start fuel b hb) hf)
  exact heldWithin_of_ledger shows conserved

/-- `fed_accounted`, modulo `crew_host_invariant`. -/
theorem fed_accounted_probe : FedAccounted := by
  intro total fuel b moves hb hhost hf hrest
  obtain ⟨I, inv⟩ := crew_host_invariant total
  obtain ⟨a, shows, conserved, custody, lost, _⟩ := inv.rest _
    (scenario_keeps inv.step fuel b moves (hostAct_scriptRows _ moves hhost)
      (inv.start fuel b hb) hf) hrest
  exact accounted_of_ledger shows conserved custody lost

/-- `queue_settled`, modulo `crew_host_invariant`. -/
theorem queue_settled_probe : QueueSettled := by
  intro total fuel b moves hb hhost hf hrest
  obtain ⟨I, inv⟩ := crew_host_invariant total
  obtain ⟨a, shows, _, _, _, rest⟩ := inv.rest _
    (scenario_keeps inv.step fuel b moves (hostAct_scriptRows _ moves hhost)
      (inv.start fuel b hb) hf) hrest
  exact settled_of_ledger shows rest

end QueueRunPacket

/-! ## 5. The audit

`#axiom_audit` walks imported modules, and this file is none. The command below runs the gate's
exact walk (`ProofGraph.reachedAxiomsMany`, `tools/ProofGraph/Axioms.lean`) over every declaration
of this file's namespace, with the planned goals as stops, as `#axiom_audit` does
(`tools/ProofGraph/AxiomAudit.lean`). It reports each declaration that rests on a goal, and it
fails on an axiom outside `[propext, Quot.sound]`. -/

open Lean Elab Command in
/-- `#packet_audit`: the gate's walk over the probe's own declarations. -/
elab "#packet_audit" : command => do
  let env ← getEnv
  let roots := env.constants.map₂.foldl (init := (#[] : Array Name)) fun acc name _ =>
    if (`QueueRunPacket).isPrefixOf name && !name.isInternal then acc.push name else acc
  let roots := roots.qsort (fun a b => a.toString < b.toString)
  let goals := roots.filter (ProofGraph.isGoal env)
  let walked := roots.filter (!ProofGraph.isGoal env ·)
  let (results, _) := ProofGraph.reachedAxiomsMany env walked {} (ProofGraph.isGoal env)
  let trusted : Array Name := #[``propext, ``Quot.sound]
  let mut offenders : Array MessageData := #[]
  let mut modulo : Array MessageData := #[]
  for (name, result) in walked.zip results do
    match result with
    | none => offenders := offenders.push m!"{name}: the walk ran out of its step budget"
    | some reached =>
      let outside := reached.filter fun a => !trusted.contains a && !ProofGraph.isGoal env a
      if !outside.isEmpty then offenders := offenders.push m!"{name} reaches {outside}"
      let rests := reached.filter (ProofGraph.isGoal env)
      if !rests.isEmpty then modulo := modulo.push m!"{name} rests on {rests}"
  if offenders.isEmpty then
    logInfo (m!"#packet_audit: {walked.size} declarations within [propext, Quot.sound]; \
      {goals.size} planned goals: {goals}; {modulo.size} declarations rest on goals:" ++
      indentD (MessageData.joinSep modulo.toList Format.line))
  else
    throwError m!"#packet_audit: {offenders.size} declarations reach axioms outside \
      [propext, Quot.sound]:{indentD (MessageData.joinSep offenders.toList Format.line)}"

#packet_audit
