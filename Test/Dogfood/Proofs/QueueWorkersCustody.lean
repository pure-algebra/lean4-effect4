import Test.Dogfood.Scenario.QueueWorkers.Ledger
import Effect4.Laws.Library.Queue.Execution
import Effect4.Laws.Machine.AnswerFlowViewsRefined

/-!
Concept: translation-simulation R10 and reactive-scheduling R12.
Question: the actual queue crew transfers each job between one request and the queue cell.
Consumer: QueueWorkers.Assertions.jobs_step, followed by rest_step.
Reach: request identities never reset when their owning fiber starts another loop iteration.
The local answer classes retain the exact payload until its assignment or offer spends it.
Limit: the source callbacks and actual native commit producer establish the machine connection.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustody
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.QueueWorkers

/-- A request's payload becomes unusable after that request spends it. -/
inductive Stage
  | fresh
  | waiting
  | holding (job : Nat)
  | spent (job : Nat)
  | abandoned
  deriving DecidableEq

/-- Request identities advance once; another loop iteration uses a fresh identity. -/
inductive Advances : Stage → Stage → Prop
  | refl (stage : Stage) : Advances stage stage
  | fresh (stage : Stage) : Advances .fresh stage
  | receive (job : Nat) : Advances .waiting (.holding job)
  | abandon : Advances .waiting .abandoned
  | spend (job : Nat) : Advances (.holding job) (.spent job)
  | cancel (job : Nat) : Advances (.holding job) .abandoned
  | receive_spent (job : Nat) : Advances .waiting (.spent job)

/-- The request order retains the payload through every intermediate phase. -/
theorem Advances.trans {first middle last : Stage}
    (one : Advances first middle) (two : Advances middle last) : Advances first last := by
  cases one with
  | refl => exact two
  | fresh => exact .fresh _
  | receive job =>
    cases two with
    | refl => exact .receive job
    | spend => exact .receive_spent job
    | cancel => exact .abandon
  | abandon => cases two; exact .abandon
  | spend job => cases two; exact .spend job
  | cancel job => cases two; exact .cancel job
  | receive_spent job => cases two; exact .receive_spent job

/-- A completed request never returns to a usable payload class. -/
theorem Advances.spent {job : Nat} {after : Stage}
    (held : Advances (.spent job) after) : after = .spent job := by
  cases held
  rfl

/-- Intermediate queue-wrapper operations keep an unfinished request usable. -/
def Stage.Pending : Stage → Prop
  | .waiting | .holding _ => True
  | _ => False

/-- A captured job retains its exact payload whenever an intermediate answer is still usable. -/
theorem Advances.holding_pending {job : Nat} {after : Stage}
    (step : Advances (.holding job) after) (pending : after.Pending) : after = .holding job := by
  cases step with
  | refl => rfl
  | spend => exact False.elim pending
  | cancel => exact False.elim pending

/-- The queue model and conserving ledger share one request-phase world. -/
structure World where
  ledger : Accounting.Ledger
  requests : Nat → Stage

/-- Every saved callback permits later request phases without reviving a spent payload. -/
def Future (before after : World) : Prop :=
  ∀ request, Advances (before.requests request) (after.requests request)

/-- The coupled driver uses the same request order as saved answer callbacks. -/
def order : Effect4.Laws.Effects.WorldOrder World where
  le := Future
  refl world := fun request => .refl (world.requests request)
  trans one two := fun request => (one request).trans (two request)

/-- Only one actual operation changes its own request's phase. -/
def setStage (world : World) (request : Nat) (stage : Stage) : World :=
  {world with requests := fun selected => if selected = request then stage else world.requests selected}

/-- An actual single-request transition preserves the shared future relation. -/
theorem setStage_future (world : World) (request : Nat) (stage : Stage)
    (step : Advances (world.requests request) stage) : Future world (setStage world request stage) := by
  intro selected
  by_cases same : selected = request
  · subst selected
    simpa only [setStage, ↓reduceIte] using step
  · simpa only [setStage, if_neg same] using Advances.refl (world.requests selected)

/-- Saved classes distinguish an operation's internal option from its delivered job. -/
inductive Kind
  | ordinary
  | job (request : Nat)
  | pending (request : Nat)
  | takeOption (request : Nat)
  | takeReply (request : Nat)
  | spent (request : Nat)
  deriving DecidableEq

/-- A take's current option contains its own held payload or records an unfinished request. -/
def OptionAt (world : World) (request : Nat) : Val → Prop
  | .none => world.requests request = .waiting
  | .some (.nat job) => world.requests request = .holding job
  | _ => False

/-- Callback inputs read the new world's actual request phase and exact job. -/
def ValueAt (world : World) : Kind → Val → Prop
  | .ordinary, _ => True
  | .job request, .nat job => world.requests request = .holding job
  | .pending request, _ => (world.requests request).Pending
  | .takeOption request, value => OptionAt world request value
  | .takeReply request, .list [value, .list _, .list _] => OptionAt world request value
  | .spent request, _ => ∃ job, world.requests request = .spent job
  | _, _ => False

/-- An intermediate callback's actual new input class retains its earlier captured job. -/
theorem pending_payload_future (before after : World) (request job : Nat)
    (future : Future before after) (held : before.requests request = .holding job)
    (answer : Val) (pending : ValueAt after (.pending request) answer) :
    after.requests request = .holding job := by
  have step := future request
  rw [held] at step
  exact step.holding_pending pending

/-- A stale successful answer cannot spend an already committed request again. -/
theorem spent_no_job (world : World) (request job : Nat)
    (spent : world.requests request = .spent job) (value : Val) :
    ¬ ValueAt world (.job request) value := by
  intro held
  cases value with
  | nat other =>
    change world.requests request = .holding other at held
    rw [spent] at held
    cases held
  | _ => exact held

/-- Retry options cannot serve as unrestricted broad answers.
Consumer: the typed recursive hook instance for the actual waiter loop. -/
theorem takeOption_not_broad (world : World) (request : Nat) :
    ¬ (∀ value, ValueAt world (.takeOption request) value) := by
  intro broad
  exact broad .unit

/-- A spent request cannot restart its loop from an old waiting option. -/
theorem spent_no_wait_option (world : World) (request job : Nat)
    (spent : world.requests request = .spent job) :
    ¬ ValueAt world (.takeOption request) .none := by
  intro waiting
  change world.requests request = .waiting at waiting
  rw [spent] at waiting
  cases waiting

/-- A spent request cannot return a previously delivered payload through its retry cursor. -/
theorem spent_no_return_option (world : World) (request job previous : Nat)
    (spent : world.requests request = .spent job) :
    ¬ ValueAt world (.takeOption request) (.some (.nat previous)) := by
  intro holding
  change world.requests request = .holding previous at holding
  rw [spent] at holding
  cases holding

/-- Removing a present natural-number job is a constructive permutation step. -/
theorem permutation_cons_erase (job : Nat) (values : List Nat) (member : job ∈ values) :
    values.Perm (job :: values.erase job) := by
  induction values with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
    by_cases same : head = job
    · subst head
      rw [List.erase_cons_head]
    · have later : job ∈ tail := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have different : ¬ (head == job) = true := fun equal => same (beq_iff_eq.mp equal)
      rw [List.erase_cons_tail different]
      exact ((ih later).cons head).trans (.swap job head _)

/-- Natural-number job counts determine a permutation using decidable equality alone.
The generic library equivalence uses classical proposition decisions. -/
theorem permutation_of_counts (first second : List Nat)
    (counts : ∀ job, first.count job = second.count job) : first.Perm second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => exact .nil
    | cons job rest =>
      have impossible := counts job
      simp only [List.count_nil, List.count_cons_self] at impossible
      exact False.elim (by omega)
  | cons job rest ih =>
    have positive : 0 < second.count job := by
      rw [← counts job, List.count_cons_self]
      omega
    have member := List.count_pos_iff.mp positive
    refine ((ih (second.erase job) ?_).cons job).trans (permutation_cons_erase job second member).symm
    intro selected
    have equal := counts selected
    rw [(permutation_cons_erase job second member).count_eq] at equal
    by_cases same : selected = job
    · subst selected
      simp only [List.count_cons_self] at equal
      omega
    · simpa only [List.count_cons_of_ne (Ne.symm same)] using equal

/-- A successful take transfers its exact job into unfinished worker custody. -/
def takeLedger (ledger : Accounting.Ledger) (run : Queue.Model.Run) (request : Nat) : Accounting.Ledger :=
  {ledger with
    queue := some (Queue.Model.step .none run (.take request 1 1))
    custody := match (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1 with
      | .got [job] => job :: ledger.custody
      | _ => ledger.custody}

/-- The take commit changes its own request class together with the conserving ledger. -/
def takeWorld (world : World) (run : Queue.Model.Run) (request token : Nat) : World :=
  let next := {world with ledger := takeLedger world.ledger run request}
  match (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1 with
  | .got [job] => setStage next token (.holding job)
  | _ => next

/-- Actual model take conservation includes the job removed before its worker writes assignment. -/
theorem takeLedger_conserved (ledger : Accounting.Ledger) (run : Queue.Model.Run) (request : Nat)
    (queue : ledger.queue = some run) (profile : Queue.Model.FirstProfile run.s)
    (conserved : ledger.Conserved) : (takeLedger ledger run request).Conserved := by
  apply permutation_of_counts
  intro job
  have counts := conserved.count_eq job
  change ledger.fed.count job = _ at counts
  simp only [Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, Accounting.stateJobs, queue,
    List.count_append] at counts
  change ledger.fed.count job = _
  simp only [takeLedger, Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, Accounting.stateJobs,
    Queue.Model.step, Queue.Model.bump, List.count_append]
  rcases Queue.Model.take_jobs profile request with obtained | waiting
  · obtain ⟨taken, answer, jobs⟩ := obtained
    rw [jobs, List.count_cons] at counts
    rw [answer]
    simp only [List.count_cons]
    omega
  · rw [waiting.1, waiting.2]
    exact counts

/-- A real take commit advances the matching request without changing any other token. -/
theorem takeWorld_future (world : World) (run : Queue.Model.Run) (request token : Nat)
    (profile : Queue.Model.FirstProfile run.s) (waiting : world.requests token = .waiting) :
    Future world (takeWorld world run request token) := by
  rcases Queue.Model.take_jobs profile request with obtained | idle
  · obtain ⟨job, answer, _⟩ := obtained
    simp only [takeWorld, answer]
    intro selected
    by_cases same : selected = token
    · subst selected
      simpa only [setStage, ↓reduceIte, waiting] using Advances.receive job
    · simpa only [setStage, if_neg same] using Advances.refl (world.requests selected)
  · simp only [takeWorld, idle.1]
    exact order.refl world

/-- The exact encoded take tuple receives the same request's new payload class. -/
theorem take_reply (world : World) (run : Queue.Model.Run) (request token : Nat)
    (profile : Queue.Model.FirstProfile run.s) (waiting : world.requests token = .waiting)
    (reply : Val) (encoded : Queue.Model.takeReplyVal Val.nat
      (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1 = some reply)
    (entered woken : List Val) :
    ValueAt (takeWorld world run request token) (.takeReply token)
      (.list [reply, .list entered, .list woken]) := by
  rcases Queue.Model.take_jobs profile request with obtained | idle
  · obtain ⟨job, answer, _⟩ := obtained
    rw [answer] at encoded
    have value : reply = .some (.nat job) := (Option.some.inj encoded).symm
    subst reply
    simp only [takeWorld, answer, ValueAt, OptionAt, setStage, ↓reduceIte]
  · rw [idle.1] at encoded
    have value : reply = .none := (Option.some.inj encoded).symm
    subst reply
    simpa only [takeWorld, idle.1, ValueAt, OptionAt] using waiting

/-- Both take outcomes retain the same committed conserving ledger. -/
theorem takeWorld_ledger (world : World) (run : Queue.Model.Run) (request token : Nat) :
    (takeWorld world run request token).ledger = takeLedger world.ledger run request := by
  unfold takeWorld
  split <;> rfl

open Effect4.Modules Effect4.Program.Authoring

/-- The actual take primitive and its new custody answer use one world witness.
The source capture premises identify the request and hint; no machine conclusion is assumed. -/
theorem take_sync (world : World) (run : Queue.Model.Run) (request token : Nat)
    (queue : world.ledger.queue = some run) (conserved : world.ledger.Conserved)
    (waiting : world.requests token = .waiting) (profile : Queue.Model.FirstProfile run.s)
    (requested : Queue.Model.Requested run.s (.take request 1 1))
    (table : Table) (injective : table.Injective) (hint : DeferredKey)
    {idSrc hintSrc : TermSrc} {env : Env} {path : List Nat} {captured : List Val}
    (depth : captured.length = env.names.length)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (Val.promise (table.handle request)))
    (readsHint : Captured hintSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (Val.promise hint))
    (stores : Stores) (cell : RefKey)
    (held : refPeek stores.refs cell = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ term reply entered woken,
      Queue.takeStep .nat idSrc hintSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok term ∧
      Queue.Model.Notified run.s (Queue.Model.take run.s ⟨request, 1, 1⟩).1
        (Queue.Model.take run.s ⟨request, 1, 1⟩).2.2 entered woken ∧
      syncOpStep (.refModify cell term captured) stores =
        some ({stores with refs := (refPoke stores.refs cell
          (Queue.Model.cellVal
            (table.afterTake request hint (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1)
            Val.nat (Queue.Model.take run.s ⟨request, 1, 1⟩).1))},
          Val.tuple [reply, .list (entered.map (Queue.Model.offerVal table Val.nat)),
            .list (woken.map (Queue.Model.takerVal
              (table.afterTake request hint (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1)))]) ∧
      Future world (takeWorld world run request token) ∧
      (takeWorld world run request token).ledger.Conserved ∧
      ValueAt (takeWorld world run request token) (.takeReply token)
        (Val.tuple [reply, .list (entered.map (Queue.Model.offerVal table Val.nat)),
          .list (woken.map (Queue.Model.takerVal
            (table.afterTake request hint (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1)))]) := by
  obtain ⟨reply, entered, woken, encoded, notified, reads⟩ :=
    Queue.Model.takeStep_agrees .nat table Val.nat run.s request hint profile requested injective
      (push_minted_length depth "current" _) readsId readsHint
      (reads_minted_last depth path "current" _)
  obtain ⟨term, tree, stepped⟩ := step_updates held reads
  refine ⟨term, reply, entered, woken, tree, notified, stepped,
    takeWorld_future world run request token profile waiting, ?_, ?_⟩
  · rw [takeWorld_ledger]
    exact takeLedger_conserved world.ledger run request queue profile conserved
  · exact take_reply world run request token profile waiting reply encoded _ _

/-- A fresh offer moves one feeder-held job into the queue's buffered or pending jobs. -/
def offerLedger (ledger : Accounting.Ledger) (run : Queue.Model.Run) (request job : Nat) : Accounting.Ledger :=
  {ledger with
    queue := some (Queue.Model.step .none run (.offer request job))
    custody := ledger.custody.erase job}

/-- A genuinely fresh request cannot hit the model's repeated-offer guard. -/
theorem fresh_offer (run : Queue.Model.Run) (request : Nat)
    (fresh : ∀ offer ∈ run.s.offers, offer.id ≠ request) :
    run.s.offers.any (fun offer => offer.id == request) = false := by
  cases selected : run.s.offers.any (fun offer => offer.id == request) with
  | false => rfl
  | true =>
    obtain ⟨offer, member, same⟩ := List.any_eq_true.mp selected
    exact False.elim (fresh offer member (beq_iff_eq.mp same))

/-- The fresh offer spends one actual custody occurrence and adds that same occurrence to the cell. -/
theorem offerLedger_conserved (ledger : Accounting.Ledger) (run : Queue.Model.Run) (request job : Nat)
    (queue : ledger.queue = some run) (profile : Queue.Model.FirstProfile run.s)
    (fresh : ∀ offer ∈ run.s.offers, offer.id ≠ request)
    (holding : job ∈ ledger.custody) (conserved : ledger.Conserved) :
    (offerLedger ledger run request job).Conserved := by
  apply permutation_of_counts
  intro selected
  have counts := conserved.count_eq selected
  change ledger.fed.count selected = _ at counts
  simp only [Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, Accounting.stateJobs, queue,
    List.count_append] at counts
  change ledger.fed.count selected = _
  simp only [offerLedger, Accounting.Ledger.heldJobs, Accounting.Ledger.cellJobs, Accounting.stateJobs,
    Queue.Model.step, fresh_offer run request fresh, Bool.false_eq_true, ↓reduceIte,
    Queue.Model.bump, Queue.Model.offer_jobs profile, List.count_append]
  have erased := (permutation_cons_erase job ledger.custody holding).count_eq selected
  by_cases same : selected = job
  · subst selected
    simp only [List.count_singleton_self]
    simp only [List.count_cons_self] at erased
    omega
  · simp only [List.count_cons_of_ne (Ne.symm same), List.count_nil, Nat.add_zero]
    simp only [List.count_cons_of_ne (Ne.symm same)] at erased
    omega

/-- The feeder's payload class becomes spent at its actual queue offer commit. -/
def offerWorld (world : World) (run : Queue.Model.Run) (request token job : Nat) : World :=
  setStage {world with ledger := offerLedger world.ledger run request job} token (.spent job)

/-- An offer's request and its feeder credit use separate identities. -/
theorem offerWorld_future (world : World) (run : Queue.Model.Run) (request token job : Nat)
    (holding : world.requests token = .holding job) :
    Future world (offerWorld world run request token job) := by
  intro selected
  by_cases same : selected = token
  · subst selected
    simpa only [offerWorld, setStage, ↓reduceIte, holding] using Advances.spend job
  · simpa only [offerWorld, setStage, if_neg same] using Advances.refl (world.requests selected)

/-- The actual offer primitive spends the captured feeder payload in the same returned world. -/
theorem offer_sync (world : World) (run : Queue.Model.Run) (request token job : Nat)
    (queue : world.ledger.queue = some run) (conserved : world.ledger.Conserved)
    (phase : world.requests token = .holding job) (holding : job ∈ world.ledger.custody)
    (profile : Queue.Model.FirstProfile run.s)
    (requested : Queue.Model.Requested run.s (.offer request job))
    (fresh : ∀ offer ∈ run.s.offers, offer.id ≠ request)
    (table : Table) (hint : DeferredKey)
    {idSrc hintSrc messageSrc : TermSrc} {env : Env} {path : List Nat} {captured : List Val}
    (depth : captured.length = env.names.length)
    (readsId : Reads idSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (Val.promise (table.handle request)))
    (readsHint : Reads hintSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (Val.promise hint))
    (readsMessage : Reads messageSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (.nat job))
    (stores : Stores) (cell : RefKey)
    (held : refPeek stores.refs cell = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ term woken,
      Queue.offerStep .nat idSrc hintSrc messageSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok term ∧
      Queue.Model.Notified run.s (Queue.Model.offer run.s request job).1
        (Queue.Model.offer run.s request job).2.2 [] woken ∧
      syncOpStep (.refModify cell term captured) stores =
        some ({stores with refs := (refPoke stores.refs cell
          (Queue.Model.cellVal
            (table.afterOffer request hint (Queue.Model.offer run.s request job).2.1)
            Val.nat (Queue.Model.offer run.s request job).1))},
          Val.tuple [Queue.Model.offerReplyVal (Queue.Model.offer run.s request job).2.1,
            .list (woken.map (Queue.Model.takerVal
              (table.afterOffer request hint (Queue.Model.offer run.s request job).2.1)))]) ∧
      Future world (offerWorld world run request token job) ∧
      (offerWorld world run request token job).ledger.Conserved ∧
      ValueAt (offerWorld world run request token job) (.spent token)
        (Val.tuple [Queue.Model.offerReplyVal (Queue.Model.offer run.s request job).2.1,
          .list (woken.map (Queue.Model.takerVal
            (table.afterOffer request hint (Queue.Model.offer run.s request job).2.1)))]) := by
  obtain ⟨woken, notified, reads⟩ :=
    Queue.Model.offerStep_agrees .nat table Val.nat run.s request job hint profile requested fresh
      readsId readsHint readsMessage (reads_minted_last depth path "current" _)
  obtain ⟨term, tree, stepped⟩ := step_updates held reads
  refine ⟨term, woken, tree, notified, stepped,
    offerWorld_future world run request token job phase, ?_, ?_⟩
  · exact offerLedger_conserved world.ledger run request job queue profile fresh holding conserved
  · change ∃ selected, (offerWorld world run request token job).requests token = .spent selected
    refine ⟨job, ?_⟩
    simp only [offerWorld, setStage, ↓reduceIte]

end Test.Dogfood.Proofs.QueueWorkersCustody
