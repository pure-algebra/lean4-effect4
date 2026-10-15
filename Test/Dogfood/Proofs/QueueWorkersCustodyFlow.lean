import Test.Dogfood.Proofs.QueueWorkersRequestKeys
import Test.Dogfood.Proofs.QueueWorkersCustodySelections
import Effect4.Laws.Program.CodeClosure.Compile

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.Assertions.jobs_step, through actual request allocation and bind inputs.
Each real fiber selects one logical request; its native key is published by the actual allocator.
A captured request class becomes empty when its owner selects a later request.
The native source graph and coupled history attachment remain separate obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustodyFlow
open Effect4 Effect4.Machine Effect4.Program
open QueueWorkersCustody

/-- Active request selection belongs to the real fiber, including repeated source iterations. -/
structure World where
  requests : QueueWorkersRequestKeys.World
  active : FiberId → Option Nat
  next : Nat

/-- Unallocated logical requests have neither a payload nor a published native key. -/
def Fresh (world : World) : Prop :=
  ∀ token, world.next ≤ token →
    world.requests.custody.requests token = .fresh ∧ world.requests.keys token = none

/-- Captured callbacks retain their request's key while its custody phase advances. -/
def Future (first last : World) : Prop :=
  QueueWorkersRequestKeys.Future first.requests last.requests ∧ first.next ≤ last.next

/-- The actual callback world advances without assuming that a fiber keeps the same request. -/
def order : Effect4.Laws.Effects.WorldOrder World where
  le := Future
  refl _world := ⟨⟨QueueWorkersCustody.order.refl _, fun _ _ held => held⟩, Nat.le_refl _⟩
  trans one two := ⟨⟨fun token => (one.1.1 token).trans (two.1.1 token),
    fun token key held => two.1.2 token key (one.1.2 token key held)⟩,
    Nat.le_trans one.2 two.2⟩

/-- Inner callbacks retain the literal request captured when their key was returned. -/
def Owns (world : World) (owner : FiberId) (token : Nat) : Prop :=
  world.active owner = some token

/-- The outer worker loop starts only before a request or after its payload becomes unusable. -/
def OwnerReady (world : World) (owner : FiberId) : Prop :=
  world.active owner = none ∨ ∃ token, Owns world owner token ∧
    ((∃ job, world.requests.custody.requests token = .spent job) ∨
      world.requests.custody.requests token = .abandoned)

/-- Actual successful inputs distinguish a new key, a take result and the delivered job. -/
inductive Kind
  | ordinary
  | maskFlag
  | newKey (owner : FiberId)
  | hintKey (owner : FiberId) (token : Nat)
  | workerKey (owner : FiberId)
  | offerKey (owner : FiberId) (job : Nat)
  | ownerReady (owner : FiberId)
  | captured (owner : FiberId) (token : Nat) (input : QueueWorkersCustody.Kind)
  | snapshot (owner : FiberId) (token : Nat) (option : Val)
  | restoreSnapshot (owner : FiberId) (token : Nat) (option : Val) (exit : ExitV)
  | job (owner : FiberId)

/-- A captured core input reads the same literal request as its enclosing owner capture. -/
def RequestInput (token : Nat) : QueueWorkersCustody.Kind → Prop
  | .ordinary => True
  | .job request | .pending request | .takeOption request | .takeReply request | .spent request => request = token

/-- Every actual worker binder reads its own owner and its captured literal request. -/
def LocalKind (owner : FiberId) : Kind → Prop
  | .ordinary | .maskFlag => True
  | .newKey actual | .hintKey actual _ | .workerKey actual | .offerKey actual _ |
      .ownerReady actual | .snapshot actual _ _ | .restoreSnapshot actual _ _ _ | .job actual => actual = owner
  | .captured actual token input => actual = owner ∧ RequestInput token input

/-- The outer job binder reads its owner's current request; inner binders retain their literal token. -/
def ValueAt (world : World) : Kind → Val → Prop
  | .ordinary, _ => True
  | .maskFlag, value => ∃ flag, value = Val.savedMask flag
  | .newKey owner, value => ∃ token, Owns world owner token ∧
      QueueWorkersRequestKeys.KeyAt world.requests token value
  | .hintKey owner token, .handle 3 _ => Owns world owner token ∧
      world.requests.custody.requests token = .waiting
  | .workerKey owner, value => ∃ token, Owns world owner token ∧
      QueueWorkersRequestKeys.KeyAt world.requests token value ∧
      world.requests.custody.requests token = .waiting
  | .offerKey owner job, value => ∃ token, Owns world owner token ∧
      QueueWorkersRequestKeys.KeyAt world.requests token value ∧
      world.requests.custody.requests token = .holding job
  | .ownerReady owner, _ => OwnerReady world owner
  | .captured owner token input, value => Owns world owner token ∧
      QueueWorkersCustody.ValueAt world.requests.custody input value
  | .snapshot owner token option, _ => Owns world owner token ∧
      OptionAt world.requests.custody token option
  | .restoreSnapshot owner token option (.success _), _ => Owns world owner token ∧
      OptionAt world.requests.custody token option
  | .restoreSnapshot _ _ _ (.failure _), _ => True
  | .job owner, .nat job => ∃ token, Owns world owner token ∧
      world.requests.custody.requests token = .holding job
  | _, _ => False

/-- A later request cannot consume an old captured callback's successful input. -/
theorem stale_input (world : World) (owner : FiberId) (old current : Nat)
    (different : old ≠ current) (selected : world.active owner = some current)
    (input : QueueWorkersCustody.Kind) (value : Val) :
    ¬ ValueAt world (.captured owner old input) value := by
  intro held
  exact different (Option.some.inj (held.1.symm.trans selected))

/-- Notification results retain the exact option captured before their helper programs start. -/
theorem snapshot_option (world : World) (owner : FiberId) (token : Nat)
    (option answer : Val) (held : ValueAt world (.snapshot owner token option) answer) :
    OptionAt world.requests.custody token option := held.2

/-- Destructuring an actual take reply retains its own option throughout notification work. -/
theorem reply_snapshot (world : World) (owner : FiberId) (token : Nat)
    (option answer : Val) (entered woken : List Val)
    (held : ValueAt world (.captured owner token (.takeReply token))
      (.list [option, .list entered, .list woken])) :
    ValueAt world (.snapshot owner token option) answer := held

/-- A held job prevents the outer loop from allocating another request on that owner. -/
theorem ready_excludes_job (world : World) (owner : FiberId) (answer : Val) (job : Nat)
    (ready : ValueAt world (.ownerReady owner) answer) :
    ¬ ValueAt world (.job owner) (.nat job) := by
  intro held
  obtain ⟨token, selected, holding⟩ := held
  rcases ready with empty | ⟨previous, earlier, finished | abandoned⟩
  · change world.active owner = some token at selected
    rw [empty] at selected
    cases selected
  · have same := Option.some.inj (earlier.symm.trans selected)
    subst previous
    obtain ⟨previousJob, spent⟩ := finished
    rw [holding] at spent
    cases spent
  · have same := Option.some.inj (earlier.symm.trans selected)
    subst previous
    rw [holding] at abandoned
    cases abandoned

/-- A notification captured while waiting cannot restart that wait after a job arrives. -/
theorem waiting_snapshot_spent (world : World) (owner : FiberId) (token job : Nat)
    (holding : world.requests.custody.requests token = .holding job) (answer : Val) :
    ¬ ValueAt world (.snapshot owner token .none) answer := by
  intro held
  have waiting := snapshot_option world owner token .none answer held
  change world.requests.custody.requests token = .waiting at waiting
  rw [holding] at waiting
  cases waiting

/-- Starting an unused request changes no existing held occurrence. -/
theorem waiting_credits (world : QueueWorkersCustody.World) (credits : Credits world)
    (token : Nat) (fresh : world.requests token = .fresh) :
    Credits (setStage world token .waiting) := by
  obtain ⟨claims, unique, counted, phases⟩ := credits
  refine ⟨claims, unique, counted, ?_⟩
  intro selected job
  by_cases same : selected = token
  · subst selected
    constructor
    · intro held
      change (if token = token then Stage.waiting else world.requests token) = .holding job at held
      rw [if_pos rfl] at held
      cases held
    · intro member
      have held := (phases token job).mpr member
      rw [fresh] at held
      cases held
  · simpa only [setStage, if_neg same] using phases selected job

/-- The observed offer-entry push creates one held occurrence before allocating its native key. -/
def issue (world : World) (owner : FiberId) (job : Nat) : World :=
  { requests := {world.requests with custody := (feedWorld (setStage world.requests.custody world.next .waiting) world.next job)}
    active := fun selected => if selected = owner then some world.next else world.active selected
    next := world.next + 1 }

/-- The feeder's actual entry observation funds its own new held request. -/
theorem issue_credit (world : World) (owner : FiberId) (job : Nat)
    (fresh : Fresh world) (credits : Credits world.requests.custody)
    (conserved : world.requests.custody.ledger.Conserved) :
    Future world (issue world owner job) ∧
      (issue world owner job).requests.custody.ledger.Conserved ∧
      Credits (issue world owner job).requests.custody ∧
      ValueAt (issue world owner job) (.job owner) (.nat job) := by
  have unused := (fresh world.next (Nat.le_refl _)).1
  have waiting : (setStage world.requests.custody world.next .waiting).requests world.next = .waiting := if_pos rfl
  have counted := feed_owned (setStage world.requests.custody world.next .waiting)
    (waiting_credits world.requests.custody credits world.next unused) world.next job waiting conserved
  refine ⟨⟨⟨?_, fun _ _ key => key⟩, Nat.le_add_right _ _⟩, counted.1, counted.2,
    world.next, ?_, ?_⟩
  · intro token
    by_cases same : token = world.next
    · subst token
      change Advances (world.requests.custody.requests world.next)
        (if world.next = world.next then Stage.holding job else _)
      rw [if_pos rfl]
      exact unused ▸ Advances.fresh (.holding job)
    · change Advances (world.requests.custody.requests token)
        (if token = world.next then Stage.holding job else
          if token = world.next then Stage.waiting else world.requests.custody.requests token)
      simpa only [if_neg same] using Advances.refl (world.requests.custody.requests token)
  · exact if_pos rfl
  · change (if world.next = world.next then Stage.holding job else _) = .holding job
    exact if_pos rfl

/-- Issuing the observed occurrence leaves every later logical request unused. -/
theorem issue_fresh (world : World) (owner : FiberId) (job : Nat) (fresh : Fresh world) :
    Fresh (issue world owner job) := by
  intro token later
  change world.next + 1 ≤ token at later
  have different : token ≠ world.next := by omega
  have unused := fresh token (by omega)
  constructor
  · change (if token = world.next then Stage.holding job else
      if token = world.next then Stage.waiting else world.requests.custody.requests token) = .fresh
    simpa only [if_neg different] using unused.1
  · exact unused.2

/-- The actual request allocation starts one unused token and publishes its returned native key. -/
def allocate (world : World) (owner : FiberId) (key : DeferredKey) : World :=
  { requests := QueueWorkersRequestKeys.publish
      {world.requests with custody := setStage world.requests.custody world.next .waiting}
      world.next key
    active := fun selected => if selected = owner then some world.next else world.active selected
    next := world.next + 1 }

/-- The feeder publishes a native key on the request already funded by its observed entry. -/
def publishKey (world : World) (token : Nat) (key : DeferredKey) : World :=
  {world with requests := QueueWorkersRequestKeys.publish world.requests token key}

/-- A usable request has already passed the fresh logical frontier. -/
theorem pending_before_next (world : World) (token : Nat) (fresh : Fresh world)
    (pending : (world.requests.custody.requests token).Pending) : token < world.next := by
  by_cases before : token < world.next
  · exact before
  · have unused := (fresh token (by omega)).1
    rw [unused] at pending
    exact pending.elim

/-- Publishing an already allocated request leaves the logical frontier fresh. -/
theorem publish_fresh (world : World) (token : Nat) (key : DeferredKey) (fresh : Fresh world)
    (pending : (world.requests.custody.requests token).Pending) :
    Fresh (publishKey world token key) := by
  have before := pending_before_next world token fresh pending
  intro selected later
  change world.next ≤ selected at later
  have different : selected ≠ token := by omega
  have unused := fresh selected later
  exact ⟨unused.1, (if_neg different).trans unused.2⟩

/-- An actual allocator publishes the existing selected request without creating another job. -/
theorem publish_native (world : World) (owner : FiberId) (token : Nat)
    (state after : Stores) (value : Val) (selected : Owns world owner token)
    (unpublished : world.requests.keys token = none)
    (pending : (world.requests.custody.requests token).Pending)
    (credits : Credits world.requests.custody)
    (bound : QueueWorkersRequestKeys.Bound world.requests state)
    (unique : QueueWorkersRequestKeys.Unique world.requests)
    (ran : syncOpStep .deferredMake state = some (after, value)) :
    let next := publishKey world token ⟨state.deferreds.cells.length⟩
    Future world next ∧ ValueAt next (.newKey owner) value ∧
      Credits next.requests.custody ∧ QueueWorkersRequestKeys.Bound next.requests after ∧
      QueueWorkersRequestKeys.Unique next.requests := by
  have allocated := QueueWorkersRequestKeys.allocated world.requests token state after value
    unpublished pending bound unique ran
  exact ⟨⟨allocated.1, Nat.le_refl _⟩, ⟨token, selected, allocated.2.1⟩,
    credits, allocated.2.2.1, allocated.2.2.2⟩

/-- The offer's allocated key retains its captured job rather than accepting an arbitrary pending request. -/
theorem published_offer_input (world : World) (owner : FiberId) (token job : Nat)
    (key : DeferredKey) (value : Val) (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (published : QueueWorkersRequestKeys.KeyAt (publishKey world token key).requests token value) :
    ValueAt (publishKey world token key) (.offerKey owner job) value :=
  ⟨token, selected, published, holding⟩

/-- Starting one request preserves every other fiber's actual selected request. -/
theorem allocate_other (world : World) (owner other : FiberId) (key : DeferredKey)
    (different : other ≠ owner) : (allocate world owner key).active other = world.active other := by
  exact if_neg different

/-- A real allocator cut returns the same proof world for its key, custody and freshness facts. -/
theorem allocate_native (world : World) (owner : FiberId) (state after : Stores) (value : Val)
    (fresh : Fresh world) (credits : Credits world.requests.custody)
    (bound : QueueWorkersRequestKeys.Bound world.requests state)
    (unique : QueueWorkersRequestKeys.Unique world.requests)
    (ran : syncOpStep .deferredMake state = some (after, value)) :
    let next := allocate world owner ⟨state.deferreds.cells.length⟩
    Future world next ∧ ValueAt next (.newKey owner) value ∧
      Credits next.requests.custody ∧ Fresh next ∧
      QueueWorkersRequestKeys.Bound next.requests after ∧
      QueueWorkersRequestKeys.Unique next.requests := by
  have unused := fresh world.next (Nat.le_refl _)
  let waiting : QueueWorkersRequestKeys.World :=
    {world.requests with custody := setStage world.requests.custody world.next .waiting}
  have phase : (waiting.custody.requests world.next).Pending := by
    change (if world.next = world.next then Stage.waiting else _).Pending
    rw [if_pos rfl]
    trivial
  have allocated := QueueWorkersRequestKeys.allocated waiting world.next state after value
    unused.2 phase bound unique ran
  refine ⟨⟨?_, Nat.le_add_right _ _⟩, ?_, ?_, ?_, allocated.2.2.1, allocated.2.2.2⟩
  · refine ⟨?_, allocated.1.2⟩
    exact QueueWorkersCustody.setStage_future world.requests.custody world.next .waiting
      (unused.1 ▸ Advances.fresh .waiting)
  · refine ⟨world.next, ?_, allocated.2.1⟩
    change (if owner = owner then some world.next else world.active owner) = some world.next
    exact if_pos rfl
  · exact waiting_credits world.requests.custody credits world.next unused.1
  · intro token later
    change world.next + 1 ≤ token at later
    have different : token ≠ world.next := by omega
    have old := fresh token (by omega)
    constructor
    · change (if token = world.next then Stage.waiting else world.requests.custody.requests token) = .fresh
      exact (if_neg different).trans old.1
    · change (if token = world.next then some ⟨state.deferreds.cells.length⟩ else world.requests.keys token) = none
      exact (if_neg different).trans old.2

/-- A freshly allocated worker request starts waiting before its take operation runs. -/
theorem allocate_worker_input (world : World) (owner : FiberId) (key : DeferredKey)
    (value : Val) (held : ValueAt (allocate world owner key) (.newKey owner) value) :
    ValueAt (allocate world owner key) (.workerKey owner) value := by
  obtain ⟨token, selected, published⟩ := held
  have same : token = world.next := by
    have active : (allocate world owner key).active owner = some world.next := if_pos rfl
    exact Option.some.inj (selected.symm.trans active)
  subst token
  refine ⟨world.next, selected, published, ?_⟩
  change (if world.next = world.next then Stage.waiting else _) = .waiting
  exact if_pos rfl

/-- The outer worker binder's actual job class owns an occurrence in the conserving ledger. -/
theorem job_member (world : World) (owner : FiberId) (job : Nat)
    (credits : Credits world.requests.custody) (answer : ValueAt world (.job owner) (.nat job)) :
    job ∈ world.requests.custody.ledger.custody := by
  obtain ⟨token, _, holding⟩ := answer
  exact Credits.member world.requests.custody credits token job holding

/-- Assignment spends the request selected by the actual classified job input. -/
def assigned (world : World) (token job worker : Nat) : World :=
  {world with requests := {world.requests with custody := assignWorld world.requests.custody token job worker}}

/-- The assignment's actual spent answer permits the next outer worker iteration. -/
theorem spent_owner_ready (world : World) (owner : FiberId) (token : Nat) (value : Val)
    (held : ValueAt world (.captured owner token (.spent token)) value) :
    ValueAt world (.ownerReady owner) value := by
  obtain ⟨owns, job, spent⟩ := held
  exact Or.inr ⟨token, owns, Or.inl ⟨job, spent⟩⟩

/-- The actual assignment write consumes its classified answer and returns the matching spent class.
This cut uses no independent job-membership or conclusion-shaped conservation premise. -/
theorem assignment_native (world : World) (owner : FiberId) (job worker : Nat)
    (credits : Credits world.requests.custody) (conserved : world.requests.custody.ledger.Conserved)
    (answer : ValueAt world (.job owner) (.nat job))
    (env : List Val) (index : Nat) (captured : env[index]? = some (.nat job)) (stores : Stores)
    (read : refPeek stores.refs ⟨3⟩ = some (.list
      (world.requests.custody.ledger.assigned.map (fun p =>
        Test.Dogfood.Scenario.QueueWorkers.gave p.1 p.2)))) :
    ∃ token, Owns world owner token ∧
      syncOpStep (.refUpdate ⟨3⟩ (assignmentTerm env.length index worker) env) stores =
        some ({stores with refs := refPoke stores.refs ⟨3⟩ (.list
          ((assigned world token job worker).requests.custody.ledger.assigned.map (fun p =>
            Test.Dogfood.Scenario.QueueWorkers.gave p.1 p.2)))}, .unit) ∧
      Future world (assigned world token job worker) ∧
      (assigned world token job worker).requests.custody.ledger.Conserved ∧
      Credits (assigned world token job worker).requests.custody ∧
      ValueAt (assigned world token job worker) (.captured owner token (.spent token)) .unit := by
  obtain ⟨token, owns, holding⟩ := answer
  have member := Credits.member world.requests.custody credits token job holding
  obtain ⟨native, future, conserving, spent⟩ := assignment_commit world.requests.custody token job worker
    holding member conserved env index captured stores read
  have counted := assignment_owned world.requests.custody credits token job worker holding conserved
  exact ⟨token, owns, native, ⟨⟨future, fun _ _ old => old⟩, Nat.le_refl _⟩,
    conserving, counted.2, owns, spent⟩

/-- The actual option-unwrapping source returns its own request's held job to the outer worker binder. -/
theorem unwrap_job (root : NativeEff) (point : Point) (fuel : Nat)
    (scrutinee : Term) (fallback : NativeEff) (world : World) (owner : FiberId) (token job : Nat)
    (available : point.fuel = fuel + 2)
    (found : Node.at_ (.eff root) point.path = some (.eff
      (.select scrutinee .option fallback (.succeed (.var point.env.length)))))
    (selected : evalTerm point.env scrutinee = some (.some (.nat job)))
    (input : ValueAt world (.captured owner token (.takeOption token)) (.some (.nat job))) :
    suspendBodyAt root (.body point) = .success (.nat job) ∧
      ValueAt world (.job owner) (.nat job) := by
  exact ⟨select_payload root point fuel scrutinee fallback job available found selected,
    token, input.1, input.2⟩

/-- A spent assignment cannot be replayed using the same owner's old successful job input. -/
theorem assigned_no_job (world : World) (owner : FiberId) (token job worker : Nat)
    (owns : Owns world owner token) (previous : Val) :
    ¬ ValueAt (assigned world token job worker) (.job owner) previous := by
  intro input
  cases previous with
  | nat value =>
    obtain ⟨other, selected, phase⟩ := input
    have same : other = token := Option.some.inj (selected.symm.trans owns)
    subst other
    change (if token = token then Stage.spent job else world.requests.custody.requests token) = .holding value at phase
    rw [if_pos rfl] at phase
    cases phase
  | _ => exact input

end Test.Dogfood.Proofs.QueueWorkersCustodyFlow
