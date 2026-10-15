import Test.Dogfood.Proofs.QueueWorkersNotificationFamily
import Test.Dogfood.Proofs.QueueWorkersJobBinding
import Test.Dogfood.Proofs.QueueWorkersTakeSites
import Test.Dogfood.Proofs.QueueWorkersWithdrawalSites
import Test.Dogfood.Proofs.QueueWorkersRetrySites
import Test.Dogfood.Proofs.QueueWorkersOfferSites
import Test.Dogfood.Proofs.QueueWorkersOfferTail
import Test.Dogfood.Proofs.QueueWorkersReadonlySource

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the worker's actual assignment continuation.
Current assignment code retains the job class read by its actual successful binder.
Ordinary tails reuse the qualified source family; this annotation adds no source traversal.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersJobGraph
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- A saved retry hook retains its actual source, immutable request key and fixed root slots. -/
structure RetryAt (total : Nat) (world : QueueWorkersCustodyFlow.World) (token worker : Nat) (point : Point) : Prop where
  source : SourceScope.At (Programs.queueProgram total) point
  path : point.path = QueueWorkersRetrySites.path worker
  leading : AnswerSlots.Prefix InitialSlots.bindings point.env
  key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key)

/-- A retry name survives future worlds without assuming its request remains waiting. -/
theorem RetryAt.future {total : Nat} {before after : QueueWorkersCustodyFlow.World} {token worker : Nat} {point : Point}
    (held : RetryAt total before token worker point) (future : Future before after) :
    RetryAt total after token worker point := by
  obtain ⟨key, published, captured⟩ := held.key
  exact ⟨held.source, held.path, held.leading, key, future.1.2 token key published, captured⟩

/-- Refreshing the actual completed-exit view retains the retry's source and literal request key. -/
theorem RetryAt.view {total : Nat} {world : QueueWorkersCustodyFlow.World} {token worker : Nat} {point : Point}
    (held : RetryAt total world token worker point) (view : List (FiberId × ExitV)) :
    RetryAt total world token worker {point with completed := view} :=
  ⟨held.source, held.path, held.leading, held.key⟩

/-- The saved success binder consumes its classified input at the actual future world. -/
inductive CodeAt (total : Nat) (table : RowTable) (owner : FiberId) : QueueWorkersCustodyFlow.World → Kind → NCode → Prop
  | success {world kind value} (good : ValueAt world kind value) :
      CodeAt total table owner world kind (.success value)
  | failure {world kind cause} : CodeAt total table owner world kind (.failure cause)
  | ordinary {world code} (held : QueueWorkersReadonly.Code total code) :
      CodeAt total table owner world .ordinary code
  | postOffer {world bindings code}
      (held : QueueWorkersOfferTail.Code total bindings (QueueWorkersOfferSites.path.dropLast ++ [1]) code) :
      CodeAt total table owner world .ordinary code
  | notification {world kind bindings code}
      (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total))
      (flat : ∀ nextWorld value, ValueAt nextWorld kind value ↔ ValueAt nextWorld kind .unit)
      (phase : ValueAt world kind .unit)
      (owned : QueueWorkersNotificationFlow.Code spec bindings code) :
      CodeAt total table owner world kind code
  | assignment {world point term}
      (held : QueueWorkersJobBinding.Capture (Programs.queueProgram total) world owner point)
      (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
      (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
        some (.eff (.perform (.refUpdateWith term) (.var 3)))) :
      CodeAt total table owner world .ordinary (.sync (.op (.refUpdate ⟨3⟩ term point.env)))
  | workerMake {world} : CodeAt total table owner world (.workerKey owner) (.sync (.op .deferredMake))
  | maskGetter {world point}
      (actual : actionAt (Programs.queueProgram total) point = some .getInterruptible) :
      CodeAt total table owner world .maskFlag (.withFiber (.act point))
  | heldGetter {world point token job}
      (actual : actionAt (Programs.queueProgram total) point = some .getInterruptible)
      (selected : Owns world owner token)
      (holding : world.requests.custody.requests token = .holding job)
      (unpublished : world.requests.keys token = none) :
      CodeAt total table owner world (.unpublished owner token job) (.withFiber (.act point))
  | offerMake {world token job}
      (selected : Owns world owner token)
      (holding : world.requests.custody.requests token = .holding job)
      (unpublished : world.requests.keys token = none) :
      CodeAt total table owner world (.offerKey owner job) (.sync (.op .deferredMake))
  | offerHintMake {world token job}
      (selected : Owns world owner token)
      (holding : world.requests.custody.requests token = .holding job) :
      CodeAt total table owner world (.offerHint owner token job) (.sync (.op .deferredMake))
  | hintMake {world token} (selected : Owns world owner token)
      (waiting : world.requests.custody.requests token = .waiting) :
      CodeAt total table owner world (.hintKey owner token) (.sync (.op .deferredMake))
  | take {world point token worker}
      (member : worker ∈ [1, 2])
      (request : QueueWorkersJobBinding.RequestCapture (Programs.queueProgram total) world owner (worker + 8) point)
      (selected : Owns world owner token)
      (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
      (path : point.path = QueueWorkersTakeSites.path worker)
      (hinted : ∃ hint, point.env[worker + 10]? = some (.promise hint)) :
      CodeAt total table owner world (.captured owner token (.takeReply token))
        (.sync (.op (.refModify ⟨0⟩ (QueueWorkersTakeSites.term worker) point.env)))
  | offer {world point token job}
      (source : SourceScope.At (Programs.queueProgram total) point)
      (selected : Owns world owner token)
      (holding : world.requests.custody.requests token = .holding job)
      (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
      (path : point.path = QueueWorkersOfferSites.path)
      (key : ∃ key, world.requests.keys token = some key ∧ point.env[12]? = some (.promise key))
      (hinted : ∃ hint, point.env[13]? = some (.promise hint))
      (payload : point.env[10]? = some (.nat job)) :
      CodeAt total table owner world (.captured owner token (.spent token))
        (.sync (.op (.refModify ⟨0⟩ QueueWorkersOfferSites.term point.env)))
  | withdraw {world point token option exit worker}
      (member : worker ∈ [1, 2])
      (source : SourceScope.At (Programs.queueProgram total) point)
      (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
      (path : point.path = QueueWorkersWithdrawalSites.path worker)
      (key : ∃ key, world.requests.keys token = some key ∧
        point.env[worker + 8]? = some (.promise key))
      (phase : ValueAt world (.restoreSnapshot owner token option exit) .unit) :
      CodeAt total table owner world (.restoreSnapshot owner token option exit)
        (.sync (.op (.refModify ⟨0⟩ (QueueWorkersWithdrawalSites.term worker) point.env)))
  | retry {world token worker point cursor}
      (member : worker ∈ [1, 2])
      (held : RetryAt total world token worker point)
      (typed : ValueAt world (.captured owner token (.takeOption token)) cursor) :
      CodeAt total table owner world (.captured owner token (.takeOption token)) (.whileLoop (.loop point) cursor)
  | awaiting {world token key}
      (selected : Owns world owner token)
      (waiting : world.requests.custody.requests token = .waiting) :
      CodeAt total table owner world (.snapshot owner token .none)
        (.async (.registerAwait key) true (some (.cancelAwait key)))
  | masking {world kind point body flag}
      (action : actionAt (Programs.queueProgram total) point = some (.setInterruptible body flag))
      (first : CodeAt total table owner world kind body) :
      CodeAt total table owner world kind (.withFiber (.act point))
  | protectedWait {world token option body point}
      (first : CodeAt total table owner world (.snapshot owner token option) body)
      (installed : ∀ nextWorld, Future world nextWorld → ∀ view exit,
        (match exit with
          | .success value => ValueAt nextWorld (.snapshot owner token option) value
          | .failure _ => True) →
        CodeAt total table owner nextWorld (.restoreSnapshot owner token option exit)
          (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 (reifyExitVal exit)))) :
      CodeAt total table owner world (.snapshot owner token option) (.onExit body (.fin point) false)
  | restoring {world token option exit body}
      (first : CodeAt total table owner world (.restoreSnapshot owner token option exit) body) :
      CodeAt total table owner world (.snapshot owner token option) (.onSuccess body (.restore exit))
  | merging {world kind exit body}
      (first : CodeAt total table owner world kind body) :
      CodeAt total table owner world kind (.onFailure body (.merge exit))
  | frontier {world kind point} (zero : point.fuel = 0) :
      CodeAt total table owner world kind (Effect4.Program.frontier point)
  | suspended {world kind thunk}
      (next : ∀ view, CodeAt total table owner world kind
        ((interpAt (Programs.queueProgram total) view table).suspendBody thunk)) :
      CodeAt total table owner world kind (.suspend thunk)
  | bound {world input output body name}
      (localInput : LocalKind owner input)
      (first : CodeAt total table owner world input body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
        ValueAt nextWorld input answer → CodeAt total table owner nextWorld output
          ((interpAt (Programs.queueProgram total) view table).contA name answer)) :
      CodeAt total table owner world output (.onSuccess body name)

/-- The concrete assignment binder keeps its job until the actual write consumes it. -/
theorem assignment_body (total : Nat) (table : RowTable) (world : QueueWorkersCustodyFlow.World) (owner : FiberId)
    (point : Point) (term : Term) (rest : NativeEff)
    (held : QueueWorkersJobBinding.Capture (Programs.queueProgram total) world owner point)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.bind (.perform (.refUpdateWith term) (.var 3)) rest))) :
    CodeAt total table owner world .ordinary (resolve (Programs.queueProgram total) point) := by
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply CodeAt.bound (input := .ordinary) True.intro
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        have slot : evalTerm (point.child 0).env (.var 3) = some (.cell ⟨3⟩) := by
          exact leading.read 3 (by decide)
        rw [slot]
        exact .assignment (QueueWorkersJobBinding.child _ _ _ _ _ _ found held) leading
          (Agreement.at_child found 0)
    · intro nextWorld future view answer good
      exact .ordinary (QueueWorkersReadonlySource.assignment_callback total point term rest view table answer found leading)

/-- The worker's actual job answer enters its assignment, with no separate membership premise. -/
theorem worker_callback (total : Nat) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (before rest : NativeEff) (term : Term) (job : Nat) (view : List (FiberId × ExitV))
    (source : SourceScope.At (Programs.queueProgram total) point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.bind before (.bind (.perform (.refUpdateWith term) (.var 3)) rest))))
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (good : ValueAt world (.job owner) (.nat job)) :
    CodeAt total table owner world .ordinary
      ((interpAt (Programs.queueProgram total) view table).contA (.cont point) (.nat job)) := by
  obtain ⟨actual, capture⟩ := QueueWorkersJobBinding.callback
    (Programs.queueProgram total) world owner point before _ job view table found source good
  rw [actual]
  exact assignment_body total table world owner _ term rest capture (leading.append [.nat job])
    (Agreement.at_childWith found 1 (.nat job))

/-- An actual assignment head can only come from the worker's classified job binder. -/
theorem assignment_input (total : Nat) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (kind : Kind)
    (term : Term) (env : List Val)
    (good : CodeAt total table owner world kind (.sync (.op (.refUpdate ⟨3⟩ term env)))) :
    kind = .ordinary ∧ ∃ point, point.env = env ∧
      QueueWorkersJobBinding.Capture (Programs.queueProgram total) world owner point ∧
      AnswerSlots.Prefix InitialSlots.bindings point.env ∧
      Node.at_ (.eff (Programs.queueProgram total)) point.path =
        some (.eff (.perform (.refUpdateWith term) (.var 3))) := by
  cases good with
  | ordinary owned =>
    change (3 ≠ 0 ∧ 3 ≠ 3) at owned
    exact (owned.2 rfl).elim
  | postOffer owned => exact (QueueWorkersOfferTail.no_assignment total _ term env owned).elim
  | notification _spec _flat _phase owned => exact owned.elim
  | assignment held leading found => exact ⟨rfl, _, rfl, held, leading, found⟩

/-- The selected assignment head spends exactly its protected occurrence and returns ordinary unit. -/
theorem assignment_step (total : Nat) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (kind : Kind)
    (term : Term) (env : List Val) (stores : Stores)
    (good : CodeAt total table owner world kind (.sync (.op (.refUpdate ⟨3⟩ term env))))
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (conserved : world.requests.custody.ledger.Conserved)
    (read : refPeek stores.refs ⟨3⟩ = some (.list
      (world.requests.custody.ledger.assigned.map (fun pair => gave pair.1 pair.2)))) :
    ∃ nextWorld after, Future world nextWorld ∧
      syncOpStep (.refUpdate ⟨3⟩ term env) stores = some (after, .unit) ∧
      nextWorld.requests.custody.ledger.Conserved ∧
      QueueWorkersCustody.Credits nextWorld.requests.custody ∧
      CodeAt total table owner nextWorld kind (.success .unit) := by
  obtain ⟨rfl, point, rfl, capture, _leading, found⟩ :=
    assignment_input total table world owner kind term env good
  obtain ⟨worker, _member, job, token, _selected, actual, future, conserving, counted, _spent⟩ :=
    QueueWorkersJobBinding.assignment_native total world owner point term capture found credits conserved stores read
  exact ⟨assigned world token job worker, _, future, actual, conserving, counted, .success trivial⟩

/-- The worker answer class contains only the natural payload of its current held request. -/
theorem job_value (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (value : Val)
    (good : ValueAt world (.job owner) value) :
    ∃ job, value = .nat job ∧ ValueAt world (.job owner) (.nat job) := by
  cases value
  all_goals aesop (add norm simp [ValueAt])

/-- The real worker binder retains a classified take result until its assignment continuation. -/
theorem worker_bound (total : Nat) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (before rest : NativeEff) (term : Term) (body : NCode)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.bind before (.bind (.perform (.refUpdateWith term) (.var 3)) rest))))
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (first : CodeAt total table owner world (.job owner) body) :
    CodeAt total table owner world .ordinary (.onSuccess body (.cont point)) := by
  apply CodeAt.bound (input := .job owner) rfl first
  intro nextWorld future view answer good
  obtain ⟨job, rfl, classified⟩ := job_value nextWorld owner answer good
  exact worker_callback total table nextWorld owner point before rest term job view source found leading classified

/-- An actual worker take head retains its own waiting request and exact source capture. -/
theorem take_input (total : Nat) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (kind : Kind) (term : Term) (env : List Val)
    (good : CodeAt total table owner world kind (.sync (.op (.refModify ⟨0⟩ term env))))
    (takeKind : ∃ token, kind = .captured owner token (.takeReply token)) :
    ∃ worker ∈ [1, 2], ∃ point token, kind = .captured owner token (.takeReply token) ∧
      term = QueueWorkersTakeSites.term worker ∧ point.env = env ∧
      QueueWorkersJobBinding.RequestCapture (Programs.queueProgram total) world owner (worker + 8) point ∧
      Owns world owner token ∧ AnswerSlots.Prefix InitialSlots.bindings point.env ∧
      point.path = QueueWorkersTakeSites.path worker ∧
      (∃ hint, point.env[worker + 10]? = some (.promise hint)) := by
  cases good with
  | ordinary owned => exact owned.elim
  | postOffer => obtain ⟨_, impossible⟩ := takeKind; cases impossible
  | notification _spec _flat _phase owned => exact owned.elim
  | take member request selected leading path hinted => exact ⟨_, member, _, _, rfl, rfl, rfl, request, selected, leading, path, hinted⟩
  | withdraw => obtain ⟨_, impossible⟩ := takeKind; cases impossible
  | offer => obtain ⟨_, impossible⟩ := takeKind; cases impossible

end Test.Dogfood.Proofs.QueueWorkersJobGraph
