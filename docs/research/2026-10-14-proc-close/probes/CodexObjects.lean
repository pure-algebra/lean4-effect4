import Effect4.Laws.Library.Queue.Steps
import Effect4.Laws.Library.Semaphore.Steps
import Effect4.Laws.Machine.Scheduling
import Effect4.Library.Waiting
import Effect4.Program.Authoring.Claims

/-! Review controls for D3 / queue-expansion-agrees / translation-simulation R10, R12.
Consumers: the proposed generic wrapper law and Queue adapter (Q5-Q7/Q10).
This file checks interfaces and sequential agreement, not a wrapper or progress theorem. -/
set_option autoImplicit false
namespace Effect4.Probes.CodexObjects
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

inductive TransitionKind | attempt | signal | withdrawal

/-- Inputs retain request identities; outputs retain replies and notifications.
The state must include pending requests and commitments. -/
structure ObjectSpec where
  State : Type
  Input : TransitionKind → Type
  Output : TransitionKind → Type
  pre : (k : TransitionKind) → State → Input k → Prop
  step : (k : TransitionKind) → State → Input k → State → Output k → Prop

/-- Relational encoding accommodates the Queue's table and Notified witnesses.
This interface alone supplies no invariant preservation, delivery or progress. -/
structure StepsAgree (O : ObjectSpec) (Concrete : Type)
    (Enc : O.State → Concrete → Prop)
    (exec : (k : TransitionKind) → Concrete → O.Input k → Concrete → O.Output k → Prop) : Prop where
  agree : ∀ k s c i, Enc s c → O.pre k s i →
    ∀ c' o, exec k c i c' o → ∃ s', O.step k s i s' o ∧ Enc s' c'

/-- The hard Queue attempt adapter, retaining every inherited premise.
Placement: review control for queue-expansion-agrees/R10; consumer D3.
Notified relates abstract signals to the two concrete lists. This proves no delivery. -/
theorem queue_take_adapter
    (A : Ty) (tb : Table) (msg : Nat → Val) (s : Queue.Model.State)
    (id : Nat) (hint : DeferredKey)
    (profile : Queue.Model.FirstProfile s)
    (requested : Queue.Model.Requested s (.take id 1 1)) (injective : tb.Injective)
    {idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (lengths : vals.length = env.names.length)
    (identity : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (hintRead : Captured hintSrc env path vals (Val.promise hint))
    (cell : Reads cellSrc env path vals (Queue.Model.cellVal tb msg s)) :
    ∃ reply entered woken,
      Queue.Model.takeReplyVal msg (Queue.Model.take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Queue.Model.Notified s (Queue.Model.take s ⟨id, 1, 1⟩).1
        (Queue.Model.take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      Reads (Queue.takeStep A idSrc hintSrc cellSrc) env path vals
        (Val.tuple [Val.tuple [reply,
          Val.list (entered.map (Queue.Model.offerVal tb msg)),
          Val.list (woken.map (Queue.Model.takerVal
            (tb.afterTake id hint (Queue.Model.take s ⟨id, 1, 1⟩).2.1)))],
          Queue.Model.cellVal (tb.afterTake id hint (Queue.Model.take s ⟨id, 1, 1⟩).2.1)
            msg (Queue.Model.take s ⟨id, 1, 1⟩).1]) :=
  Queue.Model.queue_steps_agree.take A tb msg s id hint profile requested injective
    lengths identity hintRead cell

/-- Forward sequential interface: an encoded cell and readable arguments produce
an actual term evaluation related to the model step. No invariant preservation is smuggled in.
Signal and withdrawal agreement remain separate projections, not implied by this one. -/
structure AtomicStepsAgree (O : ObjectSpec) (k : TransitionKind) (Concrete : Type)
    (Enc : O.State → Concrete → Prop)
    (Args : O.State → Concrete → O.Input k → Prop)
    (Exec : O.State → Concrete → O.Input k → O.State → O.Output k → Prop) : Prop where
  run : ∀ s c i, Enc s c → O.pre k s i → Args s c i →
    ∃ s' o, O.step k s i s' o ∧ Exec s c i s' o

structure QueueState where
  table : Table
  messages : Nat → Val
  model : Queue.Model.State
structure QueueInput where
  ty : Ty
  id : Nat
  hint : DeferredKey
structure QueueScope where
  idSrc : TermSrc
  hintSrc : TermSrc
  cellSrc : TermSrc
  env : Env
  path : List Nat
  vals : List Val
structure QueueOutput where
  reply : Val
  entered : List Queue.Model.Offer
  woken : List Queue.Model.Taker

def afterTake (s : QueueState) (i : QueueInput) : QueueState :=
  { s with table := s.table.afterTake i.id i.hint (Queue.Model.take s.model ⟨i.id, 1, 1⟩).2.1
           model := (Queue.Model.take s.model ⟨i.id, 1, 1⟩).1 }

/-- A take-arm projection of the three-transition object. The two other model relations
are explicit parameters awaiting protocol design; the adapter below assumes NO agreement
for them. This is not advertised as a full Queue or wrapper instance. -/
def queueTakeObject
    (signal withdrawal : QueueState → QueueInput → QueueState → QueueOutput → Prop) : ObjectSpec where
  State := QueueState
  Input := fun _ => QueueInput
  Output := fun _ => QueueOutput
  pre := fun _ s i => Queue.Model.FirstProfile s.model ∧
    Queue.Model.Requested s.model (.take i.id 1 1) ∧ s.table.Injective
  step := fun k s i s' o => match k with
    | .attempt => s' = afterTake s i ∧
        Queue.Model.takeReplyVal s.messages (Queue.Model.take s.model ⟨i.id, 1, 1⟩).2.1 = some o.reply ∧
        Queue.Model.Notified s.model s'.model
          (Queue.Model.take s.model ⟨i.id, 1, 1⟩).2.2 o.entered o.woken
    | .signal => signal s i s' o
    | .withdrawal => withdrawal s i s' o

def queueEncoded (s : QueueState) (c : QueueScope) : Prop :=
  Reads c.cellSrc c.env c.path c.vals (Queue.Model.cellVal s.table s.messages s.model)
def queueArguments (s : QueueState) (c : QueueScope) (i : QueueInput) : Prop :=
  c.vals.length = c.env.names.length ∧
  Captured c.idSrc c.env c.path c.vals (Val.promise (s.table.handle i.id)) ∧
  Captured c.hintSrc c.env c.path c.vals (Val.promise i.hint)
def queueExec (s : QueueState) (c : QueueScope) (i : QueueInput)
    (s' : QueueState) (o : QueueOutput) : Prop :=
  Reads (Queue.takeStep i.ty c.idSrc c.hintSrc c.cellSrc) c.env c.path c.vals
    (Val.tuple [Val.tuple [o.reply,
      Val.list (o.entered.map (Queue.Model.offerVal s.table s.messages)),
      Val.list (o.woken.map (Queue.Model.takerVal s'.table))],
      Queue.Model.cellVal s'.table s'.messages s'.model])

/-- A genuine inhabitant of the generic sequential agreement interface, not an alias.
Placement: review control for queue-expansion-agrees/R10; consumer D3's adapter.
The existential output retains Notified and the afterTake table, with no delivery premise. -/
theorem queue_atomic_steps_agree
    (signal withdrawal : QueueState → QueueInput → QueueState → QueueOutput → Prop) :
    AtomicStepsAgree (queueTakeObject signal withdrawal) .attempt QueueScope
      queueEncoded queueArguments queueExec where
  run := by
    intro s c i cell pre args
    obtain ⟨reply, entered, woken, answer, notified, reads⟩ :=
      queue_take_adapter i.ty s.table s.messages s.model i.id i.hint
        pre.1 pre.2.1 pre.2.2 args.1 args.2.1 args.2.2 cell
    exact ⟨afterTake s i, ⟨reply, entered, woken⟩, ⟨rfl, answer, notified⟩, reads⟩

-- The other five sequential projections remain unchanged. No projection proves signal delivery.
#check Queue.Model.queue_steps_agree.offer
#check Queue.Model.queue_steps_agree.poll
#check Queue.Model.queue_steps_agree.size
#check Queue.Model.queue_steps_agree.withdrawTake
#check Queue.Model.queue_steps_agree.withdrawOffer

private def emptyQ : Queue.Model.State := { capacity := some 1 }
private def waitingQ := Queue.Model.take emptyQ ⟨1, 1, 1⟩
private def signalledQ := Queue.Model.offer waitingQ.1 2 42
#guard waitingQ.2.1 == .wait
#guard signalledQ.1.messages == [42]
#guard signalledQ.1.takers == [⟨1, 1, 1⟩]
#guard signalledQ.2.2 == [⟨1, .again⟩]
#guard (Queue.Model.take signalledQ.1 ⟨3, 1, 1⟩).2.1 == .wait
#guard (Queue.Model.take signalledQ.1 ⟨1, 1, 1⟩).2.1 == .got [42]
private def sem0 := Semaphore.Model.initial 1
private def sem1 := (Semaphore.Model.take sem0 1 1).1
private def sem2 := (Semaphore.Model.take sem1 2 1).1
private def sem3 := (Semaphore.Model.release sem2 1).1
private def sem4 := Semaphore.Model.visit sem3 0
private def sem5 := Semaphore.Model.takeIfAvailable sem4.1 1
#guard sem4.2 == some ⟨2, 1, 0⟩
#guard sem5.2 == true
#guard (Semaphore.Model.take sem5.1 2 1).2 == false

-- Finite refutation of unrestricted cross-fiber commutation on the SAME hint.
-- register then complete owes a resume; complete then register returns immediately.
-- These are related protocol states, not equal stores or equal step answers.
private def hintStore : DeferredStore Nat := (DeferredStore.make ⟨[], []⟩).2
private def registeredHint := hintStore.register ⟨0⟩ ⟨1⟩ 7
private def registerThenComplete := registeredHint.1.complete ⟨0⟩ 42
private def completedHint := hintStore.complete ⟨0⟩ 42
private def completeThenRegister := completedHint.1.register ⟨0⟩ ⟨1⟩ 7
#guard registeredHint.2 == none
#guard completeThenRegister.2 == some 42
#guard registerThenComplete.1.due.length == 1
#guard completeThenRegister.1.due.length == 0
#guard registerThenComplete.1 != completeThenRegister.1

/-- Author-supplied proof package over an existing entry, without storing another block.
Each proposition parameter is instantiated at that entry and its existing block.
`protocol` includes in-flight post/await/withdraw obligations; `progress` names the
object-specific service and environment assumptions, not bare finite FairTape. -/
structure AuthorProofs (entry : Effect4.Bank.Entry)
    (typing invariant encoding freshness notifications protocol steps progress :
      Effect4.Bank.Entry → Prop) : Prop where
  typed : typing entry
  invariant_closed : invariant entry
  encoded : encoding entry
  fresh : freshness entry
  notified : notifications entry
  protocol_closed : protocol entry
  sequential : steps entry
  live : progress entry

/-- Future CONC-1 signature, not a proof. Protocol must cover fresh identities/hints,
atomic attempts and withdrawals, exact posting, stale hints, masks and interruption.
Successful retry is the linearization point; the wake commits no answer. -/
def WaitRetryLaw (Meaning : Type) (meaning : Src NativeOp → Meaning)
    (refines : Meaning → Meaning → Prop)
    (model : Ty → Waiter → Meaning) (protocol : Ty → Waiter → Prop) : Prop :=
  ∀ result ended w, protocol result w →
    refines (meaning (waitRetry result ended w)) (model result w)

/-- Future CONC-1 signature, not a proof. Protocol relates the committed answer to
its later Deferred delivery. The committing attempt (possibly another request's)
is the linearization point; neither wake delivery nor return is that point. -/
def WaitAnswerLaw (Meaning : Type) (meaning : Src NativeOp → Meaning)
    (refines : Meaning → Meaning → Prop)
    (model : Waiter → Meaning) (protocol : Waiter → Prop) : Prop :=
  ∀ w, protocol w → refines (meaning (waitAnswer w)) (model w)

/-- Per-object progress signature. Fair is supplied by the many-fiber semantics;
its intended meaning needs service of posted helpers, not merely runnable parents.
Environment includes supplies/releases, host answers, and absence of cancellation.
Queue FIFO can discharge eventual completion under these conditions; Semaphore
barging generally supports system completion, not every request's completion.
This definition is NOT a consequence of today's finite FairTape. -/
def RequestProgress (Trace Request : Type) (fair environment : Trace → Prop)
    (pending completed : Trace → Request → Nat → Prop) : Prop :=
  ∀ t, fair t → environment t →
    ∀ r n, pending t r n → ∃ m, n ≤ m ∧ completed t r m

def SystemProgress (Trace Request : Type) (fair environment : Trace → Prop)
    (pending completed : Trace → Request → Nat → Prop) : Prop :=
  ∀ t, fair t → environment t →
    ∀ n, (∃ r, pending t r n) → ∃ r m, n ≤ m ∧ completed t r m

/-- A reached machine genuinely waiting on an allocated uncompleted Deferred. -/
private def parkedMachine : RunMachine Name Thunk Val Err Defect FiberId Ann Ctx Stores :=
  (runFork stores 40 (RunMachine.empty
    { Stores.empty with deferreds := Stores.empty.deferreds.make.2 })
    (progOf (.awaitDeferred ⟨0⟩)) emptyCtx).1
#guard parkedMachine.armed == []
#guard parkedMachine.finished == false
#guard (parkedMachine.fiber? ⟨0⟩).map (fun f => f.parked) == some (.withGuard 0)

/-- Finite fairness does not force this actual parked request to complete.
Placement: review control for R12 bank-progress; consumer D3 claim template. -/
theorem parked_empty_tape_fair :
    Effect4.Machine.Scheduling.FairTape stores 40 parkedMachine [] := by
  intro pre suffix ht _ _ owner ho
  have hp : pre = [] := (List.append_eq_nil_iff.mp ht.symm).1
  subst pre
  have replay : (replayEval stores 40 [] parkedMachine).machine = parkedMachine := by rfl
  rw [replay] at ho
  have unarmed : parkedMachine.armed = [] := by decide
  rw [unarmed] at ho
  cases ho

#check Effect4.Machine.Scheduling.FairTape
#check Effect4.Machine.Scheduling.fairTape_unarmed
end Effect4.Probes.CodexObjects
