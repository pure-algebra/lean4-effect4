import Effect4.Machine.Scope
import Effect4.Machine.ScopeMachine
import Effects.Flow.Block
import Effects.Trace

set_option synthInstance.maxSize 2048

/-!
Independent scope-close stepping packet: `Test/contracts/scope-machine.contract.md`.
Existing-owner controls remain executable while the new production module is absent.
The surface and behavior sections require the actual independently stepping machine.
-/

namespace Test.Runtime.ScopeMachineContract

open Effect4

abbrev Body := Exit Nat Nat Nat Nat Nat
abbrev Reply := Exit Unit Nat Nat Nat Nat
abbrev TestScope := Scope Nat Nat Nat Nat Nat Nat Nat

def reason (n : Nat) : Reason Nat Nat Nat Nat := .fail n ReasonAnnotations.empty
def failed (n : Nat) : Reply := .failure ⟨[reason n]⟩
def emptyFailure : Reply := .failure ⟨[]⟩
def body : Body := .success 7
def bodyFailed : Body := .failure ⟨[reason 9]⟩
def zero : TestScope := ⟨.sequential, .empty⟩
def one : TestScope := ⟨.sequential, .openInline 10 3⟩
def two : TestScope := ⟨.sequential, .openMap [(10, 1), (20, 2)]⟩
def closed : TestScope := ⟨.parallel, .closed (.failure ⟨[reason 99]⟩)⟩

def pureReply (operation : Nat) (_ : Body) : Reply :=
  if operation = 0 then Exit.void
  else if operation = 3 then emptyFailure
  else failed operation

abbrev World := Nat × List (Nat × Body)
def initial : World := (40, [])

def handler (operation : Nat) (original : Body) : StateT World Id Reply :=
  fun world => (pureReply operation original,
    (world.1 + 1, world.2 ++ [(operation, original)]))

def changingFailure (operation : Nat) (original : Body) : StateT World Id Reply :=
  fun world => (failed world.1, (world.1 + 1, world.2 ++ [(operation, original)]))

def duplicateFailure (operation : Nat) (original : Body) : StateT World Id Reply :=
  fun world => (failed 9, (world.1 + 1, world.2 ++ [(operation, original)]))

def emptyFailureHandler (operation : Nat) (original : Body) : StateT World Id Reply :=
  fun world => (emptyFailure, (world.1 + 1, world.2 ++ [(operation, original)]))

def execute (program : StateT World Id (List Reply)) : List Reply × World :=
  (program.run initial).run

-- BEGIN EXISTING-CONTROLS
-- E4-RUN-CE-001/002/003: write state first, LIFO, preserve a previous close.
#guard zero.closeOrder = []
#guard one.closeOrder = [3]
#guard two.closeOrder = [2, 1]
#guard (two.closeState body).state = .closed body
#guard (two.closeState body).strategy = two.strategy
#guard (two.closeState body).closeOrder = []
#guard closed.closeState body = closed
#guard closed.closeResult pureReply body = Exit.void
#guard execute (Scope.closeExitsM handler closed body) = ([], initial)

-- E4-RUN-CE-008/009: capture all exits; singleton empty failure is not void.
#guard zero.closeResult pureReply body = Exit.void
#guard one.closeResult pureReply body = emptyFailure
#guard emptyFailure ≠ (Exit.void : Reply)
#guard Exit.asVoidAll [emptyFailure] = (Exit.void : Reply)
#guard two.closeResult pureReply body = .failure ⟨[reason 2, reason 1]⟩
#guard two.closeResult (fun _ _ => emptyFailure) body = (Exit.void : Reply)
#guard two.closeResult (fun _ _ => failed 9) body = .failure ⟨[reason 9, reason 9]⟩

-- E4-TARGET-CE-019: both requests see the unchanged successful closing exit.
#guard execute (Scope.closeExitsM handler two body) =
  ([failed 2, failed 1], (42, [(2, body), (1, body)]))
#guard execute (Scope.closeExitsM changingFailure two body) =
  ([failed 40, failed 41], (42, [(2, body), (1, body)]))
#guard execute (Scope.closeExitsM duplicateFailure two bodyFailed) =
  ([failed 9, failed 9], (42, [(2, bodyFailed), (1, bodyFailed)]))
#guard Exit.restoreAfterFinalizer bodyFailed
    (two.closeResult (fun _ _ => failed 9) bodyFailed) = bodyFailed
#guard ((two.closeResult (fun _ _ => failed 9) bodyFailed).causeReasons) =
  [reason 9, reason 9]

-- Deliberately wrong candidates; these are attacks, not reference implementations.
def abortAfterFirst (scope : TestScope) (original : Body) : StateT World Id (List Reply) :=
  match scope.closeOrder with
  | [] => pure []
  | first :: _ => do pure [← handler first original]

def threadRestoredExit (original : Body) : StateT World Id (List Reply) := do
  let first ← handler 2 original
  let second ← handler 1 (Exit.restoreAfterFinalizer original first)
  pure [first, second]

#guard execute (abortAfterFirst two body) ≠
  ([failed 2, failed 1], (42, [(2, body), (1, body)]))
#guard execute (threadRestoredExit body) ≠
  ([failed 2, failed 1], (42, [(2, body), (1, body)]))
#guard execute (threadRestoredExit body) =
  ([failed 2, failed 1], (42, [(2, body), (1, .failure ⟨[reason 2]⟩)]))

-- Named acceptance candidates let the breaker plant one violation at a time.
def sameExitCandidate : StateT World Id (List Reply) := Scope.closeExitsM handler two body
def allResponsesCandidate : StateT World Id (List Reply) := Scope.closeExitsM handler two body
def singletonCandidate : Reply := one.closeResult pureReply body
#guard execute sameExitCandidate =
  ([failed 2, failed 1], (42, [(2, body), (1, body)]))
#guard execute allResponsesCandidate =
  ([failed 2, failed 1], (42, [(2, body), (1, body)]))
#guard singletonCandidate = emptyFailure
-- END EXISTING-CONTROLS

-- BEGIN MACHINE-SURFACE
-- These are exact signatures, including constructor/field and pair order.
section Surface
universe u v
variable {κ φ : Type u} {β : Type v} {ε δ ι α σ : Type u}

example : φ → ScopeMachine.Phase φ := ScopeMachine.Phase.waiting
example : ScopeMachine.Phase φ := ScopeMachine.Phase.ready
example : ScopeMachine.Phase φ := ScopeMachine.Phase.complete
example : Scope κ φ β ε δ ι α → Exit β ε δ ι α → List φ →
    List (φ × Exit Unit ε δ ι α) → ScopeMachine.Phase φ →
    ScopeMachine.State κ φ β ε δ ι α := ScopeMachine.State.mk
example : Scope κ φ β ε δ ι α → Exit β ε δ ι α →
    ScopeMachine.State κ φ β ε δ ι α := ScopeMachine.start
example : ScopeMachine.State κ φ β ε δ ι α → ScopeMachine.State κ φ β ε δ ι α :=
  ScopeMachine.advance
example : ScopeMachine.State κ φ β ε δ ι α →
    Option (Nat × φ × Exit β ε δ ι α) := ScopeMachine.request?
example : ScopeMachine.State κ φ β ε δ ι α → Nat → Exit Unit ε δ ι α →
    Option (ScopeMachine.State κ φ β ε δ ι α) := ScopeMachine.respond
example : ScopeMachine.State κ φ β ε δ ι α → Option (Exit Unit ε δ ι α) :=
  ScopeMachine.result?
example : ScopeMachine.State κ φ β ε δ ι α → List (Reason ε δ ι α) :=
  ScopeMachine.journal
example [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    ScopeMachine.State κ φ β ε δ ι α → Option (Exit β ε δ ι α) :=
  ScopeMachine.restore?
example : Scope κ φ β ε δ ι α → Nat := ScopeMachine.bound
example : (φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α)) →
    Nat → ScopeMachine.State κ φ β ε δ ι α → σ →
    ScopeMachine.State κ φ β ε δ ι α × σ := ScopeMachine.runState

example : ∀ (machine : ScopeMachine.State κ φ β ε δ ι α) (ordinal : Nat)
    (operation : φ) (offered : Exit β ε δ ι α),
    ScopeMachine.request? machine = some (ordinal, operation, offered) →
    offered = machine.original := ScopeMachine.request_uses_original

example : ∀ (machine : ScopeMachine.State κ φ β ε δ ι α) (ordinal : Nat)
    (reply : Exit Unit ε δ ι α), ordinal ≠ machine.captured.length →
    ScopeMachine.respond machine ordinal reply = none := ScopeMachine.respond_rejects_wrong_id

example : ∀ (machine : ScopeMachine.State κ φ β ε δ ι α) (ordinal : Nat)
    (reply : Exit Unit ε δ ι α),
    (∀ operation, machine.phase ≠ ScopeMachine.Phase.waiting operation) →
    ScopeMachine.respond machine ordinal reply = none := ScopeMachine.respond_rejects_wrong_phase

example : ∀ (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (machine : ScopeMachine.State κ φ β ε δ ι α) (world : σ),
    ScopeMachine.runState handler 0 machine world = (machine, world) := ScopeMachine.runState_zero

example : ∀ (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (first later : Nat) (machine : ScopeMachine.State κ φ β ε δ ι α) (world : σ),
    ScopeMachine.runState handler (first + later) machine world =
      let resumed := ScopeMachine.runState handler first machine world
      ScopeMachine.runState handler later resumed.1 resumed.2 := ScopeMachine.runState_add

example : ∀ (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (budget : Nat) (machine : ScopeMachine.State κ φ β ε δ ι α) (world : σ),
    (ScopeMachine.runState handler budget machine world).1.scope = machine.scope :=
  ScopeMachine.runState_scope

example : ∀ (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (budget : Nat) (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ),
    let result := ScopeMachine.runState handler budget (ScopeMachine.start scope original) world
    result.1.scope = scope.closeState original ∧ result.1.original = original ∧
    result.1.captured.map Prod.fst ++
        (match result.1.phase with | .waiting operation => [operation] | _ => []) ++
        result.1.pending = scope.closeOrder ∧
    (result.1.phase = .complete → result.1.pending = []) ∧
    (((result.1.captured.map Prod.fst).mapM (fun operation => handler operation original)).run world) =
      (result.1.captured.map Prod.snd, result.2) := ScopeMachine.runState_prefix

example : ∀ (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ),
    ScopeMachine.runState handler (ScopeMachine.bound scope) (ScopeMachine.start scope original) world =
      let result := (Scope.closeExitsM handler scope original).run world
      ({ scope := scope.closeState original, original := original, pending := [],
         captured := scope.closeOrder.zip result.1, phase := .complete }, result.2) :=
  ScopeMachine.runState_complete

example : ∀ (callback : φ → Exit β ε δ ι α → Exit Unit ε δ ι α)
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ),
    ScopeMachine.result? (ScopeMachine.runState
      (fun operation exit world => (callback operation exit, world))
      (ScopeMachine.bound scope) (ScopeMachine.start scope original) world).1 =
        some (scope.closeResult callback original) := ScopeMachine.runState_result

example [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    ∀ (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α) (world : σ),
    (let result := ScopeMachine.runState handler (ScopeMachine.bound scope)
      (ScopeMachine.start scope original) world
     (ScopeMachine.restore? result.1, result.2)) =
    (let result := (Scope.closeExitsM handler scope original).run world
     let cleanup := match result.1 with
       | [] => Exit.void
       | [only] => only
       | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)
     (some (Exit.restoreAfterFinalizer original cleanup), result.2)) := ScopeMachine.runState_restore

end Surface

-- A concrete target request stores an operation identity and its resource data.
example : DecidableEq (ScopeMachine.State Nat (Effects.OperationId × Effects.Trace.Val)
    Effects.Trace.Val Effects.Trace.Val Unit Unit Unit) := inferInstance
-- END MACHINE-SURFACE

-- BEGIN MACHINE-BEHAVIOR
abbrev Machine := ScopeMachine.State Nat Nat Nat Nat Nat Nat Nat

def afterBudget (budget : Nat) : Machine × World :=
  ScopeMachine.runState handler budget (ScopeMachine.start two body) initial

#guard ScopeMachine.bound zero = 1
#guard ScopeMachine.bound one = 3
#guard ScopeMachine.bound two = 5
#guard ScopeMachine.bound closed = 1
#guard (afterBudget 0).1 = ⟨two.closeState body, body, [2, 1], [], .ready⟩
#guard (afterBudget 0).2 = initial
#guard ScopeMachine.request? (afterBudget 0).1 = none
#guard ScopeMachine.result? (afterBudget 0).1 = none
#guard ScopeMachine.restore? (afterBudget 0).1 = none
#guard ScopeMachine.respond (afterBudget 0).1 0 (failed 2) = none

-- A request is visible only after advance, and no handler ran at this pause.
#guard (afterBudget 1).1 = ⟨two.closeState body, body, [1], [], .waiting 2⟩
#guard (afterBudget 1).2 = initial
#guard ScopeMachine.request? (afterBudget 1).1 = some (0, 2, body)
#guard ScopeMachine.result? (afterBudget 1).1 = none
#guard ScopeMachine.advance (afterBudget 1).1 = (afterBudget 1).1
#guard ScopeMachine.respond (afterBudget 1).1 1 (failed 2) = none
#guard ScopeMachine.respond (afterBudget 1).1 99 (failed 2) = none
#guard ScopeMachine.respond (afterBudget 1).1 0 (failed 2) =
  some ⟨two.closeState body, body, [1], [(2, failed 2)], .ready⟩

-- Failure retains both its reply and service state; it does not finish the close.
#guard (afterBudget 2).1 = ⟨two.closeState body, body, [1], [(2, failed 2)], .ready⟩
#guard (afterBudget 2).2 = (41, [(2, body)])
#guard ScopeMachine.request? (afterBudget 2).1 = none
#guard ScopeMachine.result? (afterBudget 2).1 = none
#guard ScopeMachine.restore? (afterBudget 2).1 = none
#guard ScopeMachine.respond (afterBudget 2).1 0 (failed 2) = none
#guard ScopeMachine.journal (afterBudget 2).1 = [reason 2]

-- Stale and future responses cannot consume the next operation.
#guard (afterBudget 3).1 = ⟨two.closeState body, body, [], [(2, failed 2)], .waiting 1⟩
#guard (afterBudget 3).2 = (41, [(2, body)])
#guard ScopeMachine.request? (afterBudget 3).1 = some (1, 1, body)
#guard ScopeMachine.respond (afterBudget 3).1 0 (failed 2) = none
#guard ScopeMachine.respond (afterBudget 3).1 2 (failed 1) = none
#guard ScopeMachine.result? (afterBudget 3).1 = none
#guard ScopeMachine.restore? (afterBudget 3).1 = none

-- The last response is still a live ready state until the completion microstep.
#guard (afterBudget 4).1 = ⟨two.closeState body, body, [], [(2, failed 2), (1, failed 1)], .ready⟩
#guard (afterBudget 4).2 = (42, [(2, body), (1, body)])
#guard ScopeMachine.result? (afterBudget 4).1 = none
#guard ScopeMachine.restore? (afterBudget 4).1 = none
#guard ScopeMachine.respond (afterBudget 4).1 1 (failed 1) = none
#guard (afterBudget 5).1 = ⟨two.closeState body, body, [], [(2, failed 2), (1, failed 1)], .complete⟩
#guard (afterBudget 5).2 = (42, [(2, body), (1, body)])
#guard ScopeMachine.request? (afterBudget 5).1 = none
#guard ScopeMachine.result? (afterBudget 5).1 = some (.failure ⟨[reason 2, reason 1]⟩)
#guard ScopeMachine.restore? (afterBudget 5).1 = some (.failure ⟨[reason 2, reason 1]⟩)
#guard ScopeMachine.journal (afterBudget 5).1 = [reason 2, reason 1]
#guard ScopeMachine.respond (afterBudget 5).1 2 (failed 3) = none
#guard ScopeMachine.advance (afterBudget 5).1 = (afterBudget 5).1
#guard afterBudget 40 = afterBudget 5
#guard ScopeMachine.runState handler 3 (afterBudget 2).1 (afterBudget 2).2 = afterBudget 5
#guard ScopeMachine.runState handler 0 (afterBudget 3).1 (afterBudget 3).2 = afterBudget 3

def changed := ScopeMachine.runState changingFailure 5 (ScopeMachine.start two body) initial
#guard changed.1.captured = [(2, failed 40), (1, failed 41)]
#guard changed.2 = (42, [(2, body), (1, body)])

def duplicates := ScopeMachine.runState duplicateFailure 5 (ScopeMachine.start two bodyFailed) initial
#guard duplicates.1.captured = [(2, failed 9), (1, failed 9)]
#guard ScopeMachine.result? duplicates.1 = some (.failure ⟨[reason 9, reason 9]⟩)
#guard ScopeMachine.journal duplicates.1 = [reason 9, reason 9]
#guard ScopeMachine.restore? duplicates.1 = some bodyFailed
#guard duplicates.2 = (42, [(2, bodyFailed), (1, bodyFailed)])

def singleEmpty := ScopeMachine.runState emptyFailureHandler 3 (ScopeMachine.start one body) initial
def manyEmpty := ScopeMachine.runState emptyFailureHandler 5 (ScopeMachine.start two body) initial
#guard ScopeMachine.result? singleEmpty.1 = some emptyFailure
#guard ScopeMachine.restore? singleEmpty.1 = some (.failure ⟨[]⟩)
#guard ScopeMachine.result? manyEmpty.1 = some Exit.void
#guard ScopeMachine.restore? manyEmpty.1 = some body
#guard ScopeMachine.journal singleEmpty.1 = []
#guard ScopeMachine.journal manyEmpty.1 = []

def emptyClose := ScopeMachine.runState handler 1 (ScopeMachine.start zero body) initial
def repeatedClose := ScopeMachine.runState handler 1 (ScopeMachine.start closed body) initial
#guard ScopeMachine.result? emptyClose.1 = some Exit.void
#guard emptyClose.2 = initial
#guard repeatedClose.1.scope = closed
#guard repeatedClose.1.original = body
#guard repeatedClose.1.captured = []
#guard ScopeMachine.result? repeatedClose.1 = some Exit.void
#guard ScopeMachine.restore? repeatedClose.1 = some body
#guard repeatedClose.2 = initial

def parallelLabel := { two with strategy := FinalizerStrategy.parallel }
def retainedLabel := ScopeMachine.runState handler 5 (ScopeMachine.start parallelLabel body) initial
#guard retainedLabel.1.scope.strategy = .parallel
#guard retainedLabel.1.captured = [(2, failed 2), (1, failed 1)]
#guard retainedLabel.2 = (42, [(2, body), (1, body)])
-- This is the sequential closeExitsM interpretation, not a parallel scheduler test.
-- END MACHINE-BEHAVIOR

end Test.Runtime.ScopeMachineContract
