/-
Breaker-owned packet: `test/contracts/fiber-supervision.contract.md`.
Breaker-frozen RED, 2026-09-02; the contract records the complete red output.
Implementation must not edit this frozen battery. Pinned source is Effect 4.0.0-rc.112.
-/
import Effect4.Concurrency.Scheduler
import Effect4.Runtime.Scope
import Effect4.Concurrency.Supervision

set_option autoImplicit false

namespace Effect4Test.Concurrency.FiberSupervisionContract
universe u v w

#check (@Effect4.Supervision.MaskMode :
  Type)

#check (@Effect4.Supervision.MaskMode.interruptible :
  Effect4.Supervision.MaskMode)

#check (@Effect4.Supervision.MaskMode.uninterruptible :
  Effect4.Supervision.MaskMode)

#check (@Effect4.Supervision.MaskMode.inherit :
  Effect4.Supervision.MaskMode)

#check (@Effect4.Supervision.ForkOptions :
  Type)

#check (@Effect4.Supervision.ForkOptions.mk :
  Bool -> Bool -> Effect4.Supervision.MaskMode -> Effect4.Supervision.ForkOptions)

#check (@Effect4.Supervision.ForkOptions.startImmediately :
  Effect4.Supervision.ForkOptions -> Bool)

#check (@Effect4.Supervision.ForkOptions.daemon :
  Effect4.Supervision.ForkOptions -> Bool)

#check (@Effect4.Supervision.ForkOptions.maskMode :
  Effect4.Supervision.ForkOptions -> Effect4.Supervision.MaskMode)

#check (@Effect4.Supervision.Globals :
  Type)

#check (@Effect4.Supervision.Globals.mk :
  List Effect4.FiberId -> Bool -> Effect4.Supervision.Globals)

#check (@Effect4.Supervision.Globals.allocated :
  Effect4.Supervision.Globals -> List Effect4.FiberId)

#check (@Effect4.Supervision.Globals.middlewareInstalled :
  Effect4.Supervision.Globals -> Bool)

#check (@Effect4.Supervision.ObserverMode :
  Type)

#check (@Effect4.Supervision.ObserverMode.awaitValue :
  Effect4.Supervision.ObserverMode)

#check (@Effect4.Supervision.ObserverMode.joinEffect :
  Effect4.Supervision.ObserverMode)

#check (@Effect4.Supervision.Subscription :
  Type)

#check (@Effect4.Supervision.Subscription.mk :
  Nat -> Effect4.Supervision.ObserverMode -> Effect4.Supervision.Subscription)

#check (@Effect4.Supervision.Subscription.key :
  Effect4.Supervision.Subscription -> Nat)

#check (@Effect4.Supervision.Subscription.mode :
  Effect4.Supervision.Subscription -> Effect4.Supervision.ObserverMode)

#check (@Effect4.Supervision.Fiber :
  Type u -> Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))

#check (@Effect4.Supervision.Fiber.mk :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FiberState (Effect4.Exit β ε δ ι α) -> χ -> List Effect4.FiberId -> List Effect4.Supervision.Subscription -> Option (Effect4.Cause ε δ ι α) -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.Fiber.core :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberState (Effect4.Exit β ε δ ι α))

#check (@Effect4.Supervision.Fiber.context :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> χ)

#check (@Effect4.Supervision.Fiber.children :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> List Effect4.FiberId)

#check (@Effect4.Supervision.Fiber.subscriptions :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> List Effect4.Supervision.Subscription)

#check (@Effect4.Supervision.Fiber.interrupted :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Option (Effect4.Cause ε δ ι α))

#check (@Effect4.Supervision.Observation :
  Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))

#check (@Effect4.Supervision.Observation.waiting :
  forall {β : Type v} {ε δ ι α : Type u}, Nat -> Effect4.Supervision.Observation β ε δ ι α)

#check (@Effect4.Supervision.Observation.value :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Exit β ε δ ι α -> Effect4.Supervision.Observation β ε δ ι α)

#check (@Effect4.Supervision.Observation.effect :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Exit β ε δ ι α -> Effect4.Supervision.Observation β ε δ ι α)

#check (@Effect4.Supervision.StartObservation :
  Type u -> Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))

#check (@Effect4.Supervision.StartObservation.deferred :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.StartObservation χ β ε δ ι α)

#check (@Effect4.Supervision.StartObservation.immediate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.StartObservation χ β ε δ ι α)

#check (@Effect4.Supervision.ForkEvent :
  Type)

#check (@Effect4.Supervision.ForkEvent.scheduled :
  Effect4.FiberId -> Nat -> Effect4.Supervision.ForkEvent)

#check (@Effect4.Supervision.ForkEvent.evaluated :
  Effect4.FiberId -> Effect4.Supervision.ForkEvent)

#check (@Effect4.Supervision.ForkEvent.registered :
  Effect4.FiberId -> Effect4.FiberId -> Effect4.Supervision.ForkEvent)

#check (@Effect4.Supervision.ForkResult :
  Type u -> Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))

#check (@Effect4.Supervision.ForkResult.mk :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α -> List Effect4.Supervision.ForkEvent -> Option Effect4.FiberId -> Effect4.Supervision.ForkResult χ β ε δ ι α)

#check (@Effect4.Supervision.ForkResult.globals :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ForkResult χ β ε δ ι α -> Effect4.Supervision.Globals)

#check (@Effect4.Supervision.ForkResult.parent :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ForkResult χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.ForkResult.initial :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ForkResult χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.ForkResult.child :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ForkResult χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.ForkResult.events :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ForkResult χ β ε δ ι α -> List Effect4.Supervision.ForkEvent)

#check (@Effect4.Supervision.ForkResult.removeFromParent :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ForkResult χ β ε δ ι α -> Option Effect4.FiberId)

#check (@Effect4.Supervision.InterruptAction :
  Type)

#check (@Effect4.Supervision.InterruptAction.request :
  Effect4.FiberId -> Effect4.Supervision.InterruptAction)

#check (@Effect4.Supervision.InterruptAction.awaitAll :
  List Effect4.FiberId -> Effect4.Supervision.InterruptAction)

#check (@Effect4.Supervision.Refusal :
  Type)

#check (@Effect4.Supervision.Refusal.invalidFiber :
  Effect4.FiberId -> Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.duplicateFiber :
  Effect4.FiberId -> Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.wrongStartMode :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.wrongChildIdentity :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.wrongParentIdentity :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.invalidStartGlobals :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.invalidParentOwnership :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.invalidChildOwnership :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.duplicateSubscription :
  Nat -> Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.unknownPublication :
  Effect4.FiberId -> Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.duplicateScopeKey :
  Nat -> Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.duplicateEntrant :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.noEntrant :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.wrongRacePhase :
  Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.Refusal.unknownEntrant :
  Effect4.FiberId -> Effect4.Supervision.Refusal)

#check (@Effect4.Supervision.WaitState :
  Type u -> Type u)

#check (@Effect4.Supervision.WaitState.mk :
  forall {τ : Type u}, List Effect4.FiberId -> List Effect4.FiberId -> τ -> Effect4.Supervision.WaitState τ)

#check (@Effect4.Supervision.WaitState.targets :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> List Effect4.FiberId)

#check (@Effect4.Supervision.WaitState.published :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> List Effect4.FiberId)

#check (@Effect4.Supervision.WaitState.result :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> τ)

#check (@Effect4.Supervision.ReplayResult :
  Type u -> Type v -> Type (max u v))

#check (@Effect4.Supervision.ReplayResult.done :
  forall {σ : Type u} {τ : Type v}, σ -> τ -> Effect4.Supervision.ReplayResult σ τ)

#check (@Effect4.Supervision.ReplayResult.frontier :
  forall {σ : Type u} {τ : Type v}, σ -> Effect4.Supervision.ReplayResult σ τ)

#check (@Effect4.Supervision.ReplayResult.refused :
  forall {σ : Type u} {τ : Type v}, σ -> Effect4.Supervision.Refusal -> Effect4.Supervision.ReplayResult σ τ)

#check (@Effect4.Supervision.ScopeMode :
  Type)

#check (@Effect4.Supervision.ScopeMode.forkIn :
  Effect4.Supervision.ScopeMode)

#check (@Effect4.Supervision.ScopeMode.fiberRunIn :
  Effect4.Supervision.ScopeMode)

#check (@Effect4.Supervision.ScopeFinalizer :
  Type)

#check (@Effect4.Supervision.ScopeFinalizer.mk :
  Effect4.FiberId -> Bool -> Effect4.Supervision.ScopeFinalizer)

#check (@Effect4.Supervision.ScopeFinalizer.child :
  Effect4.Supervision.ScopeFinalizer -> Effect4.FiberId)

#check (@Effect4.Supervision.ScopeFinalizer.skipSelf :
  Effect4.Supervision.ScopeFinalizer -> Bool)

#check (@Effect4.Supervision.ScopeBinding :
  Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))

#check (@Effect4.Supervision.ScopeBinding.mk :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α -> Option Nat -> Option Effect4.FiberId -> Effect4.Supervision.ScopeBinding β ε δ ι α)

#check (@Effect4.Supervision.ScopeBinding.scope :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ScopeBinding β ε δ ι α -> Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α)

#check (@Effect4.Supervision.ScopeBinding.observerKey :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ScopeBinding β ε δ ι α -> Option Nat)

#check (@Effect4.Supervision.ScopeBinding.interruptor :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ScopeBinding β ε δ ι α -> Option Effect4.FiberId)

#check (@Effect4.Supervision.RaceAllState :
  Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))

#check (@Effect4.Supervision.RaceAllState.mk :
  forall {β : Type v} {ε δ ι α : Type u}, List Effect4.FiberId -> Option Effect4.FiberId -> List Effect4.FiberId -> Nat -> List (Effect4.Reason ε δ ι α) -> Option (Effect4.FiberId × β) -> Option (Effect4.Exit β ε δ ι α) -> Bool -> List Effect4.FiberId -> Option (Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)) -> Bool -> Effect4.Supervision.RaceAllState β ε δ ι α)

#check (@Effect4.Supervision.RaceAllState.unstarted :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> List Effect4.FiberId)

#check (@Effect4.Supervision.RaceAllState.starting :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Option Effect4.FiberId)

#check (@Effect4.Supervision.RaceAllState.live :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> List Effect4.FiberId)

#check (@Effect4.Supervision.RaceAllState.remaining :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Nat)

#check (@Effect4.Supervision.RaceAllState.failures :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> List (Effect4.Reason ε δ ι α))

#check (@Effect4.Supervision.RaceAllState.winner :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Option (Effect4.FiberId × β))

#check (@Effect4.Supervision.RaceAllState.accepted :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Option (Effect4.Exit β ε δ ι α))

#check (@Effect4.Supervision.RaceAllState.cleanupNeeded :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Bool)

#check (@Effect4.Supervision.RaceAllState.requests :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> List Effect4.FiberId)

#check (@Effect4.Supervision.RaceAllState.cleanup :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Option (Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)))

#check (@Effect4.Supervision.RaceAllState.cleanupRequested :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Bool)

#check (@Effect4.Supervision.RaceAllDecision :
  Type v -> Type u -> Type u -> Type u -> Type u -> Type (max u v))

#check (@Effect4.Supervision.RaceAllDecision.beginLaunch :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllDecision β ε δ ι α)

#check (@Effect4.Supervision.RaceAllDecision.finishLaunch :
  forall {β : Type v} {ε δ ι α : Type u}, Option (Effect4.Exit β ε δ ι α) -> Effect4.Supervision.RaceAllDecision β ε δ ι α)

#check (@Effect4.Supervision.RaceAllDecision.complete :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.FiberId -> Effect4.Exit β ε δ ι α -> Effect4.Supervision.RaceAllDecision β ε δ ι α)

#check (@Effect4.Supervision.RaceAllDecision.beginCleanup :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllDecision β ε δ ι α)

#check (@Effect4.Supervision.RaceAllDecision.requestNext :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllDecision β ε δ ι α)

#check (@Effect4.Supervision.MaskMode.select :
  Effect4.Supervision.MaskMode -> Effect4.InterruptMask -> Effect4.InterruptMask)

#check (@Effect4.Supervision.Globals.install :
  Effect4.Supervision.Globals -> Effect4.Supervision.Globals)

#check (@Effect4.Supervision.Globals.Valid :
  Effect4.Supervision.Globals -> Prop)

#check (@Effect4.Supervision.Globals.allocate :
  Effect4.Supervision.Globals -> Effect4.FiberId -> Effect4.Supervision.Globals)

#check (@Effect4.Supervision.Globals.Extends :
  Effect4.Supervision.Globals -> Effect4.Supervision.Globals -> Prop)

#check (@Effect4.Supervision.Globals.extends? :
  Effect4.Supervision.Globals -> Effect4.Supervision.Globals -> Bool)

#check (@Effect4.Supervision.Globals.OwnsChildren :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Prop)

#check (@Effect4.Supervision.Globals.ownsChildren? :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Bool)

#check (@Effect4.Supervision.Fiber.Valid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Prop)

#check (@Effect4.Supervision.Fiber.valid? :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Bool)

#check (@Effect4.Supervision.Fiber.toFiberState :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberState (Effect4.Exit β ε δ ι α))

#check (@Effect4.Supervision.Fiber.published? :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Option (Effect4.Exit β ε δ ι α))

#check (@Effect4.Supervision.Fiber.addChild :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberId -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.Fiber.removeChild :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberId -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.observation :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ObserverMode -> Effect4.Exit β ε δ ι α -> Effect4.Supervision.Observation β ε δ ι α)

#check (@Effect4.Supervision.Fiber.observe :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.Subscription -> Except Effect4.Supervision.Refusal (Effect4.Supervision.Fiber χ β ε δ ι α × Effect4.Supervision.Observation β ε δ ι α))

#check (@Effect4.Supervision.Fiber.cancel :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Nat -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.Fiber.publish :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Exit β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α × List (Nat × Effect4.Supervision.Observation β ε δ ι α))

#check (@Effect4.Supervision.interruptCause :
  forall {ε δ ι α : Type u}, (Effect4.FiberId -> ι) -> Option Effect4.FiberId -> Effect4.ReasonAnnotations α -> Effect4.Cause ε δ ι α)

#check (@Effect4.Supervision.Fiber.recordInterrupt :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> (Effect4.FiberId -> ι) -> Option Effect4.FiberId -> Effect4.ReasonAnnotations α -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.initialFiber :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberId -> Effect4.Supervision.MaskMode -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.commitFork :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.Fiber χ β ε δ ι α -> Bool -> List Effect4.Supervision.ForkEvent -> Effect4.Supervision.ForkResult χ β ε δ ι α)

#check (@Effect4.Supervision.forkUnsafe :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberId -> Effect4.Supervision.ForkOptions -> Effect4.Supervision.StartObservation χ β ε δ ι α -> Except Effect4.Supervision.Refusal (Effect4.Supervision.ForkResult χ β ε δ ι α))

#check (@Effect4.Supervision.forkChild :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberId -> Effect4.Supervision.ForkOptions -> Effect4.Supervision.StartObservation χ β ε δ ι α -> Except Effect4.Supervision.Refusal (Effect4.Supervision.ForkResult χ β ε δ ι α))

#check (@Effect4.Supervision.forkDetach :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.FiberId -> Effect4.Supervision.ForkOptions -> Effect4.Supervision.StartObservation χ β ε δ ι α -> Except Effect4.Supervision.Refusal (Effect4.Supervision.ForkResult χ β ε δ ι α))

#check (@Effect4.Supervision.WaitState.begin :
  forall {τ : Type u}, List Effect4.FiberId -> τ -> Effect4.Supervision.WaitState τ)

#check (@Effect4.Supervision.WaitState.pending :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> List Effect4.FiberId)

#check (@Effect4.Supervision.WaitState.ready? :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> Option τ)

#check (@Effect4.Supervision.WaitState.observe :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> Effect4.FiberId -> Except Effect4.Supervision.Refusal (Effect4.Supervision.WaitState τ))

#check (@Effect4.Supervision.ReplayResult.state :
  forall {σ : Type u} {τ : Type v}, Effect4.Supervision.ReplayResult σ τ -> σ)

#check (@Effect4.Supervision.WaitStep :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> Effect4.FiberId -> Effect4.Supervision.WaitState τ -> Prop)

#check (@Effect4.Supervision.waitReplay :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> List Effect4.FiberId -> Effect4.Supervision.ReplayResult (Effect4.Supervision.WaitState τ) τ)

#check (@Effect4.Supervision.WaitRuns :
  forall {τ : Type u}, Effect4.Supervision.WaitState τ -> List Effect4.FiberId -> Effect4.Supervision.ReplayResult (Effect4.Supervision.WaitState τ) τ -> Prop)

#check (@Effect4.Supervision.beginParentExit :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Globals -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Exit β ε δ ι α -> Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α))

#check (@Effect4.Supervision.parentExitView :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α) -> Effect4.Supervision.Fiber χ β ε δ ι α)

#check (@Effect4.Supervision.newChildren :
  List Effect4.FiberId -> List Effect4.FiberId -> List Effect4.FiberId)

#check (@Effect4.Supervision.awaitAllChildren :
  List Effect4.FiberId -> List Effect4.FiberId -> Effect4.Supervision.WaitState Unit)

#check (@Effect4.Supervision.interruptAllRequests :
  List Effect4.FiberId -> List Effect4.Supervision.InterruptAction)

#check (@Effect4.Supervision.interruptAllWait :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, List (Effect4.Supervision.Fiber χ β ε δ ι α) -> Effect4.Supervision.WaitState Unit)

#check (@Effect4.Supervision.bindScope :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.ScopeMode -> Effect4.FiberId -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α -> Nat -> Except Effect4.Supervision.Refusal (Effect4.Supervision.ScopeBinding β ε δ ι α))

#check (@Effect4.Supervision.forkScopedBinding :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FiberId -> Effect4.Supervision.Fiber χ β ε δ ι α -> Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α -> Nat -> Except Effect4.Supervision.Refusal (Effect4.Supervision.ScopeBinding β ε δ ι α))

#check (@Effect4.Supervision.scopeFinalizerInterruptor :
  Effect4.Supervision.ScopeFinalizer -> Effect4.FiberId -> Option Effect4.FiberId)

#check (@Effect4.Supervision.scopeObserver :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α -> Nat -> Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α)

#check (@Effect4.Supervision.raceForkOptions :
  Effect4.Supervision.ForkOptions)

#check (@Effect4.Supervision.raceCleanupMask :
  Effect4.InterruptMask)

#check (@Effect4.Supervision.RaceAllState.initial :
  forall {β : Type v} {ε δ ι α : Type u}, List Effect4.FiberId -> Effect4.Supervision.RaceAllState β ε δ ι α)

#check (@Effect4.Supervision.raceAllAdmit :
  forall {β : Type v} {ε δ ι α : Type u}, List Effect4.FiberId -> Except Effect4.Supervision.Refusal (Effect4.Supervision.RaceAllState β ε δ ι α))

#check (@Effect4.Supervision.RaceAllState.result? :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Option (Effect4.Exit β ε δ ι α))

#check (@Effect4.Supervision.raceComplete :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Effect4.FiberId -> Effect4.Exit β ε δ ι α -> Effect4.Supervision.RaceAllState β ε δ ι α)

#check (@Effect4.Supervision.raceStep :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Effect4.Supervision.RaceAllDecision β ε δ ι α -> Except Effect4.Supervision.Refusal (Effect4.Supervision.RaceAllState β ε δ ι α))

#check (@Effect4.Supervision.RaceStep :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> Effect4.Supervision.RaceAllDecision β ε δ ι α -> Effect4.Supervision.RaceAllState β ε δ ι α -> Prop)

#check (@Effect4.Supervision.raceReplay :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> List (Effect4.Supervision.RaceAllDecision β ε δ ι α) -> Effect4.Supervision.ReplayResult (Effect4.Supervision.RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α))

#check (@Effect4.Supervision.RaceRuns :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.RaceAllState β ε δ ι α -> List (Effect4.Supervision.RaceAllDecision β ε δ ι α) -> Effect4.Supervision.ReplayResult (Effect4.Supervision.RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α) -> Prop)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.MaskMode.select_interruptible :
  forall mask, Effect4.Supervision.MaskMode.select .interruptible mask = .unmasked)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.MaskMode.select_uninterruptible :
  forall mask, Effect4.Supervision.MaskMode.select .uninterruptible mask = .masked)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.MaskMode.select_inherit :
  forall mask, Effect4.Supervision.MaskMode.select .inherit mask = mask)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.MaskMode.cases_receipt :
  forall mode : Effect4.Supervision.MaskMode, mode = .interruptible ∨ mode = .uninterruptible ∨ mode = .inherit)

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.ObserverMode.cases_receipt :
  forall mode : Effect4.Supervision.ObserverMode, mode = .awaitValue ∨ mode = .joinEffect)

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.ScopeMode.cases_receipt :
  forall mode : Effect4.Supervision.ScopeMode, mode = .forkIn ∨ mode = .fiberRunIn)

/- Required production docstring census tags: fork.child rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.Globals.install_eq :
  forall g : Effect4.Supervision.Globals, Effect4.Supervision.Globals.install g = {g with middlewareInstalled := true})

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.Globals.valid_iff :
  forall g : Effect4.Supervision.Globals, Effect4.Supervision.Globals.Valid g ↔ g.allocated.Nodup)

/- Required production docstring census tags: fork.unsafe rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.Globals.ownsChildren_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (f : Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.Globals.OwnsChildren g f ↔ f.core.id ∈ g.allocated ∧ (∀ child, child ∈ f.children -> child ∈ g.allocated))

/- Required production docstring census tags: fork.unsafe fork.join -/
#check (@Effect4.Supervision.Fiber.valid_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.Valid f ↔ f.children.Nodup ∧ (f.subscriptions.map Effect4.Supervision.Subscription.key).Nodup ∧ (Effect4.FiberStatus.Active f.core.status -> f.core.terminal = none ∧ f.core.cleanup = .notStarted ∧ f.core.cleanupCount = 0) ∧ (f.core.status = .finalizing -> f.core.terminal.isSome = true ∧ f.core.cleanup = .pending ∧ f.core.cleanupCount = 0) ∧ (f.core.status = .done -> f.core.terminal.isSome = true ∧ f.core.cleanup = .done ∧ f.core.cleanupCount = 1))

/- Required production docstring census tags: fork.unsafe fork.join -/
#check (@Effect4.Supervision.Fiber.valid?_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.valid? f = true ↔ Effect4.Supervision.Fiber.Valid f)

/- Required production docstring census tags: fork.unsafe fork.join -/
#check (@Effect4.Supervision.Fiber.toFiberState_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.toFiberState f = f.core)

/- Required production docstring census tags: fork.join fork.await rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.Fiber.published_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? f = some exit ↔ f.core.status = .done ∧ f.core.terminal = some exit)

/- Required production docstring census tags: fork.join fork.await -/
#check (@Effect4.Supervision.Fiber.published_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.published? f = if f.core.status = .done then f.core.terminal else none)

/- Required production docstring census tags: rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.Fiber.addChild_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId), Effect4.Supervision.Fiber.addChild f child = {f with children := if child ∈ f.children then f.children else f.children ++ [child]})

/- Required production docstring census tags: fork.child rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.Fiber.removeChild_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId), Effect4.Supervision.Fiber.removeChild f child = {f with children := f.children.filter (fun id => decide (id ≠ child))})

/- Required production docstring census tags: fork.child rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.Fiber.addChild_nodup :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId), f.children.Nodup -> (Effect4.Supervision.Fiber.addChild f child).children.Nodup)

/- Required production docstring census tags: fork.child rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.Fiber.removeChild_membership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child other : Effect4.FiberId), other ∈ (Effect4.Supervision.Fiber.removeChild f child).children ↔ other ∈ f.children ∧ other ≠ child)

/- Required production docstring census tags: fork.await -/
#check (@Effect4.Supervision.observation_await :
  forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, Effect4.Supervision.observation .awaitValue exit = .value exit)

/- Required production docstring census tags: fork.join -/
#check (@Effect4.Supervision.observation_join :
  forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, Effect4.Supervision.observation .joinEffect exit = .effect exit)

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.observation_value_ne_effect :
  forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, (Effect4.Supervision.Observation.value exit : Effect4.Supervision.Observation β ε δ ι α) ≠ .effect exit)

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.Fiber.observe_invalid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription), Effect4.Supervision.Fiber.valid? f = false -> Effect4.Supervision.Fiber.observe f subscription = .error (.invalidFiber f.core.id))

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.Fiber.observe_done :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.Valid f -> Effect4.Supervision.Fiber.published? f = some exit -> Effect4.Supervision.Fiber.observe f subscription = .ok (f, Effect4.Supervision.observation subscription.mode exit))

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.Fiber.observe_live :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription), Effect4.Supervision.Fiber.Valid f -> Effect4.Supervision.Fiber.published? f = none -> subscription.key ∉ f.subscriptions.map Effect4.Supervision.Subscription.key -> Effect4.Supervision.Fiber.observe f subscription = .ok ({f with subscriptions := f.subscriptions ++ [subscription]}, .waiting subscription.key))

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.Fiber.observe_duplicate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription), Effect4.Supervision.Fiber.Valid f -> Effect4.Supervision.Fiber.published? f = none -> subscription.key ∈ f.subscriptions.map Effect4.Supervision.Subscription.key -> Effect4.Supervision.Fiber.observe f subscription = .error (.duplicateSubscription subscription.key))

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.Fiber.cancel_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (key : Nat), Effect4.Supervision.Fiber.cancel f key = {f with subscriptions := f.subscriptions.filter (fun subscription => decide (subscription.key ≠ key))})

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.Fiber.cancel_membership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (key : Nat) (subscription : Effect4.Supervision.Subscription), subscription ∈ (Effect4.Supervision.Fiber.cancel f key).subscriptions ↔ subscription ∈ f.subscriptions ∧ subscription.key ≠ key)

/- Required production docstring census tags: fork.await fork.join rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.Fiber.publish_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.publish f exit = ({f with core := {f.core with status := .done, terminal := some exit, interruptPending := false, cleanup := .done, cleanupCount := 1}, children := [], subscriptions := []}, f.subscriptions.map (fun subscription => (subscription.key, Effect4.Supervision.observation subscription.mode exit))))

/- Required production docstring census tags: fork.await fork.join -/
#check (@Effect4.Supervision.Fiber.publish_valid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.Valid (Effect4.Supervision.Fiber.publish f exit).1)

/- Required production docstring census tags: fork.interrupt interrupt.accumulate -/
#check (@Effect4.Supervision.interruptCause_eq :
  forall {ε δ ι α : Type u} (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α), (Effect4.Supervision.interruptCause encode requester annotations : Effect4.Cause ε δ ι α) = Effect4.Cause.annotate (Effect4.Cause.interrupt (requester.map encode)) annotations false)

/- Required production docstring census tags: fork.interrupt interrupt.accumulate -/
#check (@Effect4.Supervision.Fiber.recordInterrupt_done :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? f = some exit -> Effect4.Supervision.Fiber.recordInterrupt encode requester annotations f = f)

/- Required production docstring census tags: interrupt.accumulate fork.interrupt -/
#check (@Effect4.Supervision.Fiber.recordInterrupt_live :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.Fiber.published? f = none -> Effect4.Supervision.Fiber.recordInterrupt encode requester annotations f = {f with interrupted := some (match f.interrupted with | none => Effect4.Supervision.interruptCause encode requester annotations | some previous => Effect4.Cause.combine previous (Effect4.Supervision.interruptCause encode requester annotations))})

/- Required production docstring census tags: fork.interrupt interrupt.accumulate -/
#check (@Effect4.Supervision.Fiber.recordInterrupt_core :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Effect4.Supervision.Fiber χ β ε δ ι α), (Effect4.Supervision.Fiber.recordInterrupt encode requester annotations f).core = f.core)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.initialFiber_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (mode : Effect4.Supervision.MaskMode), Effect4.Supervision.initialFiber parent child mode = { core := {id := child, status := .runnable, terminal := none, mask := Effect4.Supervision.MaskMode.select mode parent.core.mask, interruptPending := false, cleanup := .notStarted, cleanupCount := 0}, context := parent.context, children := [], subscriptions := [], interrupted := none })

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.initialFiber_valid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (mode : Effect4.Supervision.MaskMode), Effect4.Supervision.Fiber.Valid (Effect4.Supervision.initialFiber parent child mode))

/- Required production docstring census tags: fork.unsafe rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.commitFork_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent initial child : Effect4.Supervision.Fiber χ β ε δ ι α) (daemon : Bool) (events : List Effect4.Supervision.ForkEvent), Effect4.Supervision.commitFork g parent initial child daemon events = { globals := g, parent := if daemon = false ∧ Effect4.Supervision.Fiber.published? child = none then Effect4.Supervision.Fiber.addChild parent child.core.id else parent, initial := initial, child := child, events := events ++ (if daemon = false ∧ Effect4.Supervision.Fiber.published? child = none then [.registered parent.core.id child.core.id] else []), removeFromParent := if daemon = false ∧ Effect4.Supervision.Fiber.published? child = none then some parent.core.id else none })

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_duplicate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α), child ∈ g.allocated -> Effect4.Supervision.forkUnsafe g parent child options start = .error (.duplicateFiber child))

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_deferred :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) , child ∉ g.allocated -> options.startImmediately = false -> Effect4.Supervision.forkUnsafe g parent child options .deferred = .ok (Effect4.Supervision.commitFork (Effect4.Supervision.Globals.allocate g child) parent (Effect4.Supervision.initialFiber parent child options.maskMode) (Effect4.Supervision.initialFiber parent child options.maskMode) options.daemon [.scheduled child 0]))

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_wrong_deferred :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) , child ∉ g.allocated -> options.startImmediately = true -> Effect4.Supervision.forkUnsafe g parent child options .deferred = .error .wrongStartMode)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_wrong_immediate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongStartMode)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_wrong_identity :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id ≠ child -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongChildIdentity)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_wrong_parent :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id ≠ parent.core.id -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongParentIdentity)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_invalid_child :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.valid? after = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error (.invalidFiber child))

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_invalid_parent :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.valid? postParent = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error (.invalidFiber parent.core.id))

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_invalid_globals :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.extends? (Effect4.Supervision.Globals.allocate g child) postGlobals = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidStartGlobals)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_invalid_ownership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.Extends (Effect4.Supervision.Globals.allocate g child) postGlobals -> Effect4.Supervision.Globals.ownsChildren? postGlobals postParent = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidParentOwnership)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_invalid_child_ownership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.Extends (Effect4.Supervision.Globals.allocate g child) postGlobals -> Effect4.Supervision.Globals.OwnsChildren postGlobals postParent -> Effect4.Supervision.Globals.ownsChildren? postGlobals after = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidChildOwnership)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_immediate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.Extends (Effect4.Supervision.Globals.allocate g child) postGlobals -> Effect4.Supervision.Globals.OwnsChildren postGlobals postParent -> Effect4.Supervision.Globals.OwnsChildren postGlobals after -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .ok (Effect4.Supervision.commitFork postGlobals postParent (Effect4.Supervision.initialFiber parent child options.maskMode) after options.daemon [.evaluated child]))

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_fresh :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> child ∉ g.allocated)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_allocated_nodup :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), Effect4.Supervision.Globals.Valid g -> Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> Effect4.Supervision.Globals.Valid result.globals)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.forkUnsafe_child_valid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> Effect4.Supervision.Fiber.Valid result.child)

/- Required production docstring census tags: fork.child rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.forkUnsafe_parent_children_nodup :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), parent.children.Nodup -> Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> result.parent.children.Nodup)

/- Required production docstring census tags: fork.child rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.forkChild_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α), Effect4.Supervision.forkChild g parent child options start = Effect4.Supervision.forkUnsafe (Effect4.Supervision.Globals.install g) parent child {options with daemon := false} start)

/- Required production docstring census tags: fork.detach rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.forkDetach_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α), Effect4.Supervision.forkDetach g parent child options start = Effect4.Supervision.forkUnsafe g parent child {options with daemon := true} start)

/- Required production docstring census tags: fork.unsafe fork.child -/
#check (@Effect4.Supervision.commitFork_done_untracked :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent initial child : Effect4.Supervision.Fiber χ β ε δ ι α) (daemon : Bool) (events : List Effect4.Supervision.ForkEvent) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? child = some exit -> (Effect4.Supervision.commitFork g parent initial child daemon events).parent = parent ∧ (Effect4.Supervision.commitFork g parent initial child daemon events).removeFromParent = none ∧ (Effect4.Supervision.commitFork g parent initial child daemon events).events = events)

/- Required production docstring census tags: fork.detach rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.commitFork_daemon_untracked :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent initial child : Effect4.Supervision.Fiber χ β ε δ ι α) (events : List Effect4.Supervision.ForkEvent), (Effect4.Supervision.commitFork g parent initial child true events).parent = parent ∧ (Effect4.Supervision.commitFork g parent initial child true events).removeFromParent = none ∧ (Effect4.Supervision.commitFork g parent initial child true events).events = events)

/- Required production docstring census tags: fork.unsafe -/
#check (@Effect4.Supervision.Globals.allocate_eq :
  forall (g : Effect4.Supervision.Globals) (child : Effect4.FiberId), Effect4.Supervision.Globals.allocate g child = {g with allocated := g.allocated ++ [child]})

/- Required production docstring census tags: fork.unsafe fork.child -/
#check (@Effect4.Supervision.Globals.extends_iff :
  forall before after : Effect4.Supervision.Globals, Effect4.Supervision.Globals.Extends before after ↔ after.allocated.take before.allocated.length = before.allocated ∧ (before.middlewareInstalled = true -> after.middlewareInstalled = true) ∧ after.allocated.Nodup)

/- Required production docstring census tags: fork.unsafe fork.child -/
#check (@Effect4.Supervision.Globals.extends?_iff :
  forall before after : Effect4.Supervision.Globals, Effect4.Supervision.Globals.extends? before after = true ↔ Effect4.Supervision.Globals.Extends before after)

/- Required production docstring census tags: fork.unsafe fork.child -/
#check (@Effect4.Supervision.Globals.ownsChildren?_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (f : Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.Globals.ownsChildren? g f = true ↔ Effect4.Supervision.Globals.OwnsChildren g f)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.WaitState.begin_eq :
  forall {τ : Type u}, forall (targets : List Effect4.FiberId) (result : τ), Effect4.Supervision.WaitState.begin targets result = {targets := targets, published := [], result := result})

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.WaitState.pending_eq :
  forall {τ : Type u}, forall s : Effect4.Supervision.WaitState τ, Effect4.Supervision.WaitState.pending s = s.targets.filter (fun id => decide (id ∉ s.published)))

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.WaitState.ready_iff :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (result : τ), Effect4.Supervision.WaitState.ready? s = some result ↔ Effect4.Supervision.WaitState.pending s = [] ∧ s.result = result)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.WaitState.ready_publications :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (result : τ), Effect4.Supervision.WaitState.ready? s = some result -> ∀ child, child ∈ s.targets -> child ∈ s.published)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.WaitState.observe_pending :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId), child ∈ Effect4.Supervision.WaitState.pending s -> Effect4.Supervision.WaitState.observe s child = .ok {s with published := s.published ++ [child]})

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.WaitState.observe_unknown :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId), child ∉ Effect4.Supervision.WaitState.pending s -> Effect4.Supervision.WaitState.observe s child = .error (.unknownPublication child))

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.WaitState.observe_pending_membership :
  forall {τ : Type u}, forall (s after : Effect4.Supervision.WaitState τ) (child other : Effect4.FiberId), Effect4.Supervision.WaitState.observe s child = .ok after -> (other ∈ Effect4.Supervision.WaitState.pending after ↔ other ∈ Effect4.Supervision.WaitState.pending s ∧ other ≠ child))

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitStep_iff :
  forall {τ : Type u}, forall (before after : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId), Effect4.Supervision.WaitStep before child after ↔ Effect4.Supervision.WaitState.observe before child = .ok after)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitRuns_iff :
  forall {τ : Type u}, forall (initial : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId) (result : Effect4.Supervision.ReplayResult (Effect4.Supervision.WaitState τ) τ), Effect4.Supervision.WaitRuns initial tape result ↔ result = Effect4.Supervision.waitReplay initial tape)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.race-all -/
#check (@Effect4.Supervision.ReplayResult.state_done :
  forall {σ : Type u} {τ : Type v} (state : σ) (result : τ), Effect4.Supervision.ReplayResult.state (Effect4.Supervision.ReplayResult.done state result) = state)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.race-all -/
#check (@Effect4.Supervision.ReplayResult.state_frontier :
  forall {σ : Type u} {τ : Type v} (state : σ), Effect4.Supervision.ReplayResult.state (Effect4.Supervision.ReplayResult.frontier state : Effect4.Supervision.ReplayResult σ τ) = state)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.race-all -/
#check (@Effect4.Supervision.ReplayResult.state_refused :
  forall {σ : Type u} {τ : Type v} (state : σ) (reason : Effect4.Supervision.Refusal), Effect4.Supervision.ReplayResult.state (Effect4.Supervision.ReplayResult.refused state reason : Effect4.Supervision.ReplayResult σ τ) = state)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitReplay_ready :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (result : τ) (tape : List Effect4.FiberId), Effect4.Supervision.WaitState.ready? s = some result -> Effect4.Supervision.waitReplay s tape = .done s result)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitReplay_frontier :
  forall {τ : Type u}, forall s : Effect4.Supervision.WaitState τ, Effect4.Supervision.WaitState.ready? s = none -> Effect4.Supervision.waitReplay s [] = .frontier s)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitReplay_cons_ok :
  forall {τ : Type u}, forall (s after : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId) (tape : List Effect4.FiberId), Effect4.Supervision.WaitState.ready? s = none -> Effect4.Supervision.WaitState.observe s child = .ok after -> Effect4.Supervision.waitReplay s (child :: tape) = Effect4.Supervision.waitReplay after tape)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitReplay_cons_error :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId) (tape : List Effect4.FiberId) (reason : Effect4.Supervision.Refusal), Effect4.Supervision.WaitState.ready? s = none -> Effect4.Supervision.WaitState.observe s child = .error reason -> Effect4.Supervision.waitReplay s (child :: tape) = .refused s reason)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.wait_fixedTape_deterministic :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId) (left right : Effect4.Supervision.ReplayResult (Effect4.Supervision.WaitState τ) τ), Effect4.Supervision.WaitRuns s tape left -> Effect4.Supervision.WaitRuns s tape right -> left = right)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitReplay_done_ready :
  forall {τ : Type u}, forall (s after : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId) (result : τ), Effect4.Supervision.waitReplay s tape = .done after result -> Effect4.Supervision.WaitState.ready? after = some result)

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.waitReplay_frame :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId), let after := Effect4.Supervision.ReplayResult.state (Effect4.Supervision.waitReplay s tape); after.targets = s.targets ∧ after.result = s.result ∧ (∀ child, child ∈ after.published -> child ∈ s.published ++ tape))

/- Required production docstring census tags: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
#check (@Effect4.Supervision.wait_two_publications :
  forall {τ : Type u}, forall (left right : Effect4.FiberId) (result : τ), left ≠ right -> Effect4.Supervision.waitReplay (Effect4.Supervision.WaitState.begin [left, right] result) [left, right] = .done {targets := [left, right], published := [left, right], result := result} result)

/- Required production docstring census tags: fork.child rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.beginParentExit_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.beginParentExit g parent exit = Effect4.Supervision.WaitState.begin (if g.middlewareInstalled then parent.children else []) exit)

/- Required production docstring census tags: rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.parentExitView_waiting :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)), Effect4.Supervision.WaitState.ready? wait = none -> Effect4.Supervision.parentExitView parent wait = {parent with core := {parent.core with status := .finalizing, terminal := some wait.result, interruptPending := false, cleanup := .pending, cleanupCount := 0}, children := Effect4.Supervision.WaitState.pending wait})

/- Required production docstring census tags: rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.parentExitView_ready :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.WaitState.ready? wait = some exit -> Effect4.Supervision.parentExitView parent wait = (Effect4.Supervision.Fiber.publish parent exit).1)

/- Required production docstring census tags: rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.parentExitView_not_published_while_waiting :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)), Effect4.Supervision.WaitState.ready? wait = none -> Effect4.Supervision.Fiber.published? (Effect4.Supervision.parentExitView parent wait) = none)

/- Required production docstring census tags: rule.children-interrupted-after-exit -/
#check (@Effect4.Supervision.parentExitView_publication_requires_children :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? (Effect4.Supervision.parentExitView parent wait) = some exit -> ∀ child, child ∈ wait.targets -> child ∈ wait.published)

/- Required production docstring census tags: fork.await-all-children -/
#check (@Effect4.Supervision.newChildren_eq :
  forall initial current : List Effect4.FiberId, Effect4.Supervision.newChildren initial current = current.filter (fun child => decide (child ∉ initial)))

/- Required production docstring census tags: fork.await-all-children -/
#check (@Effect4.Supervision.newChildren_membership :
  forall (initial current : List Effect4.FiberId) (child : Effect4.FiberId), child ∈ Effect4.Supervision.newChildren initial current ↔ child ∈ current ∧ child ∉ initial)

/- Required production docstring census tags: fork.await-all-children -/
#check (@Effect4.Supervision.awaitAllChildren_eq :
  forall initial current : List Effect4.FiberId, Effect4.Supervision.awaitAllChildren initial current = Effect4.Supervision.WaitState.begin (Effect4.Supervision.newChildren initial current) ())

/- Required production docstring census tags: fork.interrupt-all fork.interrupt -/
#check (@Effect4.Supervision.interruptAllRequests_eq :
  forall targets : List Effect4.FiberId, Effect4.Supervision.interruptAllRequests targets = targets.map Effect4.Supervision.InterruptAction.request ++ [.awaitAll targets])

/- Required production docstring census tags: fork.interrupt-all fork.interrupt -/
#check (@Effect4.Supervision.interruptAllWait_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall fibers : List (Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.interruptAllWait fibers = {targets := fibers.map (fun f => f.core.id), published := (fibers.filter (fun f => (Effect4.Supervision.Fiber.published? f).isSome)).map (fun f => f.core.id), result := ()})

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.bindScope_invalid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.valid? child = false -> Effect4.Supervision.bindScope mode parent child scope key = .error (.invalidFiber child.core.id))

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.bindScope_done :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = some exit -> Effect4.Supervision.bindScope mode parent child scope key = .ok {scope := scope, observerKey := none, interruptor := none})

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.bindScope_closed :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = none -> scope.isClosed = true -> Effect4.Supervision.bindScope mode parent child scope key = .ok {scope := scope, observerKey := none, interruptor := some (if mode = .forkIn then parent else child.core.id)})

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.bindScope_duplicate_key :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = none -> scope.isClosed = false -> (ULift.up key : ULift.{u} Nat) ∈ scope.finalizerKeys -> Effect4.Supervision.bindScope mode parent child scope key = .error (.duplicateScopeKey key))

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.bindScope_open :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = none -> scope.isClosed = false -> (ULift.up key : ULift.{u} Nat) ∉ scope.finalizerKeys -> Effect4.Supervision.bindScope mode parent child scope key = .ok {scope := scope.addUnsafe (ULift.up key) (ULift.up {child := child.core.id, skipSelf := decide (mode = .forkIn)}), observerKey := some key, interruptor := none})

/- Required production docstring census tags: fork.scoped -/
#check (@Effect4.Supervision.forkScopedBinding_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat), Effect4.Supervision.forkScopedBinding parent child scope key = Effect4.Supervision.bindScope .forkIn parent child scope key)

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.scopeFinalizerInterruptor_eq :
  forall (finalizer : Effect4.Supervision.ScopeFinalizer) (current : Effect4.FiberId), Effect4.Supervision.scopeFinalizerInterruptor finalizer current = if finalizer.skipSelf = true ∧ current = finalizer.child then none else some current)

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.scopeFinalizer_self_guard :
  forall child : Effect4.FiberId, Effect4.Supervision.scopeFinalizerInterruptor {child := child, skipSelf := true} child = none ∧ Effect4.Supervision.scopeFinalizerInterruptor {child := child, skipSelf := false} child = some child)

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.scopeObserver_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat), Effect4.Supervision.scopeObserver scope key = scope.removeUnsafe (ULift.up key))

/- Required production docstring census tags: fork.in fork.fiber-run-in -/
#check (@Effect4.Supervision.scopeObserver_key_membership :
  forall {β : Type v} {ε δ ι α : Type u}, forall (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key other : Nat), (ULift.up other : ULift.{u} Nat) ∈ (Effect4.Supervision.scopeObserver scope key).finalizerKeys ↔ (ULift.up other : ULift.{u} Nat) ∈ scope.finalizerKeys ∧ other ≠ key)

/- Required production docstring census tags: fork.race-all rule.only-fork-child-tracks -/
#check (@Effect4.Supervision.raceForkOptions_eq :
  Effect4.Supervision.raceForkOptions = {startImmediately := true, daemon := true, maskMode := .interruptible})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceCleanupMask_eq :
  Effect4.Supervision.raceCleanupMask = Effect4.InterruptMask.masked)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.RaceAllState.initial_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (Effect4.Supervision.RaceAllState.initial entrants : Effect4.Supervision.RaceAllState β ε δ ι α) = {unstarted := entrants, starting := none, live := [], remaining := entrants.length, failures := [], winner := none, accepted := none, cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceAllAdmit_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (Effect4.Supervision.raceAllAdmit entrants : Except Effect4.Supervision.Refusal (Effect4.Supervision.RaceAllState β ε δ ι α)) = if entrants.Nodup then .ok (Effect4.Supervision.RaceAllState.initial entrants) else .error .duplicateEntrant)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.RaceAllState.result_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, Effect4.Supervision.RaceAllState.result? s = if s.starting.isSome then none else if s.cleanupNeeded = false then s.accepted else if s.cleanupRequested = true ∧ (s.cleanup.bind Effect4.Supervision.WaitState.ready?).isSome = true then s.accepted else none)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceComplete_unknown :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> Effect4.Supervision.raceComplete s child exit = s)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceComplete_after_accepted :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit accepted : Effect4.Exit β ε δ ι α), child ∈ s.live -> s.accepted = some accepted -> Effect4.Supervision.raceComplete s child exit = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ exit.causeReasons, cleanup := s.cleanup.map (fun wait => if child ∈ Effect4.Supervision.WaitState.pending wait then {wait with published := wait.published ++ [child]} else wait)})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceComplete_success :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (value : β), child ∈ s.live -> s.accepted = none -> Effect4.Supervision.raceComplete s child (.success value) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, winner := some (child, value), accepted := some (.success value), cleanupNeeded := !(s.live.filter (fun id => decide (id ≠ child))).isEmpty, requests := [], cleanup := none, cleanupRequested := false})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceComplete_failure_last :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> s.remaining ≤ 1 -> Effect4.Supervision.raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons, accepted := some (.failure ⟨s.failures ++ cause.reasons⟩), cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceComplete_failure_pending :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> 1 < s.remaining -> Effect4.Supervision.raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_begin_blocked :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.accepted.isSome = true ∨ s.starting.isSome = true -> Effect4.Supervision.raceStep s .beginLaunch = .error .wrongRacePhase)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_begin_empty :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.accepted = none -> s.starting = none -> s.unstarted = [] -> Effect4.Supervision.raceStep s .beginLaunch = .error .noEntrant)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_begin :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (rest : List Effect4.FiberId), s.accepted = none -> s.starting = none -> s.unstarted = child :: rest -> Effect4.Supervision.raceStep s .beginLaunch = .ok {s with unstarted := rest, starting := some child})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_finish_missing :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Option (Effect4.Exit β ε δ ι α)), s.starting = none -> Effect4.Supervision.raceStep s (.finishLaunch exit) = .error .wrongRacePhase)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_finish_duplicate :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Option (Effect4.Exit β ε δ ι α)), s.starting = some child -> child ∈ s.live -> Effect4.Supervision.raceStep s (.finishLaunch exit) = .error .duplicateEntrant)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_finish_live :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId), s.starting = some child -> child ∉ s.live -> Effect4.Supervision.raceStep s (.finishLaunch none) = .ok {s with starting := none, live := s.live ++ [child]})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_finish_done :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), s.starting = some child -> child ∉ s.live -> Effect4.Supervision.raceStep s (.finishLaunch (some exit)) = .ok (Effect4.Supervision.raceComplete {s with starting := none, live := s.live ++ [child]} child exit))

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_complete :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∈ s.live -> Effect4.Supervision.raceStep s (.complete child exit) = .ok (Effect4.Supervision.raceComplete s child exit))

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_complete_unknown :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> Effect4.Supervision.raceStep s (.complete child exit) = .error (.unknownEntrant child))

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_beginCleanup :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), s.starting = none -> s.accepted = some exit -> s.cleanupNeeded = true -> s.cleanup = none -> Effect4.Supervision.raceStep s .beginCleanup = .ok {s with requests := s.live, cleanup := some (Effect4.Supervision.WaitState.begin s.live exit), cleanupRequested := s.live.isEmpty})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_beginCleanup_blocked :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.starting.isSome = true ∨ s.accepted = none ∨ s.cleanupNeeded = false ∨ s.cleanup.isSome = true -> Effect4.Supervision.raceStep s .beginCleanup = .error .wrongRacePhase)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_requestNext :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (rest : List Effect4.FiberId) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)), s.cleanup = some wait -> s.cleanupRequested = false -> s.requests = child :: rest -> Effect4.Supervision.raceStep s .requestNext = .ok {s with requests := rest, cleanupRequested := rest.isEmpty})

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_requestNext_blocked :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.cleanup = none ∨ s.cleanupRequested = true ∨ s.requests = [] -> Effect4.Supervision.raceStep s .requestNext = .error .wrongRacePhase)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceStep_iff :
  forall {β : Type v} {ε δ ι α : Type u}, forall (before after : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α), Effect4.Supervision.RaceStep before decision after ↔ Effect4.Supervision.raceStep before decision = .ok after)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceRuns_iff :
  forall {β : Type v} {ε δ ι α : Type u}, forall (initial : Effect4.Supervision.RaceAllState β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)) (result : Effect4.Supervision.ReplayResult (Effect4.Supervision.RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α)), Effect4.Supervision.RaceRuns initial tape result ↔ result = Effect4.Supervision.raceReplay initial tape)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceReplay_ready :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)), Effect4.Supervision.RaceAllState.result? s = some exit -> Effect4.Supervision.raceReplay s tape = .done s exit)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceReplay_frontier :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, Effect4.Supervision.RaceAllState.result? s = none -> Effect4.Supervision.raceReplay s [] = .frontier s)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceReplay_cons_ok :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s after : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)), Effect4.Supervision.RaceAllState.result? s = none -> Effect4.Supervision.raceStep s decision = .ok after -> Effect4.Supervision.raceReplay s (decision :: tape) = Effect4.Supervision.raceReplay after tape)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.raceReplay_cons_error :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)) (reason : Effect4.Supervision.Refusal), Effect4.Supervision.RaceAllState.result? s = none -> Effect4.Supervision.raceStep s decision = .error reason -> Effect4.Supervision.raceReplay s (decision :: tape) = .refused s reason)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.race_fixedTape_deterministic :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)) (left right : Effect4.Supervision.ReplayResult (Effect4.Supervision.RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α)), Effect4.Supervision.RaceRuns s tape left -> Effect4.Supervision.RaceRuns s tape right -> left = right)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.race_first_accepted_stable :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s after : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), s.accepted = some exit -> Effect4.Supervision.raceStep s decision = .ok after -> after.accepted = some exit)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.race_result_requires_start_finished :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.RaceAllState.result? s = some exit -> s.starting = none ∧ s.accepted = some exit)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.race_cleanup_result_requires_publications :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.RaceAllState.result? s = some exit -> s.cleanupNeeded = true -> s.cleanupRequested = true ∧ ∃ wait, s.cleanup = some wait ∧ ∀ child, child ∈ wait.targets -> child ∈ wait.published)

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.race_empty_frontier :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.raceReplay (Effect4.Supervision.RaceAllState.initial [] : Effect4.Supervision.RaceAllState β ε δ ι α) [] = .frontier (Effect4.Supervision.RaceAllState.initial []))

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.race_single_success :
  forall {β : Type v} {ε δ ι α : Type u}, forall (child : Effect4.FiberId) (value : β), ∃ after, Effect4.Supervision.raceReplay (Effect4.Supervision.RaceAllState.initial [child] : Effect4.Supervision.RaceAllState β ε δ ι α) [.beginLaunch, .finishLaunch (some (.success value))] = .done after (.success value))

/- Required production docstring census tags: fork.race-all -/
#check (@Effect4.Supervision.race_two_failures :
  forall {β : Type v} {ε δ ι α : Type u}, forall (left right : Effect4.FiberId) (first second : Effect4.Cause ε δ ι α), left ≠ right -> ∃ after, Effect4.Supervision.raceReplay (Effect4.Supervision.RaceAllState.initial [left, right] : Effect4.Supervision.RaceAllState β ε δ ι α) [.beginLaunch, .finishLaunch (some (.failure first)), .beginLaunch, .finishLaunch (some (.failure second))] = .done after (.failure ⟨first.reasons ++ second.reasons⟩))

end Effect4Test.Concurrency.FiberSupervisionContract
