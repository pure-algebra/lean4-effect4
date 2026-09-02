import Effect4.Concurrency.Fiber
import Effect4.Runtime.Scope
/-!
# Fork and supervision over observed runtime boundaries

The frozen packet is `test/contracts/fiber-supervision.contract.md`; dispositions,
shapes, and open source interpretations are owned by `docs/SUPERVISION-DAG.md`.
All program-facing content is data over admitted alphabets. Immediate execution,
interrupt delivery, and actual publication enter as observations. These controllers
do not implement the Effect continuation machine or establish host equivalence.
-/
set_option autoImplicit false
namespace Effect4.Supervision
universe u v w
inductive MaskMode | interruptible | uninterruptible | inherit
  deriving DecidableEq
structure ForkOptions where
  startImmediately : Bool
  daemon : Bool
  maskMode : MaskMode
  deriving DecidableEq
structure Globals where
  allocated : List Effect4.FiberId
  middlewareInstalled : Bool
  deriving DecidableEq
inductive ObserverMode | awaitValue | joinEffect
  deriving DecidableEq
structure Subscription where
  key : Nat
  mode : ObserverMode
  deriving DecidableEq
structure Fiber (χ : Type u) (β : Type v) (ε δ ι α : Type u) where
  core : Effect4.FiberState (Effect4.Exit β ε δ ι α)
  context : χ
  children : List Effect4.FiberId
  subscriptions : List Subscription
  interrupted : Option (Effect4.Cause ε δ ι α)
inductive Observation (β : Type v) (ε δ ι α : Type u)
  | waiting (key : Nat)
  | value (exit : Effect4.Exit β ε δ ι α)
  | effect (exit : Effect4.Exit β ε δ ι α)
inductive StartObservation (χ : Type u) (β : Type v) (ε δ ι α : Type u)
  | deferred
  | immediate (globals : Globals) (parent fiber : Fiber χ β ε δ ι α)
inductive ForkEvent
  | scheduled (child : Effect4.FiberId) (priority : Nat)
  | evaluated (child : Effect4.FiberId)
  | registered (parent child : Effect4.FiberId)
  deriving DecidableEq
structure ForkResult (χ : Type u) (β : Type v) (ε δ ι α : Type u) where
  globals : Globals
  parent : Fiber χ β ε δ ι α
  initial : Fiber χ β ε δ ι α
  child : Fiber χ β ε δ ι α
  events : List ForkEvent
  removeFromParent : Option Effect4.FiberId
inductive InterruptAction
  | request (target : Effect4.FiberId)
  | awaitAll (targets : List Effect4.FiberId)
  deriving DecidableEq
inductive Refusal
  | invalidFiber (id : Effect4.FiberId)
  | duplicateFiber (id : Effect4.FiberId)
  | wrongStartMode
  | wrongChildIdentity
  | wrongParentIdentity
  | invalidStartGlobals
  | invalidParentOwnership
  | invalidChildOwnership
  | duplicateSubscription (key : Nat)
  | unknownPublication (id : Effect4.FiberId)
  | duplicateScopeKey (key : Nat)
  | duplicateEntrant
  | noEntrant
  | wrongRacePhase
  | unknownEntrant (id : Effect4.FiberId)
  deriving DecidableEq
structure WaitState (τ : Type u) where
  targets : List Effect4.FiberId
  published : List Effect4.FiberId
  result : τ
inductive ReplayResult (σ : Type u) (τ : Type v)
  | done (state : σ) (result : τ)
  | frontier (state : σ)
  | refused (state : σ) (reason : Refusal)
inductive ScopeMode | forkIn | fiberRunIn
  deriving DecidableEq
structure ScopeFinalizer where
  child : Effect4.FiberId
  skipSelf : Bool
  deriving DecidableEq
structure ScopeBinding (β : Type v) (ε δ ι α : Type u) where
  scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α
  observerKey : Option Nat
  interruptor : Option Effect4.FiberId
structure RaceAllState (β : Type v) (ε δ ι α : Type u) where
  unstarted : List Effect4.FiberId
  starting : Option Effect4.FiberId
  live : List Effect4.FiberId
  remaining : Nat
  failures : List (Effect4.Reason ε δ ι α)
  winner : Option (Effect4.FiberId × β)
  accepted : Option (Effect4.Exit β ε δ ι α)
  cleanupNeeded : Bool
  requests : List Effect4.FiberId
  cleanup : Option (WaitState (Effect4.Exit β ε δ ι α))
  cleanupRequested : Bool
inductive RaceAllDecision (β : Type v) (ε δ ι α : Type u)
  | beginLaunch
  | finishLaunch (immediateExit : Option (Effect4.Exit β ε δ ι α))
  | complete (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α)
  | beginCleanup
  | requestNext


variable {χ : Type u} {β : Type v} {ε δ ι α : Type u}

/-- Select the canonical interrupt mask at the fork boundary. -/
def MaskMode.select : MaskMode → InterruptMask → InterruptMask
  | .interruptible, _ => .unmasked
  | .uninterruptible, _ => .masked
  | .inherit, mask => mask

/-- Install the shared child-interruption middleware. -/
def Globals.install (g : Globals) : Globals := {g with middlewareInstalled := true}

/-- Allocation uniqueness in the supplied global view. -/
def Globals.Valid (g : Globals) : Prop := g.allocated.Nodup

/-- Record an allocation; admission checks freshness separately. -/
def Globals.allocate (g : Globals) (child : FiberId) : Globals :=
  {g with allocated := g.allocated ++ [child]}

/-- Startup may extend allocations and install middleware, never retract either. -/
def Globals.Extends (before after : Globals) : Prop :=
  after.allocated.take before.allocated.length = before.allocated ∧
  (before.middlewareInstalled = true → after.middlewareInstalled = true) ∧
  after.allocated.Nodup

/-- Decidable observed-world extension, without inspecting any user payload. -/
def Globals.extends? (before after : Globals) : Bool := decide (after.allocated.take before.allocated.length = before.allocated ∧
    (before.middlewareInstalled = true → after.middlewareInstalled = true) ∧ after.allocated.Nodup)

/-- The observed fiber and all of its direct children have allocated identities. -/
def Globals.OwnsChildren (g : Globals) (f : Fiber χ β ε δ ι α) : Prop :=
  f.core.id ∈ g.allocated ∧ ∀ child, child ∈ f.children → child ∈ g.allocated

/-- Finite allocation checks for both the parent and the started child. -/
def Globals.ownsChildren? (g : Globals) (f : Fiber χ β ε δ ι α) : Bool :=
  decide (f.core.id ∈ g.allocated) && f.children.all (fun child => decide (child ∈ g.allocated))

/-- Local lifecycle validity, not the global Scheduler machine invariant. -/
def Fiber.Valid (f : Fiber χ β ε δ ι α) : Prop :=
  f.children.Nodup ∧ (f.subscriptions.map Subscription.key).Nodup ∧
  (FiberStatus.Active f.core.status → f.core.terminal = none ∧
    f.core.cleanup = .notStarted ∧ f.core.cleanupCount = 0) ∧
  (f.core.status = .finalizing → f.core.terminal.isSome = true ∧
    f.core.cleanup = .pending ∧ f.core.cleanupCount = 0) ∧
  (f.core.status = .done → f.core.terminal.isSome = true ∧
    f.core.cleanup = .done ∧ f.core.cleanupCount = 1)

/-- Check only finite control data and terminal presence, not terminal equality. -/
def Fiber.valid? (f : Fiber χ β ε δ ι α) : Bool :=
  decide f.children.Nodup && decide (f.subscriptions.map Subscription.key).Nodup &&
  match f.core.status with
  | .runnable | .running | .waiting _ =>
    f.core.terminal.isNone && decide (f.core.cleanup = .notStarted) && decide (f.core.cleanupCount = 0)
  | .finalizing =>
    f.core.terminal.isSome && decide (f.core.cleanup = .pending) && decide (f.core.cleanupCount = 0)
  | .done =>
    f.core.terminal.isSome && decide (f.core.cleanup = .done) && decide (f.core.cleanupCount = 1)

/-- Exact projection to the existing canonical FiberState owner. -/
def Fiber.toFiberState (f : Fiber χ β ε δ ι α) : FiberState (Exit β ε δ ι α) := f.core

/-- A local body exit is observable only after actual terminal publication. -/
def Fiber.published? (f : Fiber χ β ε δ ι α) : Option (Exit β ε δ ι α) :=
  if f.core.status = .done then f.core.terminal else none

/-- Append a direct child at most once, retaining registration order. -/
def Fiber.addChild (f : Fiber χ β ε δ ι α) (child : FiberId) : Fiber χ β ε δ ι α :=
  {f with children := if child ∈ f.children then f.children else f.children ++ [child]}

/-- Completion removes exactly the child identity. -/
def Fiber.removeChild (f : Fiber χ β ε δ ι α) (child : FiberId) : Fiber χ β ε δ ι α :=
  {f with children := f.children.filter (fun id => decide (id ≠ child))}

/-- Await returns an Exit as a value; join resumes it as an effect. -/
def observation (mode : ObserverMode) (exit : Exit β ε δ ι α) : Observation β ε δ ι α :=
  match mode with
  | .awaitValue => .value exit
  | .joinEffect => .effect exit

/-- Observe a valid published view or register a fresh cancellation key. -/
def Fiber.observe (f : Fiber χ β ε δ ι α) (subscription : Subscription) :
    Except Refusal (Fiber χ β ε δ ι α × Observation β ε δ ι α) :=
  if f.valid? then
    match f.published? with
    | some exit => .ok (f, observation subscription.mode exit)
    | none =>
      if subscription.key ∈ f.subscriptions.map Subscription.key then
        .error (.duplicateSubscription subscription.key)
      else .ok ({f with subscriptions := f.subscriptions ++ [subscription]}, .waiting subscription.key)
  else .error (.invalidFiber f.core.id)

/-- Remove the keyed subscription, preserving other observers in order. -/
def Fiber.cancel (f : Fiber χ β ε δ ι α) (key : Nat) : Fiber χ β ε δ ι α :=
  {f with subscriptions := f.subscriptions.filter (fun subscription => decide (subscription.key ≠ key))}

/-- Construct a terminal view from an externally justified publication.
This is not an admitted one-shot runtime transition or a proof that cleanup ran. -/
def Fiber.publish (f : Fiber χ β ε δ ι α) (exit : Exit β ε δ ι α) :
    Fiber χ β ε δ ι α × List (Nat × Observation β ε δ ι α) :=
  ({f with core := {f.core with status := .done, terminal := some exit, interruptPending := false, cleanup := .done, cleanupCount := 1}, children := [], subscriptions := []},
   f.subscriptions.map (fun subscription => (subscription.key, observation subscription.mode exit)))

/-- Encode explicit interruptor data in the canonical annotated Cause. -/
def interruptCause (encode : FiberId → ι) (requester : Option FiberId)
    (annotations : ReasonAnnotations α) : Cause ε δ ι α :=
  Cause.annotate (Cause.interrupt (requester.map encode)) annotations false

/-- Record the interrupt Cause only; execution and delivery are external boundaries. -/
def Fiber.recordInterrupt [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (encode : FiberId → ι) (requester : Option FiberId) (annotations : ReasonAnnotations α)
    (f : Fiber χ β ε δ ι α) : Fiber χ β ε δ ι α :=
  match f.published? with
  | some _ => f
  | none => {f with interrupted := some (match f.interrupted with
      | none => interruptCause encode requester annotations
      | some previous => Cause.combine previous (interruptCause encode requester annotations))}

/-- Capture inherited context and mask before any immediate startup execution. -/
def initialFiber (parent : Fiber χ β ε δ ι α) (child : FiberId) (mode : MaskMode) :
    Fiber χ β ε δ ι α :=
  {core := {id := child, status := .runnable, terminal := none, mask := mode.select parent.core.mask, interruptPending := false, cleanup := .notStarted, cleanupCount := 0}, context := parent.context, children := [], subscriptions := [], interrupted := none}

/-- Register only an unpublished non-daemon, against the observed post-start world. -/
def commitFork (g : Globals) (parent initial child : Fiber χ β ε δ ι α)
    (daemon : Bool) (events : List ForkEvent) : ForkResult χ β ε δ ι α :=
  {globals := g, parent := if daemon = false ∧ child.published? = none then parent.addChild child.core.id else parent, initial := initial, child := child, events := events ++ (if daemon = false ∧ child.published? = none then
     [.registered parent.core.id child.core.id] else []), removeFromParent := if daemon = false ∧ child.published? = none then some parent.core.id else none}

/-- Admit a fork boundary observation in the frozen guard order. -/
def forkUnsafe (g : Globals) (parent : Fiber χ β ε δ ι α) (child : FiberId)
    (options : ForkOptions) (start : StartObservation χ β ε δ ι α) :
    Except Refusal (ForkResult χ β ε δ ι α) :=
  if child ∈ g.allocated then .error (.duplicateFiber child) else
  match start with
  | .deferred =>
    if options.startImmediately then .error .wrongStartMode else
      .ok (commitFork (g.allocate child) parent (initialFiber parent child options.maskMode)
        (initialFiber parent child options.maskMode) options.daemon [.scheduled child 0])
  | .immediate postGlobals postParent after =>
    if options.startImmediately then
      if after.core.id = child then
        if postParent.core.id = parent.core.id then
          if after.valid? then
            if postParent.valid? then
              if (g.allocate child).extends? postGlobals then
                if postGlobals.ownsChildren? postParent then
                  if postGlobals.ownsChildren? after then
                    .ok (commitFork postGlobals postParent (initialFiber parent child options.maskMode)
                      after options.daemon [.evaluated child])
                  else .error .invalidChildOwnership
                else .error .invalidParentOwnership
              else .error .invalidStartGlobals
            else .error (.invalidFiber parent.core.id)
          else .error (.invalidFiber child)
        else .error .wrongParentIdentity
      else .error .wrongChildIdentity
    else .error .wrongStartMode

/-- Install global middleware and force direct-child supervision. -/
def forkChild (g : Globals) (parent : Fiber χ β ε δ ι α) (child : FiberId)
    (options : ForkOptions) (start : StartObservation χ β ε δ ι α) :
    Except Refusal (ForkResult χ β ε δ ι α) :=
  forkUnsafe g.install parent child {options with daemon := false} start

/-- Force a daemon without suppressing effects of its immediate startup. -/
def forkDetach (g : Globals) (parent : Fiber χ β ε δ ι α) (child : FiberId)
    (options : ForkOptions) (start : StartObservation χ β ε δ ι α) :
    Except Refusal (ForkResult χ β ε δ ι α) :=
  forkUnsafe g parent child {options with daemon := true} start

/-- Begin a wait with no publication assumptions. -/
def WaitState.begin {τ : Type u} (targets : List FiberId) (result : τ) : WaitState τ :=
  ⟨targets, [], result⟩

/-- Outstanding actual publications, retaining target order. -/
def WaitState.pending {τ : Type u} (s : WaitState τ) : List FiberId :=
  s.targets.filter (fun child => decide (child ∉ s.published))

/-- Return continuation data only after every target has published. -/
def WaitState.ready? {τ : Type u} (s : WaitState τ) : Option τ :=
  if s.pending = [] then some s.result else none

/-- Accept a pending publication; refuse an unknown or repeated one. -/
def WaitState.observe {τ : Type u} (s : WaitState τ) (child : FiberId) : Except Refusal (WaitState τ) :=
  if child ∈ s.pending then .ok {s with published := s.published ++ [child]}
  else .error (.unknownPublication child)

/-- The state reached at any controller boundary. -/
def ReplayResult.state {σ : Type u} {τ : Type v} : ReplayResult σ τ → σ
  | .done state _ | .frontier state | .refused state _ => state

/-- One admitted actual-publication decision. -/
def WaitStep {τ : Type u} (before : WaitState τ) (child : FiberId) (after : WaitState τ) : Prop :=
  before.observe child = .ok after

/-- Total replay of a finite publication tape; unanswered waits remain frontiers. -/
def waitReplay {τ : Type u} (s : WaitState τ) (tape : List FiberId) : ReplayResult (WaitState τ) τ :=
  match s.ready? with
  | some result => .done s result
  | none => match tape with
    | [] => .frontier s
    | child :: rest => match s.observe child with
      | .ok after => waitReplay after rest
      | .error reason => .refused s reason
termination_by structural tape

/-- Exact graph of finite replay on the fixed external publication tape. -/
def WaitRuns {τ : Type u} (s : WaitState τ) (tape : List FiberId)
    (result : ReplayResult (WaitState τ) τ) : Prop := result = waitReplay s tape

/-- Select children through the shared middleware for the successful wait continuation. -/
def beginParentExit (g : Globals) (parent : Fiber χ β ε δ ι α) (exit : Exit β ε δ ι α) :
    WaitState (Exit β ε δ ι α) :=
  WaitState.begin (if g.middlewareInstalled then parent.children else []) exit

/-- View of the successful parent wait with no intervening parent evaluation.
Further parent interruption may replace the body Exit before this boundary. -/
def parentExitView (parent : Fiber χ β ε δ ι α) (wait : WaitState (Exit β ε δ ι α)) :
    Fiber χ β ε δ ι α :=
  match wait.ready? with
  | some exit => (parent.publish exit).1
  | none => {parent with core := {parent.core with status := .finalizing, terminal := some wait.result, interruptPending := false, cleanup := .pending, cleanupCount := 0}, children := wait.pending}

/-- Children introduced since the captured initial child set. -/
def newChildren (initial current : List FiberId) : List FiberId :=
  current.filter (fun child => decide (child ∉ initial))

/-- Wait only for children introduced in the observed interval. -/
def awaitAllChildren (initial current : List FiberId) : WaitState Unit :=
  WaitState.begin (newChildren initial current) ()

/-- Call-plan order: request every target, then await the collected target list. -/
def interruptAllRequests (targets : List FiberId) : List InterruptAction :=
  targets.map InterruptAction.request ++ [.awaitAll targets]

/-- Build the wait from post-request views, allowing synchronous completion. -/
def interruptAllWait (fibers : List (Fiber χ β ε δ ι α)) : WaitState Unit :=
  {targets := fibers.map (fun f => f.core.id), published := (fibers.filter (fun f => f.published?.isSome)).map (fun f => f.core.id), result := ()}

/-- Attach a live child to the supplied post-start canonical scope. -/
def bindScope (mode : ScopeMode) (parent : FiberId) (child : Fiber χ β ε δ ι α)
    (scope : Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat) :
    Except Refusal (ScopeBinding β ε δ ι α) :=
  if child.valid? then
    match child.published? with
    | some _ => .ok ⟨scope, none, none⟩
    | none =>
      if scope.isClosed then
        .ok ⟨scope, none, some (if mode = .forkIn then parent else child.core.id)⟩
      else if (ULift.up key : ULift.{u} Nat) ∈ scope.finalizerKeys then
        .error (.duplicateScopeKey key)
      else .ok ⟨scope.addUnsafe (ULift.up key)
        (ULift.up {child := child.core.id, skipSelf := decide (mode = .forkIn)}), some key, none⟩
  else .error (.invalidFiber child.core.id)

/-- The ambient scope binding uses the same post-start forkIn policy. -/
def forkScopedBinding (parent : FiberId) (child : Fiber χ β ε δ ι α)
    (scope : Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat) :
    Except Refusal (ScopeBinding β ε δ ι α) := bindScope .forkIn parent child scope key

/-- forkIn guards self interruption; fiberRunIn does not. -/
def scopeFinalizerInterruptor (finalizer : ScopeFinalizer) (current : FiberId) : Option FiberId :=
  if finalizer.skipSelf = true ∧ current = finalizer.child then none else some current

/-- Completion removes the exact key used at finalizer registration. -/
def scopeObserver (scope : Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α)
    (key : Nat) : Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α :=
  scope.removeUnsafe (ULift.up key)

/-- Source raceAll starts immediate interruptible daemons. -/
def raceForkOptions : ForkOptions := ⟨true, true, .interruptible⟩

/-- The source cleanup continuation uses the canonical masked mode. -/
def raceCleanupMask : InterruptMask := .masked

/-- Race bookkeeping before any entrant has started. -/
def RaceAllState.initial (entrants : List FiberId) : RaceAllState β ε δ ι α :=
  ⟨entrants, none, [], entrants.length, [], none, none, false, [], none, false⟩

/-- Admit unique entrant identities; the empty race is a live frontier. -/
def raceAllAdmit (entrants : List FiberId) : Except Refusal (RaceAllState β ε δ ι α) :=
  if entrants.Nodup then .ok (RaceAllState.initial entrants) else .error .duplicateEntrant

/-- Return the accepted result only beyond startup and, when selected, cleanup. -/
def RaceAllState.result? (s : RaceAllState β ε δ ι α) : Option (Exit β ε δ ι α) :=
  if s.starting.isSome then none
  else if s.cleanupNeeded = false then s.accepted
  else if s.cleanupRequested = true ∧ (s.cleanup.bind WaitState.ready?).isSome = true
    then s.accepted else none

/-- A callback preserves the first accepted result while updating live bookkeeping.
The winning callback records the empty/nonempty set branch at that moment. -/
def raceComplete (s : RaceAllState β ε δ ι α) (child : FiberId) (exit : Exit β ε δ ι α) :
    RaceAllState β ε δ ι α :=
  if child ∈ s.live then
    let live := s.live.filter (fun id => decide (id ≠ child))
    match s.accepted with
    | some _ => {s with live := live, remaining := s.remaining - 1, failures := s.failures ++ exit.causeReasons, cleanup := s.cleanup.map (fun wait =>
          if child ∈ wait.pending then {wait with published := wait.published ++ [child]} else wait)}
    | none => match exit with
      | .success value => {s with live := live, remaining := s.remaining - 1, winner := some (child, value), accepted := some (.success value), cleanupNeeded := !live.isEmpty, requests := [], cleanup := none, cleanupRequested := false}
      | .failure cause =>
        if s.remaining ≤ 1 then
          {s with live := live, remaining := s.remaining - 1, failures := s.failures ++ cause.reasons, accepted := some (.failure ⟨s.failures ++ cause.reasons⟩), cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false}
        else {s with live := live, remaining := s.remaining - 1, failures := s.failures ++ cause.reasons}
  else s

/-- Explicit split launch permits an earlier callback during later startup.
Cleanup selects the then-current mutable-set view, after startup finishes. -/
def raceStep (s : RaceAllState β ε δ ι α) (decision : RaceAllDecision β ε δ ι α) :
    Except Refusal (RaceAllState β ε δ ι α) :=
  match decision with
  | .beginLaunch =>
    if s.accepted.isSome = true ∨ s.starting.isSome = true then .error .wrongRacePhase
    else match s.unstarted with
      | [] => .error .noEntrant
      | child :: rest => .ok {s with unstarted := rest, starting := some child}
  | .finishLaunch exit => match s.starting with
    | none => .error .wrongRacePhase
    | some child =>
      if child ∈ s.live then .error .duplicateEntrant else
      let after := {s with starting := none, live := s.live ++ [child]}
      .ok (match exit with | none => after | some value => raceComplete after child value)
  | .complete child exit =>
    if child ∈ s.live then .ok (raceComplete s child exit) else .error (.unknownEntrant child)
  | .beginCleanup =>
    if s.starting.isSome = true ∨ s.cleanupNeeded = false ∨ s.cleanup.isSome = true then
      .error .wrongRacePhase
    else match s.accepted with
      | none => .error .wrongRacePhase
      | some exit => .ok {s with requests := s.live, cleanup := some (WaitState.begin s.live exit), cleanupRequested := s.live.isEmpty}
  | .requestNext =>
    if s.cleanup.isNone = true ∨ s.cleanupRequested = true then .error .wrongRacePhase
    else match s.requests with
      | [] => .error .wrongRacePhase
      | _ :: rest => .ok {s with requests := rest, cleanupRequested := rest.isEmpty}

/-- Exactly one accepted controller decision. -/
def RaceStep (before : RaceAllState β ε δ ι α) (decision : RaceAllDecision β ε δ ι α)
    (after : RaceAllState β ε δ ι α) : Prop := raceStep before decision = .ok after

/-- Total fixed-tape race replay; scheduling and publication choices stay explicit. -/
def raceReplay (s : RaceAllState β ε δ ι α) (tape : List (RaceAllDecision β ε δ ι α)) :
    ReplayResult (RaceAllState β ε δ ι α) (Exit β ε δ ι α) :=
  match s.result? with
  | some result => .done s result
  | none => match tape with
    | [] => .frontier s
    | decision :: rest => match raceStep s decision with
      | .ok after => raceReplay after rest
      | .error reason => .refused s reason
termination_by structural tape

/-- Exact graph of fixed-tape controller replay; not a host interpreter relation. -/
def RaceRuns (s : RaceAllState β ε δ ι α) (tape : List (RaceAllDecision β ε δ ι α))
    (result : ReplayResult (RaceAllState β ε δ ι α) (Exit β ε δ ι α)) : Prop :=
  result = raceReplay s tape

/-! ## Frozen laws over the observed boundary controllers -/

/-- MaskMode.select_interruptible at the frozen observation boundary.
census: fork.unsafe -/
theorem MaskMode.select_interruptible :
    forall mask, MaskMode.select .interruptible mask = .unmasked := by
  intros
  rfl

/-- MaskMode.select_uninterruptible at the frozen observation boundary.
census: fork.unsafe -/
theorem MaskMode.select_uninterruptible :
    forall mask, MaskMode.select .uninterruptible mask = .masked := by
  intros
  rfl

/-- MaskMode.select_inherit at the frozen observation boundary.
census: fork.unsafe -/
theorem MaskMode.select_inherit :
    forall mask, MaskMode.select .inherit mask = mask := by
  intros
  rfl

/-- MaskMode.cases_receipt at the frozen observation boundary.
census: fork.unsafe -/
theorem MaskMode.cases_receipt :
    forall mode : MaskMode, mode = .interruptible ∨ mode = .uninterruptible ∨ mode = .inherit := by
  intro mode
  cases mode <;> simp

/-- ObserverMode.cases_receipt at the frozen observation boundary.
census: fork.await fork.join -/
theorem ObserverMode.cases_receipt :
    forall mode : ObserverMode, mode = .awaitValue ∨ mode = .joinEffect := by
  intro mode
  cases mode <;> simp

/-- ScopeMode.cases_receipt at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem ScopeMode.cases_receipt :
    forall mode : ScopeMode, mode = .forkIn ∨ mode = .fiberRunIn := by
  intro mode
  cases mode <;> simp

/-- Globals.install_eq at the frozen observation boundary.
census: fork.child rule.children-interrupted-after-exit -/
theorem Globals.install_eq :
    forall g : Globals, Globals.install g = {g with middlewareInstalled := true} := by
  intros
  rfl

/-- Globals.valid_iff at the frozen observation boundary.
census: fork.unsafe -/
theorem Globals.valid_iff :
    forall g : Globals, Globals.Valid g ↔ g.allocated.Nodup := by
  intros
  rfl

/-- Globals.ownsChildren_iff at the frozen observation boundary.
census: fork.unsafe rule.only-fork-child-tracks -/
theorem Globals.ownsChildren_iff :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (f : Fiber χ β ε δ ι α), Globals.OwnsChildren g f ↔ f.core.id ∈ g.allocated ∧ (∀ child, child ∈ f.children -> child ∈ g.allocated) := by
  intros
  rfl

/-- Fiber.valid_iff at the frozen observation boundary.
census: fork.unsafe fork.join -/
theorem Fiber.valid_iff :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Fiber χ β ε δ ι α, Fiber.Valid f ↔ f.children.Nodup ∧ (f.subscriptions.map Subscription.key).Nodup ∧ (Effect4.FiberStatus.Active f.core.status -> f.core.terminal = none ∧ f.core.cleanup = .notStarted ∧ f.core.cleanupCount = 0) ∧ (f.core.status = .finalizing -> f.core.terminal.isSome = true ∧ f.core.cleanup = .pending ∧ f.core.cleanupCount = 0) ∧ (f.core.status = .done -> f.core.terminal.isSome = true ∧ f.core.cleanup = .done ∧ f.core.cleanupCount = 1) := by
  intros
  rfl

/-- Fiber.valid?_iff at the frozen observation boundary.
census: fork.unsafe fork.join -/
theorem Fiber.valid?_iff :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Fiber χ β ε δ ι α, Fiber.valid? f = true ↔ Fiber.Valid f := by
  intro χ β ε δ ι α f
  cases h : f.core.status <;>
    simp [Fiber.valid?, Fiber.Valid, h, FiberStatus.Active, Bool.and_eq_true, and_assoc]

/-- Fiber.toFiberState_eq at the frozen observation boundary.
census: fork.unsafe fork.join -/
theorem Fiber.toFiberState_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Fiber χ β ε δ ι α, Fiber.toFiberState f = f.core := by
  intros
  rfl

/-- Globals.allocate_eq at the frozen observation boundary.
census: fork.unsafe -/
theorem Globals.allocate_eq :
    forall (g : Globals) (child : Effect4.FiberId), Globals.allocate g child = {g with allocated := g.allocated ++ [child]} := by
  intros
  rfl

/-- Globals.extends_iff at the frozen observation boundary.
census: fork.unsafe fork.child -/
theorem Globals.extends_iff :
    forall before after : Globals, Globals.Extends before after ↔ after.allocated.take before.allocated.length = before.allocated ∧ (before.middlewareInstalled = true -> after.middlewareInstalled = true) ∧ after.allocated.Nodup := by
  intros
  rfl

/-- Globals.extends?_iff at the frozen observation boundary.
census: fork.unsafe fork.child -/
theorem Globals.extends?_iff :
    forall before after : Globals, Globals.extends? before after = true ↔ Globals.Extends before after := by
  intro before after
  simp only [Globals.extends?, decide_eq_true_eq]
  rfl

/-- Globals.ownsChildren?_iff at the frozen observation boundary.
census: fork.unsafe fork.child -/
theorem Globals.ownsChildren?_iff :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (f : Fiber χ β ε δ ι α), Globals.ownsChildren? g f = true ↔ Globals.OwnsChildren g f := by
  intros
  simp [Globals.ownsChildren?, Globals.OwnsChildren]

/-- Fiber.published_iff at the frozen observation boundary.
census: fork.join fork.await rule.children-interrupted-after-exit -/
theorem Fiber.published_iff :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Fiber.published? f = some exit ↔ f.core.status = .done ∧ f.core.terminal = some exit := by
  intro χ β ε δ ι α f exit
  unfold Fiber.published?
  split <;> simp_all

/-- Fiber.published_eq at the frozen observation boundary.
census: fork.join fork.await -/
theorem Fiber.published_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Fiber χ β ε δ ι α, Fiber.published? f = if f.core.status = .done then f.core.terminal else none := by
  intros
  rfl

/-- Fiber.addChild_eq at the frozen observation boundary.
census: rule.only-fork-child-tracks -/
theorem Fiber.addChild_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (child : Effect4.FiberId), Fiber.addChild f child = {f with children := if child ∈ f.children then f.children else f.children ++ [child]} := by
  intros
  rfl

/-- Fiber.removeChild_eq at the frozen observation boundary.
census: fork.child rule.only-fork-child-tracks -/
theorem Fiber.removeChild_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (child : Effect4.FiberId), Fiber.removeChild f child = {f with children := f.children.filter (fun id => decide (id ≠ child))} := by
  intros
  rfl

/-- Fiber.addChild_nodup at the frozen observation boundary.
census: fork.child rule.only-fork-child-tracks -/
theorem Fiber.addChild_nodup :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (child : Effect4.FiberId), f.children.Nodup -> (Fiber.addChild f child).children.Nodup := by
  intro χ β ε δ ι α f child h
  unfold Fiber.addChild
  split
  · exact h
  · rename_i hn
    apply List.nodup_append.mpr
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb hab
    have hb' : b = child := List.mem_singleton.mp hb
    exact hn ((hab.trans hb') ▸ ha)

/-- Fiber.removeChild_membership at the frozen observation boundary.
census: fork.child rule.only-fork-child-tracks -/
theorem Fiber.removeChild_membership :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (child other : Effect4.FiberId), other ∈ (Fiber.removeChild f child).children ↔ other ∈ f.children ∧ other ≠ child := by
  intros
  simp [Fiber.removeChild]

/-- observation_await at the frozen observation boundary.
census: fork.await -/
theorem observation_await :
    forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, observation .awaitValue exit = .value exit := by
  intros
  rfl

/-- observation_join at the frozen observation boundary.
census: fork.join -/
theorem observation_join :
    forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, observation .joinEffect exit = .effect exit := by
  intros
  rfl

/-- observation_value_ne_effect at the frozen observation boundary.
census: fork.await fork.join -/
theorem observation_value_ne_effect :
    forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, (Observation.value exit : Observation β ε δ ι α) ≠ .effect exit := by
  intro β ε δ ι α exit h
  cases h

/-- Fiber.observe_invalid at the frozen observation boundary.
census: fork.await fork.join -/
theorem Fiber.observe_invalid :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (subscription : Subscription), Fiber.valid? f = false -> Fiber.observe f subscription = .error (.invalidFiber f.core.id) := by
  intros
  simp_all [Fiber.observe]

/-- Fiber.observe_done at the frozen observation boundary.
census: fork.await fork.join -/
theorem Fiber.observe_done :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (subscription : Subscription) (exit : Effect4.Exit β ε δ ι α), Fiber.Valid f -> Fiber.published? f = some exit -> Fiber.observe f subscription = .ok (f, observation subscription.mode exit) := by
  intros
  simp_all [Fiber.observe, Fiber.valid?_iff]

/-- Fiber.observe_live at the frozen observation boundary.
census: fork.await fork.join -/
theorem Fiber.observe_live :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (subscription : Subscription), Fiber.Valid f -> Fiber.published? f = none -> subscription.key ∉ f.subscriptions.map Subscription.key -> Fiber.observe f subscription = .ok ({f with subscriptions := f.subscriptions ++ [subscription]}, .waiting subscription.key) := by
  intros
  simp_all [Fiber.observe, Fiber.valid?_iff]

/-- Fiber.observe_duplicate at the frozen observation boundary.
census: fork.await fork.join -/
theorem Fiber.observe_duplicate :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (subscription : Subscription), Fiber.Valid f -> Fiber.published? f = none -> subscription.key ∈ f.subscriptions.map Subscription.key -> Fiber.observe f subscription = .error (.duplicateSubscription subscription.key) := by
  intros
  simp_all [Fiber.observe, Fiber.valid?_iff]

/-- Fiber.cancel_eq at the frozen observation boundary.
census: fork.await fork.join -/
theorem Fiber.cancel_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (key : Nat), Fiber.cancel f key = {f with subscriptions := f.subscriptions.filter (fun subscription => decide (subscription.key ≠ key))} := by
  intros
  rfl

/-- Fiber.cancel_membership at the frozen observation boundary.
census: fork.await fork.join -/
theorem Fiber.cancel_membership :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (key : Nat) (subscription : Subscription), subscription ∈ (Fiber.cancel f key).subscriptions ↔ subscription ∈ f.subscriptions ∧ subscription.key ≠ key := by
  intros
  simp [Fiber.cancel]

/-- Fiber.publish_eq at the frozen observation boundary.
census: fork.await fork.join rule.children-interrupted-after-exit -/
theorem Fiber.publish_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Fiber.publish f exit = ({f with core := {f.core with status := .done, terminal := some exit, interruptPending := false, cleanup := .done, cleanupCount := 1}, children := [], subscriptions := []}, f.subscriptions.map (fun subscription => (subscription.key, observation subscription.mode exit))) := by
  intros
  rfl

/-- Fiber.publish_valid at the frozen observation boundary.
census: fork.await fork.join -/
theorem Fiber.publish_valid :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Fiber.Valid (Fiber.publish f exit).1 := by
  intros
  simp [Fiber.publish, Fiber.Valid, FiberStatus.Active]

/-- interruptCause_eq at the frozen observation boundary.
census: fork.interrupt interrupt.accumulate -/
theorem interruptCause_eq :
    forall {ε δ ι α : Type u} (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α), (interruptCause encode requester annotations : Effect4.Cause ε δ ι α) = Effect4.Cause.annotate (Effect4.Cause.interrupt (requester.map encode)) annotations false := by
  intros
  rfl

/-- Fiber.recordInterrupt_done at the frozen observation boundary.
census: fork.interrupt interrupt.accumulate -/
theorem Fiber.recordInterrupt_done :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Fiber.published? f = some exit -> Fiber.recordInterrupt encode requester annotations f = f := by
  intros
  simp_all [Fiber.recordInterrupt]

/-- Fiber.recordInterrupt_live at the frozen observation boundary.
census: interrupt.accumulate fork.interrupt -/
theorem Fiber.recordInterrupt_live :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Fiber χ β ε δ ι α), Fiber.published? f = none -> Fiber.recordInterrupt encode requester annotations f = {f with interrupted := some (match f.interrupted with | none => interruptCause encode requester annotations | some previous => Effect4.Cause.combine previous (interruptCause encode requester annotations))} := by
  intros
  simp_all [Fiber.recordInterrupt]

/-- Fiber.recordInterrupt_core at the frozen observation boundary.
census: fork.interrupt interrupt.accumulate -/
theorem Fiber.recordInterrupt_core :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Fiber χ β ε δ ι α), (Fiber.recordInterrupt encode requester annotations f).core = f.core := by
  intro χ β ε δ ι α _ _ _ _ encode requester annotations f
  unfold Fiber.recordInterrupt
  split <;> rfl

/-- initialFiber_eq at the frozen observation boundary.
census: fork.unsafe -/
theorem initialFiber_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (mode : MaskMode), initialFiber parent child mode = { core := {id := child, status := .runnable, terminal := none, mask := MaskMode.select mode parent.core.mask, interruptPending := false, cleanup := .notStarted, cleanupCount := 0}, context := parent.context, children := [], subscriptions := [], interrupted := none } := by
  intros
  rfl

/-- initialFiber_valid at the frozen observation boundary.
census: fork.unsafe -/
theorem initialFiber_valid :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (mode : MaskMode), Fiber.Valid (initialFiber parent child mode) := by
  intros
  simp [initialFiber, Fiber.Valid, FiberStatus.Active]

/-- commitFork_eq at the frozen observation boundary.
census: fork.unsafe rule.only-fork-child-tracks -/
theorem commitFork_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent initial child : Fiber χ β ε δ ι α) (daemon : Bool) (events : List ForkEvent), commitFork g parent initial child daemon events = { globals := g, parent := if daemon = false ∧ Fiber.published? child = none then Fiber.addChild parent child.core.id else parent, initial := initial, child := child, events := events ++ (if daemon = false ∧ Fiber.published? child = none then [.registered parent.core.id child.core.id] else []), removeFromParent := if daemon = false ∧ Fiber.published? child = none then some parent.core.id else none } := by
  intros
  rfl

/-- forkUnsafe_duplicate at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_duplicate :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (start : StartObservation χ β ε δ ι α), child ∈ g.allocated -> forkUnsafe g parent child options start = .error (.duplicateFiber child) := by
  intros
  simp_all [forkUnsafe]

/-- forkUnsafe_deferred at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_deferred :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) , child ∉ g.allocated -> options.startImmediately = false -> forkUnsafe g parent child options .deferred = .ok (commitFork (Globals.allocate g child) parent (initialFiber parent child options.maskMode) (initialFiber parent child options.maskMode) options.daemon [.scheduled child 0]) := by
  intros
  simp_all [forkUnsafe]

/-- forkUnsafe_wrong_deferred at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_wrong_deferred :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) , child ∉ g.allocated -> options.startImmediately = true -> forkUnsafe g parent child options .deferred = .error .wrongStartMode := by
  intros
  simp_all [forkUnsafe]

/-- forkUnsafe_wrong_immediate at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_wrong_immediate :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = false -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongStartMode := by
  intros
  simp_all [forkUnsafe]

/-- forkUnsafe_wrong_identity at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_wrong_identity :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id ≠ child -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongChildIdentity := by
  intros
  simp_all [forkUnsafe]

/-- forkUnsafe_wrong_parent at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_wrong_parent :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id ≠ parent.core.id -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongParentIdentity := by
  intros
  simp_all [forkUnsafe]

/-- forkUnsafe_invalid_child at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_invalid_child :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Fiber.valid? after = false -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error (.invalidFiber child) := by
  intros
  simp_all [forkUnsafe]

/-- forkUnsafe_invalid_parent at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_invalid_parent :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Fiber.Valid after -> Fiber.valid? postParent = false -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error (.invalidFiber parent.core.id) := by
  intros
  simp_all [forkUnsafe, Fiber.valid?_iff]

/-- forkUnsafe_invalid_globals at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_invalid_globals :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Fiber.Valid after -> Fiber.Valid postParent -> Globals.extends? (Globals.allocate g child) postGlobals = false -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidStartGlobals := by
  intros
  simp_all [forkUnsafe, Fiber.valid?_iff]

/-- forkUnsafe_invalid_ownership at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_invalid_ownership :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Fiber.Valid after -> Fiber.Valid postParent -> Globals.Extends (Globals.allocate g child) postGlobals -> Globals.ownsChildren? postGlobals postParent = false -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidParentOwnership := by
  intros
  simp_all [forkUnsafe, Fiber.valid?_iff, Globals.extends?_iff]

/-- forkUnsafe_invalid_child_ownership at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_invalid_child_ownership :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Fiber.Valid after -> Fiber.Valid postParent -> Globals.Extends (Globals.allocate g child) postGlobals -> Globals.OwnsChildren postGlobals postParent -> Globals.ownsChildren? postGlobals after = false -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidChildOwnership := by
  intros
  simp_all [forkUnsafe, Fiber.valid?_iff, Globals.extends?_iff, Globals.ownsChildren?_iff]

/-- forkUnsafe_immediate at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_immediate :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (postGlobals : Globals) (postParent after : Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Fiber.Valid after -> Fiber.Valid postParent -> Globals.Extends (Globals.allocate g child) postGlobals -> Globals.OwnsChildren postGlobals postParent -> Globals.OwnsChildren postGlobals after -> forkUnsafe g parent child options (.immediate postGlobals postParent after) = .ok (commitFork postGlobals postParent (initialFiber parent child options.maskMode) after options.daemon [.evaluated child]) := by
  intros
  simp_all [forkUnsafe, Fiber.valid?_iff, Globals.extends?_iff, Globals.ownsChildren?_iff]

/-- forkUnsafe_fresh at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_fresh :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (start : StartObservation χ β ε δ ι α) (result : ForkResult χ β ε δ ι α), forkUnsafe g parent child options start = .ok result -> child ∉ g.allocated := by
  intro χ β ε δ ι α g parent child options start result h
  intro hmem
  rw [forkUnsafe_duplicate g parent child options start hmem] at h
  cases h

/-- forkUnsafe_allocated_nodup at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_allocated_nodup :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (start : StartObservation χ β ε δ ι α) (result : ForkResult χ β ε δ ι α), Globals.Valid g -> forkUnsafe g parent child options start = .ok result -> Globals.Valid result.globals := by
  intro χ β ε δ ι α g parent child options start result hg h
  have hfresh := forkUnsafe_fresh g parent child options start result h
  cases start with
  | deferred =>
    simp only [forkUnsafe, if_neg hfresh] at h
    split at h
    · cases h
    · cases h
      change (g.allocated ++ [child]).Nodup
      refine List.nodup_append.mpr ⟨hg, by simp, ?_⟩
      intro a ha b hb hab
      exact hfresh ((hab.trans (List.mem_singleton.mp hb)) ▸ ha)
  | immediate postGlobals postParent after =>
    simp only [forkUnsafe, if_neg hfresh] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    exact ((Globals.extends?_iff (g.allocate child) postGlobals).mp (by assumption)).2.2

/-- forkUnsafe_child_valid at the frozen observation boundary.
census: fork.unsafe -/
theorem forkUnsafe_child_valid :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (start : StartObservation χ β ε δ ι α) (result : ForkResult χ β ε δ ι α), forkUnsafe g parent child options start = .ok result -> Fiber.Valid result.child := by
  intro χ β ε δ ι α g parent child options start result h
  have hfresh := forkUnsafe_fresh g parent child options start result h
  cases start with
  | deferred =>
    simp only [forkUnsafe, if_neg hfresh] at h
    split at h
    · cases h
    · cases h
      exact initialFiber_valid parent child options.maskMode
  | immediate postGlobals postParent after =>
    simp only [forkUnsafe, if_neg hfresh] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    exact (Fiber.valid?_iff after).mp (by assumption)

/-- forkUnsafe_parent_children_nodup at the frozen observation boundary.
census: fork.child rule.only-fork-child-tracks -/
theorem forkUnsafe_parent_children_nodup :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (start : StartObservation χ β ε δ ι α) (result : ForkResult χ β ε δ ι α), parent.children.Nodup -> forkUnsafe g parent child options start = .ok result -> result.parent.children.Nodup := by
  intro χ β ε δ ι α g parent child options start result hp h
  have hcommit : ∀ (world : Globals) (p initial c : Fiber χ β ε δ ι α) daemon events,
      p.children.Nodup → (commitFork world p initial c daemon events).parent.children.Nodup := by
    intro world p initial c daemon events hn
    unfold commitFork
    split
    · exact Fiber.addChild_nodup p c.core.id hn
    · exact hn
  have hfresh := forkUnsafe_fresh g parent child options start result h
  cases start with
  | deferred =>
    simp only [forkUnsafe, if_neg hfresh] at h
    split at h
    · cases h
    · cases h
      exact hcommit _ _ _ _ _ _ hp
  | immediate postGlobals postParent after =>
    simp only [forkUnsafe, if_neg hfresh] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    exact hcommit _ _ _ _ _ _ ((Fiber.valid?_iff postParent).mp (by assumption)).1

/-- forkChild_eq at the frozen observation boundary.
census: fork.child rule.children-interrupted-after-exit -/
theorem forkChild_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (start : StartObservation χ β ε δ ι α), forkChild g parent child options start = forkUnsafe (Globals.install g) parent child {options with daemon := false} start := by
  intros
  rfl

/-- forkDetach_eq at the frozen observation boundary.
census: fork.detach rule.only-fork-child-tracks -/
theorem forkDetach_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : ForkOptions) (start : StartObservation χ β ε δ ι α), forkDetach g parent child options start = forkUnsafe g parent child {options with daemon := true} start := by
  intros
  rfl

/-- commitFork_done_untracked at the frozen observation boundary.
census: fork.unsafe fork.child -/
theorem commitFork_done_untracked :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent initial child : Fiber χ β ε δ ι α) (daemon : Bool) (events : List ForkEvent) (exit : Effect4.Exit β ε δ ι α), Fiber.published? child = some exit -> (commitFork g parent initial child daemon events).parent = parent ∧ (commitFork g parent initial child daemon events).removeFromParent = none ∧ (commitFork g parent initial child daemon events).events = events := by
  intros
  simp_all [commitFork]

/-- commitFork_daemon_untracked at the frozen observation boundary.
census: fork.detach rule.only-fork-child-tracks -/
theorem commitFork_daemon_untracked :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent initial child : Fiber χ β ε δ ι α) (events : List ForkEvent), (commitFork g parent initial child true events).parent = parent ∧ (commitFork g parent initial child true events).removeFromParent = none ∧ (commitFork g parent initial child true events).events = events := by
  intros
  simp [commitFork]

/-- WaitState.begin_eq at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem WaitState.begin_eq :
    forall {τ : Type u}, forall (targets : List Effect4.FiberId) (result : τ), WaitState.begin targets result = {targets := targets, published := [], result := result} := by
  intros
  rfl

/-- WaitState.pending_eq at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem WaitState.pending_eq :
    forall {τ : Type u}, forall s : WaitState τ, WaitState.pending s = s.targets.filter (fun id => decide (id ∉ s.published)) := by
  intros
  rfl

/-- WaitState.ready_iff at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem WaitState.ready_iff :
    forall {τ : Type u}, forall (s : WaitState τ) (result : τ), WaitState.ready? s = some result ↔ WaitState.pending s = [] ∧ s.result = result := by
  intro τ s result
  unfold WaitState.ready?
  split <;> simp_all

/-- WaitState.ready_publications at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem WaitState.ready_publications :
    forall {τ : Type u}, forall (s : WaitState τ) (result : τ), WaitState.ready? s = some result -> ∀ child, child ∈ s.targets -> child ∈ s.published := by
  intro τ s result h child ht
  have hempty := (WaitState.ready_iff s result).mp h |>.1
  by_cases hp : child ∈ s.published
  · exact hp
  · have hm : child ∈ s.pending := by simp [WaitState.pending, ht, hp]
    rw [hempty] at hm
    cases hm

/-- WaitState.observe_pending at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem WaitState.observe_pending :
    forall {τ : Type u}, forall (s : WaitState τ) (child : Effect4.FiberId), child ∈ WaitState.pending s -> WaitState.observe s child = .ok {s with published := s.published ++ [child]} := by
  intros
  simp_all [WaitState.observe]

/-- WaitState.observe_unknown at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem WaitState.observe_unknown :
    forall {τ : Type u}, forall (s : WaitState τ) (child : Effect4.FiberId), child ∉ WaitState.pending s -> WaitState.observe s child = .error (.unknownPublication child) := by
  intros
  simp_all [WaitState.observe]

/-- WaitState.observe_pending_membership at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem WaitState.observe_pending_membership :
    forall {τ : Type u}, forall (s after : WaitState τ) (child other : Effect4.FiberId), WaitState.observe s child = .ok after -> (other ∈ WaitState.pending after ↔ other ∈ WaitState.pending s ∧ other ≠ child) := by
  intro τ s after child other h
  unfold WaitState.observe at h
  split at h
  · cases h
    simp [WaitState.pending, not_or, and_assoc]
  · cases h

/-- waitStep_iff at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitStep_iff :
    forall {τ : Type u}, forall (before after : WaitState τ) (child : Effect4.FiberId), WaitStep before child after ↔ WaitState.observe before child = .ok after := by
  intros
  rfl

/-- waitRuns_iff at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitRuns_iff :
    forall {τ : Type u}, forall (initial : WaitState τ) (tape : List Effect4.FiberId) (result : ReplayResult (WaitState τ) τ), WaitRuns initial tape result ↔ result = waitReplay initial tape := by
  intros
  rfl

/-- ReplayResult.state_done at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.race-all -/
theorem ReplayResult.state_done :
    forall {σ : Type u} {τ : Type v} (state : σ) (result : τ), ReplayResult.state (ReplayResult.done state result) = state := by
  intros
  rfl

/-- ReplayResult.state_frontier at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.race-all -/
theorem ReplayResult.state_frontier :
    forall {σ : Type u} {τ : Type v} (state : σ), ReplayResult.state (ReplayResult.frontier state : ReplayResult σ τ) = state := by
  intros
  rfl

/-- ReplayResult.state_refused at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.race-all -/
theorem ReplayResult.state_refused :
    forall {σ : Type u} {τ : Type v} (state : σ) (reason : Refusal), ReplayResult.state (ReplayResult.refused state reason : ReplayResult σ τ) = state := by
  intros
  rfl

/-- waitReplay_ready at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitReplay_ready :
    forall {τ : Type u}, forall (s : WaitState τ) (result : τ) (tape : List Effect4.FiberId), WaitState.ready? s = some result -> waitReplay s tape = .done s result := by
  intro τ s result tape h
  cases tape <;> simp [waitReplay, h]

/-- waitReplay_frontier at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitReplay_frontier :
    forall {τ : Type u}, forall s : WaitState τ, WaitState.ready? s = none -> waitReplay s [] = .frontier s := by
  intros
  rw [waitReplay]
  simp_all

/-- waitReplay_cons_ok at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitReplay_cons_ok :
    forall {τ : Type u}, forall (s after : WaitState τ) (child : Effect4.FiberId) (tape : List Effect4.FiberId), WaitState.ready? s = none -> WaitState.observe s child = .ok after -> waitReplay s (child :: tape) = waitReplay after tape := by
  intros
  rw [waitReplay]
  simp_all

/-- waitReplay_cons_error at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitReplay_cons_error :
    forall {τ : Type u}, forall (s : WaitState τ) (child : Effect4.FiberId) (tape : List Effect4.FiberId) (reason : Refusal), WaitState.ready? s = none -> WaitState.observe s child = .error reason -> waitReplay s (child :: tape) = .refused s reason := by
  intros
  rw [waitReplay]
  simp_all

/-- wait_fixedTape_deterministic at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem wait_fixedTape_deterministic :
    forall {τ : Type u}, forall (s : WaitState τ) (tape : List Effect4.FiberId) (left right : ReplayResult (WaitState τ) τ), WaitRuns s tape left -> WaitRuns s tape right -> left = right := by
  intros
  simp_all [WaitRuns]

/-- waitReplay_done_ready at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitReplay_done_ready :
    forall {τ : Type u}, forall (s after : WaitState τ) (tape : List Effect4.FiberId) (result : τ), waitReplay s tape = .done after result -> WaitState.ready? after = some result := by
  intro τ s after tape result
  induction tape generalizing s with
  | nil =>
    intro h
    rw [waitReplay] at h
    split at h
    · cases h
      assumption
    · cases h
  | cons child rest ih =>
    intro h
    rw [waitReplay] at h
    split at h
    · cases h
      assumption
    · split at h
      · exact ih _ h
      · cases h

/-- waitReplay_frame at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem waitReplay_frame :
    forall {τ : Type u}, forall (s : WaitState τ) (tape : List Effect4.FiberId), let after := ReplayResult.state (waitReplay s tape); after.targets = s.targets ∧ after.result = s.result ∧ (∀ child, child ∈ after.published -> child ∈ s.published ++ tape) := by
  intro τ s tape
  induction tape generalizing s with
  | nil =>
    rw [waitReplay]
    split <;> simp [ReplayResult.state]
  | cons child rest ih =>
    rw [waitReplay]
    split
    · simp [ReplayResult.state]
      exact fun _ hm => Or.inl hm
    · split
      · rename_i after hstep
        have hframe : after.targets = s.targets ∧ after.result = s.result ∧
            after.published = s.published ++ [child] := by
          unfold WaitState.observe at hstep
          split at hstep
          · cases hstep
            exact ⟨rfl, rfl, rfl⟩
          · cases hstep
        have hi := ih after
        refine ⟨hi.1.trans hframe.1, hi.2.1.trans hframe.2.1, ?_⟩
        intro id hm
        have hm' := hi.2.2 id hm
        simpa [hframe.2.2, List.append_assoc] using hm'
      · simp [ReplayResult.state]
        exact fun _ hm => Or.inl hm

/-- wait_two_publications at the frozen observation boundary.
census: rule.children-interrupted-after-exit fork.interrupt-all fork.race-all -/
theorem wait_two_publications :
    forall {τ : Type u}, forall (left right : Effect4.FiberId) (result : τ), left ≠ right -> waitReplay (WaitState.begin [left, right] result) [left, right] = .done {targets := [left, right], published := [left, right], result := result} result := by
  intro τ left right result hne
  simp [waitReplay, WaitState.begin, WaitState.ready?, WaitState.pending,
    WaitState.observe, hne, Ne.symm hne]

/-- beginParentExit_eq at the frozen observation boundary.
census: fork.child rule.children-interrupted-after-exit -/
theorem beginParentExit_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Globals) (parent : Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), beginParentExit g parent exit = WaitState.begin (if g.middlewareInstalled then parent.children else []) exit := by
  intros
  rfl

/-- parentExitView_waiting at the frozen observation boundary.
census: rule.children-interrupted-after-exit -/
theorem parentExitView_waiting :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Fiber χ β ε δ ι α) (wait : WaitState (Effect4.Exit β ε δ ι α)), WaitState.ready? wait = none -> parentExitView parent wait = {parent with core := {parent.core with status := .finalizing, terminal := some wait.result, interruptPending := false, cleanup := .pending, cleanupCount := 0}, children := WaitState.pending wait} := by
  intros
  simp_all [parentExitView]

/-- parentExitView_ready at the frozen observation boundary.
census: rule.children-interrupted-after-exit -/
theorem parentExitView_ready :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Fiber χ β ε δ ι α) (wait : WaitState (Effect4.Exit β ε δ ι α)) (exit : Effect4.Exit β ε δ ι α), WaitState.ready? wait = some exit -> parentExitView parent wait = (Fiber.publish parent exit).1 := by
  intros
  simp_all [parentExitView]

/-- parentExitView_not_published_while_waiting at the frozen observation boundary.
census: rule.children-interrupted-after-exit -/
theorem parentExitView_not_published_while_waiting :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Fiber χ β ε δ ι α) (wait : WaitState (Effect4.Exit β ε δ ι α)), WaitState.ready? wait = none -> Fiber.published? (parentExitView parent wait) = none := by
  intros
  simp_all [parentExitView, Fiber.published?]

/-- parentExitView_publication_requires_children at the frozen observation boundary.
census: rule.children-interrupted-after-exit -/
theorem parentExitView_publication_requires_children :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Fiber χ β ε δ ι α) (wait : WaitState (Effect4.Exit β ε δ ι α)) (exit : Effect4.Exit β ε δ ι α), Fiber.published? (parentExitView parent wait) = some exit -> ∀ child, child ∈ wait.targets -> child ∈ wait.published := by
  intro χ β ε δ ι α parent wait exit h
  cases hw : wait.ready? with
  | none => simp [parentExitView, hw, Fiber.published?] at h
  | some result => exact WaitState.ready_publications wait result hw

/-- newChildren_eq at the frozen observation boundary.
census: fork.await-all-children -/
theorem newChildren_eq :
    forall initial current : List Effect4.FiberId, newChildren initial current = current.filter (fun child => decide (child ∉ initial)) := by
  intros
  rfl

/-- newChildren_membership at the frozen observation boundary.
census: fork.await-all-children -/
theorem newChildren_membership :
    forall (initial current : List Effect4.FiberId) (child : Effect4.FiberId), child ∈ newChildren initial current ↔ child ∈ current ∧ child ∉ initial := by
  intros
  simp [newChildren]

/-- awaitAllChildren_eq at the frozen observation boundary.
census: fork.await-all-children -/
theorem awaitAllChildren_eq :
    forall initial current : List Effect4.FiberId, awaitAllChildren initial current = WaitState.begin (newChildren initial current) () := by
  intros
  rfl

/-- interruptAllRequests_eq at the frozen observation boundary.
census: fork.interrupt-all fork.interrupt -/
theorem interruptAllRequests_eq :
    forall targets : List Effect4.FiberId, interruptAllRequests targets = targets.map InterruptAction.request ++ [.awaitAll targets] := by
  intros
  rfl

/-- interruptAllWait_eq at the frozen observation boundary.
census: fork.interrupt-all fork.interrupt -/
theorem interruptAllWait_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall fibers : List (Fiber χ β ε δ ι α), interruptAllWait fibers = {targets := fibers.map (fun f => f.core.id), published := (fibers.filter (fun f => (Fiber.published? f).isSome)).map (fun f => f.core.id), result := ()} := by
  intros
  rfl

/-- bindScope_invalid at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem bindScope_invalid :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : ScopeMode) (parent : Effect4.FiberId) (child : Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat) , Fiber.valid? child = false -> bindScope mode parent child scope key = .error (.invalidFiber child.core.id) := by
  intros
  simp_all [bindScope]

/-- bindScope_done at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem bindScope_done :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : ScopeMode) (parent : Effect4.FiberId) (child : Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat) (exit : Effect4.Exit β ε δ ι α), Fiber.Valid child -> Fiber.published? child = some exit -> bindScope mode parent child scope key = .ok {scope := scope, observerKey := none, interruptor := none} := by
  intros
  simp_all [bindScope, Fiber.valid?_iff]

/-- bindScope_closed at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem bindScope_closed :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : ScopeMode) (parent : Effect4.FiberId) (child : Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat) , Fiber.Valid child -> Fiber.published? child = none -> scope.isClosed = true -> bindScope mode parent child scope key = .ok {scope := scope, observerKey := none, interruptor := some (if mode = .forkIn then parent else child.core.id)} := by
  intros
  simp_all [bindScope, Fiber.valid?_iff]

/-- bindScope_duplicate_key at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem bindScope_duplicate_key :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : ScopeMode) (parent : Effect4.FiberId) (child : Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat) , Fiber.Valid child -> Fiber.published? child = none -> scope.isClosed = false -> (ULift.up key : ULift.{u} Nat) ∈ scope.finalizerKeys -> bindScope mode parent child scope key = .error (.duplicateScopeKey key) := by
  intros
  simp_all [bindScope, Fiber.valid?_iff]

/-- bindScope_open at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem bindScope_open :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : ScopeMode) (parent : Effect4.FiberId) (child : Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat) , Fiber.Valid child -> Fiber.published? child = none -> scope.isClosed = false -> (ULift.up key : ULift.{u} Nat) ∉ scope.finalizerKeys -> bindScope mode parent child scope key = .ok {scope := scope.addUnsafe (ULift.up key) (ULift.up {child := child.core.id, skipSelf := decide (mode = .forkIn)}), observerKey := some key, interruptor := none} := by
  intros
  simp_all [bindScope, Fiber.valid?_iff]

/-- forkScopedBinding_eq at the frozen observation boundary.
census: fork.scoped -/
theorem forkScopedBinding_eq :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.FiberId) (child : Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat), forkScopedBinding parent child scope key = bindScope .forkIn parent child scope key := by
  intros
  rfl

/-- scopeFinalizerInterruptor_eq at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem scopeFinalizerInterruptor_eq :
    forall (finalizer : ScopeFinalizer) (current : Effect4.FiberId), scopeFinalizerInterruptor finalizer current = if finalizer.skipSelf = true ∧ current = finalizer.child then none else some current := by
  intros
  rfl

/-- scopeFinalizer_self_guard at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem scopeFinalizer_self_guard :
    forall child : Effect4.FiberId, scopeFinalizerInterruptor {child := child, skipSelf := true} child = none ∧ scopeFinalizerInterruptor {child := child, skipSelf := false} child = some child := by
  intros
  simp [scopeFinalizerInterruptor]

/-- scopeObserver_eq at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem scopeObserver_eq :
    forall {β : Type v} {ε δ ι α : Type u}, forall (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key : Nat), scopeObserver scope key = scope.removeUnsafe (ULift.up key) := by
  intros
  rfl

/-- scopeObserver_key_membership at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem scopeObserver_key_membership :
    forall {β : Type v} {ε δ ι α : Type u}, forall (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α) (key other : Nat), (ULift.up other : ULift.{u} Nat) ∈ (scopeObserver scope key).finalizerKeys ↔ (ULift.up other : ULift.{u} Nat) ∈ scope.finalizerKeys ∧ other ≠ key := by
  intro β ε δ ι α scope key other
  cases scope with
  | mk strategy state =>
    cases state with
    | empty =>
      change (ULift.up other : ULift.{u} Nat) ∈ ([] : List (ULift.{u} Nat)) ↔
        (ULift.up other : ULift.{u} Nat) ∈ ([] : List (ULift.{u} Nat)) ∧ other ≠ key
      simp
    | openEmpty =>
      change (ULift.up other : ULift.{u} Nat) ∈ ([] : List (ULift.{u} Nat)) ↔
        (ULift.up other : ULift.{u} Nat) ∈ ([] : List (ULift.{u} Nat)) ∧ other ≠ key
      simp
    | closed exit =>
      change (ULift.up other : ULift.{u} Nat) ∈ ([] : List (ULift.{u} Nat)) ↔
        (ULift.up other : ULift.{u} Nat) ∈ ([] : List (ULift.{u} Nat)) ∧ other ≠ key
      simp
    | openInline existing finalizer =>
      by_cases h : existing = ULift.up key
      · subst existing
        simp [scopeObserver, Scope.finalizerKeys, Scope.finalizers,
          Scope.removeUnsafe_inline_hit, ScopeState.entries]
      · rw [scopeObserver, Scope.removeUnsafe_inline_miss _ existing (ULift.up key) finalizer rfl h]
        simp only [Scope.finalizerKeys, Scope.finalizers, ScopeState.entries, List.map_cons,
          List.map_nil, List.mem_singleton]
        constructor
        · intro he
          refine ⟨he, ?_⟩
          intro hk
          exact h (he.symm.trans (congrArg ULift.up hk))
        · exact And.left
    | openMap table =>
      change (ULift.up other : ULift.{u} Nat) ∈ (Scope.tableRemove table (ULift.up key)).map Prod.fst ↔
        (ULift.up other : ULift.{u} Nat) ∈ table.map Prod.fst ∧ other ≠ key
      simp only [Scope.tableRemove, List.mem_map, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨entry, ⟨hm, hn⟩, he⟩
        refine ⟨⟨entry, hm, he⟩, ?_⟩
        intro hk
        exact hn (he.trans (congrArg ULift.up hk))
      · rintro ⟨⟨entry, hm, he⟩, hn⟩
        refine ⟨entry, ⟨hm, ?_⟩, he⟩
        intro hk
        exact hn (congrArg ULift.down (he.symm.trans hk))

/-- raceForkOptions_eq at the frozen observation boundary.
census: fork.race-all rule.only-fork-child-tracks -/
theorem raceForkOptions_eq :
    raceForkOptions = {startImmediately := true, daemon := true, maskMode := .interruptible} := by
  intros
  rfl

/-- raceCleanupMask_eq at the frozen observation boundary.
census: fork.race-all -/
theorem raceCleanupMask_eq :
    raceCleanupMask = Effect4.InterruptMask.masked := by
  intros
  rfl

/-- RaceAllState.initial_eq at the frozen observation boundary.
census: fork.race-all -/
theorem RaceAllState.initial_eq :
    forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (RaceAllState.initial entrants : RaceAllState β ε δ ι α) = {unstarted := entrants, starting := none, live := [], remaining := entrants.length, failures := [], winner := none, accepted := none, cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false} := by
  intros
  rfl

/-- raceAllAdmit_eq at the frozen observation boundary.
census: fork.race-all -/
theorem raceAllAdmit_eq :
    forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (raceAllAdmit entrants : Except Refusal (RaceAllState β ε δ ι α)) = if entrants.Nodup then .ok (RaceAllState.initial entrants) else .error .duplicateEntrant := by
  intros
  rfl

/-- RaceAllState.result_eq at the frozen observation boundary.
census: fork.race-all -/
theorem RaceAllState.result_eq :
    forall {β : Type v} {ε δ ι α : Type u}, forall s : RaceAllState β ε δ ι α, RaceAllState.result? s = if s.starting.isSome then none else if s.cleanupNeeded = false then s.accepted else if s.cleanupRequested = true ∧ (s.cleanup.bind WaitState.ready?).isSome = true then s.accepted else none := by
  intros
  rfl

/-- raceComplete_unknown at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_unknown :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> raceComplete s child exit = s := by
  intros
  simp_all [raceComplete]

/-- raceComplete_after_accepted at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_after_accepted :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit accepted : Effect4.Exit β ε δ ι α), child ∈ s.live -> s.accepted = some accepted -> raceComplete s child exit = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ exit.causeReasons, cleanup := s.cleanup.map (fun wait => if child ∈ WaitState.pending wait then {wait with published := wait.published ++ [child]} else wait)} := by
  intros
  simp_all [raceComplete]

/-- raceComplete_success at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_success :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (value : β), child ∈ s.live -> s.accepted = none -> raceComplete s child (.success value) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, winner := some (child, value), accepted := some (.success value), cleanupNeeded := !(s.live.filter (fun id => decide (id ≠ child))).isEmpty, requests := [], cleanup := none, cleanupRequested := false} := by
  intros
  simp_all [raceComplete]

/-- raceComplete_failure_last at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_failure_last :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> s.remaining ≤ 1 -> raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons, accepted := some (.failure ⟨s.failures ++ cause.reasons⟩), cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false} := by
  intros
  simp_all [raceComplete]

/-- raceComplete_failure_pending at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_failure_pending :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> 1 < s.remaining -> raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons} := by
  intros
  simp_all [raceComplete]

/-- raceStep_begin_blocked at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_begin_blocked :
    forall {β : Type v} {ε δ ι α : Type u}, forall s : RaceAllState β ε δ ι α, s.accepted.isSome = true ∨ s.starting.isSome = true -> raceStep s .beginLaunch = .error .wrongRacePhase := by
  intros
  simp_all [raceStep]

/-- raceStep_begin_empty at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_begin_empty :
    forall {β : Type v} {ε δ ι α : Type u}, forall s : RaceAllState β ε δ ι α, s.accepted = none -> s.starting = none -> s.unstarted = [] -> raceStep s .beginLaunch = .error .noEntrant := by
  intros
  simp_all [raceStep]

/-- raceStep_begin at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_begin :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (rest : List Effect4.FiberId), s.accepted = none -> s.starting = none -> s.unstarted = child :: rest -> raceStep s .beginLaunch = .ok {s with unstarted := rest, starting := some child} := by
  intros
  simp_all [raceStep]

/-- raceStep_finish_missing at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_finish_missing :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (exit : Option (Effect4.Exit β ε δ ι α)), s.starting = none -> raceStep s (.finishLaunch exit) = .error .wrongRacePhase := by
  intros
  simp_all [raceStep]

/-- raceStep_finish_duplicate at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_finish_duplicate :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Option (Effect4.Exit β ε δ ι α)), s.starting = some child -> child ∈ s.live -> raceStep s (.finishLaunch exit) = .error .duplicateEntrant := by
  intros
  simp_all [raceStep]

/-- raceStep_finish_live at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_finish_live :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId), s.starting = some child -> child ∉ s.live -> raceStep s (.finishLaunch none) = .ok {s with starting := none, live := s.live ++ [child]} := by
  intros
  simp_all [raceStep]

/-- raceStep_finish_done at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_finish_done :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), s.starting = some child -> child ∉ s.live -> raceStep s (.finishLaunch (some exit)) = .ok (raceComplete {s with starting := none, live := s.live ++ [child]} child exit) := by
  intros
  simp_all [raceStep]

/-- raceStep_complete at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_complete :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∈ s.live -> raceStep s (.complete child exit) = .ok (raceComplete s child exit) := by
  intros
  simp_all [raceStep]

/-- raceStep_complete_unknown at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_complete_unknown :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> raceStep s (.complete child exit) = .error (.unknownEntrant child) := by
  intros
  simp_all [raceStep]

/-- raceStep_beginCleanup at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_beginCleanup :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), s.starting = none -> s.accepted = some exit -> s.cleanupNeeded = true -> s.cleanup = none -> raceStep s .beginCleanup = .ok {s with requests := s.live, cleanup := some (WaitState.begin s.live exit), cleanupRequested := s.live.isEmpty} := by
  intros
  simp_all [raceStep]

/-- raceStep_beginCleanup_blocked at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_beginCleanup_blocked :
    forall {β : Type v} {ε δ ι α : Type u}, forall s : RaceAllState β ε δ ι α, s.starting.isSome = true ∨ s.accepted = none ∨ s.cleanupNeeded = false ∨ s.cleanup.isSome = true -> raceStep s .beginCleanup = .error .wrongRacePhase := by
  intro β ε δ ι α s h
  rcases h with h | h | h | h
  all_goals simp_all [raceStep]

/-- raceStep_requestNext at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_requestNext :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (rest : List Effect4.FiberId) (wait : WaitState (Effect4.Exit β ε δ ι α)), s.cleanup = some wait -> s.cleanupRequested = false -> s.requests = child :: rest -> raceStep s .requestNext = .ok {s with requests := rest, cleanupRequested := rest.isEmpty} := by
  intros
  simp_all [raceStep]

/-- raceStep_requestNext_blocked at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_requestNext_blocked :
    forall {β : Type v} {ε δ ι α : Type u}, forall s : RaceAllState β ε δ ι α, s.cleanup = none ∨ s.cleanupRequested = true ∨ s.requests = [] -> raceStep s .requestNext = .error .wrongRacePhase := by
  intro β ε δ ι α s h
  rcases h with h | h | h
  all_goals simp_all [raceStep]

/-- raceStep_iff at the frozen observation boundary.
census: fork.race-all -/
theorem raceStep_iff :
    forall {β : Type v} {ε δ ι α : Type u}, forall (before after : RaceAllState β ε δ ι α) (decision : RaceAllDecision β ε δ ι α), RaceStep before decision after ↔ raceStep before decision = .ok after := by
  intros
  rfl

/-- raceRuns_iff at the frozen observation boundary.
census: fork.race-all -/
theorem raceRuns_iff :
    forall {β : Type v} {ε δ ι α : Type u}, forall (initial : RaceAllState β ε δ ι α) (tape : List (RaceAllDecision β ε δ ι α)) (result : ReplayResult (RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α)), RaceRuns initial tape result ↔ result = raceReplay initial tape := by
  intros
  rfl

/-- raceReplay_ready at the frozen observation boundary.
census: fork.race-all -/
theorem raceReplay_ready :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (tape : List (RaceAllDecision β ε δ ι α)), RaceAllState.result? s = some exit -> raceReplay s tape = .done s exit := by
  intro β ε δ ι α s exit tape h
  cases tape <;> simp [raceReplay, h]

/-- raceReplay_frontier at the frozen observation boundary.
census: fork.race-all -/
theorem raceReplay_frontier :
    forall {β : Type v} {ε δ ι α : Type u}, forall s : RaceAllState β ε δ ι α, RaceAllState.result? s = none -> raceReplay s [] = .frontier s := by
  intros
  rw [raceReplay]
  simp_all

/-- raceReplay_cons_ok at the frozen observation boundary.
census: fork.race-all -/
theorem raceReplay_cons_ok :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s after : RaceAllState β ε δ ι α) (decision : RaceAllDecision β ε δ ι α) (tape : List (RaceAllDecision β ε δ ι α)), RaceAllState.result? s = none -> raceStep s decision = .ok after -> raceReplay s (decision :: tape) = raceReplay after tape := by
  intros
  rw [raceReplay]
  simp_all

/-- raceReplay_cons_error at the frozen observation boundary.
census: fork.race-all -/
theorem raceReplay_cons_error :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (decision : RaceAllDecision β ε δ ι α) (tape : List (RaceAllDecision β ε δ ι α)) (reason : Refusal), RaceAllState.result? s = none -> raceStep s decision = .error reason -> raceReplay s (decision :: tape) = .refused s reason := by
  intros
  rw [raceReplay]
  simp_all

/-- race_fixedTape_deterministic at the frozen observation boundary.
census: fork.race-all -/
theorem race_fixedTape_deterministic :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (tape : List (RaceAllDecision β ε δ ι α)) (left right : ReplayResult (RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α)), RaceRuns s tape left -> RaceRuns s tape right -> left = right := by
  intros
  simp_all [RaceRuns]

/-- race_first_accepted_stable at the frozen observation boundary.
census: fork.race-all -/
theorem race_first_accepted_stable :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s after : RaceAllState β ε δ ι α) (decision : RaceAllDecision β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), s.accepted = some exit -> raceStep s decision = .ok after -> after.accepted = some exit := by
  intro β ε δ ι α s after decision exit ha hs
  have hc : ∀ (state : RaceAllState β ε δ ι α) child value,
      state.accepted = some exit → (raceComplete state child value).accepted = some exit := by
    intro state child value h
    unfold raceComplete
    split <;> simp [h]
  cases decision with
  | beginLaunch => simp [raceStep, ha] at hs
  | finishLaunch immediate =>
    cases ht : s.starting with
    | none => simp [raceStep, ht] at hs
    | some child =>
      by_cases hm : child ∈ s.live
      · simp [raceStep, ht, hm] at hs
      · cases immediate with
        | none =>
          simp only [raceStep, ht, if_neg hm] at hs
          cases hs
          exact ha
        | some value =>
          simp only [raceStep, ht, if_neg hm] at hs
          cases hs
          exact hc _ child value ha
  | complete child value =>
    by_cases hm : child ∈ s.live
    · simp only [raceStep, if_pos hm] at hs
      cases hs
      exact hc s child value ha
    · simp [raceStep, hm] at hs
  | beginCleanup =>
    simp only [raceStep] at hs
    split at hs
    · cases hs
    · simp only [ha] at hs
      cases hs
      rfl
  | requestNext =>
    simp only [raceStep] at hs
    split at hs
    · cases hs
    · cases hr : s.requests with
      | nil => simp [hr] at hs
      | cons child rest =>
        simp only [hr] at hs
        cases hs
        exact ha

/-- race_result_requires_start_finished at the frozen observation boundary.
census: fork.race-all -/
theorem race_result_requires_start_finished :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), RaceAllState.result? s = some exit -> s.starting = none ∧ s.accepted = some exit := by
  intro β ε δ ι α s exit h
  unfold RaceAllState.result? at h
  split at h
  · cases h
  · rename_i hstart
    have hnone : s.starting = none := by simpa using hstart
    split at h
    · exact ⟨hnone, h⟩
    · split at h
      · exact ⟨hnone, h⟩
      · cases h

/-- race_cleanup_result_requires_publications at the frozen observation boundary.
census: fork.race-all -/
theorem race_cleanup_result_requires_publications :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), RaceAllState.result? s = some exit -> s.cleanupNeeded = true -> s.cleanupRequested = true ∧ ∃ wait, s.cleanup = some wait ∧ ∀ child, child ∈ wait.targets -> child ∈ wait.published := by
  intro β ε δ ι α s exit h hcleanup
  unfold RaceAllState.result? at h
  split at h
  · cases h
  · simp only [hcleanup, Bool.true_eq_false, ↓reduceIte] at h
    split at h
    · rename_i hready
      refine ⟨hready.1, ?_⟩
      cases hw : s.cleanup with
      | none => simp [hw] at hready
      | some wait =>
        refine ⟨wait, rfl, ?_⟩
        have hr := hready.2
        simp only [hw, Option.bind_some] at hr
        cases he : wait.ready? with
        | none => simp [he] at hr
        | some result => exact WaitState.ready_publications wait result he
    · cases h

/-- race_empty_frontier at the frozen observation boundary.
census: fork.race-all -/
theorem race_empty_frontier :
    forall {β : Type v} {ε δ ι α : Type u}, raceReplay (RaceAllState.initial [] : RaceAllState β ε δ ι α) [] = .frontier (RaceAllState.initial []) := by
  intros
  rfl

/-- race_single_success at the frozen observation boundary.
census: fork.race-all -/
theorem race_single_success :
    forall {β : Type v} {ε δ ι α : Type u}, forall (child : Effect4.FiberId) (value : β), ∃ after, raceReplay (RaceAllState.initial [child] : RaceAllState β ε δ ι α) [.beginLaunch, .finishLaunch (some (.success value))] = .done after (.success value) := by
  intros
  simp [raceReplay, RaceAllState.initial, RaceAllState.result?, raceStep,
    raceComplete]

/-- race_two_failures at the frozen observation boundary.
census: fork.race-all -/
theorem race_two_failures :
    forall {β : Type v} {ε δ ι α : Type u}, forall (left right : Effect4.FiberId) (first second : Effect4.Cause ε δ ι α), left ≠ right -> ∃ after, raceReplay (RaceAllState.initial [left, right] : RaceAllState β ε δ ι α) [.beginLaunch, .finishLaunch (some (.failure first)), .beginLaunch, .finishLaunch (some (.failure second))] = .done after (.failure ⟨first.reasons ++ second.reasons⟩) := by
  intros
  simp [raceReplay, RaceAllState.initial, RaceAllState.result?, raceStep,
    raceComplete]

end Effect4.Supervision
