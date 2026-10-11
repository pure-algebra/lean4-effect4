import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Run.Tape
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout
import ProofGraph.AxiomAudit

/-!
# Probe: release at most once (R11), the plan for four goals

A probe seat's file (history, not authority). It compiles with `lake env lean` in the seat's
worktree. It proves each of the four goals of the family modulo planned goals, and it proves the
cheap layers outright. `README.md` beside it is the plan.

* Section 1, **the run frame** (proved): every row of a run keeps the machine, or steps it by one
  decision that a run hands the machine: any decision but a direct answer, or an answer at a
  parked host call (`RunDecision`). So the machine of every scenario's script is reachable from
  the load by such decisions (`RunReachable`), and so it is `Guard.Reachable`.
* Section 2, **the reductions** (proved): each goal follows from a statement about every machine
  that a run of its program reaches. The statements read the cells only.
* Section 3, **the marks**: the trace events that count a registration, a release's start, an
  `onExit` push and a finalizer's start, and the static test `OncePlaced`.
* Section 4, **the general laws** (planned goals): control linearity in three readings, and R11
  per registration for releases and for `onExit`.
* Section 5, **the programs' facts** (planned goals) and the assemblies (proved modulo them): the
  static facts, the bridges, the order of the fetch's attempts, and `fetch_keeps`.
* Section 6, **finite controls**: the marks on real runs, the static test, and their red controls.

Placement of the probe's own theorems: concept `scope-lifetime-finalization`, requirement R11;
each docstring names the claim it serves and its consumer.
-/

set_option autoImplicit false

namespace Probe.ReleaseOnce

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session)
open Effect4.Api.Runner (Command)

/-! ## 1. The run frame -/

/-- A decision that a run hands its machine: any decision but a direct answer, or an answer at a
host call that a fiber is parked on. `HostSession.advance` refuses a direct answer, and
`HostSession.applyReply` steps the answer of a preflighted reply only. -/
def RunDecision (m : NativeMachine) : NativeDecision → Prop
  | .answerAsync fiber token _ => (requestOf m fiber token).isSome = true
  | _ => True

/-- The machines reachable from a program's load by decisions that a run hands the machine, each
at its own command budget. -/
inductive RunReachable (p : NativeEff) (t : RowTable) (cf : Nat) : NativeMachine → Prop
  | load : RunReachable p t cf (Api.load p cf)
  | step {m : NativeMachine} (fuel : Nat) (d : NativeDecision) :
      RunReachable p t cf m → RunDecision m d → RunReachable p t cf (steppedBy p fuel t m d)

/-- **A machine invariant that every run decision keeps**, at every command budget: the frame's
one premise for a step. -/
def MachineKeeps (p : NativeEff) (t : RowTable) (I : NativeMachine → Prop) : Prop :=
  ∀ (m : NativeMachine) (fuel : Nat) (d : NativeDecision), I m → RunDecision m d →
    I (steppedBy p fuel t m d)

/-- **The frame's lift**: an invariant of the load that every run decision keeps holds at every
machine a run reaches. With `scenario_runReachable`, it holds after every script. Claim served:
the frame of every goal over scripts; consumers: the coordinator's frame, and each family's
invariants. -/
theorem runReachable_keeps {p : NativeEff} {t : RowTable} {cf : Nat} {I : NativeMachine → Prop}
    (keeps : MachineKeeps p t I) (hload : I (Api.load p cf)) {m : NativeMachine}
    (h : RunReachable p t cf m) : I m := by
  induction h with
  | load => exact hload
  | step fuel d _ hd ih => exact keeps _ fuel d ih hd

/-- A machine that a run reaches is reachable by raw decisions (`Guard.Reachable`). Step of the
frame; its consumers are the general laws stated over `Guard.Reachable`. -/
theorem RunReachable.reachable {p : NativeEff} {t : RowTable} {cf : Nat} {m : NativeMachine}
    (h : RunReachable p t cf m) : Guard.Reachable p t cf m := by
  induction h with
  | load => exact Guard.reachable_load p t cf
  | step fuel d _ _ ih => exact Guard.reachable_step ih fuel d

/-- Step of the frame: a preflighted reply's decision answers a host call that a fiber is parked
on. -/
theorem preflight_runDecision {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (d : NativeDecision)
    (h : Api.HostSession.preflight s reply = .ok d) : RunDecision s.machine d := by
  obtain ⟨bound, _, _, env, rfl⟩ := Api.HostSession.preflight_envelope s reply d h
  show (requestOf s.machine (bound.record reply).fiber (bound.record reply).token).isSome = true
  rcases env with ⟨_, hreq, _⟩ | ⟨_, hreq, _⟩
  · rw [hreq]
    rfl
  · rw [hreq]
    rfl

/-- Step of the frame: a reply application keeps the machine or steps it by a run's decision. -/
theorem applyReply_machine {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat) :
    (Api.HostSession.applyReply s key fuel).session.machine = s.machine ∨
      ∃ d, RunDecision s.machine d ∧
        (Api.HostSession.applyReply s key fuel).session.machine =
          steppedBy program fuel table s.machine d := by
  unfold Api.HostSession.applyReply
  split
  · exact Or.inl rfl
  · rename_i n
    split
    · rename_i bound reply _ _
      split
      · exact Or.inl rfl
      · rename_i decision hpre
        dsimp only
        split
        · exact Or.inl rfl
        · split
          · exact Or.inr ⟨decision, preflight_runDecision s reply decision hpre, rfl⟩
          · exact Or.inr ⟨decision, preflight_runDecision s reply decision hpre, rfl⟩
    · exact Or.inl rfl

/-- Step of the frame: a control keeps the machine or steps it by a decision that is no direct
answer. -/
theorem advance_machine {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (d : NativeDecision) :
    (Api.HostSession.advance s fuel d).session.machine = s.machine ∨
      ∃ d', RunDecision s.machine d' ∧
        (Api.HostSession.advance s fuel d).session.machine =
          steppedBy program fuel table s.machine d' := by
  cases d with
  | answerAsync fiber token answer => exact Or.inl rfl
  | fire owner =>
    rcases Run.advance_step s fuel (.fire owner) with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨(.fire owner), trivial, by rw [h]; rfl⟩
  | flush =>
    rcases Run.advance_step s fuel .flush with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨.flush, trivial, by rw [h]; rfl⟩
  | evaluate fiber =>
    rcases Run.advance_step s fuel (.evaluate fiber) with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨(.evaluate fiber), trivial, by rw [h]; rfl⟩
  | yieldVerdict fiber verdict =>
    rcases Run.advance_step s fuel (.yieldVerdict fiber verdict) with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨(.yieldVerdict fiber verdict), trivial, by rw [h]; rfl⟩
  | interruptFrom who extra target =>
    rcases Run.advance_step s fuel (.interruptFrom who extra target) with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨(.interruptFrom who extra target), trivial, by rw [h]; rfl⟩
  | installMiddleware =>
    rcases Run.advance_step s fuel .installMiddleware with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨.installMiddleware, trivial, by rw [h]; rfl⟩
  | advance millis =>
    rcases Run.advance_step s fuel (.advance millis) with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨(.advance millis), trivial, by rw [h]; rfl⟩

/-- **Every row keeps the machine, or steps it by a decision that a run hands the machine.** The
receipt rows keep it (`bindCall_inert`, `submit_inert`, `src/Effect4/Laws/Run/Rows.lean`). Step of
the frame; its consumer is `play_runReachable`. -/
theorem step_machine (s : Run) (c : Command) :
    (s.step c).machine = s.machine ∨
      ∃ d, RunDecision s.machine d ∧
        (s.step c).machine = steppedBy s.built.program s.budget.fuel s.built.table s.machine d := by
  cases c with
  | bind call token =>
    exact Or.inl ((congrArg Session.machine (Run.step_session_bind s call token)).trans
      (Run.bindCall_inert s.session call token).1)
  | submit reply =>
    exact Or.inl ((congrArg Session.machine (Run.step_session_submit s reply)).trans
      (Run.submit_inert s.session reply).1)
  | apply key =>
    rcases applyReply_machine s.session key s.budget.fuel with e | ⟨d, hd, e⟩
    · exact Or.inl ((congrArg Session.machine (Run.step_session_apply s key)).trans e)
    · exact Or.inr ⟨d, hd, (congrArg Session.machine (Run.step_session_apply s key)).trans e⟩
  | control d =>
    rcases advance_machine s.session s.budget.fuel d with e | ⟨d', hd, e⟩
    · exact Or.inl ((congrArg Session.machine (Run.step_session_control s d)).trans e)
    · exact Or.inr ⟨d', hd, (congrArg Session.machine (Run.step_session_control s d)).trans e⟩

/-- Rows played keep the machine reachable by a run's decisions. Step of the frame. -/
theorem play_runReachable (s : Run) (rows : List Command) (cf : Nat)
    (h : RunReachable s.built.program s.built.table cf s.machine) :
    RunReachable s.built.program s.built.table cf (s.play rows).machine := by
  induction rows generalizing s with
  | nil => exact h
  | cons c rest ih =>
    rw [Run.play_cons]
    have hb : (s.step c).built = s.built := Run.step_built s c
    have hstep : RunReachable s.built.program s.built.table cf (s.step c).machine := by
      rcases step_machine s c with e | ⟨d, hd, e⟩
      · rw [e]
        exact h
      · rw [e]
        exact RunReachable.step _ _ h hd
    have next := ih (s.step c) (by rw [hb]; exact hstep)
    rw [hb] at next
    exact next

/-- **A scenario's machine is reachable by a run's decisions.** For every built program, name,
budget and script of the driver's alphabet, the machine that the script reaches from the opened
program is reachable from the program's load at the budget's compile fuel. Claim served: R11's
whole-run clause, read at a run (`docs/core/system-map.md` §8); consumers: the four reductions of
section 2. Reach: every move, raw rows included. It establishes nothing of the session's ledger. -/
theorem scenario_runReachable (b : Api.Built) (id : String) (budget : Api.Budget)
    (moves : List Test.Dogfood.Scenario.Move) :
    RunReachable b.program b.table budget.compileFuel
      (Test.Dogfood.Scenario.play (Run.open b id budget) moves).machine := by
  suffices key : ∀ (s : Run), s.built = b →
      RunReachable b.program b.table budget.compileFuel s.machine →
      RunReachable b.program b.table budget.compileFuel (Test.Dogfood.Scenario.play s moves).machine by
    exact key _ rfl (by rw [Run.open_machine]; exact RunReachable.load)
  intro s hs h
  induction moves generalizing s with
  | nil => exact h
  | cons mv rest ih =>
    apply ih (Test.Dogfood.Scenario.step s mv)
    · show (s.play (mv.rows s)).built = b
      rw [Run.play_built, hs]
    · show RunReachable _ _ _ (s.play (mv.rows s)).machine
      subst hs
      exact play_runReachable s (mv.rows s) budget.compileFuel h

/-! ## 2. The reductions: each goal from a statement about the machines a run reaches -/

/-- A cell of a machine, by its allocation index: what `Test.Dogfood.Scenario.cell` reads. -/
def cellAt (m : NativeMachine) (index : Nat) : Option Val := m.state.refs[index]?

/-- The machine-level form of `Workers.releases_once`: at every machine that a run of the crew
reaches, at every job count and compile budget, the `released` cell holds no connection twice. -/
def CrewReleased : Prop :=
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine),
    Effect4.Api.Author.build (Test.Dogfood.Scenario.Workers.crew total) = .ok b →
    RunReachable b.program b.table cf m →
    (Test.Dogfood.Scenario.Workers.entries (cellAt m 1)).Nodup

/-- **`Workers.releases_once` from its machine-level form.** Claim served:
`Workers.releases_once` (R11); consumer: the workers scenario's claim. -/
theorem workers_releases_once_of (h : CrewReleased) :
    Test.Dogfood.Scenario.Workers.ReleasesOnce := by
  intro total budget b moves hb
  exact h total budget.compileFuel b _ hb (scenario_runReachable b "workers" budget moves)

/-- The machine-level form of `QueueWorkers.releases_once`, with no budget premise: at every
machine that a run of the queue crew reaches, the `released` cell holds no connection twice. -/
def QueueCrewReleased : Prop :=
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine),
    Effect4.Api.Author.build (Test.Dogfood.Scenario.QueueWorkers.crew total) = .ok b →
    RunReachable b.program b.table cf m →
    (Test.Dogfood.Scenario.QueueWorkers.entries (cellAt m 2)).Nodup

/-- **`QueueWorkers.releases_once` from its machine-level form.** The goal's `funded` premise is
not used. Claim served: `QueueWorkers.releases_once` (R11); consumer: `queueWorkers`. -/
theorem queueWorkers_releases_once_of (h : QueueCrewReleased) :
    Test.Dogfood.Scenario.QueueWorkers.ReleasesOnce := by
  intro total fuel b moves hb _
  exact decide_eq_true
    (h total _ b _ hb (scenario_runReachable b "queue-workers" _ moves))

/-- The request identities of the shop's cleanup log, at a machine: what
`Atomic.Observation.cleaned` reads. -/
def cleanedAt (m : NativeMachine) : List Nat :=
  ({ decisions := [], window := none, account := none, completed := 0
     cleanups := Test.Dogfood.Scenario.Atomic.entries (cellAt m 2) } :
      Test.Dogfood.Scenario.Atomic.Observation).cleaned

/-- The machine-level form of `Atomic.cleans_once`: at every machine that a run of the shop
reaches, no request's number stands twice in the cleanup log. -/
def ShopCleaned : Prop :=
  ∀ (b : Api.Built) (m : NativeMachine),
    Effect4.Api.Author.build (Test.Dogfood.Scenario.Atomic.shop .none) = .ok b →
    RunReachable b.program b.table Test.Dogfood.Scenario.Atomic.budget.compileFuel m →
    (cleanedAt m).Nodup

/-- **`Atomic.cleans_once` from its machine-level form.** Claim served: `cleans_once` (R11);
consumer: the atomic scenario's claim. -/
theorem atomic_cleans_once_of (h : ShopCleaned) : Test.Dogfood.Scenario.Atomic.CleansOnce := by
  intro b moves hb
  exact h b _ hb (scenario_runReachable b "atomic" _ moves)

/-- `cleanupKeeps`'s reading, at a machine: the count cell and the cleanup log, as
`Timeout.observe` reads them. -/
def keepsAt (m : NativeMachine) : Bool :=
  ({ calls := [], receipts := [], applications := [], retired := [], stored := []
     attempts := match cellAt m 0 with
       | some (.nat n) => n
       | _ => 0
     cleanups := match cellAt m 1 with
       | some (.list entries) => entries
       | _ => []
     root := .running, timers := [] } : Test.Dogfood.Scenario.Timeout.Observation).cleanupKeeps

/-- The machine-level form of `Timeout.cleanup_keeps`: at every machine that a run of the fetch
reaches, the cleanup log names the attempts 1, 2, … once each and in order, and the count is the
log's length or one more. It is stated over `RunReachable`, not over `Guard.Reachable`: a direct
answer to the root's park breaks it (`scratch/SearchTimeout.lean`, the machine-level red
control). -/
def FetchKeeps : Prop :=
  ∀ (b : Api.Built) (m : NativeMachine),
    Effect4.Api.Author.build Test.Dogfood.Scenario.Timeout.fetch = .ok b →
    RunReachable b.program b.table Test.Dogfood.Scenario.Timeout.budget.compileFuel m →
    keepsAt m = true

/-- **`Timeout.cleanup_keeps` from its machine-level form.** Claim served: `cleanup_keeps` (R11);
consumer: the timeout scenario's claim. -/
theorem timeout_cleanup_keeps_of (h : FetchKeeps) : Test.Dogfood.Scenario.Timeout.CleanupKeeps := by
  intro b moves hb
  exact h b _ hb (scenario_runReachable b "timeout" _ moves)

/-! ## 3. The marks of the trace, and the static placement

The machine's trace is its history: `RunMachine.emit` only appends to it, and the law graph says
so (`RunMachine.Extends`, `src/Effect4/Laws/Machine/Approximation.lean`). The frame machine
traces every frame push with its frame, and a compiled frame's name carries its program point.
So the entry of a node is a countable event. The marks below are the ones the four goals read. -/

/-- An event of the native machine's trace. -/
abbrev NEvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- A release's registration at the `acquireRelease` at path `q`: the frame pushed before the
release is added to its scope (`EffName.afterScopeAdd`, `resolve`'s `acquired` arm,
`src/Effect4/Program/Compile.lean`). -/
def registersAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onSuccess _ (.afterScopeAdd _ (.foreign c)))) => c.path == q
  | _ => false

/-- A release's start, for the `acquireRelease` at path `q`: the frame pushed when the release
begins (`EffName.releaseUnder`, `suspendBodyAt`'s `Thunk.foreign` arm). -/
def releaseStartsAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onSuccess _ (.releaseUnder p _ _))) => p.path == q
  | _ => false

/-- An `onExit` registration at path `q`, on any fiber: its frame pushed. -/
def onExitPushAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onExit _ (.fin p) _)) => p.path == q
  | _ => false

/-- An `onExit` finalizer's start, for the `onExit` at path `q`, on any fiber
(`evaluatePrim.finalizerOr`, or the frame machine's pure shortcut). -/
def finStartAt (q : List Nat) : NEvent → Bool
  | .finalizerProgram _ (.fin p) _ => p.path == q
  | .frame _ (.ranFinalizer (.fin p) _) => p.path == q
  | _ => false

/-- The same two `onExit` marks, on one fiber. -/
def onExitPushOn (f : FiberId) (q : List Nat) : NEvent → Bool
  | .frame g (.pushed (.onExit _ (.fin p) _)) => g == f && p.path == q
  | _ => false

def finStartOn (f : FiberId) (q : List Nat) : NEvent → Bool
  | .finalizerProgram g (.fin p) _ => g == f && p.path == q
  | .frame g (.ranFinalizer (.fin p) _) => g == f && p.path == q
  | _ => false

/-- Whether a node runs its child at this index at most once each time the node itself runs.
Excluded: an `iterate`'s body, a `whileTrue`'s statements, the definition bodies and the
invocation arguments (each can run many times per run of the node), and the layers (a memo
build is shared). -/
def onceChild : Node NativeOp → Nat → Bool
  | .eff (.suspend _), 0 => true
  | .eff (.bind _ _), _ => true
  | .eff (.gen _), 0 => true
  | .eff (.catchCause _ _), _ => true
  | .eff (.matchCause _ _ _), _ => true
  | .eff (.onExit _ _), _ => true
  | .eff (.exit _), 0 => true
  | .eff (.uninterruptible _), 0 => true
  | .eff (.interruptible _), 0 => true
  | .eff (.withFiber _), 0 => true
  | .eff (.scoped _), 0 => true
  | .eff (.acquireRelease _ _), _ => true
  | .eff (.provideLayer _ _ _), 1 => true
  | .eff (.provideService _ _ _), 0 => true
  | .eff (.catchIf _ _ _), _ => true
  | .eff (.select _ _ _ _), _ => true
  | .eff (.restore _ _), 0 => true
  | .eff (.defs _ _ _ _), 1 => true
  | .action (.fork _ _), 0 => true
  | .action (.forkIn _ _ _), 0 => true
  | .action (.forkScoped _ _), 0 => true
  | .action (.raceAll _), 0 => true
  | .effs (.cons _ _), _ => true
  | .stmts (.cons _ _), _ => true
  | .stmt (.bindYield _), 0 => true
  | .stmt (.yieldDiscard _), 0 => true
  | .stmt (.ifElse _ _ _), _ => true
  | _, _ => false

/-- **A once-placed node.** Every step of its path from the root is a once step, so the node
runs at most once per run of the program. A static, decidable test of the program tree. -/
def OncePlaced : Node NativeOp → List Nat → Bool
  | _, [] => true
  | n, i :: rest =>
    onceChild n i &&
      match n.child i with
      | some c => OncePlaced c rest
      | none => false

/-- A node once-placed below a fork's program: the walk starts at the node at `site`, the
program that a fiber forked there runs. -/
def OncePlacedBelow (root : Node NativeOp) (site : List Nat) (q : List Nat) : Bool :=
  site.isPrefixOf q &&
    match root.at_ site with
    | some n => OncePlaced n (q.drop site.length)
    | none => false

/-! ### The base case, and two decisions that record nothing

Each general law of section 4 is an inequality between counts of the trace, carried along a run.
Its base case holds at the load, whose trace is empty. Two decisions emit no event, so they keep
every count: these are the frame cases of each law's step. -/

/-- The load's trace is empty. Step of each general law's base case. -/
theorem load_trace (p : NativeEff) (cf : Nat) : (Api.load p cf).trace = [] := rfl

/-- **The base case of every law of section 4**: at the load, every count of the trace is zero.
Claim served: each law's base case; consumers: the laws' proofs. -/
theorem load_count (p : NativeEff) (cf : Nat) (e : NEvent → Bool) :
    (Api.load p cf).trace.countP e = 0 := by
  rw [load_trace]
  rfl

/-- A yield verdict keeps the trace: it writes one fiber's override and emits nothing. Frame case
of each law's step. -/
theorem yieldVerdict_trace (p : NativeEff) (t : RowTable) (fuel : Nat) (m : NativeMachine)
    (id : FiberId) (verdict : Bool) :
    (steppedBy p fuel t m (.yieldVerdict id verdict)).trace = m.trace := by
  show (RunMachine.modify m id fun f => { f with yieldOverride := some verdict }).trace = m.trace
  unfold RunMachine.modify
  split
  · rfl
  · rfl

/-- The middleware latch keeps the trace. Frame case of each law's step. -/
theorem installMiddleware_trace (p : NativeEff) (t : RowTable) (fuel : Nat) (m : NativeMachine) :
    (steppedBy p fuel t m .installMiddleware).trace = m.trace := rfl

/-! ## 4. The general laws (planned goals)

Each is placed in concept `scope-lifetime-finalization` and requirement R11. Each is stated over
`Guard.Reachable`: every raw decision at every budget, so a run's machines are among them
(`RunReachable.reachable`). -/

/-- **Control linearity, read at a release.** A release whose `acquireRelease` is once-placed in
the program is registered at most once along any run. Claim served: R11's whole-run clause "at
most once per registration" (proposed claim `release-at-most-once`); consumers: the bridges of the
two crews. Route: a coverage invariant (`README.md`, "The one general theorem"), carried through
each decision by `Guard.reachable_lift_pure`. It says nothing of a release under a loop. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal once_placed_registers_once :
    ∀ (p : NativeEff) (t : RowTable) (cf : Nat) (m : NativeMachine) (q : List Nat),
      OncePlaced (Node.eff p) q = true → Guard.Reachable p t cf m →
      m.trace.countP (registersAt q) ≤ 1

/-- **R11 per registration, for a compiled release.** Along any run, the releases that start for
the `acquireRelease` at a path are no more than its registrations there. It is the scope's own
`close_twice` and `closeOrder_eq` carried through the store, the close walks and the immediate
run of a registration after close. Claim served: `release-at-most-once`; consumers: the crews'
assemblies. It holds at every path, once-placed or not. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal release_starts_le_registrations :
    ∀ (p : NativeEff) (t : RowTable) (cf : Nat) (m : NativeMachine) (q : List Nat),
      Guard.Reachable p t cf m →
      m.trace.countP (releaseStartsAt q) ≤ m.trace.countP (registersAt q)

/-- **Control linearity, read at an `onExit`.** A once-placed `onExit` is pushed at most once
along any run, on all fibers together. Claim served: `release-at-most-once`; consumer: the shop's
assembly. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal once_placed_pushes_once :
    ∀ (p : NativeEff) (t : RowTable) (cf : Nat) (m : NativeMachine) (q : List Nat),
      OncePlaced (Node.eff p) q = true → Guard.Reachable p t cf m →
      m.trace.countP (onExitPushAt q) ≤ 1

/-- **R11 per registration, for an `onExit`.** Along any run, the finalizer starts of the `onExit`
at a path are no more than its pushes, on all fibers together. A pushed `OnExit` frame is popped
at most once, and its finalizer starts only at that pop. Claim served: `release-at-most-once`;
consumer: the shop's assembly. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal finalizer_starts_le_pushes :
    ∀ (p : NativeEff) (t : RowTable) (cf : Nat) (m : NativeMachine) (q : List Nat),
      Guard.Reachable p t cf m →
      m.trace.countP (finStartAt q) ≤ m.trace.countP (onExitPushAt q)

/-- The fiber a machine forked at a site, by fork order: the `n`-th fiber whose fork record names
the site. -/
def forkedAt (m : NativeMachine) (site : List Nat) : List FiberId :=
  (m.forks.filter (·.site == site)).map (·.child)

/-- **Control linearity per fiber.** A node once-placed below a fork's program is entered at most
once on each fiber forked there: the `onExit` is pushed at most once, and its finalizer starts at
most once. Claim served: `release-at-most-once`, per activation; consumer: `fetch_keeps`'s proof
(the attempt's `onExit` is under the retry loop, so it is once-placed per attempt fiber only). -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal once_placed_below_fiber :
    ∀ (p : NativeEff) (t : RowTable) (cf : Nat) (m : NativeMachine) (site q : List Nat)
      (f : FiberId),
      OncePlacedBelow (Node.eff p) site q = true → Guard.Reachable p t cf m →
      f ∈ forkedAt m site →
      m.trace.countP (onExitPushOn f q) ≤ 1 ∧ m.trace.countP (finStartOn f q) ≤ 1

/-! ## 5. The programs' facts (planned goals) and the assemblies -/

/-- The paths of the crew's two `acquireRelease` nodes in its built program, by worker identity:
read off the named runs' traces (`scratch/marks.out`). -/
def crewAcquire : Nat → List Nat
  | 1 => [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

/-- **The crew's static facts.** In the crew's built program, at every job count, both workers'
`acquireRelease` nodes are once-placed. Decidable on the program tree. Claim served:
`Workers.releases_once`; consumer: `crew_released`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal crew_acquire_once_placed :
    ∀ (total : Nat) (b : Api.Built),
      Effect4.Api.Author.build (Test.Dogfood.Scenario.Workers.crew total) = .ok b →
      ∀ i ∈ [1, 2], OncePlaced (Node.eff b.program) (crewAcquire i) = true

/-- **The crew's bridge: the released cell is its two releases' writes.** At every machine that a
run of the crew reaches, every entry of the `released` cell is a worker's identity, and identity
`i` stands no more often than worker `i`'s release has started. It needs the census of the cell's
writers (handle provenance) and the release's straight body. Claim served:
`Workers.releases_once`; consumer: `crew_released`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal crew_released_by_releases :
    ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine),
      Effect4.Api.Author.build (Test.Dogfood.Scenario.Workers.crew total) = .ok b →
      RunReachable b.program b.table cf m →
      (∀ v ∈ Test.Dogfood.Scenario.Workers.entries (cellAt m 1), v = .nat 1 ∨ v = .nat 2) ∧
      ∀ i ∈ [1, 2], (Test.Dogfood.Scenario.Workers.entries (cellAt m 1)).count (.nat i) ≤
        m.trace.countP (releaseStartsAt (crewAcquire i))

/-- Step of the assemblies: a list each of whose entries stands at most once is free of
duplicates, read through a bound on each listed value. -/
theorem nodup_of_count_le_one {α : Type} [DecidableEq α] (l : List α) (vs : List α)
    (hmem : ∀ v ∈ l, v ∈ vs) (hcount : ∀ v ∈ vs, l.count v ≤ 1) : l.Nodup := by
  rw [List.nodup_iff_count]
  intro v
  exact if hv : v ∈ l then hcount v (hmem v hv)
    else (List.count_eq_zero_of_not_mem hv).symm ▸ Nat.zero_le 1

/-- **The crew's machine-level goal, assembled.** Claim served: `Workers.releases_once`;
consumer: `workers_releases_once_of`. Proved modulo the five goals it uses. -/
theorem crew_released : CrewReleased := by
  intro total cf b m hb hm
  obtain ⟨hall, hcount⟩ := crew_released_by_releases total cf b m hb hm
  refine nodup_of_count_le_one _ [.nat 1, .nat 2] ?_ ?_
  · intro v hv
    rcases hall v hv with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro v hv
    have hv' : v = .nat 1 ∨ v = .nat 2 := by
      rcases List.mem_cons.mp hv with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.mp h)
    rcases hv' with rfl | rfl
    · exact Nat.le_trans (hcount 1 List.mem_cons_self)
        (Nat.le_trans (release_starts_le_registrations _ _ _ _ _ hm.reachable)
          (once_placed_registers_once _ _ _ _ _
            (crew_acquire_once_placed total b hb 1 List.mem_cons_self) hm.reachable))
    · exact Nat.le_trans (hcount 2 (List.mem_cons_of_mem _ List.mem_cons_self))
        (Nat.le_trans (release_starts_le_registrations _ _ _ _ _ hm.reachable)
          (once_placed_registers_once _ _ _ _ _
            (crew_acquire_once_placed total b hb 2 (List.mem_cons_of_mem _ List.mem_cons_self))
            hm.reachable))

/-- **`Workers.releases_once`, proved modulo its planned goals.** -/
theorem workers_releases_once : Test.Dogfood.Scenario.Workers.ReleasesOnce :=
  workers_releases_once_of crew_released

/-! ### The queue crew -/

/-- The paths of the queue crew's three `acquireRelease` nodes: workers 1 and 2, the feeder 3. -/
def queueAcquire : Nat → List Nat
  | 1 => [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]

/-- **The queue crew's static facts.** Claim served: `QueueWorkers.releases_once`; consumer:
`queueCrew_released`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal queueCrew_acquire_once_placed :
    ∀ (total : Nat) (b : Api.Built),
      Effect4.Api.Author.build (Test.Dogfood.Scenario.QueueWorkers.crew total) = .ok b →
      ∀ i ∈ [1, 2, 3], OncePlaced (Node.eff b.program) (queueAcquire i) = true

/-- **The queue crew's bridge.** As the crew's, with three members. The queue's operations write
the queue's cell and no other: the census needs that. Claim served: `QueueWorkers.releases_once`;
consumer: `queueCrew_released`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal queueCrew_released_by_releases :
    ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine),
      Effect4.Api.Author.build (Test.Dogfood.Scenario.QueueWorkers.crew total) = .ok b →
      RunReachable b.program b.table cf m →
      (∀ v ∈ Test.Dogfood.Scenario.QueueWorkers.entries (cellAt m 2),
        v = .nat 1 ∨ v = .nat 2 ∨ v = .nat 3) ∧
      ∀ i ∈ [1, 2, 3], (Test.Dogfood.Scenario.QueueWorkers.entries (cellAt m 2)).count (.nat i) ≤
        m.trace.countP (releaseStartsAt (queueAcquire i))

/-- **The queue crew's machine-level goal, assembled.** Proved modulo its planned goals. -/
theorem queueCrew_released : QueueCrewReleased := by
  intro total cf b m hb hm
  obtain ⟨hall, hcount⟩ := queueCrew_released_by_releases total cf b m hb hm
  have once : ∀ i ∈ [1, 2, 3],
      (Test.Dogfood.Scenario.QueueWorkers.entries (cellAt m 2)).count (.nat i) ≤ 1 := fun i hi =>
    Nat.le_trans (hcount i hi)
      (Nat.le_trans (release_starts_le_registrations _ _ _ _ _ hm.reachable)
        (once_placed_registers_once _ _ _ _ _
          (queueCrew_acquire_once_placed total b hb i hi) hm.reachable))
  refine nodup_of_count_le_one _ [.nat 1, .nat 2, .nat 3] ?_ ?_
  · intro v hv
    rcases hall v hv with rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact once 1 List.mem_cons_self
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact once 2 (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [List.mem_singleton.mp hv]
        exact once 3 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **`QueueWorkers.releases_once`, proved modulo its planned goals**, without its `funded`
premise. -/
theorem queueWorkers_releases_once : Test.Dogfood.Scenario.QueueWorkers.ReleasesOnce :=
  queueWorkers_releases_once_of queueCrew_released

/-! ### The shop -/

/-- The paths of the shop's six requests' `onExit` nodes, by request number. -/
def shopRequest : Nat → List Nat
  | 1 => [1, 1, 1, 1, 0, 0, 0]
  | 2 => [1, 1, 1, 1, 1, 0, 0, 0]
  | 3 => [1, 1, 1, 1, 1, 1, 0, 0, 0]
  | 4 => [1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
  | 5 => [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]

/-- **The shop's static facts.** Claim served: `cleans_once`; consumer: `shop_cleaned`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal shop_requests_once_placed :
    ∀ (b : Api.Built), Effect4.Api.Author.build (Test.Dogfood.Scenario.Atomic.shop .none) = .ok b →
      ∀ i ∈ [1, 2, 3, 4, 5, 6], OncePlaced (Node.eff b.program) (shopRequest i) = true

/-- **The shop's bridge: the cleanup log is its six finalizers' writes.** At every machine that a
run of the shop reaches, every identity in the cleanup log is a request's number, and number `i`
stands no more often than request `i`'s finalizer has started. Claim served: `cleans_once`;
consumer: `shop_cleaned`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal shop_cleaned_by_finalizers :
    ∀ (b : Api.Built) (m : NativeMachine),
      Effect4.Api.Author.build (Test.Dogfood.Scenario.Atomic.shop .none) = .ok b →
      RunReachable b.program b.table Test.Dogfood.Scenario.Atomic.budget.compileFuel m →
      (∀ i ∈ cleanedAt m, i ∈ [1, 2, 3, 4, 5, 6]) ∧
      ∀ i ∈ [1, 2, 3, 4, 5, 6], (cleanedAt m).count i ≤ m.trace.countP (finStartAt (shopRequest i))

/-- **The shop's machine-level goal, assembled.** Proved modulo its planned goals. -/
theorem shop_cleaned : ShopCleaned := by
  intro b m hb hm
  obtain ⟨hall, hcount⟩ := shop_cleaned_by_finalizers b m hb hm
  exact nodup_of_count_le_one _ [1, 2, 3, 4, 5, 6] hall fun i hi =>
    Nat.le_trans (hcount i hi)
      (Nat.le_trans (finalizer_starts_le_pushes _ _ _ _ _ hm.reachable)
        (once_placed_pushes_once _ _ _ _ _ (shop_requests_once_placed b hb i hi) hm.reachable))

/-- **`Atomic.cleans_once`, proved modulo its planned goals.** -/
theorem atomic_cleans_once : Test.Dogfood.Scenario.Atomic.CleansOnce :=
  atomic_cleans_once_of shop_cleaned

/-! ### The fetch -/

/-- The attempt's fork site and its `onExit`, in the fetch's built program, read off the fork
records and the trace of the timeout scenario's run `four`. -/
def attemptSite : List Nat := [1, 1, 0, 0, 1, 0, 0, 0, 0]
def attemptExit : List Nat := [1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

/-- Whether a fiber of a machine has exited. -/
def exitedIn (m : NativeMachine) (f : FiberId) : Bool := ((m.fiber? f).bind (·.exit)).isSome

/-- **The attempts run one at a time.** At every machine that a run of the fetch reaches, every
attempt fiber but the last one forked has exited. The timeout form awaits its attempt's exit
before it returns (`join entrant`, or `Action.interrupt entrant`), and the retry loop forks the
next attempt only after that. It needs the join law over `RunReachable`: a direct answer to the
root's join breaks it (`scratch/SearchTimeout.lean`). Claim served: `cleanup_keeps`; consumer:
`fetch_keeps`'s proof (`README.md`, section 4.4). -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal fetch_attempts_ordered :
    ∀ (b : Api.Built) (m : NativeMachine),
      Effect4.Api.Author.build Test.Dogfood.Scenario.Timeout.fetch = .ok b →
      RunReachable b.program b.table Test.Dogfood.Scenario.Timeout.budget.compileFuel m →
      ∀ f ∈ (forkedAt m attemptSite).dropLast, exitedIn m f = true

/-- **The fetch's machine-level goal** (program-specific; `README.md`, section 4.4, gives its
decomposition: per-fiber linearity, the attempts' order, each attempt's phases, and the census of
the two cells). Claim served: `cleanup_keeps`; consumer: `timeout_cleanup_keeps`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal fetch_keeps : FetchKeeps

/-- **`Timeout.cleanup_keeps`, proved modulo `fetch_keeps`.** -/
theorem timeout_cleanup_keeps : Test.Dogfood.Scenario.Timeout.CleanupKeeps :=
  timeout_cleanup_keeps_of fetch_keeps

/-! ## 6. Finite controls

Finite evaluations that no theorem covers. They tie the marks of section 3 to the events that real
runs record, so that no planned goal above is true by an empty count, and they keep the red
controls of the static test and of the bridges. -/

/-- The queue take's `onExit` under worker 2's loop, in the queue crew's built program. -/
def queueTakeExit : List Nat :=
  [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0]

/-- A named run of a scenario's record, played. -/
def playedRun (runs : List Test.Dogfood.Scenario.NamedRun) (name : String) : Option Run :=
  (runs.find? (·.name == name)).map (·.played)

-- Green, the static test: both workers' `acquireRelease` nodes are once-placed (job count 2).
#guard match Effect4.Api.Author.build (Test.Dogfood.Scenario.Workers.crew 2) with
  | .ok b => [1, 2].all fun i => OncePlaced (Node.eff b.program) (crewAcquire i)
  | .error _ => false

-- Green, the static test: the queue crew's three `acquireRelease` nodes (job count 3).
#guard match Effect4.Api.Author.build (Test.Dogfood.Scenario.QueueWorkers.crew 3) with
  | .ok b => [1, 2, 3].all fun i => OncePlaced (Node.eff b.program) (queueAcquire i)
  | .error _ => false

-- Red, the static test: the queue take's `onExit` stands under the worker's loop.
#guard match Effect4.Api.Author.build (Test.Dogfood.Scenario.QueueWorkers.crew 3) with
  | .ok b => !OncePlaced (Node.eff b.program) queueTakeExit
  | .error _ => false

-- Green, the static test: the shop's six `onExit` nodes are once-placed.
#guard match Effect4.Api.Author.build (Test.Dogfood.Scenario.Atomic.shop .none) with
  | .ok b => [1, 2, 3, 4, 5, 6].all fun i => OncePlaced (Node.eff b.program) (shopRequest i)
  | .error _ => false

-- Red and green, the static test: the attempt's `onExit` stands under the retry loop, and it is
-- once-placed below the attempt's fork site.
#guard match Effect4.Api.Author.build Test.Dogfood.Scenario.Timeout.fetch with
  | .ok b =>
    !OncePlaced (Node.eff b.program) attemptExit &&
      OncePlacedBelow (Node.eff b.program) attemptSite attemptExit
  | .error _ => false

-- Green, the marks: on the workers' run `lowest`, each worker's release is registered once and
-- starts once, and the released cell holds each identity once.
#guard match playedRun Test.Dogfood.Scenario.Workers.runsAndControls.1 "lowest" with
  | some s =>
    [1, 2].all (fun i =>
      s.machine.trace.countP (registersAt (crewAcquire i)) == 1 &&
        s.machine.trace.countP (releaseStartsAt (crewAcquire i)) == 1) &&
      Test.Dogfood.Scenario.Workers.entries (cellAt s.machine 1) == [.nat 2, .nat 1]
  | none => false

-- Red, the bridge: on the run `twice`, identity 1 stands twice in the released cell, and the
-- release at worker 1's first `acquireRelease` started once.
#guard match playedRun Test.Dogfood.Scenario.Workers.runsAndControls.1 "twice" with
  | some s =>
    (Test.Dogfood.Scenario.Workers.entries (cellAt s.machine 1)).count (.nat 1) == 2 &&
      s.machine.trace.countP (releaseStartsAt (crewAcquire 1)) == 1
  | none => false

-- Green, the marks: on the shop's run `started`, requests 1 to 5 each push their `onExit` once
-- and start their finalizer once.
#guard match playedRun Test.Dogfood.Scenario.Atomic.runsAndControls.1 "started" with
  | some s =>
    [1, 2, 3, 4, 5].all fun i =>
      s.machine.trace.countP (onExitPushAt (shopRequest i)) == 1 &&
        s.machine.trace.countP (finStartAt (shopRequest i)) == 1
  | none => false

-- Green, the marks per fiber: on the timeout scenario's run `four`, the four attempt fibers each
-- push the attempt's `onExit` once and start its finalizer once; per path the counts are four.
#guard match playedRun Test.Dogfood.Scenario.Timeout.runsAndControls.1 "four" with
  | some s =>
    forkedAt s.machine attemptSite == [⟨1⟩, ⟨5⟩, ⟨9⟩, ⟨13⟩] &&
      (forkedAt s.machine attemptSite).all (fun f =>
        s.machine.trace.countP (onExitPushOn f attemptExit) == 1 &&
          s.machine.trace.countP (finStartOn f attemptExit) == 1) &&
      s.machine.trace.countP (onExitPushAt attemptExit) == 4
  | none => false

-- Green, the attempts' order: on every named run of the timeout scenario, every attempt fiber but
-- the last one forked has exited.
#guard Test.Dogfood.Scenario.Timeout.runsAndControls.1.all fun run =>
  (forkedAt run.played.machine attemptSite).dropLast.all (exitedIn run.played.machine)

/-! ## The audit of the probe's own declarations

`#axiom_audit` walks imported modules. This file is no module, so the command below runs the
gate's walk (`ProofGraph.reachedAxiomsMany`, with planned goals as leaves) over every declaration
of this file's namespace. -/

open Lean Elab Command in
/-- The gate's walk over the probe's declarations, as `#axiom_audit` reports a module. -/
elab "#probe_axiom_audit" : command => do
  let env ← getEnv
  let roots := (env.constants.map₂.toList.map (·.1)).filter fun n =>
    (`Probe.ReleaseOnce).isPrefixOf n && !n.isInternal
  let goals := roots.filter (ProofGraph.isGoal env)
  let walked := (roots.filter (!ProofGraph.isGoal env ·)).toArray
  let (results, _) := ProofGraph.reachedAxiomsMany env walked {} (ProofGraph.isGoal env)
  let mut offenders : Array MessageData := #[]
  let mut modulo : Nat := 0
  for (name, result) in walked.zip results do
    match result with
    | none => offenders := offenders.push m!"{name}: the walk ran out of its step budget"
    | some reached =>
      let outside := reached.filter fun axiomName =>
        !ProofGraph.trustedAxioms.contains axiomName && !ProofGraph.isGoal env axiomName
      if !outside.isEmpty then offenders := offenders.push m!"{name} reaches {outside}"
      if reached.any (ProofGraph.isGoal env) then modulo := modulo + 1
  if offenders.isEmpty then
    logInfo m!"probe audit: {walked.size} declarations within [propext, Quot.sound], \
      {modulo} of them modulo planned goals; {goals.length} planned goals"
  else
    throwError m!"probe audit: {offenders.size} declarations reach axioms outside \
      [propext, Quot.sound]: {offenders}"

#probe_axiom_audit

end Probe.ReleaseOnce
