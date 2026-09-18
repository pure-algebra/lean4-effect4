import Effect4.Laws.Api.Supervision
import Effect4.Program.Profile

/-!
# Supervision contract: three runs, read for who holds what

Three programs on the raw route (`Api.run`, `src/Effect4/Api.lean:314`), one per shape the
supervision data has to separate:

* `childFork` — a tracked child, awaited. Everything exits; the run is quiet because nothing
  is alive.
* `looseDaemon` — DI-75's `g78`: a daemon forked by a root that exits first, parked on a host
  call nobody answers. It is alive when the run ends and nobody holds it. This is the **red
  control**: `daemonsQuiet` is `false` here and `true` in the other two, so the check has
  teeth.
* `pinnedDaemon` — a `forkScoped` inside a scope that stays open, both halves parked. The
  daemon is alive and *held*, so the run is quiet with something still running. It also shows
  the rc.112 override: the program writes `daemon := false` and the machine forks a daemon
  anyway (`internal/effect.ts:5406`).

Every static `#guard` reads `supervision`, every dynamic one reads `fiberStatuses` of the
machine the run left. The two are joined by the `forked` events: the flag on each event is
the flag of the site at that path, which is `supervision_static`
(`src/Effect4/Laws/Api/Supervision.lean`) on a real run.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Test.Api.SupervisionContract

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api (ForkSite ForkKind FiberStatus)

/-! ## The table and the three programs -/

def table : RowTable := [Profile.Scalar.waitRow]

/-- A host call nobody answers: the park that keeps a fiber alive to the end of the run. -/
def wait (request : Nat) : Api.Program := .perform (.external 0) (.lit (.nat request))

/-- A tracked child, forked immediately and joined. -/
def childFork : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩))
    (.awaitFiber (.var 0) .joinEffect)

/-- DI-75's `g78`: a daemon the root forks and then outlives. The daemon parks on a call
nobody answers, so it is still there when the run ends. -/
def looseDaemon : Api.Program :=
  .bind (.withFiber (.fork (wait 2) ⟨true, true, .interruptible⟩))
    (.succeed (.lit (.nat 0)))

/-- A `forkScoped` inside a scope that stays open: the fork is written `daemon := false` and
the machine forks a daemon at the pin anyway. Both halves park, so the scope never closes and
the pinned daemon is alive when the run ends. -/
def pinnedDaemon : Api.Program :=
  .scoped (.bind (.withFiber (.forkScoped (wait 2) ⟨true, false, .inherit⟩)) (wait 3))

def childRun : Api.Inspection := Api.run childFork 400 [] table
def looseRun : Api.Inspection := Api.run looseDaemon 400 [] table
def pinnedRun : Api.Inspection := Api.run pinnedDaemon 400 [] table

/-! ## Supervision before the run: one site each, of three different kinds -/

#guard Api.supervision childFork = [⟨[0, 0], .child, ⟨true, false, .interruptible⟩⟩]
#guard Api.supervision looseDaemon = [⟨[0, 0], .daemon, ⟨true, true, .interruptible⟩⟩]
#guard Api.supervision pinnedDaemon = [⟨[0, 0, 0], .pinned none, ⟨true, false, .inherit⟩⟩]

-- Each site's path names the node that forks, and its body the program forked there.
#guard ((Api.supervision childFork).map fun s => (Node.eff childFork).at_ s.path) =
  [some (Node.action (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩))]
#guard ((Api.supervision looseDaemon).map fun s => (Node.eff looseDaemon).at_ s.body) =
  [some (Node.eff (wait 2))]
#guard ((Api.supervision pinnedDaemon).map fun s => (Node.eff pinnedDaemon).at_ s.body) =
  [some (Node.eff (wait 2))]

-- `isDaemon` is the kind alone: only the tracked child is not a daemon, and the `forkScoped`
-- site is a daemon although the program wrote `daemon := false`.
#guard (Api.supervision childFork).map ForkSite.isDaemon = [false]
#guard (Api.supervision looseDaemon).map ForkSite.isDaemon = [true]
#guard (Api.supervision pinnedDaemon).map ForkSite.isDaemon = [true]
#guard (Api.supervision pinnedDaemon).map (fun s => s.options.daemon) = [false]

-- The whole-program law `supervision_child_flag` on these three: a site the table calls a
-- tracked child was written `daemon := false`.
#guard [childFork, looseDaemon, pinnedDaemon].all fun p =>
  (Api.supervision p).all fun s => s.kind != ForkKind.child || !s.options.daemon

/-! ## `supervision_static` on a real run: the event's flag is the site's -/

#guard Api.Inspection.forked childRun = [(⟨0⟩, ⟨1⟩, false)]
#guard Api.Inspection.forked looseRun = [(⟨0⟩, ⟨1⟩, true)]
#guard Api.Inspection.forked pinnedRun = [(⟨0⟩, ⟨1⟩, true)]

#guard [(childFork, childRun), (looseDaemon, looseRun), (pinnedDaemon, pinnedRun)].all
  fun entry => (Api.Inspection.forked entry.2).map (fun e => e.2.2) ==
    (Api.supervision entry.1).map ForkSite.isDaemon

/-! ## The fibers of each run -/

/-- The alternative a status is, as a number, so a guard reads without an exit value. -/
def tagOf : FiberStatus → Nat
  | .child _ => 0
  | .pinned _ _ => 1
  | .daemon => 2
  | .root => 3
  | .exited _ => 4

def tags (r : Api.Inspection) : List (FiberId × Nat) :=
  (Api.Inspection.fibers r).map fun entry => (entry.1, tagOf entry.2)

-- The child fork: root and child both exit.
#guard tags childRun = [(⟨0⟩, 4), (⟨1⟩, 4)]
#guard childRun.exit = some (.success (.nat 1))
#guard Api.Inspection.unpinnedDaemonsAlive childRun = []
#guard Api.Inspection.daemonsQuiet childRun

-- The loose daemon: the root exited, the daemon is alive and nobody holds it.
#guard tags looseRun = [(⟨0⟩, 4), (⟨1⟩, 2)]
#guard looseRun.exit = some (.success (.nat 0))
#guard Api.Inspection.unpinnedDaemonsAlive looseRun = [⟨1⟩]
#guard Api.Inspection.daemonsQuiet looseRun = false

-- The pinned daemon: the root is the run's own fiber, still parked; the daemon is alive and
-- held by the scope, so the run is quiet although something is running.
#guard tags pinnedRun = [(⟨0⟩, 3), (⟨1⟩, 1)]
#guard pinnedRun.exit = none
#guard Api.Inspection.unpinnedDaemonsAlive pinnedRun = []
#guard Api.Inspection.daemonsQuiet pinnedRun
#guard (Api.Inspection.fibers pinnedRun).any fun entry =>
  match entry.2 with | .pinned _ _ => true | _ => false

/-! ## The hypotheses the laws take, on these machines -/

-- `exitedUnparked`: no exited fiber is parked. Every run keeps it.
#guard [childRun, looseRun, pinnedRun].all fun r => Api.exitedUnparked r.machine
-- `nextIdFresh`: the machine's next id is carried and tracked by nobody.
#guard [childRun, looseRun, pinnedRun].all fun r => Api.nextIdFresh r.machine

/-! ## `awaits` and `fiberStatuses` agree on the parked fibers -/

#guard Program.awaits childRun.machine = []
#guard Program.awaits looseRun.machine = [(⟨1⟩, 0, .external 0, .nat 2)]
#guard Program.awaits pinnedRun.machine =
  [(⟨0⟩, 1, .external 0, .nat 3), (⟨1⟩, 0, .external 0, .nat 2)]

-- `awaits_live` on these machines: every outstanding call names a fiber whose status is live.
#guard [childRun, looseRun, pinnedRun].all fun r =>
  (Program.awaits r.machine).all fun a =>
    (Api.Inspection.fibers r).any fun entry => entry.1 == a.1 && entry.2.live

/-! ## The property at the observation -/

-- `terminated_daemonsQuiet`: the two runs whose observation is terminated are quiet.
#guard Api.HostProtocol.observe childRun.machine = .terminated
#guard Api.HostProtocol.observe looseRun.machine = .awaitingAsync
#guard Api.HostProtocol.observe pinnedRun.machine = .awaitingAsync
#guard [childRun].all fun r =>
  Api.HostProtocol.observe r.machine != .terminated || Api.daemonsQuiet r.machine

/-! ## The ceilings -/

/-- info: 'Effect4.Api.supervision_child_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.supervision_child_flag
/-- info: 'Effect4.Api.supervision_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.supervision_static
/-- info: 'Effect4.Api.status_persists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.status_persists
/-- info: 'Effect4.Api.spawn_status_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.spawn_status_fresh
/-- info: 'Effect4.Api.spawn_status_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.spawn_status_other
/-- info: 'Effect4.Api.awaits_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.awaits_live
/-- info: 'Effect4.Api.daemonsQuiet_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.daemonsQuiet_iff
/-- info: 'Effect4.Api.terminated_daemonsQuiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Effect4.Api.terminated_daemonsQuiet

end Test.Api.SupervisionContract
