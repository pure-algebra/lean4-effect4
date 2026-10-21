import Probe.Deploy
import Probe.Session
import Effect4.Laws.Api.HostDrive

/-! Review probe: assembly applies reply admission. The deployment's host is the assembled reactor
behind the loaded object's named types (`Reactor.guardRows`), so every deployment's run is inside
the envelope by construction, and the driver laws read it with no host premise. The artifacts are
the object's bytes alone; the run's name is given at assembly. Each theorem is proved; each
`#guard` is a finite evaluation on the to-do's lifetime. -/

set_option autoImplicit false
namespace Review.Guard
open Effect4 Effect4.Program Effect4.Program.Denote Effect4.Machine Effect4.Run
open Probe.Deploy (Host)
open Probe.Session (todoSessionBuilt todoSession script both requests replySpellings Script)
open Test.Dogfood.Scenario.Todo (repository Repo)

/-- What `emit` writes for every target: the object's node bytes. The interface is read off the
loaded object; no second copy travels. -/
abbrev Artifacts := Store.Bytes

def emit (o : Object) : Artifacts := o.bytes

/-- A deployable: the bytes, the run's name, and a host. The name is the deployment's identity;
every call claim of its journal carries it. -/
structure Deployable where
  object : Artifacts
  name : String
  host : Host

/-- Assembly pairs; the guard is applied where the object is known, at the run. -/
def assemble (a : Artifacts) (name : String) (h : Host) : Deployable := ⟨a, name, h⟩

/-- **The deployment's host**: the assembled reactor behind the loaded object's named types. Reply
admission is applied to every answer by construction. -/
abbrev Deployable.reactor (d : Deployable) (b : Api.Built) : Reactor d.host.σ :=
  d.host.reactor.guardRows b.app.types

/-- A deployment's run: load, then drive under the guarded host. -/
def Deployable.run (d : Deployable) (budget : Api.Budget := {}) (rounds : Nat := 512) :
    Except Object.LoadRefusal (Run × d.host.σ) :=
  (Object.load d.object).map fun b => Run.runWith b (d.reactor b) d.host.initial d.name budget rounds

/-- Every deployment's host is inside the envelope of the object it runs. -/
theorem reactor_envelops (d : Deployable) (b : Api.Built) : (d.reactor b).Envelops b.app :=
  guardRows_envelops _ _

/-- Every deployment's host answers with exits. -/
theorem reactor_exitsOnly (d : Deployable) (b : Api.Built) : (d.reactor b).ExitsOnly :=
  guardRows_exitsOnly _ _

/-- A loaded deployment's run is the driver's run under the guarded host. -/
theorem run_eq (d : Deployable) (b : Api.Built) (hload : Object.load d.object = .ok b)
    (budget : Api.Budget) (rounds : Nat) :
    d.run budget rounds = .ok (Run.runWith b (d.reactor b) d.host.initial d.name budget rounds) := by
  unfold Deployable.run
  rw [hload]
  rfl

/-- **Every deployment denotes, with no premise on its host**: the fragment, funding, rest and the
exit are the only premises left of `runWith_guarded_denotes`. The envelope is the assembly's. -/
theorem run_denotes (d : Deployable) (b : Api.Built)
    (budget : Api.Budget) (rounds : Nat) (hfrag : StraightRows b.table b.program = true)
    (hfund : funded (Run.runWith b (d.reactor b) d.host.initial d.name budget rounds).1 = true)
    (hrest : atRest (Run.runWith b (d.reactor b) d.host.initial d.name budget rounds).1 = true)
    (ex : ExitV) (hex : (Run.runWith b (d.reactor b) d.host.initial d.name budget rounds).1.exit = some ex) :
    hostRun (reactorHost b.table (d.reactor b)) b.program [] Stores.empty d.host.initial =
      some (ex, ((Run.runWith b (d.reactor b) d.host.initial d.name budget rounds).1.machine.state,
        (Run.runWith b (d.reactor b) d.host.initial d.name budget rounds).2)) :=
  runWith_guarded_denotes b d.host.reactor d.host.initial d.name budget rounds hfrag hfund hrest ex hex

/-! ## The to-do's lifetime under the guard -/

/-- The driver beside the reference repository, as one host. -/
def lifetimeHost : Host :=
  ⟨Script × Repo, ((requests, []), (1, [])), both (script replySpellings) repository⟩

/-- The deployment of the to-do's session object under that host. -/
def todoDeployable : Option Deployable :=
  todoSession.map fun so => assemble (emit so) "todo-1" lifetimeHost

def guarded : Option (Run × (Script × Repo)) :=
  todoSession.bind fun so => ((assemble (emit so) "todo-1" lifetimeHost).run).toOption
def unguarded : Option (Run × (Script × Repo)) :=
  todoSessionBuilt.map fun b =>
    Run.runWith b lifetimeHost.reactor lifetimeHost.initial "todo-1" {} 512

-- finite evaluation: the guarded lifetime serves the seven requests and ends, as the unguarded one
#guard guarded.map (fun (s, st) => (s.exit.isSome, st.1.1.length, st.1.2.length, st.2.1)) =
  some (true, 0, 7, 3)
-- finite evaluation: on the whole lifetime the guard changes nothing: the same observation, the
-- same journal, the same host state. So the reference host is inside the envelope on every
-- answer it gave, not only on sampled requests
#guard (guarded.bind fun (g, gs) => unguarded.map fun (u, us) =>
  decide (g.observe = u.observe) && decide (g.journal = u.journal) && decide (gs = us)) = some true
-- finite evaluation: the run's name is the one assembly gave, and every call claim carries it
#guard guarded.map (fun (s, _) => s.id == "todo-1" && s.journal.all fun c => match c with
  | .bind call _ => call.session == "todo-1"
  | _ => true) = some true
/-- A host that answers `Session.next` with a natural, outside the row's answer column. -/
def bad : Reactor Unit := fun row _ st =>
  if row.spelling == "Session.next" then some (.ofExit (.success (.nat 7)), st) else none

/-- Its deployment: the guard stops the answer before the session sees it. -/
def badRun : Option Run :=
  todoSession.bind fun so => ((assemble (emit so) "bad" ⟨Unit, (), bad⟩).run).toOption.map (·.1)

-- control: the guarded run waits at `Session.next` with no exit and no refused verdict: the bad
-- answer is filtered before the session; the unguarded driver carries it to reply admission, which
-- refuses it as `.refused .envelope` (the control of `probe-session.lean` §4)
#guard badRun.map (fun s => s.exit.isNone && s.phases.all fun ph => decide (ph ≠ .refused .envelope)) =
  some true
#guard badRun.map (fun s => (s.journal.length, s.phases.length)) = some (1, 1)

end Review.Guard
