import Effect4.Laws.Api.Object
import Effect4.Laws.Api.HostDrive
import Test.Dogfood.Scenario.Todo.CachedProgram
import Test.Dogfood.Scenario.Todo.Typed

/-! Probe: emission and assembly as functions. `emit` reads an object and nothing else, so its
artifacts are the same for every host. `assemble` pairs artifacts with a host and computes
nothing. A deployment's run is the Lean driver's run of the admitted object, so every law of
`Run.runWith` reads it. The definitions are this probe's, proposed for the landing; each theorem
is proved, and each `#guard` is a finite evaluation on the to-do. -/

set_option autoImplicit false
namespace Probe.Deploy
open Effect4 Effect4.Program Effect4.Machine Effect4.Store
open Test.Dogfood.Scenario.Todo (repository Repo)

/-- **What `emit` writes for every target**: the object's node bytes and the host interface, its
row table. A target adds its own print (a TypeScript module, an OCaml signature); no field holds
a host. -/
structure Artifacts where
  object : Bytes
  interface : RowTable

/-- **Emission**: a function of the object alone. -/
def emit (o : Object) : Artifacts := ⟨o.bytes, o.app.rows⟩

/-- **A host implementation**: its state, the state a deployment starts from, and the host as a
function of the row, the request and the state. `Compiler.Hosted` less its display. -/
structure Host where
  σ : Type
  initial : σ
  reactor : Run.Reactor σ

/-- **A deployable**: artifacts and a host, side by side. -/
structure Deployable where
  artifacts : Artifacts
  host : Host

/-- **Assembly**: it pairs; it reads and computes nothing. -/
def assemble (a : Artifacts) (h : Host) : Deployable := ⟨a, h⟩

/-- **A deployment's run**: load the object (read, then program admission), then the driver
(`Run.runWith`) under the host. -/
def Deployable.run (d : Deployable) (budget : Api.Budget := {}) (rounds : Nat := 512) :
    Except Object.LoadRefusal (Run × d.host.σ) :=
  (Object.load d.artifacts.object).map fun b =>
    Run.runWith b d.host.reactor d.host.initial "deployment" budget rounds

/-- **The emitted artifacts do not depend on the host**: two assemblies of one emission hold the
same artifacts. By definition. Placement: concept `exact-codecs`; the proposed claim
`emit-host-free` (role compatibility); consumer: the assembled package's manifest, whose
artifact digests a host edit leaves unchanged. -/
theorem emit_host_free (o : Object) (h₁ h₂ : Host) :
    (assemble (emit o) h₁).artifacts = (assemble (emit o) h₂).artifacts := rfl

/-- Step of `run_assemble_emit`: loading a storable object's bytes is its program admission. -/
theorem load_bytes_of_wf (o : Object) (hwf : (toVal o).WF) :
    Object.load o.bytes = o.open.mapError .admission := by
  unfold Object.load
  rw [Object.read_bytes o hwf]

/-- **A deployment runs the Lean driver on the admitted object.** For a storable object, the run of
any assembly of its emission is `Run.runWith` of the object's admission, under the assembled host.
So `runWith_denotes`, `runWith_denotesB`, `drive_envelope`, `runWith_guarded_denotes` and
`journal_replays` read every deployment's run, with their premises. Placement: concept
`host-session-protocol`; the proposed claim `deployment-runs-driver` (role compatibility), at R6
and R13; consumer: the native deployment's reference (README §6). Reach: every object whose value
tree is `Val.WF`, every host, every budget. It does not establish that a native engine computes
this run (the lowering stage, decisions row 391), host progress, or that the drive's rounds
suffice. -/
theorem run_assemble_emit (o : Object) (hwf : (toVal o).WF) (h : Host) (budget : Api.Budget)
    (rounds : Nat) :
    (assemble (emit o) h).run budget rounds =
      (o.open.mapError .admission).map fun b =>
        Run.runWith b h.reactor h.initial "deployment" budget rounds := by
  show (Object.load o.bytes).map _ = _
  rw [load_bytes_of_wf o hwf]
  rfl

/-- **The host interface is the comodel's signature**: a host assembled against an emission is a
comodel of the row signature of the emitted interface (`reactorHost`), the one H9 quantifies over.
By definition. -/
def Host.comodel (a : Artifacts) (h : Host) : Effects.Comodel (Denote.RowSig a.interface) h.σ :=
  Run.reactorHost a.interface h.reactor

/-! ## The to-do -/

def todoObject : Option Object :=
  (Test.Dogfood.Scenario.Todo.Cached.built? Test.Dogfood.Scenario.Todo.application).map Object.ofBuilt

/-- The reference repository as a host. -/
def repoHost : Host := ⟨Repo, (1, []), repository⟩

/-- The typed model as a host: a typed record is one host by `Host.reactor`. -/
def typedHost : Host :=
  ⟨Repo, (1, []), Test.Dogfood.Scenario.Todo.Typed.Host.reactor Test.Dogfood.Scenario.Todo.Typed.model⟩

-- finite evaluation: the object is storable, so `run_assemble_emit` applies to it
#guard todoObject.map (fun o => decide (toVal o).WF) = some true
-- finite evaluation: the emission's interface is the four rows and its object is the 7,894 bytes of
-- the object's node
#guard todoObject.map (fun o => ((emit o).interface.length, (emit o).object.length)) = some (4, 7894)
-- finite evaluation: the deployment of the service block itself finishes at once: its main program
-- is the unit, and no request reaches a method (the session program of `probe-session.lean` is the
-- object a deployment ships)
#guard todoObject.map (fun o => match (assemble (emit o) repoHost).run with
  | .ok (s, _) => (s.exit.isSome, s.journal.length)
  | .error _ => (false, 0)) = some (true, 2)
-- control: bytes that are no object's node refuse at the node reader, before admission
#guard todoObject.map (fun o => match (assemble { emit o with object := (emit o).object.drop 1 } repoHost).run with
  | .error (.node _) => true
  | _ => false) = some true

end Probe.Deploy
