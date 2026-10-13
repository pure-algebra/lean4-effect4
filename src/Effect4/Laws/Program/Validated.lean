import Effect4.Laws.Api.SessionMeaning
import Effect4.Program.RowProtocol

/-!
# Program.Validated — a run validated against declared protocols and a reference model

The grade "validated for one run" of the claims packet
(`docs/research/2026-10-07-packet-application-claims.md`, §3.4 to §3.6; decisions rows 307 (9)
and 336 (9)). A claim under a promise of the rows is a conditional theorem of the call tree. A
decision on one run's own tape discharges its premise for that run.

* **A declared protocol as a protocol of the row signature** (`declaredProtocol`): at a call, a
  successful answer keeps the promise of its row's declared protocol
  (`src/Effect4/Program/RowProtocol.lean`). The reply host behind it (`keptTapeHost`) meets it.
* **A run conforms** (`conforms`): each call the host held meets its row's demand, and the guarded
  reply host gave the run's applied answers, a check of `hostAnsweredCheck`
  (`src/Effect4/Laws/Api/SessionMeaning.lean`). It is decided on the run, and it changes no step of
  the session.
* **A conforming run has the tree's postcondition** (`conforms_sat`): a postcondition that the
  call tree meets under the declared protocols (`Effects.Program.Sat`) holds of the run's exit.
  The proof is H9 (`denoteRows_eq_session_host`) at the guarded reply host, then
  `Effects.Program.Sat.sound`.
* **A run agrees with a reference model** (`agrees`): the model, read as a host (`reactorHost`),
  gave the run's applied answers, a check of `hostAnsweredCheck`. Such a run is a run of its call
  tree under the model (`agrees_hostRun`), by H9.

Placement: concept `host-session-protocol`; R6's open part "the host as a relation between the
machine's calls and its answers". Reach: H9's fragment and premises: `StraightRows`, one fiber, a
recorded run that is funded, at rest, driven by a host, and whose root exited. It does not
establish that a host conforms on another run, that a run finishes, or anything of a check at the
reply receipt, which would change reply admission (the packet's slice MONITOR, a ruling first).
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- **The declared protocols of a row table, as a protocol of its hosts**: at a call, a successful
answer keeps its row's declared promise at the call's request. A failure is not read. -/
def declaredProtocol (table : RowTable) (protocols : RowProtocols) :
    Effects.Protocol (RowSig table) :=
  fun op ex => protocols.keepsAt table op.1.val op.2 ex = true

/-- The stores and the rows under the declared protocols: the stores' answers are not read. -/
def rowsProtocol (table : RowTable) (protocols : RowProtocols) : Effects.Protocol (RowsSig table) :=
  Effects.Protocol.sum Effects.Protocol.top (declaredProtocol table protocols)

/-- The reply host behind the declared protocols: it answers the tape's next exit where the
exit keeps its row's promise, and nothing otherwise. -/
def keptTapeHost (table : RowTable) (protocols : RowProtocols) :
    Effects.Comodel (RowSig table) ReplyTape :=
  (tapeHost table).guard fun op ex => protocols.keepsAt table op.1.val op.2 ex

/-- The guarded reply host meets the declared protocols. A step of `conforms_sat`. -/
theorem keptTapeHost_meets (table : RowTable) (protocols : RowProtocols) :
    (keptTapeHost table protocols).Meets (declaredProtocol table protocols) :=
  Effects.Comodel.guard_meets _ (tapeHost table)

/-- The stores routed beside a host that meets the declared protocols meet them on the sum. A
step of `conforms_sat`. -/
theorem rowsHost_meets {σ : Type} {table : RowTable} {protocols : RowProtocols}
    {host : Effects.Comodel (RowSig table) σ} (h : host.Meets (declaredProtocol table protocols)) :
    (rowsHost host).Meets (rowsProtocol table protocols) :=
  Effects.Comodel.Meets.route (fun _ _ _ _ _ => trivial) h

/-- **A run conforms to declared protocols**: each call the host held meets its row's demand, and
the reply host behind the protocols gave the run's applied answers, each keeping its row's
promise at the machine's request. Decided on the run; it changes no step of the session. -/
def conforms (protocols : RowProtocols) (s : Run) : Bool :=
  (held s).all (fun call => protocols.admits call.row call.request) &&
    (hostAnsweredCheck s.built.table (keptTapeHost s.built.table protocols) s.built.program
      s.budget.fuel (tapeOf s) (Api.load s.built.program s.budget.compileFuel)
      (appliedExits s)).isSome

/-- **A conforming run has every postcondition that its call tree meets under the declared
protocols.** For a recorded run of a `StraightRows` program that is funded, at rest, driven by a
host and conforms, a postcondition that the call tree meets under the stores and the declared
protocols (`Effects.Program.Sat`) holds of the root's exit.

Placement: concept `host-session-protocol`, role adequacy; question: the proposed registry claim
`run-conforms-postcondition`; consumer: `Todo.complete_answers_requested`
(`Test/Dogfood/Scenario/Todo/Claims.lean`). Reach: H9's (`denoteRows_eq_session_host`), the run's
own tape. Does not establish: that a host conforms; the demand on the requests, which the proof
does not read; progress. Unlocks: a claim under a promise of the rows, read on a real run by a
decided premise (R6). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem conforms_sat (protocols : RowProtocols) (s : Run) (hreach : Run.Reached s)
    (hfund : funded s = true) (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hfrag : StraightRows s.built.table s.built.program = true)
    (hconf : conforms protocols s = true) {Q : ExitV → Prop}
    (hsat : Effects.Program.Sat (rowsProtocol s.built.table protocols) Q
      (denoteRows s.built.table s.built.program []))
    (ex : ExitV) (hex : s.exit = some ex) : Q ex := by
  obtain ⟨-, hcheck⟩ := Bool.and_eq_true_iff.mp hconf
  obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp hcheck
  have hA := hostAnsweredCheck_sound s.built.table (keptTapeHost s.built.table protocols)
    s.built.program s.budget.fuel (tapeOf s) _ (appliedExits s) st' hst'
  have h9 := denoteRows_eq_session_host s hreach hfund hrest hhost hfrag
    (keptTapeHost s.built.table protocols) (appliedExits s) st' hA ex hex
  exact Effects.Program.Sat.sound (rowsHost (keptTapeHost s.built.table protocols))
    (rowsHost_meets (keptTapeHost_meets s.built.table protocols)) _ hsat
    (Stores.empty, appliedExits s) ex (s.machine.state, st') h9

/-! ## A run validated against a reference model -/

/-- **A run agrees with a model of its rows** (the claims packet's §3.6): the model, read as a host
(`reactorHost`), gave the run's applied answers from `start`. The answer is the model's last
state, or `none` at the first answer that the model does not give. It is `hostAnsweredCheck` on
the run's own tape, so the host need be no Lean function. -/
def agrees {σ : Type} (model : Reactor σ) (s : Run) (start : σ) : Option σ :=
  hostAnsweredCheck s.built.table (reactorHost s.built.table model) s.built.program s.budget.fuel
    (tapeOf s) (Api.load s.built.program s.budget.compileFuel) start

/-- **A run that agrees with a model is a run of its call tree under the model.** For a recorded
run of a `StraightRows` program that is funded, at rest, driven by a host, and whose root exited,
where the model gave the run's answers from `start` to `finish`, the model's run of the call tree
is the root's exit with the run's stores, and the model ends at `finish`.

Placement: concept `translation-simulation`, role simulation; question: the proposed registry
claim `run-agrees-model`; consumers: `Todo.list_after_add` and `Todo.complete_idempotent`
(`Test/Dogfood/Scenario/Todo/Claims.lean`). Reach: H9's (`denoteRows_eq_session_host`), with its
premise `HostAnswered` decided by `agrees` (`hostAnsweredCheck_sound`). Does not establish: that
a host agrees with the model on another run; progress. Unlocks: a claim under the laws of the
rows, read on a real run by a decided premise (R6). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem agrees_hostRun {σ : Type} (model : Reactor σ) (s : Run) (hreach : Run.Reached s)
    (hfund : funded s = true) (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hfrag : StraightRows s.built.table s.built.program = true) (start finish : σ)
    (hagree : agrees model s start = some finish) (ex : ExitV) (hex : s.exit = some ex) :
    hostRun (reactorHost s.built.table model) s.built.program [] Stores.empty start =
      some (ex, (s.machine.state, finish)) :=
  denoteRows_eq_session_host s hreach hfund hrest hhost hfrag _ start finish
    (hostAnsweredCheck_sound _ _ _ _ _ _ _ _ hagree) ex hex

end Effect4.Run
