import Effect4.Api.HostSession

/-!
# Api.Player: a session as something that plays a journal

The session API of the player plan (`docs/research/2026-09-17-player-schema-codegen-plan.md`
§4, §4b). `HostSession` owns the checked transitions; this module gives them the one shape a
holder needs on every host:

* **One alphabet.** `Command` is a row of a job's journal: bind a recorded call to a guard,
  receive a reply, apply a received reply, or a control decision. Everything that changes a
  session is one of these four.
* **One transition.** `step : Player → Command → Player × Phase` is total. A refusal is a
  verdict: the phase says why and the player is unchanged (`step_refused`), so a journal may
  hold refused rows and replay still means the same thing.
* **No index.** `Player` packs the program, the table and the session indexed by them, so a
  holder keeps one value of one type. The job's step fuel lives here, never in the instance
  that plays it.
* **Replay.** `replay` folds `step` over a journal and keeps every phase. It distributes over
  concatenation (`replay_append`): journals act on players, and a player reached by a prefix
  can be handed the rest.

This module owns no byte codec, no journal and no reactor. The codec is the `Canonical`
instances of `Command`, `Phase` and the observation, which the generator derives.
-/

set_option autoImplicit false

namespace Effect4.Api.Player

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Session Header Call Reply Key Result)

/-- One row of a job's journal. -/
inductive Command
  /-- A recorded call start, associated with the outstanding guard `token`. -/
  | bind (call : Call) (token : Nat)
  /-- A reply received for a bound call. Receipt stores; it does not run the machine. -/
  | submit (reply : Reply)
  /-- Apply the received reply of one explicitly selected key. -/
  | apply (key : Key)
  /-- A control decision of the machine's own alphabet (never a direct answer). -/
  | control (decision : NativeDecision)
deriving DecidableEq

/-- A session with what indexes it, and the job's step fuel. -/
structure Player where
  program : Api.Program
  table : RowTable
  /-- The fuel of every `apply` and `control` of this job. It is the job's, so two instances
  playing one journal stop at the same places. -/
  fuel : Nat
  session : Session program table

/-- A player from a program, its row table and an explicit header, or the refusal. -/
def load (program : Api.Program) (table : RowTable) (expectedProfile : String)
    (header : Header) (compileFuel stepFuel : Nat) : Except HostSession.Refusal Player :=
  match HostSession.start program table expectedProfile header compileFuel with
  | .error why => .error why
  | .ok session => .ok { program, table, fuel := stepFuel, session }

/-- The checked transition a command names. -/
def result (p : Player) : Command → Result p.program p.table
  | .bind call token => HostSession.bindCall p.session call token
  | .submit reply => HostSession.submit p.session reply
  | .apply key => HostSession.applyReply p.session key p.fuel
  | .control decision => HostSession.advance p.session p.fuel decision

/-- One row played: the next player and the phase the row ended in. -/
def step (p : Player) (c : Command) : Player × HostSession.Phase :=
  let r := result p c
  ({ p with session := r.session }, r.phase)

/-- A journal played from a player: the player it reaches and the phase of every row. -/
def replay (p : Player) : List Command → Player × List HostSession.Phase
  | [] => (p, [])
  | c :: rest =>
    let (p₁, phase) := step p c
    let (p₂, phases) := replay p₁ rest
    (p₂, phase :: phases)

/-- The run as a frontier reading: outcome, machine and reasons. Reads only. -/
def inspect (p : Player) : Api.Run := HostSession.inspect p.session

/-- The protocol state a holder schedules by: idle, awaiting a host, parked or terminated. -/
def observe (p : Player) : HostProtocol.State := HostProtocol.observe p.session.machine

/-- The calls the machine is waiting on, which a reactor answers. -/
def outstanding (p : Player) : List Await := HostSession.outstanding p.session

end Effect4.Api.Player
