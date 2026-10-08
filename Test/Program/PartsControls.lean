import Effect4.Run.Tape
import Effect4.Modules.Queue.Defs
import Effect4.Api.Author
import Effect4.Laws.Api.HostSession

/-!
# The call instance inside a definition block (decisions row 333, claim `block-call-instance`)

Seat HOST's probe, part B (`docs/research/2026-10-08-host-authoring-boundary/BoundaryProbe.lean`),
as a battery. One client calls the template host row of decisions row 183, `List<A>` to
`Option<A>`, on `[1]`, and offers 3 to a queue. Filling 1 writes the Queue's `offer` inline.
Filling 2 invokes the installed definitions, so its program holds a block at the root, and its
host call stands at `[1, 1, 0]`. Before the repair the session's call table of filling 2 was
empty, and the session refused the reply `some 1` with `envelope`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Test.Program.PartsControls

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The Queue's definitions at numbers. -/
def numbers := Queue.Definitions.make "numbers" .nat

/-- The template row of decisions row 183. -/
def firstRow : RowDef := Row.host "L.first" (.list (.var 0)) (.option (.var 0))

/-- The client: a queue, the host call on `[1]`, one offer, and the host's answer. -/
def clientMain (offer : TermSrc → TermSrc → Src NativeOp) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let o ← Row.call firstRow (app "cons" [nat 1, nilT])
  let _ ← offer q (nat 3)
  return o

/-- Filling 1: `offer` inline, no block. -/
def inlineClient : Module NativeOp :=
  { rows := [firstRow], main := clientMain (Queue.offer .nat) }

/-- Filling 2: the installed definitions, a block at the root. -/
def definedClient : Module NativeOp :=
  { numbers.module (clientMain numbers.offer) with rows := [firstRow] }

def builtOf (m : Module NativeOp) : Option Api.Built := (Api.Author.build m).toOption

/-- The run opened and its root evaluated, at the default budget. -/
def startOf (m : Module NativeOp) : Option Run :=
  (builtOf m).map fun b => (Run.open b "parts" {}).play Rows.start

/-- The key of the first call the machine waits on. -/
def hostKey (s : Run) : Option Api.HostSession.Key :=
  s.outstanding.head?.map fun a => ⟨a.fiber, a.token⟩

/-- The verdict of the receipt of one answer at the waiting call: its last phase. -/
def receiptOf (m : Module NativeOp) (a : Api.HostSession.Answer) :
    Option Api.HostSession.Phase :=
  (startOf m).bind fun s => (hostKey s).bind fun k => (s.receive k a).phases.getLast?

/-- The waiting call's address and its instance's answer column, as the session reads them. -/
def instanceOf (m : Module NativeOp) : Option (Option (List Nat) × Option Ty) :=
  (startOf m).bind fun s => (hostKey s).map fun k =>
    let origin := originOf s.machine k.fiber k.token
    (origin, (origin.bind fun o => s.session.callInstance o).map (·.answer))

/-- The addresses of the call table, as the session makes it. -/
def tableOf (m : Module NativeOp) : Option (List (List Nat)) :=
  (builtOf m).map fun b => (Api.HostSession.callTable b.program b.table).map (·.1)

def some1 : Api.HostSession.Answer := .ofExit (.success (.some (.nat 1)))

-- finite evaluation: the host call's instance is `Option<number>` in both fillings, at `[1, 0]`
-- inline and at `[1, 1, 0]`, the main program's child, behind the block
#guard instanceOf inlineClient = some (some [1, 0], some (.option .nat))
#guard instanceOf definedClient = some (some [1, 1, 0], some (.option .nat))
-- finite evaluation: the reply that only the instance admits is admitted in both fillings
#guard receiptOf inlineClient some1 = some .preflight
#guard receiptOf definedClient some1 = some .preflight
-- finite evaluation: filling 2's table lists the bodies' calls under `[0]` and the main
-- program's under `[1]`, and no address of the block itself or of its bodies' spine
#guard (tableOf definedClient).map (fun as => (as.any (·.head? == some 0),
  as.any (·.head? == some 1), as.contains [], as.contains [0])) = some (true, true, false, false)

-- control: an address of the block itself, or past the main program, holds no part
#guard (builtOf definedClient).map (fun b =>
  ((b.program.expandRefs.partAt (SigApp.signature ⟨b.table, []⟩) [] []).isNone,
    (b.program.expandRefs.partAt (SigApp.signature ⟨b.table, []⟩) [] [2]).isNone,
    (b.program.expandRefs.partAt (SigApp.signature ⟨b.table, []⟩) [] [0]).isNone)) =
  some (true, true, true)

end Test.Program.PartsControls
