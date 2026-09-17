/-! Runner boundary acceptance: every row of a journal and every verdict written as content,
read back exactly, refused with a byte added or removed, and fitting its generated shape. -/
namespace RunnerAcceptance
open Effect4 Effect4.Machine Effect4.Program Effect4.Api
open Effect4.Api.HostSession (Header Call Reply)
open Effect4.Api.Runner (Command)

def header : Header := ⟨1, "job", "serial-root-scalar-v1", []⟩
def call : Call := ⟨1, "job", [], 0, ⟨0⟩, .external 0, .list [.nat 2, .str "k"]⟩
def annotated : ReasonAnnotations Unit := ⟨[("span", ())], by decide⟩
def failed : Cause Err Defect FiberId Unit :=
  ⟨[.fail (.tagged "NotFound" "no row") annotated, .die (.error (.text "x")) ⟨[], by decide⟩,
    .interrupt (some ⟨3⟩) ⟨[], by decide⟩, .interrupt none annotated]⟩
def replies : List Reply :=
  [⟨1, "job", 0, ⟨⟨0⟩, 0⟩, .ofExit (.success (.nat 3))⟩,
   ⟨1, "job", 1, ⟨⟨0⟩, 1⟩, .ofExit (.failure failed)⟩,
   ⟨1, "job", 2, ⟨⟨2⟩, 5⟩, .ofRefGet ⟨4⟩⟩]

def decisions : List NativeDecision :=
  [.fire ⟨1⟩, .flush, .evaluate ⟨0⟩, .yieldVerdict ⟨2⟩ true,
   .answerAsync ⟨0⟩ 7 (.ofExit (.success (.pair (.nat 1) .none))),
   .interruptFrom (some ⟨1⟩) annotated ⟨2⟩, .interruptFrom none ⟨[], by decide⟩ ⟨0⟩,
   .installMiddleware, .advance 250]

def commands : List Command :=
  [.bind call 0, .apply ⟨⟨0⟩, 0⟩] ++ replies.map .submit ++ decisions.map .control

def refusals : List HostSession.Refusal :=
  [.version, .session, .profile, .table, .program .illTyped,
   .program (.duplicateKey ("Db", ["get"])), .program (.table (.notAsync 2)),
   .program (.uninhabited ["program", "answer"]), .duplicateCall, .protocol,
   .selectionRequired, .pendingReply, .callOrder, .noCall, .staleCall, .envelope,
   .directAnswer, .pendingControl, .stuck]

def phases : List HostSession.Phase :=
  [.bound, .preflight, .applied, .progressed, .frontier] ++ refusals.map .refused

#guard commands.all fun x => Canonical.decode (α := Command) (Canonical.encode x) = some x
#guard commands.all fun x => Canonical.decode (α := Command) (Canonical.encode x ++ [0]) = none
#guard commands.all fun x => Canonical.decode (α := Command) (Canonical.encode x).dropLast = none
#guard commands.all fun x => (Canonical.shape Command).accepts (Canonical.toVal x)
#guard phases.all fun x => Canonical.decode (α := HostSession.Phase) (Canonical.encode x) = some x
#guard phases.all fun x => Canonical.decode (α := HostSession.Phase) (Canonical.encode x ++ [0]) = none
#guard phases.all fun x => (Canonical.shape HostSession.Phase).accepts (Canonical.toVal x)
#guard Canonical.decode (α := Header) (Canonical.encode header) = some header
#guard (Canonical.shape Header).accepts (Canonical.toVal header)
-- A row and a verdict are different content: neither reads as the other.
#guard commands.all fun x => Canonical.decode (α := Header) (Canonical.encode x) = none
-- Rows are distinct as bytes exactly when they are distinct as commands.
#guard (commands.map Canonical.encode).eraseDups.length = commands.length
-- A duplicate annotation key is refused on reading, never repaired.
#guard Canonical.ofVal (α := ReasonAnnotations Unit)
  (.ctor 0 [.list [.pair (.str "a") .unit, .pair (.str "a") .unit]]) = none
#guard [HostProtocol.State.idle, .awaitingAsync, .parked, .terminated].all fun x =>
  Canonical.decode (α := HostProtocol.State) (Canonical.encode x) = some x
#guard [Api.Outcome.finished, .frontier, .stuck (.unknownFiber ⟨9⟩)].all fun x =>
  Canonical.decode (α := Api.Outcome) (Canonical.encode x) = some x
#guard Canonical.decode (α := Command) [] = none

end RunnerAcceptance
