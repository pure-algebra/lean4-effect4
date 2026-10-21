import Review.Transcript

/-! Finite controls for the transcript's accepted-command reading.
Consumer: host-session-protocol journal evidence, R6 and R13.
Replay validates commands. It neither captures physical output nor restores host state. -/

set_option autoImplicit false
namespace Refinement.Transcript
open Effect4 Effect4.Program Effect4.Machine
open Effect4.Api.Runner (Command)
open Probe.Session (todoLive)
open Review.Transcript (boundAt isReply)

def alterReplies (j : List Command) : List Command := j.map fun
  | .bind call token => match call.op with
    | .external i => if isReply i then .bind { call with request := .unit } token
      else .bind call token
    | _ => .bind call token
  | command => command

def altered : Option Live := todoLive.bind fun l =>
  let r := LiveRecord.save l
  (LiveRecord.restore { r with journal := alterReplies r.journal }).toOption

def acceptedAt (s : Run) (keep : Nat → Bool) : List Val :=
  (Run.rows s).filterMap fun
    | (.bind call _, .bound) => match call.op with
      | .external i => if keep i then some call.request else none
      | _ => none
    | _ => none

#guard todoLive.map (fun l => decide
  (boundAt l.run isReply = acceptedAt l.run isReply)) = some true
#guard altered.isSome
#guard altered.map (fun l => l.run.phases.any fun ph =>
  decide (ph = .refused .staleCall)) = some true
#guard altered.map (fun l => ((boundAt l.run isReply).length,
  (acceptedAt l.run isReply).length)) = some (7, 0)

end Refinement.Transcript
