import Probe.Session
import Probe.Run

/-! Review probe: the session rows are the dual of the service, so a deployment's outputs are host
calls, and the journal's bound calls carry them. The per-run check (`journal_bound_call`) then
validates the replies a deployment gave, not only the calls it made. Each `#guard` is a finite
evaluation on the to-do's lifetime. -/

set_option autoImplicit false
namespace Review.Transcript
open Effect4 Effect4.Program Effect4.Run
open Probe.Session (todoRun todoSession)

/-- The requests of the journal's bound calls at the rows a predicate on the position selects. The
positions are the signature's: the application's rows first, then `Session.next`, then one reply
row a method (`probe-session.lean` §1). Spellings stay inside the `#guard`s. -/
def boundAt (s : Run) (keep : Nat → Bool) : List Store.Val :=
  s.journal.filterMap fun c => match c with
    | .bind call _ => match call.op with
      | .external i => if keep i then some call.request else none
      | _ => none
    | _ => none

/-- The to-do's positions: four repository rows, `Session.next`, four reply rows. -/
def isRepo (i : Nat) : Bool := i < 4
def isNext (i : Nat) : Bool := i == 4
def isReply (i : Nat) : Bool := 4 < i

-- finite evaluation: the seven replies the driver recorded are exactly the seven requests the
-- program sent at the reply rows, in order. The outputs of the lifetime are bound calls, so
-- `journal_bound_call` reads each of them as the Lean machine's own request at that point
#guard todoRun.map (fun (s, st) => boundAt s isReply == st.1.2.map (·.2)) = some true

-- finite evaluation: the 22 bound calls are 8 at `Session.next` (seven requests and the end), 7 at
-- the reply rows, and 7 at the repository: the whole interaction, inputs, outputs and the host's
-- calls, is in the journal
#guard todoRun.map (fun (s, _) =>
  ((boundAt s isNext).length, (boundAt s isReply).length, (boundAt s isRepo).length)) =
  some (8, 7, 7)

-- finite evaluation: the session rows are the service's dual. Each method `m : A → Exit B E` of
-- the service becomes a reply row `Session.reply_m : Exit B E → unit`, and the request row's
-- answer is the sum of the methods' arguments: one row the other way for each method
#guard (todoSession.map fun so =>
  let replies := (so.app.rows.zipIdx.filter fun (_, i) => isReply i).map (·.1)
  let methods := so.program.defsOf.filterMap fun d => match d.role with
    | .serviceMethod _ m _ => some (m, d.answer, d.error)
    | _ => none
  so.app.rows[4]?.map (·.spelling) == some "Session.next" && replies.length == methods.length &&
    (replies.zip methods).all fun (row, (m, answer, error)) =>
      row.spelling == "Session.reply_" ++ m && row.request == .exitOf answer error && row.answer == .unit) =
  some true

end Review.Transcript
