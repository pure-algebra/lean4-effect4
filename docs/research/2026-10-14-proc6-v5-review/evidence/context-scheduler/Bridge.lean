import Effect4.Laws.Program.Agreement.Machine
import Effect4.Run
import Effect4.Api.Author
open Effect4 Effect4.Machine Effect4.Program
-- Review control for rows-block-host/R6: finite refutation of proposed membership bridge.
def poison : Ctx := Ctx.withServices ((Env.Context.empty : Env.Ctx).addV Env.maxOpsKey (.nat 1))
def frame : Val := .ctor 0 [.list [.str "hidden"], .list [Val.context poison]]
def payload : Payload := ⟨frame, by decide⟩
def defectReason : Reason Err Defect FiberId Ann := .die (.error (.payload payload)) .empty
def defectCause : CauseV := ⟨[defectReason]⟩
-- Bounded whole-tree inspection; these witness trees have depth below 100.
def unsafeNode (v : Val) : Bool := match Val.context? v with
 | some c => (c.services.getV Env.maxOpsKey).isSome || (c.services.getV Env.preventYieldKey).isSome
 | none => false
def unsafeWithin : Nat → Val → Bool
 | 0, v => unsafeNode v
 | n+1, v => unsafeNode v || match v with
   | .ctor _ xs | .list xs => xs.any (unsafeWithin n)
   | .pair a b => unsafeWithin n a || unsafeWithin n b
   | .some a => unsafeWithin n a
   | _ => false
#eval (Val.hasTy (Val.exitErr defectCause) (.causeOf .never), unsafeWithin 100 (Val.exitErr defectCause))
#eval (Val.hasTy (Val.exitErr defectCause) (.exitOf .unit .never), unsafeWithin 100 (Val.exitErr defectCause))
#eval errAdmits .never defectReason
#eval reservedDie defectReason
#eval frame.handles.isEmpty
-- Record controls: extra fields and malformed column lengths do not satisfy closed record types.
#eval Val.hasTy frame (.record [])
#eval Val.hasTy frame (.record [("hidden", false, .nat)])
#eval Val.hasTy (.ctor 0 [.list [.str "x", .str "hidden"], .list [.nat 1, Val.context poison]])
  (.record [("x", false, .nat)])
#eval Val.hasTy (.ctor 0 [.list [.str "x"], .list [.nat 1, Val.context poison]])
  (.record [("x", false, .nat)])

-- Closed legal row and actual checked-session application of the same nested payload.
def row : Row :=
 {name := "v5ClosedExit", spelling := "v5ClosedExit", kind := .async, registration := .external,
  request := .unit, answer := .exitOf .unit .never, cite := "rows-block-host/R6 review control"}
def source : NativeEff := .perform (.external 0) (.lit .unit)
#eval admitSig ⟨[row], []⟩
#eval (admitProgram source ⟨[row], []⟩).isOk
#eval (externalValue row.answer [] (Val.exitErr defectCause)).isSome
def appliedRun : Option Run := do
 let built ← (Api.Author.Internal.finishBuild source [row] []).toOption
 let r := (Run.open built "v5" {fuel := 500, compileFuel := 100}).control Api.evaluate
 let a ← r.outstanding.head?
 pure (r.answer ⟨a.fiber, a.token⟩ (.ofExit (.success (Val.exitErr defectCause))))
#eval appliedRun.map fun r => (r.outstanding.length,
 r.machine.completedExits.any (fun pair => match pair.2 with | .success v => unsafeWithin 100 v | _ => false),
 r.machine.fibers.map (fun f => f.maxOpsBeforeYield))
-- A nominal application's arguments are unread by hasTy (source inspection control).
#eval Val.hasTy (.handle 7 0) (.app "Foreign" [.unknown]) ["Foreign"]
