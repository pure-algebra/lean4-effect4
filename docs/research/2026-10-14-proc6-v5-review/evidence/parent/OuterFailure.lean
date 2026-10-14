import Effect4.Run
import Effect4.Api.Author
import Effect4.Laws.Program.DenoteRowsB

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/- Review control for rows-block-host, translation-simulation, R6.
   The block contains one ordinary external call under exit.
   This checks the proposed all-descendants reply invariant, not scheduler progress. -/

def poisoned : Ctx :=
  Ctx.withServices ((Env.Context.empty : Env.Ctx).addV Env.maxOpsKey (.nat 1))
def payloadFrame : Val := .ctor 0 [.list [.str "hidden"], .list [Val.context poisoned]]
def payload : Payload := ⟨payloadFrame, by decide⟩
def hostCause : CauseV := Cause.die (.error (.payload payload))
def ordinaryRow : Row :=
  { name := "ordinaryUnit", spelling := "ordinaryUnit", kind := .async,
    registration := .external, request := .unit, answer := .unit,
    cite := "rows-block-host R6 version-5 review control" }
def mainBody : NativeEff := .exit (.perform (.external 0) (.lit .unit))
def root : NativeEff := .defs [] .nil mainBody .nil

#eval admitSig ⟨[ordinaryRow], []⟩
#eval (admitProgram root ⟨[ordinaryRow], []⟩).isOk
#eval LoopedDataRows [ordinaryRow] mainBody
#eval ordinaryRow.error == .never

def answered : Option Run := do
  let built ← (Api.Author.Internal.finishBuild root [ordinaryRow] []).toOption
  let r := (Run.open built "v5-outer-failure" {fuel := 500, compileFuel := 100}).control Api.evaluate
  let a ← r.outstanding.head?
  pure (r.answer ⟨a.fiber, a.token⟩ (.ofExit (.failure hostCause)))

#eval answered.map fun r =>
  (r.outstanding.length, r.exit == some (.success (Val.exitErr hostCause)),
    r.machine.fibers.map (fun f => f.maxOpsBeforeYield))
