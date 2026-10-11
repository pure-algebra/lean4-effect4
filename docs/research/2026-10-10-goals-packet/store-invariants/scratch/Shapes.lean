import Test.Dogfood.Scenario.Atomic

set_option autoImplicit false
set_option maxRecDepth 100000
open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario.Atomic

def nameTag : EffName → String
  | .cont p => s!"cont@{p.path.length}"
  | .fin p => s!"fin@{p.path.length}"
  | .caught p => s!"caught@{p.path.length}"
  | .onValue p => s!"onValue@{p.path.length}"
  | .onCause p => s!"onCause@{p.path.length}"
  | .restore _ => "restore"
  | .merge _ => "merge"
  | .store _ => "store"
  | .constant _ => "constant"
  | _ => "name"

def thunkTag : EffThunk → String
  | .op _ => "op"
  | .pure p => s!"pure@{p.path.length}"
  | .body p => s!"body@{p.path.length}"
  | .act p => s!"act@{p.path.length}"
  | .park _ => "park"
  | .store _ => "storeThunk"
  | _ => "thunk"

def primTag : NCode → String
  | .success _ => "success"
  | .failure _ => "failure"
  | .sync t => s!"sync({thunkTag t})"
  | .suspend t => s!"suspend({thunkTag t})"
  | .withFiber t => s!"withFiber({thunkTag t})"
  | .onSuccess b n => s!"onSuccess({primTag b},{nameTag n})"
  | .onSuccessConst b n => s!"onSuccessConst({primTag b},{primTag n})"
  | .onFailure b n => s!"onFailure({primTag b},{nameTag n})"
  | .onExit b n _ => s!"onExit({primTag b},{nameTag n})"
  | .yieldNowWith _ => "yield"
  | .async _ _ _ => "async"
  | .asyncFinalizer _ => "asyncFin"
  | .setInterruptible f => s!"setInt({f})"
  | _ => "other"

def frameTag (f : NCode) : String :=
  match f with
  | .onSuccess _ n => s!"[onSuccess {nameTag n}]"
  | .onExit _ n _ => s!"[onExit {nameTag n}]"
  | .onFailure _ n => s!"[onFailure {nameTag n}]"
  | .setInterruptible fl => s!"[setInt {fl}]"
  | other => s!"[{primTag other}]"

def shapeOf : Option (RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) → String
  | none => "absent"
  | some f =>
    s!"{primTag f.frame.current} | {f.frame.stack.map frameTag} | run={f.running} park={decide (f.parked ≠ .notParked)} exit={f.exit.isSome} int={f.frame.interruptible} cause={f.frame.interruptedCause.isSome}"

def shopBuilt : Option Api.Built := (Effect4.Api.Author.build (shop .none)).toOption

def afterStart (b : Api.Built) : NativeMachine :=
  steppedBy b.program 2000 b.table (Api.load b.program 2000) (.evaluate Api.root)

def flushAt (b : Api.Built) (k : Nat) : NativeMachine :=
  steppedBy b.program k b.table (afterStart b) .flush

def dedup : List String → List String
  | [] => []
  | x :: xs => if xs.contains x then dedup xs else x :: dedup xs

#eval (shopBuilt.map fun b => dedup ((List.range 400).map fun k => shapeOf ((flushAt b k).fiber? ⟨3⟩))).map List.length
#eval (shopBuilt.map fun b => dedup ((List.range 400).map fun k => shapeOf ((flushAt b k).fiber? ⟨3⟩)))
