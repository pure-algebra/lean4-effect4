import Test.Dogfood.Scenario.Atomic

/-!
# Measure: the shop's write sites and its fibers' shapes (finite probes)

The numbers of `README.md` come from this file: `lake env lean` on it prints them. Each line is
a finite probe on the Lean machine, outside any proof.

1. The census of the shop's `perform` sites: each address, its row and its level.
2. The frame shapes of a request fiber at command boundaries: the scenario's flush is cut at
   every fuel from 0 to 399, and the fiber's shape is read after each cut.
3. The frame shapes of request 2 alone (`alone .none false`, one fiber), the failing path.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Probe.StoreInvariants.Measure

open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario.Atomic

/-! ## 1. The census -/

def levelAt : Node NativeOp → Nat → List Nat → Option Nat
  | _, n, [] => some n
  | node, n, i :: rest => (node.child i).bind fun c => levelAt c (node.childLevel n i) rest

def performSites (root : NativeEff) : List (List Nat × NativeOp × Term × Option Nat) :=
  (Node.addresses (.eff root)).filterMap fun path =>
    match Node.at_ (.eff root) path with
    | some (.eff (.perform op request)) => some (path, op, request, levelAt (.eff root) 0 path)
    | _ => none

def kind : NativeOp → String
  | .refMake => "refMake"
  | .refGet => "refGet"
  | .refUpdateWith _ => "refUpdateWith"
  | .refModifyWith _ => "refModifyWith"
  | .sleep => "sleep"
  | _ => "other"

def shopProgram : Option NativeEff := (Authoring.elaborateModule (shop .none)).toOption

-- 31 sites
#eval shopProgram.map fun p => (performSites p).length
-- each site: its address, its row and its level
#eval shopProgram.map fun p => (performSites p).map fun (path, op, _, lvl) => (path, kind op, lvl)

/-! ## 2. The shapes of a request fiber -/

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
    s!"{primTag f.frame.current} | {f.frame.stack.map frameTag} | run={f.running} park={decide (f.parked ≠ .notParked)} exit={f.exit.isSome} int={f.frame.interruptible}"

def dedup : List String → List String
  | [] => []
  | x :: xs => if xs.contains x then dedup xs else x :: dedup xs

def shopBuilt : Option Api.Built := (Effect4.Api.Author.build (shop .none)).toOption

def afterStart (b : Api.Built) : NativeMachine :=
  steppedBy b.program 2000 b.table (Api.load b.program 2000) (.evaluate Api.root)

def flushAt (b : Api.Built) (k : Nat) : NativeMachine :=
  steppedBy b.program k b.table (afterStart b) .flush

-- request 1 (fiber 2), admitted and not failing: 23 shapes
#eval (shopBuilt.map fun b => dedup ((List.range 400).map fun k => shapeOf ((flushAt b k).fiber? ⟨2⟩))).map List.length
#eval shopBuilt.map fun b => dedup ((List.range 400).map fun k => shapeOf ((flushAt b k).fiber? ⟨2⟩))

/-! ## 3. Request 2 alone: the failing path -/

def aloneBuilt : Option Api.Built := (Effect4.Api.Author.build (alone .none false)).toOption

def aloneAt (b : Api.Built) (k : Nat) : NativeMachine :=
  steppedBy b.program k b.table (Api.load b.program 2000) (.evaluate Api.root)

-- 33 shapes, of which the first nine are the three allocations
#eval (aloneBuilt.map fun b => dedup ((List.range 200).map fun k => shapeOf ((aloneAt b k).fiber? Api.root))).map List.length
#eval aloneBuilt.map fun b => dedup ((List.range 200).map fun k => shapeOf ((aloneAt b k).fiber? Api.root))

end Probe.StoreInvariants.Measure
