import Test.Dogfood.Scenario.Atomic

open Effect4 Effect4.Program Test.Dogfood.Scenario.Atomic

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def levelAt : Node NativeOp → Nat → List Nat → Option Nat
  | _, n, [] => some n
  | node, n, i :: rest => (node.child i).bind fun c => levelAt c (node.childLevel n i) rest

def performSites (root : NativeEff) : List (List Nat × NativeOp × Term × Option Nat) :=
  (Node.addresses (.eff root)).filterMap fun path =>
    match Node.at_ (.eff root) path with
    | some (.eff (.perform op request)) => some (path, op, request, levelAt (.eff root) 0 path)
    | _ => none

def shopProgram : Option NativeEff := (Authoring.elaborateModule (shop .none)).toOption

#eval (shopProgram.map fun p => (performSites p).length)
def kind : NativeOp → String
  | .refMake => "refMake" | .refGet => "refGet" | .refSet => "refSet"
  | .refUpdateWith _ => "refUpdateWith" | .refModifyWith _ => "refModifyWith"
  | .sleep => "sleep" | .clockNow => "clockNow" | _ => "other"

#eval (shopProgram.map fun p => (performSites p).map fun (path, op, _, lvl) => (path, kind op, lvl))


-- kernel: the census length
example : (shopProgram.map fun p => (performSites p).length) = some 31 := by decide

-- kernel: every site has a level
example : (shopProgram.map fun p => (performSites p).all fun site => site.2.2.2.isSome) = some true := by decide

deriving instance Repr for Effect4.Program.Lit
deriving instance Repr for Effect4.Program.FieldReadMode
deriving instance Repr for Effect4.Program.Term, Effect4.Program.Terms

def termsOf (p : NativeEff) : List (String × Option Nat × Term) :=
  (performSites p).filterMap fun (_, op, _, lvl) =>
    match op with
    | .refModifyWith f => some ("modify", lvl, f)
    | .refUpdateWith f => some ("update", lvl, f)
    | _ => none

#eval (shopProgram.map fun p => (((termsOf p).drop 3).take 1).map fun (k, l, f) => (k, l, repr f))
#eval (shopProgram.map fun p => (performSites p).filterMap fun (path, op, req, lvl) => match op with | .refMake => some (path, lvl, repr req) | _ => none)
