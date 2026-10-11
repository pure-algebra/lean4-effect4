import Effect4.Api

/-!
Probe (scratch): is a parked fiber's frame stack a chain in the program tree's prefix order?
For each fiber parked after the root's first evaluation, read the point each frame's name
carries (where one does), top first, and check that each frame's path extends the path of the
frame below it, within one call segment (`Point.call`).
-/

open Effect4 Effect4.Machine Effect4.Program

namespace StackProbe

abbrev M := Api.Machine
def fuel : Nat := 400

/-- The point a continuation name carries, for the names whose meaning is a subterm. -/
def namePoint? : EffName → Option (String × Point)
  | .cont p => some ("cont", p)
  | .caught p => some ("caught", p)
  | .onValue p => some ("onValue", p)
  | .onCause p => some ("onCause", p)
  | .fin p => some ("fin", p)
  | .gen p pc _ => some (s!"gen pc={pc}", p)
  | .loop p => some ("loop", p)
  | .scopeBody p _ => some ("scopeBody", p)
  | .caughtError p => some ("caughtError", p)
  | _ => none

/-- The names a frame stores. -/
def frameNames : NCode → List EffName
  | .onSuccess _ n => [n]
  | .onFailure _ n => [n]
  | .onSuccessAndFailure _ a b => [a, b]
  | .onExit _ n _ => [n]
  | .iterator n _ => [n]
  | .whileLoop n _ => [n]
  | .asyncFinalizer n => [n]
  | _ => []

def frameTag : NCode → String
  | .onSuccess _ _ => "OnSuccess"
  | .onSuccessConst _ _ => "OnSuccessConst"
  | .onFailure _ _ => "OnFailure"
  | .onSuccessAndFailure _ _ _ => "OnSuccessAndFailure"
  | .onExit _ _ _ => "OnExit"
  | .iterator _ _ => "Iterator"
  | .whileLoop _ _ => "While"
  | .asyncFinalizer _ => "AsyncFinalizer"
  | .setInterruptible b => s!"SetInterruptible {b}"
  | .exitFrame _ => "Exit"
  | _ => "other"

/-- One frame read: its tag, and the (kind, path, call) of the first name with a point. -/
def readFrame (c : NCode) : String × Option (String × List Nat × List (List Nat)) :=
  (frameTag c, ((frameNames c).filterMap namePoint?).head?.map fun (k, p) => (k, p.path, p.call))

/-- The chain check: top first, each pointed frame's path extends the next pointed frame's path
below it in the same call segment. -/
def chainOk : List (List Nat × List (List Nat)) → Bool
  | a :: b :: rest => (if a.2 == b.2 then b.1.isPrefixOf a.1 && a.1 != b.1 else true) && chainOk (b :: rest)
  | _ => true

def report (_p : NativeEff) (m : M) : List String :=
  m.fibers.map fun f =>
    let frames := f.frame.stack.map readFrame
    let pts := frames.filterMap (·.2) |>.map fun (_, path, call) => (path, call)
    s!"fiber {f.id.value} parked={f.parked != .notParked} exit={f.exit.isSome} chain={chainOk pts}\n" ++
      String.intercalate "\n" (frames.map fun (t, x) =>
        match x with
        | some (k, path, call) => s!"    {t} [{k} {path} call={call}]"
        | none => s!"    {t}")

def stepD (p : NativeEff) (m : M) (d : Api.Decision) : M :=
  letI := evaluatorFor p []
  (stepDecisionState (interpOf p []) fuel m d).1

def run (name : String) (p : NativeEff) : IO Unit := do
  let m := stepD p (Api.load p fuel) Api.evaluate
  IO.println s!"== {name}"
  for line in report p m do IO.println line

def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit

/-- Regions nested around a yield: a bind, a catch, an onExit, a matchCause. -/
def nested : NativeEff :=
  .bind
    (.catchCause
      (.onExit
        (.matchCause (.bind (.yieldNow 0) (.succeed (n 1))) (.succeed (.var 0)) (.succeed (n 0)))
        (.succeed u))
      (.succeed (n 2)))
    (.succeed (.var 0))

/-- A generator and a loop around a yield. -/
def genLoop : NativeEff :=
  .bind
    (.gen (.cons (.bindYield (.bind (.yieldNow 0) (.succeed (n 3)))) (.cons (.ret (.var 0)) .nil)))
    (.iterate none (n 0) (.app "lt" (.cons (.var 1) (.cons (n 2) .nil)))
      (.app "succ" (.cons (.var 1) .nil)) (.var 1)
      (.bind (.yieldNow 0) (.succeed u)))

/-- A definition whose parameter is a program; the passed program yields. -/
def withCall : NativeEff :=
  .defs
    [{ name := "f", request := .unit, answer := .nat,
       params := [{ name := "p", request := .unit, answer := .nat }] }]
    (.cons (.bind (.bind (.perform (.param 0) u) (.succeed (.var 1))) (.succeed (.var 1))) .nil)
    (.bind (.invoke 0 u (.cons (.bind (.yieldNow 0) (.succeed (n 7))) .nil)) (.succeed (.var 0)))
    .nil

/-- A definition that invokes itself twice, then yields at the leaf. -/
def recur : NativeEff :=
  .defs
    [{ name := "f", request := .nat, answer := .nat }]
    (.cons (.select (.app "lt" (.cons (.var 0) (.cons (n 2) .nil))) .bool
      (.bind (.perform (.call 0) (.app "succ" (.cons (.var 0) .nil))) (.succeed (.var 1)))
      (.bind (.yieldNow 0) (.succeed (n 9)))) .nil)
    (.bind (.perform (.call 0) (n 0)) (.succeed (.var 0)))
    .nil

end StackProbe

open StackProbe in
def main : IO Unit := do
  run "nested" nested
  run "genLoop" genLoop
  run "withCall" withCall
  run "recur" recur
