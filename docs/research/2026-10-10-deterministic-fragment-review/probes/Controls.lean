import Fragment
import ReviewTapes
import Effect4.Laws.Machine.Behaviour

/-! Finite design controls; no schedule-independence theorem is asserted. -/
namespace DetProbe.Controls
open Effect4 Effect4.Program Effect4.Machine
open Effect4.Program.Authoring

abbrev S := Src NativeOp

def thenDo : S → S → S := Forms.andThenEffect
def joinNamed (name : String) : S := awaitFiber (var name) .joinEffect

def workers (a b result : S) : S :=
  bind "left" (Forms.forkChildDefault a)
    (bind "right" (Forms.forkChildDefault b)
      (thenDo (joinNamed "left") (thenDo (joinNamed "right") result)))

def setWorker (name : String) (n : Nat) : S :=
  thenDo Forms.yieldNow (Forms.asVoid (Ref.set (var name) (nat n)))
def addWorker (name : String) (n : Nat) : S :=
  thenDo Forms.yieldNow (Ref.updateWith (var name) fun x => app "add" [x, nat n])
def readWorker (name : String) : S :=
  thenDo Forms.yieldNow (Forms.asVoid (Ref.get (var name)))
def oneCell (a b : S) : S := bind "r" (Ref.make (nat 0))
  (workers a b (Ref.get (var "r")))

def privateCells : S :=
  bind "r" (Ref.make (nat 0)) (bind "s" (Ref.make (nat 0))
    (workers (setWorker "r" 1) (setWorker "s" 2)
      (bind "x" (Ref.get (var "r")) (bind "y" (Ref.get (var "s"))
        (succeed (app "pair" [var "x", var "y"]))))))
def sharedAdds : S := oneCell (addWorker "r" 1) (addWorker "r" 2)
def sharedReads : S := oneCell (readWorker "r") (readWorker "r")
def sharedWrites : S := oneCell (setWorker "r" 1) (setWorker "r" 2)
def readWrite : S := oneCell (setWorker "r" 1) (readWorker "r")
def addRead : S := oneCell (addWorker "r" 1) (readWorker "r")
def aliasedWrite : S := oneCell
  (bind "alias" (succeed (var "r")) (setWorker "alias" 1)) (setWorker "r" 2)
def aliasPrivate : S := bind "r" (Ref.make (nat 0)) (bind "s" (Ref.make (nat 0))
  (workers (bind "alias" (succeed (var "r")) (setWorker "alias" 1))
    (setWorker "s" 2) Forms.void))
def noJoin : S := bind "r" (Ref.make (nat 0))
  (thenDo (Forms.forkChildDefault (setWorker "r" 1)) Forms.void)
def parentRead : S := bind "r" (Ref.make (nat 0))
  (bind "left" (Forms.forkChildDefault (setWorker "r" 1))
    (thenDo (Ref.get (var "r")) (thenDo (joinNamed "left") Forms.void)))
def childAllocation : S := oneCell (Forms.asVoid (Ref.make (nat 1))) Forms.void
def nestedFork : S := oneCell (Forms.asVoid (Forms.forkChildDefault Forms.void)) Forms.void
def promiseWait : S := bind "d" (Deferred.make .nat .never) (Deferred.await (var "d"))
def sharedReturnedUpdates : S := bind "r" (Ref.make (nat 0))
  (bind "left" (Forms.forkChildDefault
    (thenDo Forms.yieldNow (Ref.updateAndGetWith (var "r") fun x => app "succ" [x])))
  (bind "right" (Forms.forkChildDefault
    (thenDo Forms.yieldNow (Ref.updateAndGetWith (var "r") fun x => app "succ" [x])))
  (bind "x" (joinNamed "left") (bind "y" (joinNamed "right")
    (succeed (app "pair" [var "x", var "y"]))))))

def program (source : S) : NativeEff :=
  (elaborate source).toOption.getD (.fail (.lit (.nat 999)))
def accepted (source : S) : Bool := (inspect (program source)).toOption.isSome

def parallelValues : S :=
  bind "left" (Forms.forkChildDefault (thenDo Forms.yieldNow (succeed (nat 21))))
  (bind "right" (Forms.forkChildDefault (thenDo Forms.yieldNow (succeed (nat 2))))
    (bind "x" (joinNamed "left") (bind "y" (joinNamed "right")
      (succeed (app "mul" [var "x", var "y"])))))
def privateResults : S :=
  bind "r" (Ref.make (nat 0)) (bind "s" (Ref.make (nat 0))
  (bind "left" (Forms.forkChildDefault
    (thenDo (setWorker "r" 4) (Ref.get (var "r"))))
  (bind "right" (Forms.forkChildDefault
    (thenDo (setWorker "s" 7) (Ref.get (var "s"))))
  (bind "x" (joinNamed "left") (bind "y" (joinNamed "right")
    (succeed (app "pair" [var "x", var "y"])))))))
def earlyJoinRead : S := bind "r" (Ref.make (nat 0))
  (bind "left" (Forms.forkChildDefault Forms.void)
  (bind "right" (Forms.forkChildDefault (setWorker "r" 2))
    (thenDo (joinNamed "left")
      (thenDo (Ref.get (var "r")) (thenDo (joinNamed "right") Forms.void)))))
def writeBetweenForks : S := bind "r" (Ref.make (nat 0))
  (bind "left" (Forms.forkChildDefault (readWorker "r"))
    (thenDo (Ref.set (var "r") (nat 1))
      (bind "right" (Forms.forkChildDefault Forms.void)
        (thenDo (joinNamed "left") (thenDo (joinNamed "right") Forms.void)))))
def returnedCell : S := bind "r" (Ref.make (nat 0))
  (succeed (app "pair" [nat 1, var "r"]))
def workerCell : S := bind "r" (Ref.make (nat 0))
  (workers (succeed (var "r")) Forms.void Forms.void)
def capturedAddend : S := oneCell
  (bind "n" (succeed (nat 1))
    (Ref.updateWith (var "r") fun x => app "add" [x, var "n"]))
  (addWorker "r" 2)
def reversedAdd : S := oneCell
  (Ref.updateWith (var "r") fun x => app "add" [nat 1, x])
  (addWorker "r" 2)

def sharedReadResults : S := bind "r" (Ref.make (nat 6))
  (bind "left" (Forms.forkChildDefault (thenDo Forms.yieldNow (Ref.get (var "r"))))
  (bind "right" (Forms.forkChildDefault (thenDo Forms.yieldNow (Ref.get (var "r"))))
  (bind "x" (joinNamed "left") (bind "y" (joinNamed "right")
    (succeed (app "pair" [var "x", var "y"]))))))
def sharedReturnedDiscarded : S := oneCell
  (Forms.asVoid (Ref.updateAndGetWith (var "r") fun x => app "succ" [x]))
  (Forms.asVoid (Ref.updateAndGetWith (var "r") fun x => app "succ" [x]))

def good : List S := [privateCells, sharedAdds, sharedReads, aliasPrivate, parallelValues, privateResults, sharedReadResults]
def bad : List S := [sharedWrites, readWrite, addRead, aliasedWrite, noJoin,
  parentRead, childAllocation, nestedFork, promiseWait, sharedReturnedUpdates, earlyJoinRead,
  writeBetweenForks, returnedCell, workerCell, capturedAddend, reversedAdd, sharedReturnedDiscarded]

#guard (good ++ bad).all fun s => (elaborate s).toOption.isSome
#guard (good ++ bad).all fun s => (Api.explain (program s)).isNone
#guard good.all accepted
#guard bad.all fun s => !accepted s
#guard (inspect (program aliasedWrite)).toOption.isNone
#guard (inspect (program aliasPrivate)).toOption.isSome
#eval ("accepted ordinary author programs", good.length)
#eval ("refused ordinary author programs", bad.length)
#eval (inspect (program aliasedWrite)).toOption.isNone
#eval match inspect (program aliasedWrite) with | .error (.fragment e) => some e | _ => none
#eval match inspect (program parentRead) with | .error (.fragment e) => some e | _ => none

/-- Stronger than the original root-exit/reference-only probe observation. -/
def sameFullObservation (runs : List (List Api.Decision × Api.Machine × String)) : Bool :=
  match runs with
  | [] => false
  | (_, first, _) :: rest => rest.all fun (_, m, _) => decide (obs m = obs first)
def finishedRuns (runs : List (List Api.Decision × Api.Machine × String)) : Bool :=
  !runs.isEmpty && runs.all fun (_, m, why) => why == "complete" && m.finished

def runs (source : S) := TapeProbe.explore (program source) 12 (TapeProbe.start (program source))
def runsY (source : S) := TapeProbe.exploreY (program source) 12 2 (TapeProbe.start (program source))

/-- Retain the initial and every decision's sufficiency receipt, including yield verdicts. -/
def funded (source : S) (tape : List Api.Decision) : Bool :=
  let p := program source
  let initial := TapeProbe.stepD p (Api.load p 400) Api.evaluate
  (tape.foldl (fun (acc : Api.Machine × Bool) d =>
    let next := TapeProbe.stepD p acc.1 d
    (next.1, acc.2 && next.2)) initial).2

#guard good.all fun s => ((runs s) ++ (runsY s)).all fun (tape, _, _) => funded s tape
#guard good.all fun s => (TapeProbe.stepD (program s) (Api.load (program s) 400) Api.evaluate).2
#guard good.all fun s => finishedRuns (runs s) && sameFullObservation (runs s)
#guard good.all fun s => finishedRuns (runsY s) && sameFullObservation (runsY s)
#eval good.map fun s => ((runs s).length, (runsY s).length,
  sameFullObservation (runs s), sameFullObservation (runsY s))
#guard finishedRuns (runs sharedReturnedUpdates)
#guard !sameFullObservation (runs sharedReturnedUpdates)
#guard (runs sharedReturnedUpdates).all fun (_, m, _) => m.state.refs == [.nat 2]
#eval TapeProbe.summary (program sharedReturnedUpdates) 12

/-- No armed callback does not imply a finished run. -/
def blocked := Api.run (program promiseWait) 400
#guard blocked.machine.armed.isEmpty
#guard !blocked.machine.finished
#guard blocked.machine.stuck.isNone
#guard TapeProbe.endings (program promiseWait) 12 == ["complete"]

/-- Zero initial fuel is already cut; the original start helper drops that receipt. -/
def zeroStart :=
  let p := program privateCells
  letI := evaluatorFor p []
  stepDecisionState (interpOf p []) 0 (Api.load p 400) Api.evaluate
#guard !zeroStart.2
#guard !zeroStart.1.finished
#guard zeroStart.1.armed.isEmpty

/-- Disabled raw fires admit arbitrary extra tape length with the same observation. -/
def finished := (Api.run (program privateCells) 400).machine
def padded :=
  let p := program privateCells
  letI := evaluatorFor p []
  replayEval (interpOf p []) 400 (List.replicate 9 (.fire ⟨999⟩)) finished
#guard finished.finished
#guard decide (obs padded.machine = obs finished)
#guard padded.machine.finished

end DetProbe.Controls
