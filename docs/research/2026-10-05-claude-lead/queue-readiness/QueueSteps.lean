import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Folds
import Test.Program.QueueModel

/-!
# Probe: the Queue's first profile with the real steps, after seat FOLD's merge

Status: research evidence (2026-10-05, base `0dbb17c3`). A finite probe: one schedule for each
scenario, on the Lean machine only. `QueueSteps.out` beside this file is its output.

    lake env lean docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean

The cell is one record: the buffer, the waiting takers, the pending offers and the capacity.
A request's identity is a `Deferred` that nobody resolves. Each step is one `Ref.modify` whose
term folds: it finds a request by `sameHandle`, removes it, accepts pending offers into freed
room, and names the hints to post. The first profile is the contract's: a positive capacity and
the `suspend` strategy, with `take` and `offer` of one message.

`uninterruptible` stands for the mask and `interruptible` for its restore, which is right under
an interruptible caller only. The answers are compared with the abstract model of
`Test/Program/QueueModel.lean` on the same operations.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace QueueSteps
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## The cell -/

/-- A request's identity, and a taker's hint: a Deferred of nothing that cannot fail. -/
def idTy : Ty := .deferredOf .unit .never
/-- An offerer's hint carries the decided answer (decisions row 240). -/
def answerTy : Ty := .deferredOf .bool .never

def takerFields : List (String × Bool × Ty) := [("id", false, idTy), ("hint", false, idTy)]
def takerTy : Ty := .record [("hint", false, idTy), ("id", false, idTy)]
def offerFields : List (String × Bool × Ty) :=
  [("id", false, idTy), ("hint", false, answerTy), ("msg", false, .nat)]
def offerTy : Ty := .record [("hint", false, answerTy), ("id", false, idTy), ("msg", false, .nat)]
def stateFields : List (String × Bool × Ty) :=
  [("msgs", false, .list .nat), ("takers", false, .list takerTy),
   ("offers", false, .list offerTy), ("cap", false, .nat)]

def nilT : TermSrc := app "nil" []
def noneT : TermSrc := app "none" []
def len (xs : TermSrc) : TermSrc := app "length" [xs]
def snoc (xs x : TermSrc) : TermSrc := app "append" [xs, app "cons" [x, nilT]]
def notT (b : TermSrc) : TermSrc := app "not" [b]
def andT (a b : TermSrc) : TermSrc := app "and" [a, b]
def orT (a b : TermSrc) : TermSrc := app "or" [a, b]
def empty (xs : TermSrc) : TermSrc := app "isZero" [len xs]
def ite (c t f : TermSrc) : TermSrc := app "ite" [c, t, f]
def same (a b : TermSrc) : TermSrc := app "sameHandle" [a, b]

def state0 (cap : Nat) : TermSrc :=
  record stateFields [("msgs", nilT), ("takers", nilT), ("offers", nilT), ("cap", nat cap)]

def mkTaker (id hint : TermSrc) : TermSrc := record takerFields [("id", id), ("hint", hint)]
def mkOffer (id hint msg : TermSrc) : TermSrc :=
  record offerFields [("id", id), ("hint", hint), ("msg", msg)]

/-! ## The pure parts, each one fold -/

/-- Whether the request `id` waits among the takers. -/
def enrolled (takers id : TermSrc) : TermSrc :=
  fold "e_acc" "e_t" none takers (bool false) (orT (var "e_acc") (same (field (var "e_t") "id") id))

/-- Whether the request `id` is the earliest taker. -/
def isHead (takers id : TermSrc) : TermSrc :=
  fold "h_acc" "h_t" none (app "take" [takers, nat 1]) (bool false)
    (same (field (var "h_t") "id") id)

/-- The takers without the request `id`. -/
def removeTaker (takers id : TermSrc) : TermSrc :=
  fold "r_acc" "r_t" (some (.list takerTy)) takers nilT
    (ite (same (field (var "r_t") "id") id) (var "r_acc") (snoc (var "r_acc") (var "r_t")))

/-- The takers, with the hint of the request `id` replaced. -/
def renewHint (takers id hint : TermSrc) : TermSrc :=
  fold "n_acc" "n_t" (some (.list takerTy)) takers nilT
    (snoc (var "n_acc") (ite (same (field (var "n_t") "id") id) (mkTaker id hint) (var "n_t")))

/-- The pending offers without the request `id`. -/
def removeOffer (offers id : TermSrc) : TermSrc :=
  fold "o_acc" "o_t" (some (.list offerTy)) offers nilT
    (ite (same (field (var "o_t") "id") id) (var "o_acc") (snoc (var "o_acc") (var "o_t")))

/-- The hint of the earliest taker, as a list of at most one, when a message is ready. -/
def wake (takers msgs : TermSrc) : TermSrc :=
  ite (empty msgs) nilT
    (fold "w_acc" "w_t" (some (.list idTy)) (app "take" [takers, nat 1]) nilT
      (snoc (var "w_acc") (field (var "w_t") "hint")))

/-- The accumulator of the accept pass: room, buffer, kept offers, answered hints. -/
def acceptTy : Ty := .tuple [.nat, .list .nat, .list offerTy, .list answerTy]

/-- Pending offers enter freed room in arrival order (the model's `acceptLoop`, one message
for each offer). An offer behind one that stays also stays. -/
def accept (room msgs offers : TermSrc) : TermSrc :=
  fold "a_acc" "a_o" (some acceptTy) offers (tuple [room, msgs, nilT, nilT])
    (ite (andT (notT (app "isZero" [tupleAt (var "a_acc") 0])) (empty (tupleAt (var "a_acc") 2)))
      (tuple [app "pred" [tupleAt (var "a_acc") 0],
        snoc (tupleAt (var "a_acc") 1) (field (var "a_o") "msg"),
        tupleAt (var "a_acc") 2,
        snoc (tupleAt (var "a_acc") 3) (field (var "a_o") "hint")])
      (tuple [tupleAt (var "a_acc") 0, tupleAt (var "a_acc") 1,
        snoc (tupleAt (var "a_acc") 2) (var "a_o"), tupleAt (var "a_acc") 3]))

/-! ## The steps, each one term of a `Ref.modify` -/

/-- A take of one message. Answer: `[message?, hints of takers to wake, hints of offers
answered]`. It consumes when a message is there and no earlier taker waits. Otherwise it
enrols the request, or renews its hint. -/
def takeStep (id hint s : TermSrc) : TermSrc :=
  let msgs := field s "msgs"
  let takers := field s "takers"
  let offers := field s "offers"
  let turn := orT (isHead takers id) (andT (notT (enrolled takers id)) (empty takers))
  let msgs1 := app "drop" [msgs, nat 1]
  let takers1 := removeTaker takers id
  let acc := accept (app "sub" [field s "cap", len msgs1]) msgs1 offers
  let consumed := recordSet (recordSet (recordSet s "msgs" (tupleAt acc 1)) "takers" takers1)
    "offers" (tupleAt acc 2)
  let waiting := recordSet s "takers"
    (ite (enrolled takers id) (renewHint takers id hint) (snoc takers (mkTaker id hint)))
  ite (andT (notT (empty msgs)) turn)
    (app "pair" [tuple [app "get" [msgs, nat 0], wake takers1 (tupleAt acc 1), tupleAt acc 3],
      consumed])
    (app "pair" [tuple [noneT, nilT, nilT], waiting])

/-- An offer of one message. Answer: `[decided?, hints of takers to wake]`. It is accepted
when room is left and no earlier offer is pending. Otherwise it stays pending with its hint. -/
def offerStep (id hint a s : TermSrc) : TermSrc :=
  let msgs := field s "msgs"
  let accepted := recordSet s "msgs" (snoc msgs a)
  let pending := recordSet s "offers" (snoc (field s "offers") (mkOffer id hint a))
  ite (andT (app "lt" [len msgs, field s "cap"]) (empty (field s "offers")))
    (app "pair" [tuple [app "some" [bool true], wake (field s "takers") (snoc msgs a)], accepted])
    (app "pair" [tuple [noneT, nilT], pending])

/-- A waiting taker leaves. Answer: the hints to wake. -/
def withdrawTake (id s : TermSrc) : TermSrc :=
  let takers1 := removeTaker (field s "takers") id
  app "pair" [wake takers1 (field s "msgs"), recordSet s "takers" takers1]

/-- A pending offer leaves. An offer that a step already accepted is not there, so nothing
changes. -/
def withdrawOffer (id s : TermSrc) : TermSrc :=
  recordSet s "offers" (removeOffer (field s "offers") id)

/-! ## The operations -/

def posted : Effect4.Supervision.ForkOptions := ⟨false, true, .uninterruptible⟩

/-- Post every hint of a list with one answer: one helper for each (decisions row 238). -/
def postAll (hints answer : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len hints]
      body := fun i => selectOption "h" (app "get" [hints, i]) (succeed unit)
        (andThen (withFiber (Action.fork (Deferred.succeed (var "h") answer) posted))
          (succeed unit))
      step := fun i _ => app "succ" [i] }

/-- The pin's `onInterrupt`: `onExit` with a test of the exit. -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

def take (q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    let got ← iterateWith noneT
      { cursorTy := some (.option .nat)
        while_ := fun c => notT (app "isSome" [c])
        body := fun _ => eff do
          let hint ← Deferred.make .unit .never
          let r ← Ref.modify "s" (takeStep id hint (var "s")) q
          let _ ← postAll (tupleAt r 1) unit
          let _ ← postAll (tupleAt r 2) (bool true)
          selectOption "m" (tupleAt r 0)
            (andThen
              (onInterrupt (interruptible (Deferred.await hint))
                (eff do
                  let hints ← Ref.modify "s" (withdrawTake id (var "s")) q
                  postAll hints unit))
              (succeed noneT))
            (succeed (app "some" [var "m"]))
        step := fun _ a => a }
    selectOption "m" got (failCause (Cause.die (str "queue: the loop ended without a message")))
      (succeed (var "m")))

def offer (q a : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    let hint ← Deferred.make .bool .never
    let r ← Ref.modify "s" (offerStep id hint a (var "s")) q
    let _ ← postAll (tupleAt r 1) unit
    selectOption "ok" (tupleAt r 0)
      (onInterrupt (interruptible (Deferred.await hint))
        (Ref.update "s" (withdrawOffer id (var "s")) q))
      (succeed (var "ok")))

def size (q : TermSrc) : Src NativeOp := eff do
  let s ← Ref.get q
  return len (field s "msgs")

/-! ## Runs -/

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def verdict (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

def showReason : Reason Err Defect FiberId Ann → String
  | .fail _ _ => "fail"
  | .interrupt who _ => "interrupt by " ++ toString (repr who)
  | .die _ _ => "die"

def showExit : Option ExitV → String
  | none => "no exit"
  | some (.success v) => "success " ++ toString (repr v)
  | some (.failure c) => "failure " ++ toString (c.reasons.map showReason)

def exitOf (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => "not built"
  | .ok b =>
    let r := (List.range 3).foldl (fun (s : Run) _ => s.control Effect4.Api.flush)
      (Run.runPure b "q" { fuel := 20000, compileFuel := 20000 })
    showExit r.exit

/-- R1: two offers into room, then two takes. -/
def r1 : Src NativeOp := eff do
  let q ← Ref.make (state0 2)
  let a ← offer q (nat 1)
  let b ← offer q (nat 2)
  let x ← take q
  let y ← take q
  return tuple [a, b, x, y]

/-- R2: a taker waits; an offer wakes it. -/
def r2 : Src NativeOp := eff do
  let q ← Ref.make (state0 2)
  let f ← fork (take q)
  let _ ← offer q (nat 7)
  let x ← join f
  return x

/-- R3: two takers wait in order; two offers; each gets its message in order. -/
def r3 : Src NativeOp := eff do
  let q ← Ref.make (state0 2)
  let fa ← fork (take q)
  let fb ← fork (take q)
  let _ ← offer q (nat 1)
  let _ ← offer q (nat 2)
  let x ← join fa
  let y ← join fb
  return tuple [x, y]

/-- R4: capacity one. A second offer waits; the take that frees room accepts it and its
answer is posted; then the second message is taken. -/
def r4 : Src NativeOp := eff do
  let q ← Ref.make (state0 1)
  let a ← offer q (nat 1)
  let f ← fork (offer q (nat 2))
  let x ← take q
  let b ← join f
  let y ← take q
  return tuple [a, x, b, y]

/-- R5: a waiting taker is interrupted; a later offer stays; the next take gets it. -/
def r5 : Src NativeOp := eff do
  let q ← Ref.make (state0 2)
  let f ← fork (take q)
  let _ ← withFiber (Action.interrupt f)
  let _ ← offer q (nat 5)
  let x ← take q
  let s ← Ref.get q
  return tuple [x, len (field s "takers")]

/-- R6: capacity one. A pending offer is interrupted before any step accepts it: its message
never enters. -/
def r6 : Src NativeOp := eff do
  let q ← Ref.make (state0 1)
  let _ ← offer q (nat 1)
  let f ← fork (offer q (nat 2))
  let _ ← withFiber (Action.interrupt f)
  let x ← take q
  let n ← size q
  let s ← Ref.get q
  return tuple [x, n, len (field s "offers")]

/-- R7: the interrupted taker's own exit keeps its interruptor. -/
def r7 : Src NativeOp := eff do
  let q ← Ref.make (state0 2)
  let f ← fork (take q)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  return e

#eval (verdict (mk r1), verdict (mk r2), verdict (mk r3), verdict (mk r4), verdict (mk r5),
  verdict (mk r6), verdict (mk r7))
#eval (Effect4.Api.Author.build (mk r4)).toOption.map fun b =>
  toString (repr (b.ty.answer, b.ty.error))
#eval exitOf r1
#eval exitOf r2
#eval exitOf r3
#eval exitOf r4
#eval exitOf r5
#eval exitOf r6
#eval exitOf r7

/-! ## The same operations on the abstract model -/

/-- R1 on the model: both offers accepted, then the two messages in order. -/
def model1 : QueueContract.OfferReply × QueueContract.OfferReply × QueueContract.TakeReply ×
    QueueContract.TakeReply :=
  let s : QueueContract.State := { capacity := some 2 }
  let a := QueueContract.offer s 100 1
  let b := QueueContract.offer a.1 101 2
  let x := QueueContract.take b.1 ⟨1, 1, 1⟩
  let y := QueueContract.take x.1 ⟨2, 1, 1⟩
  (a.2.1, b.2.1, x.2.1, y.2.1)

/-- R4 on the model: the second offer waits; the take frees room and answers it; then the
second message. -/
def model4 : QueueContract.OfferReply × QueueContract.OfferReply × QueueContract.TakeReply ×
    List QueueContract.Signal × QueueContract.TakeReply :=
  let s : QueueContract.State := { capacity := some 1 }
  let a := QueueContract.offer s 100 1
  let b := QueueContract.offer a.1 101 2
  let x := QueueContract.take b.1 ⟨1, 1, 1⟩
  let y := QueueContract.take x.1 ⟨2, 1, 1⟩
  (a.2.1, b.2.1, x.2.1, x.2.2, y.2.1)

#eval toString (repr model1)
#eval toString (repr model4)

/-! ## The size of the take step

The term language has no local binding. The accept pass and the removal are written once in
Lean and occur several times in the term. -/

mutual
def termSize : Term → Nat
  | .var _ | .lit _ => 1
  | .app _ args => 1 + argsSize args
  | .record _ _ values => 1 + argsSize values
  | .field _ t _ => 1 + termSize t
  | .recordSet t _ v => 1 + termSize t + termSize v
  | .tupleAt t _ => 1 + termSize t
  | .fold _ l i b => 1 + termSize l + termSize i + termSize b
def argsSize : Terms → Nat
  | .nil => 0
  | .cons t ts => termSize t + argsSize ts
end

/-- How many folds a term holds. -/
def foldCount : Term → Nat
  | .var _ | .lit _ => 0
  | .app _ args => foldCounts args
  | .record _ _ values => foldCounts values
  | .field _ t _ => foldCount t
  | .recordSet t _ v => foldCount t + foldCount v
  | .tupleAt t _ => foldCount t
  | .fold _ l i b => 1 + foldCount l + foldCount i + foldCount b
where foldCounts : Terms → Nat
  | .nil => 0
  | .cons t ts => foldCount t + foldCounts ts

def stepTerm (step : TermSrc) : Option Term :=
  (step { names := ["id", "hint", "s"] } []).toOption

-- The take step: its nodes and its folds. Then one accept pass, and the offer step.
#eval (stepTerm (takeStep (var "id") (var "hint") (var "s"))).map fun t => (termSize t, foldCount t)
#eval (stepTerm (accept (nat 1) nilT nilT)).map fun t => (termSize t, foldCount t)
#eval (stepTerm (offerStep (var "id") (var "hint") (nat 1) (var "s"))).map fun t =>
  (termSize t, foldCount t)

/-! ## What the faces answer today

The printer refuses the first thing it cannot spell. Seat T5 lifts both refusals. -/

def printVerdict (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => "not built"
  | .ok b =>
    match Effect4.Api.emitModule "main" b.program b.table with
    | .ok _ => "printed"
    | .error (.print (.binderTerm spelling)) => "refused: binderTerm " ++ spelling
    | .error (.print (.typeSpelling name)) => "refused: typeSpelling " ++ name
    | .error (.print (.internalAction name)) => "refused: internalAction " ++ name
    | .error _ => "refused"

/-- A hint alone: `Deferred.make` at a type the printer does not spell yet. -/
def hintOnly : Src NativeOp := eff do
  let hint ← Deferred.make .unit .never
  let _ ← Deferred.succeed hint unit
  return nat 1

/-- The posted helper alone, at a type the printer spells. -/
def helperOnly : Src NativeOp := eff do
  let hint ← Deferred.make .nat .nat
  let _ ← withFiber (Action.fork (Deferred.succeed hint (nat 1)) posted)
  return nat 1

#eval (printVerdict r4, printVerdict hintOnly, printVerdict helperOnly)

end QueueSteps
