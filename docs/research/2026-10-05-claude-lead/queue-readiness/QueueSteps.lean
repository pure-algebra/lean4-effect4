import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Folds
import Effect4.Codegen.ListFold
import Test.Program.QueueModel

/-!
# Probe: the Queue's first profile with the real steps, after seat FOLD's merge

Status: research evidence (2026-10-05, base `61fecd0c`; revised twice the same day after
Codex's two reviews of the step design). A finite probe: one schedule for each scenario, on the
Lean machine only. `QueueSteps.out` beside this file is its output.

    lake env lean docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean

The cell is one record: the buffer, the waiting takers, the pending offers and the capacity.
A request's identity is a `Deferred` that nobody resolves. Each step is one `Ref.modify` whose
term folds: it finds a request by `sameHandle`, removes it, accepts pending offers into freed
room, and names the requests to notify. The first profile is the contract's: a positive
capacity and the `suspend` strategy, with `take` and `offer` of one message.

A step names its notifications as the abstract model does (`Test/Program/QueueModel.lean`), and
in the model's order: the offers that the step accepted, then the taker to wake. Section
"The first profile's states" states the closed predicate that a step goal quantifies over.
Section "The steps against the model" compares each step's answer, stored value and ordered
notifications with the model's: on named states, and on every state of a finite universe of the
profile. A comparison refuses a state outside the profile, and a signal with no encoding. No
fold of a step states a type: an empty list of the right type is `take xs 0`, so every step term
is inside the reader's domain.

`uninterruptible` stands for the mask and `interruptible` for its restore, which is right under
an interruptible caller only.
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
/-- A pending offer, with the model's fields: `batch` is false in the first profile, and `rest`
holds one message. -/
def offerFields : List (String × Bool × Ty) :=
  [("id", false, idTy), ("hint", false, answerTy), ("batch", false, .bool),
   ("rest", false, .list .nat)]
def offerTy : Ty := .record
  [("batch", false, .bool), ("hint", false, answerTy), ("id", false, idTy),
   ("rest", false, .list .nat)]
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
/-- The empty list at the type of `xs`: no fold has to state its accumulator's type. -/
def none_of (xs : TermSrc) : TermSrc := app "take" [xs, nat 0]
def minT (a b : TermSrc) : TermSrc := ite (app "lt" [a, b]) a b

def state0 (cap : Nat) : TermSrc :=
  record stateFields [("msgs", nilT), ("takers", nilT), ("offers", nilT), ("cap", nat cap)]

def mkTaker (id hint : TermSrc) : TermSrc := record takerFields [("id", id), ("hint", hint)]
def mkOffer (id hint batch rest : TermSrc) : TermSrc :=
  record offerFields [("id", id), ("hint", hint), ("batch", batch), ("rest", rest)]

/-! ## The pure parts -/

/-- Whether the request `id` waits among the takers. -/
def enrolled (takers id : TermSrc) : TermSrc :=
  fold "e_acc" "e_t" none takers (bool false) (orT (var "e_acc") (same (field (var "e_t") "id") id))

/-- Whether the request `id` is the earliest taker. -/
def isHead (takers id : TermSrc) : TermSrc :=
  fold "h_acc" "h_t" none (app "take" [takers, nat 1]) (bool false)
    (same (field (var "h_t") "id") id)

/-- The takers without the request `id`. -/
def removeTaker (takers id : TermSrc) : TermSrc :=
  fold "r_acc" "r_t" none takers (none_of takers)
    (ite (same (field (var "r_t") "id") id) (var "r_acc") (snoc (var "r_acc") (var "r_t")))

/-- The takers, with the hint of the request `id` replaced. -/
def renewHint (takers id hint : TermSrc) : TermSrc :=
  fold "n_acc" "n_t" none takers (none_of takers)
    (snoc (var "n_acc") (ite (same (field (var "n_t") "id") id) (mkTaker id hint) (var "n_t")))

/-- The pending offers without the request `id`. -/
def removeOffer (offers id : TermSrc) : TermSrc :=
  fold "o_acc" "o_t" none offers (none_of offers)
    (ite (same (field (var "o_t") "id") id) (var "o_acc") (snoc (var "o_acc") (var "o_t")))

/-- The model's `wake` in the first profile: the earliest taker, when a message is ready. A
list of at most one taker. -/
def wake (takers msgs : TermSrc) : TermSrc :=
  ite (empty msgs) (none_of takers) (app "take" [takers, nat 1])

/-- The model's `acceptLoop` at a finite room. The accumulator: room, buffer, kept offers,
accepted offers, a stop flag. An offer that fits whole is accepted; the first that does not
keeps its rest, and every later one stays. -/
def accept (room msgs offers : TermSrc) : TermSrc :=
  let acc := var "a_acc"
  let o := var "a_o"
  let room' := tupleAt acc 0
  let msgs' := tupleAt acc 1
  let kept := tupleAt acc 2
  let done := tupleAt acc 3
  let rest := field o "rest"
  let k := minT room' (len rest)
  let taken := app "append" [msgs', app "take" [rest, k]]
  fold "a_acc" "a_o" none offers
    (tuple [room, msgs, none_of offers, none_of offers, bool false])
    (ite (orT (tupleAt acc 4) (app "isZero" [room']))
      (tuple [room', msgs', snoc kept o, done, bool true])
      (ite (app "eq" [len rest, k])
        (tuple [app "sub" [room', k], taken, kept, snoc done o, bool false])
        (tuple [nat 0, taken, snoc kept (recordSet o "rest" (app "drop" [rest, k])), done,
          bool true])))

/-! ## The steps, each one term of a `Ref.modify` -/

/-- The model's `take` at bounds one and one. Answer: `[message?, accepted offers, takers to
wake]`, the notifications in the model's order. It consumes when a message is there and no
earlier taker waits. Otherwise it enrols the request, or renews its hint. -/
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
    (app "pair" [tuple [app "get" [msgs, nat 0], tupleAt acc 3, wake takers1 (tupleAt acc 1)],
      consumed])
    (app "pair" [tuple [noneT, none_of offers, none_of takers], waiting])

/-- The model's `offer` under `suspend`. Answer: `[decided?, takers to wake]`. Behind a pending
offer it waits and notifies nobody. With room it is accepted. At a full buffer it waits, and
the model still wakes the earliest taker. -/
def offerStep (id hint a s : TermSrc) : TermSrc :=
  let msgs := field s "msgs"
  let offers := field s "offers"
  let takers := field s "takers"
  let pending := recordSet s "offers"
    (snoc offers (mkOffer id hint (bool false) (app "cons" [a, nilT])))
  let accepted := recordSet s "msgs" (snoc msgs a)
  ite (notT (empty offers))
    (app "pair" [tuple [noneT, none_of takers], pending])
    (ite (app "lt" [len msgs, field s "cap"])
      (app "pair" [tuple [app "some" [bool true], wake takers (snoc msgs a)], accepted])
      (app "pair" [tuple [noneT, wake takers msgs], pending]))

/-- The model's `withdrawTake`. Answer: the takers to wake. -/
def withdrawTake (id s : TermSrc) : TermSrc :=
  let takers1 := removeTaker (field s "takers") id
  app "pair" [wake takers1 (field s "msgs"), recordSet s "takers" takers1]

/-- The model's `withdrawOffer` in an opened queue. Answer: the takers to wake. An offer that
a step already accepted is not there, so only the wake remains. -/
def withdrawOffer (id s : TermSrc) : TermSrc :=
  app "pair" [wake (field s "takers") (field s "msgs"),
    recordSet s "offers" (removeOffer (field s "offers") id)]

/-- The model's `poll`. Answer: `[message?, accepted offers]`. It consumes when a message is
there and no taker waits, so it wakes no taker. -/
def pollStep (s : TermSrc) : TermSrc :=
  let msgs := field s "msgs"
  let offers := field s "offers"
  let msgs1 := app "drop" [msgs, nat 1]
  let acc := accept (app "sub" [field s "cap", len msgs1]) msgs1 offers
  let consumed := recordSet (recordSet s "msgs" (tupleAt acc 1)) "offers" (tupleAt acc 2)
  ite (andT (notT (empty msgs)) (empty (field s "takers")))
    (app "pair" [tuple [app "get" [msgs, nat 0], tupleAt acc 3], consumed])
    (app "pair" [tuple [noneT, none_of offers], s])

/-- The model's `size` in an opened queue: a read, and no step of the cell. -/
def sizeStep (s : TermSrc) : TermSrc := len (field s "msgs")

/-! ## The operations -/

def posted : Effect4.Supervision.ForkOptions := ⟨false, true, .uninterruptible⟩

/-- Post one helper for each request of a list: it resolves the request's hint with one answer
(decisions rows 238 and 240). -/
def postAll (requests answer : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len requests]
      body := fun i => selectOption "r" (app "get" [requests, i]) (succeed unit)
        (andThen
          (withFiber (Action.fork (Deferred.succeed (field (var "r") "hint") answer) posted))
          (succeed unit))
      step := fun i _ => app "succ" [i] }

/-- The pin's `onInterrupt`: `onExit` with a test of the exit. -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

/-- `take`. A step's notifications are posted in the model's order: the accepted offers'
answers, then the taker's wake. -/
def take (q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    let got ← iterateWith noneT
      { cursorTy := some (.option .nat)
        while_ := fun c => notT (app "isSome" [c])
        body := fun _ => eff do
          let hint ← Deferred.make .unit .never
          let r ← Ref.modify "s" (takeStep id hint (var "s")) q
          let _ ← postAll (tupleAt r 1) (bool true)
          let _ ← postAll (tupleAt r 2) unit
          selectOption "m" (tupleAt r 0)
            (andThen
              (onInterrupt (interruptible (Deferred.await hint))
                (eff do
                  let woken ← Ref.modify "s" (withdrawTake id (var "s")) q
                  postAll woken unit))
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
        (eff do
          let woken ← Ref.modify "s" (withdrawOffer id (var "s")) q
          postAll woken unit))
      (succeed (var "ok")))

def size (q : TermSrc) : Src NativeOp := eff do
  let s ← Ref.get q
  return sizeStep s

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

/-- R8: the order of a step's notifications (Codex's control). Capacity one; takers A and B
wait; message 1 is offered; a second offer waits at the full buffer. A's take frees room: it
accepts the second offer and leaves B ready. The model names the offerer first and B second.
Each fiber writes its mark when it goes on, so the log shows the order of the two resumptions:
A's own mark, then the offerer's `101`, then B's message. -/
def r8 : Src NativeOp := eff do
  let q ← Ref.make (state0 1)
  let log ← Ref.make (app "take" [app "cons" [nat 0, nilT], nat 0])
  let fa ← fork (eff do
    let x ← take q
    Ref.update "l" (snoc (var "l") x) log)
  let fb ← fork (eff do
    let x ← take q
    Ref.update "l" (snoc (var "l") x) log)
  let _ ← offer q (nat 1)
  let fc ← fork (eff do
    let _ ← offer q (nat 2)
    Ref.update "l" (snoc (var "l") (nat 101)) log)
  let _ ← join fa
  let _ ← join fb
  let _ ← join fc
  let l ← Ref.get log
  return l

#eval (verdict (mk r1), verdict (mk r2), verdict (mk r3), verdict (mk r4), verdict (mk r5),
  verdict (mk r6), verdict (mk r7), verdict (mk r8))
#eval (Effect4.Api.Author.build (mk r4)).toOption.map fun b =>
  toString (repr (b.ty.answer, b.ty.error))
#eval exitOf r1
#eval exitOf r2
#eval exitOf r3
#eval exitOf r4
#eval exitOf r5
#eval exitOf r6
#eval exitOf r7
#eval exitOf r8

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

/-! ## The first profile's states

A step goal quantifies over the states of the first profile, and over no other. The predicate is
closed: each first operation leaves it true (`closed`, below, on a finite universe). The model's
`within` and `tidy` are no part of it. They are the capacity claim's, and a step agrees with the
model at a state that breaks them too. -/

def distinct : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- What puts a model state outside the first profile, each fault in words. Empty for a state of
the profile. -/
def profileFaults (s : QueueContract.State) : List String :=
  (if s.phase == .opened then [] else ["the queue is not opened"]) ++
  (if s.strategy == .suspend then [] else ["the strategy is not suspend"]) ++
  (match s.capacity with
    | some (_ + 1) => []
    | _ => ["the capacity is no positive number"]) ++
  (if s.takers.all (fun t => t.min == 1 && t.max == 1) then []
    else ["a stored taker's bounds are not one and one"]) ++
  (if s.offers.all (fun o => !o.batch && o.rest.length == 1) then []
    else ["a pending offer is a batch, or holds no single message"]) ++
  (if s.peekers.isEmpty then [] else ["a peeker waits"]) ++
  (if s.awaiters.isEmpty then [] else ["an awaiter waits"]) ++
  (if distinct (QueueContract.waiting s) then [] else ["two waiting requests share an identity"])

def firstProfile (s : QueueContract.State) : Bool := (profileFaults s).isEmpty

/-! ## The steps against the model

A control evaluates one step term on the encoding of a model state, and compares its answer,
its stored value and its notifications with the model's step. Model request `n` has the
identity handle `i<n>` and a current hint `h<n>`. A step that enrols a taker, or renews its
hint, changes that request's entry of the table and no other.

A comparison has five verdicts. It refuses a state outside the profile, before and after the
step, and a request that breaks the step's premise. It refuses a reply or a signal that a
first-profile step cannot answer, and drops none. So `agrees` accounts for every signal of the
model, in order. -/

def ids : List Nat := [1, 2, 3, 100, 101, 102]
def idName (n : Nat) : String := s!"i{n}"
def hintName (n : Nat) : String := s!"h{n}"
def envNames : List String := ids.flatMap (fun n => [idName n, hintName n]) ++ ["fresh"]
def envVals : List Val :=
  ids.flatMap (fun n => [Val.promise ⟨n⟩, Val.promise ⟨1000 + n⟩]) ++ [Val.promise ⟨9999⟩]

def evalAt (src : TermSrc) : Option Val :=
  (src { names := envNames } []).toOption.bind (evalTerm envVals ·)

def natList (xs : List Nat) : TermSrc := xs.foldr (fun x acc => app "cons" [nat x, acc]) nilT
def listOf (xs : List TermSrc) : TermSrc := xs.foldr (fun x acc => app "cons" [x, acc]) nilT

/-- The table: a request's current hint. -/
abbrev Table := Nat → TermSrc
def table0 : Table := fun n => var (hintName n)
def Table.set (tb : Table) (id : Nat) (hint : TermSrc) : Table :=
  fun n => if n = id then hint else tb n

def takerTerm (tb : Table) (t : QueueContract.Taker) : TermSrc := mkTaker (var (idName t.id)) (tb t.id)
def offerTerm (o : QueueContract.Offer) : TermSrc :=
  mkOffer (var (idName o.id)) (var (hintName o.id)) (bool o.batch) (natList o.rest)
/-- The cell's value for a model state. On the first profile it loses nothing: a stored taker's
bounds, the strategy, the phase and the two empty lists are fixed there. -/
def stateTerm (tb : Table) (s : QueueContract.State) : TermSrc :=
  record stateFields [("msgs", natList s.messages),
    ("takers", listOf (s.takers.map (takerTerm tb))),
    ("offers", listOf (s.offers.map offerTerm)), ("cap", nat (s.capacity.getD 0))]

inductive Verdict
  /-- The term's whole result is the encoding of the model's. -/
  | agrees
  | differs
  /-- A term has no value. -/
  | stuck (which : String)
  /-- The model answers what a first-profile step cannot. -/
  | unencoded (why : String)
  /-- The state, the request or the next state is outside the profile. -/
  | outside (faults : List String)
  deriving DecidableEq

def Verdict.text : Verdict → String
  | .agrees => "agrees"
  | .differs => "differs"
  | .stuck which => "stuck: " ++ which
  | .unencoded why => "no encoding: " ++ why
  | .outside faults => "outside the profile: " ++ "; ".intercalate faults

instance : ToString Verdict := ⟨Verdict.text⟩

/-- The model's signals as a first-profile step answers them: the accepted offers' answers, then
the takers to wake. It refuses a signal that such a step cannot answer: an answer other than
`offered true`, an identity that names no stored request of its kind, any other note, and an
answer behind a wake. -/
def notifications (before after : QueueContract.State) (tb : Table)
    (signals : List QueueContract.Signal) : Except String (List TermSrc × List TermSrc) := do
  let isAnswer := fun (g : QueueContract.Signal) => g.note == QueueContract.Note.offered true
  let accepted ← (signals.takeWhile isAnswer).mapM fun g =>
    match before.offers.find? (·.id == g.id) with
    | some o => pure (offerTerm o)
    | none => throw s!"the answer for request {g.id} names no pending offer"
  let woken ← (signals.dropWhile isAnswer).mapM fun g =>
    match g.note, after.takers.find? (·.id == g.id) with
    | .again, some t => pure (takerTerm tb t)
    | .again, none => throw s!"the wake of request {g.id} names no stored taker"
    | _, _ => throw s!"the signal for request {g.id} is no accepted answer and no wake"
  pure (accepted, woken)

/-- One comparison, with no premise: the step term's whole result against the encoding of the
model's. -/
def judge (step : TermSrc) (expected : Except String TermSrc) : Verdict :=
  match expected with
  | .error why => .unencoded why
  | .ok e =>
    match evalAt step, evalAt e with
    | some got, some want => if got = want then .agrees else .differs
    | none, _ => .stuck "the step term"
    | _, none => .stuck "the expected term"

/-- A comparison under its premises: the state before the step and the state after it are of the
first profile, and the request keeps the step's premise. -/
def guarded (before after : QueueContract.State) (request : List String) (raw : Verdict) :
    Verdict :=
  match profileFaults before ++ request ++
      (profileFaults after).map ("after the step, " ++ ·) with
  | [] => raw
  | faults => .outside faults

/-- A take's request is fresh, or it is its own waiting taker. -/
def foreign (s : QueueContract.State) (id : Nat) : List String :=
  if (s.offers.map (·.id) ++ s.peekers ++ s.awaiters).contains id
  then ["the request's identity names a waiting request of another kind"] else []

/-- An offer's request is fresh. -/
def notFresh (s : QueueContract.State) (id : Nat) : List String :=
  if (QueueContract.waiting s).contains id then ["the request's identity is not fresh"] else []

/-- A deliberate defect of an expected result, for a red control. The reply and the stored value
stay as they are. -/
inductive Mutation
  | exact
  /-- The two notification lists change places. -/
  | swapNotifications
  /-- The takers to wake are left out. -/
  | dropWake

/-- A take of request `id` with the hint `fresh`, on the encoding of `s`: the encoding of the
model's result, the accepted offers before the takers. -/
def takeExpected (mutation : Mutation) (s : QueueContract.State) (id : Nat) :
    Except String TermSrc := do
  let r := QueueContract.take s ⟨id, 1, 1⟩
  let (reply, tb) ← (match r.2.1 with
    | .got [m] => pure (app "some" [nat m], table0)
    | .wait => pure (noneT, table0.set id (var "fresh"))
    | _ => throw "the reply is no single message and no wait" : Except String (TermSrc × Table))
  let (accepted, woken) ← notifications s r.1 tb r.2.2
  let (first, second) := match mutation with
    | .swapNotifications => (woken, accepted)
    | .dropWake => (accepted, [])
    | .exact => (accepted, woken)
  pure (app "pair" [tuple [reply, listOf first, listOf second], stateTerm tb r.1])

def takeRaw (mutation : Mutation) (s : QueueContract.State) (id : Nat) : Verdict :=
  judge (takeStep (var (idName id)) (var "fresh") (stateTerm table0 s)) (takeExpected mutation s id)

def takeAgrees (s : QueueContract.State) (id : Nat) : Verdict :=
  guarded s (QueueContract.take s ⟨id, 1, 1⟩).1 (foreign s id) (takeRaw .exact s id)

/-- The takers that a step with no accepted offer wakes. -/
def wakesOnly (before after : QueueContract.State) (signals : List QueueContract.Signal) :
    Except String (List TermSrc) := do
  let (accepted, woken) ← notifications before after table0 signals
  unless accepted.isEmpty do throw "this step answers no accepted offer"
  pure woken

/-- An offer of `a` by request `id`, on the encoding of `s`. -/
def offerExpected (mutation : Mutation) (s : QueueContract.State) (id a : Nat) :
    Except String TermSrc := do
  let r := QueueContract.offer s id a
  let reply := match r.2.1 with
    | .accepted ok => app "some" [bool ok]
    | .wait => noneT
  let woken ← wakesOnly s r.1 r.2.2
  let woken := match mutation with
    | .dropWake => []
    | _ => woken
  pure (app "pair" [tuple [reply, listOf woken], stateTerm table0 r.1])

def offerRaw (mutation : Mutation) (s : QueueContract.State) (id a : Nat) : Verdict :=
  judge (offerStep (var (idName id)) (var (hintName id)) (nat a) (stateTerm table0 s))
    (offerExpected mutation s id a)

def offerAgrees (s : QueueContract.State) (id a : Nat) : Verdict :=
  guarded s (QueueContract.offer s id a).1 (notFresh s id) (offerRaw .exact s id a)

def pollAgrees (s : QueueContract.State) : Verdict :=
  let r := QueueContract.poll s
  guarded s r.1 [] (judge (pollStep (stateTerm table0 s)) (do
    let (accepted, woken) ← notifications s r.1 table0 r.2.2
    unless woken.isEmpty do throw "a poll wakes no taker"
    let reply := match r.2.1 with
      | some m => app "some" [nat m]
      | none => noneT
    pure (app "pair" [tuple [reply, listOf accepted], stateTerm table0 r.1])))

def sizeAgrees (s : QueueContract.State) : Verdict :=
  guarded s s [] (judge (sizeStep (stateTerm table0 s)) (pure (nat (QueueContract.size s))))

def withdrawTakeAgrees (s : QueueContract.State) (id : Nat) : Verdict :=
  let r := QueueContract.withdrawTake s id
  guarded s r.1 [] (judge (withdrawTake (var (idName id)) (stateTerm table0 s)) (do
    let woken ← wakesOnly s r.1 r.2
    pure (app "pair" [listOf woken, stateTerm table0 r.1])))

def withdrawOfferAgrees (s : QueueContract.State) (id : Nat) : Verdict :=
  let r := QueueContract.withdrawOffer s id
  guarded s r.1 [] (judge (withdrawOffer (var (idName id)) (stateTerm table0 s)) (do
    let woken ← wakesOnly s r.1 r.2
    pure (app "pair" [listOf woken, stateTerm table0 r.1])))

def T (n : Nat) : QueueContract.Taker := ⟨n, 1, 1⟩

/-- Codex's prefix, before its last step: capacity one, takers 1 and 2, message 1 buffered,
the offer of message 2 by request 101 pending. -/
def mixed : QueueContract.State :=
  { capacity := some 1, messages := [1], takers := [T 1, T 2], offers := [⟨101, false, [2]⟩] }

/-- `mixed` before its second offer: the buffer is full, and no offer is pending. -/
def full : QueueContract.State := { mixed with offers := [] }

-- The model's last step: message 1, then the offerer's answer before taker 2's wake.
#eval toString (repr (QueueContract.take mixed (T 1)).2)
-- C1. The mixed notifications: the term agrees, in the model's order.
#eval takeAgrees mixed 1
-- C2. The first offer at a full buffer waits, and the model wakes the earliest taker again.
#eval toString (repr (QueueContract.offer full 101 2).2)
#eval offerAgrees full 101 2
-- C2b. An offer behind a pending offer waits and notifies nobody.
#eval toString (repr (QueueContract.offer mixed 102 3).2)
#eval offerAgrees mixed 102 3
-- C3. A taker that waits already, and no message: the model's state is unchanged, and the
-- term renews that request's hint and no other entry.
#eval toString (repr (QueueContract.take { capacity := some 1, takers := [T 1, T 2] } (T 1)).2)
#eval takeAgrees { capacity := some 1, takers := [T 1, T 2] } 1
-- C4. A new taker enrols behind a waiting one; and an offer into room wakes the earliest.
#eval takeAgrees { capacity := some 1, takers := [T 1] } 2
#eval offerAgrees { capacity := some 2, takers := [T 1] } 100 7
-- C5. The withdrawals: the earliest taker leaves and the next is woken; a pending offer leaves.
#eval toString (repr (QueueContract.withdrawTake mixed 1).2)
#eval withdrawTakeAgrees mixed 1
#eval withdrawOfferAgrees mixed 101
-- C6. A poll that frees room accepts the pending offer; the size is the buffer's length.
#eval toString (repr (QueueContract.poll { mixed with takers := [] }).2)
#eval pollAgrees { mixed with takers := [] }
#eval sizeAgrees mixed

/-! ### Outside the profile: the comparison refuses

Codex's witness is C4's state with one peeker. The model wakes taker 1 and then peeker 2. The
cell has no place for a peeker, so the comparison must not go on. -/

def peeked : QueueContract.State := { capacity := some 2, takers := [T 1], peekers := [2] }
/-- A stored taker with the bounds two and two: one message does not make it ready. -/
def twoTwo : QueueContract.State := { capacity := some 2, takers := [⟨1, 2, 2⟩] }

-- P1. The model's signals at the peeker's state: taker 1, then peeker 2.
#eval toString (repr (QueueContract.offer peeked 100 7).2)
-- The comparison refuses the state. With no premise, the encoder refuses the peeker's signal.
#eval offerAgrees peeked 100 7
#eval offerRaw .exact peeked 100 7
-- P2. The model wakes nobody for the two-and-two taker. The comparison refuses the state. With
-- no premise it differs: the step's wake does not read a stored taker's bounds.
#eval toString (repr (QueueContract.offer twoTwo 100 7).2)
#eval offerAgrees twoTwo 100 7
#eval offerRaw .exact twoTwo 100 7
-- P3. A request that breaks a step's premise: an offer by a request that waits already.
#eval offerAgrees mixed 101 9

/-! ### Red controls: one notification changed, and nothing else

Each mutant keeps the shape, the reply and the stored value of a passing control. -/

-- M1. C1's expected result with its two notification lists exchanged.
#eval takeRaw .swapNotifications mixed 1
-- M2. C2's expected result with its wake left out.
#eval offerRaw .dropWake full 101 2
-- M3. C1's expected result with its wake left out.
#eval takeRaw .dropWake mixed 1

/-! ### Every state of a finite universe of the profile

The universe: capacity one or two; a buffer of zero to three messages; the takers 1 and 2 in
each order; the pending offers 100 and 101 in each order. A buffer may be longer than the
capacity, and an offer may be pending beside free room: the profile does not ask for `within`
or `tidy`. Each move's request keeps its step's premise. -/

inductive Move
  | take (id : Nat) | offer (id a : Nat) | poll | size | dropTake (id : Nat) | dropOffer (id : Nat)
  deriving Repr

def moves : List Move :=
  [.take 1, .take 2, .take 3, .offer 102 30, .poll, .size, .dropTake 1, .dropTake 2, .dropTake 3,
   .dropOffer 100, .dropOffer 101, .dropOffer 102]

def Move.verdict (s : QueueContract.State) : Move → Verdict
  | .take id => takeAgrees s id
  | .offer id a => offerAgrees s id a
  | .poll => pollAgrees s
  | .size => sizeAgrees s
  | .dropTake id => withdrawTakeAgrees s id
  | .dropOffer id => withdrawOfferAgrees s id

def Move.next (s : QueueContract.State) : Move → QueueContract.State
  | .take id => (QueueContract.take s ⟨id, 1, 1⟩).1
  | .offer id a => (QueueContract.offer s id a).1
  | .poll => (QueueContract.poll s).1
  | .size => s
  | .dropTake id => (QueueContract.withdrawTake s id).1
  | .dropOffer id => (QueueContract.withdrawOffer s id).1

def orders {α : Type} (a b : α) : List (List α) := [[], [a], [b], [a, b], [b, a]]

def profileStates : List QueueContract.State :=
  [1, 2].flatMap fun cap =>
  ([[], [7], [7, 8], [7, 8, 9]] : List (List Nat)).flatMap fun messages =>
  (orders (T 1) (T 2)).flatMap fun takers =>
  (orders (⟨100, false, [20]⟩ : QueueContract.Offer) ⟨101, false, [21]⟩).map fun offers =>
    ({ capacity := some cap, messages := messages, takers := takers, offers := offers } :
      QueueContract.State)

/-- Every state of the universe is of the profile, and each move leaves the profile true. -/
def closed : Bool :=
  profileStates.all fun s => firstProfile s && moves.all fun m => firstProfile (m.next s)

/-- Each state and move whose verdict is not `agrees`. -/
def disagreements : List (String × String) :=
  profileStates.flatMap fun s => moves.filterMap fun m =>
    let v := m.verdict s
    if v = .agrees then none else some (toString (repr s) ++ " / " ++ toString (repr m), v.text)

-- The states, the comparisons, whether the profile is closed on them, and the disagreements.
#eval (profileStates.length, profileStates.length * moves.length, closed)
#eval (disagreements.length, disagreements.take 3)

/-- A deliberate defect of a step, for a red control of the whole comparison: the first draft's
offer, which notifies nobody when it waits at a full buffer. -/
def offerStepSilent (id hint a s : TermSrc) : TermSrc :=
  let msgs := field s "msgs"
  let offers := field s "offers"
  let takers := field s "takers"
  let pending := recordSet s "offers"
    (snoc offers (mkOffer id hint (bool false) (app "cons" [a, nilT])))
  ite (orT (notT (empty offers)) (notT (app "lt" [len msgs, field s "cap"])))
    (app "pair" [tuple [noneT, none_of takers], pending])
    (app "pair" [tuple [app "some" [bool true], wake takers (snoc msgs a)],
      recordSet s "msgs" (snoc msgs a)])

-- M4. The comparison over every state finds the silent offer: it differs exactly where the
-- buffer is full, no offer is pending, and a taker waits behind a message. Twenty states.
#eval (profileStates.filter fun s =>
  judge (offerStepSilent (var (idName 102)) (var (hintName 102)) (nat 30) (stateTerm table0 s))
    (offerExpected .exact s 102 30) != .agrees).length
#eval (profileStates.filter fun s =>
  decide (s.offers = []) && decide (s.capacity.getD 0 ≤ s.messages.length) &&
    !s.takers.isEmpty && !s.messages.isEmpty).length

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
#eval (stepTerm (pollStep (var "s"))).map fun t => (termSize t, foldCount t)
-- No step states an accumulator's type, so each is inside the reader's domain.
#eval ((stepTerm (takeStep (var "id") (var "hint") (var "s"))).map (·.unannotated),
  (stepTerm (offerStep (var "id") (var "hint") (nat 1) (var "s"))).map (·.unannotated),
  (stepTerm (withdrawTake (var "id") (var "s"))).map (·.unannotated),
  (stepTerm (withdrawOffer (var "id") (var "s"))).map (·.unannotated),
  (stepTerm (pollStep (var "s"))).map (·.unannotated),
  (stepTerm (sizeStep (var "s"))).map (·.unannotated))

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
