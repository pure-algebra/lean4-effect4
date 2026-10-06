import Test.Dogfood.P4RateLimiter
import Test.Dogfood.Scenario.Timeout
import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Folds
import Effect4.Codegen.ListFold
import Effect4.Laws.Codegen.Read
import Effect4.Laws.Codegen.PrintReadable
import TypeScript.Render

/-!
# Term rows: an operation's binder term as a printed function (the state plan's T5)

A read-modify-write row carries a binder term (decisions row 43). Since the state plan's T5 the
faces print the term as a function of the cell's current value, after the row's call, and read
it back (`printPerform`, `Codegen/PrintLeaf.lean`; `readPerform`, `Codegen/Read.lean`). This
battery is the slice's acceptance for printing (decisions row 251):

1. the forty terms that printed as five names before, each with its text and its round trip;
2. the Queue probe's programs `s9`, `s11` and `s12`
   (`docs/research/2026-10-05-claude-lead/queue-readiness/QueueSkeleton.lean`) and the program
   `r4` of the Queue's real steps (`QueueSteps.lean`, beside it): each step's `Ref.modify` prints
   and reads back, and each program's module is pinned at what the faces answer today;
3. a class construction that only an operation's term holds: the module declares its class
   with the construction's own fields, through `ScopedOp.term?`;
4. the texts that the truth lane's compiler control copies
   (`harness/truth/term-rows.typecheck.ts`), each pinned in full, and the Lean half of two
   programs that the truth lane runs or holds out.

Part B of the slice adds the operation's type arguments (the coordinator's addenda 6 and 7):

5. `Deferred.make<A, E>()` at its instances: the type arguments are derived from the operation,
   printed through the type printer and read back by the checked type reader, on the readable
   types (`Classes.ReadableTy`, `Test/Codegen/TypeReader.lean`);
6. an operation's types as program annotations (decisions row 212): raw formation, the integer
   scan and the module's class table reach them;
7. a fixture alphabet whose one operation carries a binder term and a type argument: the two
   updates of a reader are independent for any lawful signature (`LawfulTypeArgs`);
8. a loop's stated cursor type, read back by the same checked type reader. With it the Queue's
   programs read back as modules, `r4` among them, in Lean and in `ts/eff/read.ts`
   (`ts/eff/test/term-rows.test.ts` reads the module that this battery pins by its digest).

Every guard is a finite check on one program. None states target typing or a host run: the
TypeScript reader's twin is `ts/eff/test/term-rows.test.ts`, and the truth lane runs printed
modules on the pin. The rendered bytes stay inside each guard: a battery `def` over rendered
text reaches `Classical.choice` (AGENTS.md, Trust).
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Codegen.TermRows

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open TypeScript (house0 Expr)
open TypeScript.Render (expr)

/-! ## 1. The forty terms that five names spelled -/

/-- The printed body of each name's image at each shape, over the current value `a`: what the
function's body reads after `(a) => `. Five names at four shapes; a row prints the body of its
shape. Before T5 a row printed the name (`Ref.update(a0, incr)`), and one name stood for a
different function at each shape. -/
def bodies (a : String) : FnShape → FnName → String
  | .update, .incr => s!"succ({a})"
  | .update, .double => s!"mul({a}, 2)"
  | .update, .zeroWhenPositive => s!"add({a}, 0)"
  | .update, .noChange => a
  | .update, .takeAndBump => s!"add({a}, 1)"
  | .updateSome, .incr => s!"some(succ({a}))"
  | .updateSome, .double => s!"some(mul({a}, 2))"
  | .updateSome, .zeroWhenPositive => s!"ite(lt(0, {a}), some(0), none())"
  | .updateSome, .noChange => "none()"
  | .updateSome, .takeAndBump => s!"some(add({a}, 1))"
  | .modify, .incr => s!"pair({a}, succ({a}))"
  | .modify, .double => s!"pair({a}, mul({a}, 2))"
  | .modify, .zeroWhenPositive => s!"pair({a}, add({a}, 0))"
  | .modify, .noChange => s!"pair({a}, {a})"
  | .modify, .takeAndBump => s!"pair({a}, add({a}, 1))"
  | .modifySome, .incr => s!"pair({a}, some(succ({a})))"
  | .modifySome, .double => s!"pair({a}, some(mul({a}, 2)))"
  | .modifySome, .zeroWhenPositive => s!"pair({a}, some({a}))"
  | .modifySome, .noChange => s!"pair({a}, none())"
  | .modifySome, .takeAndBump => s!"pair({a}, some(add({a}, 1)))"

-- each of the forty images prints as the function of its own term, at levels 0 to 3: the
-- parameter is the binder of the node's level
#guard (List.range 4).all fun n => NativeOp.termRows.all fun row => fnNames.all fun g =>
  decide ((print nativeSignature n
      (.perform (row.1 (FnName.image row.2 n g)) (.lit (.nat 0)))).map (expr house0 0)
    = .ok ((NativeOp.row (row.1 (.lit .unit))).spelling ++ "(0, (a" ++ toString n ++ ") => " ++
        bodies ("a" ++ toString n) row.2 g ++ ")"))
-- and reads back as itself
#guard (List.range 4).all fun n => NativeOp.termRows.all fun row => fnNames.all fun g =>
  let p : Eff NativeOp := .perform (row.1 (FnName.image row.2 n g)) (.lit (.nat 0))
  readable nativeSignature nativeSpell n p &&
    decide (roundTrip nativeSignature nativeSpell n p = .ok p)
-- no two of a shape's five bodies are one text: one term has one printed form
#guard [FnShape.update, .updateSome, .modify, .modifySome].all fun s =>
  (fnNames.map (bodies "a" s)).eraseDups.length == fnNames.length
-- one text in full
#guard (print nativeSignature 1
    (.perform (.refModifySomeWith (FnName.image .modifySome 1 .takeAndBump)) (.var 0))).map
      (expr house0 0)
  = .ok "Ref.modifySome(a0, (a1) => pair(a1, some(add(a1, 1))))"
-- red control: the function's parameter is the node's level, so the text of another level is
-- another program's, and it does not read back at this level
#guard (readEff [] nativeSignature nativeSpell 1
    (.call (.ident "Ref.update") [.ident "a0",
      .lambda [{ name := "a2" }] (.call (.ident "succ") [.ident "a2"])])).isOk = false

/-! ## 2. The Queue probe's programs

The definitions are the probe's, copied: `Skeleton` from `QueueSkeleton.lean` (two lists and two
indexes, before the fold) and `Steps` from `QueueSteps.lean` (the real steps, whose terms fold).
Each step is one `Ref.modify` whose term reads a record that holds lists of `Deferred` handles. -/

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def verdict (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

/-- The module printer's answer on a source, by name. -/
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

/-- Whether the printed module of a source reads back to the built program. -/
def readsBack (src : Src NativeOp) : Bool :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => false
  | .ok b =>
    match Effect4.Api.printModule "main" b.program b.table with
    | some m => decide (Effect4.Api.readModule m b.table = .ok b.program)
    | none => false

/-- The root exit of a source's run, after three flushes of the posted helpers. -/
def exitOf (src : Src NativeOp) (fuel : Nat := 4000) : Option ExitV :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => none
  | .ok b =>
    ((List.range 3).foldl (fun (s : Run) _ => s.control Effect4.Api.flush)
      (Run.runPure b "q" { fuel := fuel, compileFuel := fuel })).exit

/-- A row's node elaborated under bound names, at the level they give: the program a step's
`Ref.modify` is where it stands. -/
def nodeAt (names : List String) (src : Src NativeOp) : Option (Eff NativeOp) :=
  (src { names := names } []).toOption

/-- A node prints, and reads back as itself, at a level. -/
def roundTrips (level : Nat) (node : Option (Eff NativeOp)) : Bool :=
  match node with
  | some p => readable nativeSignature nativeSpell level p &&
      decide (roundTrip nativeSignature nativeSpell level p = .ok p)
  | none => false

namespace Skeleton

/-- A hint: a Deferred that carries nothing and cannot fail. -/
def hintTy : Ty := .deferredOf .unit .never

def stateFields : List (String × Bool × Ty) :=
  [("msgs", false, .list .nat), ("mHead", false, .nat),
   ("takers", false, .list hintTy), ("tHead", false, .nat), ("withdrawn", false, .nat)]

def state0 : TermSrc :=
  record stateFields [("msgs", app "nil" []), ("mHead", nat 0), ("takers", app "nil" []),
    ("tHead", nat 0), ("withdrawn", nat 0)]

def len (xs : TermSrc) : TermSrc := app "length" [xs]
def snoc (xs x : TermSrc) : TermSrc := app "append" [xs, app "cons" [x, app "nil" []]]
def ready (s : TermSrc) : TermSrc := app "lt" [field s "mHead", len (field s "msgs")]
def waiting (s : TermSrc) : TermSrc := app "lt" [field s "tHead", len (field s "takers")]

/-- The hint to signal: the earliest waiting taker's, when a message is ready. -/
def wake (s : TermSrc) : TermSrc :=
  app "ite" [ready s, app "get" [field s "takers", field s "tHead"], app "none" []]

/-- An offer into an unbounded buffer. Answer: the signal. -/
def offerStep (a s : TermSrc) : TermSrc :=
  let s' := recordSet s "msgs" (snoc (field s "msgs") a)
  app "pair" [wake s', s']

/-- A taker's first attempt. Answer: `[message?, position, signal?]`. -/
def tryTake (hint s : TermSrc) : TermSrc :=
  let consumed := recordSet s "mHead" (app "succ" [field s "mHead"])
  let enrolled := recordSet s "takers" (snoc (field s "takers") hint)
  app "ite" [app "and" [ready s, app "not" [waiting s]],
    app "pair" [tuple [app "get" [field s "msgs", field s "mHead"], nat 0, wake consumed], consumed],
    app "pair" [tuple [app "none" [], len (field s "takers"), app "none" []], enrolled]]

/-- A waiting taker's later attempt, at its position. Answer: `[message?, signal?]`. -/
def retryTake (p s : TermSrc) : TermSrc :=
  let consumed := recordSet (recordSet s "mHead" (app "succ" [field s "mHead"]))
    "tHead" (app "succ" [field s "tHead"])
  app "ite" [app "and" [ready s, app "eq" [field s "tHead", p]],
    app "pair" [tuple [app "get" [field s "msgs", field s "mHead"], wake consumed], consumed],
    app "pair" [tuple [app "none" [], app "none" []], s]]

/-- The earliest taker leaves. Answer: the signal that passes on. -/
def withdraw (p s : TermSrc) : TermSrc :=
  let counted := recordSet s "withdrawn" (app "succ" [field s "withdrawn"])
  let left := recordSet counted "tHead" (app "succ" [field s "tHead"])
  app "ite" [app "eq" [field s "tHead", p],
    app "pair" [wake left, left],
    app "pair" [app "none" [], counted]]

/-- Decisions row 238: a detached fork with a deferred start, uninterruptible. -/
def posted : Effect4.Supervision.ForkOptions := ⟨false, true, .uninterruptible⟩

/-- Post one signal: the helper resolves the hint. -/
def post (signal : TermSrc) : Src NativeOp :=
  selectOption "h" signal (succeed unit)
    (andThen (withFiber (Action.fork (Deferred.succeed (var "h") unit) posted)) (succeed unit))

def offer (q a : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let signal ← Ref.modify "s" (offerStep a (var "s")) q
    let _ ← post signal
    return bool true)

/-- The cleanup of a wait, as the pin defines `onInterrupt`: `onExit` with a test of the exit. -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

/-- `take` as a loop that ends with the message: the cursor is the message, absent at first. -/
def takeLoop (q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let hint ← Deferred.make .unit .never
    let r ← Ref.modify "s" (tryTake hint (var "s")) q
    let _ ← post (tupleAt r 2)
    let got ← iterateWith (tupleAt r 0)
      { cursorTy := some (.option .nat)
        while_ := fun c => app "not" [app "isSome" [c]]
        body := fun _ => eff do
          let _ ← onInterrupt (interruptible (Deferred.await hint))
            (eff do
              let signal ← Ref.modify "s" (withdraw (tupleAt r 1) (var "s")) q
              post signal)
          let r2 ← Ref.modify "s" (retryTake (tupleAt r 1) (var "s")) q
          let _ ← post (tupleAt r2 1)
          return tupleAt r2 0
        step := fun _ a => a }
    selectOption "m" got (failCause (Cause.die (str "queue: the loop ended without a message")))
      (succeed (var "m")))

/-- S9: two takers in order, two offers. -/
def s9 : Src NativeOp := eff do
  let q ← Ref.make state0
  let fa ← fork (takeLoop q)
  let fb ← fork (takeLoop q)
  let _ ← offer q (nat 1)
  let _ ← offer q (nat 2)
  let a ← join fa
  let b ← join fb
  return tuple [a, b]

/-- S11: after a withdrawal a later offer stays and a take gets it. -/
def s11 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (takeLoop q)
  let _ ← withFiber (Action.interrupt f)
  let _ ← offer q (nat 5)
  let a ← takeLoop q
  let s ← Ref.get q
  return tuple [a, field s "withdrawn", field s "tHead"]

/-- S12: the cleanup does not run when the wait succeeds: one taker, one offer, no withdrawal. -/
def s12 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (takeLoop q)
  let _ ← offer q (nat 3)
  let a ← join f
  let s ← Ref.get q
  return tuple [a, field s "withdrawn"]

end Skeleton

-- The three programs build, and the machine answers what the probe recorded
-- (`QueueSkeleton.out`): each is one schedule on the Lean machine.
#guard [Skeleton.s9, Skeleton.s11, Skeleton.s12].map (verdict ∘ mk) = ["built", "built", "built"]
#guard exitOf Skeleton.s9 = some (.success (.list [.nat 1, .nat 2]))
#guard exitOf Skeleton.s11 = some (.success (.list [.nat 5, .nat 1, .nat 1]))
#guard exitOf Skeleton.s12 = some (.success (.list [.nat 3, .nat 0]))

-- Each step's `Ref.modify` prints and reads back where it stands: the queue's cell, the bound
-- values its term captures, and the cell's current value one level up. The steps are `offer`'s,
-- the taker's first attempt, its later attempt and its withdrawal.
#guard roundTrips 2 (nodeAt ["q", "a"]
  (Ref.modify "s" (Skeleton.offerStep (var "a") (var "s")) (var "q")))
#guard roundTrips 2 (nodeAt ["q", "hint"]
  (Ref.modify "s" (Skeleton.tryTake (var "hint") (var "s")) (var "q")))
#guard roundTrips 2 (nodeAt ["q", "r"]
  (Ref.modify "s" (Skeleton.retryTake (tupleAt (var "r") 1) (var "s")) (var "q")))
#guard roundTrips 2 (nodeAt ["q", "r"]
  (Ref.modify "s" (Skeleton.withdraw (tupleAt (var "r") 1) (var "s")) (var "q")))
-- The offer's step in full: the term reads the record through its generic accessors, captures
-- the message `a1`, and binds the cell's value as `a2`.
#guard ((nodeAt ["q", "a"] (Ref.modify "s" (Skeleton.offerStep (var "a") (var "s")) (var "q"))).bind
    fun p => (print nativeSignature 2 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a2) => pair(ite(lt(recordRequired<\"mHead\">(\"mHead\")(recordSet<\"msgs\">(\"msgs\")(a2)(append(recordRequired<\"msgs\">(\"msgs\")(a2), cons(a1, nil())))), length(recordRequired<\"msgs\">(\"msgs\")(recordSet<\"msgs\">(\"msgs\")(a2)(append(recordRequired<\"msgs\">(\"msgs\")(a2), cons(a1, nil())))))), get(recordRequired<\"takers\">(\"takers\")(recordSet<\"msgs\">(\"msgs\")(a2)(append(recordRequired<\"msgs\">(\"msgs\")(a2), cons(a1, nil())))), recordRequired<\"tHead\">(\"tHead\")(recordSet<\"msgs\">(\"msgs\")(a2)(append(recordRequired<\"msgs\">(\"msgs\")(a2), cons(a1, nil()))))), none()), recordSet<\"msgs\">(\"msgs\")(a2)(append(recordRequired<\"msgs\">(\"msgs\")(a2), cons(a1, nil())))))"

namespace Steps

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

end Steps

-- `r4` builds, and the machine answers what the probe recorded (`QueueSteps.out`).
#guard verdict (mk Steps.r4) = "built"
#guard exitOf Steps.r4 20000 =
  some (.success (.list [.bool true, .nat 1, .bool true, .nat 2]))

-- Each of the four steps prints and reads back where it stands. The take step's term is the
-- large one: the term language has no local binding, so the accept pass and the removal occur
-- several times in it.
#guard roundTrips 3 (nodeAt ["q", "id", "hint"]
  (Ref.modify "s" (Steps.takeStep (var "id") (var "hint") (var "s")) (var "q")))
#guard roundTrips 4 (nodeAt ["q", "a", "id", "hint"]
  (Ref.modify "s" (Steps.offerStep (var "id") (var "hint") (var "a") (var "s")) (var "q")))
#guard roundTrips 2 (nodeAt ["q", "id"]
  (Ref.modify "s" (Steps.withdrawTake (var "id") (var "s")) (var "q")))
#guard roundTrips 2 (nodeAt ["q", "id"]
  (Ref.modify "s" (Steps.withdrawOffer (var "id") (var "s")) (var "q")))
-- A fold inside a step's term binds the two levels above the cell's value: the withdrawal's
-- removal reads the cell as `a2` and folds with `a3` and `a4`. The removal stands three times in
-- the term: twice in the wake, and once as the new list of takers.
#guard ((nodeAt ["q", "id"] (Ref.modify "s" (Steps.withdrawTake (var "id") (var "s")) (var "q"))).bind
    fun p => (print nativeSignature 2 p).toOption.map (expr house0 0)).any fun text =>
  (text.splitOn "Ref.modify(a0, (a2) => pair(").length == 2 &&
    (text.splitOn "(a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))").length == 4

/-! ### The programs' modules

Each program makes a `Deferred` at a type other than `Deferred<number, number>`, and its take
loop states its cursor's type. Until part B of the slice the faces spelled `Deferred.make`'s type
arguments at one instance (decisions row 212), so the module printer refused each program by
name, `typeSpelling Deferred.make`. Since part B the faces derive the type arguments from the
operation and print each through the type printer, so each program prints as a module. -/

#guard [Skeleton.s9, Skeleton.s11, Skeleton.s12, Steps.r4].map printVerdict =
  ["printed", "printed", "printed", "printed"]
-- Each module's text, by its length in characters and the SHA-256 of its bytes. `r4`'s text is
-- the fixture `ts/eff/test/fixtures/queue-r4.module.txt`, which the TypeScript reader's test
-- holds to the same digest.
#guard [Skeleton.s9, Skeleton.s11, Skeleton.s12, Steps.r4].map (fun src =>
    (Effect4.Api.Author.build (mk src)).toOption.bind fun b =>
      (Effect4.Api.printModule "main" b.program b.table).map fun m =>
        let text := TypeScript.Render.module house0 m
        (text.length, (Effect4.Store.sha256 text.toUTF8.data.toList).hex)) =
  [ some (12813, "6ef5d1607fedcee6e42312168634c052b48ad2342a4cf77628b5d103a4aed9da")
  , some (11855, "b420a593926466ba5b0e1693970a780a04e920d8f2a39dd90f8880c3e4f56d32")
  , some (6858, "03b96e441e7c359bc7b91969d9fad79ca46c4110dc3ea5eb0362c728245ee5d6")
  , some (33585, "a337704b7826539b3a7837475f97f030e000a929aa1e8ed57a97da3ea9cac5b7") ]
-- What `r4`'s text holds: six hints of nothing and two that carry the answer, each with its
-- type arguments, the two take loops' stated cursor type, and no bare `Deferred.make()`.
#guard ((Effect4.Api.Author.build (mk Steps.r4)).toOption.bind fun b =>
    (Effect4.Api.printModule "main" b.program b.table).map
      (TypeScript.Render.module house0)).any fun text =>
  (text.splitOn "Deferred.make<void, never>()").length == 7 &&
    (text.splitOn "Deferred.make<boolean, never>()").length == 3 &&
    (text.splitOn "Option.Option<number> = none()").length == 3 &&
    (text.splitOn "Deferred.make()").length == 1
-- Each module reads back to its program. Each take loop states its cursor's type, which the
-- reader reads by the checked type reader (section 8). Before that step the reader refused each
-- module at the loop's `let`, by name (`ReadRefusal.annotation "local const"`).
#guard [Skeleton.s9, Skeleton.s11, Skeleton.s12, Steps.r4].map readsBack =
  [true, true, true, true]
-- Each program's canonical bytes, by their SHA-256. A reader that reads the printed module to
-- these bytes read the program back: the TypeScript reader's test holds its reading of `r4`'s
-- module to the fourth digest.
#guard [Skeleton.s9, Skeleton.s11, Skeleton.s12, Steps.r4].map (fun src =>
    (Effect4.Api.Author.build (mk src)).toOption.map fun b =>
      (Effect4.Store.sha256 (Effect4.Api.bytesOf b.program)).hex) =
  [ some "c7f5906b1d9248b4302203d7e5d9a67ed1fd1789551e95314af3ce6e0c6e2b09"
  , some "c518eff3441c3c2074143e217e7af27a80d4930be2aab17b205964053d0d19a3"
  , some "4f22c0bb71884dec589c09fa11b5a0bf43e7e18ec8ceeea6b5288d3e11e31c23"
  , some "5b21ec39fb424b507cc7f21478f46431911da74e7dd92c46fa214e50afcdb53d" ]
-- Green control: a step alone, over a cell of the Queue's first state and no `Deferred`, prints
-- as a module and reads back.
#guard printVerdict (bindName "q" (Ref.make Skeleton.state0) fun q =>
    Ref.modify "s" (Skeleton.offerStep (nat 1) (var "s")) q) = "printed"
#guard readsBack (bindName "q" (Ref.make Skeleton.state0) fun q =>
    Ref.modify "s" (Skeleton.offerStep (nat 1) (var "s")) q)

/-! ## 3. A class construction that only an operation's term holds

The term of a `Ref.modify` builds a tagged record, and nothing else in the program does. The
module declares the record's class with the construction's own fields, in their written order
(`needed` before `available`), because the record collector reads an operation's term through
the alphabet's view (`argumentRecords`, `ScopedOp.term?`). -/

def shortFields : List (String × Bool × Ty) :=
  [("_tag", false, .lit "Short"), ("needed", false, .nat), ("available", false, .nat)]

def short (needed available : TermSrc) : TermSrc :=
  record shortFields [("_tag", str "Short"), ("needed", needed), ("available", available)]

/-- A number cell whose `Ref.modify` answers a `Short` record built from the cell's value. -/
def shortModule : Src NativeOp :=
  bindName "c" (Ref.make (nat 0)) fun c =>
    Ref.modify "s" (app "pair" [short (var "s") (nat 1), var "s"]) c

#guard verdict (mk shortModule) = "built"
#guard printVerdict shortModule = "printed"
#guard readsBack shortModule
-- the program's classes hold the construction, with its declared fields
#guard ((Effect4.Api.Author.build (mk shortModule)).toOption.map fun b =>
    classesOf b.program) = some [("Short", shortFields)]
-- and the expression round trip, which reads under those classes, gives the program back
#guard ((Effect4.Api.Author.build (mk shortModule)).toOption.map fun b =>
    decide (Effect4.Api.roundTrip b.program = .ok b.program)) = some true
-- the module's text: the class, then the program, whose term constructs it with `new`
#guard ((Effect4.Api.Author.build (mk shortModule)).toOption.bind fun b =>
    (Effect4.Api.printModule "main" b.program b.table).map
      (TypeScript.Render.module house0)).any fun text =>
  (text.splitOn "export class Short extends Data.TaggedError(\"Short\")<{ readonly needed: number; readonly available: number }> {}").length == 2 &&
    (text.splitOn "Ref.modify(a0, (a1) => pair(new Short({ needed: a1, available: 1 }), a1))").length == 2

/-- An alphabet that shows the collector no term: the native operations with the class's default
reading view. Scope and the term map are the native ones. -/
structure Blind where
  op : NativeOp

instance : ScopedOp Blind where
  scopedAt blind level := ScopedOp.scopedAt blind.op level
  mapTerm g blind := ⟨ScopedOp.mapTerm g blind.op⟩

/-- The construction inside an operation's term, as the native operation holds it. -/
def shortOp : NativeOp :=
  .refModifyWith (.app "pair" (.cons
    (.record shortFields ["_tag", "needed", "available"]
      (.cons (.lit (.str "Short")) (.cons (.var 1) (.cons (.lit (.nat 1)) .nil))))
    (.cons (.var 1) .nil)))

-- Red control of the collector: where the alphabet shows no term, the program names no class,
-- as at every alphabet before the collector read `ScopedOp.term?`. The native alphabet shows
-- the term, and the same construction is found.
#guard classesOf (Op := Blind) (.perform ⟨shortOp⟩ (.var 0)) = []
#guard classesOf (Op := NativeOp) (.perform shortOp (.var 0)) = [("Short", shortFields)]

/-! ## 4. The texts the compiler control copies

`harness/truth/term-rows.typecheck.ts` type-checks printed steps under tsgo 7, at the cell's
printed type. It copies the five texts below, so each is pinned here in full: a change of the
printer moves this file and that one together. Each type-checks there. Until the literal rule
of decisions row 256 the last three were that file's red lines: on the target, `pair` and
`tuple` kept a Boolean or a number literal as a literal type, where Lean types `bool` and
`nat`, so two arms that Lean types alike were two target types. The two helpers now widen a
number or a Boolean in an immediate slot, as `litArgTy` types them, and keep a string literal's
type (`harness/truth/literals.typecheck.ts` holds the rule's controls). -/

-- the probe's offer step is pinned in section 2; the model's `withdrawTake`:
#guard ((nodeAt ["q", "id"] (Ref.modify "s" (Steps.withdrawTake (var "id") (var "s")) (var "q"))).bind
    fun p => (print nativeSignature 2 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a2) => pair(ite(isZero(length(recordRequired<\"msgs\">(\"msgs\")(a2))), take(fold(recordRequired<\"takers\">(\"takers\")(a2), take(recordRequired<\"takers\">(\"takers\")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))), 0), take(fold(recordRequired<\"takers\">(\"takers\")(a2), take(recordRequired<\"takers\">(\"takers\")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))), 1)), recordSet<\"takers\">(\"takers\")(a2)(fold(recordRequired<\"takers\">(\"takers\")(a2), take(recordRequired<\"takers\">(\"takers\")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))))))"
-- the rate limiter's request (`Test/Dogfood/P4RateLimiter.lean`, `decision`): one arm pairs
-- `true` with the window, the other `false`
#guard ((nodeAt ["a0"] (Ref.modify "w" (Test.Dogfood.P4RateLimiter.decision (var "w")) (var "a0"))).bind
    fun p => (print nativeSignature 1 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a1) => ite(lt(recordRequired<\"used\">(\"used\")(a1), 3), pair(true, recordSet<\"admitted\">(\"admitted\")(recordSet<\"used\">(\"used\")(a1)(succ(recordRequired<\"used\">(\"used\")(a1))))(succ(recordRequired<\"admitted\">(\"admitted\")(a1)))), pair(false, recordSet<\"rejected\">(\"rejected\")(a1)(succ(recordRequired<\"rejected\">(\"rejected\")(a1))))))"
-- the probe's first take attempt: one arm answers the position `0`, the other a length
#guard ((nodeAt ["q", "hint"] (Ref.modify "s" (Skeleton.tryTake (var "hint") (var "s")) (var "q"))).bind
    fun p => (print nativeSignature 2 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a2) => ite(and(lt(recordRequired<\"mHead\">(\"mHead\")(a2), length(recordRequired<\"msgs\">(\"msgs\")(a2))), not(lt(recordRequired<\"tHead\">(\"tHead\")(a2), length(recordRequired<\"takers\">(\"takers\")(a2))))), pair(tuple(get(recordRequired<\"msgs\">(\"msgs\")(a2), recordRequired<\"mHead\">(\"mHead\")(a2)), 0, ite(lt(recordRequired<\"mHead\">(\"mHead\")(recordSet<\"mHead\">(\"mHead\")(a2)(succ(recordRequired<\"mHead\">(\"mHead\")(a2)))), length(recordRequired<\"msgs\">(\"msgs\")(recordSet<\"mHead\">(\"mHead\")(a2)(succ(recordRequired<\"mHead\">(\"mHead\")(a2)))))), get(recordRequired<\"takers\">(\"takers\")(recordSet<\"mHead\">(\"mHead\")(a2)(succ(recordRequired<\"mHead\">(\"mHead\")(a2)))), recordRequired<\"tHead\">(\"tHead\")(recordSet<\"mHead\">(\"mHead\")(a2)(succ(recordRequired<\"mHead\">(\"mHead\")(a2))))), none())), recordSet<\"mHead\">(\"mHead\")(a2)(succ(recordRequired<\"mHead\">(\"mHead\")(a2)))), pair(tuple(none(), length(recordRequired<\"takers\">(\"takers\")(a2)), none()), recordSet<\"takers\">(\"takers\")(a2)(append(recordRequired<\"takers\">(\"takers\")(a2), cons(a1, nil()))))))"
-- the probe's take step in full: 9120 characters and eleven folds. Its accept pass folds with a
-- flag that starts `false` and answers `true`; until decisions row 256 the compiler refused the
-- text at that flag, with twelve diagnostics
#guard ((nodeAt ["q", "id", "hint"]
    (Ref.modify "s" (Steps.takeStep (var "id") (var "hint") (var "s")) (var "q"))).bind
    fun p => (print nativeSignature 3 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a3) => ite(and(not(isZero(length(recordRequired<\"msgs\">(\"msgs\")(a3)))), or(fold(take(recordRequired<\"takers\">(\"takers\")(a3), 1), false, (a4, a5) => sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)), and(not(fold(recordRequired<\"takers\">(\"takers\")(a3), false, (a4, a5) => or(a4, sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)))), isZero(length(recordRequired<\"takers\">(\"takers\")(a3)))))), pair(tuple(get(recordRequired<\"msgs\">(\"msgs\")(a3), 0), tupleAt<\"3\">(\"3\")(fold(recordRequired<\"offers\">(\"offers\")(a3), tuple(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1), take(recordRequired<\"offers\">(\"offers\")(a3), 0), take(recordRequired<\"offers\">(\"offers\")(a3), 0), false), (a4, a5) => ite(or(tupleAt<\"4\">(\"4\")(a4), isZero(tupleAt<\"0\">(\"0\")(a4))), tuple(tupleAt<\"0\">(\"0\")(a4), tupleAt<\"1\">(\"1\")(a4), append(tupleAt<\"2\">(\"2\")(a4), cons(a5, nil())), tupleAt<\"3\">(\"3\")(a4), true), ite(eq(length(recordRequired<\"rest\">(\"rest\")(a5)), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), tuple(sub(tupleAt<\"0\">(\"0\")(a4), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), tupleAt<\"2\">(\"2\")(a4), append(tupleAt<\"3\">(\"3\")(a4), cons(a5, nil())), false), tuple(0, append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), append(tupleAt<\"2\">(\"2\")(a4), cons(recordSet<\"rest\">(\"rest\")(a5)(drop(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), nil())), tupleAt<\"3\">(\"3\")(a4), true))))), ite(isZero(length(tupleAt<\"1\">(\"1\")(fold(recordRequired<\"offers\">(\"offers\")(a3), tuple(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1), take(recordRequired<\"offers\">(\"offers\")(a3), 0), take(recordRequired<\"offers\">(\"offers\")(a3), 0), false), (a4, a5) => ite(or(tupleAt<\"4\">(\"4\")(a4), isZero(tupleAt<\"0\">(\"0\")(a4))), tuple(tupleAt<\"0\">(\"0\")(a4), tupleAt<\"1\">(\"1\")(a4), append(tupleAt<\"2\">(\"2\")(a4), cons(a5, nil())), tupleAt<\"3\">(\"3\")(a4), true), ite(eq(length(recordRequired<\"rest\">(\"rest\")(a5)), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), tuple(sub(tupleAt<\"0\">(\"0\")(a4), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), tupleAt<\"2\">(\"2\")(a4), append(tupleAt<\"3\">(\"3\")(a4), cons(a5, nil())), false), tuple(0, append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), append(tupleAt<\"2\">(\"2\")(a4), cons(recordSet<\"rest\">(\"rest\")(a5)(drop(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), nil())), tupleAt<\"3\">(\"3\")(a4), true))))))), take(fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), a4, append(a4, cons(a5, nil())))), 0), take(fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), a4, append(a4, cons(a5, nil())))), 1))), recordSet<\"offers\">(\"offers\")(recordSet<\"takers\">(\"takers\")(recordSet<\"msgs\">(\"msgs\")(a3)(tupleAt<\"1\">(\"1\")(fold(recordRequired<\"offers\">(\"offers\")(a3), tuple(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1), take(recordRequired<\"offers\">(\"offers\")(a3), 0), take(recordRequired<\"offers\">(\"offers\")(a3), 0), false), (a4, a5) => ite(or(tupleAt<\"4\">(\"4\")(a4), isZero(tupleAt<\"0\">(\"0\")(a4))), tuple(tupleAt<\"0\">(\"0\")(a4), tupleAt<\"1\">(\"1\")(a4), append(tupleAt<\"2\">(\"2\")(a4), cons(a5, nil())), tupleAt<\"3\">(\"3\")(a4), true), ite(eq(length(recordRequired<\"rest\">(\"rest\")(a5)), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), tuple(sub(tupleAt<\"0\">(\"0\")(a4), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), tupleAt<\"2\">(\"2\")(a4), append(tupleAt<\"3\">(\"3\")(a4), cons(a5, nil())), false), tuple(0, append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), append(tupleAt<\"2\">(\"2\")(a4), cons(recordSet<\"rest\">(\"rest\")(a5)(drop(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), nil())), tupleAt<\"3\">(\"3\")(a4), true)))))))(fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), a4, append(a4, cons(a5, nil()))))))(tupleAt<\"2\">(\"2\")(fold(recordRequired<\"offers\">(\"offers\")(a3), tuple(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1), take(recordRequired<\"offers\">(\"offers\")(a3), 0), take(recordRequired<\"offers\">(\"offers\")(a3), 0), false), (a4, a5) => ite(or(tupleAt<\"4\">(\"4\")(a4), isZero(tupleAt<\"0\">(\"0\")(a4))), tuple(tupleAt<\"0\">(\"0\")(a4), tupleAt<\"1\">(\"1\")(a4), append(tupleAt<\"2\">(\"2\")(a4), cons(a5, nil())), tupleAt<\"3\">(\"3\")(a4), true), ite(eq(length(recordRequired<\"rest\">(\"rest\")(a5)), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), tuple(sub(tupleAt<\"0\">(\"0\")(a4), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5)))), append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), tupleAt<\"2\">(\"2\")(a4), append(tupleAt<\"3\">(\"3\")(a4), cons(a5, nil())), false), tuple(0, append(tupleAt<\"1\">(\"1\")(a4), take(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), append(tupleAt<\"2\">(\"2\")(a4), cons(recordSet<\"rest\">(\"rest\")(a5)(drop(recordRequired<\"rest\">(\"rest\")(a5), ite(lt(tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))), tupleAt<\"0\">(\"0\")(a4), length(recordRequired<\"rest\">(\"rest\")(a5))))), nil())), tupleAt<\"3\">(\"3\")(a4), true))))))), pair(tuple(none(), take(recordRequired<\"offers\">(\"offers\")(a3), 0), take(recordRequired<\"takers\">(\"takers\")(a3), 0)), recordSet<\"takers\">(\"takers\")(a3)(ite(fold(recordRequired<\"takers\">(\"takers\")(a3), false, (a4, a5) => or(a4, sameHandle(recordRequired<\"id\">(\"id\")(a5), a1))), fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => append(a4, cons(ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { id: a1, hint: a2 }), a5), nil()))), append(recordRequired<\"takers\">(\"takers\")(a3), cons(recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { id: a1, hint: a2 }), nil())))))))"

/-- The rate limiter's request, four times in a row on one window cell. The window admits three
requests. The answer is `[first decision, fourth decision, admitted, rejected, used]`. The brief
names this request as a truth program: it is `pRateRequest` (`harness/truth/Truth.lean`), and
its printed module runs on rc.112 with the machine's answer. Until the literal rule of decisions
row 256, tsgo 7 refused its type at the request's two arms, and the truth lane held it out. -/
def fourRequests : Src NativeOp :=
  open Test.Dogfood.P4RateLimiter in eff do
    let state ← Ref.make window0
    let first ← request false state
    let _ ← request false state
    let _ ← request false state
    let fourth ← request false state
    let w ← Ref.get state
    return tuple [first, fourth, field w "admitted", field w "rejected", field w "used"]

#guard verdict (mk fourRequests) = "built"
#guard exitOf fourRequests =
  some (.success (.list [.bool true, .bool false, .nat 3, .nat 1, .nat 3]))
#guard printVerdict fourRequests = "printed"
#guard readsBack fourRequests

/-- The probe's offer step, twice on the Queue's first state with no taker: the truth program
`pQueueOffer` (`harness/truth/Truth.lean`). The first step's answer is the hint to signal, which
is absent. The program answers `[a hint was due, the buffer's length, the head index]`. Its cell
holds the probe's whole state record, whose type names `Deferred<void, never>`; it makes no
`Deferred`, so its module prints today. -/
def twoOffers : Src NativeOp := eff do
  let q ← Ref.make Skeleton.state0
  let s1 ← Ref.modify "s" (Skeleton.offerStep (nat 1) (var "s")) q
  let _ ← Ref.modify "s" (Skeleton.offerStep (nat 2) (var "s")) q
  let s ← Ref.get q
  return tuple [app "isSome" [s1], app "length" [field s "msgs"], field s "mHead"]

#guard verdict (mk twoOffers) = "built"
#guard exitOf twoOffers = some (.success (.list [.bool false, .nat 2, .nat 0]))
#guard printVerdict twoOffers = "printed"
#guard readsBack twoOffers

/-! ## 5. `Deferred.make` at its instances (part B)

`Deferred.make<A, E>()` carries its two types in the operation (`NativeOp.deferredMakeOf`). The
faces print them on the call's head, each as the type printer prints it, and read them back
through the checked type reader (`printCall`, `readCall`). The row declares none. -/

/-- `Deferred.make<A, E>()` at an instance. -/
def make (value error : Ty) : Eff NativeOp := .perform (.deferredMakeOf value error) (.lit .unit)

/-- A record type with no tag: it prints as an object type. -/
def plainTy : Ty := .record [("a", false, .nat), ("b", true, .string)]

/-- Instances whose two types are readable (`Classes.ReadableTy`), each with its printed call.
The first two are the Queue's hints. -/
def readableInstances : List (Ty × Ty × String) :=
  [ (.unit, .never, "Deferred.make<void, never>()")
  , (.bool, .never, "Deferred.make<boolean, never>()")
  , (.nat, .nat, "Deferred.make<number, number>()")
  , (.string, .nat, "Deferred.make<string, number>()")
  , (.option .nat, .never, "Deferred.make<Option.Option<number>, never>()")
  , (.list .string, .never, "Deferred.make<ReadonlyArray<string>, never>()")
  , (.prod .nat .bool, .never, "Deferred.make<readonly [number, boolean], never>()")
  , (.lit "x", .never, "Deferred.make<\"x\", never>()")
  , (plainTy, .never, "Deferred.make<{ readonly a: number; readonly b?: string }, never>()") ]

-- each prints its type arguments, derived from the instance
#guard readableInstances.all fun (v, e, text) =>
  decide ((print nativeSignature 0 (make v e)).map (expr house0 0) = .ok text)
-- and reads back to itself: the round trip, and the domain's own verdict on the type arguments
#guard readableInstances.all fun (v, e, _) =>
  readable nativeSignature nativeSpell 0 (make v e) &&
    typeArgsReadable (nativeSignature.rowOf (.deferredMakeOf v e)) [v, e]
-- the Queue's hint, read from its syntax
#guard readEff [] nativeSignature nativeSpell 0
    (.call (.generic (.ident "Deferred.make") [.name ["void"] [], .name ["never"] []]) []) =
  .ok (make .unit .never)

/-- Instances that print and do not read back, each with its printed call: a collision, a type
that is not the reader's choice for its spelling, and a spelling with no reading
(`Classes.ReadableTy`). -/
def unreadableInstances : List (Ty × Ty × String) :=
  [ (.int, .never, "Deferred.make<number, never>()")
  , (.number, .never, "Deferred.make<number, never>()")
  , (.tuple [.nat, .bool], .never, "Deferred.make<readonly [number, boolean], never>()")
  , (.union .string .nat, .never, "Deferred.make<number | string, never>()")
  , (.unknown, .never, "Deferred.make<unknown, never>()")
  , (.refOf .nat, .never, "Deferred.make<Ref.Ref<number>, never>()")
  , (.deferredOf .unit .never, .never, "Deferred.make<Deferred.Deferred<void, never>, never>()")
  , (.record shortFields, .never, "Deferred.make<Short, never>()") ]

-- Each prints, and is outside the readable domain: the round trip does not give it back.
#guard unreadableInstances.all fun (v, e, text) =>
  decide ((print nativeSignature 0 (make v e)).map (expr house0 0) = .ok text) &&
    !readable nativeSignature nativeSpell 0 (make v e) &&
    !typeArgsReadable (nativeSignature.rowOf (.deferredMakeOf v e)) [v, e]
-- A collision reads back at the reader's choice for the spelling: `int` at `nat`, a tuple of
-- two items at a product, a union at its normal order.
#guard roundTrip nativeSignature nativeSpell 0 (make .int .never) = .ok (make .nat .never)
#guard roundTrip nativeSignature nativeSpell 0 (make (.tuple [.nat, .bool]) .never) =
  .ok (make (.prod .nat .bool) .never)
#guard roundTrip nativeSignature nativeSpell 0 (make (.union .string .nat) .never) =
  .ok (make (.union .nat .string) .never)
-- A spelling with no reading is refused as an annotation, named by the row's spelling: a
-- handle, `unknown`, and a class's name.
#guard [Ty.refOf .nat, .deferredOf .unit .never, .unknown, .record shortFields].all fun ty =>
  decide (roundTrip nativeSignature nativeSpell 0 (make ty .never) =
    .error (.annotation "Deferred.make type argument"))

-- A type with no printed form refuses the row by its spelling: a row template's parameter, a
-- nominal application at arguments, a map whose key is no string, a handle whose name does not
-- parse.
#guard [Ty.var 0, .app "Foo" [.nat], .map .nat .nat, .handle "not a type !"].all fun ty =>
  match print nativeSignature 0 (make ty .never) with
  | .error (.typeSpelling spelling) => spelling == "Deferred.make"
  | _ => false

-- Red controls of the reader. A bare call is refused by its spelling: no instance is read at a
-- default (`E4-CHECK-CE-013`). So is a call with another count of type arguments.
#guard readEff [] nativeSignature nativeSpell 0 (.call (.ident "Deferred.make") []) =
  .error (.arity "Deferred.make")
#guard readEff [] nativeSignature nativeSpell 0
    (.call (.generic (.ident "Deferred.make") [.name ["void"] []]) []) =
  .error (.arity "Deferred.make")
#guard readEff [] nativeSignature nativeSpell 0
    (.call (.generic (.ident "Deferred.make")
      [.name ["void"] [], .name ["never"] [], .name ["never"] []]) []) =
  .error (.arity "Deferred.make")
-- an empty list of type arguments is no printed form
#guard (readEff [] nativeSignature nativeSpell 0
    (.call (.generic (.ident "Deferred.make") []) [])).isOk = false
-- A row whose operation carries no type argument takes none.
#guard readEff [] nativeSignature nativeSpell 1
    (.call (.generic (.ident "Ref.get") [.name ["number"] []]) [.ident "a0"]) =
  .error (.arity "Ref.get")
-- The face is one instance for every instance, and no reading yields it without its two type
-- arguments: the spelled instance `(nat, nat)` is read like any other.
#guard nativeSignature.face (.deferredMakeOf .unit .never) = .deferredMakeOf .nat .nat
#guard nativeSpell [] "Deferred.make" [] = some (.deferredMakeOf .nat .nat)
#guard (NativeOp.row (.deferredMakeOf .unit .never)).typeArgs = []
#guard (NativeOp.row (.deferredMakeOf .unit .never)).answer = .deferredOf .unit .never

/-! ## 6. An operation's types are program annotations (decisions row 212)

Until part B the raw annotation collector read an operation's binder term and none of its type
arguments. The faces now print those types, so the collector reads them
(`ScopedOp.typeArgs`, `Formation.argumentAnnotations`): raw formation, the integer scan, the
module's representability check and its class table reach them at a located path. -/

#guard Formation.programAnnotations (make .unit .never) =
  [ (["program", "argument", "0", "op", "typeArgs", "0"], .unit)
  , (["program", "argument", "0", "op", "typeArgs", "1"], .never) ]
-- Red control: an alphabet that shows the collector no type argument names none, as every
-- alphabet did before the collector read `ScopedOp.typeArgs`.
#guard Formation.programAnnotations (Op := Blind)
    (.perform ⟨.deferredMakeOf .unit .never⟩ (.lit .unit)) = []
-- Raw formation refuses a repeated field inside a type argument, at its path.
#guard match Formation.checkInput
    (make (.record [("x", false, .nat), ("x", true, .string)]) .never) [] with
  | some why =>
    why.path == ["program", "argument", "0", "op", "typeArgs", "0", "type", "0"] &&
      why.reason == .repeatedField "x"
  | none => false
-- The integer scan refuses `int` there. Before part B such a program was admitted: the scan
-- read the program's own type at its root, and a `Deferred` that is made and dropped does not
-- show there.
#guard findIntInProgram (make .int .never) =
  some ["program", "argument", "0", "op", "typeArgs", "0"]
#guard findIntInProgram (.bind (make .int .never) (.succeed (.lit (.nat 0)))) =
  some ["program", "0", "argument", "0", "op", "typeArgs", "0"]
#guard (admitProgram (.bind (make .int .never) (.succeed (.lit (.nat 0)))) ⟨[], []⟩).isOk =
  false
#guard (admitProgram (.bind (make .unit .never) (.succeed (.lit (.nat 0)))) ⟨[], []⟩).isOk
-- A module declares the class that a type argument names: its text holds the declaration
-- before the program. Without the collector's arm the module named `Short` and declared no
-- such class.
#guard ((Effect4.Api.emitModule "main"
      (.bind (make (.record shortFields) .never) (.succeed (.lit (.nat 0))))).toOption.map
    fun emission => TypeScript.Render.module house0 emission.module).any fun text =>
  (text.splitOn "export class Short extends Data.TaggedError(\"Short\")<{ readonly available: number; readonly needed: number }> {}").length == 2 &&
    (text.splitOn "Effect.flatMap(Deferred.make<Short, never>(), (a0) => Effect.succeed(0))").length == 2
-- A type argument with no printed form refuses the module by the type's own rendering: the
-- shared check of stored annotations names the type (`annotationRefusal`). The control is a
-- nominal application at arguments.
#guard match Effect4.Api.emitModule "main" (make (.app "Foo" [.nat]) .never) with
  | .error (.print (.typeSpelling text)) => text == "Foo<number>"
  | _ => false
-- A row template's parameter in a type argument is refused before the printer, at formation: a
-- type variable is formed in a template only (`Formation.HeadFormed`; decisions row 288, point
-- 6 a). Until that clause this module was refused by the printer, at the rendering `A`.
#guard match Effect4.Api.emitModule "main" (make (.var 0) .never) with
  | .error (.formation why) =>
    why.path == ["program", "argument", "0", "op", "typeArgs", "0", "type", "0"] &&
      why.ty == .var 0 && why.reason == .typeVariable
  | _ => false

/-! ## 7. An operation that carries a binder term and type arguments

No native operation carries both. The reader's laws are stated for any lawful signature
(`LawfulTypeArgs`, `Codegen/Read.lean`): the two updates commute, and each leaves the other's
reading as it is. This fixture alphabet has one operation that carries both, so the printed
call holds the type argument on its head and the function after its arguments, and the reader
installs the one and then the other. -/

/-- `Cell.cast<T>(cell, (aN) => body)`, and `Cell.peek(cell)`. -/
inductive BothOp
  | cast (ty : Ty) (f : Term)
  | peek
deriving DecidableEq

def BothOp.term? : BothOp → Option Term
  | .cast _ f => some f
  | .peek => none

def BothOp.typeArgs : BothOp → List Ty
  | .cast ty _ => [ty]
  | .peek => []

def BothOp.withTerm : BothOp → Term → BothOp
  | .cast ty _, f => .cast ty f
  | .peek, _ => .peek

/-- At a list of another length, the face: the instance `unit`. -/
def BothOp.withTypeArgs : BothOp → List Ty → BothOp
  | .cast _ f, [ty] => .cast ty f
  | .cast _ f, _ => .cast .unit f
  | .peek, _ => .peek

instance : ScopedOp BothOp where
  scopedAt op n := op.term?.all fun f => f.scoped (n + 1)
  mapTerm g op := match op with
    | .cast ty f => .cast ty (g f)
    | .peek => .peek
  term? := BothOp.term?
  typeArgs := BothOp.typeArgs

/-- The rows: a cell at any element as the request. The cast's answer is its type argument, so
the row depends on it, in its answer column alone. -/
def bothRow : BothOp → Row
  | .cast ty _ =>
    ⟨"cast", "Cell.cast", .call, [], .sync, .refOf (.var 0), ty, .never, [], "fixture", [],
      .deferred⟩
  | .peek =>
    ⟨"peek", "Cell.peek", .call, [], .sync, .refOf (.var 0), .var 0, .never, [], "fixture", [],
      .deferred⟩

def bothSig : Signature BothOp :=
  { rowOf := bothRow, atomOf := nativeAtomTy, scopeKey := ⟨⟨0⟩, ⟨0⟩⟩
    serviceTy := fun _ => none
    termOf := fun op => op.term?.map fun f => ⟨f, .var 0, .var 0⟩
    withTerm := BothOp.withTerm
    typeArgsOf := BothOp.typeArgs
    withTypeArgs := BothOp.withTypeArgs }

/-- The inverse of the table on (spelling, trailing names): each operation at its face. -/
def bothSpell (s : String) (names : List String) : Option BothOp :=
  if s = "Cell.cast" ∧ names = [] then some (.cast .unit (.lit .unit))
  else if s = "Cell.peek" ∧ names = [] then some .peek
  else none

/-- The fixture meets the reader's laws, the type arguments' and the term's with their
independence among them. -/
theorem bothLawful : LawfulSpelling bothSig bothSpell where
  spell_row := by
    intro op _ _
    cases op <;> rfl
  row_of_spell := by
    intro s names op h
    unfold bothSpell at h
    split at h
    · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
    · split at h
      · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
      · cases h
  value_trailing := by
    intro op h
    cases op <;> cases h
  spelling_ne_name := by
    intro op i
    cases op with
    | cast ty f => exact (Var.name_ne (s := "Cell.cast") (by decide) i).symm
    | peek => exact (Var.name_ne (s := "Cell.peek") (by decide) i).symm
  spelling_not_reserved := by
    intro op
    cases op with
    | cast ty f => exact (by decide : "Cell.cast" ∉ reserved)
    | peek => exact (by decide : "Cell.peek" ∉ reserved)
  trailing_ne_name := by
    intro op i
    cases op <;> exact List.not_mem_nil
  trailing_ne_undefined := by
    intro op
    cases op <;> exact List.not_mem_nil
  withTerm_row := by
    intro op f
    cases op <;> rfl
  termOf_withTerm := by
    intro op f
    cases op <;> rfl
  withTerm_termOf := by
    intro op b hb
    cases op with
    | cast ty f =>
      cases hb
      rfl
    | peek => cases hb
  withTerm_withTerm := by
    intro op f g
    cases op <;> rfl
  withTerm_none := by
    intro op f h
    cases op with
    | cast ty t => cases h
    | peek => rfl
  typeArgs :=
    { call := by
        intro op tys
        cases op with
        | cast ty f => rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> rfl
        | peek => rfl
      typeArgsOf_withTypeArgs := by
        intro op tys h
        cases op with
        | cast ty f =>
          rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · cases h
          · rfl
          · exact absurd (Nat.succ.inj h) (Nat.succ_ne_zero _)
        | peek => exact (List.eq_nil_of_length_eq_zero h).symm
      length_typeArgsOf := by
        intro op tys
        cases op with
        | cast ty f => rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> rfl
        | peek => rfl
      withTypeArgs_typeArgsOf := by
        intro op
        cases op <;> rfl
      withTypeArgs_withTypeArgs := by
        intro op tys tys'
        cases op with
        | cast ty f =>
          rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
            rcases tys' with _ | ⟨a', _ | ⟨b', rest'⟩⟩ <;> rfl
        | peek => rfl
      withTypeArgs_withTerm := by
        intro op tys f
        cases op with
        | cast ty t => rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> rfl
        | peek => rfl
      termOf_withTypeArgs := by
        intro op tys
        cases op with
        | cast ty f => rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> rfl
        | peek => rfl
      typeArgsOf_withTerm := by
        intro op f
        cases op <;> rfl }

/-- A cast at `boolean` whose term negates the cell's value, on the cell `a0`. -/
def castNot : Eff BothOp := .perform (.cast .bool (.app "not" (.cons (.var 1) .nil))) (.var 0)

-- The printed call holds both: the type argument on the head, the function after the arguments.
#guard (print bothSig 1 castNot).map (expr house0 0) = .ok "Cell.cast<boolean>(a0, (a1) => not(a1))"
-- It reads back: the reader installs the type argument, then the term.
#guard readable bothSig bothSpell 1 castNot
#guard roundTrip bothSig bothSpell 1 castNot = .ok castNot
-- The face holds neither, and each update restores its own part whatever the order.
#guard bothSig.face (.cast .bool (.var 1)) = .cast .unit (.lit .unit)
#guard bothSig.withTerm (bothSig.withTypeArgs (bothSig.face (.cast .bool (.var 1))) [.bool])
    (.var 1) = .cast .bool (.var 1)
#guard bothSig.withTypeArgs (bothSig.withTerm (bothSig.face (.cast .bool (.var 1))) (.var 1))
    [.bool] = .cast .bool (.var 1)
-- Red controls: each part alone is refused by the row's spelling, an unread type by name, and a
-- row that carries neither takes neither.
#guard readEff [] bothSig bothSpell 1
    (.call (.ident "Cell.cast") [.ident "a0", .lambda [{ name := "a1" }] (.ident "a1")]) =
  .error (.arity "Cell.cast")
#guard readEff [] bothSig bothSpell 1
    (.call (.generic (.ident "Cell.cast") [.name ["boolean"] []]) [.ident "a0"]) =
  .error (.arity "Cell.cast")
#guard readEff [] bothSig bothSpell 1
    (.call (.generic (.ident "Cell.cast") [.name ["boolean"] [], .name ["boolean"] []])
      [.ident "a0", .lambda [{ name := "a1" }] (.ident "a1")]) =
  .error (.arity "Cell.cast")
#guard readEff [] bothSig bothSpell 1
    (.call (.generic (.ident "Cell.cast") [.name ["Foo"] []])
      [.ident "a0", .lambda [{ name := "a1" }] (.ident "a1")]) =
  .error (.annotation "Cell.cast type argument")
#guard readEff [] bothSig bothSpell 1
    (.call (.generic (.ident "Cell.peek") [.name ["boolean"] []]) [.ident "a0"]) =
  .error (.arity "Cell.peek")
#guard readEff [] bothSig bothSpell 1 (.call (.ident "Cell.peek") [.ident "a0"]) =
  .ok (.perform .peek (.var 0))

/-! ## 8. A loop's stated cursor type (part B)

`iterate` may state its cursor's type (DI-91), and the faces print it on the loop's `let`. Until
part B no reader read it: an annotated loop was printed and refused at reading. The reader now
reads the stated type through the checked type reader (`readLeaf`, `Classes.readTyChecked`), so
the loop reads back on the readable types (`Classes.ReadableTy`). -/

/-- A loop whose cursor starts absent and takes the body's answer, at a stated cursor type or
at none. -/
def loopAt (cursorTy : Option Ty) : Eff NativeOp :=
  .iterate cursorTy (.app "none" .nil)
    (.app "not" (.cons (.app "isSome" (.cons (.var 0) .nil)) .nil))
    (.var 1) (.var 0) (.succeed (.app "some" (.cons (.lit (.nat 1)) .nil)))

-- The printed text at the Queue's cursor type. `ts/eff/test/term-rows.test.ts` reads the same
-- text.
#guard (print nativeSignature 0 (loopAt (some (.option .nat)))).map (expr house0 0) =
  .ok ("Effect.suspend(() => {\n  let a0: Option.Option<number> = none()\n"
    ++ "  return Effect.map(Effect.whileLoop({\n"
    ++ "    while: () => not(isSome(a0)),\n    body: () => Effect.succeed(some(1)),\n"
    ++ "    step: (a1) => {\n      a0 = a1\n    },\n  }), () => a0)\n})")
-- It reads back to itself, and so does the loop that states no type.
#guard roundTrip nativeSignature nativeSpell 0 (loopAt (some (.option .nat))) =
  .ok (loopAt (some (.option .nat)))
#guard readable nativeSignature nativeSpell 0 (loopAt (some (.option .nat)))
#guard roundTrip nativeSignature nativeSpell 0 (loopAt none) = .ok (loopAt none)
-- Other readable cursor types read back too.
#guard [Ty.option .bool, .prod .nat (.option .string), .union .nat .string,
    .list (.option .unit), .record [("a", false, .nat)]].all fun ty =>
  readable nativeSignature nativeSpell 0 (loopAt (some ty))
-- Red controls. A collision reads back at the reader's choice for the spelling, another
-- program: the loop is outside the readable domain.
#guard roundTrip nativeSignature nativeSpell 0 (loopAt (some (.option .int))) =
  .ok (loopAt (some (.option .nat)))
#guard readable nativeSignature nativeSpell 0 (loopAt (some (.option .int))) = false
-- A spelling with no reading is refused by name, as every annotated loop was before part B.
#guard [Ty.refOf .nat, .unknown, .option (.deferredOf .unit .never), .record shortFields].all
  fun ty => decide (roundTrip nativeSignature nativeSpell 0 (loopAt (some ty)) =
    .error (.annotation "local const"))
-- A second reader of this step: `Timeout.fetch` (`Test/Dogfood/Scenario/Timeout.lean`), p1's
-- quote fetch, whose retry loop states its cursor's type. It printed as a module and did not
-- read back; since this step its module reads back to the program.
#guard (Effect4.Api.Author.build Test.Dogfood.Scenario.Timeout.fetch).toOption.map
    (fun b => (Test.Dogfood.printVerdict b, Test.Dogfood.readBackVerdict b)) =
  some ("printed", true)
-- A stated type on a yielded constant is still refused by name: the printer writes none there.
#guard readEff [] nativeSignature nativeSpell 0
    (.call (.ident "Effect.gen") [.generator
      [.constYield "a0" (.call (.ident "Effect.succeed") [.int 1])
        (some (.name ["number"] [])), .ret (.ident "a0")]]) =
  .error (.annotation "yielded const")

/-! ## The laws this battery reads

`read_print` and `read_exact` (R8's top nodes, `Laws/Codegen/ReadPrint.lean` and
`Laws/Codegen/Read.lean`) keep their statements. Their row-call steps are the two theorems
below, at their exact propositions over the native signature. -/

/-- The row call's round trip at a term row: a readable request, type arguments that read back
on the row (`typeArgsReadable`) and a term that reads back there (`termReadable`). -/
example {classes : Effect4.Codegen.Classes.Classes} {n : Nat} {op : NativeOp} {r : Term}
    (hd : nativeSignature.dom op = true)
    (hreq : requestReadable (nativeSignature.rowOf op) n r = true)
    (hc : r.covers classes = true) (hu : r.unannotated = true)
    (htypes : typeArgsReadable (nativeSignature.rowOf op) (nativeSignature.typeArgsOf op) = true)
    (hterm : termReadable classes n (nativeSignature.rowOf op)
      ((nativeSignature.termOf op).map (·.term)) = true)
    {x : TypeScript.Expr} (hp : printPerform nativeSignature n op r = .ok x) :
    readPerform classes nativeSignature nativeSpell n x = .ok (.perform op r) :=
  readPerform_printPerform nativeLawful hd hreq hc hu htypes hterm hp

/-- The row call's exactness: what the reader accepts prints back to the tree it read. -/
example {classes : Effect4.Codegen.Classes.Classes} {n : Nat} {x : TypeScript.Expr}
    {e : Eff NativeOp} (h : readPerform classes nativeSignature nativeSpell n x = .ok e) :
    print nativeSignature n e = .ok x :=
  readPerform_exact nativeLawful h

/-- The call's round trip with its type arguments (part B): the operation at its term's face. -/
example {classes : Effect4.Codegen.Classes.Classes} {n : Nat} {op : NativeOp} {r : Term}
    (hd : nativeSignature.dom op = true)
    (hreq : requestReadable (nativeSignature.rowOf op) n r = true)
    (hc : r.covers classes = true) (hu : r.unannotated = true)
    (htypes : typeArgsReadable (nativeSignature.rowOf op) (nativeSignature.typeArgsOf op) = true)
    {x : TypeScript.Expr} (hp : printCall nativeSignature n op r = .ok x) :
    readCall classes nativeSignature nativeSpell n x =
      .ok (.perform (nativeSignature.withTerm op (.lit .unit)) r) :=
  readCall_printCall nativeLawful hd hreq hc hu htypes hp

/-- The call's exactness: what the reader accepts is a `perform` that prints back to the tree
read. It asks for no readable-type premise. -/
example {classes : Effect4.Codegen.Classes.Classes} {n : Nat} {x : TypeScript.Expr}
    {e : Eff NativeOp} (h : readCall classes nativeSignature nativeSpell n x = .ok e) :
    ∃ op r, e = .perform op r ∧ printCall nativeSignature n op r = .ok x :=
  readCall_exact nativeLawful h

/-- The native signature's laws of an operation's type arguments, at their exact propositions
(`nativeLawful.typeArgs`): the call columns of the row do not depend on them, and the two
updates commute. -/
example : ∀ (op : NativeOp) (tys : List Ty),
    (nativeSignature.rowOf (nativeSignature.withTypeArgs op tys)).callColumns =
      (nativeSignature.rowOf op).callColumns :=
  (nativeLawful).typeArgs.call
example : ∀ (op : NativeOp) (tys : List Ty) (f : Term),
    nativeSignature.withTypeArgs (nativeSignature.withTerm op f) tys =
      nativeSignature.withTerm (nativeSignature.withTypeArgs op tys) f :=
  (nativeLawful).typeArgs.withTypeArgs_withTerm
-- The row itself does depend on the type arguments, in its answer column: no law of whole rows
-- holds, which is why the laws are stated on the call columns.
#guard nativeSignature.rowOf (.deferredMakeOf .unit .never) !=
  nativeSignature.rowOf (nativeSignature.face (.deferredMakeOf .unit .never))

#print axioms Effect4.Program.read_print
#print axioms Effect4.Program.read_exact
#print axioms Effect4.Program.readPerform_printPerform
#print axioms Effect4.Program.readPerform_exact
#print axioms Effect4.Program.withFunction_of_splitFunction
#print axioms Effect4.Program.splitFunction_withFunction
#print axioms Effect4.Program.splitFunction_printRow
#print axioms Effect4.Program.printPerform_ok
#print axioms Effect4.Program.nativeLawful
#print axioms Effect4.Program.readCall_printCall
#print axioms Effect4.Program.readCall_exact
#print axioms Effect4.Program.readRowCall_typeArgs_ne
#print axioms Effect4.Program.readPerformFace_bare_error
#print axioms Effect4.Program.splitHeadTypes_withHeadTypes
#print axioms Effect4.Program.withHeadTypes_of_splitHeadTypes
#print axioms Effect4.Program.printRow_congr
#print axioms Effect4.Program.printCall_ok
#print axioms Test.Codegen.TermRows.bothLawful
#print axioms Effect4.Program.readLeaf_print
#print axioms Effect4.Program.readLeaf_exact

end Test.Codegen.TermRows
