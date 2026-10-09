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
-- Transient measurement of current printed bytes; production guards stay in their source.
#eval do
  let out := System.FilePath.mk "/tmp/authoring-branches-queue-print"
  for (name, src) in [("s9", Skeleton.s9), ("s11", Skeleton.s11), ("s12", Skeleton.s12), ("r4", Steps.r4)] do
    let some built := (Effect4.Api.Author.build (mk src)).toOption
      | throw (IO.userError s!"{name}: source refuses")
    let some printed := Effect4.Api.printModule "main" built.program built.table
      | throw (IO.userError s!"{name}: printing refuses")
    let text := TypeScript.Render.module house0 printed
    IO.FS.writeFile (out / s!"{name}.module.txt") text
    let printedHash := (Effect4.Store.sha256 text.toUTF8.data.toList).hex
    let programHash := (Effect4.Store.sha256 (Effect4.Api.bytesOf built.program)).hex
    IO.println s!"{name}\t{text.length}\t{printedHash}\t{programHash}"
end Test.Codegen.TermRows
