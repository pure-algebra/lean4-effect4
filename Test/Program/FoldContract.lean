import Effect4.Api
import Effect4.Program.Authoring.Folds
import Effect4.Laws.Program.Typed.ListFold

/-!
# The list fold and the identity of a handle: the acceptance fixture (decisions rows 228, 229)

Finite controls. Each `#guard` checks one input, and no guard is a law. The two registry claims
`fold-typed-atomic-update` and `handle-identity-laws` have their statements in
`src/Effect4/Laws/Program/Typed/ListFold.lean`.

The six steps are the design's (`docs/research/2026-10-05-claude-lead/fold-design/`, F2), each
one term of the tree, against the function the model checks it against. `take` and `drop` take
the list first, as `get` does, where the model wrote the count first.

It establishes no agreement with a target. The truth lane runs one printed fold on the pin
(`harness/truth/Truth.lean`, the program `pFold`).
-/

namespace Effect4.Test.FoldContract
open Effect4 Effect4.Machine Effect4.Program

/-! ## Builders -/

def ts (xs : List Term) : Terms := xs.foldr .cons .nil
def call (name : String) (args : List Term) : Term := .app name (ts args)
def n (k : Nat) : Term := .lit (.nat k)
def flag (x : Bool) : Term := .lit (.bool x)
def v (i : Nat) : Term := .var i
def tuple (items : List Term) : Term := call "tuple" items
def nilT : Term := call "nil" []
def one (x : Term) : Term := call "cons" [x, nilT]
def snoc (xs x : Term) : Term := call "append" [xs, one x]
def ite (c t f : Term) : Term := call "ite" [c, t, f]
def len (xs : Term) : Term := call "length" [xs]
def item (t : Term) (i : Nat) : Term := .tupleAt t i
def fold (list init body : Term) : Term := .fold none list init body
def foldAt (ty : Ty) (list init body : Term) : Term := .fold (some ty) list init body
def natList (xs : List Nat) : Term := xs.foldr (fun x acc => call "cons" [n x, acc]) nilT

def nats (xs : List Nat) : Val := Val.list (xs.map Val.nat)
/-- A Deferred handle, by its key. -/
def h (index : Nat) : Val := Val.promise ⟨index⟩
/-- The type of the handles above. -/
def hTy : Ty := .deferredOf .nat .never

/-! ## The fold's own rules -/

-- An empty list answers the initial value, and the body is not evaluated: the body here would
-- refuse.
#guard evalTerm [nats []] (fold (v 0) (n 7) (item (v 1) 5)) = some (Val.nat 7)

-- From the head: `((10 - 1) - 2) - 3`, and a list built in the list's order.
#guard evalTerm [nats [1, 2, 3]] (fold (v 0) (n 10) (call "sub" [v 1, v 2])) = some (Val.nat 4)
#guard evalTerm [nats [1, 2, 3]] (fold (v 0) nilT (snoc (v 1) (v 2))) = some (nats [1, 2, 3])
-- Red control of the order: the same fold from the tail answers another number.
#guard [1, 2, 3].foldr (fun x acc => acc - x) 10 = 4 && [1, 2, 3].foldr (fun x acc => x - acc) 10 ≠ 4

-- The body reads an outer variable below the fold's level, unchanged at every step.
#guard evalTerm [Val.nat 100, nats [1, 2]] (fold (v 1) (n 0)
    (call "add" [v 2, call "add" [v 3, v 0]])) = some (Val.nat 203)

/-- A fold inside a fold: the inner binders are two levels above the outer ones, and the inner
body reads the outer element. Each inner item is paired with the length of its own list. -/
def nestedT : Term :=
  foldAt (.list (.prod .nat .nat)) (v 0) nilT
    (fold (v 2) (v 1) (snoc (v 3) (tuple [v 4, len (v 2)])))

#guard nestedT.scoped 1
#guard evalTerm [Val.list [nats [1, 2], nats [3]]] nestedT =
  some (Val.list [Val.list [Val.nat 1, Val.nat 2], Val.list [Val.nat 2, Val.nat 2],
    Val.list [Val.nat 3, Val.nat 1]])
#guard termTy nativeSignature [.list (.list .nat)] nestedT = some (.list (.prod .nat .nat))

-- A body that refuses on one element refuses the fold: no partial answer.
#guard evalTerm [nats [1, 2]] (fold (v 0) (n 0) (item (v 2) 0)) = none
-- The same body on the empty list is not evaluated.
#guard evalTerm [nats []] (fold (v 0) (n 0) (item (v 2) 0)) = some (Val.nat 0)

-- The scope check: the body may read the two binders and no level above them. Two red cases:
-- a body that reads one level too high, and a list that reads the accumulator's level.
#guard (fold (v 0) (n 0) (call "add" [v 1, v 2])).scoped 1
#guard !(fold (v 0) (n 0) (call "add" [v 1, v 3])).scoped 1
#guard !(fold (v 1) (n 0) (v 1)).scoped 1

/-! ## The six steps of the groundwork plan, each as one term -/

def minT (a b : Term) : Term := ite (call "lt" [a, b]) a b

/-- The type of an offer and of a waiter with a count: an identity and a payload. -/
def offerTy : Ty := .prod .nat (.list .nat)

/-- The accumulator of step 1: room, messages, kept offers, answered identities, a stop flag. -/
def acceptTy : Ty := .tuple [.nat, .list .nat, .list offerTy, .list .nat, .bool]

/-- **Step 1. The queue accepts pending offers into freed room.** Environment:
`[room, messages, offers]`; an offer is `(identity, rest)`. -/
def acceptT : Term :=
  let acc := v 3
  let o := v 4
  let room := item acc 0
  let msgs := item acc 1
  let kept := item acc 2
  let answered := item acc 3
  let stopped := item acc 4
  let rest := item o 1
  let k := minT room (len rest)
  let taken := call "append" [msgs, call "take" [rest, k]]
  foldAt acceptTy (v 2) (tuple [v 0, v 1, nilT, nilT, flag false])
    (ite (call "or" [stopped, call "isZero" [room]])
      (tuple [room, msgs, snoc kept o, answered, flag true])
      (ite (call "eq" [len rest, k])
        (tuple [call "sub" [room, k], taken, kept, snoc answered (item o 0), flag false])
        (tuple [n 0, taken, snoc kept (tuple [item o 0, call "drop" [rest, k]]), answered,
          flag true])))

/-- The same step as a direct function: room, messages, offers to messages, kept offers and the
identities answered. -/
def acceptRef : Nat → List Nat → List (Nat × List Nat) → List Nat × List (Nat × List Nat) × List Nat
  | _, msgs, [] => (msgs, [], [])
  | room, msgs, (id, rest) :: more =>
    if room = 0 then (msgs, (id, rest) :: more, [])
    else
      let k := Nat.min room rest.length
      let msgs' := msgs ++ rest.take k
      if rest.drop k = [] then
        let r := acceptRef (room - k) msgs' more
        (r.1, r.2.1, id :: r.2.2)
      else (msgs', (id, rest.drop k) :: more, [])

def offerVal (o : Nat × List Nat) : Val := Val.list [Val.nat o.1, nats o.2]

def acceptRun (room : Nat) (msgs : List Nat) (offers : List (Nat × List Nat)) : Option Val :=
  evalTerm [Val.nat room, nats msgs, Val.list (offers.map offerVal)] acceptT

def acceptAgrees (room : Nat) (msgs : List Nat) (offers : List (Nat × List Nat)) : Bool :=
  let r := acceptRef room msgs offers
  match acceptRun room msgs offers with
  | some (.list [_, m, kept, answered, _]) =>
    m == nats r.1 && kept == Val.list (r.2.1.map offerVal) && answered == nats r.2.2
  | _ => false

def offerLists : List (List (Nat × List Nat)) :=
  [[], [(101, [2])], [(101, [2]), (102, [3])], [(101, [2, 3, 4])], [(101, [2, 3]), (102, [4])],
   [(101, [2]), (102, [3, 4, 5]), (103, [6])]]

#guard acceptT.scoped 3
#guard (List.range 5).all fun room => offerLists.all fun offers => acceptAgrees room [1] offers
#guard termTy nativeSignature [.nat, .list .nat, .list offerTy] acceptT = some acceptTy

/-- **Step 2. The requests that became ready are named.** Environment: `[peekers]`; each peeker
gets the note `0`, which stands for "run again". -/
def nameT : Term := foldAt (.list (.prod hTy .nat)) (v 0) nilT (snoc (v 1) (tuple [v 2, n 0]))

#guard evalTerm [Val.list [h 5, h 6]] nameT =
  some (Val.list [Val.list [h 5, Val.nat 0], Val.list [h 6, Val.nat 0]])
#guard termTy nativeSignature [.list hTy] nameT = some (.list (.prod hTy .nat))

/-- The accumulator of step 3: permits, granted identities, waiters still waiting, a stop flag. -/
def grantTy : Ty := .tuple [.nat, .list .nat, .list (.prod .nat .nat), .bool]

/-- **Step 3. A semaphore grants permits to its waiters in order, while permits remain.**
Environment: `[permits, waiters]`; a waiter is `(identity, wanted)`. The first waiter that does
not fit stops the grants. -/
def grantT : Term :=
  let acc := v 2
  let w := v 3
  let permits := item acc 0
  foldAt grantTy (v 1) (tuple [v 0, nilT, nilT, flag false])
    (ite (call "or" [item acc 3, call "lt" [permits, item w 1]])
      (tuple [permits, item acc 1, snoc (item acc 2) w, flag true])
      (tuple [call "sub" [permits, item w 1], snoc (item acc 1) (item w 0), item acc 2,
        flag false]))

def grantRef : Nat → List (Nat × Nat) → Nat × List Nat × List (Nat × Nat)
  | permits, [] => (permits, [], [])
  | permits, (id, wanted) :: more =>
    if permits < wanted then (permits, [], (id, wanted) :: more)
    else
      let r := grantRef (permits - wanted) more
      (r.1, id :: r.2.1, r.2.2)

def waiterVal (w : Nat × Nat) : Val := Val.list [Val.nat w.1, Val.nat w.2]

def grantAgrees (permits : Nat) (waiters : List (Nat × Nat)) : Bool :=
  let r := grantRef permits waiters
  evalTerm [Val.nat permits, Val.list (waiters.map waiterVal)] grantT ==
    some (Val.list [Val.nat r.1, nats r.2.1, Val.list (r.2.2.map waiterVal),
      Val.bool !r.2.2.isEmpty])

#guard grantT.scoped 2
#guard (List.range 6).all fun permits =>
  [[], [(1, 1)], [(1, 2), (2, 1)], [(1, 1), (2, 3), (3, 1)], [(1, 4), (2, 1)]].all
    (grantAgrees permits)
#guard termTy nativeSignature [.nat, .list (.prod .nat .nat)] grantT = some grantTy

/-- A subscriber: its handle and its messages. -/
def subscriberTy : Ty := .prod hTy (.list .nat)

/-- **Step 4. A hub hands one message to every subscriber.** Environment: `[message,
subscribers]`. The body reads the message from the outer environment. -/
def publishT : Term :=
  foldAt (.list subscriberTy) (v 1) nilT
    (snoc (v 2) (tuple [item (v 3) 0, snoc (item (v 3) 1) (v 0)]))

#guard evalTerm [Val.nat 9, Val.list [Val.list [h 1, nats [7]], Val.list [h 2, nats []]]] publishT =
  some (Val.list [Val.list [h 1, nats [7, 9]], Val.list [h 2, nats [9]]])
#guard termTy nativeSignature [.nat, .list subscriberTy] publishT = some (.list subscriberTy)

/-- A waiter of step 5: its handle and its minimum. -/
def waiterTy : Ty := .prod hTy .nat

/-- **Step 5. One waiter leaves, by the identity of its handle.** Environment: `[target,
waiters]`. Two waiters with equal minimum are told apart. -/
def removeT : Term :=
  foldAt (.list waiterTy) (v 1) nilT
    (ite (call "sameHandle" [item (v 3) 0, v 0]) (v 2) (snoc (v 2) (v 3)))

#guard evalTerm [h 6, Val.list [Val.list [h 5, Val.nat 1], Val.list [h 6, Val.nat 1],
    Val.list [h 7, Val.nat 1]]] removeT =
  some (Val.list [Val.list [h 5, Val.nat 1], Val.list [h 7, Val.nat 1]])
-- A handle that the list does not hold removes nothing.
#guard evalTerm [h 9, Val.list [Val.list [h 5, Val.nat 1]]] removeT =
  some (Val.list [Val.list [h 5, Val.nat 1]])
#guard termTy nativeSignature [hTy, .list waiterTy] removeT = some (.list waiterTy)

/-- **Step 6. The oldest `k` entries leave a cache.** As the atom, and as a fold with a
counter; the two agree. Environment: `[k, entries]`. -/
def evictT : Term := call "drop" [v 1, v 0]

def evictFoldT : Term :=
  item (foldAt (.prod .nat (.list .nat)) (v 1) (tuple [n 0, nilT])
    (tuple [call "succ" [item (v 2) 0],
      ite (call "lt" [item (v 2) 0, v 0]) (item (v 2) 1) (snoc (item (v 2) 1) (v 3))])) 1

#guard (List.range 6).all fun k =>
  let env := [Val.nat k, nats [10, 20, 30, 40]]
  evalTerm env evictT == some (nats ([10, 20, 30, 40].drop k)) &&
    evalTerm env evictFoldT == evalTerm env evictT
#guard termTy nativeSignature [.nat, .list .nat] evictT = some (.list .nat)
#guard termTy nativeSignature [.nat, .list .nat] evictFoldT = some (.list .nat)

/-- `take` is a fold too, so the two atoms add no meaning. -/
def takeFoldT : Term :=
  item (foldAt (.prod .nat (.list .nat)) (v 1) (tuple [n 0, nilT])
    (tuple [call "succ" [item (v 2) 0],
      ite (call "lt" [item (v 2) 0, v 0]) (snoc (item (v 2) 1) (v 3)) (item (v 2) 1)])) 1

#guard (List.range 6).all fun k =>
  let env := [Val.nat k, nats [10, 20, 30, 40]]
  evalTerm env takeFoldT == evalTerm env (call "take" [v 1, v 0]) &&
    evalTerm env takeFoldT == some (nats ([10, 20, 30, 40].take k))

/-! ## Weakening

Inserting an unused slot at a cut changes no answer: checked for every step at every cut of its
environment. The law is `evalTerm_weaken`; these are its finite instances. -/

def insertAt (cut : Nat) (x : Val) (env : List Val) : List Val := env.take cut ++ [x] ++ env.drop cut

def weakenAgrees (env : List Val) (t : Term) : Bool :=
  (List.range (env.length + 1)).all fun cut =>
    evalTerm (insertAt cut (Val.nat 999) env) (Term.weaken cut t) == evalTerm env t

#guard weakenAgrees [Val.nat 2, nats [1], Val.list ([(101, [2]), (102, [3, 4])].map offerVal)] acceptT
#guard weakenAgrees [Val.list [h 5, h 6]] nameT
#guard weakenAgrees [Val.nat 3, Val.list ([(1, 2), (2, 1), (3, 5)].map waiterVal)] grantT
#guard weakenAgrees [Val.nat 9, Val.list [Val.list [h 1, nats [7]]]] publishT
#guard weakenAgrees [h 6, Val.list [Val.list [h 5, Val.nat 1], Val.list [h 6, Val.nat 1]]] removeT
#guard weakenAgrees [Val.nat 2, nats [10, 20, 30, 40]] evictFoldT
#guard weakenAgrees [Val.list [nats [1, 2], nats [3]]] nestedT

/-- The red control: a map that leaves a fold's body alone is not weakening. -/
def weakenWrong (cut : Nat) : Term → Term
  | .fold accTy list init body => .fold accTy (Term.weaken cut list) (Term.weaken cut init) body
  | t => Term.weaken cut t

#guard
  let env := [Val.list [h 5, h 6]]
  evalTerm (insertAt 0 (Val.nat 999) env) (weakenWrong 0 nameT) != evalTerm env nameT

/-! ## The checker's refusals, by reason -/

def refusalOf (env : TyEnv) (t : Term) : Option TermTypingRefusal :=
  TermRefusal.diagnose nativeSignature env t

-- A fold over a value that is no list.
#guard match refusalOf [] (fold (n 1) (n 0) (v 0)) with
  | some (.fold ⟨path, .notList ty⟩) => path == [] && ty == .nat
  | _ => false
-- A body whose answer is no subtype of the accumulator's type: the initial value is a number
-- and the body answers a list.
#guard match refusalOf [] (fold (natList [1]) (n 0) (one (v 1))) with
  | some (.fold ⟨path, .bodyNotAccumulator body acc⟩) =>
    path == [] && body == .list .nat && acc == .nat
  | _ => false
-- An initial value that is no member of the stated type.
#guard match refusalOf [] (foldAt .string (natList [1]) (n 0) (v 0)) with
  | some (.fold ⟨path, .initialNotAccumulator initial acc⟩) =>
    path == [] && initial == .nat && acc == .string
  | _ => false
-- A refusal inside a fold's body is found at the body's own environment, at the body's path.
#guard match refusalOf [] (fold (natList [1]) (n 0) (item (v 1) 3)) with
  | some (.tuple ⟨path, _, _⟩) => path == [2]
  | _ => false
-- An accumulator that starts as the empty list needs its stated type: without it the body's
-- wider list is refused, and with it the fold types.
#guard (termTy nativeSignature [.list .nat] (fold (v 0) nilT (snoc (v 1) (v 2)))).isNone
#guard termTy nativeSignature [.list .nat] (foldAt (.list .nat) (v 0) nilT (snoc (v 1) (v 2))) =
  some (.list .nat)

/-! ### The identity atom: typing admits one handle family, and evaluation follows the kind byte -/

-- Two cells, at two payload types, and two Deferred cells are admitted.
#guard nativeAtomTy "sameHandle" [.refOf .nat, .refOf .string] = some .bool
#guard nativeAtomTy "sameHandle" [.deferredOf .nat .never, .deferredOf .string .nat] = some .bool
-- Two kinds are refused, and so is a kind the rule does not name: two fibers, two scopes.
#guard nativeAtomTy "sameHandle" [.refOf .nat, .deferredOf .nat .never] = none
#guard nativeAtomTy "sameHandle" [.fiberOf .nat .never, .fiberOf .nat .never] = none
#guard nativeAtomTy "sameHandle" [.handle Ty.scopeTarget, .handle Ty.scopeTarget] = none
#guard nativeAtomTy "sameHandle" [.nat, .nat] = none
#guard nativeAtomTy "sameHandle" [.refOf .nat] = none
-- The evaluation reads the kind byte and the two keys, and nothing else: one kind compares
-- the keys, two kinds refuse, and a value that is no handle refuses.
#guard nativeAtom "sameHandle" [Val.cell ⟨4⟩, Val.cell ⟨4⟩] = some (Val.bool true)
#guard nativeAtom "sameHandle" [Val.cell ⟨4⟩, Val.cell ⟨5⟩] = some (Val.bool false)
#guard nativeAtom "sameHandle" [h 4, h 4] = some (Val.bool true)
#guard nativeAtom "sameHandle" [Val.cell ⟨4⟩, h 4] = none
#guard nativeAtom "sameHandle" [Val.fiber ⟨1⟩, Val.fiber ⟨1⟩] = some (Val.bool true)
#guard nativeAtom "sameHandle" [Val.nat 4, Val.nat 4] = none
-- A program that compares a cell with a Deferred cell is refused by the checker.
#guard (Effect4.Api.typeOf
  (.bind (.perform .refMake (n 0)) (.bind (.perform (.deferredMakeOf .nat .never) (.lit .unit))
    (.succeed (call "sameHandle" [v 0, v 1]))))).isNone
#guard (Effect4.Api.typeOf
  (.bind (.perform .refMake (n 0)) (.bind (.perform .refMake (n 1))
    (.succeed (call "sameHandle" [v 0, v 1]))))).map (·.answer) = some .bool

/-! ### `take` and `drop` -/

#guard nativeAtom "take" [nats [1, 2, 3], Val.nat 2] = some (nats [1, 2])
#guard nativeAtom "drop" [nats [1, 2, 3], Val.nat 2] = some (nats [3])
#guard nativeAtom "take" [nats [1, 2, 3], Val.nat 9] = some (nats [1, 2, 3])
#guard nativeAtom "drop" [nats [1, 2, 3], Val.nat 9] = some (nats [])
#guard nativeAtom "take" [Val.nat 2, nats [1, 2, 3]] = none
#guard nativeAtomTy "take" [.list .string, .nat] = some (.list .string)
#guard nativeAtomTy "drop" [.list .string, .nat] = some (.list .string)
#guard nativeAtomTy "take" [.nat, .list .string] = none

/-! ## Programs: the machine's exits -/

def exitOf (program : Api.Program) : ExitV := (Api.runSync program 400).2

/-- `fold([1, 2, 3], 10, (acc, x) => acc - x)`. -/
def pFold : Api.Program := .succeed (fold (natList [1, 2, 3]) (n 10) (call "sub" [v 0, v 1]))
/-- An outer capture: the body adds the bound `100` at every step. -/
def pFoldCapture : Api.Program :=
  .bind (.succeed (n 100))
    (.succeed (fold (natList [1, 2]) (n 0) (call "add" [v 1, call "add" [v 2, v 0]])))
/-- A fold inside a fold, over a bound list of lists. -/
def pFoldNested : Api.Program :=
  .bind (.succeed (call "cons" [natList [1, 2], call "cons" [natList [3], nilT]]))
    (.succeed nestedT)
/-- A fold inside an operation's term: `Ref.modify(cell, a => [fold([1, 2, 3], a, +), a])`. The
cell is variable 0, its value variable 1, and the fold binds variables 2 and 3. -/
def pFoldInOp : Api.Program :=
  .bind (.perform .refMake (n 5))
    (.perform (.refModifyWith (call "pair"
      [fold (natList [1, 2, 3]) (v 1) (call "add" [v 2, v 3]), v 1])) (v 0))
/-- A body that refuses on its first element: it projects a number. -/
def pFoldRefuses : Api.Program := .succeed (fold (natList [1, 2]) (n 0) (item (v 1) 0))

#guard exitOf pFold == .success (Val.nat 4)
#guard exitOf pFoldCapture == .success (Val.nat 203)
#guard exitOf pFoldNested ==
  .success (Val.list [Val.list [Val.nat 1, Val.nat 2], Val.list [Val.nat 2, Val.nat 2],
    Val.list [Val.nat 3, Val.nat 1]])
-- One atomic step: the row answers the fold's sum and leaves the cell's value in the cell.
#guard exitOf pFoldInOp == .success (Val.nat 11)
#guard (Api.runSync pFoldInOp 400).1.state.refs == [Val.nat 5]
#guard (Effect4.Api.typeOf pFold).map (·.answer) = some .nat
#guard (Effect4.Api.typeOf pFoldInOp).map (·.answer) = some .nat
#guard (admitProgram pFoldInOp ⟨[], []⟩).isOk
-- A failing body. The checker refuses the program: a typed fold answers
-- (`ListFoldRules.typed`), so only a raw run meets a refusing step. The raw run exits with the
-- wrong-shape defect, and no partial answer.
#guard (Effect4.Api.typeOf pFoldRefuses).isNone
#guard exitOf pFoldRefuses == .failure (Cause.die Defect.badName)

/-! ## The faces -/

/-- The printed text of a program. It is a macro, so the rendered bytes stay inside each guard:
a battery `def` over rendered text reaches `Classical.choice` (AGENTS.md, Trust). -/
local macro "printed% " program:term:max : term =>
  `((Api.print $program).toOption.map (TypeScript.Render.expr TypeScript.house0 0))

#guard printed% pFold =
  some "Effect.succeed(fold(cons(1, cons(2, cons(3, nil()))), 10, (a0, a1) => sub(a0, a1)))"
-- The binders are the names of the fold's own level: below a bound value they are `a1`, `a2`.
#guard (printed% pFoldCapture).any fun text =>
  (text.splitOn "(a1, a2) => add(a1, add(a2, a0))").length == 2
-- A term position prints and reads back.
#guard Api.roundTrip pFold == .ok pFold
#guard Api.roundTrip pFoldCapture == .ok pFoldCapture
-- A stated type prints as the call's type argument, and the reader refuses it by name (B19).
-- The checked type reader of the state plan's T5, part B, reads an operation's type arguments
-- and a loop's stated cursor type; the fold's stated type is the place it does not serve yet.
#guard (printed% pFoldNested).any fun text =>
  (text.splitOn "fold<ReadonlyArray<readonly [number, number]>>(a0, nil(), (a1, a2) => fold(a2, a1, (a3, a4) =>").length == 2
#guard match Api.roundTrip pFoldNested with
  | .error (.annotation what) => what == "fold accumulator"
  | _ => false
-- An operation's term prints as a function of the current value (the state plan's T5), and a
-- fold inside it binds the two levels above that value: the cell is `a0`, its value `a1`, and
-- the fold's binders `a2` and `a3`. The program reads back.
#guard printed% pFoldInOp = some
  "Effect.flatMap(Ref.make(5), (a0) => Ref.modify(a0, (a1) => pair(fold(cons(1, cons(2, cons(3, nil()))), a1, (a2, a3) => add(a2, a3)), a1)))"
#guard Api.roundTrip pFoldInOp == .ok pFoldInOp

/-! ### The fold's level under a binder, and in a closed layer (Codex's depth control)

A fold over `[true]` from `false` whose body answers its accumulator answers `false`. Under one
binder its two binders are the names of the levels one and two above the node's. A printer that
handed the fold the node's own level would name the element where the body names the
accumulator, and the printed program would answer `true`. -/

def depthFold (level : Nat) : Term :=
  fold (one (flag true)) (flag false) (v level)

/-- `catchIf`'s test binds the failure at the node's level, so the fold inside stands one above. -/
def pDepth : Api.Program :=
  .catchIf (depthFold 1) (.fail (n 7)) (.succeed (n 1))

#guard (Effect4.Api.typeOf pDepth).isSome
-- The test answers `false`, so the failure is not caught.
#guard exitOf pDepth == .failure (Cause.fail (errOf (Val.nat 7)))
#guard (printed% pDepth).any fun text =>
  (text.splitOn "fold(cons(true, nil()), false, (a1, a2) => a1)").length == 2
#guard Api.roundTrip pDepth == .ok pDepth
-- Red control: the same body at the node's own level names the caught failure, not the
-- accumulator, and is refused by the checker (a number is no Boolean).
#guard (Effect4.Api.typeOf (.catchIf (depthFold 0) (.fail (n 7)) (.succeed (n 1)))).isNone

/-- The same control over numbers: the accumulator starts at `0` and the one element is `1`. -/
def depthFoldNat (level : Nat) : Term := fold (one (n 1)) (n 0) (v level)

def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

/-- The closed companion: a layer's body is checked and printed at level `0`, whatever the
node's level. Under one bound value, the fold inside the layer binds `a0` and `a1` again. -/
def pLayer (level : Nat) : Api.Program :=
  .bind (.succeed (n 5))
    (.scoped (.provideLayer (.effect kA (.succeed (depthFoldNat level))) false (.service kA)))

#guard exitOf (pLayer 0) == .success (Val.nat 0)
#guard (printed% (pLayer 0)).any fun text =>
  (text.splitOn "Effect.succeed(fold(cons(1, nil()), 0, (a0, a1) => a0))").length == 2
#guard Api.roundTrip (pLayer 0) == .ok (pLayer 0)
-- Red control: one level up names the element, and the layer answers `1`.
#guard exitOf (pLayer 1) == .success (Val.nat 1)

/-! ## A stated type inside an operation's term is a program annotation (Codex's candidate)

The fold's stated type is compared after normalization, so the term typer alone admits a stated
type that raw formation refuses: a map whose key is no string. The raw annotation collector must
therefore reach it wherever a fold may stand. In an operation's binder term it reaches it
through the alphabet's reading view (`ScopedOp.term?`), at the path segment `op`. -/

/-- An empty fold whose stated accumulator type is a list of maps with the given key type. Its
body answers its accumulator, at the given level. -/
def keyedFold (level : Nat) (key : Ty) : Term :=
  foldAt (.list (.map key .nat)) nilT nilT (v level)

/-- The candidate: the fold inside `Ref.modify`'s term. The cell is variable 0, its value
variable 1, the accumulator variable 2. The length hides the stated type from the row's columns. -/
def hiddenFold (key : Ty) : Api.Program :=
  .bind (.perform .refMake (n 0))
    (.perform (.refModifyWith (call "pair" [len (keyedFold 2 key), v 1])) (v 0))

/-- The same fold in a term position of the program. -/
def visibleFold (key : Ty) : Api.Program :=
  .bind (.perform .refMake (n 0)) (.succeed (len (keyedFold 1 key)))

-- The term typer admits both placements at a number key: it is not the check.
#guard (Effect4.Api.typeOf (hiddenFold .nat)).isSome
#guard (Effect4.Api.typeOf (visibleFold .nat)).isSome
-- Raw formation refuses both, each at its located path, before normalization.
#guard match Formation.checkInput (visibleFold .nat) [] with
  | some why =>
    why.path == ["program", "1", "argument", "0", "term", "0", "0", "accTy", "type", "1"] &&
      why.reason == .mapKey
  | none => false
#guard match Formation.checkInput (hiddenFold .nat) [] with
  | some why =>
    why.path == ["program", "1", "argument", "0", "op", "term", "0", "0", "0", "0", "accTy",
      "type", "1"] && why.reason == .mapKey
  | none => false
-- Ordinary admission refuses both, with the same located refusal.
#guard match admitProgram (visibleFold .nat) ⟨[], []⟩ with
  | .error (.formation why) => why.reason == .mapKey && why.ty == .map .nat .nat
  | _ => false
#guard match admitProgram (hiddenFold .nat) ⟨[], []⟩ with
  | .error (.formation why) =>
    why.reason == .mapKey && why.ty == .map .nat .nat &&
      why.path == ["program", "1", "argument", "0", "op", "term", "0", "0", "0", "0", "accTy",
        "type", "1"]
  | _ => false
-- Green control: a string key is formed, and both placements are admitted.
#guard Formation.checkInput (hiddenFold .string) [] = none
#guard (admitProgram (hiddenFold .string) ⟨[], []⟩).isOk
#guard (admitProgram (visibleFold .string) ⟨[], []⟩).isOk

/-- An alphabet that shows the collector no term: the native operations with the class's default
reading view. Scope and the term map are the native ones. -/
structure Blind where
  op : NativeOp

instance : ScopedOp Blind where
  scopedAt blind level := ScopedOp.scopedAt blind.op level
  mapTerm g blind := ⟨ScopedOp.mapTerm g blind.op⟩

/-- The candidate over the blind alphabet. -/
def blindFold : Eff Blind :=
  .bind (.perform ⟨.refMake⟩ (n 0))
    (.perform ⟨.refModifyWith (call "pair" [len (keyedFold 2 .nat), v 1])⟩ (v 0))

-- Red control of the repair: where the alphabet shows no term, the collector finds no
-- annotation and raw formation accepts the malformed type. This is what the collector did at
-- every alphabet before it read `ScopedOp.term?`.
#guard Formation.programAnnotations blindFold = []
#guard Formation.checkInput blindFold [] = none
#guard (Formation.programAnnotations (hiddenFold .nat)).map (·.1) =
  [["program", "1", "argument", "0", "op", "term", "0", "0", "0", "0", "accTy"]]

/-! ## The builder an author writes -/

/-- `pFoldCapture`, by names. -/
def authored : Authoring.Src NativeOp :=
  Authoring.bind "base" (Authoring.succeed (Authoring.nat 100))
    (Authoring.succeed (Authoring.fold "total" "x" none
      (Authoring.app "cons" [Authoring.nat 1,
        Authoring.app "cons" [Authoring.nat 2, Authoring.app "nil" []]])
      (Authoring.nat 0)
      (Authoring.app "add" [Authoring.var "total",
        Authoring.app "add" [Authoring.var "x", Authoring.var "base"]])))

#guard match Effect4.Api.author authored with
  | .ok typed => typed.program == pFoldCapture && typed.runSync == .success (Val.nat 203)
  | .error _ => false
-- The two names are in scope in the body only: the list does not see them.
#guard match Effect4.Api.author (Authoring.succeed (Authoring.fold "total" "x" none
    (Authoring.var "x") (Authoring.nat 0) (Authoring.var "total"))) with
  | .error _ => true
  | .ok _ => false

end Effect4.Test.FoldContract
