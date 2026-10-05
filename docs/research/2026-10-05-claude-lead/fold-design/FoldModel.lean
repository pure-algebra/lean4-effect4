import Effect4.Machine.Term

/-!
# The list fold with two binders, as a model over the tree's own values and atoms
(research probe, 2026-10-05)

Not part of the tree. It imports the term language's module for three things only: the value
carrier `Val`, the atom evaluator `nativeAtom`, and the tuple reader. Run it from the repository
root: `lake env lean docs/research/2026-10-05-claude-lead/fold-design/FoldModel.lean`.

The model's term language `T` is the tree's `Term` cut to what the six steps need, plus the
proposed constructor:

* `fold list init body`: `body` is at the level of the fold plus two. It reads the accumulator
  at `var n` and the element at `var (n + 1)`, where `n` is the length of the environment at
  the fold. This is `iterate`'s convention: the carried value first, then the new one.

Three atoms are proposed and are not in the tree: `take`, `drop` and `sameHandle`. Every other
atom is evaluated by the tree's `nativeAtom`.

Every `#guard` is a finite check. The model has no typing, and it proves nothing about the
tree.
-/

namespace FoldModel

open Effect4 Effect4.Machine Effect4.Program

mutual
  inductive T
    | var (i : Nat)
    | nat (n : Nat)
    | bool (b : Bool)
    | app (atom : String) (args : Ts)
    | at (t : T) (i : Nat)
    | fold (list init body : T)
  inductive Ts
    | nil
    | cons (head : T) (tail : Ts)
end

def ts : List T → Ts
  | [] => .nil
  | t :: rest => .cons t (ts rest)

/-- The three proposed atoms, and the tree's atoms for every other name. -/
def atom (name : String) (vs : List Val) : Option Val :=
  match name, vs with
  | "take", [Val.nat k, xs] => (Val.asList? xs).map fun l => Val.list (l.take k)
  | "drop", [Val.nat k, xs] => (Val.asList? xs).map fun l => Val.list (l.drop k)
  | "sameHandle", [Store.Val.handle k i, Store.Val.handle k' j] =>
    if k = k' then some (Val.bool (i = j)) else none
  | _, _ => nativeAtom name vs

mutual
  /-- Evaluation. The fold runs from the head of the list; an empty list answers `init`. -/
  def eval (env : List Val) : T → Option Val
    | .var i => env[i]?
    | .nat n => some (Val.nat n)
    | .bool b => some (Val.bool b)
    | .app name args => do
      let vs ← evals env args
      atom name vs
    | .at t i => do
      let v ← eval env t
      Val.tupleAt? v i
    | .fold list init body => do
      let xs ← (eval env list).bind Val.asList?
      let start ← eval env init
      xs.foldlM (fun acc x => eval (env ++ [acc, x]) body) start
  def evals (env : List Val) : Ts → Option (List Val)
    | .nil => some []
    | .cons head tail => do
      let v ← eval env head
      let rest ← evals env tail
      some (v :: rest)
end

mutual
  /-- Every variable is below the level. A fold's body is two levels up. -/
  def inScope (n : Nat) : T → Bool
    | .var i => decide (i < n)
    | .nat _ | .bool _ => true
    | .app _ args => inScopes n args
    | .at t _ => inScope n t
    | .fold list init body => inScope n list && inScope n init && inScope (n + 2) body
  def inScopes (n : Nat) : Ts → Bool
    | .nil => true
    | .cons head tail => inScope n head && inScopes n tail
end

mutual
  /-- Weakening at a cut: one map of every variable, bound or free. With levels, a binder needs
  no case of its own. -/
  def weaken (cut : Nat) : T → T
    | .var i => .var (if cut ≤ i then i + 1 else i)
    | .nat n => .nat n
    | .bool b => .bool b
    | .app name args => .app name (weakens cut args)
    | .at t i => .at (weaken cut t) i
    | .fold list init body => .fold (weaken cut list) (weaken cut init) (weaken cut body)
  def weakens (cut : Nat) : Ts → Ts
    | .nil => .nil
    | .cons head tail => .cons (weaken cut head) (weakens cut tail)
end

/-! ## Builders -/

def call (name : String) (args : List T) : T := .app name (ts args)
def tuple (items : List T) : T := call "tuple" items
def nilT : T := call "nil" []
def one (x : T) : T := call "cons" [x, nilT]
def snoc (xs x : T) : T := call "append" [xs, one x]
def ite (c t f : T) : T := call "ite" [c, t, f]
def len (xs : T) : T := call "length" [xs]

def nats (xs : List Nat) : Val := Val.list (xs.map Val.nat)
def h (index : Nat) : Val := Store.Val.handle 3 index

/-! ## The fold's own rules -/

-- An empty list answers the initial value, and the body is not evaluated: the body here would
-- refuse.
#guard eval [nats []] (.fold (.var 0) (.nat 7) (.at (.var 1) 5)) = some (Val.nat 7)

-- From the head: `((10 - 1) - 2) - 3`, and a list built in the list's order.
#guard eval [nats [1, 2, 3]] (.fold (.var 0) (.nat 10) (call "sub" [.var 1, .var 2])) =
  some (Val.nat 4)
#guard eval [nats [1, 2, 3]] (.fold (.var 0) nilT (snoc (.var 1) (.var 2))) = some (nats [1, 2, 3])

-- The body reads an outer variable below the fold's level.
#guard eval [Val.nat 100, nats [1, 2]] (.fold (.var 1) (.nat 0)
    (call "add" [.var 2, call "add" [.var 3, .var 0]])) = some (Val.nat 203)

/-- A fold inside a fold: the inner binders are two levels above the outer ones, and the inner
body reads the outer element. Each inner item is paired with the length of its own list. -/
def nestedT : T :=
  .fold (.var 0) nilT
    (.fold (.var 2) (.var 1) (snoc (.var 3) (tuple [.var 4, len (.var 2)])))

#guard inScope 1 nestedT
#guard eval [Val.list [nats [1, 2], nats [3]]] nestedT =
  some (Val.list [Val.list [Val.nat 1, Val.nat 2], Val.list [Val.nat 2, Val.nat 2],
    Val.list [Val.nat 3, Val.nat 1]])

-- A body that fails on one element fails the fold: no partial answer.
#guard eval [nats [1, 2]] (.fold (.var 0) (.nat 0) (.at (.var 2) 0)) = none

-- The scope check: the body may read the two binders and no level above them.
#guard inScope 1 (.fold (.var 0) (.nat 0) (call "add" [.var 1, .var 2]))
#guard !inScope 1 (.fold (.var 0) (.nat 0) (call "add" [.var 1, .var 3]))
#guard !inScope 1 (.fold (.var 1) (.nat 0) (.var 1))

/-! ## The six steps of the groundwork plan, each as one term

Each step is compared with a direct function on a finite set of inputs. -/

def minT (a b : T) : T := ite (call "lt" [a, b]) a b

/-- **Step 1. The queue accepts pending offers into freed room** (`acceptLoop` of the Queue's
contract). Environment: `[room, messages, offers]`; an offer is `(identity, rest)`. The
accumulator is `(room, messages, kept, answered, stopped)`. -/
def acceptT : T :=
  let acc := T.var 3
  let o := T.var 4
  let room := T.at acc 0
  let msgs := T.at acc 1
  let kept := T.at acc 2
  let answered := T.at acc 3
  let stopped := T.at acc 4
  let rest := T.at o 1
  let k := minT room (len rest)
  let taken := call "append" [msgs, call "take" [k, rest]]
  .fold (.var 2) (tuple [.var 0, .var 1, nilT, nilT, .bool false])
    (ite (call "or" [stopped, call "isZero" [room]])
      (tuple [room, msgs, snoc kept o, answered, .bool true])
      (ite (call "eq" [len rest, k])
        (tuple [call "sub" [room, k], taken, kept, snoc answered (T.at o 0), .bool false])
        (tuple [.nat 0, taken, snoc kept (tuple [T.at o 0, call "drop" [k, rest]]), answered,
          .bool true])))

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
  eval [Val.nat room, nats msgs, Val.list (offers.map offerVal)] acceptT

def acceptAgrees (room : Nat) (msgs : List Nat) (offers : List (Nat × List Nat)) : Bool :=
  let r := acceptRef room msgs offers
  match acceptRun room msgs offers with
  | some (.list [_, m, kept, answered, _]) =>
    m == nats r.1 && kept == Val.list (r.2.1.map offerVal) && answered == nats r.2.2
  | _ => false

def offerLists : List (List (Nat × List Nat)) :=
  [[], [(101, [2])], [(101, [2]), (102, [3])], [(101, [2, 3, 4])], [(101, [2, 3]), (102, [4])],
   [(101, [2]), (102, [3, 4, 5]), (103, [6])]]

#guard inScope 3 acceptT
#guard (List.range 5).all fun room => offerLists.all fun offers => acceptAgrees room [1] offers

/-- **Step 2. The requests that became ready are named.** Environment: `[peekers]`; each peeker
gets the note `0`, which stands for "run again". -/
def nameT : T := .fold (.var 0) nilT (snoc (.var 1) (tuple [.var 2, .nat 0]))

#guard eval [Val.list [h 5, h 6]] nameT =
  some (Val.list [Val.list [h 5, Val.nat 0], Val.list [h 6, Val.nat 0]])

/-- **Step 3. A semaphore grants permits to its waiters in order, while permits remain.**
Environment: `[permits, waiters]`; a waiter is `(identity, wanted)`. The accumulator is
`(permits, granted, waiting, stopped)`. The first waiter that does not fit stops the grants. -/
def grantT : T :=
  let acc := T.var 2
  let w := T.var 3
  let permits := T.at acc 0
  .fold (.var 1) (tuple [.var 0, nilT, nilT, .bool false])
    (ite (call "or" [T.at acc 3, call "lt" [permits, T.at w 1]])
      (tuple [permits, T.at acc 1, snoc (T.at acc 2) w, .bool true])
      (tuple [call "sub" [permits, T.at w 1], snoc (T.at acc 1) (T.at w 0), T.at acc 2,
        .bool false]))

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
  eval [Val.nat permits, Val.list (waiters.map waiterVal)] grantT ==
    some (Val.list [Val.nat r.1, nats r.2.1, Val.list (r.2.2.map waiterVal),
      Val.bool !r.2.2.isEmpty])

#guard inScope 2 grantT
#guard (List.range 6).all fun permits =>
  [[], [(1, 1)], [(1, 2), (2, 1)], [(1, 1), (2, 3), (3, 1)], [(1, 4), (2, 1)]].all
    (grantAgrees permits)

/-- **Step 4. A hub hands one message to every subscriber.** Environment: `[message,
subscribers]`; a subscriber is `(identity, its messages)`. The body reads the message from the
outer environment. -/
def publishT : T :=
  .fold (.var 1) nilT
    (snoc (.var 2) (tuple [T.at (.var 3) 0, snoc (T.at (.var 3) 1) (.var 0)]))

#guard eval [Val.nat 9, Val.list [Val.list [h 1, nats [7]], Val.list [h 2, nats []]]] publishT =
  some (Val.list [Val.list [h 1, nats [7, 9]], Val.list [h 2, nats [9]]])

/-- **Step 5. One waiter leaves, by the identity of its handle.** Environment: `[target,
waiters]`; a waiter is `(handle, minimum)`. Two waiters with equal minimum are told apart. -/
def removeT : T :=
  .fold (.var 1) nilT
    (ite (call "sameHandle" [T.at (.var 3) 0, .var 0]) (.var 2) (snoc (.var 2) (.var 3)))

#guard eval [h 6, Val.list [Val.list [h 5, Val.nat 1], Val.list [h 6, Val.nat 1],
    Val.list [h 7, Val.nat 1]]] removeT =
  some (Val.list [Val.list [h 5, Val.nat 1], Val.list [h 7, Val.nat 1]])

-- A handle that the list does not hold removes nothing.
#guard eval [h 9, Val.list [Val.list [h 5, Val.nat 1]]] removeT =
  some (Val.list [Val.list [h 5, Val.nat 1]])

-- Handles of two kinds are not compared: the atom refuses, and typing excludes the case.
#guard atom "sameHandle" [Store.Val.handle 2 1, Store.Val.handle 3 1] = none

/-- **Step 6. The oldest `k` entries leave a cache.** As the proposed atom, and as a fold with a
counter; the two agree. Environment: `[k, entries]`. -/
def evictT : T := call "drop" [.var 0, .var 1]

def evictFoldT : T :=
  T.at (.fold (.var 1) (tuple [.nat 0, nilT])
    (tuple [call "succ" [T.at (.var 2) 0],
      ite (call "lt" [T.at (.var 2) 0, .var 0]) (T.at (.var 2) 1) (snoc (T.at (.var 2) 1) (.var 3))])) 1

#guard (List.range 6).all fun k =>
  let env := [Val.nat k, nats [10, 20, 30, 40]]
  eval env evictT == some (nats ([10, 20, 30, 40].drop k)) && eval env evictFoldT == eval env evictT

/-- `take` is a fold too, so the two atoms add no meaning. They are asked for the Queue's
consuming step and for a batch's acceptance. -/
def takeFoldT : T :=
  T.at (.fold (.var 1) (tuple [.nat 0, nilT])
    (tuple [call "succ" [T.at (.var 2) 0],
      ite (call "lt" [T.at (.var 2) 0, .var 0]) (snoc (T.at (.var 2) 1) (.var 3)) (T.at (.var 2) 1)])) 1

#guard (List.range 6).all fun k =>
  let env := [Val.nat k, nats [10, 20, 30, 40]]
  eval env takeFoldT == eval env (call "take" [.var 0, .var 1])

/-! ## Weakening

Inserting an unused slot at a cut changes no answer: checked for every step at every cut of its
environment. -/

def insertAt (cut : Nat) (v : Val) (env : List Val) : List Val := env.take cut ++ [v] ++ env.drop cut

def weakenAgrees (env : List Val) (t : T) : Bool :=
  (List.range (env.length + 1)).all fun cut =>
    eval (insertAt cut (Val.nat 999) env) (weaken cut t) == eval env t

#guard weakenAgrees [Val.nat 2, nats [1], Val.list ([(101, [2]), (102, [3, 4])].map offerVal)] acceptT
#guard weakenAgrees [Val.list [h 5, h 6]] nameT
#guard weakenAgrees [Val.nat 3, Val.list ([(1, 2), (2, 1), (3, 5)].map waiterVal)] grantT
#guard weakenAgrees [Val.nat 9, Val.list [Val.list [h 1, nats [7]]]] publishT
#guard weakenAgrees [h 6, Val.list [Val.list [h 5, Val.nat 1], Val.list [h 6, Val.nat 1]]] removeT
#guard weakenAgrees [Val.nat 2, nats [10, 20, 30, 40]] evictFoldT
#guard weakenAgrees [Val.list [nats [1, 2], nats [3]]] nestedT

/-- The red control: a map that leaves a fold's body alone is not weakening. -/
def weakenWrong (cut : Nat) : T → T
  | .fold list init body => .fold (weaken cut list) (weaken cut init) body
  | t => weaken cut t

def wrongDiffers : Bool :=
  let env := [Val.list [h 5, h 6]]
  eval (insertAt 0 (Val.nat 999) env) (weakenWrong 0 nameT) != eval env nameT

#guard wrongDiffers

end FoldModel
