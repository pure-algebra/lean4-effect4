import Effect4.Library.Semaphore.Steps
import Effect4.Program.Authoring.Sugar
import Effect4.Laws.Library.Semaphore.Typing
import Effect4.Laws.Step.Store
import Test.Program.QueueSteps

/-!
# Semaphore's cell and its steps: finite controls of the library module (decisions row 265)

The module is `src/Effect4/Library/Semaphore/`: the cell's type and initial value (`Cell.lean`),
and the five step terms (`Steps.lean`). This battery holds the finite controls of the module
alone, and what the typing theorems do not say by themselves.

1. The cell: its two declarations, the checker's answer for the initial value, and the value.
2. Each step's type by the checker, at the step's own scope, with red controls of the scope.
3. Each step's size in nodes and folds, and the reader's domain.
4. A caller's variable under each pass that folds, with the red control of fixed names.
5. Each typing theorem at a scope of names: the step's own, and one where `bindWith` minted a
   name, with no assumed capture.
6. The connector to the store: `step_keeps_cell` on a step's typing.

The comparison with the abstract model is `Test/Program/SemaphoreAgreement.lean`. The runs on
the machine are `Test/Program/SemaphoreScenarios.lean`.

Placement. Concept `store-typing`, requirement R4. Every guard is a finite check, and every
example is an instance of a theorem of `src/Effect4/Laws/Library/Semaphore/Typing.lean`. None
states agreement with the model, and none is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Test.Program.SemaphoreSteps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Semaphore.Model
open Test.Program.QueueSteps (termAt measure)

/-- The checker's type of a source term at a scope, at the native signature. -/
def typeOf (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  typeAt nativeSignature names types src

/-! ## 1. The cell -/

-- Each written declaration normalizes to its type: the fields in the canonical order.
#guard decide (Ty.normalize (.record Semaphore.waiterFields) = Semaphore.waiterTy)
#guard decide (Ty.normalize (.record Semaphore.cellFields) = Semaphore.cellTy)
-- The checker answers the cell's type for the initial value, at each total and in any scope.
#guard [0, 1, 2, 7].all fun permits =>
  decide (typeOf [] [] (Semaphore.empty permits) = some Semaphore.cellTy) &&
    decide (typeOf ["x"] [.string] (Semaphore.empty permits) = some Semaphore.cellTy)
-- The initial value: the record frame of the four fields in the canonical order.
#guard decide (((termAt [] (Semaphore.empty 2)).bind (evalTerm [])) = some
  (.ctor 0 [.list [.str "next", .str "permits", .str "taken", .str "waiters"],
    .list [.nat 0, .nat 2, .nat 0, .list []]]))

/-! ## 2. The steps' types

Each guard is the statement of one typing theorem, at the step's own scope, by the checker's
own answer. -/

#guard decide (typeOf ["need", "id", "hint", "s"]
    [.nat, idTy, idTy, Semaphore.cellTy]
    (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s")) =
  some (.prod .bool Semaphore.cellTy))
#guard decide (typeOf ["need", "s"] [.nat, Semaphore.cellTy]
    (Semaphore.takeIfAvailableStep (var "need") (var "s")) =
  some (.prod .bool Semaphore.cellTy))
#guard decide (typeOf ["count", "s"] [.nat, Semaphore.cellTy]
    (Semaphore.releaseStep (var "count") (var "s")) =
  some (.prod releaseReplyTy Semaphore.cellTy))
#guard decide (typeOf ["cursor", "s"] [.nat, Semaphore.cellTy]
    (Semaphore.visitStep (var "cursor") (var "s")) =
  some (.prod visitReplyTy Semaphore.cellTy))
#guard decide (typeOf ["id", "s"] [idTy, Semaphore.cellTy]
    (Semaphore.withdrawStep (var "id") (var "s")) =
  some (.prod .unit Semaphore.cellTy))
-- A count that is a literal is typed too: the scenarios write their counts so.
#guard decide (typeOf ["s"] [Semaphore.cellTy] (Semaphore.releaseStep (nat 2) (var "s")) =
  some (.prod releaseReplyTy Semaphore.cellTy))

-- Red controls of the scope. A request's identity at a number has no type: `sameHandle` takes
-- two handles of one kind. A count at a Boolean has none, and a cursor at a string has none.
#guard (typeOf ["need", "id", "hint", "s"] [.nat, .nat, idTy, Semaphore.cellTy]
  (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s"))).isNone
#guard (typeOf ["need", "s"] [.bool, Semaphore.cellTy]
  (Semaphore.takeIfAvailableStep (var "need") (var "s"))).isNone
#guard (typeOf ["cursor", "s"] [.string, Semaphore.cellTy]
  (Semaphore.visitStep (var "cursor") (var "s"))).isNone
-- A hint at a `Deferred` of a number has none: a `Deferred` is invariant in its answer.
#guard (typeOf ["need", "id", "hint", "s"]
  [.nat, idTy, .deferredOf .nat .never, Semaphore.cellTy]
  (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s"))).isNone
-- A step over a waiter in place of the cell has none.
#guard (typeOf ["count", "s"] [.nat, Semaphore.waiterTy]
  (Semaphore.releaseStep (var "count") (var "s"))).isNone

/-! ## 3. The steps' sizes, and the reader's domain

The term language has no local binding, so a step repeats its passes. The measures are the
Queue battery's two algebras of the generated term fold: nodes, then folds. -/

#guard measure ["need", "id", "hint", "s"]
  (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s")) = some (74, 2)
#guard measure ["need", "s"] (Semaphore.takeIfAvailableStep (var "need") (var "s")) =
  some (20, 0)
#guard measure ["count", "s"] (Semaphore.releaseStep (var "count") (var "s")) = some (20, 0)
#guard measure ["cursor", "s"] (Semaphore.visitStep (var "cursor") (var "s")) = some (133, 3)
#guard measure ["id", "s"] (Semaphore.withdrawStep (var "id") (var "s")) = some (23, 1)
-- The two passes that fold: one fold each.
#guard measure ["cursor", "s"] (Semaphore.fromFirst (var "cursor") (var "s")) = some (34, 1)
#guard measure ["ws", "id"] (Semaphore.removeWaiter (var "ws") (var "id")) = some (16, 1)

-- No fold of a step states its accumulator's type, so each step is inside the reader's domain.
#guard ([Semaphore.takeStep (var "a") (var "b") (var "c") (var "s"),
    Semaphore.takeIfAvailableStep (var "a") (var "s"), Semaphore.releaseStep (var "a") (var "s"),
    Semaphore.visitStep (var "a") (var "s"), Semaphore.withdrawStep (var "b") (var "s")].map
  fun src => (termAt ["a", "b", "c", "s"] src).map (·.unannotated)) = List.replicate 5 (some true)

/-! ## 4. A caller's variable under each pass that folds

Each pass places its caller's term in the fold's body. The controls hand each pass a caller's
variable named `acc` or `item`: the names that a fold with fixed names would bind
(`Test/Program/FoldHygiene.lean` holds that capture). -/

/-- The scope of the controls. `acc` is request 2's identity and `item` request 1's. `cursor`
is the number 1. `cell` holds 2 permits with nothing taken, and the waiters 1 and 2, at the
stamps 0 and 1, for 1 permit each. -/
def hygieneNames : List String := ["acc", "item", "other", "h1", "h2", "cursor", "cell"]

def waiter (id : Nat) (stamp : Nat) : Val :=
  .ctor 0 [.list [.str "hint", .str "id", .str "need", .str "stamp"],
    .list [Val.promise ⟨10 + id⟩, Val.promise ⟨id⟩, .nat 1, .nat stamp]]

def cellOfWaiters (waiters : List Val) : Val :=
  .ctor 0 [.list [.str "next", .str "permits", .str "taken", .str "waiters"],
    .list [.nat 2, .nat 2, .nat 0, .list waiters]]

def hygieneValues : List Val :=
  [Val.promise ⟨2⟩, Val.promise ⟨1⟩, Val.promise ⟨3⟩, Val.promise ⟨11⟩, Val.promise ⟨12⟩, .nat 1,
   cellOfWaiters [waiter 1 0, waiter 2 1]]

/-- A term's value in the scope of the controls. -/
def valueAt (src : TermSrc) : Option Val :=
  (termAt hygieneNames src).bind (evalTerm hygieneValues)

-- `removeWaiter`: one entry leaves, by the caller's variable, whatever its name.
#guard valueAt (Semaphore.removeWaiter (field (var "cell") "waiters") (var "acc")) =
  some (.list [waiter 1 0])
#guard valueAt (Semaphore.removeWaiter (field (var "cell") "waiters") (var "item")) =
  some (.list [waiter 2 1])
#guard valueAt (Semaphore.removeWaiter (field (var "cell") "waiters") (var "other")) =
  some (.list [waiter 1 0, waiter 2 1])
-- `fromFirst`: the caller's cursor and the caller's cell both stand in the body. At the cursor
-- 1 the first waiter is passed. At the cursor 0 both stay.
#guard valueAt (Semaphore.fromFirst (var "cursor") (var "cell")) = some (.list [waiter 2 1])
#guard valueAt (Semaphore.fromFirst (nat 0) (var "cell")) =
  some (.list [waiter 1 0, waiter 2 1])

/-- The scope of the same controls with the cursor named `acc` and the cell named `item`. -/
def clashNames : List String := ["acc", "item"]

def clashValues : List Val := [.nat 1, cellOfWaiters [waiter 1 0, waiter 2 1]]

-- Under the names that a fixed fold would bind, the library's pass reads the caller's values.
#guard ((termAt clashNames (Semaphore.fromFirst (var "acc") (var "item"))).bind
  (evalTerm clashValues)) = some (.list [waiter 2 1])

/-- Red control of the hygiene: `fromFirst` with the fold's two names fixed. -/
def fromFirstFixed (cursor s : TermSrc) : TermSrc :=
  fold "acc" "item" none (field s "waiters") (noneOf (field s "waiters"))
    (ifT
      (orT (notT (isEmpty (var "acc")))
        (Semaphore.eligibleT cursor s (var "item")))
      (snoc (var "acc") (var "item")) (var "acc"))

-- Under names that the fixed pass does not bind, it answers as the library's pass.
#guard valueAt (fromFirstFixed (var "cursor") (var "cell")) = some (.list [waiter 2 1])
-- The capture: the caller's cursor `acc` reads the fold's accumulator, a list and no number,
-- so the comparison refuses and the fixed pass has no value.
#guard ((termAt clashNames (fromFirstFixed (var "acc") (var "item"))).bind
  (evalTerm clashValues)).isNone
-- A minted name is no name an author can write: the scope reader refuses it.
#guard (termAt [Env.mint {} "item"] (var (Env.mint {} "item"))).isNone

/-! ## 5. The typing theorems at a scope of names

Each example is an instance of a theorem, and no evaluation of the checker. -/

/-- The take step at its own scope: an author's variable is a caller's term under the removal's
fold (`capturedTy_var`). -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig ["need", "id", "hint", "s"] [.nat, idTy, idTy, Semaphore.cellTy]
        (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s")) =
      some (.prod .bool Semaphore.cellTy) := by
  apply typeAt_of_types
  exact takeStep_types sig atoms (needSrc := var "need") (idSrc := var "id")
    (hintSrc := var "hint") (cellSrc := var "s") (env := { names := ["need", "id", "hint", "s"] })
    (path := []) (types := [.nat, idTy, idTy, Semaphore.cellTy]) rfl
    (types_var rfl rfl rfl) (capturedTy_var rfl rfl rfl) (types_var rfl rfl rfl)
    (types_var rfl rfl rfl) false

/-- The visit at its own scope: the cursor and the cell's own source are caller's terms under
the visit's fold. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig ["cursor", "s"] [.nat, Semaphore.cellTy]
        (Semaphore.visitStep (var "cursor") (var "s")) =
      some (.prod visitReplyTy Semaphore.cellTy) := by
  apply typeAt_of_types
  exact visitStep_types sig atoms (cursorSrc := var "cursor") (cellSrc := var "s")
    (env := { names := ["cursor", "s"] }) (path := []) (types := [.nat, Semaphore.cellTy]) rfl
    (capturedTy_var rfl rfl rfl) (capturedTy_var rfl rfl rfl) false

/-! ### A cursor and an identity that `bindWith` binds

A wrapper binds its values with `bindWith`, whose names are minted, and writes the step under a
row's binder for the cell's value. Here the scope holds two minted names and the binder `s`.
`capturedTy_answer` gives the capture of a minted name, with no assumption. -/

/-- The two names that two nested `bindWith`s mint: they differ by their depths. -/
def firstName : String := Env.mint {} "answer"
def secondName : String := Env.mint { names := [firstName] } "answer"

/-- The scope of a step: the two minted names, and the row's binder `s`. -/
def stepScope : Env := { names := [firstName, secondName, "s"] }

/-- The second name is the scope's second level: the binder `s` is another name. -/
theorem stepScope_second : stepScope.names.resolve secondName = some 1 := by
  have binder : "s" ≠ secondName := written_ne_mint rfl _ "answer"
  exact (Names.resolve_append_ne binder [firstName, secondName]).trans
    (resolve_last [firstName] secondName)

/-- The cell's binder is the scope's last level. -/
theorem stepScope_cell : stepScope.names.resolve "s" = some 2 :=
  resolve_last [firstName, secondName] "s"

/-- The visit, with a cursor that `bindWith` bound: the minted name goes under the visit's fold
by `capturedTy_answer`, and the row's binder by `capturedTy_var`. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig stepScope.names [.refOf Semaphore.cellTy, .nat, Semaphore.cellTy]
        (Semaphore.visitStep (minted secondName) (var "s")) =
      some (.prod visitReplyTy Semaphore.cellTy) := by
  apply typeAt_of_types
  exact visitStep_types sig atoms (cursorSrc := minted secondName) (cellSrc := var "s")
    (env := stepScope) (path := []) (types := [.refOf Semaphore.cellTy, .nat, Semaphore.cellTy])
    rfl (capturedTy_answer (outer := { names := [firstName] }) stepScope_second rfl)
    (capturedTy_var rfl stepScope_cell rfl) false

/-- The withdrawal, with an identity that `bindWith` bound. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig stepScope.names [.refOf Semaphore.cellTy, idTy, Semaphore.cellTy]
        (Semaphore.withdrawStep (minted secondName) (var "s")) =
      some (.prod .unit Semaphore.cellTy) := by
  apply typeAt_of_types
  exact withdrawStep_types sig atoms (idSrc := minted secondName) (cellSrc := var "s")
    (env := stepScope) (path := [])
    (types := [.refOf Semaphore.cellTy, idTy, Semaphore.cellTy]) rfl
    (capturedTy_answer (outer := { names := [firstName] }) stepScope_second rfl)
    (types_var rfl stepScope_cell rfl) false

/-- A program that binds a cell and a cursor with `bindWith`, then visits. -/
def visiting : Src NativeOp :=
  bindWith (Ref.make (Semaphore.empty 2)) fun q =>
    bindWith (succeed (nat 0)) fun cursor =>
      Ref.modify "s" (Semaphore.visitStep cursor (var "s")) q

/-- The program's tree, built from the step's tree at the scope of the examples: the cell made,
the cursor bound, and one `Ref.modify` of the step on the cell's handle. -/
def visitingTree : Option (Eff NativeOp) := do
  let cell ← (Semaphore.empty 2 {} []).toOption
  let step ← (Semaphore.visitStep (minted secondName) (var "s") stepScope []).toOption
  pure (.bind (.perform .refMake cell)
    (.bind (.succeed (.lit (.nat 0))) (.perform (.refModifyWith step) (.var 0))))

-- The program's step term is the step's source at the scope of the examples: the scope at
-- which the capture is stated is the scope that the program elaborates the step in.
#guard visitingTree.isSome && (elaborate visiting).toOption == visitingTree
-- The checker types the step's term there.
#guard decide (typeOf stepScope.names [.refOf Semaphore.cellTy, .nat, Semaphore.cellTy]
    (Semaphore.visitStep (minted secondName) (var "s")) =
  some (.prod visitReplyTy Semaphore.cellTy))

/-! ## 6. The connector to the store

`step_keeps_cell` (`src/Effect4/Laws/Step/Store.lean`) reads a step's `termTy` equation:
one `Ref.modify` of the step keeps the cell a member of the cell's type. The tree
that a step's reading evaluates is the tree that the step's theorem types (`Types.tree`). The
cell's value is the scope's last name. -/

/-- **A visit keeps the cell a member of its type**, at every scope and for every caller's
terms: its reply is an option of a waiter, and its stored value is a cell. -/
theorem visitStep_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {cursorSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {tys : List Ty}
    {w : Typed.World} {captured : List Val}
    (depth : (tys ++ [Semaphore.cellTy]).length = env.names.length)
    (typesCursor : CapturedTy sig cursorSrc env path (tys ++ [Semaphore.cellTy]) .nat)
    (typesCell : CapturedTy sig cellSrc env path (tys ++ [Semaphore.cellTy]) Semaphore.cellTy)
    (typedEnv : Typed.EnvTyped w tys captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell Semaphore.cellTy)
    (reads : Reads (Semaphore.visitStep cursorSrc cellSrc) env path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    Typed.Fits w reply visitReplyTy ∧ Typed.Fits w next Semaphore.cellTy := by
  obtain ⟨f, tree, value⟩ := reads
  exact step_keeps_cell sig atoms typedEnv
    ((visitStep_types sig atoms depth typesCursor typesCell false).tree tree) held member value

/-- **A release keeps the cell a member of its type**, at every scope. -/
theorem releaseStep_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {countSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {tys : List Ty}
    {w : Typed.World} {captured : List Val}
    (typesCount : TypesEach sig countSrc env path (tys ++ [Semaphore.cellTy]) .nat)
    (typesCell : TypesEach sig cellSrc env path (tys ++ [Semaphore.cellTy]) Semaphore.cellTy)
    (typedEnv : Typed.EnvTyped w tys captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell Semaphore.cellTy)
    (reads : Reads (Semaphore.releaseStep countSrc cellSrc) env path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    Typed.Fits w reply releaseReplyTy ∧ Typed.Fits w next Semaphore.cellTy := by
  obtain ⟨f, tree, value⟩ := reads
  exact step_keeps_cell sig atoms typedEnv
    ((releaseStep_types sig atoms typesCount typesCell false).tree tree) held member value

end Test.Program.SemaphoreSteps
