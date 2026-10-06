import Effect4.Modules.Pool.Steps
import Effect4.Program.Authoring.Sugar
import Effect4.Laws.Modules.Pool.Typing
import Effect4.Laws.Modules.Store
import Effect4.Laws.Modules.Waiting
import Test.Program.QueueSteps
import ProofGraph.Plan

/-!
# Pool's cell and its steps: finite controls of the library module (decisions rows 267 to 269)

The module is `src/Effect4/Modules/Pool/`: the cell's type and initial value (`Cell.lean`), and
the five step terms (`Steps.lean`). This battery holds the finite controls of the module alone,
and what the typing theorems do not say by themselves.

1. The cell: its three declarations, the checker's answer for the initial value, and the value.
2. Each step's type by the checker, at the step's own scope, with red controls of the scope.
3. Each step's size in nodes and folds, and the reader's domain.
4. A caller's variable under each pass that folds, with the red control of fixed names.
5. Each typing theorem at a scope of names: the step's own, and the scope of a row of
   `Ref.modifyWith` under three names that `bindWith` minted, with no assumed capture.
6. The connector to the store: `step_keeps_cell` on a step's typing.
7. The pinned axioms and the pinned standing of each typing theorem.

The comparison with the abstract model is `Test/Program/PoolAgreement.lean`. The runs on the
machine are `Test/Program/PoolScenarios.lean`.

Placement. Concept `store-typing`, requirement R4. Every guard is a finite check, and every
example is an instance of a theorem of `src/Effect4/Laws/Modules/Pool/Typing.lean`. None states
agreement with the model, and none is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Test.Program.PoolSteps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Pool.Model
open Test.Program.QueueSteps (termAt measure)

/-- The checker's type of a source term at a scope, at the native signature. -/
def typeOf (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  typeAt nativeSignature names types src

/-! ## 1. The cell -/

/-- Resource types that are their own normal form. The cell is checked at each. -/
def resourceTypes : List Ty :=
  [.nat, .string, .bool, .unit, .option .nat, .list .string, .prod .nat .string,
   .refOf .nat, .deferredOf .nat .never, .record [("a", false, .nat), ("b", true, .string)],
   .tuple [.nat, .string, .bool], Pool.itemTy .nat]

/-- Resource types that are not their own normal form. -/
def unnormalTypes : List Ty :=
  [.union .nat .nat, .tuple [.nat, .string], .record [("b", false, .nat), ("a", false, .nat)]]

-- Each written declaration normalizes to its type: the fields in the canonical order.
#guard decide (Ty.normalize (.record Pool.waiterFields) = Pool.waiterTy)
#guard resourceTypes.all fun A =>
  decide (Ty.normalize (.record (Pool.itemFields A)) = Pool.itemTy A) &&
    decide (Ty.normalize (.record (Pool.cellFields A)) = Pool.cellTy A)
-- `ResourceTy` holds at each, and it refuses a type that is not its own normal form.
#guard resourceTypes.all fun A => decide (ResourceTy A)
#guard unnormalTypes.all fun A => !decide (ResourceTy A)

-- The checker answers the cell's type for the initial value, at one, two and three resources
-- and in any scope.
#guard [[nat 1], [nat 1, nat 2], [nat 5, nat 5, nat 5]].all fun resources =>
  decide (typeOf [] [] (Pool.initial .nat resources) = some (Pool.cellTy .nat)) &&
    decide (typeOf ["x"] [.string] (Pool.initial .nat resources) = some (Pool.cellTy .nat))
-- The resources may be a caller's variables, at each resource type.
#guard resourceTypes.all fun A =>
  decide (typeOf ["r", "q"] [A, A] (Pool.initial A [var "r", var "q"]) = some (Pool.cellTy A))
-- Red control. A resource at another type has no type as the cell.
#guard (typeOf ["r"] [.bool] (Pool.initial .nat [var "r"])).isNone
-- A limit of `initial_types`, and no limit of the checker. A string literal has its literal
-- type inside a record, so it is no caller's term of the theorem. The checker types the
-- initial value at it all the same: the literal's type is below the declared one.
#guard decide (typeOf [] [] (Pool.initial .string [str "x"]) = some (Pool.cellTy .string))
-- The initial value at two resources: the record frames in the canonical order. Each resource
-- has the stamp of its position, every item is idle, and the idle stamps are `[0, 1]`.
#guard decide (((termAt [] (Pool.initial .nat [nat 7, nat 8])).bind (evalTerm [])) = some
  (.ctor 0 [.list [.str "available", .str "closing", .str "items", .str "next", .str "waiters"],
    .list [.list [.nat 0, .nat 1], .bool false,
      .list [
        .ctor 0 [.list [.str "borrowed", .str "lease", .str "resource", .str "stamp"],
          .list [.bool false, .nat 0, .nat 7, .nat 0]],
        .ctor 0 [.list [.str "borrowed", .str "lease", .str "resource", .str "stamp"],
          .list [.bool false, .nat 0, .nat 8, .nat 1]]],
      .nat 0, .list []]]))

/-! ## 2. The steps' types

Each guard is the statement of one typing theorem, at the step's own scope, by the checker's
own answer, at each resource type. -/

#guard resourceTypes.all fun A =>
  decide (typeOf ["id", "hint", "s"] [idTy, idTy, Pool.cellTy A]
      (Pool.leaseStep (var "id") (var "hint") (var "s")) =
    some (.prod (leaseReplyTy A) (Pool.cellTy A)))
#guard resourceTypes.all fun A =>
  decide (typeOf ["item", "lease", "s"] [.nat, .nat, Pool.cellTy A]
      (Pool.returnStep (var "item") (var "lease") (var "s")) =
    some (.prod returnReplyTy (Pool.cellTy A)))
#guard resourceTypes.all fun A =>
  decide (typeOf ["count", "s"] [.nat, Pool.cellTy A]
      (Pool.selectStep (var "count") (var "s")) =
    some (.prod selectReplyTy (Pool.cellTy A)))
#guard resourceTypes.all fun A =>
  decide (typeOf ["id", "s"] [idTy, Pool.cellTy A] (Pool.withdrawStep (var "id") (var "s")) =
    some (.prod .unit (Pool.cellTy A)))
#guard resourceTypes.all fun A =>
  decide (typeOf ["s"] [Pool.cellTy A] (Pool.closeStep (var "s")) =
    some (.prod closeReplyTy (Pool.cellTy A)))
-- A count and two stamps that are literals are typed too: the scenarios write them so.
#guard decide (typeOf ["s"] [Pool.cellTy .nat] (Pool.selectStep (nat 2) (var "s")) =
  some (.prod selectReplyTy (Pool.cellTy .nat)))
#guard decide (typeOf ["s"] [Pool.cellTy .nat] (Pool.returnStep (nat 0) (nat 0) (var "s")) =
  some (.prod returnReplyTy (Pool.cellTy .nat)))

-- Red controls of the scope. A request's identity at a number has no type: `sameHandle` takes
-- two handles of one kind. A stamp at a Boolean has none, and a count at a string has none.
#guard (typeOf ["id", "hint", "s"] [.nat, idTy, Pool.cellTy .nat]
  (Pool.leaseStep (var "id") (var "hint") (var "s"))).isNone
#guard (typeOf ["item", "lease", "s"] [.bool, .nat, Pool.cellTy .nat]
  (Pool.returnStep (var "item") (var "lease") (var "s"))).isNone
#guard (typeOf ["item", "lease", "s"] [.nat, idTy, Pool.cellTy .nat]
  (Pool.returnStep (var "item") (var "lease") (var "s"))).isNone
#guard (typeOf ["count", "s"] [.string, Pool.cellTy .nat]
  (Pool.selectStep (var "count") (var "s"))).isNone
-- A hint at a `Deferred` of a number has none: a `Deferred` is invariant in its answer.
#guard (typeOf ["id", "hint", "s"] [idTy, .deferredOf .nat .never, Pool.cellTy .nat]
  (Pool.leaseStep (var "id") (var "hint") (var "s"))).isNone
-- A step over an item in place of the cell has none.
#guard (typeOf ["s"] [Pool.itemTy .nat] (Pool.closeStep (var "s"))).isNone
#guard (typeOf ["count", "s"] [.nat, Pool.itemTy .nat]
  (Pool.selectStep (var "count") (var "s"))).isNone
-- At a resource type that is not its own normal form the lease step does not answer the
-- stated type: the theorems take the normal form as a premise.
#guard unnormalTypes.all fun A =>
  !decide (typeOf ["id", "hint", "s"] [idTy, idTy, Pool.cellTy A]
      (Pool.leaseStep (var "id") (var "hint") (var "s")) =
    some (.prod (leaseReplyTy A) (Pool.cellTy A)))

/-! ## 3. The steps' sizes, and the reader's domain

The term language has no local binding, so a step repeats its passes. The measures are the
Queue battery's two algebras of the generated term fold: nodes, then folds. -/

#guard measure ["id", "hint", "s"] (Pool.leaseStep (var "id") (var "hint") (var "s")) =
  some (166, 7)
#guard measure ["item", "lease", "s"] (Pool.returnStep (var "item") (var "lease") (var "s")) =
  some (69, 2)
#guard measure ["count", "s"] (Pool.selectStep (var "count") (var "s")) = some (11, 0)
#guard measure ["id", "s"] (Pool.withdrawStep (var "id") (var "s")) = some (22, 1)
#guard measure ["s"] (Pool.closeStep (var "s")) = some (11, 0)
-- The passes. The lease's two folds over the items hold the fold of the front stamp in their
-- bodies: two folds each.
#guard measure ["s"] (Pool.headStamp (var "s")) = some (7, 1)
#guard measure ["s"] (Pool.marked (var "s")) = some (29, 2)
#guard measure ["s"] (Pool.leasedOf (var "s")) = some (29, 2)
#guard measure ["item", "lease", "s"] (Pool.heldBy (var "item") (var "lease") (var "s")) =
  some (18, 1)
#guard measure ["item", "lease", "s"] (Pool.freed (var "item") (var "lease") (var "s")) =
  some (28, 1)
#guard measure ["id", "s"] (Pool.withdrawn (var "id") (var "s")) = some (20, 1)
-- The initial value folds nothing: 14 nodes at one resource, and 12 more for each resource.
#guard measure [] (Pool.initial .nat [nat 1]) = some (14, 0)
#guard measure [] (Pool.initial .nat [nat 1, nat 2]) = some (26, 0)

-- No fold of a step states its accumulator's type, so each step is inside the reader's domain.
#guard ([Pool.leaseStep (var "a") (var "b") (var "s"),
    Pool.returnStep (var "c") (var "c") (var "s"), Pool.selectStep (var "c") (var "s"),
    Pool.withdrawStep (var "a") (var "s"), Pool.closeStep (var "s")].map
  fun src => (termAt ["a", "b", "c", "s"] src).map (·.unannotated)) = List.replicate 5 (some true)

/-! ## 4. A caller's variable under each pass that folds

Each pass places its caller's term in a fold's body. The controls hand each pass a caller's
variable named `acc` or `item`: the names that a fold with fixed names would bind
(`Test/Program/FoldHygiene.lean` holds that capture). A control compares the pass's value under
those names with its value under names that no fold binds. -/

/-- A term's value at a scope of names and their values. -/
def valueAt (names : List String) (values : List Val) (src : TermSrc) : Option Val :=
  (termAt names src).bind (evalTerm values)

/-- The scope in which the controls' cells are built: four identities and a hint. -/
def makers : List String := ["a", "b", "c", "d", "h"]

def makerValues : List Val :=
  [Val.promise ⟨1⟩, Val.promise ⟨2⟩, Val.promise ⟨3⟩, Val.promise ⟨4⟩, Val.promise ⟨9⟩]

/-- The cell's next value of one step, over the cell's value. A cell is built step by step: a
step term holds its cell's source many times, so a step inside a step is a large term. -/
def afterStep (step : TermSrc → TermSrc) (cell : Val) : Option Val :=
  valueAt (makers ++ ["cell"]) (makerValues ++ [cell]) (tupleAt (step (var "cell")) 1)

/-- Two items, both leased, by the requests `c` and `d`. The requests `a` and `b` wait. -/
def busyCell : Option Val := do
  let cell ← valueAt [] [] (Pool.initial .nat [nat 7, nat 8])
  let cell ← afterStep (Pool.leaseStep (var "c") (var "h")) cell
  let cell ← afterStep (Pool.leaseStep (var "d") (var "h")) cell
  let cell ← afterStep (Pool.leaseStep (var "a") (var "h")) cell
  afterStep (Pool.leaseStep (var "b") (var "h")) cell

/-- The same, after the lease 0 returned: the item 0 is idle beside the two waiters. -/
def idleCell : Option Val := busyCell.bind (afterStep (Pool.returnStep (nat 0) (nat 0)))

def busy : Val := busyCell.getD .unit
def idle : Val := idleCell.getD .unit

-- Both cells have a value, and they differ.
#guard busyCell.isSome && idleCell.isSome && busy != idle

/-- A pass keeps its caller's reading: its value under the clashing names is its value under
the plain names, and it has one. -/
def keeps (plain clash : Option Val) : Bool := plain.isSome && plain == clash

-- `withdrawn`: the request's identity, named `acc` and then `item`.
#guard keeps
  (valueAt ["x", "cell"] [Val.promise ⟨1⟩, busy] (Pool.withdrawn (var "x") (var "cell")))
  (valueAt ["acc", "cell"] [Val.promise ⟨1⟩, busy] (Pool.withdrawn (var "acc") (var "cell")))
#guard keeps
  (valueAt ["x", "cell"] [Val.promise ⟨2⟩, busy] (Pool.withdrawn (var "x") (var "cell")))
  (valueAt ["item", "cell"] [Val.promise ⟨2⟩, busy] (Pool.withdrawn (var "item") (var "cell")))
-- The removal reads the identity: the two requests give two lists, and a third gives the cell.
#guard valueAt ["x", "cell"] [Val.promise ⟨1⟩, busy] (Pool.withdrawn (var "x") (var "cell")) !=
  valueAt ["x", "cell"] [Val.promise ⟨2⟩, busy] (Pool.withdrawn (var "x") (var "cell"))
#guard valueAt ["x", "cell"] [Val.promise ⟨3⟩, busy] (Pool.withdrawn (var "x") (var "cell")) =
  some busy
-- `marked` and `leasedOf`: the cell's own source, named `acc` and then `item`.
#guard ["acc", "item"].all fun name =>
  keeps (valueAt ["cell"] [idle] (Pool.marked (var "cell")))
      (valueAt [name] [idle] (Pool.marked (var name))) &&
    keeps (valueAt ["cell"] [idle] (Pool.leasedOf (var "cell")))
      (valueAt [name] [idle] (Pool.leasedOf (var name)))
-- `heldBy` and `freed`: the item's stamp named `acc`, and the lease's stamp named `item`.
#guard keeps
  (valueAt ["i", "l", "cell"] [.nat 1, .nat 1, busy] (Pool.heldBy (var "i") (var "l") (var "cell")))
  (valueAt ["acc", "item", "cell"] [.nat 1, .nat 1, busy]
    (Pool.heldBy (var "acc") (var "item") (var "cell")))
#guard keeps
  (valueAt ["i", "l", "cell"] [.nat 1, .nat 1, busy] (Pool.freed (var "i") (var "l") (var "cell")))
  (valueAt ["acc", "item", "cell"] [.nat 1, .nat 1, busy]
    (Pool.freed (var "acc") (var "item") (var "cell")))
-- The pass reads both stamps: the lease 1 holds the item 1, and the lease 0 does not.
#guard valueAt ["i", "l", "cell"] [.nat 1, .nat 1, busy]
    (Pool.heldBy (var "i") (var "l") (var "cell")) = some (.bool true)
#guard valueAt ["i", "l", "cell"] [.nat 1, .nat 0, busy]
    (Pool.heldBy (var "i") (var "l") (var "cell")) = some (.bool false)

/-- Red control of the hygiene: `marked` with the fold's two names fixed. -/
def markedFixed (s : TermSrc) : TermSrc :=
  fold "acc" "item" none (field s "items") (noneOf (field s "items"))
    (snoc (var "acc")
      (ifT (app "eq" [field (var "item") "stamp", Pool.headStamp s])
        (Pool.leasedAs (field s "next") (var "item")) (var "item")))

/-- Red control of the hygiene: `heldBy` with the fold's two names fixed. -/
def heldByFixed (i l s : TermSrc) : TermSrc :=
  fold "acc" "item" none (field s "items") (bool false)
    (orT (var "acc") (Pool.holdsT i l (var "item")))

-- Under names that the fixed passes do not bind, they answer as the library's passes.
#guard keeps (valueAt ["cell"] [idle] (Pool.marked (var "cell")))
  (valueAt ["cell"] [idle] (markedFixed (var "cell")))
#guard keeps
  (valueAt ["i", "l", "cell"] [.nat 1, .nat 1, busy] (Pool.heldBy (var "i") (var "l") (var "cell")))
  (valueAt ["i", "l", "cell"] [.nat 1, .nat 1, busy] (heldByFixed (var "i") (var "l") (var "cell")))
-- The capture. The caller's cell `acc` reads the fold's accumulator, a list and no record, so
-- the fixed pass has no value.
#guard (valueAt ["acc"] [idle] (markedFixed (var "acc"))).isNone
-- The caller's stamp `acc` reads the accumulator, a Boolean and no number: no value.
#guard (valueAt ["acc", "item", "cell"] [.nat 1, .nat 1, busy]
  (heldByFixed (var "acc") (var "item") (var "cell"))).isNone
-- A minted name is no name an author can write: the scope reader refuses it.
#guard (termAt [Env.mint {} "item"] (var (Env.mint {} "item"))).isNone

/-! ## 5. The typing theorems at a scope of names

Each example is an instance of a theorem, and no evaluation of the checker. -/

/-- The lease step at its own scope: an author's variable is a caller's term under each fold
(`capturedTy_var`). -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig ["id", "hint", "s"] [idTy, idTy, Pool.cellTy .nat]
        (Pool.leaseStep (var "id") (var "hint") (var "s")) =
      some (.prod (leaseReplyTy .nat) (Pool.cellTy .nat)) := by
  apply typeAt_of_types
  exact leaseStep_types sig atoms rfl (idSrc := var "id") (hintSrc := var "hint")
    (cellSrc := var "s") (env := { names := ["id", "hint", "s"] }) (path := [])
    (types := [idTy, idTy, Pool.cellTy .nat]) rfl (capturedTy_var rfl rfl rfl)
    (types_var rfl rfl rfl) (capturedTy_var rfl rfl rfl) false

/-- The return step at its own scope: the two stamps are caller's terms under its folds. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig ["item", "lease", "s"] [.nat, .nat, Pool.cellTy .string]
        (Pool.returnStep (var "item") (var "lease") (var "s")) =
      some (.prod returnReplyTy (Pool.cellTy .string)) := by
  apply typeAt_of_types
  exact returnStep_types sig atoms rfl (itemSrc := var "item") (leaseSrc := var "lease")
    (cellSrc := var "s") (env := { names := ["item", "lease", "s"] }) (path := [])
    (types := [.nat, .nat, Pool.cellTy .string]) rfl (capturedTy_var rfl rfl rfl)
    (capturedTy_var rfl rfl rfl) (types_var rfl rfl rfl) false

/-- The selection and the close's first step at their own scopes: no capture. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig ["count", "s"] [.nat, Pool.cellTy .nat] (Pool.selectStep (var "count") (var "s")) =
      some (.prod selectReplyTy (Pool.cellTy .nat)) := by
  apply typeAt_of_types
  exact selectStep_types sig atoms rfl (countSrc := var "count") (cellSrc := var "s")
    (env := { names := ["count", "s"] }) (path := []) (types := [.nat, Pool.cellTy .nat])
    (types_var rfl rfl rfl) (types_var rfl rfl rfl) false

example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig ["s"] [Pool.cellTy .nat] (Pool.closeStep (var "s")) =
      some (.prod closeReplyTy (Pool.cellTy .nat)) := by
  apply typeAt_of_types
  exact closeStep_types sig atoms rfl (cellSrc := var "s") (env := { names := ["s"] })
    (path := []) (types := [Pool.cellTy .nat]) (types_var rfl rfl rfl) false

/-- The initial value, at two resources that are a caller's variables. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig ["r", "q"] [.nat, .nat] (Pool.initial .nat [var "r", var "q"]) =
      some (Pool.cellTy .nat) := by
  apply typeAt_of_types
  refine initial_types sig atoms (A := .nat) (by decide) (List.cons_ne_nil _ _)
    (env := { names := ["r", "q"] }) (path := []) (types := [.nat, .nat]) (fun r member => ?_)
    false
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact types_var rfl rfl rfl
  · exact types_var rfl rfl rfl

/-! ### The lease step in a row of `Ref.modifyWith`

A wrapper binds the pool's handle, the request's identity and its hint with `bindWith`, whose
names are minted. It writes the lease step as the term of `Ref.modifyWith`, whose binder for
the cell's current value is minted too. So the step's scope holds four minted names. Each
capture premise is discharged there with no assumption: the identity by `capturedTy_answer`,
and the cell's own source by `capturedTy_minted`. -/

/-- The three names that three nested `bindWith`s mint: they differ by their depths. -/
def poolName : String := Env.mint {} "answer"
def idName : String := Env.mint { names := [poolName] } "answer"
def hintName : String := Env.mint { names := [poolName, idName] } "answer"

/-- The scope of the row, and the name of the cell's current value under it. -/
def rowScope : Env := { names := [poolName, idName, hintName] }
def currentName : String := rowScope.mint "current"

/-- The scope of the step: the row's scope under the row's own binder. -/
def stepScope : Env := rowScope.push [currentName]

/-- The identity is the scope's second level: no later binder has its name. -/
theorem stepScope_id : stepScope.names.resolve idName = some 1 := by
  refine resolve_unshadowed [poolName] idName [hintName, currentName] fun name member => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact later_mint_ne_answer (b := 97) (by decide) (by decide) (Or.inl rfl)
  · exact mint_current_ne_answer _ _

/-- The hint is the scope's third level. -/
theorem stepScope_hint : stepScope.names.resolve hintName = some 2 := by
  refine resolve_unshadowed [poolName, idName] hintName [currentName] fun name member => ?_
  rw [List.mem_singleton.mp member]
  exact mint_current_ne_answer _ _

/-- The cell's current value is the scope's last level. -/
theorem stepScope_cell : stepScope.names.resolve currentName = some 3 :=
  resolve_last [poolName, idName, hintName] currentName

/-- The types of the step's scope: the pool's handle, the two `Deferred`s and the cell. -/
def stepTypes : List Ty := [.refOf (Pool.cellTy .nat), idTy, idTy, Pool.cellTy .nat]

/-- **The lease step in a row of `Ref.modifyWith`, typed with no assumed capture.** The folds
of the step mint their names at the step's scope. Those names begin with other bytes than
`current`, so the cell's own source keeps its type under them. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) :
    typeAt sig stepScope.names stepTypes
        (Pool.leaseStep (minted idName) (minted hintName) (minted currentName)) =
      some (.prod (leaseReplyTy .nat) (Pool.cellTy .nat)) := by
  apply typeAt_of_types
  exact leaseStep_types sig atoms rfl (idSrc := minted idName) (hintSrc := minted hintName)
    (cellSrc := minted currentName) (env := stepScope) (path := []) (types := stepTypes) rfl
    (capturedTy_answer (outer := { names := [poolName] }) stepScope_id rfl)
    (types_minted stepScope_hint rfl)
    (capturedTy_minted stepScope_cell rfl
      (mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) _ _)
      (mint_ne_of_head (b := 105) (c := 99) (by decide) (by decide) (by decide) _ _))
    false

/-- A program that binds a pool, an identity and a hint with `bindWith`, then leases. -/
def leasing : Src NativeOp :=
  bindWith (Ref.make (Pool.initial .nat [nat 1])) fun pool =>
    bindWith (Deferred.make .unit .never) fun id =>
      bindWith (Deferred.make .unit .never) fun hint =>
        Ref.modifyWith pool (Pool.leaseStep id hint)

/-- The term of a program's last row: the row of `Ref.modifyWith` under three binders. -/
def rowTerm : Eff NativeOp → Option Term
  | .bind _ (.bind _ (.bind _ (.perform (.refModifyWith f) _))) => some f
  | _ => none

-- The program's step term is the step's source at the scope of the example: the scope at
-- which the capture is stated is the scope that the program elaborates the step in.
#guard ((elaborate leasing).toOption.bind rowTerm).isSome &&
  (elaborate leasing).toOption.bind rowTerm ==
    (Pool.leaseStep (minted idName) (minted hintName) (minted currentName) stepScope []).toOption
-- The checker types the step's term there.
#guard decide (typeOf stepScope.names stepTypes
    (Pool.leaseStep (minted idName) (minted hintName) (minted currentName)) =
  some (.prod (leaseReplyTy .nat) (Pool.cellTy .nat)))

/-! ## 6. The connector to the store

`step_keeps_cell` (`src/Effect4/Laws/Modules/Store.lean`) reads a step's `termTy` equation:
one `Ref.modify` of the step keeps the cell a member of the cell's type. The tree that a step's
reading evaluates is the tree that the step's theorem types (`Types.tree`). The cell's value is
the scope's last name. -/

/-- **A lease keeps the cell a member of its type**, at every scope and for every caller's
terms: its reply is a Boolean and an option of an item, and its stored value is a cell. -/
theorem leaseStep_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {idSrc hintSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : (tys ++ [Pool.cellTy A]).length = env.names.length)
    (typesId : CapturedTy sig idSrc env path (tys ++ [Pool.cellTy A]) idTy)
    (typesHint : TypesEach sig hintSrc env path (tys ++ [Pool.cellTy A]) idTy)
    (typesCell : CapturedTy sig cellSrc env path (tys ++ [Pool.cellTy A]) (Pool.cellTy A))
    (typedEnv : Typed.EnvTyped w tys captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell (Pool.cellTy A))
    (reads : Reads (Pool.leaseStep idSrc hintSrc cellSrc) env path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    Typed.Fits w reply (leaseReplyTy A) ∧ Typed.Fits w next (Pool.cellTy A) := by
  obtain ⟨f, tree, value⟩ := reads
  exact step_keeps_cell sig atoms typedEnv
    ((leaseStep_types sig atoms canonical depth typesId typesHint typesCell false).tree tree)
    held member value

/-- **A selection keeps the cell a member of its type**, at every scope: its reply is a list of
waiters. -/
theorem selectStep_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {countSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (typesCount : TypesEach sig countSrc env path (tys ++ [Pool.cellTy A]) .nat)
    (typesCell : TypesEach sig cellSrc env path (tys ++ [Pool.cellTy A]) (Pool.cellTy A))
    (typedEnv : Typed.EnvTyped w tys captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell (Pool.cellTy A))
    (reads : Reads (Pool.selectStep countSrc cellSrc) env path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    Typed.Fits w reply selectReplyTy ∧ Typed.Fits w next (Pool.cellTy A) := by
  obtain ⟨f, tree, value⟩ := reads
  exact step_keeps_cell sig atoms typedEnv
    ((selectStep_types sig atoms canonical typesCount typesCell false).tree tree) held member
    value

/-- **A return keeps the cell a member of its type**, at every scope. -/
theorem returnStep_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {itemSrc leaseSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : (tys ++ [Pool.cellTy A]).length = env.names.length)
    (typesItem : CapturedTy sig itemSrc env path (tys ++ [Pool.cellTy A]) .nat)
    (typesLease : CapturedTy sig leaseSrc env path (tys ++ [Pool.cellTy A]) .nat)
    (typesCell : TypesEach sig cellSrc env path (tys ++ [Pool.cellTy A]) (Pool.cellTy A))
    (typedEnv : Typed.EnvTyped w tys captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell (Pool.cellTy A))
    (reads : Reads (Pool.returnStep itemSrc leaseSrc cellSrc) env path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    Typed.Fits w reply returnReplyTy ∧ Typed.Fits w next (Pool.cellTy A) := by
  obtain ⟨f, tree, value⟩ := reads
  exact step_keeps_cell sig atoms typedEnv
    ((returnStep_types sig atoms canonical depth typesItem typesLease typesCell false).tree tree)
    held member value

/--
info: 'Test.Program.PoolSteps.leaseStep_keeps_cell' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms leaseStep_keeps_cell

/--
info: 'Test.Program.PoolSteps.selectStep_keeps_cell' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms selectStep_keeps_cell

/--
info: 'Test.Program.PoolSteps.returnStep_keeps_cell' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms returnStep_keeps_cell

/--
info: Test.Program.PoolSteps.leaseStep_keeps_cell: proved; nearest []; 0 lemmas, 0 definitions
Test.Program.PoolSteps.selectStep_keeps_cell: proved; nearest []; 0 lemmas, 0 definitions
Test.Program.PoolSteps.returnStep_keeps_cell: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status leaseStep_keeps_cell selectStep_keeps_cell returnStep_keeps_cell

/-! ## 7. The pinned outputs

Each typing theorem's axioms, and its standing as the plan derives it from its proof. The
counts are of this battery's tree, which holds no step of a proof. -/

/-- info: 'Effect4.Pool.Model.initial_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_types

/-- info: 'Effect4.Pool.Model.leaseStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms leaseStep_types

/-- info: 'Effect4.Pool.Model.returnStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms returnStep_types

/-- info: 'Effect4.Pool.Model.selectStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selectStep_types

/-- info: 'Effect4.Pool.Model.withdrawStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms withdrawStep_types

/-- info: 'Effect4.Pool.Model.closeStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms closeStep_types

/-- info: 'Effect4.Program.nativeAtomTy_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nativeAtomTy_eq

/-- info: 'Effect4.Modules.types_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_eq

/-- info: 'Effect4.Modules.types_listOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_listOf

/--
info: Effect4.Pool.Model.initial_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.leaseStep_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.returnStep_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.selectStep_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.withdrawStep_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.closeStep_types: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status initial_types leaseStep_types returnStep_types selectStep_types withdrawStep_types
  closeStep_types

end Test.Program.PoolSteps
