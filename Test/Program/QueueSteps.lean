import Effect4.Modules.Queue.Steps
import Effect4.Laws.Modules.Queue.Typing
import Effect4.Codegen.ListFold

/-!
# The Queue's cell and its steps: finite controls of the library module (decisions row 255)

The module is `src/Effect4/Modules/Queue/`: the cell's type and initial value (`Cell.lean`), and
the six step terms (`Steps.lean`). This battery holds the finite controls of the module alone:
the cell's type and value, and each step's type, size and reading domain. The comparison with
the abstract model is `Test/Program/QueueAgreement.lean`. The runs on the machine are
`Test/Program/QueueScenarios.lean`.

Placement. The typing controls are finite instances of the typing statements of
`src/Effect4/Laws/Modules/Queue/Typing.lean` (concept `store-typing`, requirement R4). Every
guard is a finite check at the listed message types. None proves a statement at every message
type, and none states agreement with the model. The seven statements are proved at every
message type in the law graph, and the guards stay as their finite controls and red controls.
The pins of the five steps of a `Ref.modify` are in `Test/Program/QueueTyping.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Test.Program.QueueSteps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

open Effect4.Queue.Model (MessageTy takeReplyTy offerReplyTy pollReplyTy wakeReplyTy)

/-- A source term's tree at a scope of names. -/
def termAt (names : List String) (src : TermSrc) : Option Term :=
  (src { names := names } []).toOption

/-- The checker's type of a source term, at a scope of names and their types: the function of
the typing statements, at the native signature. -/
def typeAt (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  Modules.typeAt nativeSignature names types src

/-! ## 1. The cell -/

/-- Message types that are their own normal form. The cell is checked at each. -/
def messageTypes : List Ty :=
  [.nat, .string, .bool, .unit, .never, .unknown, .option .nat, .list .string,
   .union .nat .string, .prod .nat .string, .lit "x", .refOf .nat, .deferredOf .nat .never,
   .record [("a", false, .nat), ("b", true, .string)], .map .string .nat,
   .tuple [.nat, .string, .bool], .fiberOf .nat .never, .exitOf .nat .string, .causeOf .string,
   .int, .number, .null, .undefined, .bytes, Queue.cellTy .nat,
   .list (.union .nat (.lit "a")), .except .string .nat]

/-- Message types that are not their own normal form. -/
def unnormalTypes : List Ty :=
  [.union .nat .nat, .tuple [.nat, .string], .union .string (.lit "x"),
   .record [("b", false, .nat), ("a", false, .nat)], .prod (.union .nat .string) .bool]

/-- Message types that formation refuses: a repeated field, a map key that is no string, and a
`Deferred` whose error column the error alphabet does not admit. -/
def malformedTypes : List Ty :=
  [.record [("a", false, .nat), ("a", false, .string)], .map .nat .nat,
   .deferredOf .nat (.refOf .nat)]

#guard messageTypes.all fun A => decide (A.normalize = A)
#guard unnormalTypes.all fun A => decide (A.normalize ≠ A)

-- Each written declaration normalizes to its type: the fields in the canonical order.
#guard decide (Ty.normalize (.record Queue.takerFields) = Queue.takerTy)
#guard messageTypes.all fun A =>
  decide (Ty.normalize (.record (Queue.offerFields A)) = Queue.offerTy A) &&
    decide (Ty.normalize (.record (Queue.cellFields A)) = Queue.cellTy A)

-- The checker answers the cell's type for the initial value, at each message type and in any
-- scope.
#guard messageTypes.all fun A =>
  decide (typeAt [] [] (Queue.empty A 2) = some (Queue.cellTy A)) &&
    decide (typeAt ["x"] [.string] (Queue.empty A 0) = some (Queue.cellTy A))
-- Red control: at a message type that is not its own normal form, the checker answers the
-- cell's type at the normal form, and not at the written type.
#guard unnormalTypes.all fun A =>
  decide (typeAt [] [] (Queue.empty A 2) = some (Queue.cellTy A.normalize)) &&
    decide (typeAt [] [] (Queue.empty A 2) ≠ some (Queue.cellTy A))
-- Red control: at a message type that formation refuses, the initial value has no type.
#guard malformedTypes.all fun A => (typeAt [] [] (Queue.empty A 2)).isNone

-- The initial value: the record frame of the four fields in the canonical order, with the
-- capacity and three empty lists. The message type has no part in the value.
#guard messageTypes.all fun A =>
  decide (((termAt [] (Queue.empty A 2)).bind (evalTerm [])) = some
    (.ctor 0 [.list [.str "cap", .str "msgs", .str "offers", .str "takers"],
      .list [.nat 2, .list [], .list [], .list []]]))

-- Each listed message type is one that the checker types in a cell, and no red type is.
#guard messageTypes.all fun A => decide (MessageTy A)
#guard (unnormalTypes ++ malformedTypes).all fun A => !decide (MessageTy A)

/-! ## 2. The steps' types

Each guard is the statement of one typing theorem of
`src/Effect4/Laws/Modules/Queue/Typing.lean`, at each listed message type. -/

def takeTyped (A : Ty) : Bool :=
  decide (typeAt ["id", "hint", "s"] [idTy, idTy, Queue.cellTy A]
    (Queue.takeStep A (var "id") (var "hint") (var "s")) =
      some (.prod (takeReplyTy A) (Queue.cellTy A)))

def offerTyped (A : Ty) : Bool :=
  decide (typeAt ["id", "hint", "a", "s"] [idTy, Queue.answerTy, A, Queue.cellTy A]
    (Queue.offerStep A (var "id") (var "hint") (var "a") (var "s")) =
      some (.prod offerReplyTy (Queue.cellTy A)))

def pollTyped (A : Ty) : Bool :=
  decide (typeAt ["s"] [Queue.cellTy A] (Queue.pollStep A (var "s")) =
    some (.prod (pollReplyTy A) (Queue.cellTy A)))

def sizeTyped (A : Ty) : Bool :=
  decide (typeAt ["s"] [Queue.cellTy A] (Queue.sizeStep A (var "s")) = some .nat)

def withdrawTakeTyped (A : Ty) : Bool :=
  decide (typeAt ["id", "s"] [idTy, Queue.cellTy A]
    (Queue.withdrawTake A (var "id") (var "s")) = some (.prod wakeReplyTy (Queue.cellTy A)))

def withdrawOfferTyped (A : Ty) : Bool :=
  decide (typeAt ["id", "s"] [idTy, Queue.cellTy A]
    (Queue.withdrawOffer A (var "id") (var "s")) = some (.prod wakeReplyTy (Queue.cellTy A)))

#guard messageTypes.all takeTyped
#guard messageTypes.all offerTyped
#guard messageTypes.all pollTyped
#guard messageTypes.all sizeTyped
#guard messageTypes.all withdrawTakeTyped
#guard messageTypes.all withdrawOfferTyped

-- Red control of the premise: at a message type that is not its own normal form, no step that
-- answers the cell has the stated type. The checker answers the cell's type at the normal form.
#guard unnormalTypes.all fun A =>
  !takeTyped A && !offerTyped A && !pollTyped A && !withdrawTakeTyped A && !withdrawOfferTyped A
#guard unnormalTypes.all fun A =>
  decide (typeAt ["s"] [Queue.cellTy A] (Queue.pollStep A (var "s")) =
    some (.prod (pollReplyTy A.normalize) (Queue.cellTy A.normalize)))
-- Red controls of the scope. A request's identity at a number has no type: `sameHandle` takes
-- two handles of one kind. An offerer's hint at a taker's hint type has none: a `Deferred` is
-- invariant in its answer. A message at another type has none.
#guard (typeAt ["id", "hint", "s"] [.nat, idTy, Queue.cellTy .nat]
  (Queue.takeStep .nat (var "id") (var "hint") (var "s"))).isNone
#guard (typeAt ["id", "hint", "a", "s"] [idTy, idTy, .nat, Queue.cellTy .nat]
  (Queue.offerStep .nat (var "id") (var "hint") (var "a") (var "s"))).isNone
#guard (typeAt ["id", "hint", "a", "s"] [idTy, Queue.answerTy, .string, Queue.cellTy .nat]
  (Queue.offerStep .nat (var "id") (var "hint") (var "a") (var "s"))).isNone
-- A message below the cell's message type is typed: a literal in a cell of strings.
#guard decide (typeAt ["id", "hint", "a", "s"]
    [idTy, Queue.answerTy, .lit "x", Queue.cellTy .string]
    (Queue.offerStep .string (var "id") (var "hint") (var "a") (var "s")) =
  some (.prod offerReplyTy (Queue.cellTy .string)))

/-! ## 3. The steps' sizes, and the reader's domain

The term language has no local binding, so a step repeats its passes (decisions row 255). The
measures are algebras of the generated term fold: one field for each constructor. -/

/-- The nodes of a term. -/
def nodesAlgebra : TermAlgebra (fun _ => Nat) where
  term_var _ := 1
  term_lit _ := 1
  term_app _ args := 1 + args
  term_record _ _ values := 1 + values
  term_field _ target _ := 1 + target
  term_recordSet target _ value := 1 + target + value
  term_tupleAt target _ := 1 + target
  term_fold _ list init body := 1 + list + init + body
  terms_nil := 0
  terms_cons head tail := head + tail

/-- The folds of a term. -/
def foldsAlgebra : TermAlgebra (fun _ => Nat) where
  term_var _ := 0
  term_lit _ := 0
  term_app _ args := args
  term_record _ _ values := values
  term_field _ target _ := target
  term_recordSet target _ value := target + value
  term_tupleAt target _ := target
  term_fold _ list init body := 1 + list + init + body
  terms_nil := 0
  terms_cons head tail := head + tail

/-- A step's nodes and folds, at the scope of its arguments. -/
def measure (names : List String) (src : TermSrc) : Option (Nat × Nat) :=
  (termAt names src).map fun t => (cata_term nodesAlgebra t, cata_term foldsAlgebra t)

-- Each step's nodes and folds. The message type does not change a measure.
#guard measure ["id", "hint", "s"] (Queue.takeStep .nat (var "id") (var "hint") (var "s")) =
  some (290, 9)
#guard measure ["id", "hint", "a", "s"]
  (Queue.offerStep .nat (var "id") (var "hint") (var "a") (var "s")) = some (101, 0)
#guard measure ["s"] (Queue.pollStep .nat (var "s")) = some (120, 1)
#guard measure ["s"] (Queue.sizeStep .nat (var "s")) = some (3, 0)
#guard measure ["id", "s"] (Queue.withdrawTake .nat (var "id") (var "s")) = some (69, 3)
#guard measure ["id", "s"] (Queue.withdrawOffer .nat (var "id") (var "s")) = some (35, 1)
-- The accept pass's one fold.
#guard measure [] (Queue.gained (nat 1) nilT nilT) = some (16, 1)
#guard messageTypes.all fun A =>
  measure ["id", "hint", "s"] (Queue.takeStep A (var "id") (var "hint") (var "s")) ==
    some (290, 9)

-- No fold of a step states its accumulator's type, so each step is inside the reader's domain.
#guard ((termAt ["id", "hint", "s"] (Queue.takeStep .nat (var "id") (var "hint") (var "s"))).map
  (·.unannotated)) = some true
#guard ((termAt ["id", "hint", "a", "s"]
  (Queue.offerStep .nat (var "id") (var "hint") (var "a") (var "s"))).map (·.unannotated)) =
    some true
#guard ((termAt ["s"] (Queue.pollStep .nat (var "s"))).map (·.unannotated)) = some true
#guard ((termAt ["s"] (Queue.sizeStep .nat (var "s"))).map (·.unannotated)) = some true
#guard ((termAt ["id", "s"] (Queue.withdrawTake .nat (var "id") (var "s"))).map
  (·.unannotated)) = some true
#guard ((termAt ["id", "s"] (Queue.withdrawOffer .nat (var "id") (var "s"))).map
  (·.unannotated)) = some true
-- Red control of the predicate: a fold that states a type is outside the domain.
#guard ((termAt ["xs"] (fold "acc" "item" (some (.list .nat)) (var "xs") nilT
  (var "acc"))).map (·.unannotated)) = some false

/-! ## 4. A caller's variable under each helper

Each helper that folds places its caller's term in the fold's body. The controls hand each
helper a caller's variable named `acc` or `item`: the names that a fold with fixed names would
bind (`Test/Program/FoldHygiene.lean` holds that capture). Request `n` has the identity handle
`n`. The takers 1 and 2 wait, in that order, and the offers 3 and 1 are pending. -/

def hygieneNames : List String := ["acc", "item", "other", "h1", "h2", "h3", "fresh"]

def hygieneValues : List Val :=
  [Val.promise ⟨1⟩, Val.promise ⟨2⟩, Val.promise ⟨3⟩, Val.promise ⟨11⟩, Val.promise ⟨12⟩,
   Val.promise ⟨13⟩, Val.promise ⟨99⟩]

/-- A term's value in the scope of the controls. -/
def valueAt (src : TermSrc) : Option Val :=
  (termAt hygieneNames src).bind (evalTerm hygieneValues)

def listOf (xs : List TermSrc) : TermSrc :=
  xs.foldr (fun x acc => app "cons" [x, acc]) nilT

def taker1 : TermSrc := Queue.mkTaker (var "acc") (var "h1")
def taker2 : TermSrc := Queue.mkTaker (var "item") (var "h2")
def takers : TermSrc := listOf [taker1, taker2]
def offer3 : TermSrc :=
  Queue.mkOffer .nat (var "other") (var "h3") (bool false) (listOf [nat 30])
def offer1 : TermSrc := Queue.mkOffer .nat (var "acc") (var "h1") (bool false) (listOf [nat 10])
def offers : TermSrc := listOf [offer3, offer1]

/-- A helper answers the value of an expected term. -/
def answers (helper expected : TermSrc) : Bool :=
  (valueAt helper).isSome && decide (valueAt helper = valueAt expected)

-- `enrolled`: the caller's `acc` and `item` are the waiting requests 1 and 2, and `other` is
-- not enrolled.
#guard answers (Queue.enrolled takers (var "acc")) (bool true)
#guard answers (Queue.enrolled takers (var "item")) (bool true)
#guard answers (Queue.enrolled takers (var "other")) (bool false)
-- `isHead`: request 1 is the earliest taker, and request 2 is not.
#guard answers (Queue.isHead takers (var "acc")) (bool true)
#guard answers (Queue.isHead takers (var "item")) (bool false)
-- `removeTaker`: one entry leaves, by the caller's variable.
#guard answers (Queue.removeTaker takers (var "item")) (listOf [taker1])
#guard answers (Queue.removeTaker takers (var "acc")) (listOf [taker2])
#guard answers (Queue.removeTaker takers (var "other")) takers
-- `renewHint`: the caller's identity and the caller's hint both stand in the body.
#guard answers (Queue.renewHint takers (var "item") (var "fresh"))
  (listOf [taker1, Queue.mkTaker (var "item") (var "fresh")])
#guard answers (Queue.renewHint takers (var "item") (var "acc"))
  (listOf [taker1, Queue.mkTaker (var "item") (var "acc")])
#guard answers (Queue.renewHint takers (var "acc") (var "item"))
  (listOf [Queue.mkTaker (var "acc") (var "item"), taker2])
-- `removeOffer`: one entry leaves, by the caller's variable.
#guard answers (Queue.removeOffer offers (var "acc")) (listOf [offer3])
#guard answers (Queue.removeOffer offers (var "other")) (listOf [offer1])
#guard answers (Queue.removeOffer offers (var "item")) offers
-- `gained`: no caller's term stands in its body. Its three arguments are read at the caller's
-- scope: one place, the buffer `[7]`, and two offers, of which the first enters.
#guard answers (Queue.gained (nat 1) (listOf [nat 7]) offers) (listOf [nat 7, nat 30])
#guard answers (Queue.gained (nat 2) (listOf [nat 7]) offers) (listOf [nat 7, nat 30, nat 10])
#guard answers (Queue.gained (nat 0) (listOf [nat 7]) offers) (listOf [nat 7])

/-- Red control of the hygiene: `enrolled` with the fold's two names fixed. -/
def enrolledFixed (takers id : TermSrc) : TermSrc :=
  fold "acc" "item" none takers (bool false)
    (orT (var "acc") (same (field (var "item") "id") id))

-- Under a name the fixed helper does not bind, it answers as the library's helper.
#guard answers (enrolledFixed takers (var "other")) (bool false)
-- The capture: the caller's `item` reads the folded taker, a record and no handle, so the
-- identity test refuses and the fixed helper has no value. The library's helper answers.
#guard (valueAt (enrolledFixed takers (var "item"))).isNone
#guard answers (Queue.enrolled takers (var "item")) (bool true)
-- A minted name is no name an author can write: the scope reader refuses it.
#guard (termAt [Env.mint {} "item"] (var (Env.mint {} "item"))).isNone

/-! ## 5. The two removals are the shared pass

The Queue's `removeTaker` and `removeOffer` are each one application of the shared removal pass
`removeById` (`src/Effect4/Modules/Words.lean`). Each is that pass as a function, by
definition: the kernel accepts the equality by `rfl`. Seat MOVE's comparison held the two names
by their types only (Codex's review), so the values are held here. -/

example : @Effect4.Queue.removeTaker = @Effect4.Modules.removeById := rfl
example : @Effect4.Queue.removeOffer = @Effect4.Modules.removeById := rfl

-- Red control, at the same type: another pass of two terms is no `removeById`. `enrolled`
-- answers a Boolean where the removal answers a list, so their trees differ at one scope.
example : @Effect4.Queue.enrolled ≠ @Effect4.Modules.removeById := fun same =>
  absurd
    (congrFun (congrFun (congrFun (congrFun same (var "xs")) (var "i")) { names := ["xs", "i"] })
      [])
    (by decide)

end Test.Program.QueueSteps
