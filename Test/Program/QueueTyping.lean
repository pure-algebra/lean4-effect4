import Effect4.Modules.Queue.Steps
import Effect4.Program.Authoring.Sugar
import Effect4.Laws.Modules.Queue.Typing
import Effect4.Laws.Modules.Queue.Steps
import Effect4.Laws.Modules.Store

/-!
# The Queue's steps typed at every message type: instances, red controls and pins (row 257)

The five steps of a `Ref.modify` are typed at every message type that the checker types in a
cell (`src/Effect4/Laws/Modules/Queue/Typing.lean`). The proofs read the checker's rules in
their introduction form (`src/Effect4/Laws/Program/Typing/TermIntro.lean`) through the judgment
`Types` (`src/Effect4/Laws/Modules/Checking.lean`). This battery holds what the theorems do not
say by themselves:

1. the statements at a record message type and at a message type that holds a handle;
2. a step's typing at a scope that is not the statement's own: a binder before the arguments,
   and a caller's term that is no variable;
3. an identity and a hint that `bindWith` binds, through the folds of a step, with no assumed
   capture, for values and for types, and the red control of the capture;
4. the red controls of the new rules, the literal flag, and a positional read of a reply;
5. the connector to the store: `step_keeps_cell` on a step's typing.

Placement. Concept `store-typing`, requirement R4, for the typing; concept
`translation-simulation`, requirement R10, for the capture of a minted name. Every guard is a
finite check, and every example is an instance of a theorem. None states agreement with the
model beyond the instance of `withdrawTake_agrees`, and none is a host run. The finite controls
of the seven statements at 27 message types stay in `Test/Program/QueueSteps.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Test.Program.QueueTyping

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Queue.Model
open Effect4.Modules

/-- The checker's type of a source term at a scope, at the native signature. -/
def typeOf (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  typeAt nativeSignature names types src

/-! ## 1. A record message type, and a message type that holds a handle

`MessageTy` holds at both, so each typing statement applies. The examples are instances of the
theorems, and no evaluation of the checker. -/

/-- A record message type, with an optional field. -/
def recordMessage : Ty := .record [("a", false, .nat), ("b", true, .string)]

/-- A message type that holds a handle. -/
def handleMessage : Ty := .deferredOf .nat .never

example : MessageTy recordMessage := by decide
example : MessageTy handleMessage := by decide

example :
    typeAt nativeSignature ["id", "hint", "s"]
        [idTy, idTy, Queue.cellTy recordMessage]
        (Queue.takeStep recordMessage (var "id") (var "hint") (var "s")) =
      some (.prod (takeReplyTy recordMessage) (Queue.cellTy recordMessage)) :=
  takeStep_typed nativeSignature rfl recordMessage (by decide)

example :
    typeAt nativeSignature ["id", "hint", "a", "s"]
        [idTy, Queue.answerTy, handleMessage, Queue.cellTy handleMessage]
        (Queue.offerStep handleMessage (var "id") (var "hint") (var "a") (var "s")) =
      some (.prod offerReplyTy (Queue.cellTy handleMessage)) :=
  offerStep_typed nativeSignature rfl handleMessage (by decide)

-- The checker's own answer at both types, by evaluation.
#guard decide (typeOf ["id", "hint", "s"] [idTy, idTy, Queue.cellTy recordMessage]
    (Queue.takeStep recordMessage (var "id") (var "hint") (var "s")) =
  some (.prod (takeReplyTy recordMessage) (Queue.cellTy recordMessage)))
#guard decide (typeOf ["id", "hint", "a", "s"]
    [idTy, Queue.answerTy, handleMessage, Queue.cellTy handleMessage]
    (Queue.offerStep handleMessage (var "id") (var "hint") (var "a") (var "s")) =
  some (.prod offerReplyTy (Queue.cellTy handleMessage)))

/-! ## 2. A step's typing at another scope

A step's theorem holds at every scope, for every caller's terms that have the arguments' types
and keep them under a fold's binders. The two examples are instances at a scope that is not the
statement's own. Weakening is not used: the theorem types the source at the new scope. -/

/-- A binder before the arguments: the identity is the scope's second name. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) :
    typeAt sig ["before", "id", "s"] [.nat, idTy, Queue.cellTy A]
        (Queue.withdrawOffer A (var "id") (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact withdrawOffer_types sig atoms A message (idSrc := var "id") (cellSrc := var "s")
    (env := { names := ["before", "id", "s"] }) (path := [])
    (types := [.nat, idTy, Queue.cellTy A]) rfl (capturedTy_var rfl rfl rfl)
    (types_var rfl rfl rfl) false

/-- A caller's term that is no variable: the identity is a field of a caller's record. The
field's read keeps its type under a fold's binders with its target (`capturedTy_field`). -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) :
    typeAt sig ["taker", "s"] [Queue.takerTy, Queue.cellTy A]
        (Queue.withdrawTake A (field (var "taker") "id") (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact withdrawTake_types sig atoms A message (idSrc := field (var "taker") "id")
    (cellSrc := var "s") (env := { names := ["taker", "s"] }) (path := [])
    (types := [Queue.takerTy, Queue.cellTy A]) rfl
    (capturedTy_field (capturedTy_var rfl rfl rfl) taker_idTy) (types_var rfl rfl rfl) false

-- The checker's own answer at both scopes, at number messages.
#guard decide (typeOf ["before", "id", "s"] [.nat, idTy, Queue.cellTy .nat]
    (Queue.withdrawOffer .nat (var "id") (var "s")) =
  some (.prod wakeReplyTy (Queue.cellTy .nat)))
#guard decide (typeOf ["taker", "s"] [Queue.takerTy, Queue.cellTy .nat]
    (Queue.withdrawTake .nat (field (var "taker") "id") (var "s")) =
  some (.prod wakeReplyTy (Queue.cellTy .nat)))
-- Red control of the scope: the identity at the scope's first name is a number, and the step
-- has no type.
#guard (typeOf ["before", "id", "s"] [.nat, idTy, Queue.cellTy .nat]
    (Queue.withdrawOffer .nat (var "before") (var "s"))).isNone

/-! ## 3. An identity that `bindWith` binds

A wrapper binds a request's identity and its hint with `bindWith`, whose names are minted, and
writes the step under a row's binder for the cell's value. Here a program binds a cell, an
identity and a hint so, and takes. The step's term stands under four names: the three minted
names, and the binder. `captured_answer` and `capturedTy_answer` give the capture of the
identity and of the hint there, with no assumption. The resolution premise is discharged by two
facts: an author's binder is no minted name (`written_ne_mint`), and one stem at two depths
gives two names (`mint_depth_inj`). -/

/-- The three names that the program's three `bindWith`s mint: the cell's handle, the request's
identity, and its hint. They differ by their depths. -/
def cellName : String := Env.mint {} "answer"
def identityName : String := Env.mint { names := [cellName] } "answer"
def hintName : String := Env.mint { names := [cellName, identityName] } "answer"

/-- The scope of the step: the three minted names, and the row's binder `s`. -/
def takeScope : Env := { names := [cellName, identityName, hintName, "s"] }

/-- The hint's name is the scope's third level: the binder `s` is another name. -/
theorem takeScope_hint : takeScope.names.resolve hintName = some 2 := by
  have binder : "s" ≠ hintName := written_ne_mint rfl _ "answer"
  exact (Names.resolve_append_ne binder [cellName, identityName, hintName]).trans
    (resolve_last [cellName, identityName] hintName)

/-- The identity's name is the scope's second level: the binder `s` and the hint's name are
other names. -/
theorem takeScope_identity : takeScope.names.resolve identityName = some 1 := by
  have binder : "s" ≠ identityName := written_ne_mint rfl _ "answer"
  have later : hintName ≠ identityName := fun same => absurd (mint_depth_inj same) (by decide)
  exact (Names.resolve_append_ne binder [cellName, identityName, hintName]).trans
    ((Names.resolve_append_ne later [cellName, identityName]).trans
      (resolve_last [cellName] identityName))

/-- The cell's binder is the scope's last level. -/
theorem takeScope_cell : takeScope.names.resolve "s" = some 3 :=
  resolve_last [cellName, identityName, hintName] "s"

/-- **The identity goes through a fold into `withdrawTake_agrees`**: `removeTaker` places it in
a fold's body, and its capture is `captured_answer`. No `Captured` is assumed. -/
example (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (q h : Val)
    (profile : FirstProfile s) (injective : tb.Injective) :
    ∃ woken,
      Notified s (withdrawTake s id).1 (withdrawTake s id).2 [] woken ∧
      Reads (Queue.withdrawTake A (minted identityName) (var "s")) takeScope []
        [q, Val.promise (tb.handle id), h, cellVal tb msg s]
        (Val.tuple [Val.list (woken.map (takerVal tb)), cellVal tb msg (withdrawTake s id).1]) :=
  withdrawTake_agrees A tb msg s id profile injective rfl
    (captured_answer (outer := { names := [cellName] }) takeScope_identity rfl)
    (captured_var (x := "s") rfl takeScope_cell rfl).atScope

/-- **The identity and the hint go through the take step's folds into `takeStep_agrees`**:
`renewHint` places both in a fold's body. No `Captured` is assumed. -/
example (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (q : Val) (profile : FirstProfile s) (requested : Requested s (.take id 1 1))
    (injective : tb.Injective) :
    ∃ reply entered woken,
      takeReplyVal msg (take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Notified s (take s ⟨id, 1, 1⟩).1 (take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      Reads (Queue.takeStep A (minted identityName) (minted hintName) (var "s")) takeScope []
        [q, Val.promise (tb.handle id), Val.promise hint, cellVal tb msg s]
        (Val.tuple [Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
            Val.list (woken.map (takerVal (tb.afterTake id hint (take s ⟨id, 1, 1⟩).2.1)))],
          cellVal (tb.afterTake id hint (take s ⟨id, 1, 1⟩).2.1) msg
            (take s ⟨id, 1, 1⟩).1]) :=
  takeStep_agrees A tb msg s id hint profile requested injective rfl
    (captured_answer (outer := { names := [cellName] }) takeScope_identity rfl)
    (captured_answer (outer := { names := [cellName, identityName] }) takeScope_hint rfl)
    (captured_var (x := "s") rfl takeScope_cell rfl).atScope

/-- The take step is typed there: the typed twin of the capture is `capturedTy_answer`. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) :
    typeAt sig [cellName, identityName, hintName, "s"]
        [.refOf (Queue.cellTy A), idTy, idTy, Queue.cellTy A]
        (Queue.takeStep A (minted identityName) (minted hintName) (var "s")) =
      some (.prod (takeReplyTy A) (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact takeStep_types sig atoms A message (idSrc := minted identityName)
    (hintSrc := minted hintName) (cellSrc := var "s") (env := takeScope) (path := [])
    (types := [.refOf (Queue.cellTy A), idTy, idTy, Queue.cellTy A]) rfl
    (capturedTy_answer (outer := { names := [cellName] }) takeScope_identity rfl)
    (capturedTy_answer (outer := { names := [cellName, identityName] }) takeScope_hint rfl)
    (types_var rfl takeScope_cell rfl) false

/-- A program that binds a cell, an identity and a hint with `bindWith`, then takes. -/
def taking : Src NativeOp :=
  bindWith (Ref.make (Queue.empty .nat 2)) fun q =>
    bindWith (Deferred.make .unit .never) fun id =>
      bindWith (Deferred.make .unit .never) fun hint =>
        Ref.modify "s" (Queue.takeStep .nat id hint (var "s")) q

/-- The term of the program's one `Ref.modify`. -/
def modifyTerm : Eff NativeOp → Option Term
  | .bind _ (.bind _ (.bind _ (.perform (.refModifyWith f) _))) => some f
  | _ => none

-- The program's step term is the step's source at the scope of the examples: the scope at
-- which the capture is stated is the scope that the program elaborates the step in.
#guard ((elaborate taking).toOption.bind modifyTerm).isSome
#guard (elaborate taking).toOption.bind modifyTerm ==
  (Queue.takeStep .nat (minted identityName) (minted hintName) (var "s") takeScope []).toOption
-- The checker types the step's term there.
#guard decide (typeOf takeScope.names
    [.refOf (Queue.cellTy .nat), idTy, idTy, Queue.cellTy .nat]
    (Queue.takeStep .nat (minted identityName) (minted hintName) (var "s")) =
  some (.prod (takeReplyTy .nat) (Queue.cellTy .nat)))
-- Red control of the depth: two `bindWith`s at one depth would mint one name, and the first
-- would resolve to the second's level.
#guard (minted cellName { names := [cellName, cellName] } []).toOption == some (Term.var 1)

/-! ### Red control of the capture: a caller's name equal to the fold's accumulator name

`captured_minted` asks that the caller's name differs from the two names that a fold of the
scope mints. Here it does not: the scope's one name is the name that a fold of this scope mints
for its accumulator. Under the fold's binders the name reads the accumulator. The caller's
value and the accumulator are two numbers, so the checker types both readings alike. -/

/-- A scope whose one name is its own fold's accumulator name. -/
def clash : Env := { names := ["_%acc1"] }

#guard clash.mint "acc" == "_%acc1"
-- At the scope the name reads the caller's value.
#guard (minted "_%acc1" clash []).toOption.bind (evalTerm [Val.nat 7]) == some (Val.nat 7)
-- Under the fold's two binders it reads the accumulator.
#guard (minted "_%acc1" (clash.push [clash.mint "acc", clash.mint "item"]) []).toOption.bind
  (evalTerm [Val.nat 7, Val.nat 100, Val.nat 5]) == some (Val.nat 100)
-- So a fold whose body answers the name answers its initial value, and not the caller's.
#guard ((foldWith (app "cons" [nat 1, nilT]) (nat 100) fun _ _ => minted "_%acc1")
  clash []).toOption.bind (evalTerm [Val.nat 7]) == some (Val.nat 100)
-- The checker types the fold at a number under both readings.
#guard decide (typeOf ["_%acc1"] [.nat]
    (foldWith (app "cons" [nat 1, nilT]) (nat 100) fun _ _ => minted "_%acc1") =
  some .nat)
-- A name that `bindWith` mints is no such name: the same fold answers the caller's value.
#guard ((foldWith (app "cons" [nat 1, nilT]) (nat 100) fun _ _ => minted cellName)
  { names := [cellName] } []).toOption.bind (evalTerm [Val.nat 7]) == some (Val.nat 7)

/-! ## 4. The red controls of the new rules

Each control is a term that one premise of a rule excludes: the checker gives it no type, and
the twin that keeps the premise is typed. -/

/-! ### A fold's body above its accumulator's type

The fold's introduction rule asks that the body's type is below the accumulator's
(`argTy_fold_intro`, `types_foldWith`). Here the accumulator starts as the empty list, at the
type of a list of nothing, and the body answers a list of numbers. -/

#guard (typeOf ["xs"] [.list .nat]
  (foldWith (var "xs") nilT fun acc item => app "cons" [item, acc])).isNone
-- With the accumulator's type stated, the same fold is typed.
#guard decide (typeOf ["xs"] [.list .nat]
    (foldWith (var "xs") nilT (fun acc item => app "cons" [item, acc])
      (some (.list .nat))) =
  some (.list .nat))

/-! ### A record with a field named twice

A construction asks that the raw declaration is formed and that no name is supplied twice
(`argTy_record_intro`, `Record.check_declared`). -/

-- The declaration names a field twice.
#guard (typeOf [] [] (record [("a", false, .nat), ("a", false, .nat)] [("a", nat 1)])).isNone
-- The construction supplies a name twice.
#guard (typeOf [] [] (record [("a", false, .nat)] [("a", nat 1), ("a", nat 2)])).isNone
-- The record rule itself refuses the repeated declaration.
#guard (Record.check [("a", false, .nat), ("a", false, .nat)] ["a", "a"] [.nat, .nat]).isNone
-- Each field once: the construction is typed.
#guard decide (typeOf [] [] (record [("a", false, .nat)] [("a", nat 1)]) =
  some (.record [("a", false, .nat)]))

/-! ### The accumulator and the item in each other's place

Under a fold's two binders the accumulator's name has the accumulator's type and the element's
name the element's (`types_minted_acc`, `types_minted_item`). The accumulator is a Boolean here
and the element a number. -/

#guard decide (typeOf ["xs"] [.list .nat]
    (foldWith (var "xs") (bool false) fun acc item => orT acc (app "isZero" [item])) =
  some .bool)
#guard (typeOf ["xs"] [.list .nat]
  (foldWith (var "xs") (bool false) fun acc item => orT item (app "isZero" [acc]))).isNone

/-! ### A term moved under the binders without its capture

A source term is a function of its scope. Scope and typing at one scope do not give its type
under two more names, so `CapturedTy` is a premise. -/

/-- A source whose type depends on its scope: a number in a scope of one name, a Boolean
elsewhere. It is scoped and typed at every scope, and it is no caller's term. -/
def unstable : TermSrc := fun env _ =>
  .ok (.lit (if env.names.length = 1 then .nat 0 else .bool true))

-- At the scope it is a number.
#guard decide (typeOf ["xs"] [.list .nat] unstable = some .nat)
-- Under a fold's two binders it is a Boolean, so the sum in the body has no type.
#guard (typeOf ["xs"] [.list .nat]
  (foldWith (var "xs") (nat 0) fun acc _ => app "add" [acc, unstable])).isNone
-- An author's variable in the same place keeps its type (`capturedTy_var`).
#guard decide (typeOf ["xs", "n"] [.list .nat, .nat]
    (foldWith (var "xs") (nat 0) fun acc _ => app "add" [acc, var "n"]) =
  some .nat)

/-! ### The literal flag

`Types` carries the checker's literal flag: a string literal keeps its literal type as a
record's value and as a const-generic atom's argument, and it is a string elsewhere. `termTy`
alone has the second reading only. -/

-- Inside the const-generic atom `pair`, the literal keeps its literal type.
example :
    Types nativeSignature (app "pair" [str "A", nat 1]) {} [] [] false (.prod (.lit "A") .nat) :=
  types_app (.cons (types_lit (.str "A") true) (.cons (types_lit (.nat 1) true) .nil))
    (nativeAtomTy_pair (.lit "A") .nat)

-- As a record's value, it has the type of a tag field.
example :
    Types nativeSignature (record [("tag", false, .lit "A")] [("tag", str "A")]) {} [] [] false
      (.record [("tag", false, .lit "A")]) :=
  types_record (by decide) (.cons (types_lit (.str "A") true) .nil)
    (Record.check_declared (fields := [("tag", false, .lit "A")]) (by decide))

-- The checker's own answers, and the same literal outside a const-generic position.
#guard decide (typeOf [] [] (app "pair" [str "A", nat 1]) = some (.prod (.lit "A") .nat))
#guard decide (typeOf [] [] (record [("tag", false, .lit "A")] [("tag", str "A")]) =
  some (.record [("tag", false, .lit "A")]))
#guard decide (typeOf [] [] (str "A") = some .string)
-- Red control: a string that is no literal of the tag does not fit the tag field.
#guard (typeOf ["x"] [.string] (record [("tag", false, .lit "A")] [("tag", var "x")])).isNone

/-! ### A positional read of a step's reply

The wrapper reads a step's reply by position. A reply's type is its own normal form, so the
tuple rule answers the item at the position (`Tuple.typeAt_normal`, `types_tupleAt`). -/

-- The offers that a take accepted: the second part of its reply, at every message type.
example (sig : Signature NativeOp) (A : Ty) (message : MessageTy A) :
    Types sig (tupleAt (var "r") 1) { names := ["r"] } [] [takeReplyTy A] false
      (.list (Queue.offerTy A)) :=
  types_tupleAt (types_var rfl rfl rfl false)
    (Tuple.typeAt_normal (takeReplyTy_normal message.canonical) rfl)

-- The checker's own answer at number messages, and a poll's reply, which is a product.
#guard decide (typeOf ["r"] [takeReplyTy .nat] (tupleAt (var "r") 1) =
  some (.list (Queue.offerTy .nat)))
#guard decide (typeOf ["r"] [pollReplyTy .nat] (tupleAt (var "r") 0) = some (.option .nat))
-- Red control: a tuple of three has no fourth part, and a list has no fixed position.
#guard (typeOf ["r"] [takeReplyTy .nat] (tupleAt (var "r") 3)).isNone
#guard (typeOf ["r"] [wakeReplyTy] (tupleAt (var "r") 0)).isNone

/-! ## 5. The connector to the store

`typeAt_tree` recovers the step's tree and its `termTy` equation from the typing statement, and
`step_keeps_cell` reads that equation: one `Ref.modify` of the step keeps the cell a member of
the cell's type. No planned goal is among its dependencies. The first theorem stands at the
statement's own scope, and the second at every scope. -/

/-- **The withdrawal of an offer keeps the cell a member of its type**, at every message type
that the checker types in a cell: the step's tree at the statement's own scope, and what its
answer and its stored value are members of. -/
theorem withdrawOffer_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) {w : Typed.World} {captured : List Val}
    (typedEnv : Typed.EnvTyped w [idTy] captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell (Queue.cellTy A)) :
    ∃ f, Queue.withdrawOffer A (var "id") (var "s") { names := ["id", "s"] } [] = .ok f ∧
      (evalTerm (captured ++ [cell]) f = some (Val.tuple [reply, next]) →
        Typed.Fits w reply wakeReplyTy ∧ Typed.Fits w next (Queue.cellTy A)) := by
  obtain ⟨f, tree, typed⟩ := typeAt_tree (withdrawOffer_typed sig atoms A message)
  exact ⟨f, tree, fun value => step_keeps_cell sig atoms typedEnv typed held member value⟩

/-- **A step's tree is one tree, at every scope.** The tree that a step's reading evaluates is
the tree that the step's theorem types (`Types.tree`). So a withdrawal of a take that reads a
reply and a next value keeps the cell a member of its type, at every scope and for every
caller's terms. The cell's value is the scope's last name. The wrapper's law has this shape,
and it takes its tree from `step_updates`. -/
theorem withdrawTake_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : (tys ++ [Queue.cellTy A]).length = env.names.length)
    (typesId : CapturedTy sig idSrc env path (tys ++ [Queue.cellTy A]) idTy)
    (typesCell : TypesEach sig cellSrc env path (tys ++ [Queue.cellTy A]) (Queue.cellTy A))
    (typedEnv : Typed.EnvTyped w tys captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell (Queue.cellTy A))
    (reads : Reads (Queue.withdrawTake A idSrc cellSrc) env path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    Typed.Fits w reply wakeReplyTy ∧ Typed.Fits w next (Queue.cellTy A) := by
  obtain ⟨f, tree, value⟩ := reads
  exact step_keeps_cell sig atoms typedEnv
    ((withdrawTake_types sig atoms A message depth typesId typesCell false).tree tree) held
    member value

end Test.Program.QueueTyping
