import Effect4.Modules.Queue.Steps
import Effect4.Program.Authoring.Sugar
import Effect4.Laws.Modules.Queue.Typing
import Effect4.Laws.Modules.Queue.Steps
import ProofGraph.Plan

/-!
# The Queue's steps typed at every message type: instances, red controls and pins (row 257)

The five steps of a `Ref.modify` are typed at every message type that the checker types in a
cell (`src/Effect4/Laws/Modules/Queue/Typing.lean`). The proofs read the checker's rules in
their introduction form (`src/Effect4/Laws/Program/Typing/TermIntro.lean`) through the judgment
`Types` (`src/Effect4/Laws/Modules/Queue/Checking.lean`). This battery holds what the theorems
do not say by themselves:

1. the statements at a record message type and at a message type that holds a handle;
2. a step's typing at a scope that is not the statement's own: a binder before the arguments,
   and a caller's term that is no variable;
3. an identity that `bindWith` binds, through a fold of a step, with no assumed capture, for
   values and for types, and the red control of the capture;
4. the red controls of the new rules;
5. the connector to the store: `step_keeps_cell` on a step's typing;
6. the pinned axioms and the pinned standing of each theorem.

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
        [Queue.idTy, Queue.idTy, Queue.cellTy recordMessage]
        (Queue.takeStep recordMessage (var "id") (var "hint") (var "s")) =
      some (.prod (takeReplyTy recordMessage) (Queue.cellTy recordMessage)) :=
  takeStep_typed nativeSignature rfl recordMessage (by decide)

example :
    typeAt nativeSignature ["id", "hint", "a", "s"]
        [Queue.idTy, Queue.answerTy, handleMessage, Queue.cellTy handleMessage]
        (Queue.offerStep handleMessage (var "id") (var "hint") (var "a") (var "s")) =
      some (.prod offerReplyTy (Queue.cellTy handleMessage)) :=
  offerStep_typed nativeSignature rfl handleMessage (by decide)

-- The checker's own answer at both types, by evaluation.
#guard decide (typeOf ["id", "hint", "s"] [Queue.idTy, Queue.idTy, Queue.cellTy recordMessage]
    (Queue.takeStep recordMessage (var "id") (var "hint") (var "s")) =
  some (.prod (takeReplyTy recordMessage) (Queue.cellTy recordMessage)))
#guard decide (typeOf ["id", "hint", "a", "s"]
    [Queue.idTy, Queue.answerTy, handleMessage, Queue.cellTy handleMessage]
    (Queue.offerStep handleMessage (var "id") (var "hint") (var "a") (var "s")) =
  some (.prod offerReplyTy (Queue.cellTy handleMessage)))

/-! ## 2. A step's typing at another scope

A step's theorem holds at every scope, for every caller's terms that have the arguments' types
and keep them under a fold's binders. The two examples are instances at a scope that is not the
statement's own. Weakening is not used: the theorem types the source at the new scope. -/

/-- A binder before the arguments: the identity is the scope's second name. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) :
    typeAt sig ["before", "id", "s"] [.nat, Queue.idTy, Queue.cellTy A]
        (Queue.withdrawOffer A (var "id") (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact withdrawOffer_types sig atoms A message (idSrc := var "id") (cellSrc := var "s")
    (env := { names := ["before", "id", "s"] }) (path := [])
    (types := [.nat, Queue.idTy, Queue.cellTy A]) rfl (capturedTy_var rfl rfl rfl)
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
#guard decide (typeOf ["before", "id", "s"] [.nat, Queue.idTy, Queue.cellTy .nat]
    (Queue.withdrawOffer .nat (var "id") (var "s")) =
  some (.prod wakeReplyTy (Queue.cellTy .nat)))
#guard decide (typeOf ["taker", "s"] [Queue.takerTy, Queue.cellTy .nat]
    (Queue.withdrawTake .nat (field (var "taker") "id") (var "s")) =
  some (.prod wakeReplyTy (Queue.cellTy .nat)))
-- Red control of the scope: the identity at the scope's first name is a number, and the step
-- has no type.
#guard (typeOf ["before", "id", "s"] [.nat, Queue.idTy, Queue.cellTy .nat]
    (Queue.withdrawOffer .nat (var "before") (var "s"))).isNone

/-! ## 3. An identity that `bindWith` binds

A wrapper binds a request's identity with `bindWith`, whose name is minted, and writes the step
under a row's binder for the cell's value. The step's term then stands under two names: the
identity's minted name, and the binder. `captured_answer` and `capturedTy_answer` give the
capture of the identity there, with no assumption. -/

/-- The scope of a step under one `bindWith` and a row's binder `s`. -/
def stepScope : Env := { names := [Env.mint {} "answer", "s"] }

/-- The identity's name is the scope's first level: the binder `s` is another name, because an
author can write it. -/
theorem stepScope_identity : stepScope.names.resolve (Env.mint {} "answer") = some 0 := by
  have other : "s" ≠ Env.mint {} "answer" := by
    intro same
    have reserved : Name.reserved "s" = true := by
      rw [same]
      exact mint_reserved {} "answer"
    exact absurd reserved (by decide)
  exact (Names.resolve_append_ne other [Env.mint {} "answer"]).trans
    (resolve_last [] (Env.mint {} "answer"))

/-- The cell's binder is the scope's second level. -/
theorem stepScope_cell : stepScope.names.resolve "s" = some 1 :=
  resolve_last [Env.mint {} "answer"] "s"

/-- **The identity goes through a fold into `withdrawTake_agrees`**: `removeTaker` places it in
a fold's body, and its capture is `captured_answer`. No `Captured` is assumed. -/
example (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) :
    ∃ woken,
      Notified s (withdrawTake s id).1 (withdrawTake s id).2 [] woken ∧
      Reads (Queue.withdrawTake A (minted (Env.mint {} "answer")) (var "s")) stepScope []
        [Val.promise (tb.handle id), cellVal tb msg s]
        (Val.tuple [Val.list (woken.map (takerVal tb)), cellVal tb msg (withdrawTake s id).1]) :=
  withdrawTake_agrees A tb msg s id profile injective rfl
    (captured_answer (outer := {}) stepScope_identity rfl)
    (captured_var (x := "s") rfl stepScope_cell rfl).atScope

/-- The same step is typed there: the typed twin of the capture is `capturedTy_answer`. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) :
    typeAt sig [Env.mint {} "answer", "s"] [Queue.idTy, Queue.cellTy A]
        (Queue.withdrawTake A (minted (Env.mint {} "answer")) (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact withdrawTake_types sig atoms A message (idSrc := minted (Env.mint {} "answer"))
    (cellSrc := var "s") (env := stepScope) (path := [])
    (types := [Queue.idTy, Queue.cellTy A]) rfl
    (capturedTy_answer (outer := {}) stepScope_identity rfl)
    (types_var rfl stepScope_cell rfl) false

/-- A program that binds a cell and an identity with `bindWith`, then withdraws the identity.
The two minted names differ by their depths. -/
def withdrawing : Src NativeOp :=
  bindWith (Ref.make (Queue.empty .nat 2)) fun q =>
    bindWith (Deferred.make .unit .never) fun id =>
      Ref.modify "s" (Queue.withdrawTake .nat id (var "s")) q

/-- The term of the program's one `Ref.modify`. -/
def modifyTerm : Eff NativeOp → Option Term
  | .bind _ (.bind _ (.perform (.refModifyWith f) _)) => some f
  | _ => none

/-- The name of the cell and the name of the identity, as the two `bindWith`s mint them. -/
def cellName : String := Env.mint {} "answer"
def identityName : String := Env.mint { names := [cellName] } "answer"

-- The program's step term is the step's source under the two minted names and the binder: the
-- scope at which the capture is stated.
#guard (elaborate withdrawing).toOption.bind modifyTerm ==
  (Queue.withdrawTake .nat (minted identityName) (var "s")
    { names := [cellName, identityName, "s"] } []).toOption
#guard ((elaborate withdrawing).toOption.bind modifyTerm).isSome
-- The checker types the step's term there.
#guard decide (typeOf [cellName, identityName, "s"]
    [.refOf (Queue.cellTy .nat), Queue.idTy, Queue.cellTy .nat]
    (Queue.withdrawTake .nat (minted identityName) (var "s")) =
  some (.prod wakeReplyTy (Queue.cellTy .nat)))

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
#guard ((foldWith (app "cons" [nat 1, Queue.nilT]) (nat 100) fun _ _ => minted "_%acc1")
  clash []).toOption.bind (evalTerm [Val.nat 7]) == some (Val.nat 100)
-- The checker types the fold at a number under both readings.
#guard decide (typeOf ["_%acc1"] [.nat]
    (foldWith (app "cons" [nat 1, Queue.nilT]) (nat 100) fun _ _ => minted "_%acc1") =
  some .nat)
-- A name that `bindWith` mints is no such name: the same fold answers the caller's value.
#guard ((foldWith (app "cons" [nat 1, Queue.nilT]) (nat 100) fun _ _ => minted cellName)
  { names := [cellName] } []).toOption.bind (evalTerm [Val.nat 7]) == some (Val.nat 7)

/-! ## 4. The red controls of the new rules

Each control is a term that one premise of a rule excludes: the checker gives it no type, and
the twin that keeps the premise is typed. -/

/-! ### A fold's body above its accumulator's type

The fold's introduction rule asks that the body's type is below the accumulator's
(`argTy_fold_intro`, `types_foldWith`). Here the accumulator starts as the empty list, at the
type of a list of nothing, and the body answers a list of numbers. -/

#guard (typeOf ["xs"] [.list .nat]
  (foldWith (var "xs") Queue.nilT fun acc item => app "cons" [item, acc])).isNone
-- With the accumulator's type stated, the same fold is typed.
#guard decide (typeOf ["xs"] [.list .nat]
    (foldWith (var "xs") Queue.nilT (fun acc item => app "cons" [item, acc])
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
    (foldWith (var "xs") (bool false) fun acc item => Queue.orT acc (app "isZero" [item])) =
  some .bool)
#guard (typeOf ["xs"] [.list .nat]
  (foldWith (var "xs") (bool false) fun acc item => Queue.orT item (app "isZero" [acc]))).isNone

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

/-! ## 5. The connector to the store

`typeAt_tree` recovers the step's tree and its `termTy` equation from the typing statement, and
`step_keeps_cell` reads that equation: one `Ref.modify` of the step keeps the cell a member of
the cell's type. No planned goal is among its dependencies. -/

/-- **The withdrawal of an offer keeps the cell a member of its type**, at every message type
that the checker types in a cell: the step's tree at the statement's own scope, and what its
answer and its stored value are members of. -/
theorem withdrawOffer_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) {w : Typed.World} {captured : List Val}
    (typedEnv : Typed.EnvTyped w [Queue.idTy] captured) {stores : Stores} {q : RefKey}
    {cell reply next : Val} (held : refPeek stores.refs q = some cell)
    (member : Typed.Fits w cell (Queue.cellTy A)) :
    ∃ f, Queue.withdrawOffer A (var "id") (var "s") { names := ["id", "s"] } [] = .ok f ∧
      (evalTerm (captured ++ [cell]) f = some (Val.tuple [reply, next]) →
        Typed.Fits w reply wakeReplyTy ∧ Typed.Fits w next (Queue.cellTy A)) := by
  obtain ⟨f, tree, typed⟩ := typeAt_tree (withdrawOffer_typed sig atoms A message)
  exact ⟨f, tree, fun value => step_keeps_cell sig atoms typedEnv typed held member value⟩

/-- info: 'Test.Program.QueueTyping.withdrawOffer_keeps_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms withdrawOffer_keeps_cell

/--
info: Test.Program.QueueTyping.withdrawOffer_keeps_cell: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status withdrawOffer_keeps_cell

/-! ## 6. The pinned outputs

Each theorem's axioms, and its standing as the plan derives it from its proof. The five
statements at a step's own scope are no planned goals now: each rests on its step's theorem at
every scope, and that theorem rests on no goal. The counts are of this battery's tree, which
holds no step of a proof: the steps are in the law graph. -/

/-! ### The five steps of a `Ref.modify`: at the step's own scope, and at every scope -/

/-- info: 'Effect4.Queue.Model.takeStep_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms takeStep_typed

/-- info: 'Effect4.Queue.Model.offerStep_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms offerStep_typed

/-- info: 'Effect4.Queue.Model.pollStep_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pollStep_typed

/-- info: 'Effect4.Queue.Model.withdrawTake_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms withdrawTake_typed

/-- info: 'Effect4.Queue.Model.withdrawOffer_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms withdrawOffer_typed

/-- info: 'Effect4.Queue.Model.takeStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms takeStep_types

/-- info: 'Effect4.Queue.Model.offerStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms offerStep_types

/-- info: 'Effect4.Queue.Model.pollStep_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pollStep_types

/-- info: 'Effect4.Queue.Model.withdrawTake_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms withdrawTake_types

/-- info: 'Effect4.Queue.Model.withdrawOffer_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms withdrawOffer_types

/--
info: Effect4.Queue.Model.takeStep_typed: proved; nearest [Effect4.Queue.Model.takeStep_types]; 0 lemmas, 0 definitions
Effect4.Queue.Model.offerStep_typed: proved; nearest [Effect4.Queue.Model.offerStep_types]; 0 lemmas, 0 definitions
Effect4.Queue.Model.pollStep_typed: proved; nearest [Effect4.Queue.Model.pollStep_types]; 0 lemmas, 0 definitions
Effect4.Queue.Model.withdrawTake_typed: proved; nearest [Effect4.Queue.Model.withdrawTake_types]; 0 lemmas, 0 definitions
Effect4.Queue.Model.withdrawOffer_typed: proved; nearest [Effect4.Queue.Model.withdrawOffer_types]; 0 lemmas, 0 definitions
Effect4.Queue.Model.takeStep_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.offerStep_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.pollStep_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.withdrawTake_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.withdrawOffer_types: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status takeStep_typed offerStep_typed pollStep_typed withdrawTake_typed withdrawOffer_typed
  takeStep_types offerStep_types pollStep_types withdrawTake_types withdrawOffer_types

/-! ### Each pass, typed once -/

/-- info: 'Effect4.Queue.Model.types_removeTaker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_removeTaker

/-- info: 'Effect4.Queue.Model.types_removeOffer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_removeOffer

/-- info: 'Effect4.Queue.Model.types_renewHint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_renewHint

/-- info: 'Effect4.Queue.Model.types_gained' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_gained

/-- info: 'Effect4.Queue.Model.types_wake' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_wake

/-- info: 'Effect4.Queue.Model.types_fitting' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_fitting

/-- info: 'Effect4.Queue.Model.types_entering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_entering

/-- info: 'Effect4.Queue.Model.types_staying' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_staying

/-- info: 'Effect4.Queue.Model.types_enrolled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_enrolled

/-- info: 'Effect4.Queue.Model.types_isHead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms types_isHead

/--
info: Effect4.Queue.Model.types_removeTaker: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_removeOffer: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_renewHint: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_gained: proved; nearest [Effect4.Queue.Model.types_entering]; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_wake: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_fitting: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_entering: proved; nearest [Effect4.Queue.Model.types_fitting]; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_staying: proved; nearest [Effect4.Queue.Model.types_fitting]; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_enrolled: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.types_isHead: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status types_removeTaker types_removeOffer types_renewHint types_gained types_wake
  types_fitting types_entering types_staying types_enrolled types_isHead

/-! ### The capture of a minted name, its typed twin, and the connector -/

/-- info: 'Effect4.Queue.Model.captured_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms captured_minted

/-- info: 'Effect4.Queue.Model.captured_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms captured_answer

/-- info: 'Effect4.Queue.Model.capturedTy_var' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms capturedTy_var

/-- info: 'Effect4.Queue.Model.capturedTy_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms capturedTy_minted

/-- info: 'Effect4.Queue.Model.capturedTy_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms capturedTy_answer

/-- info: 'Effect4.Queue.Model.typeAt_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms typeAt_tree

/--
info: Effect4.Queue.Model.captured_minted: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.captured_answer: proved; nearest [Effect4.Queue.Model.captured_minted]; 0 lemmas, 0 definitions
Effect4.Queue.Model.capturedTy_var: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.capturedTy_minted: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.capturedTy_answer: proved; nearest [Effect4.Queue.Model.capturedTy_minted]; 0 lemmas, 0 definitions
Effect4.Queue.Model.typeAt_tree: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status captured_minted captured_answer capturedTy_var capturedTy_minted capturedTy_answer
  typeAt_tree

end Test.Program.QueueTyping
