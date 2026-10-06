import Effect4.Modules.Queue.Steps
import Effect4.Program.Typing
import Effect4.Program.Native
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.TyView
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# The typing of the Queue's cell and of its six steps (decisions row 255)

The module is `src/Effect4/Modules/Queue/`: the cell (`Cell.lean`) and the step terms
(`Steps.lean`). This file states that the checker types the initial value and each step at the
cell's type, for every message type that it types in a cell (`MessageTy`).

Placement. Concept `store-typing`. Requirement R4. Each statement is one typing judgment of the
checker (`termTy`) on a step's tree, at the step's own scope: the names of its arguments, and
the cell's value last. Its consumer is the wrapper's law, in the public path's slice: with a
step's typing, `ListFoldRules.step` (`src/Effect4/Laws/Program/Typed/ListFold.lean`) gives that
one `Ref.modify` of the step keeps the cell a member of the cell's type. Reach: the signature's
atoms are the native table's. At another scope a step's type follows by `termTy_weaken`
(`src/Effect4/Program/Typing/Rules.lean`), which this file does not state.

The statements establish no agreement with the model, no typing of a wrapper and nothing about
a target. Two are proved, each in place of its planned goal (decisions row 203): the initial
value's (`empty_typed`) and the size step's (`sizeStep_typed`). Their proofs read the checker's
rule at each node, with the cell's type as its own normal form (`cellTy_normal`). The five
steps of a `Ref.modify` stay planned goals: their proofs need the same reading of the checker
at the atoms' templates, at a record's overwrite and at a fold's two binders. The finite
controls are in `Test/Program/QueueSteps.lean`: each statement at 27 message types, with red
controls.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

open Effect4.Program Effect4.Program.Authoring

/-- **A message type that the checker types in a cell.** It is its own normal form, so the
cell's type at it is the type that the checker answers. The two record declarations that hold
it are formed: the cell's and a pending offer's (`Formation.check`,
`src/Effect4/Program/Formation.lean`). -/
structure MessageTy (A : Ty) : Prop where
  canonical : A.normalize = A
  cell : Formation.check (Formation.sites false [] (.record (Queue.cellFields A))) = none
  offer : Formation.check (Formation.sites false [] (.record (Queue.offerFields A))) = none

instance (A : Ty) : Decidable (MessageTy A) :=
  decidable_of_iff
    (A.normalize = A ∧
      Formation.check (Formation.sites false [] (.record (Queue.cellFields A))) = none ∧
      Formation.check (Formation.sites false [] (.record (Queue.offerFields A))) = none)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.canonical, h.cell, h.offer⟩⟩

/-- The checker's type of a source term, at a scope of names and their types. `none` where the
source refuses or its tree has no type. -/
def typeAt (sig : Signature NativeOp) (names : List String) (types : List Ty) (src : TermSrc) :
    Option Ty :=
  (src { names := names } []).toOption.bind (termTy sig types)

/-! ## The types of the steps' replies -/

/-- A take's reply: the message when it consumed, the offers that the step accepted, and the
takers to wake. -/
def takeReplyTy (A : Ty) : Ty :=
  .tuple [.option A, .list (Queue.offerTy A), .list Queue.takerTy]

/-- An offer's reply: its decided answer when it does not wait, and the takers to wake. A pair,
as the checker normalizes a tuple of two. -/
def offerReplyTy : Ty := .prod (.option .bool) (.list Queue.takerTy)

/-- A poll's reply: the message when it consumed, and the offers that the step accepted. -/
def pollReplyTy (A : Ty) : Ty := .prod (.option A) (.list (Queue.offerTy A))

/-- A withdrawal's reply: the takers to wake. -/
def wakeReplyTy : Ty := .list Queue.takerTy

/-! ## The cell's type is its own normal form, at a canonical message type -/

theorem offerTy_normal {A : Ty} (canonical : A.normalize = A) :
    (Queue.offerTy A).normalize = Queue.offerTy A := by
  show Ty.normalize (.record _) = _
  rw [Ty.normalize_record]
  show Ty.record [("batch", false, Ty.normalize .bool), ("hint", false, Ty.normalize Queue.answerTy),
    ("id", false, Ty.normalize Queue.idTy), ("rest", false, Ty.normalize (.list A))] = _
  have rest : Ty.normalize (.list A) = .list A := by
    show Ty.list (Ty.normalize A) = _
    rw [canonical]
  rw [rest]
  rfl

theorem cellTy_normal {A : Ty} (canonical : A.normalize = A) :
    (Queue.cellTy A).normalize = Queue.cellTy A := by
  show Ty.normalize (.record _) = _
  rw [Ty.normalize_record]
  show Ty.record [("cap", false, Ty.normalize .nat), ("msgs", false, Ty.normalize (.list A)),
    ("offers", false, Ty.normalize (.list (Queue.offerTy A))),
    ("takers", false, Ty.normalize (.list Queue.takerTy))] = _
  have msgs : Ty.normalize (.list A) = .list A := by
    show Ty.list (Ty.normalize A) = _
    rw [canonical]
  have offers : Ty.normalize (.list (Queue.offerTy A)) = .list (Queue.offerTy A) := by
    show Ty.list (Ty.normalize (Queue.offerTy A)) = _
    rw [offerTy_normal canonical]
  rw [msgs, offers]
  rfl

/-- The type of the cell's buffer, as the checker reads the field. -/
theorem cell_msgsTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.cellTy A) "msgs" = some (.list A) := by
  unfold Record.fieldType
  rw [cellTy_normal canonical]
  show some (Record.joinResults [Ty.list A]) = _
  show some (Ty.join .never (.list A)) = _
  rw [Ty.join_never]
  show some (Ty.list (Ty.normalize A)) = _
  rw [canonical]

/-- The empty list is below every list type. -/
theorem sub_nil_list (T : Ty) : Ty.sub (.list .never) (.list T) = true := by
  rw [Ty.sub_args_list]
  show (Ty.sub .never T && true) = true
  rw [Ty.OrderProof.sub_never]
  rfl

/-- The cell's written declaration normalizes to the cell's type. -/
theorem cellFields_normal {A : Ty} (canonical : A.normalize = A) :
    Ty.normalize (.record (Queue.cellFields A)) = Queue.cellTy A := by
  rw [Ty.normalize_record]
  show Ty.record [("cap", false, Ty.normalize .nat), ("msgs", false, Ty.normalize (.list A)),
    ("offers", false, Ty.normalize (.list (Queue.offerTy A))),
    ("takers", false, Ty.normalize (.list Queue.takerTy))] = _
  have msgs : Ty.normalize (.list A) = .list A := by
    show Ty.list (Ty.normalize A) = _
    rw [canonical]
  have offers : Ty.normalize (.list (Queue.offerTy A)) = .list (Queue.offerTy A) := by
    show Ty.list (Ty.normalize (Queue.offerTy A)) = _
    rw [offerTy_normal canonical]
  rw [msgs, offers]
  rfl

/-! ## The statements -/

/-- **The initial value has the cell's type**, at every capacity and in every scope. -/
@[semantics "store-typing" (requirement := R4)]
theorem empty_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (capacity : Nat) (names : List String) (types : List Ty) :
    typeAt sig names types (Queue.empty A capacity) = some (Queue.cellTy A) := by
  have fits : Record.argumentsFit (Queue.cellFields A)
      [("msgs", Ty.list .never), ("cap", Ty.nat), ("takers", Ty.list .never),
        ("offers", Ty.list .never)] = true := by
    unfold Record.argumentsFit
    rw [Bool.and_eq_true]
    refine ⟨rfl, List.all_eq_true.mpr fun field member => ?_⟩
    simp only [Queue.cellFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact sub_nil_list _
    · exact Ty.sub_refl _
    · exact sub_nil_list _
    · exact sub_nil_list _
  have nilTy : ∀ const : Bool, argTy sig types const (.app "nil" .nil) = some (Ty.list .never) := by
    intro const
    show sig.atomOf "nil" [] = _
    rw [atoms]
    rfl
  have capTy : argTy sig types true (.lit (.nat capacity)) = some Ty.nat := rfl
  have noneTy : argsTy sig types true .nil = some [] := rfl
  have values : argsTy sig types true (.cons (.app "nil" .nil) (.cons (.lit (.nat capacity))
      (.cons (.app "nil" .nil) (.cons (.app "nil" .nil) .nil)))) =
      some [Ty.list .never, Ty.nat, Ty.list .never, Ty.list .never] := by
    simp only [argsTy_cons, nilTy, capTy, noneTy, Option.bind_some]
  show (match Formation.check (Formation.sites false [] (.record (Queue.cellFields A))) with
    | some _ => none
    | none => (argsTy sig types true (.cons (.app "nil" .nil) (.cons (.lit (.nat capacity))
        (.cons (.app "nil" .nil) (.cons (.app "nil" .nil) .nil))))).bind
          (Record.check (Queue.cellFields A) ["msgs", "cap", "takers", "offers"])) = _
  rw [message.cell, values]
  show Record.check (Queue.cellFields A) ["msgs", "cap", "takers", "offers"]
    [Ty.list .never, Ty.nat, Ty.list .never, Ty.list .never] = _
  unfold Record.check
  show (if _ then some (Ty.normalize (.record (Queue.cellFields A))) else none) = _
  have named : (["msgs", "cap", "takers", "offers"] : List String).Nodup := by decide
  rw [if_pos ⟨named, named, fits⟩, cellFields_normal message.canonical]

/-- **The take step is typed at the cell's type**: under the request's identity, its hint and
the cell's value, it answers the pair of a take's reply and the cell's next value. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal takeStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "hint", "s"] [Queue.idTy, Queue.idTy, Queue.cellTy A]
        (Queue.takeStep A (var "id") (var "hint") (var "s")) =
      some (.prod (takeReplyTy A) (Queue.cellTy A))

/-- **The offer step is typed at the cell's type**: under the request's identity, its hint at
the answer's type, the message and the cell's value. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal offerStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "hint", "a", "s"] [Queue.idTy, Queue.answerTy, A, Queue.cellTy A]
        (Queue.offerStep A (var "id") (var "hint") (var "a") (var "s")) =
      some (.prod offerReplyTy (Queue.cellTy A))

/-- **The poll step is typed at the cell's type.** -/
@[semantics "store-typing" (requirement := R4)]
proof_goal pollStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["s"] [Queue.cellTy A] (Queue.pollStep A (var "s")) =
      some (.prod (pollReplyTy A) (Queue.cellTy A))

/-- **The size step is a number**, over the cell's value. It is no term of a `Ref.modify`. -/
@[semantics "store-typing" (requirement := R4)]
theorem sizeStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["s"] [Queue.cellTy A] (Queue.sizeStep A (var "s")) = some .nat := by
  show (termTy sig [Queue.cellTy A]
    (.app "length" (.cons (.field .required (.var 0) "msgs") .nil))) = some .nat
  show ((Record.fieldType false (Queue.cellTy A) "msgs").bind fun t =>
    (some [t])).bind (sig.atomOf "length") = some .nat
  rw [cell_msgsTy message.canonical, atoms]
  have below : Ty.sub (.list A) (.list .unknown) = true := by
    rw [Ty.sub_args_list]
    show (Ty.sub A .unknown && true) = true
    rw [Ty.sub_unknown]
    rfl
  show NativeAtom.monoApply [Ty.list .unknown] .nat [Ty.list A] = some .nat
  unfold NativeAtom.monoApply
  exact if_pos ⟨rfl, by
    show (Ty.sub (.list A) (.list .unknown) && true) = true
    rw [below]
    rfl⟩

/-- **The withdrawal of a take is typed at the cell's type.** -/
@[semantics "store-typing" (requirement := R4)]
proof_goal withdrawTake_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "s"] [Queue.idTy, Queue.cellTy A]
        (Queue.withdrawTake A (var "id") (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A))

/-- **The withdrawal of an offer is typed at the cell's type.** -/
@[semantics "store-typing" (requirement := R4)]
proof_goal withdrawOffer_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "s"] [Queue.idTy, Queue.cellTy A]
        (Queue.withdrawOffer A (var "id") (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A))

end Effect4.Queue.Model
