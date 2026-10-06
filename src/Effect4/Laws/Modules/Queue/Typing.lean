import Effect4.Modules.Queue.Steps
import Effect4.Program.Typing
import Effect4.Program.Native
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
a target. Each is a planned goal (`proof_goal`, decisions row 203) until its proof replaces it
in place. The finite controls are in `Test/Program/QueueSteps.lean`: each statement at 27
message types, with red controls.
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

/-! ## The statements -/

/-- **The initial value has the cell's type**, at every capacity and in every scope. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal empty_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (capacity : Nat) (names : List String) (types : List Ty) :
    typeAt sig names types (Queue.empty A capacity) = some (Queue.cellTy A)

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
proof_goal sizeStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["s"] [Queue.cellTy A] (Queue.sizeStep A (var "s")) = some .nat

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
