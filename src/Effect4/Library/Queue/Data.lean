module

public import Effect4.Library.Queue.Cell
public import Effect4.Step.Lists
public import Effect4.Step.Inputs
meta import Effect4.Step.Elab.Inputs
public meta import Effect4.Step.Elab

/-! Queue pure operations as typed first-order steps. Canonical schemas live in Cell.
The fold bodies bind accumulator and item before their original operation inputs.
Their consumers are Queue model agreement and typing, under decisions row 330. -/

@[expose] public section
namespace Effect4.Queue.Data
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

theorem cellTy_eq (A : Ty) : cellTy A = .record (cellRecord A) := rfl

def msgsF (A : Ty) : FieldRef (cellRecord A) (.list A) := field_ref% "msgs"
def capF (A : Ty) : FieldRef (cellRecord A) .nat := field_ref% "cap"
def takersF (A : Ty) : FieldRef (cellRecord A) (.list takerTy) := field_ref% "takers"
def offersF (A : Ty) : FieldRef (cellRecord A) (.list (offerTy A)) := field_ref% "offers"
def takerIdF : FieldRef takerRecord idTy := field_ref% "id"
def takerHintF : FieldRef takerRecord idTy := field_ref% "hint"
def offerIdF (A : Ty) : FieldRef (offerRecord A) idTy := field_ref% "id"
def offerRestF (A : Ty) : FieldRef (offerRecord A) (.list A) := field_ref% "rest"

def mkTaker {Γ : List Ty} (id hint : Step Γ idTy) : Step Γ takerTy :=
  record_step% { id := id, hint := hint }
def mkOffer {Γ : List Ty} (A : Ty) (id : Step Γ idTy) (hint : Step Γ answerTy)
    (batch : Step Γ .bool) (rest : Step Γ (.list A)) : Step Γ (offerTy A) :=
  record_step% { id := id, hint := hint, batch := batch, rest := rest }

def enrolled {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Step Γ idTy) : Step Γ .bool :=
  Step.Lists.any ts (item_step% ts with entry => .sameDeferred (.get entry takerIdF) id)
def isHead {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Step Γ idTy) : Step Γ .bool :=
  Step.Lists.any (.take ts (.nat 1))
    (item_step% ts with entry => .sameDeferred (.get entry takerIdF) id)
def removeTaker {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Step Γ idTy) : Step Γ (.list takerTy) :=
  Step.Lists.removeBy ts (item_step% ts with entry => .sameDeferred (.get entry takerIdF) id)
def renewHint {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id hint : Step Γ idTy) : Step Γ (.list takerTy) :=
  Step.Lists.map ts (item_step% ts with entry =>
    .ite (.sameDeferred (.get entry takerIdF) id) (mkTaker id hint) entry)
def removeOffer {Γ : List Ty} (A : Ty) (os : Step Γ (.list (offerTy A))) (id : Step Γ idTy) : Step Γ (.list (offerTy A)) :=
  Step.Lists.removeBy os (item_step% os with entry => .sameDeferred (.get entry (offerIdF A)) id)
def wake {Γ : List Ty} (A : Ty) (ts : Step Γ (.list takerTy)) (ms : Step Γ (.list A)) : Step Γ (.list takerTy) :=
  .ite (.isZero (.len ms)) (.emptyLike ts) (.take ts (.nat 1))
def fitting {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (os : Step Γ (.list (offerTy A))) : Step Γ .nat :=
  .ite (.lt room (.len os)) room (.len os)
def entering {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (os : Step Γ (.list (offerTy A))) : Step Γ (.list (offerTy A)) :=
  .take os (fitting A room os)
def staying {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (os : Step Γ (.list (offerTy A))) : Step Γ (.list (offerTy A)) :=
  .drop os (fitting A room os)
def gained {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (ms : Step Γ (.list A)) (os : Step Γ (.list (offerTy A))) : Step Γ (.list A) :=
  fold_step% (entering A room os) from buffer := ms with entry =>
    .append buffer (.get entry (offerRestF A))

step_context% CellInputs (A : Ty) where (state : cellTy A)
step_context% TakeInputs (A : Ty) where (id : idTy, hint : idTy, state : cellTy A)
step_context% OfferInputs (A : Ty) where (id : idTy, hint : answerTy, message : A, state : cellTy A)
step_context% WithdrawInputs (A : Ty) where (id : idTy, state : cellTy A)

def cell (A : Ty) : Input (CellInputs A).types (cellTy A) := input_ref% (CellInputs A) state
def size (A : Ty) : Step (CellInputs A).types .nat :=
  step_inputs% (CellInputs A) => .len (.get state (msgsF A))
def takeΓ (A : Ty) : List Ty := (TakeInputs A).types
def offerΓ (A : Ty) : List Ty := (OfferInputs A).types
def withdrawΓ (A : Ty) : List Ty := (WithdrawInputs A).types

def take (A : Ty) : Step (takeΓ A) (.prod (.tuple [.option A, .list (offerTy A), .list takerTy]) (cellTy A)) :=
  step_inputs% (TakeInputs A) =>
  let s := state
  let ms := .get s (msgsF A); let ts := .get s (takersF A); let os := .get s (offersF A)
  let turn := .or (isHead ts id) (.and (.not (enrolled ts id)) (.isZero (.len ts)))
  let ms1 := .drop ms (.nat 1); let ts1 := removeTaker ts id
  let room := .sub (.get s (capF A)) (.len ms1)
  let ms2 := gained A room ms1 os
  let consumed := .set (.set (.set s (msgsF A) ms2) (takersF A) ts1) (offersF A) (staying A room os)
  let waiting := .set s (takersF A) (.ite (enrolled ts id) (renewHint ts id hint) (.snoc ts (mkTaker id hint)))
  .ite (.and (.not (.isZero (.len ms))) turn)
    (.pair (.tuple3 (.head ms) (entering A room os) (wake A ts1 ms2)) consumed)
    (.pair (.tuple3 .none (.emptyLike os) (.emptyLike ts)) waiting)

def offer (A : Ty) : Step (offerΓ A) (.prod (.prod (.option .bool) (.list takerTy)) (cellTy A)) :=
  step_inputs% (OfferInputs A) =>
  let a := message; let s := state
  let ms := .get s (msgsF A); let os := .get s (offersF A); let ts := .get s (takersF A)
  let pending := .set s (offersF A) (.snoc os (mkOffer A id hint (.bool false) (.cons a .nil)))
  let accepted := .set s (msgsF A) (.snoc ms a)
  .ite (.not (.isZero (.len os))) (.pair (.tuple2 .none (.emptyLike ts)) pending)
    (.ite (.lt (.len ms) (.get s (capF A)))
      (.pair (.tuple2 (.some (.bool true)) (wake A ts (.snoc ms a))) accepted)
      (.pair (.tuple2 .none (wake A ts ms)) pending))

def poll (A : Ty) : Step [cellTy A] (.prod (.prod (.option A) (.list (offerTy A))) (cellTy A)) :=
  step_inputs% (CellInputs A) =>
  let s := state
  let ms := .get s (msgsF A); let os := .get s (offersF A)
  let ms1 := .drop ms (.nat 1); let room := .sub (.get s (capF A)) (.len ms1)
  let consumed := .set (.set s (msgsF A) (gained A room ms1 os)) (offersF A) (staying A room os)
  .ite (.and (.not (.isZero (.len ms))) (.isZero (.len (.get s (takersF A)))))
    (.pair (.tuple2 (.head ms) (entering A room os)) consumed)
    (.pair (.tuple2 .none (.emptyLike os)) s)

def withdrawTake (A : Ty) : Step (withdrawΓ A) (.prod (.list takerTy) (cellTy A)) :=
  step_inputs% (WithdrawInputs A) =>
  let s := state
  let ts1 := removeTaker (.get s (takersF A)) id
  .pair (wake A ts1 (.get s (msgsF A))) (.set s (takersF A) ts1)
def withdrawOffer (A : Ty) : Step (withdrawΓ A) (.prod (.list takerTy) (cellTy A)) :=
  step_inputs% (WithdrawInputs A) =>
  let s := state
  .pair (wake A (.get s (takersF A)) (.get s (msgsF A)))
    (.set s (offersF A) (removeOffer A (.get s (offersF A)) id))
end Effect4.Queue.Data
