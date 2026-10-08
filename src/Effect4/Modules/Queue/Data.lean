module

public import Effect4.Modules.Queue.Cell
public import Effect4.Modules.Step
public meta import Effect4.Modules.Step.Elab

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

def lift2 {Γ : List Ty} {a b t : Ty} (x : Input Γ t) : Input (a :: b :: Γ) t :=
  .there _ (.there _ x)
def acc {Γ : List Ty} {a b : Ty} : Input (a :: b :: Γ) a := .here _ _
def item {Γ : List Ty} {a b : Ty} : Input (a :: b :: Γ) b := .there _ (.here _ _)

def mkTaker {Γ : List Ty} (id hint : Step Γ idTy) : Step Γ takerTy :=
  record_step% { id := id, hint := hint }
def mkOffer {Γ : List Ty} (A : Ty) (id : Step Γ idTy) (hint : Step Γ answerTy)
    (batch : Step Γ .bool) (rest : Step Γ (.list A)) : Step Γ (offerTy A) :=
  record_step% { id := id, hint := hint, batch := batch, rest := rest }

def enrolled {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Input Γ idTy) : Step Γ .bool :=
  .fold ts (.bool false) (.or (.var acc) (.sameDeferred (.get (.var item) takerIdF) (.var (lift2 id))))
def isHead {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Input Γ idTy) : Step Γ .bool :=
  .fold (.take ts (.nat 1)) (.bool false) (.sameDeferred (.get (.var item) takerIdF) (.var (lift2 id)))
def removeTaker {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Input Γ idTy) : Step Γ (.list takerTy) :=
  .fold ts (.emptyLike ts) (.ite (.sameDeferred (.get (.var item) takerIdF) (.var (lift2 id)))
    (.var acc) (.snoc (.var acc) (.var item)))
def renewHint {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id hint : Input Γ idTy) : Step Γ (.list takerTy) :=
  .fold ts (.emptyLike ts) (.snoc (.var acc)
    (.ite (.sameDeferred (.get (.var item) takerIdF) (.var (lift2 id)))
      (mkTaker (.var (lift2 id)) (.var (lift2 hint))) (.var item)))
def removeOffer {Γ : List Ty} (A : Ty) (os : Step Γ (.list (offerTy A))) (id : Input Γ idTy) : Step Γ (.list (offerTy A)) :=
  .fold os (.emptyLike os) (.ite (.sameDeferred (.get (.var item) (offerIdF A)) (.var (lift2 id)))
    (.var acc) (.snoc (.var acc) (.var item)))
def wake {Γ : List Ty} (A : Ty) (ts : Step Γ (.list takerTy)) (ms : Step Γ (.list A)) : Step Γ (.list takerTy) :=
  .ite (.isZero (.len ms)) (.emptyLike ts) (.take ts (.nat 1))
def fitting {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (os : Step Γ (.list (offerTy A))) : Step Γ .nat :=
  .ite (.lt room (.len os)) room (.len os)
def entering {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (os : Step Γ (.list (offerTy A))) : Step Γ (.list (offerTy A)) :=
  .take os (fitting A room os)
def staying {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (os : Step Γ (.list (offerTy A))) : Step Γ (.list (offerTy A)) :=
  .drop os (fitting A room os)
def gained {Γ : List Ty} (A : Ty) (room : Step Γ .nat) (ms : Step Γ (.list A)) (os : Step Γ (.list (offerTy A))) : Step Γ (.list A) :=
  .fold (entering A room os) ms (.append (.var acc) (.get (.var item) (offerRestF A)))

def cell (A : Ty) : Input [cellTy A] (cellTy A) := .here _ _
def size (A : Ty) : Step [cellTy A] .nat := .len (.get (.var (cell A)) (msgsF A))
def takeΓ (A : Ty) : List Ty := [idTy, idTy, cellTy A]
def offerΓ (A : Ty) : List Ty := [idTy, answerTy, A, cellTy A]
def withdrawΓ (A : Ty) : List Ty := [idTy, cellTy A]

def take (A : Ty) : Step (takeΓ A) (.prod (.tuple [.option A, .list (offerTy A), .list takerTy]) (cellTy A)) :=
  let id : Input (takeΓ A) idTy := .here _ _
  let hint : Input (takeΓ A) idTy := .there _ (.here _ _)
  let s : Step (takeΓ A) (cellTy A) := .var (.there _ (.there _ (.here _ _)))
  let ms := .get s (msgsF A); let ts := .get s (takersF A); let os := .get s (offersF A)
  let turn := .or (isHead ts id) (.and (.not (enrolled ts id)) (.isZero (.len ts)))
  let ms1 := .drop ms (.nat 1); let ts1 := removeTaker ts id
  let room := .sub (.get s (capF A)) (.len ms1)
  let ms2 := gained A room ms1 os
  let consumed := .set (.set (.set s (msgsF A) ms2) (takersF A) ts1) (offersF A) (staying A room os)
  let waiting := .set s (takersF A) (.ite (enrolled ts id) (renewHint ts id hint) (.snoc ts (mkTaker (.var id) (.var hint))))
  .ite (.and (.not (.isZero (.len ms))) turn)
    (.pair (.tuple3 (.head ms) (entering A room os) (wake A ts1 ms2)) consumed)
    (.pair (.tuple3 .none (.emptyLike os) (.emptyLike ts)) waiting)

def offer (A : Ty) : Step (offerΓ A) (.prod (.prod (.option .bool) (.list takerTy)) (cellTy A)) :=
  let id : Step (offerΓ A) idTy := .var (.here _ _)
  let hint : Step (offerΓ A) answerTy := .var (.there _ (.here _ _))
  let a : Step (offerΓ A) A := .var (.there _ (.there _ (.here _ _)))
  let s : Step (offerΓ A) (cellTy A) := .var (.there _ (.there _ (.there _ (.here _ _))))
  let ms := .get s (msgsF A); let os := .get s (offersF A); let ts := .get s (takersF A)
  let pending := .set s (offersF A) (.snoc os (mkOffer A id hint (.bool false) (.cons a .nil)))
  let accepted := .set s (msgsF A) (.snoc ms a)
  .ite (.not (.isZero (.len os))) (.pair (.tuple2 .none (.emptyLike ts)) pending)
    (.ite (.lt (.len ms) (.get s (capF A)))
      (.pair (.tuple2 (.some (.bool true)) (wake A ts (.snoc ms a))) accepted)
      (.pair (.tuple2 .none (wake A ts ms)) pending))

def poll (A : Ty) : Step [cellTy A] (.prod (.prod (.option A) (.list (offerTy A))) (cellTy A)) :=
  let s := Step.var (cell A)
  let ms := .get s (msgsF A); let os := .get s (offersF A)
  let ms1 := .drop ms (.nat 1); let room := .sub (.get s (capF A)) (.len ms1)
  let consumed := .set (.set s (msgsF A) (gained A room ms1 os)) (offersF A) (staying A room os)
  .ite (.and (.not (.isZero (.len ms))) (.isZero (.len (.get s (takersF A)))))
    (.pair (.tuple2 (.head ms) (entering A room os)) consumed)
    (.pair (.tuple2 .none (.emptyLike os)) s)

def withdrawTake (A : Ty) : Step (withdrawΓ A) (.prod (.list takerTy) (cellTy A)) :=
  let id : Input (withdrawΓ A) idTy := .here _ _
  let s : Step (withdrawΓ A) (cellTy A) := .var (.there _ (.here _ _))
  let ts1 := removeTaker (.get s (takersF A)) id
  .pair (wake A ts1 (.get s (msgsF A))) (.set s (takersF A) ts1)
def withdrawOffer (A : Ty) : Step (withdrawΓ A) (.prod (.list takerTy) (cellTy A)) :=
  let id : Input (withdrawΓ A) idTy := .here _ _
  let s : Step (withdrawΓ A) (cellTy A) := .var (.there _ (.here _ _))
  .pair (wake A (.get s (takersF A)) (.get s (msgsF A)))
    (.set s (offersF A) (removeOffer A (.get s (offersF A)) id))
end Effect4.Queue.Data
