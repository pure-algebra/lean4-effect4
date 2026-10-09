import Effect4.Laws.Library.Pool.Passes
import Effect4.Laws.Library.Pool.Relation
import Effect4.Laws.Step
import Effect4.Laws.Step.Reading

/-!
# Reading Pool's step terms: the values of its records and of its passes (rows 267 to 269)

A step goal says that a step's source term reads a value (`Reads`,
`src/Effect4/Laws/Step/Reading.lean`). The shared reading rules give what each authoring
builder and each word of a step reads, and they serve here as they are. This file adds what
Pool's steps need beside them.

- **The three records**: what a read answers and what an overwrite stores, one `rfl` for each
  field of the cell, of an item and of a waiter.
The pass readers apply `Step.sound` to the stored Step data.
The independent model equations live in `Laws/Library/Pool/Passes.lean`.
The table's renewal law retains each other request's hint.
Fold readers supply the existing scope premise and deferred identity capability.

Placement. Concept `translation-simulation`, requirement R10. Every lemma here is a helper of
the six step goals (`src/Effect4/Laws/Library/Pool/Steps.lean`), parts of the proposed claim
`pool-expansion-agrees`. Its consumer is the proof of a step goal. The lemmas establish nothing
of a model's transition by themselves.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules Effect4.Schema Effect4.Schema.Model
open Effect4.Constructive.List (foldl_snoc_map foldl_or_any foldl_append_flatMap)

/-! ## The three records: what a read answers and what an overwrite stores -/

theorem cell_available (a c i n w : Val) :
    Machine.Record.read false (cellOf a c i n w) "available" = some a := rfl
theorem cell_closing (a c i n w : Val) :
    Machine.Record.read false (cellOf a c i n w) "closing" = some c := rfl
theorem cell_items (a c i n w : Val) :
    Machine.Record.read false (cellOf a c i n w) "items" = some i := rfl
theorem cell_next (a c i n w : Val) :
    Machine.Record.read false (cellOf a c i n w) "next" = some n := rfl
theorem cell_waiters (a c i n w : Val) :
    Machine.Record.read false (cellOf a c i n w) "waiters" = some w := rfl
theorem cell_setAvailable (a c i n w v : Val) :
    Machine.Record.set (cellOf a c i n w) "available" v = some (cellOf v c i n w) := rfl
theorem cell_setClosing (a c i n w v : Val) :
    Machine.Record.set (cellOf a c i n w) "closing" v = some (cellOf a v i n w) := rfl
theorem cell_setItems (a c i n w v : Val) :
    Machine.Record.set (cellOf a c i n w) "items" v = some (cellOf a c v n w) := rfl
theorem cell_setNext (a c i n w v : Val) :
    Machine.Record.set (cellOf a c i n w) "next" v = some (cellOf a c i v w) := rfl
theorem cell_setWaiters (a c i n w v : Val) :
    Machine.Record.set (cellOf a c i n w) "waiters" v = some (cellOf a c i n v) := rfl
theorem item_borrowed (b l r s : Val) :
    Machine.Record.read false (itemOf b l r s) "borrowed" = some b := rfl
theorem item_lease (b l r s : Val) :
    Machine.Record.read false (itemOf b l r s) "lease" = some l := rfl
theorem item_stamp (b l r s : Val) :
    Machine.Record.read false (itemOf b l r s) "stamp" = some s := rfl
theorem item_setBorrowed (b l r s v : Val) :
    Machine.Record.set (itemOf b l r s) "borrowed" v = some (itemOf v l r s) := rfl
theorem item_setLease (b l r s v : Val) :
    Machine.Record.set (itemOf b l r s) "lease" v = some (itemOf b v r s) := rfl
theorem waiter_id (h i : Val) : Machine.Record.read false (waiterOf h i) "id" = some i := rfl
theorem waiter_build (i h : Val) :
    Machine.Record.build ["id", "hint"] [i, h] = some (waiterOf h i) := rfl

/-! ## The table's one change frames every other request -/

/-- The record of a waiter of another identity stays. -/
theorem waiterVal_renew {tb : Table} {w id : Nat} (other : w ≠ id) (hint : DeferredKey) :
    waiterVal (tb.renew id hint) w = waiterVal tb w := by
  show waiterOf (Val.promise (if w = id then hint else tb.hint w)) (Val.promise (tb.handle w)) = _
  rw [if_neg other]
  rfl

/-- Waiters that are not the request keep their records. -/
theorem waiters_renew (tb : Table) (ws : List Nat) (id : Nat) (hint : DeferredKey)
    (others : ∀ w ∈ ws, w ≠ id) :
    ws.map (waiterVal (tb.renew id hint)) = ws.map (waiterVal tb) :=
  List.map_congr_left fun w member => waiterVal_renew (others w member) hint

/-- The request's own record, through the table that holds the step's hint. -/
theorem waiterVal_renewed (tb : Table) (id : Nat) (hint : DeferredKey) :
    waiterVal (tb.renew id hint) id =
      waiterOf (Val.promise hint) (Val.promise (tb.handle id)) := by
  show waiterOf (Val.promise (if id = id then hint else tb.hint id)) (Val.promise (tb.handle id)) = _
  rw [if_pos rfl]

/-- The cell of a state whose waiters are not the request reads the same through the renewed
table. -/
theorem cellVal_renew (tb : Table) (res : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (others : ∀ w ∈ s.waiters, w ≠ id) :
    cellVal (tb.renew id hint) res s = cellVal tb res s := by
  show cellOf _ _ _ _ (.list (s.waiters.map (waiterVal (tb.renew id hint)))) = _
  rw [waiters_renew tb s.waiters id hint others]
  rfl

/-! ## The passes, on the encoding of a model state -/

section Passes

variable {env : Env} {path : List Nat} {vals : List Val}

/-- `withdrawn`: the cell without the request, on the encoding of a model state. -/
theorem reads_withdrawn {id s : TermSrc} (tb : Table) (injective : tb.Injective)
    (res : Nat → Val) (state : State) (i : Nat) (depth : vals.length = env.names.length)
    (hid : Captured id env path vals (Val.promise (tb.handle i)))
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.withdrawn id s) env path vals (cellVal tb res (withdraw state i)) := by
  have h := Step.sound (Γ := [idTy, cellTy P]) Leaves.deferredKeys (tb.handle i, (cellC tb res state, ()))
    (Input.reads_cons hid.atScope (Input.reads_cons
      (hs.to (cellVal_image tb res state).symm) Input.reads_nil))
    (Data.withdrawn P (.var (.here _ _)) (.var (.there _ (.here _ _)))) rfl depth
      ⟨DeferredIdentity.deferredKeys⟩
  rw [withdrawn_eval tb injective res state i (.here idTy [cellTy P])
    (.there idTy (.here (cellTy P) [])) (tb.handle i, (cellC tb res state, ())) rfl rfl] at h
  exact h.to (cellVal_image tb res _)

/-- `noItem`: no item. -/
theorem reads_noItem {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.noItem s) env path vals Store.Val.none := by
  have h := Step.sound (Γ := [cellTy P]) Leaves.deferredKeys (cellC tb res state, ())
    (Input.reads_cons (hs.to (cellVal_image tb res state).symm) Input.reads_nil) (Data.noItem P (.var (.here _ _))) rfl
  exact h.to rfl

/-- `headStamp` reads the first idle stamp or zero through the native option operation.
The former fold-scope premise remains for source compatibility. -/
theorem reads_headStamp {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (depth : vals.length = env.names.length)
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.headStamp s) env path vals (Val.nat (state.available.headD 0)) := by
  have _retainedScope := depth
  have h := Step.sound (Γ := [cellTy P]) Leaves.deferredKeys (cellC tb res state, ())
    (Input.reads_cons (hs.to (cellVal_image tb res state).symm) Input.reads_nil) (Data.headStamp P (.var (.here _ _))) rfl
  rw [headStamp_eval tb res state (.here (cellTy P) []) (cellC tb res state, ()) rfl] at h
  exact h.to rfl

/-- `leasedAs`: an item's record as a lease of a stamp holds it. -/
theorem reads_leasedAs {lease it : TermSrc} (res : Nat → Val) (x : Item) (l : Nat)
    (hlease : Reads lease env path vals (Val.nat l))
    (hit : Reads it env path vals (itemVal res x)) :
    Reads (Pool.leasedAs lease it) env path vals (itemVal res (x.leasedAs l)) := by
  have h := Step.sound (Γ := [.nat, itemTy P]) Leaves.deferredKeys (l, (itemC res x, ()))
    (Input.reads_cons hlease (Input.reads_cons
      (hit.to (itemVal_image res x).symm) Input.reads_nil))
    (Data.leasedAs P (.var (.here _ _)) (.var (.there _ (.here _ _)))) rfl
  exact h.to rfl

/-- `holdsT`: whether a lease holds an item, at one item's record. -/
theorem reads_holdsT {i l it : TermSrc} (res : Nat → Val) (x : Item) (item lease : Nat)
    (hi : Reads i env path vals (Val.nat item)) (hl : Reads l env path vals (Val.nat lease))
    (hit : Reads it env path vals (itemVal res x)) :
    Reads (Pool.holdsT i l it) env path vals (Val.bool (x.heldBy item lease)) := by
  have h := Step.sound (Γ := [.nat, .nat, itemTy P]) Leaves.deferredKeys (item, (lease, (itemC res x, ())))
    (Input.reads_cons hi (Input.reads_cons hl
      (Input.reads_cons (hit.to (itemVal_image res x).symm) Input.reads_nil)))
    (Data.holds P (.var (.here _ _)) (.var (.there _ (.here _ _))) (.var (.there _ (.there _ (.here _ _))))) rfl
  rw [holds_eval res x item lease (.here .nat [.nat, itemTy P])
    (.there .nat (.here .nat [itemTy P])) (.there .nat (.there .nat (.here (itemTy P) [])))
    (item, (lease, (itemC res x, ()))) rfl rfl rfl] at h
  exact h.to rfl

/-- The test of the lease's two folds, under their binders: the folded item's stamp against
the front idle stamp of the caller's cell. -/
theorem reads_atFront {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State) (x : Item)
    (acc : Val) (depth : vals.length = env.names.length)
    (hs : Captured s env path vals (cellVal tb res state)) :
    Reads (app "eq" [field (minted (env.mint "item")) "stamp", Pool.headStamp s])
      (env.push [env.mint "acc", env.mint "item"]) path (vals ++ [acc, itemVal res x])
      (Val.bool (decide (x.stamp = state.available.headD 0))) :=
  reads_eq (reads_field (reads_minted_item depth path acc (itemVal res x)) (item_stamp _ _ _ _))
    (reads_headStamp tb res state
      (depth_under depth (env.mint "acc") (env.mint "item") acc (itemVal res x))
      (hs.underFold acc (itemVal res x)))

/-- The folded item as the next lease holds it, under a fold's binders. -/
theorem reads_leasedItem {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (x : Item) (acc : Val) (depth : vals.length = env.names.length)
    (hs : Captured s env path vals (cellVal tb res state)) :
    Reads (Pool.leasedAs (field s "next") (minted (env.mint "item")))
      (env.push [env.mint "acc", env.mint "item"]) path (vals ++ [acc, itemVal res x])
      (itemVal res (x.leasedAs state.next)) :=
  reads_leasedAs res x state.next
    (reads_field (hs.underFold acc (itemVal res x)) (cell_next _ _ _ _ _))
    (reads_minted_item depth path acc (itemVal res x))

/-- `marked`: the items, with the front idle item leased at the stamp `next`. The cell stands
in the fold's body, so it is a caller's term under a fold. -/
theorem reads_marked {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (depth : vals.length = env.names.length)
    (hs : Captured s env path vals (cellVal tb res state)) :
    Reads (Pool.marked s) env path vals
      (Val.list ((mark state.items (state.available.headD 0) state.next).map (itemVal res))) := by
  have h := Step.sound (Γ := [cellTy P]) Leaves.deferredKeys (cellC tb res state, ())
    (Input.reads_cons (hs.atScope.to (cellVal_image tb res state).symm) Input.reads_nil) (Data.marked P (.var (.here _ _))) rfl depth
  rw [marked_eval tb res state (.here (cellTy P) []) (cellC tb res state, ()) rfl] at h
  exact h.to (items_image res _)

/-- `leasedOf`: the front idle item as its new lease holds it. Its first entry is the model's
`leased`. -/
theorem reads_leasedOf {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (depth : vals.length = env.names.length)
    (hs : Captured s env path vals (cellVal tb res state)) :
    Reads (Pool.leasedOf s) env path vals
      (Val.list ((state.items.flatMap fun it =>
        if it.stamp = state.available.headD 0 then [it.leasedAs state.next] else []).map
          (itemVal res))) := by
  have h := Step.sound (Γ := [cellTy P]) Leaves.deferredKeys (cellC tb res state, ())
    (Input.reads_cons (hs.atScope.to (cellVal_image tb res state).symm) Input.reads_nil) (Data.leasedOf P (.var (.here _ _))) rfl depth
  rw [leasedOf_list_eval tb res state (.here (cellTy P) []) (cellC tb res state, ()) rfl] at h
  exact h.to (items_image res _)

/-- `heldBy`: whether a lease holds an item. The two stamps stand in the fold's body. -/
theorem reads_heldBy {i l s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (item lease : Nat) (depth : vals.length = env.names.length)
    (hi : Captured i env path vals (Val.nat item)) (hl : Captured l env path vals (Val.nat lease))
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.heldBy i l s) env path vals
      (Val.bool (state.items.any (·.heldBy item lease))) := by
  have h := Step.sound (Γ := Data.returnΓ P) Leaves.deferredKeys (item, (lease, (cellC tb res state, ())))
    (Input.reads_cons hi.atScope (Input.reads_cons hl.atScope
      (Input.reads_cons (hs.to (cellVal_image tb res state).symm) Input.reads_nil)))
    (Data.heldBy P (Data.returnStamp P) (Data.returnLease P) (Data.returnCell P)) rfl depth
  rw [heldBy_eval tb res state item lease (Data.returnStamp P) (Data.returnLease P)
    (Data.returnCell P) (item, (lease, (cellC tb res state, ()))) rfl rfl rfl] at h
  exact h.to rfl

/-- `freed`: the items, with the item that the lease holds idle again. -/
theorem reads_freed {i l s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (item lease : Nat) (depth : vals.length = env.names.length)
    (hi : Captured i env path vals (Val.nat item)) (hl : Captured l env path vals (Val.nat lease))
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.freed i l s) env path vals
      (Val.list ((freed state.items item lease).map (itemVal res))) := by
  have h := Step.sound (Γ := Data.returnΓ P) Leaves.deferredKeys (item, (lease, (cellC tb res state, ())))
    (Input.reads_cons hi.atScope (Input.reads_cons hl.atScope
      (Input.reads_cons (hs.to (cellVal_image tb res state).symm) Input.reads_nil)))
    (Data.freed P (Data.returnStamp P) (Data.returnLease P) (Data.returnCell P)) rfl depth
  rw [freed_eval tb res state item lease (Data.returnStamp P) (Data.returnLease P)
    (Data.returnCell P) (item, (lease, (cellC tb res state, ()))) rfl rfl rfl] at h
  exact h.to (items_image res _)

/-- `outstanding`: whether a lease is outstanding, on the encoding of a model state. -/
theorem reads_outstanding {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (depth : vals.length = env.names.length)
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.outstanding s) env path vals (Val.bool (state.items.any (·.borrowed))) := by
  have h := Step.sound (Γ := [cellTy P]) Leaves.deferredKeys (cellC tb res state, ())
    (Input.reads_cons (hs.to (cellVal_image tb res state).symm) Input.reads_nil) (Data.outstanding P (.var (.here _ _))) rfl depth
  rw [outstanding_eval tb res state (.here (cellTy P) []) (cellC tb res state, ()) rfl] at h
  exact h.to rfl

/-- A waiter's record, built from an identity and a hint. -/
theorem reads_mkWaiter {id hint : TermSrc} {i h : Val} (hid : Reads id env path vals i)
    (hhint : Reads hint env path vals h) :
    Reads (Pool.mkWaiter id hint) env path vals (waiterOf h i) := by
  have h := Step.sound (Γ := [idTy, idTy]) Leaves.opaque (i, (h, ()))
    (Input.reads_cons hid (Input.reads_cons hhint Input.reads_nil))
    (Data.mkWaiter (.var (.here _ _)) (.var (.there _ (.here _ _)))) rfl
  exact h.to rfl

end Passes

end Effect4.Pool.Model
