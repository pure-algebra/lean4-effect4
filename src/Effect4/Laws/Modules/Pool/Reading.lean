import Effect4.Laws.Modules.Pool.Relation
import Effect4.Laws.Modules.Reading

/-!
# Reading Pool's step terms: the values of its records and of its passes (rows 267 to 269)

A step goal says that a step's source term reads a value (`Reads`,
`src/Effect4/Laws/Modules/Reading.lean`). The shared reading rules give what each authoring
builder and each word of a step reads, and they serve here as they are. This file adds what
Pool's steps need beside them.

- **The three records**: what a read answers and what an overwrite stores, one `rfl` for each
  field of the cell, of an item and of a waiter.
- **The removal by identity** (`reads_withdrawn`): one application of the shared rule of the
  pass `removeById` (`reads_removeById`), at a waiter's record.
- **The table's one change frames every other request** (`waiters_renew`).
- **The passes** of `src/Effect4/Modules/Pool/Steps.lean` on the encoding of a model state: the
  front idle stamp, the two folds of a lease, the two folds of a return, and the fold of the
  closer's step.
- **Two facts of Pool's own definitions** put a fold's answer in the model's form: the first
  entry's fold is the front stamp (`front_headD`), and the fold that keeps the leased item is
  the model's `leased` (`leased_flatMap`).

The lease's two folds over the items read the front idle stamp in their bodies, by a fold of
its own. Its rule holds at every scope, so it is applied under the outer fold's binders, at the
depth that `depth_under` gives.

Placement. Concept `translation-simulation`, requirement R10. Every lemma here is a helper of
the six step goals (`src/Effect4/Laws/Modules/Pool/Steps.lean`), parts of the proposed claim
`pool-expansion-agrees`. Its consumer is the proof of a step goal. The lemmas establish nothing
of a model's transition by themselves.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
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

/-! ## Two facts of Pool's own definitions -/

/-- The fold over the first idle stamp answers the front stamp, or zero. -/
theorem front_headD : ∀ (stamps : List Nat),
    (stamps.take 1).foldl (fun _ stamp => stamp) 0 = stamps.headD 0
  | [] => rfl
  | _ :: _ => rfl

/-- The fold that keeps the front item as leased answers the model's `leased`. -/
theorem leased_flatMap (items : List Item) (i l : Nat) :
    (items.flatMap fun it => if it.stamp = i then [it.leasedAs l] else [])[0]? =
      leased items i l := by
  unfold leased
  induction items with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.filter_cons]
    by_cases same : x.stamp = i
    · rw [if_pos same, decide_eq_true same, if_pos rfl]
      rfl
    · rw [if_neg same, decide_eq_false same, if_neg Bool.false_ne_true, List.nil_append]
      exact ih

/-! ## The passes, on the encoding of a model state -/

section Passes

variable {env : Env} {path : List Nat} {vals : List Val}

/-- `withdrawn`: the cell without the request, on the encoding of a model state. -/
theorem reads_withdrawn {id s : TermSrc} (tb : Table) (injective : tb.Injective)
    (res : Nat → Val) (state : State) (i : Nat) (depth : vals.length = env.names.length)
    (hid : Captured id env path vals (Val.promise (tb.handle i)))
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.withdrawn id s) env path vals (cellVal tb res (withdraw state i)) :=
  reads_recordSet hs
    (reads_removeById tb injective (waiterVal tb) (fun w => w) (fun _ => waiter_id _ _) 0
      state.waiters i depth (reads_field hs (cell_waiters _ _ _ _ _)) hid)
    (cell_setWaiters _ _ _ _ _ _)

/-- `noItem`: no item. -/
theorem reads_noItem {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.noItem s) env path vals Store.Val.none :=
  reads_head (reads_noneOf (reads_field hs (cell_items _ _ _ _ _)))

/-- `headStamp`: the stamp at the front of the idle stamps, or zero. A fold whose body reads no
caller's term, so the rule holds at every scope, and under another fold's binders too. -/
theorem reads_headStamp {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (depth : vals.length = env.names.length)
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.headStamp s) env path vals (Val.nat (state.available.headD 0)) := by
  have first : Reads (app "take" [field s "available", nat 1]) env path vals
      (Val.list ((state.available.take 1).map Val.nat)) :=
    (reads_take (reads_field hs (cell_available _ _ _ _ _)) (reads_nat 1 env path vals)).to
      (by rw [← List.map_take])
  have folded := reads_foldWith_model Val.nat Val.nat (fun _ stamp => stamp)
    (state.available.take 1) 0 0 first (reads_nat 0 env path vals)
    (body := fun _ stamp => stamp)
    fun b x => reads_minted_item depth path (Val.nat b) (Val.nat x)
  exact folded.to (congrArg Val.nat (front_headD state.available))

/-- `leasedAs`: an item's record as a lease of a stamp holds it. -/
theorem reads_leasedAs {lease it : TermSrc} (res : Nat → Val) (x : Item) (l : Nat)
    (hlease : Reads lease env path vals (Val.nat l))
    (hit : Reads it env path vals (itemVal res x)) :
    Reads (Pool.leasedAs lease it) env path vals (itemVal res (x.leasedAs l)) :=
  reads_recordSet
    (reads_recordSet hit (reads_bool true env path vals) (item_setBorrowed _ _ _ _ _)) hlease
    (item_setLease _ _ _ _ _)

/-- `holdsT`: whether a lease holds an item, at one item's record. -/
theorem reads_holdsT {i l it : TermSrc} (res : Nat → Val) (x : Item) (item lease : Nat)
    (hi : Reads i env path vals (Val.nat item)) (hl : Reads l env path vals (Val.nat lease))
    (hit : Reads it env path vals (itemVal res x)) :
    Reads (Pool.holdsT i l it) env path vals (Val.bool (x.heldBy item lease)) :=
  reads_andT (reads_eq (reads_field hit (item_stamp _ _ _ _)) hi)
    (reads_andT (reads_field hit (item_borrowed _ _ _ _))
      (reads_eq (reads_field hit (item_lease _ _ _ _)) hl))

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
  have items := reads_field hs.atScope (cell_items _ _ _ _ _)
  have folded := reads_foldWith_model (itemVal res)
    (fun out : List Item => Val.list (out.map (itemVal res)))
    (fun out it =>
      out ++ [if it.stamp = state.available.headD 0 then it.leasedAs state.next else it])
    state.items [] ⟨0, 0, false, 0⟩ items (reads_noneOf items)
    (body := fun out it =>
      snoc out (ifT (app "eq" [field it "stamp", Pool.headStamp s])
        (Pool.leasedAs (field s "next") it) it))
    fun out x => by
      have acc := reads_minted_acc depth path (Val.list (out.map (itemVal res))) (itemVal res x)
      have item := reads_minted_item depth path (Val.list (out.map (itemVal res))) (itemVal res x)
      refine (reads_snoc acc
        (reads_ifT (reads_atFront tb res state x _ depth hs)
          (reads_leasedItem tb res state x _ depth hs) item)).to ?_
      by_cases same : x.stamp = state.available.headD 0
      · rw [decide_eq_true same, if_pos rfl, if_pos same, List.map_append]
        rfl
      · rw [decide_eq_false same, if_neg Bool.false_ne_true, if_neg same, List.map_append]
        rfl
  exact folded.to (by rw [foldl_snoc_map, List.nil_append]; rfl)

/-- `leasedOf`: the front idle item as its new lease holds it. Its first entry is the model's
`leased`. -/
theorem reads_leasedOf {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (depth : vals.length = env.names.length)
    (hs : Captured s env path vals (cellVal tb res state)) :
    Reads (Pool.leasedOf s) env path vals
      (Val.list ((state.items.flatMap fun it =>
        if it.stamp = state.available.headD 0 then [it.leasedAs state.next] else []).map
          (itemVal res))) := by
  have items := reads_field hs.atScope (cell_items _ _ _ _ _)
  have folded := reads_foldWith_model (itemVal res)
    (fun kept : List Item => Val.list (kept.map (itemVal res)))
    (fun kept it =>
      kept ++ (if it.stamp = state.available.headD 0 then [it.leasedAs state.next] else []))
    state.items [] ⟨0, 0, false, 0⟩ items (reads_noneOf items)
    (body := fun kept it =>
      ifT (app "eq" [field it "stamp", Pool.headStamp s])
        (snoc kept (Pool.leasedAs (field s "next") it)) kept)
    fun kept x => by
      have acc := reads_minted_acc depth path (Val.list (kept.map (itemVal res))) (itemVal res x)
      refine (reads_ifT (reads_atFront tb res state x _ depth hs)
        (reads_snoc acc (reads_leasedItem tb res state x _ depth hs)) acc).to ?_
      by_cases same : x.stamp = state.available.headD 0
      · rw [decide_eq_true same, if_pos rfl, if_pos same, List.map_append]
        rfl
      · rw [decide_eq_false same, if_neg Bool.false_ne_true, if_neg same, List.append_nil]
  exact folded.to (by rw [foldl_append_flatMap, List.nil_append])

/-- `heldBy`: whether a lease holds an item. The two stamps stand in the fold's body. -/
theorem reads_heldBy {i l s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (item lease : Nat) (depth : vals.length = env.names.length)
    (hi : Captured i env path vals (Val.nat item)) (hl : Captured l env path vals (Val.nat lease))
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.heldBy i l s) env path vals
      (Val.bool (state.items.any (·.heldBy item lease))) := by
  have folded := reads_foldWith_model (itemVal res) Val.bool
    (fun found it => found || it.heldBy item lease) state.items false ⟨0, 0, false, 0⟩
    (reads_field hs (cell_items _ _ _ _ _)) (reads_bool false env path vals)
    (body := fun found it => orT found (Pool.holdsT i l it))
    fun found x =>
      reads_orT (reads_minted_acc depth path (Val.bool found) (itemVal res x))
        (reads_holdsT res x item lease (hi.underFold _ _) (hl.underFold _ _)
          (reads_minted_item depth path (Val.bool found) (itemVal res x)))
  exact folded.to (by rw [foldl_or_any, Bool.false_or])

/-- `freed`: the items, with the item that the lease holds idle again. -/
theorem reads_freed {i l s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (item lease : Nat) (depth : vals.length = env.names.length)
    (hi : Captured i env path vals (Val.nat item)) (hl : Captured l env path vals (Val.nat lease))
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.freed i l s) env path vals
      (Val.list ((freed state.items item lease).map (itemVal res))) := by
  have items := reads_field hs (cell_items _ _ _ _ _)
  have folded := reads_foldWith_model (itemVal res)
    (fun out : List Item => Val.list (out.map (itemVal res)))
    (fun out it =>
      out ++ [if it.heldBy item lease = true then { it with borrowed := false } else it])
    state.items [] ⟨0, 0, false, 0⟩ items (reads_noneOf items)
    (body := fun out it =>
      snoc out (ifT (Pool.holdsT i l it) (recordSet it "borrowed" (bool false)) it))
    fun out x => by
      have acc := reads_minted_acc depth path (Val.list (out.map (itemVal res))) (itemVal res x)
      have entry := reads_minted_item depth path (Val.list (out.map (itemVal res)))
        (itemVal res x)
      refine (reads_snoc acc
        (reads_ifT (reads_holdsT res x item lease (hi.underFold _ _) (hl.underFold _ _) entry)
          (reads_recordSet entry (reads_bool false _ path _) (item_setBorrowed _ _ _ _ _))
          entry)).to ?_
      by_cases holds : x.heldBy item lease = true
      · rw [holds, if_pos rfl, if_pos rfl, List.map_append]
        rfl
      · rw [Bool.not_eq_true] at holds
        rw [holds, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, List.map_append]
        rfl
  exact folded.to (by rw [foldl_snoc_map, List.nil_append]; rfl)

/-- `outstanding`: whether a lease is outstanding, on the encoding of a model state. -/
theorem reads_outstanding {s : TermSrc} (tb : Table) (res : Nat → Val) (state : State)
    (depth : vals.length = env.names.length)
    (hs : Reads s env path vals (cellVal tb res state)) :
    Reads (Pool.outstanding s) env path vals (Val.bool (state.items.any (·.borrowed))) := by
  have folded := reads_foldWith_model (itemVal res) Val.bool
    (fun found it => found || it.borrowed) state.items false ⟨0, 0, false, 0⟩
    (reads_field hs (cell_items _ _ _ _ _)) (reads_bool false env path vals)
    (body := fun found it => orT found (field it "borrowed"))
    fun found x =>
      reads_orT (reads_minted_acc depth path (Val.bool found) (itemVal res x))
        (reads_field (reads_minted_item depth path (Val.bool found) (itemVal res x))
          (item_borrowed _ _ _ _))
  exact folded.to (by rw [foldl_or_any, Bool.false_or])

/-- A waiter's record, built from an identity and a hint. -/
theorem reads_mkWaiter {id hint : TermSrc} {i h : Val} (hid : Reads id env path vals i)
    (hhint : Reads hint env path vals h) :
    Reads (Pool.mkWaiter id hint) env path vals (waiterOf h i) :=
  reads_record (.cons hid (.cons hhint .nil)) (waiter_build i h)

end Passes

end Effect4.Pool.Model
