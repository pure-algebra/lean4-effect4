import Effect4.Laws.Modules.Pool.Data
import Effect4.Laws.Schema.Identity

/-! Pool's pass values on the shared Step carriers.
Concept: Translation Simulation; helpers of the existing `pool-steps-agree` claim, requirement R10.
The consumers are Pool's unchanged pass readers and operation agreement statements.
Identity removal retains the table's injectivity; list passes retain the independent model.
These equations establish no wrapper, allocation, membership, progress, or host execution law. -/

set_option autoImplicit false

namespace Effect4.Pool.Model
open Effect4 Effect4.Machine Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.Constructive.List

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


abbrev ItemCarrier := Bool × Nat × Val × Nat × Unit
abbrev CellCarrier := List Nat × Bool × List ItemCarrier × Nat × List (DeferredKey × DeferredKey × Unit) × Unit

theorem lease_enrols {s : State} (id : Nat) (open_ : s.closing = false)
    (empty : s.available = []) :
    lease s id = ({ s with waiters := without s.waiters id ++ [id] }, false, none) := by
  unfold lease
  rw [open_, if_neg Bool.false_ne_true, empty]

theorem lease_takes {s : State} (id : Nat) {i : Nat} {rest : List Nat}
    (open_ : s.closing = false) (front : s.available = i :: rest) :
    lease s id =
      ({ s with
          items := mark s.items i s.next, available := rest,
          waiters := without s.waiters id, next := s.next + 1 },
        false, leased s.items i s.next) := by
  unfold lease
  rw [open_, if_neg Bool.false_ne_true, front]

theorem giveBack_returns {s : State} {i l : Nat} (held : s.items.any (·.heldBy i l) = true) :
    giveBack s i l =
      ({ s with items := freed s.items i l, available := i :: s.available }, true,
        !s.waiters.isEmpty) := by
  unfold giveBack
  rw [if_pos held]

variable {Γ : List Ty}

/-- The front pass evaluates on the independent cell carrier. -/
theorem headStamp_eval (tb : Table) (res : Nat → Val) (s : State)
    (cell : Input Γ (cellTy P)) (vs : Inputs Leaves.deferredKeys Γ)
    (hc : cell.get vs = cellC tb res s) :
    (Data.headStamp P cell).eval Leaves.deferredKeys vs = s.available.headD 0 := by
  let cv : CellCarrier := cell.get vs
  have hcv : cv = cellC tb res s := hc
  change (cv.1.take 1).foldl (fun _ stamp => stamp) 0 = _
  rw [hcv]
  exact front_headD s.available

/-- The borrowed-item pass evaluates on the independent cell carrier. -/
theorem outstanding_eval (tb : Table) (res : Nat → Val) (s : State)
    (cell : Input Γ (cellTy P)) (vs : Inputs Leaves.deferredKeys Γ)
    (hc : cell.get vs = cellC tb res s) :
    (Data.outstanding P cell).eval Leaves.deferredKeys vs = s.items.any (·.borrowed) := by
  let cv : CellCarrier := cell.get vs
  have hcv : cv = cellC tb res s := hc
  change cv.2.2.1.foldl (fun found (it : ItemCarrier) => found || it.1) false = _
  rw [hcv]
  change (s.items.map (fun it => (it.borrowed, (it.lease, (res it.resource, (it.stamp, ())))))).foldl (fun found (it : ItemCarrier) => found || it.1) false = _
  rw [List.foldl_map]
  change s.items.foldl (fun found it => found || it.borrowed) false = _
  rw [foldl_or_any]
  rfl


/-- The held-item test evaluates on the independent item's carrier. -/
theorem holds_eval (res : Nat → Val) (it : Item) (i l : Nat)
    (stamp lease : Input Γ .nat) (item : Input Γ (itemTy P))
    (vs : Inputs Leaves.deferredKeys Γ) (hi : stamp.get vs = i)
    (hl : lease.get vs = l) (hx : item.get vs = itemC res it) :
    (Data.holds P stamp lease item).eval Leaves.deferredKeys vs = it.heldBy i l := by
  let sv : Nat := stamp.get vs
  let lv : Nat := lease.get vs
  have hsv : sv = i := hi
  have hlv : lv = l := hl
  let xv : ItemCarrier := item.get vs
  have hxv : xv = itemC res it := hx
  change (decide (xv.2.2.2.1 = sv) &&
    (xv.1 && decide (xv.2.1 = lv))) = _
  rw [hsv, hlv, hxv]
  rfl

/-- The existence test evaluates on the independent model's items. -/
theorem heldBy_eval (tb : Table) (res : Nat → Val) (s : State) (i l : Nat)
    (stamp lease : Input Γ .nat) (cell : Input Γ (cellTy P))
    (vs : Inputs Leaves.deferredKeys Γ) (hi : stamp.get vs = i)
    (hl : lease.get vs = l) (hc : cell.get vs = cellC tb res s) :
    (Data.heldBy P stamp lease cell).eval Leaves.deferredKeys vs =
      s.items.any (fun it => it.heldBy i l) := by
  let sv : Nat := stamp.get vs
  let lv : Nat := lease.get vs
  have hsv : sv = i := hi
  have hlv : lv = l := hl
  let cv : CellCarrier := cell.get vs
  have hcv : cv = cellC tb res s := hc
  change cv.2.2.1.foldl (fun found (it : ItemCarrier) => found ||
    (decide (it.2.2.2.1 = sv) && (it.1 && decide (it.2.1 = lv)))) false = _
  rw [hsv, hlv, hcv]
  change (s.items.map (fun it => (it.borrowed, (it.lease, (res it.resource, (it.stamp, ())))))).foldl (fun found (it : ItemCarrier) => found ||
    (decide (it.2.2.2.1 = i) && (it.1 && decide (it.2.1 = l)))) false = _
  rw [List.foldl_map, foldl_or_any]
  rfl

/-- The returned-item pass evaluates on the independent model's items. -/
theorem freed_eval (tb : Table) (res : Nat → Val) (s : State) (i l : Nat)
    (stamp lease : Input Γ .nat) (cell : Input Γ (cellTy P))
    (vs : Inputs Leaves.deferredKeys Γ) (hi : stamp.get vs = i)
    (hl : lease.get vs = l) (hc : cell.get vs = cellC tb res s) :
    (Data.freed P stamp lease cell).eval Leaves.deferredKeys vs =
      (freed s.items i l).map (itemC res) := by
  let sv : Nat := stamp.get vs
  let lv : Nat := lease.get vs
  have hsv : sv = i := hi
  have hlv : lv = l := hl
  let cv : CellCarrier := cell.get vs
  have hcv : cv = cellC tb res s := hc
  change cv.2.2.1.foldl (fun out (it : ItemCarrier) => out ++
    [if (decide (it.2.2.2.1 = sv) &&
      (it.1 && decide (it.2.1 = lv))) then (false, it.2) else it]) [] = _
  rw [hsv, hlv, hcv]
  change (s.items.map (fun it => (it.borrowed, (it.lease, (res it.resource, (it.stamp, ())))))).foldl (fun out (it : ItemCarrier) => out ++
    [if (decide (it.2.2.2.1 = i) && (it.1 && decide (it.2.1 = l))) then
      (false, it.2) else it]) [] = _
  rw [List.foldl_map, foldl_snoc_map, List.nil_append]
  unfold freed
  rw [List.map_map]
  apply List.map_congr_left
  intro it _
  change (if it.heldBy i l then (false, (itemC res it).2) else itemC res it) = _
  simp only [Function.comp_apply, itemC]
  cases it.heldBy i l <;> simp only [Bool.false_eq_true, ↓reduceIte]


/-- The lease-marking pass evaluates on the independent model's items. -/
theorem marked_eval (tb : Table) (res : Nat → Val) (s : State)
    (cell : Input Γ (cellTy P)) (vs : Inputs Leaves.deferredKeys Γ)
    (hc : cell.get vs = cellC tb res s) :
    (Data.marked P cell).eval Leaves.deferredKeys vs =
      (mark s.items (s.available.headD 0) s.next).map (itemC res) := by
  let cv : CellCarrier := cell.get vs
  have hcv : cv = cellC tb res s := hc
  change cv.2.2.1.foldl (fun out (it : ItemCarrier) => out ++
    [if decide (it.2.2.2.1 = (cv.1.take 1).foldl (fun _ stamp => stamp) 0)
      then (true, (cv.2.2.2.1, it.2.2)) else it]) [] = _
  rw [hcv]
  simp only [cellC, front_headD]
  rw [List.foldl_map, foldl_snoc_map, List.nil_append]
  unfold mark
  rw [List.map_map]
  apply List.map_congr_left
  intro it _
  change (if decide (it.stamp = s.available.headD 0) then
    itemC res (it.leasedAs s.next) else itemC res it) =
    itemC res (if it.stamp = s.available.headD 0 then it.leasedAs s.next else it)
  by_cases h : it.stamp = s.available.headD 0
  · rw [decide_eq_true h, if_pos rfl, if_pos h]
  · rw [decide_eq_false h, if_neg Bool.false_ne_true, if_neg h]

/-- The selected-lease pass evaluates on the independent model's items. -/
theorem leasedOf_list_eval (tb : Table) (res : Nat → Val) (s : State)
    (cell : Input Γ (cellTy P)) (vs : Inputs Leaves.deferredKeys Γ)
    (hc : cell.get vs = cellC tb res s) :
    (Data.leasedOf P cell).eval Leaves.deferredKeys vs =
      (s.items.flatMap fun it => if it.stamp = s.available.headD 0 then [it.leasedAs s.next] else []).map (itemC res) := by
  let cv : CellCarrier := cell.get vs
  have hcv : cv = cellC tb res s := hc
  change (cv.2.2.1.foldl (fun out (it : ItemCarrier) =>
    if decide (it.2.2.2.1 = (cv.1.take 1).foldl (fun _ stamp => stamp) 0)
      then out ++ [(true, (cv.2.2.2.1, it.2.2))] else out) []) = _
  rw [hcv]
  simp only [cellC, front_headD]
  rw [List.foldl_map]
  have point : (fun (out : List ItemCarrier) (it : Item) =>
      if decide (it.stamp = s.available.headD 0) then out ++
        [itemC res (it.leasedAs s.next)] else out) =
      (fun out it => out ++ (if it.stamp = s.available.headD 0 then
        [itemC res (it.leasedAs s.next)] else [])) := by
    funext out it
    by_cases h : it.stamp = s.available.headD 0
    · rw [decide_eq_true h, if_pos rfl, if_pos h]
    · rw [decide_eq_false h, if_neg Bool.false_ne_true, if_neg h, List.append_nil]
  change (s.items.foldl (fun out it => if decide (it.stamp = s.available.headD 0)
    then out ++ [itemC res (it.leasedAs s.next)] else out) []) = _
  rw [point, foldl_append_flatMap, List.nil_append]
  have gifts : (fun (it : Item) => if it.stamp = s.available.headD 0 then
      [itemC res (it.leasedAs s.next)] else []) =
      (fun it => (if it.stamp = s.available.headD 0 then [it.leasedAs s.next] else []).map (itemC res)) := by
    funext it
    by_cases h : it.stamp = s.available.headD 0
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl
  rw [gifts, ← List.map_flatMap]



/-- The selected lease is the head of the pass's list. -/
theorem leasedOf_eval (tb : Table) (res : Nat → Val) (s : State)
    (cell : Input Γ (cellTy P)) (vs : Inputs Leaves.deferredKeys Γ)
    (hc : cell.get vs = cellC tb res s) :
    List.head? (α := ItemCarrier) ((Data.leasedOf P cell).eval Leaves.deferredKeys vs) =
      (leased s.items (s.available.headD 0) s.next).map (itemC res) := by
  rw [leasedOf_list_eval tb res s cell vs hc, List.head?_eq_getElem?, List.getElem?_map, leased_flatMap]

/-- Waiter removal uses the table's injectivity to recover model identity. -/
theorem removed_eval (tb : Table) (injective : tb.Injective) (res : Nat → Val) (s : State)
    (i : Nat) (id : Input Γ idTy) (cell : Input Γ (cellTy P))
    (vs : Inputs Leaves.deferredKeys Γ) (hi : id.get vs = tb.handle i)
    (hc : cell.get vs = cellC tb res s) :
    (Data.removed P id cell).eval Leaves.deferredKeys vs =
      (without s.waiters i).map (waiterC tb) := by
  let cv : CellCarrier := cell.get vs
  let kv : DeferredKey := id.get vs
  have hcv : cv = cellC tb res s := hc
  have hkv : kv = tb.handle i := hi
  change cv.2.2.2.2.1.foldl (fun out (w : DeferredKey × DeferredKey × Unit) =>
    if decide (w.2.1 = kv) then out else out ++ [w]) [] = _
  rw [hcv, hkv]
  change (s.waiters.map (waiterC tb)).foldl
    (fun out w => if decide (w.2.1 = tb.handle i) then out else out ++ [w]) [] = _
  simp only [decide_eq_true_iff]
  rw [foldl_keep, List.nil_append, List.filter_map]
  change (s.waiters.filter (fun n => !decide (tb.handle n = tb.handle i))).map (waiterC tb) = _
  simp only [injective.decides]
  rfl

/-- The waiter update evaluates on the independent withdrawal model. -/
theorem withdrawn_eval (tb : Table) (injective : tb.Injective) (res : Nat → Val) (s : State)
    (i : Nat) (id : Input Γ idTy) (cell : Input Γ (cellTy P))
    (vs : Inputs Leaves.deferredKeys Γ) (hi : id.get vs = tb.handle i)
    (hc : cell.get vs = cellC tb res s) :
    (Data.withdrawn P id cell).eval Leaves.deferredKeys vs = cellC tb res (withdraw s i) := by
  change ((cell.get vs).1, ((cell.get vs).2.1, ((cell.get vs).2.2.1,
    ((cell.get vs).2.2.2.1, ((Data.removed P id cell).eval Leaves.deferredKeys vs, ()))))) = _
  rw [hc, removed_eval tb injective res s i id cell vs hi hc]
  rfl


/-- Renewal frames the carrier of every other waiter's record. -/
theorem waiterC_renew {tb : Table} {i w : Nat} (other : w ≠ i) (hint : DeferredKey) :
    waiterC (tb.renew i hint) w = waiterC tb w := by
  change ((if w = i then hint else tb.hint w), (tb.handle w, ())) = _
  rw [if_neg other]
  rfl

/-- Renewal frames every waiter remaining after removal. -/
theorem waiterCs_without_renew (tb : Table) (ws : List Nat) (i : Nat) (hint : DeferredKey) :
    (without ws i).map (waiterC (tb.renew i hint)) = (without ws i).map (waiterC tb) :=
  List.map_congr_left fun _ member => waiterC_renew (mem_without.mp member).2 hint

/-- An operation's withdrawal reads the same cell after its hint-table renewal. -/
theorem withdrawn_renew_eval (tb : Table) (injective : tb.Injective) (res : Nat → Val)
    (s : State) (i : Nat) (hint : DeferredKey) (id : Input Γ idTy) (cell : Input Γ (cellTy P))
    (vs : Inputs Leaves.deferredKeys Γ) (hi : id.get vs = tb.handle i)
    (hc : cell.get vs = cellC tb res s) :
    (Data.withdrawn P id cell).eval Leaves.deferredKeys vs = cellC (tb.renew i hint) res (withdraw s i) := by
  rw [withdrawn_eval tb injective res s i id cell vs hi hc]
  change (s.available, (s.closing, (s.items.map (itemC res), (s.next,
    ((without s.waiters i).map (waiterC tb), ()))))) =
    (s.available, (s.closing, (s.items.map (itemC res), (s.next,
    ((without s.waiters i).map (waiterC (tb.renew i hint)), ())))))
  rw [waiterCs_without_renew]

/-- Enrolment evaluates to the model's renewed waiter list. -/
theorem enrolled_eval (tb : Table) (injective : tb.Injective) (res : Nat → Val)
    (s : State) (i : Nat) (hint : DeferredKey) :
    (Data.enrolled P).eval (Γ := Data.leaseΓ P) Leaves.deferredKeys ((tb.handle i, (hint, (cellC tb res s, ()))) : Inputs Leaves.deferredKeys (Data.leaseΓ P)) =
      cellC (tb.renew i hint) res {s with waiters := without s.waiters i ++ [i]} := by
  let vs : Inputs Leaves.deferredKeys (Data.leaseΓ P) := (tb.handle i, (hint, (cellC tb res s, ())))
  let gone : List (DeferredKey × DeferredKey × Unit) :=
    (Data.removed P (Data.leaseId P) (Data.leaseCell P)).eval Leaves.deferredKeys vs
  have hg : gone = (without s.waiters i).map (waiterC tb) :=
    removed_eval tb injective res s i _ _ vs rfl rfl
  change (s.available, (s.closing, (s.items.map (itemC res), (s.next,
    (gone ++ [(hint, (tb.handle i, ()))], ()))))) = _
  rw [hg]
  change (_, (_, (_, (_, (_, ()))))) = (s.available, (s.closing, (s.items.map (itemC res),
    (s.next, ((without s.waiters i ++ [i]).map (waiterC (tb.renew i hint)), ())))))
  rw [List.map_append, waiterCs_without_renew, List.map_cons, List.map_nil]
  change _ = (s.available, (s.closing, (s.items.map (itemC res), (s.next,
    ((without s.waiters i).map (waiterC tb) ++ [(if i = i then hint else tb.hint i, (tb.handle i, ()))], ())))))
  rw [if_pos rfl]


/-- The returned-item operation evaluates to the independent return model. -/
theorem giveBack_eval (tb : Table) (res : Nat → Val) (s : State) (i l : Nat) :
    (Data.giveBack P).eval (Γ := Data.returnΓ P) Leaves.deferredKeys
      (i, (l, (cellC tb res s, ()))) =
      ((giveBack s i l).2, cellC tb res (giveBack s i l).1) := by
  let vs : Inputs Leaves.deferredKeys (Data.returnΓ P) := (i, (l, (cellC tb res s, ())))
  let freedItems : List ItemCarrier :=
    (Data.freed P (Data.returnStamp P) (Data.returnLease P) (Data.returnCell P)).eval Leaves.deferredKeys vs
  have hf : freedItems = (freed s.items i l).map (itemC res) :=
    freed_eval tb res s i l _ _ _ vs rfl rfl rfl
  let found : Bool := (Data.heldBy P (Data.returnStamp P) (Data.returnLease P) (Data.returnCell P)).eval Leaves.deferredKeys vs
  have hfound : found = s.items.any (fun it => it.heldBy i l) :=
    heldBy_eval tb res s i l (Data.returnStamp P) (Data.returnLease P) (Data.returnCell P) vs rfl rfl rfl
  change (if found
    then ((true, !decide ((s.waiters.map (waiterC tb)).length = 0)),
      (i :: s.available, (s.closing, (freedItems, (s.next, (s.waiters.map (waiterC tb), ()))))))
    else ((false, false), cellC tb res s)) = _
  rw [hfound, hf, List.length_map]
  cases h : s.items.any (fun it => it.heldBy i l) with
  | false => rw [if_neg Bool.false_ne_true, giveBack_stale h]
  | true =>
    rw [if_pos rfl]
    unfold giveBack
    rw [h, if_pos rfl, decide_length_zero]
    rfl

/-- The withdrawal operation evaluates to the independent withdrawal model. -/
theorem withdraw_eval (tb : Table) (injective : tb.Injective) (res : Nat → Val) (s : State) (i : Nat) :
    (Data.withdraw P).eval (Γ := Data.withdrawΓ P) Leaves.deferredKeys
      (tb.handle i, (cellC tb res s, ())) = ((), cellC tb res (withdraw s i)) := by
  change ((), (Data.withdrawn P (Data.withdrawId P) (Data.withdrawCell P)).eval (Γ := Data.withdrawΓ P) Leaves.deferredKeys
    ((tb.handle i, (cellC tb res s, ())) : Inputs Leaves.deferredKeys (Data.withdrawΓ P))) = _
  rw [withdrawn_eval tb injective res s i (Data.withdrawId P) (Data.withdrawCell P)
    (tb.handle i, (cellC tb res s, ())) rfl rfl]
  rfl

/-- The closer's operation evaluates to the independent drain model. -/
theorem drain_eval (tb : Table) (injective : tb.Injective) (res : Nat → Val)
    (s : State) (i : Nat) (hint : DeferredKey) :
    (Data.drain P).eval (Γ := Data.leaseΓ P) Leaves.deferredKeys
      (tb.handle i, (hint, (cellC tb res s, ()))) =
      ((drain s i).2, cellC (tb.renew i hint) res (drain s i).1) := by
  let vs : Inputs Leaves.deferredKeys (Data.leaseΓ P) := (tb.handle i, (hint, (cellC tb res s, ())))
  let found : Bool := (Data.outstanding P (Data.leaseCell P)).eval Leaves.deferredKeys vs
  have hfound : found = s.items.any (fun it => it.borrowed) :=
    outstanding_eval tb res s (Data.leaseCell P) vs rfl
  change (if found
    then (false, (Data.enrolled P).eval (Γ := Data.leaseΓ P) Leaves.deferredKeys vs)
    else (true, (Data.withdrawn P (Data.leaseId P) (Data.leaseCell P)).eval Leaves.deferredKeys vs)) = _
  rw [hfound, enrolled_eval tb injective res s i hint,
    withdrawn_renew_eval tb injective res s i hint (Data.leaseId P) (Data.leaseCell P) vs rfl rfl]
  change (if s.items.any (fun it => it.borrowed) then
    (false, cellC (tb.renew i hint) res {s with waiters := without s.waiters i ++ [i]})
    else (true, cellC (tb.renew i hint) res (withdraw s i))) =
    ((drain s i).2, cellC (tb.renew i hint) res (drain s i).1)
  cases h : s.items.any (fun it => it.borrowed) with
  | false => rw [if_neg Bool.false_ne_true, drain_drained i h]
  | true => rw [if_pos rfl, drain_enrols i h]


/-- The lease operation evaluates to the independent lease model and renewed table. -/
theorem lease_eval (tb : Table) (injective : tb.Injective) (res : Nat → Val)
    (s : State) (i : Nat) (hint : DeferredKey) :
    (Data.lease P).eval (Γ := Data.leaseΓ P) Leaves.deferredKeys
      (tb.handle i, (hint, (cellC tb res s, ()))) =
      (((lease s i).2.1, (lease s i).2.2.map (itemC res)),
        cellC (tb.renew i hint) res (lease s i).1) := by
  let vs : Inputs Leaves.deferredKeys (Data.leaseΓ P) := (tb.handle i, (hint, (cellC tb res s, ())))
  let gone : CellCarrier :=
    (Data.withdrawn P (Data.leaseId P) (Data.leaseCell P)).eval Leaves.deferredKeys vs
  have hg : gone = cellC (tb.renew i hint) res (withdraw s i) :=
    withdrawn_renew_eval tb injective res s i hint (Data.leaseId P) (Data.leaseCell P) vs rfl rfl
  let markedItems : List ItemCarrier := (Data.marked P (Data.leaseCell P)).eval Leaves.deferredKeys vs
  have hm : markedItems = (mark s.items (s.available.headD 0) s.next).map (itemC res) :=
    marked_eval tb res s (Data.leaseCell P) vs rfl
  let selected : List ItemCarrier := (Data.leasedOf P (Data.leaseCell P)).eval Leaves.deferredKeys vs
  have hl : selected.head? = (leased s.items (s.available.headD 0) s.next).map (itemC res) :=
    leasedOf_eval tb res s (Data.leaseCell P) vs rfl
  change (if s.closing then ((true, none), gone) else
    if decide (s.available.length = 0) then ((false, none),
      (Data.enrolled P).eval (Γ := Data.leaseΓ P) Leaves.deferredKeys vs)
    else ((false, selected.head?), (s.available.drop 1,
      (gone.2.1, (markedItems, (s.next + 1, (gone.2.2.2.2.1, ()))))))) = _
  rw [hg, hm, hl, enrolled_eval tb injective res s i hint]
  cases closed : s.closing with
  | true => rw [if_pos rfl, lease_closed closed i]
            rfl
  | false =>
    rw [if_neg Bool.false_ne_true]
    cases front : s.available with
    | nil =>
      have empty : decide (([] : List Nat).length = 0) = true := rfl
      rw [empty, if_pos rfl, lease_enrols i closed front]
      simp only [cellC, closed, front]
      rfl
    | cons stamp tail =>
      have nonempty : decide ((stamp :: tail).length = 0) = false := rfl
      rw [nonempty, if_neg Bool.false_ne_true, lease_takes i closed front]
      simp only [cellC, withdraw, closed, front]
      rfl

end Effect4.Pool.Model
