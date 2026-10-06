import Effect4.Laws.Modules.Semaphore.Relation
import Effect4.Laws.Modules.Reading

/-!
# Reading Semaphore's step terms: the values of its records, words and passes (row 265)

A step goal says that a step's source term reads a value (`Reads`,
`src/Effect4/Laws/Modules/Reading.lean`). The shared reading rules give what each authoring
builder and each word of a step reads, and they serve here as they are. This file adds what
Semaphore's steps need beside them.

- **The two records**: what a read answers and what an overwrite stores, one `rfl` for each
  field of the cell and of a waiter.
- **The removal by identity** (`reads_removeWaiter`): one application of the shared rule of
  the pass `removeById` (`reads_removeById`, `src/Effect4/Laws/Modules/Reading.lean`).
- **The table's one change frames every other request** (`waiters_renew`).
- **The passes** of `src/Effect4/Modules/Semaphore/Steps.lean` on the encoding of a model
  state: the free count, the fit, the fold that starts at the first fitting waiter, and a
  visit's reply and stored value.
- **Three facts of lists** serve that fold: it is `dropWhile`, the first entry that it keeps is
  what `find?` answers, and the list around that entry is the list without it. They are in
  `Effect4.Constructive.List` (`src/Effect4/Data/Constructive.lean`), with the fact of a test
  on two numbers (`not_decide_lt`, in `Effect4.Constructive.Decidable`).

Placement. Concept `translation-simulation`, requirement R10. Every lemma here is a helper of
the five step goals (`src/Effect4/Laws/Modules/Semaphore/Steps.lean`), parts of the proposed
claim `semaphore-expansion-agrees`. Its consumer is the proof of a step goal. The lemmas
establish nothing of a model's transition by themselves.
-/

set_option autoImplicit false

namespace Effect4.Semaphore.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Constructive.List (foldl_fromFirst)
open Effect4.Constructive.Decidable (not_decide_lt)

/-! ## The two records: what a read answers and what an overwrite stores -/

theorem cell_next (n p t w : Val) :
    Machine.Record.read false (cellOf n p t w) "next" = some n := rfl
theorem cell_permits (n p t w : Val) :
    Machine.Record.read false (cellOf n p t w) "permits" = some p := rfl
theorem cell_taken (n p t w : Val) :
    Machine.Record.read false (cellOf n p t w) "taken" = some t := rfl
theorem cell_waiters (n p t w : Val) :
    Machine.Record.read false (cellOf n p t w) "waiters" = some w := rfl
theorem cell_setNext (n p t w v : Val) :
    Machine.Record.set (cellOf n p t w) "next" v = some (cellOf v p t w) := rfl
theorem cell_setTaken (n p t w v : Val) :
    Machine.Record.set (cellOf n p t w) "taken" v = some (cellOf n p v w) := rfl
theorem cell_setWaiters (n p t w v : Val) :
    Machine.Record.set (cellOf n p t w) "waiters" v = some (cellOf n p t v) := rfl
theorem waiter_id (h i n s : Val) :
    Machine.Record.read false (waiterOf h i n s) "id" = some i := rfl
theorem waiter_need (h i n s : Val) :
    Machine.Record.read false (waiterOf h i n s) "need" = some n := rfl
theorem waiter_stamp (h i n s : Val) :
    Machine.Record.read false (waiterOf h i n s) "stamp" = some s := rfl
theorem waiter_build (i n h s : Val) :
    Machine.Record.build ["id", "need", "hint", "stamp"] [i, n, h, s] = some (waiterOf h i n s) :=
  rfl

/-! ## The removal by identity, on the encoding of the model's waiters -/

section Removal

variable {env : Env} {path : List Nat} {vals : List Val}

/-- `removeWaiter`: the waiters without the request, on the encoding of the model's waiters. -/
theorem reads_removeWaiter {waiters id : TermSrc} (tb : Table) (injective : tb.Injective)
    (ws : List Waiter) (i : Nat) (depth : vals.length = env.names.length)
    (hwaiters : Reads waiters env path vals (Val.list (ws.map (waiterVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Semaphore.removeWaiter waiters id) env path vals
      (Val.list ((without ws i).map (waiterVal tb))) :=
  reads_removeById tb injective (waiterVal tb) (·.id) (fun _ => waiter_id _ _ _ _) ⟨0, 0, 0⟩ ws i
    depth hwaiters hid

end Removal

/-! ## The table's one change frames every other request -/

/-- The record of a waiter of another identity stays. -/
theorem waiterVal_renew {tb : Table} {w : Waiter} {id : Nat} (other : w.id ≠ id)
    (hint : DeferredKey) : waiterVal (tb.renew id hint) w = waiterVal tb w := by
  show waiterOf (Val.promise (if w.id = id then hint else tb.hint w.id))
    (Val.promise (tb.handle w.id)) (.nat w.need) (.nat w.stamp) = _
  rw [if_neg other]
  rfl

/-- Waiters that are not the request keep their records. -/
theorem waiters_renew (tb : Table) (ws : List Waiter) (id : Nat) (hint : DeferredKey)
    (others : ∀ w ∈ ws, w.id ≠ id) :
    ws.map (waiterVal (tb.renew id hint)) = ws.map (waiterVal tb) :=
  List.map_congr_left fun w member => waiterVal_renew (others w member) hint

/-- The request's own record, through the table that holds the step's hint. -/
theorem waiterVal_renewed (tb : Table) (id n stamp : Nat) (hint : DeferredKey) :
    waiterVal (tb.renew id hint) ⟨id, n, stamp⟩ =
      waiterOf (Val.promise hint) (Val.promise (tb.handle id)) (.nat n) (.nat stamp) := by
  show waiterOf (Val.promise (if id = id then hint else tb.hint id))
    (Val.promise (tb.handle id)) (.nat n) (.nat stamp) = _
  rw [if_pos rfl]

/-! ## The passes, on the encoding of a model state -/

section Passes

variable {env : Env} {path : List Nat} {vals : List Val}

/-- `freeT`: the free count. -/
theorem reads_freeT {s : TermSrc} (tb : Table) (state : State)
    (hs : Reads s env path vals (cellVal tb state)) :
    Reads (Semaphore.freeT s) env path vals (Val.nat (free state)) :=
  reads_sub (reads_field hs (cell_permits _ _ _ _)) (reads_field hs (cell_taken _ _ _ _))

/-- `fitsT`: whether a count fits the free count. -/
theorem reads_fitsT {need s : TermSrc} (tb : Table) (state : State) (n : Nat)
    (hneed : Reads need env path vals (Val.nat n))
    (hs : Reads s env path vals (cellVal tb state)) :
    Reads (Semaphore.fitsT need s) env path vals (Val.bool (decide (n ≤ free state))) :=
  (reads_notT (reads_lt (reads_freeT tb state hs) hneed)).to
    (congrArg Val.bool (not_decide_lt (free state) n))

/-- A waiter's record, built from an identity, a count, a hint and a stamp. -/
theorem reads_mkWaiter {id need hint stamp : TermSrc} {i n h s : Val}
    (hid : Reads id env path vals i) (hneed : Reads need env path vals n)
    (hhint : Reads hint env path vals h) (hstamp : Reads stamp env path vals s) :
    Reads (Semaphore.mkWaiter id need hint stamp) env path vals (waiterOf h i n s) :=
  reads_record (.cons hid (.cons hneed (.cons hhint (.cons hstamp .nil)))) (waiter_build i n h s)

/-- `eligibleT`: whether a visit at a cursor may select a waiter. -/
theorem reads_eligibleT {cursor s w : TermSrc} (tb : Table) (state : State) (c : Nat)
    (x : Waiter) (hcursor : Reads cursor env path vals (Val.nat c))
    (hs : Reads s env path vals (cellVal tb state))
    (hw : Reads w env path vals (waiterVal tb x)) :
    Reads (Semaphore.eligibleT cursor s w) env path vals (Val.bool (fits c (free state) x)) :=
  (reads_andT
    (reads_notT (reads_lt (reads_field hw (waiter_stamp _ _ _ _)) hcursor))
    (reads_notT (reads_lt (reads_freeT tb state hs) (reads_field hw (waiter_need _ _ _ _))))).to
    (by
      show Val.bool ((!decide (x.stamp < c)) && (!decide (free state < x.need))) =
        Val.bool (decide (c ≤ x.stamp) && decide (x.need ≤ free state))
      rw [not_decide_lt, not_decide_lt])

/-- `fromFirst`: the waiters from the first one that a visit at the cursor may select. The
cursor and the cell both stand in the fold's body, so each is a caller's term under a fold. -/
theorem reads_fromFirst {cursor s : TermSrc} (tb : Table) (state : State) (c : Nat)
    (depth : vals.length = env.names.length)
    (hcursor : Captured cursor env path vals (Val.nat c))
    (hs : Captured s env path vals (cellVal tb state)) :
    Reads (Semaphore.fromFirst cursor s) env path vals
      (Val.list ((state.waiters.dropWhile (fun w => !fits c (free state) w)).map
        (waiterVal tb))) := by
  have waiters := reads_field hs.atScope (cell_waiters _ _ _ _)
  have folded : Reads (Semaphore.fromFirst cursor s) env path vals
      (Val.list ((state.waiters.foldl
        (fun kept w =>
          if (!decide (kept.length = 0) || fits c (free state) w) = true then kept ++ [w]
          else kept) []).map (waiterVal tb))) :=
    reads_foldWith_model (waiterVal tb) (fun kept : List Waiter => Val.list (kept.map (waiterVal tb)))
      (fun kept w =>
        if (!decide (kept.length = 0) || fits c (free state) w) = true then kept ++ [w] else kept)
      state.waiters [] ⟨0, 0, 0⟩ waiters (reads_noneOf waiters) fun kept w => by
        have acc := reads_minted_acc depth path (Val.list (kept.map (waiterVal tb)))
          (waiterVal tb w)
        have item := reads_minted_item depth path (Val.list (kept.map (waiterVal tb)))
          (waiterVal tb w)
        refine (reads_ifT
          (reads_orT (reads_notT (reads_isEmpty acc))
            (reads_eligibleT tb state c w (hcursor.underFold _ _) (hs.underFold _ _) item))
          (reads_snoc acc item) acc).to ?_
        rw [List.length_map]
        by_cases keeps : (!decide (kept.length = 0) || fits c (free state) w) = true
        · rw [keeps, if_pos rfl, if_pos rfl, List.map_append]
          rfl
        · rw [Bool.not_eq_true] at keeps
          rw [keeps, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  exact folded.to (by rw [foldl_fromFirst]; rfl)

/-- `visitFrom`: a visit's reply and stored value, from the waiters `rest` that start at the
selected one. -/
theorem reads_visitFrom {rest s : TermSrc} (tb : Table) (state : State) (items : List Waiter)
    (hrest : Reads rest env path vals (Val.list (items.map (waiterVal tb))))
    (hs : Reads s env path vals (cellVal tb state)) :
    Reads (Semaphore.visitFrom rest s) env path vals
      (if free state = 0 then Val.tuple [Store.Val.none, cellVal tb state]
        else Val.tuple [visitReplyVal tb items[0]?,
          cellVal tb { state with
            waiters := state.waiters.take (state.waiters.length - items.length) ++
              items.drop 1 }]) := by
  have waiters := reads_field hs (cell_waiters _ _ _ _)
  have stop := reads_pair (reads_head (reads_noneOf waiters)) hs
  have go := reads_pair (reads_head hrest)
    (reads_recordSet hs
      (reads_append
        (reads_take waiters (reads_sub (reads_len waiters) (reads_len hrest)))
        (reads_drop hrest (reads_nat 1 env path vals)))
      (cell_setWaiters _ _ _ _ _))
  refine (reads_ifT (reads_isZero (reads_freeT tb state hs)) stop go).to ?_
  by_cases noneFree : free state = 0
  · rw [decide_eq_true noneFree, if_pos rfl, if_pos noneFree]
    rfl
  · rw [decide_eq_false noneFree, if_neg Bool.false_ne_true, if_neg noneFree, List.length_map,
      List.length_map, ← List.map_take, ← List.map_drop, ← List.map_append, List.getElem?_map]
    cases items[0]? with
    | none => rfl
    | some w => rfl

end Passes

end Effect4.Semaphore.Model
