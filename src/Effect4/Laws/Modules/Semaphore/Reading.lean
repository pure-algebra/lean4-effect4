import Effect4.Laws.Modules.Semaphore.Relation
import Effect4.Laws.Modules.Queue.Reading

/-!
# Reading Semaphore's step terms: the values of its records, words and passes (row 265)

A step goal says that a step's source term reads a value (`Reads`,
`src/Effect4/Laws/Modules/Reading.lean`). The shared reading rules give what each authoring
builder and each word of a step reads, and they serve here as they are. This file adds what
Semaphore's steps need beside them.

- **The two records**: what a read answers and what an overwrite stores, one `rfl` for each
  field of the cell and of a waiter.
- **Three words** that the Queue's steps do not use: `add`, `isZero` at a number, and the
  literal of nothing.
- **The removal by identity, stated once** (`reads_removeById`). The shared pass `removeById`
  (`src/Effect4/Modules/Words.lean`) reads the filter by identity on the encoding of every list
  of entries whose `id` field reads the table's handle of the entry's identity. The Queue's own
  two lemmas, `reads_removeTaker` and `reads_removeOffer`, are its instances at a taker and at
  an offer. They stay where they are until the helpers move.
- **The table's one change frames every other request** (`waiters_renew`).
- **The passes** of `src/Effect4/Modules/Semaphore/Steps.lean` on the encoding of a model
  state: the free count, the fit, the fold that starts at the first fitting waiter, and a
  visit's reply and stored value.
- **Three facts of lists** for that fold: it is `dropWhile`, the first entry that it keeps is
  what `find?` answers, and the list around that entry is the list without it.

Placement. Concept `translation-simulation`, requirement R10. Every lemma here is a helper of
the five step goals (`src/Effect4/Laws/Modules/Semaphore/Steps.lean`), parts of the proposed
claim `semaphore-expansion-agrees`. Its consumer is the proof of a step goal. The lemmas
establish nothing of a model's transition by themselves.
-/

set_option autoImplicit false

namespace Effect4.Semaphore.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
-- a fact of lists that waits in the Queue's folder for its move to `Effect4.Constructive.List`
open Effect4.Queue.Model (foldl_keep)

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

/-! ## Three words that the Queue's steps do not use -/

theorem atom_add (a b : Nat) :
    nativeAtom "add" [Val.nat a, Val.nat b] = some (Val.nat (a + b)) := rfl

section Words

variable {env : Env} {path : List Nat} {vals : List Val}

theorem reads_add {a b : TermSrc} {x y : Nat} (ha : Reads a env path vals (Val.nat x))
    (hb : Reads b env path vals (Val.nat y)) :
    Reads (app "add" [a, b]) env path vals (Val.nat (x + y)) :=
  reads_app (.cons ha (.cons hb .nil)) (atom_add x y)

theorem reads_isZero {n : TermSrc} {x : Nat} (hn : Reads n env path vals (Val.nat x)) :
    Reads (app "isZero" [n]) env path vals (Val.bool (decide (x = 0))) :=
  reads_app (.cons hn .nil) (atom_isZero x)

theorem reads_unit : Reads unit env path vals Val.unit := reads_lit .unit env path vals rfl

end Words

/-- A number is not below another exactly when the other is at most it: the test that a step
writes with `not` and `lt`. -/
theorem not_decide_lt (a b : Nat) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases below : a < b
  · rw [decide_eq_true below, decide_eq_false (Nat.not_le_of_lt below)]
    rfl
  · rw [decide_eq_false below, decide_eq_true (Nat.le_of_not_lt below)]
    rfl

/-! ## The removal by identity, on the encoding of any list of entries -/

section Removal

variable {env : Env} {path : List Nat} {vals : List Val}

/-- **The removal pass reads the filter by identity.** The entries are the encoding of a list,
and each entry's `id` field reads the table's handle of the entry's identity. On an injective
table the pass `removeById` reads the encoding of the entries of another identity. The
statement names no type of the Queue and none of Semaphore. -/
theorem reads_removeById {α : Type} {entries id : TermSrc} (tb : Table)
    (injective : tb.Injective) (encode : α → Val) (identity : α → Nat)
    (hasId : ∀ x, Machine.Record.read false (encode x) "id" =
      some (Val.promise (tb.handle (identity x))))
    (witness : α) (xs : List α) (i : Nat) (depth : vals.length = env.names.length)
    (hentries : Reads entries env path vals (Val.list (xs.map encode)))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (removeById entries id) env path vals
      (Val.list ((xs.filter (fun x => identity x != i)).map encode)) := by
  have folded : Reads (removeById entries id) env path vals
      (Val.list ((xs.foldl (fun kept x => if identity x = i then kept else kept ++ [x]) []).map
        encode)) :=
    reads_foldWith_model encode (fun kept : List α => Val.list (kept.map encode))
      (fun kept x => if identity x = i then kept else kept ++ [x]) xs [] witness hentries
      (reads_noneOf hentries) fun kept x => by
        refine (reads_ifT
          ((reads_same (reads_field (reads_minted_item depth path _ (encode x)) (hasId x))
            (hid.underFold _ (encode x))).to (by rw [injective.decides]))
          (reads_minted_acc depth path _ (encode x))
          (reads_snoc (reads_minted_acc depth path _ (encode x))
            (reads_minted_item depth path _ (encode x)))).to ?_
        by_cases same : identity x = i
        · rw [decide_eq_true same, if_pos rfl, if_pos same]
        · rw [decide_eq_false same, if_neg Bool.false_ne_true, if_neg same, List.map_append]
          rfl
  exact folded.to (by rw [foldl_keep, List.nil_append]; rfl)

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

/-! ## Three facts of lists, for the fold that starts at the first fitting waiter -/

/-- A fold that keeps every entry from the first one that satisfies a test is `dropWhile`. With
entries already kept, it keeps every later entry. -/
theorem foldl_fromFirst {α : Type} (p : α → Bool) :
    ∀ (xs kept : List α),
      xs.foldl
          (fun kept x => if (!decide (kept.length = 0) || p x) = true then kept ++ [x] else kept)
          kept =
        if kept.length = 0 then xs.dropWhile (fun x => !p x) else kept ++ xs
  | [], kept => by
    rw [List.foldl_nil, List.dropWhile_nil, List.append_nil]
    by_cases empty : kept.length = 0
    · rw [if_pos empty]
      exact List.eq_nil_of_length_eq_zero empty
    · rw [if_neg empty]
  | x :: xs, kept => by
    rw [List.foldl_cons, foldl_fromFirst p xs]
    by_cases empty : kept.length = 0
    · have none : kept = [] := List.eq_nil_of_length_eq_zero empty
      subst none
      rw [List.dropWhile_cons]
      cases holds : p x with
      | true => rfl
      | false => rfl
    · have keeps : (!decide (kept.length = 0) || p x) = true := by
        rw [decide_eq_false empty]
        rfl
      have more : ¬ (kept ++ [x]).length = 0 := by
        rw [List.length_append]
        exact Nat.succ_ne_zero _
      rw [keeps, if_pos rfl, if_neg more, if_neg empty, List.append_assoc]
      rfl

/-- What `dropWhile` keeps is no longer than the list. -/
theorem length_dropWhile_le {α : Type} (q : α → Bool) :
    ∀ (xs : List α), (xs.dropWhile q).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    rw [List.dropWhile_cons]
    by_cases drops : q x = true
    · rw [if_pos drops]
      exact Nat.le_succ_of_le (length_dropWhile_le q xs)
    · rw [if_neg drops]
      exact Nat.le_refl _

/-- **The entries from the first one that satisfies a test, against `find?` and `erase`.** The
first kept entry is what `find?` answers. The entries before the kept ones, then the kept ones
without their first, are the list without that entry, or the whole list where no entry
satisfies the test. The removal compares no entry with another in the term: an earlier entry
that is equal to the found one would satisfy the test too, so `find?` would have answered
it. -/
theorem fromFirst_find? {α : Type} [DecidableEq α] (p : α → Bool) :
    ∀ (xs : List α),
      (xs.dropWhile (fun x => !p x))[0]? = xs.find? p ∧
        xs.take (xs.length - (xs.dropWhile (fun x => !p x)).length) ++
            (xs.dropWhile (fun x => !p x)).drop 1 =
          (match xs.find? p with
            | some w => xs.erase w
            | none => xs)
  | [] => ⟨rfl, rfl⟩
  | x :: xs => by
    obtain ⟨head, around⟩ := fromFirst_find? p xs
    rw [List.dropWhile_cons, List.find?_cons]
    cases holds : p x with
    | true =>
      rw [if_neg (by decide : ¬ ((!true) = true))]
      refine ⟨rfl, ?_⟩
      show (x :: xs).take ((x :: xs).length - (x :: xs).length) ++ xs = (x :: xs).erase x
      rw [Nat.sub_self, List.take_zero, List.nil_append, List.erase_cons,
        show (x == x) = true from decide_eq_true rfl, if_pos rfl]
    | false =>
      rw [if_pos (by decide : (!false) = true)]
      refine ⟨head, ?_⟩
      have shorter := length_dropWhile_le (fun x => !p x) xs
      have longer : (x :: xs).length - (xs.dropWhile (fun x => !p x)).length =
          (xs.length - (xs.dropWhile (fun x => !p x)).length) + 1 := by
        rw [List.length_cons]
        omega
      rw [longer, List.take_succ_cons, List.cons_append, around]
      cases found : xs.find? p with
      | none => rfl
      | some w =>
        have other : ¬ x = w := fun same => by
          have fitsW := List.find?_some found
          rw [← same, holds] at fitsW
          cases fitsW
        show x :: xs.erase w = (x :: xs).erase w
        rw [List.erase_cons, show (x == w) = false from decide_eq_false other,
          if_neg Bool.false_ne_true]

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
