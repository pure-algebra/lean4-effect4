(* E4_store — the three per-family cell stores over E4_table: the Ref heap, the Deferred
   cells, the Scope entries (docs/research/2026-09-08-engine-a1-state.md §4.4; fields F3, F4,
   F5 of §1.2).  One module because the three obey the same two laws — a keyed read, and a
   replace that is a NO-OP on an absent key — and the extern rows differ only in the field
   they name.

   Depends on: E4_table.

   The Lean operation each function reproduces, verbatim:
     peek k h        `refPeek heap cell = heap[cell.index]?`        (Stores.lean:1116)
     poke k v h      `refPoke heap cell v = heap.set cell.index v`  (Stores.lean:1119-1120)
     grow v h        `refMake`: `(Val.cell ⟨heap.length⟩, heap ++ [initial])`
                                                                     (Stores.lean:1150)
     cell_at k d     `DeferredStore.cellAt = self.cells[cell.index]?` (Stores.lean:1369-1370)
     set_cell k v d  `DeferredStore.setCell = cells.set cell.index v` (Stores.lean:1372-1374)
     make_cell v d   `DeferredStore.make`: `(⟨cells.length⟩, cells ++ [⟨none, []⟩])`
                                                                     (Stores.lean:1365-1366)
     entry_at k s    `ScopeStore.entryAt = entries.find? (·.key = key)` (Stores.lean:1567-1568)
     set_entry k v s `ScopeStore.setEntry = entries.map (replace by key)`
                                                                     (Stores.lean:1571-1572)
     add_entry k v s `ScopeStore.make/forkChild`: `entries ++ [⟨key, scope⟩]`
                                                       (Stores.lean:1576, :1605-1607)

   Behaviours (each is a named PASS/FAIL line in test/prop_store.ml; the right-hand side of
   every law is the Lean list operation, written out in the test):
   ST1 peek is refPeek: peek k h = List.nth_opt (to_list h) k for a dense heap
                                                                           tested
   ST2 poke is refPoke AND IS A NO-OP OUT OF RANGE: Lean's `heap.set i v` leaves the list
       alone when i >= length, and refStep guards with refPeek first (Stores.lean:1151-1185)
       so the two coincide — but the carrier must not INSERT.               tested
   ST3 grow is refMake: grow v h = (cardinal h, add (cardinal h) v h), and
       to_list (snd (grow v h)) = to_list h @ [v], and fst (grow v h) = List.length
       (to_list h)                                                          tested
   ST4 cell_at / set_cell / make_cell are DeferredStore.cellAt / setCell / make, with the
       same no-op-out-of-range rule                                         tested
   ST5 entry_at is ScopeStore.entryAt — a find? BY KEY, so E4_table.find_opt is exact;
       set_entry is the replace-by-key map, a no-op on an absent key        tested
   ST6 scope keys are SUPPLY-drawn, not dense: `scopeMake` takes st.nextName
       (Stores.lean:2203-2205) and `scopeFork` takes two (:2229-2236), so the scope table is
       SPARSE and `cardinal` is NOT the next key.  The supply is Stores.nextName and stays an
       int.  A carrier that allocated by cardinal would break E4-CHECK-CE-016: `add_entry`
       therefore takes the key and `grow`/`make_cell` are NOT offered for scopes.
                                                             by construction; tested (ST6b)
   ST7 agreement with the list carrier (e4_table_list.ml) on random operation sequences,
       compared against the Lean list operations spelled out    tested (>= 10 000 ops, LCG)
   ST8 KeysBelow is preserved: every registration key any scope holds is < nextName
       (Stores.lean:1645-1646); the carrier neither mints nor drops keys.   by construction
   Bound: `grow` and `make_cell` allocate at `cardinal`, which is O(1) in E4_table — an O(n)
   cardinal here would restore the quadratic the carrier exists to remove. *)

type 'a t = 'a E4_table.t

(* --- the Ref heap: DENSE, index-keyed (RefHeap = List Val, Stores.lean:1112) --- *)

val peek : int -> 'a t -> 'a option
val poke : int -> 'a -> 'a t -> 'a t
(** No-op — and physically the same heap — when the key is absent (ST2). *)

val grow : 'a -> 'a t -> int * 'a t
(** (fresh key = cardinal, heap'): `refMake`. *)

(* --- the Deferred cells: DENSE, index-keyed (DeferredStore.cells, Stores.lean:1357) --- *)

val cell_at : int -> 'a t -> 'a option
val set_cell : int -> 'a -> 'a t -> 'a t
(** No-op when absent. *)

val make_cell : 'a -> 'a t -> int * 'a t

(* --- the Scope entries: SPARSE, supply-keyed (ScopeStore.entries, Stores.lean:1561) --- *)

val entry_at : int -> 'a t -> 'a option
val set_entry : int -> 'a -> 'a t -> 'a t
(** No-op when absent. *)

val add_entry : int -> 'a -> 'a t -> 'a t
(** Insert at a SUPPLIED key (ST6): the scope store never allocates by cardinal. *)

(* --- shared --- *)

val empty : 'a t
val to_list : 'a t -> 'a list
val cardinal : 'a t -> int
val bindings : 'a t -> (int * 'a) list
