(* E4_fibers_view — the machine's fiber table WITH an incrementally maintained completed view
   (lane G3, docs/research/2026-09-08-engine-lane-g3-delivery.md; the seam's `FIBERS`
   parameter, `RunMachine.fibers`, field F2 of docs/research/2026-09-08-engine-a1-state.md
   §1.2).

   What it is and why it exists.  `RunMachine.completedExits` (src/Effect4/Machine/Fibers.lean:
   1541-1543) is `m.fibers.filterMap (fun f => f.exit.map ((f.id, ·)))` and it is called on
   essentially every step (`Program.evaluateNative`, `Program.exitScoped`, through
   `interpAt`).  Over a `TABLE` that is a Θ(N) `Map.fold` per step — 62.7 % inclusive on
   fan-out 512 after lane G2 (that receipt §6).  A cache does not fix it: lane G2 built the
   one-entry memo keyed on the physical identity of the fiber table and MEASURED 0.0 % hits,
   because every call sees a table a `set`/`add` has already rebuilt.  The answer has to be
   MAINTAINED, not cached — so the carrier keeps the exited subset as the table is written and
   `completed` is a field read.

   `('a, 'x) t` is a table of fibers `'a` whose exit is `'x`.  The fiber record is declared
   INSIDE the generated functor, so this module cannot project `f.exit`: every write takes the
   projection as a labelled argument `~exit_of` (the same device as lane C's `E4_fibers`
   `~id_of`/`~exit_of`, deviation D2 there).  The view holds the EXIT, not the fiber, so
   `completed` IS the answer `completedExits` returns — one shared list, allocated only when a
   fiber's exit changes, never per step.

   Depends on: the OCaml standard library only (`Map.Make(Int)`).  It is NOT a face over
   `E4_table`: the value is ONE flat record (`{ cardinal; map; view }`) because a wrapped
   table costs a second block on every write and this carrier is written on nearly every
   step.  `E4_table`'s two-arm `Small`/`Big` representation is not reproduced — lane C
   measured its threshold at 0, so the small arm is dead — and its O(1) cardinal is.

   Behaviours (each is a named PASS/FAIL line in test/prop_fibers_view.ml):
   FV1 THE LAW.  For every value reachable by any sequence of {empty, add, set, map, of_list},
       `completed t` = `List.filter_map (fun (id, f) -> Option.map (fun x -> (id, x))
       (exit_of f)) (bindings t)` — the maintained view is the scan it replaces, ascending by
       id, for the SAME `exit_of` the writes were given.    tested (>= 12 000 ops, LCG)
   FV2 `set` on an ABSENT key is a no-op on the table AND on the view: Lean's replace-by-key
       map matches nothing (Fibers.lean:577-579) and `E4_table.set` does not insert (lane C
       law T1).                                                            tested
   FV3 `add` inserts at the key; the view gains `(k, x)` in id order when `exit_of v` is
       `Some x` and nothing otherwise.  `spawn`'s child (Fibers.lean:867-877) has
       `exit = none`, so the common case adds nothing.                     tested
   FV4 `map` is id-preserving (Fibers.lean:1256, :1344 are `fibers.map`) and RE-DERIVES the
       view from the mapped table, so a mapping function that changes an exit is still
       answered exactly.  It is Θ(N), which is what the map itself costs.  tested
   FV5 the view is INVISIBLE to every other operation: `find_opt`, `bindings`, `to_list`,
       `cardinal` and `for_all` are `E4_table`'s, value for value.         tested
   FV6 agreement with the LIST twin (`e4_fibers_view_list.ml`: Lean's list, and `completed`
       is Lean's `filterMap` WALK at read time) on random sequences of
       {find, set, add, map, completed, finished, bindings}.  tested (>= 12 000 ops, LCG)
   FV7 persistent: every operation answers a new value and no earlier value changes; no
       mutable structure is reachable from a table (brief §2.3, A2-OQ6).   tested
   FV8 THE SHARING LAW, and the reason this is not a cache.  A `set` that does not change any
       fiber's exit leaves the view PHYSICALLY equal (`==`), so the `(fiber_id * exit) list`
       the machine hands `interpAt` every step is ONE list, allocated when a fiber exits and
       shared by every step and every `Point.completed` after it.          tested
   FV9 cost: `completed` O(1); `find_opt`/`add` O(log n); `set` O(log n) when no exit changes
       and O(log n + C) when one does (C = the completed count, the view's insertion point);
       `map` O(N).  `cardinal` is O(1) (E4_table's law D5).                argued; benched

   Bound: fiber ids are host ints.  Nothing here removes a fiber — `remove` is not offered,
   because the ordering argument that licenses the whole substitution is "no fiber is ever
   removed" (gen-check.sh C1). *)

type ('a, 'x) t
(** The fiber table and its completed view.  Abstract: the invariant FV1 is the module's, and
    a caller that could build the record could break it. *)

val empty : ('a, 'x) t
val find_opt : int -> ('a, 'x) t -> 'a option
val set : exit_of:('a -> 'x option) -> int -> 'a -> ('a, 'x) t -> ('a, 'x) t
val add : exit_of:('a -> 'x option) -> int -> 'a -> ('a, 'x) t -> ('a, 'x) t
val map : exit_of:('a -> 'x option) -> ('a -> 'a) -> ('a, 'x) t -> ('a, 'x) t
val for_all : (int -> 'a -> bool) -> ('a, 'x) t -> bool
val completed : ('a, 'x) t -> (int * 'x) list
val cardinal : ('a, 'x) t -> int
val bindings : ('a, 'x) t -> (int * 'a) list
val to_list : ('a, 'x) t -> 'a list
val of_list : exit_of:('a -> 'x option) -> (int * 'a) list -> ('a, 'x) t

(* --- windows, for the property tests and the drive loop; not on the seam. --- *)

val mem : int -> ('a, 'x) t -> bool
val is_empty : ('a, 'x) t -> bool
