(* E4_table — the persistent int-keyed table behind the fiber table, the ref heap, the
   deferred cells and the scope entries (docs/research/2026-09-08-engine-a1-state.md §4.1,
   fields F2-F5 of §1.2).

   What it is: `Map.Make(Int)` with a Lean-shaped API and a small-size representation.
   The `set` / `add` split is the whole point: Lean's `List.set` is a NO-OP out of range
   (src/Effect4/Machine/Stores.lean:1120 refPoke, :1374 DeferredStore.setCell) and Lean's
   replace-by-key `List.map` is a NO-OP on an absent key (:1572 ScopeStore.setEntry,
   Fibers.lean:579 RunMachine.update), whereas allocation is an APPEND (Stores.lean:1150
   refMake, :1366 DeferredStore.make, :1576 ScopeStore.make, Fibers.lean:877 spawn).
   A carrier with one `add` would silently create cells Lean never mints.

   This module satisfies the generated functor's `TABLE` signature
   (2026-09-08-engine-a1-state.md §1.5) verbatim, plus the extras of §4.1; `e4_table_list.ml`
   is its list twin and satisfies the same signature.  Both ascriptions are checked at compile
   time in test/prop_table.ml.

   Depends on: the OCaml standard library only (Map, List).

   Representation (R6 of §7; the answer to acceptance AC9, "no W1 regression"):
     Small l   an assoc list, ASCENDING by key, no duplicate key, length <= small_max
     Big m     a Map.Make(Int), cardinal > small_max
   `small_max` is 0, MEASURED: A1 §7 R6 predicted an assoc list would beat Map.Make(Int)
   below ~8 entries; it loses `find` by 1.65x and `add` by 1.41x at ONE entry and the gap
   only widens (the table is in e4_table.ml and in test/bench_carriers.ml's crossover
   section).  R6's mitigation is therefore refuted, not adopted, and AC9 must be met — if it
   needs meeting at all — some other way.  The two-arm representation is retained because
   raising the constant re-enables it, and because `Small []` is a cheaper `empty`.
   The cardinal is carried in the value, so `cardinal` is O(1): `E4_store.grow` allocates at
   `cardinal`, once per `refMake`, and an O(n) `Map.cardinal` there would restore the very
   quadratic the carrier exists to remove.  The representation is CANONICAL: `Big` is never
   used at or below `small_max` (a `remove` that crosses back down rebuilds a `Small`), so
   two tables with equal bindings have equal representations up to the Map's internal shape.

   Behaviours (each is a named PASS/FAIL line in test/prop_table.ml; `L` is the list carrier
   of e4_table_list.ml and `[[ ]]` is `bindings`):
   T1  set-absent-is-a-no-op:  not (mem k t)  ==>  set k v t == t  (PHYSICALLY equal)
                                                                          tested
   T2  set-present-replaces:   mem k t  ==>  find_opt k (set k v t) = Some v, and
                               bindings (set k v t) = bindings t with k's value replaced
                                                                          tested
   T3  add-fresh-appends:      cardinal (add (cardinal t) v t) = cardinal t + 1, and
                               to_list (add (cardinal t) v t) = to_list t @ [v]
                               WHEN the keys of t are 0 .. cardinal t - 1 (the dense case:
                               the ref heap and the deferred cells)        tested
   T4  bindings is ascending, and for a dense table it is
                               List.mapi (fun i v -> (i, v)) (to_list t)   tested
   T5  fold and filter_map visit in ASCENDING key order.  `for_all` does NOT: it keeps
       Map.for_all's node-first traversal so that it still SHORT-CIRCUITS, exactly as Lean's
       `List.all` does (Fibers.lean:609).  Its answer is a conjunction and therefore
       order-independent, and `finished` is its only caller; no law of any carrier in this
       lane depends on the order `for_all` visits in.  (A1 §4.1's T5 named `for_all` among
       the ordered operations — MEASURED FALSE for Map.Make and corrected here; the
       deviation is recorded in 2026-09-08-engine-lane-c-delivery.md.)      tested
   T6  agreement with the list carrier: for every sequence of operations drawn from
       {find_opt, set, add, remove, map, filter_map, for_all, fold}, E4_table and
       E4_table_list agree on every answer and on `bindings`   tested (>= 10 000 ops, LCG)
   T7  persistence: no operation mutates its argument; `t` observed after any operation on
       it is unchanged                                                     tested
   T8  snapshot = the value: a table is an ordinary immutable OCaml value with no mutable
       field anywhere in its representation (brief §2.3)         by construction; argued
   R6a canonical representation: is_small t  <->  cardinal t <= small_max, after every
       operation sequence, including one that grows past the threshold and shrinks back
                                                                           tested
   R6b representation independence: two tables with the same bindings, built by different
       op sequences, have the same `bindings`, `cardinal` and `is_small`   tested
   Bound: keys are host ints.  Lean's keys are `Nat` (RefKey.index, DeferredKey.index,
   ScopeEntry.key, FiberId) and every one of them is < E4_nat.max_nat on this host. *)

type 'a t

val empty : 'a t
val is_empty : 'a t -> bool
val mem : int -> 'a t -> bool

val find_opt : int -> 'a t -> 'a option
(** The key first: the shape the generated call sites use. *)

val find_opt' : 'a t -> int -> 'a option
(** The TABLE first: Lean's argument order for `RunMachine.fiber?` (Fibers.lean:573) and
    `DeferredStore.cellAt` (Stores.lean:1369), so an extern row is a name substitution and
    not an argument permutation.  See the deviation note in
    docs/research/2026-09-08-engine-lane-c-delivery.md. *)

val set : int -> 'a -> 'a t -> 'a t
(** Replace an EXISTING binding.  A no-op — and PHYSICALLY the same table — when the key is
    absent (T1).  This is Lean's `List.set` / replace-by-key `List.map`. *)

val add : int -> 'a -> 'a t -> 'a t
(** Insert or replace.  Allocation uses [add k v t] with [k = cardinal t] (E4_store.grow). *)

val remove : int -> 'a t -> 'a t
(** No Lean carrier removes; `remove` exists for the property tests and for A3. *)

val cardinal : 'a t -> int
(** O(1): carried in the value.  See the representation note above. *)

val map : ('a -> 'a) -> 'a t -> 'a t
(** Key-preserving bulk transform (RunMachine.dropObservers, Fibers.lean:1256, :1344). *)

val filter_map : (int -> 'a -> 'b option) -> 'a t -> 'b list
(** ASCENDING; the shape of RunMachine.completedExits (Fibers.lean:1543). *)

val for_all : (int -> 'a -> bool) -> 'a t -> bool
(** The shape of RunMachine.finished (Fibers.lean:609).  Short-circuits; the visit ORDER is
    unspecified (T5) — the answer is not. *)

val fold : (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
(** Ascending key order. *)

val bindings : 'a t -> (int * 'a) list
(** Ascending.  O(n) and 4-5x a list walk (§6.2 C6): paid once per READ, never per step. *)

val to_list : 'a t -> 'a list
(** Ascending, values only: the Lean list, for every table whose keys are allocated
    monotonically (§4.2's licence). *)

val of_list : (int * 'a) list -> 'a t
(** Left to right, each pair through [add]: a later duplicate key REPLACES an earlier one. *)

val singleton : int -> 'a -> 'a t

(* --- representation introspection: for the property tests and the bench, not for the
   machine.  Nothing in the engine's hot path may branch on these. --- *)

val small_max : int
(** The assoc-list / Map threshold, MEASURED in test/bench_carriers.ml: 0. *)

val is_small : 'a t -> bool
(** True iff the table is held as an assoc list (R6a: iff [cardinal t <= small_max]). *)
