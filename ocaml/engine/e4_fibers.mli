(* E4_fibers — the machine's fiber table over E4_table
   (docs/research/2026-09-08-engine-a1-state.md §4.2; field F2 of §1.2, extern rows 4-10 of
   §1.4).

   What it is: the RunMachine operations the extern table replaces, plus the ordering
   argument that licenses the substitution.

   The ordering argument, re-verified against src/Effect4/Machine/Fibers.lean at the tree
   this lane built on (781cfbc):
     * ids are allocated strictly monotonically — `childId := ⟨m.nextId⟩`, `nextId+1`
       (:867, :877), and nothing else writes nextId;
     * the root is id 0 with nextId := 1 (src/Effect4/Api.lean);
     * every insertion is an APPEND: `m.fibers ++ [child]` (:877 spawn, :2055 runFork,
       :2066 runCallback);
     * NO fiber is ever removed.  Every write to the field is one of :579 update (map,
       id-preserving), :613 empty (:= []), :877 append, :1256 / :1344 dropObservers (map,
       id-preserving).  :1543 completedExits is a filterMap READ, not a write.  `exitDone`
       clears a fiber's fields; it does not remove it.
     Therefore `m.fibers` is exactly the id-ascending list, and `to_list` reproduces it
     exactly.  RE-CHECK after each join commit (A1 risk R1); the differential's p4 row is
     the standing check.

   Because this module lives BESIDE the generated functor and not inside it, the fiber
   record is abstract here: every operation that Lean writes as a field access takes the
   accessor as a labelled argument (`~id_of`, `~exit_of`).  The instantiation site
   (`e4_engine.ml`, lane D) partially applies them once, so the generated call sites see a
   two-argument function.

   Depends on: E4_table.

   Behaviours (each is a named PASS/FAIL line in test/prop_fibers.ml):
   FB1 to_list = the Lean list: for every corpus program and tape, `to_list (fibers m)`
       equals api_gen's `m.fibers`, element for element.  NOT TESTABLE IN THIS LANE (the
       engine does not exist yet); the twin differential FB8 stands in.
                                                                  owed to lane X (§6.3 D1/D2)
   FB2 find is fiber?: find id t = List.find_opt (fun f -> id_of f = id) (to_list t)
       (Fibers.lean:573-575)                                                 tested
   FB3 update is update: to_list (update ~id_of f t) =
         List.map (fun g -> if id_of g = id_of f then f else g) (to_list t)
       (Fibers.lean:577-579)                                                 tested
   FB4 update on an UNKNOWN id is a no-op — Lean's map matches nothing, and E4_table.set
       does not insert (T1)                                                  tested
   FB5 append is spawn's: to_list (append id f t) = to_list t @ [f], and id = cardinal t
       for every machine the engine can reach (the monotone-allocation argument)
                                                                             tested
   FB6 finished is `m.fibers.all (·.exit.isSome)` (Fibers.lean:608-609); completed_exits is
       the ASCENDING filterMap `m.fibers.filterMap (fun f => f.exit.map ((f.id, ·)))`
       (Fibers.lean:1541-1543)                                               tested
   FB7 drop_observers is id-preserving: it is E4_table.map, so
       `List.map fst (bindings (drop_observers step t)) = List.map fst (bindings t)`
       (Fibers.lean:1256, :1344 are `fibers.map`, key-preserving)            tested
   FB8 agreement with the list twin (e4_table_list.ml driven by the same Lean operations)
       on random sequences of {find, update, append, drop_observers, finished,
       completed_exits}                                        tested (>= 10 000 ops, LCG)
   FB9 to_list is a READ, 4-5x a list walk (§6.2 C6).  A caller that puts it inside a
       per-step loop undoes the whole design.                     argued; benched
   Bound: fiber ids are host ints; `cardinal` is O(1). *)

type 'f t = 'f E4_table.t
(** Transparently an E4_table, so the generated functor can name one carrier. *)

val empty : 'f t

val find : int -> 'f t -> 'f option
(** `RunMachine.fiber?` with the key first. *)

val find_opt' : 'f t -> int -> 'f option
(** `RunMachine.fiber? m id`: Lean's argument order, so extern row 4 is a name substitution
    and not an argument permutation. *)

val update : id_of:('f -> int) -> 'f -> 'f t -> 'f t
(** `RunMachine.update`: replace the binding at [id_of f]; a NO-OP when absent (FB4). *)

val update_at : int -> 'f -> 'f t -> 'f t
(** The same, with the id already projected: what the shim calls once `run_fiber` is
    concrete (A1 §4.2's `update_by_id`). *)

val append : int -> 'f -> 'f t -> 'f t
(** `spawn`'s `m.fibers ++ [child]` at the freshly minted id (Fibers.lean:877). *)

val finished : exit_of:('f -> 'x option) -> 'f t -> bool
(** `RunMachine.finished` (Fibers.lean:608-609). *)

val completed_exits : id_of:('f -> int) -> exit_of:('f -> 'x option) -> 'f t -> (int * 'x) list
(** `RunMachine.completedExits` (Fibers.lean:1541-1543), ascending by id. *)

val drop_observers : ('f -> 'f) -> 'f t -> 'f t
(** `evaluatePrim.withFiber`'s and `dropObservers`' bulk `fibers.map`
    (Fibers.lean:1256, :1344): the per-fiber observer filter is the argument, because the
    fiber record is abstract here.  Id-preserving by construction (FB7). *)

val map : ('f -> 'f) -> 'f t -> 'f t
val for_all : ('f -> bool) -> 'f t -> bool
val filter_map : ('f -> 'b option) -> 'f t -> 'b list
val to_list : 'f t -> 'f list
val bindings : 'f t -> (int * 'f) list
val cardinal : 'f t -> int
