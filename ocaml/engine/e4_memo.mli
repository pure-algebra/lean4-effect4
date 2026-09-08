(* E4_memo — the Layer machine's memo world: per-map entry tables keyed by layer path
   (docs/research/2026-09-08-engine-a1-state.md §4.6; field F8 of §1.2, extern rows 25-28).

   What it is: the carrier for `MemoMap.entries : List (LayerId × MemoEntry)`
   (src/Effect4/Machine/Stores.lean:851), a persistent map keyed by `int list` — the layer's
   PATH from the root program, never an identity (LayerId := List Nat, :176;
   LAYER-FB-LAYER-IDENTITY, :906-910).

   The world itself (`MemoWorld = List MemoMap`, :855) is NOT tabled: the append is inline in
   syncOpStep's memoFork arm (:2238) and syncOpStep must stay generated (A1 §1.2, owner
   decision Q3).  One map per `Layer.provide` site; measure before revisiting.  `lookup`
   below is the world's parent walk, spelled here so that the engine and A2's cache share one
   spelling.

   This module satisfies the generated functor's `LAYERS` signature (A1 §1.5) verbatim;
   `e4_memo_list.ml` is its list twin and satisfies the same signature.  Both ascriptions are
   checked at compile time in test/prop_memo.ml.

   Depends on: the OCaml standard library only (Map.Make over `int list`, with an EXPLICIT
   lexicographic comparison — a concrete type and a written comparison, so
   ocaml/STANDARDS.md §4's ban on polymorphic compare over abstract types is respected).

   Behaviours (each is a named PASS/FAIL line in test/prop_memo.ml):
   MM1 find_opt is entryAt: `(m.entries.find? fun e => e.1 = layer).map Prod.snd`
       (Stores.lean:866-867) — the FIRST binding                              tested
   MM2 insert KEEPS an existing binding.  Lean appends unconditionally (:876-880) and
       `find?` answers the FIRST, so a duplicate insert is invisible to entryAt;
       updateEntry (:869-873) and deleteEntry (:883-886) touch ALL matching entries, so
       after either one the list and the map agree again.  Therefore "insert-if-absent" is
       EXACT for every observation the machine can make.  This is the one carrier law that
       is not an obvious equality; the property test against e4_memo_list.ml (which DOES
       append the duplicate, as Lean does) is what carries it.                tested
   MM3 update is a no-op on an absent key (Lean's map-by-key, :869-873)       tested
   MM4 delete removes EVERY matching entry (:883-886), so after a delete no duplicate
       survives in the twin either                                            tested
   MM5 the parent chain's fuel is `world length + 1` (:890-904).  A forged parent id can
       make the chain cyclic (:906-910: the model cannot stop a program from forging a
       path), so the fuel MUST be kept: `lookup` answers None at exhaustion rather than
       looping.                                                               tested
   MM6 bindings is in ASCENDING PATH ORDER (lexicographic on int list, shorter-first on a
       prefix), which is NOT Lean's insertion order.  Nothing in the run path reads entry
       order — entryAt is by key, updateEntry and deleteEntry are by key — so the difference
       is unobservable.  If a future reader iterates entries, it must sort or this law
       breaks.  Stated so the breach is loud; the differential's p13 row compares the two
       sides sorted by path (A1 §6.3).                            argued; tested (MM6a/MM6b)
   MM7 agreement with the twin on random {insert, update, delete, find_opt} sequences over
       a small path universe: `find_opt` agrees at EVERY key after EVERY operation
                                                                 tested (>= 10 000 ops, LCG)
   Bound: a path is a list of host ints; `cardinal` counts DISTINCT paths. *)

type 'a t

val empty : 'a t

val find_opt : int list -> 'a t -> 'a option
(** `MemoWorld.entryAt`'s inner half (MM1). *)

val insert : int list -> 'a -> 'a t -> 'a t
(** KEEPS an existing binding (MM2), and returns the table PHYSICALLY when the path is
    already bound. *)

val update : int list -> ('a -> 'a) -> 'a t -> 'a t
(** `MemoWorld.updateEntry`'s inner half; a no-op when absent (MM3). *)

val delete : int list -> 'a t -> 'a t
(** `MemoWorld.deleteEntry`'s inner half (MM4). *)

val bindings : 'a t -> (int list * 'a) list
(** Ascending lexicographic on the path (MM6), NOT insertion order. *)

val cardinal : 'a t -> int
(** Distinct paths. *)

val mem : int list -> 'a t -> bool

val compare_path : int list -> int list -> int
(** The lexicographic order `bindings` is sorted by, written out: element by element, and a
    proper prefix first.  Exposed so the twin and the differential sort the same way. *)

val lookup :
  parent:('m -> int option) ->
  id:('m -> int) ->
  entries:('m -> 'a t) ->
  'm list ->
  int list ->
  int ->
  (int * 'a) option
(** [lookup ~parent ~id ~entries world layer start] is `MemoWorld.get`
    (src/Effect4/Machine/Stores.lean:890-904): the map at [start] first, then the parent
    chain, with fuel `List.length world + 1` (MM5).  `mapAt` is `world.find?`, so the FIRST
    map with a given id wins.  Answers None at fuel exhaustion — a forged parent can make
    the chain cyclic and the fuel is what makes `lookup` total. *)
