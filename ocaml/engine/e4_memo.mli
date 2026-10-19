(* E4_memo — the Layer machine's memo world: per-map entry tables keyed by a layer's identity
   (docs/research/2026-09-08-engine-a1-state.md §4.6; field F8 of §1.2, extern rows 25-28).

   What it is: the carrier for `MemoMap.entries : List (LayerId × MemoEntry)`
   (`MemoMap`, src/Effect4/Machine/Stores.lean), a persistent map keyed by `key` — the
   layer's PATH from the root program and the CALL that runs it, `[]` outside a definition's
   body (`LayerId := List Nat × CallId`, `CallId := List (List Nat)`,
   src/Effect4/Machine/Alphabets.lean; decisions row 341, step 3).

   The world itself (`MemoWorld`, src/Effect4/Machine/Stores.lean) is NOT tabled.
   Its append stays in `syncOpStep`'s `memoFork` arm in that file; `syncOpStep` stays generated (A1 §1.2, owner
   decision Q3).  One map per `Layer.provide` site; measure before revisiting.  `lookup`
   below is the world's parent walk, spelled here so that the engine and A2's cache share one
   spelling.

   This module satisfies the generated functor's `LAYERS` signature (A1 §1.5) verbatim;
   test/reference/e4_memo_list.ml, in the test library e4_reference, is its list twin and
   satisfies the same signature.  Both ascriptions are checked at compile time in
   test/prop_memo.ml.

   Depends on: the OCaml standard library only (Map.Make over `key`, with an EXPLICIT
   lexicographic comparison — a concrete type and a written comparison, so
   ocaml/STANDARDS.md §4's ban on polymorphic compare over abstract types is respected).

   Behaviours (each is a named PASS/FAIL line in test/prop_memo.ml):
   MM1 find_opt is entryAt: `(m.entries.find? fun e => e.1 = layer).map Prod.snd`
       (MemoWorld.entryAt (src/Effect4/Machine/Stores.lean)) — the FIRST binding                              tested
   MM2 insert KEEPS an existing binding.  Lean appends unconditionally (`MemoWorld.insertEntry`, src/Effect4/Machine/Stores.lean) and
       `find?` answers the FIRST, so a duplicate insert is invisible to entryAt;
       `MemoWorld.updateEntry` and `MemoWorld.deleteEntry` (src/Effect4/Machine/Stores.lean) touch
       ALL matching entries, so
       after either one the list and the map agree again.  Therefore "insert-if-absent" is
       EXACT for every observation the machine can make.  This is the one carrier law that
       is not an obvious equality; the property test against e4_memo_list.ml (which DOES
       append the duplicate, as Lean does) is what carries it.                tested
   MM3 update is a no-op on an absent key (`MemoWorld.updateEntry`, src/Effect4/Machine/Stores.lean)       tested
   MM4 delete removes EVERY matching entry (`MemoWorld.deleteEntry`, src/Effect4/Machine/Stores.lean), so after a delete no duplicate
       survives in the twin either                                            tested
   MM5 the parent chain's fuel is `world length + 1` (`MemoWorld.lookup`, src/Effect4/Machine/Stores.lean).  A forged parent id can
       make the chain cyclic (`MemoMap.parent`, src/Effect4/Machine/Stores.lean), so the fuel
       MUST be kept: `lookup` answers None at exhaustion rather than
       looping.                                                               tested
   MM6 bindings is in ASCENDING KEY ORDER (`compare_key`: the path lexicographic on int list,
       shorter-first on a prefix, then the call, path by path), which is NOT Lean's insertion
       order.  Nothing in the run path reads entry
       order — entryAt is by key, updateEntry and deleteEntry are by key — so the difference
       is unobservable.  If a future reader iterates entries, it must sort or this law
       breaks.  Stated so the breach is loud; the differential's p13 row compares the two
       sides sorted by path (A1 §6.3).                            argued; tested (MM6a/MM6b)
   MM7 agreement with the twin on random {insert, update, delete, find_opt} sequences over
       a small key universe: `find_opt` agrees at EVERY key after EVERY operation
                                                                 tested (>= 10 000 ops, LCG)
   Bound: a path is a list of host ints; `cardinal` counts DISTINCT keys. *)

(** A layer's identity: its path and the call that runs it. *)
type key = int list * int list list

type 'a t

val empty : 'a t

(** `MemoWorld.entryAt`'s inner half (MM1). *)
val find_opt : key -> 'a t -> 'a option

(** KEEPS an existing binding (MM2), and returns the table PHYSICALLY when the key is
    already bound. *)
val insert : key -> 'a -> 'a t -> 'a t

(** `MemoWorld.updateEntry`'s inner half; a no-op when absent (MM3). *)
val update : key -> ('a -> 'a) -> 'a t -> 'a t

(** `MemoWorld.deleteEntry`'s inner half (MM4). *)
val delete : key -> 'a t -> 'a t

(** Ascending by `compare_key` (MM6), NOT insertion order. *)
val bindings : 'a t -> (key * 'a) list

(** Distinct keys. *)
val cardinal : 'a t -> int

val mem : key -> 'a t -> bool

(** The lexicographic order on paths, written out: element by element, and a proper prefix
    first. *)
val compare_path : int list -> int list -> int

(** The order on calls: path by path with `compare_path`, a proper prefix first. *)
val compare_call : int list list -> int list list -> int

(** The order `bindings` is sorted by: the path, then the call.  Exposed so the twin and the
    differential sort the same way. *)
val compare_key : key -> key -> int

(** [lookup ~parent ~id ~entries world layer start] is `MemoWorld.get`
    (MemoWorld.lookup (src/Effect4/Machine/Stores.lean)): the map at [start] first, then the parent
    chain, with fuel `List.length world + 1` (MM5).  `mapAt` is `world.find?`, so the FIRST
    map with a given id wins.  Answers None at fuel exhaustion — a forged parent can make
    the chain cyclic and the fuel is what makes `lookup` total. *)
val lookup
  :  parent:('m -> int option)
  -> id:('m -> int)
  -> entries:('m -> 'a t)
  -> 'm list
  -> key
  -> int
  -> (int * 'a) option
