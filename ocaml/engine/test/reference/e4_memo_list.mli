(* E4_memo_list -- Lean's memo entry list: the model of E4_memo's carrier, and the reading of
   the generated machine's memo maps.

   What it is: `List (LayerId × MemoEntry)` in INSERTION order, as `MemoWorld.entryAt`,
   `MemoWorld.insertEntry`, `MemoWorld.updateEntry` and `MemoWorld.deleteEntry`
   (src/Effect4/Machine/Stores.lean) keep it, duplicates included.  It satisfies the generated
   functor's `LAYERS` signature, as E4_memo does.  Two tests read it:
   - test/prop_memo.ml, whose law MM2 is that E4_memo, which keeps the first binding of a key,
     makes every observation this list makes, though the list holds Lean's duplicates;
   - test/api_gen_inst.ml, whose memo projection reads the generated machine's lists through
     {!bindings}, so the differential compares them with E4_memo's {!E4_memo.bindings}.
   It is test machinery: it left the installed effect4_engine for the test library
   e4_reference on 2026-10-18 (the hygiene lane's H3), and it is the one list twin of the
   seven the C4 mutant campaign kept, for those two readers.

   Lean's insertEntry appends unconditionally, so a second insert under a bound key leaves TWO
   entries where E4_memo has one.  `find?` answers the FIRST, updateEntry maps over ALL matches
   and deleteEntry filters ALL matches, so every observation the machine can make is the same
   on both carriers (MM2).

   Depends on: Effect4_engine.E4_memo (the key and its order), the OCaml standard library.

   Behaviours:
   ML1 the list is in INSERTION order with Lean's duplicates               by construction
   ML2 find_opt is `List.find?`: the FIRST binding                         by construction
   ML3 insert APPENDS unconditionally (`MemoWorld.insertEntry`)            by construction
   ML4 update maps over ALL matching entries (`MemoWorld.updateEntry`)     by construction
   ML5 delete filters out ALL matching entries (`MemoWorld.deleteEntry`)   by construction
   ML6 bindings dedupes by key keeping the FIRST, then sorts by E4_memo.compare_key, so it is
       exactly what E4_memo's `bindings` answers (MM6)               tested (prop_memo MM6b)
   ML7 lookup is `MemoWorld.lookup` over these lists, with the same fuel as E4_memo's
                                                                      tested (prop_memo MM5) *)

type key = Effect4_engine.E4_memo.key

(** Lean's list itself: the generated machine's memo maps hold exactly this type. *)
type 'a t = (key * 'a) list

val empty : 'a t

(** The first binding under the key (ML2). *)
val find_opt : key -> 'a t -> 'a option

(** Appends, whatever the list holds (ML3). *)
val insert : key -> 'a -> 'a t -> 'a t

(** Maps every binding under the key (ML4). *)
val update : key -> ('a -> 'a) -> 'a t -> 'a t

(** Removes every binding under the key (ML5). *)
val delete : key -> 'a t -> 'a t

(** The first binding of each key, ascending by {!E4_memo.compare_key} (ML6). *)
val bindings : 'a t -> (key * 'a) list

(** The length of the list, duplicates included. *)
val raw_length : 'a t -> int

(** `MemoWorld.lookup` over a world whose maps hold these lists (ML7). *)
val lookup
  :  parent:('m -> Z.t option)
  -> id:('m -> Z.t)
  -> entries:('m -> 'a t)
  -> 'm list
  -> key
  -> Z.t
  -> (Z.t * 'a) option
