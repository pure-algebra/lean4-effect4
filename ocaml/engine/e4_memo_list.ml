(* E4_memo_list — the LIST twin of E4_memo: the same signature (`LAYERS`, 2026-09-08-engine-
   a1-state.md §1.5), backed by `List (LayerId × MemoEntry)` in INSERTION order, reproducing
   src/Effect4/Machine/Stores.lean:866-886 operation for operation — DUPLICATES AND ALL.

   This is the one twin whose raw carrier can differ from the map's: Lean's `insertEntry`
   appends unconditionally (:880), so a second insert under a bound key leaves TWO entries
   in the list where the map has one.  `find?` answers the FIRST (:867), `updateEntry` maps
   over ALL matching (:873) and `deleteEntry` filters ALL matching (:886) — so every
   OBSERVATION the machine can make is the same on both sides.  That is law MM2, and the
   differential in test/prop_memo.ml is what carries it.  `raw` exposes the duplicated list;
   `bindings` is the observable projection (first binding per key, sorted by key) so that
   the two carriers can be compared directly.

   Depends on: E4_memo (for `key` and `compare_key` only), the OCaml standard library.

   Behaviours:
   ML1 the internal list is in INSERTION order with Lean's duplicates      by construction
   ML2 find_opt is `List.find?`: the FIRST binding                         by construction
   ML3 insert APPENDS unconditionally (Lean :880)                          by construction
   ML4 update maps over ALL matching entries (Lean :873)                   by construction
   ML5 delete filters out ALL matching entries (Lean :886)                 by construction
   ML6 bindings dedupes by key keeping the FIRST, then sorts by E4_memo.compare_key, so
       it is exactly what the map's `bindings` answers (MM6)               tested *)

type 'a t = (E4_memo.key * 'a) list

(* Written out rather than `=`, so no polymorphic comparison appears in this file. *)
let key_eq (a : E4_memo.key) (b : E4_memo.key) : bool = E4_memo.compare_key a b = 0

let empty : 'a t = []

let find_opt (p : E4_memo.key) (t : 'a t) : 'a option =
  let rec go = function
    | [] -> None
    | (q, v) :: r -> if key_eq q p then Some v else go r
  in
  go t

let mem (p : E4_memo.key) (t : 'a t) : bool =
  match find_opt p t with Some _ -> true | None -> false

(* Lean's insertEntry: `m.entries ++ [(layer, entry)]`, with no membership test (:880). *)
let insert (p : E4_memo.key) (v : 'a) (t : 'a t) : 'a t = t @ [ (p, v) ]

(* Lean's updateEntry: `m.entries.map fun e => if e.1 = layer then (e.1, f e.2) else e`
   (:873) — every matching entry, and a no-op when none matches. *)
let update (p : E4_memo.key) (f : 'a -> 'a) (t : 'a t) : 'a t =
  List.map (fun (q, v) -> if key_eq q p then (q, f v) else (q, v)) t

(* Lean's deleteEntry: `m.entries.filter fun e => !(e.1 = layer)` (:886). *)
let delete (p : E4_memo.key) (t : 'a t) : 'a t =
  List.filter (fun (q, _) -> not (key_eq q p)) t

(* ML6: the observable projection — first binding per key, sorted by key. *)
let bindings (t : 'a t) : (E4_memo.key * 'a) list =
  let rec dedupe seen = function
    | [] -> []
    | (q, v) :: r ->
        if List.exists (fun s -> key_eq s q) seen then dedupe seen r
        else (q, v) :: dedupe (q :: seen) r
  in
  List.stable_sort (fun (a, _) (b, _) -> E4_memo.compare_key a b) (dedupe [] t)

let cardinal (t : 'a t) : int = List.length (bindings t)

(* The Lean carrier itself, duplicates included. *)
let raw (t : 'a t) : (E4_memo.key * 'a) list = t
let raw_length (t : 'a t) : int = List.length t

(* MemoWorld.lookup over list-backed entry tables (Stores.lean:890-904); the same fuel. *)
let lookup ~(parent : 'm -> int option) ~(id : 'm -> int) ~(entries : 'm -> 'a t)
    (world : 'm list) (layer : E4_memo.key) (start : int) : (int * 'a) option =
  let map_at (i : int) : 'm option = List.find_opt (fun m -> id m = i) world in
  let rec go (fuel : int) (i : int) : (int * 'a) option =
    if fuel <= 0 then None
    else
      match map_at i with
      | None -> None
      | Some m -> (
          match find_opt layer (entries m) with
          | Some e -> Some (i, e)
          | None -> ( match parent m with None -> None | Some p -> go (fuel - 1) p))
  in
  go (List.length world + 1) start
