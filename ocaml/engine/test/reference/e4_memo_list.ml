(* E4_memo_list -- see e4_memo_list.mli. *)

module E4_memo = Effect4_engine.E4_memo

type key = E4_memo.key
type 'a t = (key * 'a) list

(* Written out rather than `=`, so no polymorphic comparison appears in this file. *)
let key_eq (a : E4_memo.key) (b : E4_memo.key) : bool = E4_memo.compare_key a b = 0
let empty : 'a t = []

let find_opt (p : E4_memo.key) (t : 'a t) : 'a option =
  let rec go = function
    | [] -> None
    | (q, v) :: r -> if key_eq q p then Some v else go r
  in
  go t
;;

(* Lean's insertEntry: `m.entries ++ [(layer, entry)]`, with no membership test (`MemoWorld.insertEntry`, src/Effect4/Machine/Stores.lean). *)
let insert (p : E4_memo.key) (v : 'a) (t : 'a t) : 'a t = t @ [ p, v ]

(* Lean's updateEntry: `m.entries.map fun e => if e.1 = layer then (e.1, f e.2) else e`
   MemoWorld.updateEntry (src/Effect4/Machine/Stores.lean) — every matching entry, and a no-op when none matches. *)
let update (p : E4_memo.key) (f : 'a -> 'a) (t : 'a t) : 'a t =
  List.map (fun (q, v) -> if key_eq q p then q, f v else q, v) t
;;

(* Lean's deleteEntry: `m.entries.filter fun e => !(e.1 = layer)` MemoWorld.deleteEntry (src/Effect4/Machine/Stores.lean). *)
let delete (p : E4_memo.key) (t : 'a t) : 'a t =
  List.filter (fun (q, _) -> not (key_eq q p)) t
;;

(* ML6: the observable projection — first binding per key, sorted by key. *)
let bindings (t : 'a t) : (E4_memo.key * 'a) list =
  let rec dedupe seen = function
    | [] -> []
    | (q, v) :: r ->
      if List.exists (fun s -> key_eq s q) seen
      then dedupe seen r
      else (q, v) :: dedupe (q :: seen) r
  in
  List.stable_sort (fun (a, _) (b, _) -> E4_memo.compare_key a b) (dedupe [] t)
;;

(* The length of the Lean carrier itself, duplicates included. *)
let raw_length (t : 'a t) : int = List.length t

(* MemoWorld.lookup over list-backed entry tables (MemoWorld.lookup (src/Effect4/Machine/Stores.lean)); the same fuel. *)
let lookup
      ~(parent : 'm -> Z.t option)
      ~(id : 'm -> Z.t)
      ~(entries : 'm -> 'a t)
      (world : 'm list)
      (layer : E4_memo.key)
      (start : Z.t)
  : (Z.t * 'a) option
  =
  let map_at (i : Z.t) : 'm option = List.find_opt (fun m -> Z.equal (id m) i) world in
  let rec go (fuel : int) (i : Z.t) : (Z.t * 'a) option =
    if fuel <= 0
    then None
    else (
      match map_at i with
      | None -> None
      | Some m ->
        (match find_opt layer (entries m) with
         | Some e -> Some (i, e)
         | None ->
           (match parent m with
            | None -> None
            | Some p -> go (fuel - 1) p)))
  in
  go (List.length world + 1) start
;;
