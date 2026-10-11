(* E4_memo — the memo world's per-map entry table, keyed by a layer's identity: its path and
   the call that runs it (`LayerId := List Nat × CallId`, decisions row 341, step 3).
   The property list is in e4_memo.mli. *)

(* Written out rather than `List.compare Int.compare`, so that the order this module sorts
   by is in this file and not in a stdlib version (ocaml/STANDARDS.md §4). *)
let rec compare_path (a : int list) (b : int list) : int =
  match (a, b) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys -> if x < y then -1 else if x > y then 1 else compare_path xs ys

(* A call is the list of its invocations' paths, innermost first (`CallId := List (List Nat)`):
   compared element by element with `compare_path`, a proper prefix first. *)
let rec compare_call (a : int list list) (b : int list list) : int =
  match (a, b) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
      let c = compare_path x y in
      if c <> 0 then c else compare_call xs ys

type key = int list * int list list

(* The path first, then the call: the builds of one layer under different calls sort
   together. *)
let compare_key ((p, c) : key) ((q, d) : key) : int =
  let k = compare_path p q in
  if k <> 0 then k else compare_call c d

module PMap = Map.Make (struct
  type t = key

  let compare = compare_key
end)

type 'a t = 'a PMap.t

let empty : 'a t = PMap.empty
let find_opt (p : key) (t : 'a t) : 'a option = PMap.find_opt p t
let mem (p : key) (t : 'a t) : bool = PMap.mem p t

(* MM2: Lean appends unconditionally and `find?` answers the first, so an insert over a bound
   key changes nothing any observation can see.  Returning `t` itself makes that explicit
   and costs nothing. *)
let insert (p : key) (v : 'a) (t : 'a t) : 'a t =
  if PMap.mem p t then t else PMap.add p v t

(* MM3: Lean's `entries.map (fun e => if e.1 = layer then (e.1, f e.2) else e)` matches
   nothing when the key is absent. *)
let update (p : key) (f : 'a -> 'a) (t : 'a t) : 'a t =
  match PMap.find_opt p t with None -> t | Some v -> PMap.add p (f v) t

let delete (p : key) (t : 'a t) : 'a t = PMap.remove p t
let bindings (t : 'a t) : (key * 'a) list = PMap.bindings t
let cardinal (t : 'a t) : int = PMap.cardinal t

(* MemoWorld.lookup (Stores.lean:890-904).  `mapAt` is `w.find? (·.id = id)`: the FIRST map
   with that id.  The fuel is `w.length + 1` and the `0` arm is `none` — a forged parent id
   can make the chain cyclic, and the fuel is what keeps this total (MM5). *)
let lookup ~(parent : 'm -> int option) ~(id : 'm -> int) ~(entries : 'm -> 'a t)
    (world : 'm list) (layer : key) (start : int) : (int * 'a) option =
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
