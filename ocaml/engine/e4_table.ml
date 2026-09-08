(* E4_table — the persistent int-keyed table.  The property list is in e4_table.mli. *)

module IMap = Map.Make (Int)

(* The threshold, MEASURED in test/bench_carriers.ml (crossover section, 10 000 ops per cell,
   best of 7, native, OCaml 5.1.1).  A1 §7 R6 predicted an ascending assoc list would beat
   Map.Make(Int) below ~8 entries.  It does not, at any size:

     n     find (assoc/map)   set (assoc/map)   add (assoc/map)
     1           1.65x              0.91x             1.41x
     4           1.84x              0.98x             1.62x
     8           2.48x              1.17x             2.13x
     64          9.62x              3.51x             8.33x

   The Map wins `find` and `add` from ONE entry up; the assoc list is 2-12% faster on `set`
   only up to n = 4, which is noise beside a 1.5x loss on the other two.  So the mitigation
   R6 proposed for acceptance AC9 is REFUTED, and the threshold is 0: every non-empty table
   is a Map.  The two-arm representation is kept because it is one constant away from being
   re-enabled if a future workload contradicts the measurement, and because `Small []` is a
   genuinely cheaper `empty` than an empty Map node. *)
let small_max = 0

type 'a rep =
  | Small of (int * 'a) list (* ascending by key, no duplicate key, length <= small_max *)
  | Big of 'a IMap.t (* cardinal > small_max *)

(* The cardinal is carried so that `cardinal` is O(1) (E4_store.grow allocates at it). *)
type 'a t = { n : int; rep : 'a rep }

let empty : 'a t = { n = 0; rep = Small [] }
let is_empty (t : 'a t) : bool = t.n = 0
let cardinal (t : 'a t) : int = t.n
let is_small (t : 'a t) : bool = match t.rep with Small _ -> true | Big _ -> false

let big_of_small (l : (int * 'a) list) : 'a IMap.t =
  List.fold_left (fun m (k, v) -> IMap.add k v m) IMap.empty l

(* ------------------------------------------------------------------ reads *)

let rec find_small (k : int) (l : (int * 'a) list) : 'a option =
  match l with
  | [] -> None
  | (k', v) :: r -> if k' = k then Some v else if k' > k then None else find_small k r

let find_opt (k : int) (t : 'a t) : 'a option =
  match t.rep with Small l -> find_small k l | Big m -> IMap.find_opt k m

let find_opt' (t : 'a t) (k : int) : 'a option = find_opt k t

(* Separate from find_small so that no `option` is ever compared structurally: the values
   are abstract to this module (ocaml/STANDARDS.md §4). *)
let rec mem_small (k : int) (l : (int * 'a) list) : bool =
  match l with
  | [] -> false
  | (k', _) :: r -> if k' = k then true else if k' > k then false else mem_small k r

let mem (k : int) (t : 'a t) : bool =
  match t.rep with Small l -> mem_small k l | Big m -> IMap.mem k m

(* ------------------------------------------------------------------ writes *)

(* Replace-if-present, ascending list.  `None` means "absent", so the caller can return the
   argument PHYSICALLY (T1). *)
let rec set_small (k : int) (v : 'a) (acc : (int * 'a) list) (l : (int * 'a) list) :
    (int * 'a) list option =
  match l with
  | [] -> None
  | (k', v') :: r ->
      if k' = k then Some (List.rev_append acc ((k, v) :: r))
      else if k' > k then None
      else set_small k v ((k', v') :: acc) r

(* ONE walk, not `mem` then `add`: Map.update rebuilds nothing when the callback answers
   None, and the stdlib's `if l == ll then m` short-circuit means an absent key gives back
   the SAME map physically — which is exactly T1. *)
let set (k : int) (v : 'a) (t : 'a t) : 'a t =
  match t.rep with
  | Small l -> (
      match set_small k v [] l with None -> t | Some l' -> { t with rep = Small l' })
  | Big m ->
      let m' = IMap.update k (function None -> None | Some _ -> Some v) m in
      if m' == m then t else { t with rep = Big m' }

(* Insert-or-replace, ascending list; the flag says whether the key was fresh. *)
let rec add_small (k : int) (v : 'a) (acc : (int * 'a) list) (l : (int * 'a) list) :
    (int * 'a) list * bool =
  match l with
  | [] -> (List.rev_append acc [ (k, v) ], true)
  | (k', v') :: r ->
      if k' = k then (List.rev_append acc ((k, v) :: r), false)
      else if k' > k then (List.rev_append acc ((k, v) :: (k', v') :: r), true)
      else add_small k v ((k', v') :: acc) r

let add (k : int) (v : 'a) (t : 'a t) : 'a t =
  match t.rep with
  | Small l ->
      let l', fresh = add_small k v [] l in
      let n' = if fresh then t.n + 1 else t.n in
      if n' > small_max then { n = n'; rep = Big (big_of_small l') }
      else { n = n'; rep = Small l' }
  | Big m ->
      (* ONE walk: the flag is set by the callback.  The ref is step-local and never enters a
         machine value (brief §2.3). *)
      let fresh = ref true in
      let m' = IMap.update k (function None -> Some v | Some _ -> fresh := false; Some v) m in
      { n = (if !fresh then t.n + 1 else t.n); rep = Big m' }

let remove (k : int) (t : 'a t) : 'a t =
  match t.rep with
  | Small l ->
      if not (mem_small k l) then t
      else { n = t.n - 1; rep = Small (List.filter (fun (k', _) -> k' <> k) l) }
  | Big m ->
      if not (IMap.mem k m) then t
      else
        let m' = IMap.remove k m in
        let n' = t.n - 1 in
        if n' <= small_max then { n = n'; rep = Small (IMap.bindings m') }
        else { n = n'; rep = Big m' }

let map (f : 'a -> 'a) (t : 'a t) : 'a t =
  match t.rep with
  | Small l -> { t with rep = Small (List.map (fun (k, v) -> (k, f v)) l) }
  | Big m -> { t with rep = Big (IMap.map f m) }

(* ------------------------------------------------------------- enumeration *)

let bindings (t : 'a t) : (int * 'a) list =
  match t.rep with Small l -> l | Big m -> IMap.bindings m

let fold (f : int -> 'a -> 'b -> 'b) (t : 'a t) (init : 'b) : 'b =
  match t.rep with
  | Small l -> List.fold_left (fun acc (k, v) -> f k v acc) init l
  | Big m -> IMap.fold f m init

let for_all (f : int -> 'a -> bool) (t : 'a t) : bool =
  match t.rep with
  | Small l -> List.for_all (fun (k, v) -> f k v) l
  | Big m -> IMap.for_all f m

let filter_map (f : int -> 'a -> 'b option) (t : 'a t) : 'b list =
  List.rev (fold (fun k v acc -> match f k v with Some b -> b :: acc | None -> acc) t [])

let to_list (t : 'a t) : 'a list = List.map snd (bindings t)
let of_list (l : (int * 'a) list) : 'a t = List.fold_left (fun t (k, v) -> add k v t) empty l
let singleton (k : int) (v : 'a) : 'a t = add k v empty
