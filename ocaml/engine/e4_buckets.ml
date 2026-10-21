(* e4_buckets.ml — the dispatcher: priority -> FIFO, persistent.
   The property list, the licences and the refusals are in e4_buckets.mli; this file holds the
   two carriers and nothing else.

   THE ABSTRACTION FUNCTION, once, for both carriers:

       bucket_contents (front, back) = front @ List.rev back        (Deque (git:79752b3e6^:src/OCaml5/Lib/Deque.lean))
       to_list t = the (priority, bucket_contents) pairs, ascending  (Map (git:79752b3e6^:src/OCaml5/Lib/Map.lean))

   `enqueue` conses onto `back` (O(1)); `drain` reverses each `back` exactly once (O(n) for
   the whole snapshot). The Lean carrier's `tasks ++ [t]` (Dispatcher.insert (src/Effect4/Machine/Fibers.lean)) is the same
   observation at quadratic cost: 79 x slower at bucket depth 1 024 and 18 500 x at 1e5
   (design §6.2), which is D-A3-1.

   Nothing here is mutable: no record field is `mutable`, no array is allocated, and neither
   Hashtbl nor Buffer nor Queue is named. That is brief rule 3 (B7). *)

module type S = sig
  type 'a t

  val empty : 'a t
  val is_empty : 'a t -> bool
  val armed : 'a t -> bool
  val arm : 'a t -> 'a t
  val disarm : 'a t -> 'a t
  val enqueue : 'a t -> priority:Z.t -> 'a -> 'a t
  val drain : 'a t -> 'a list * 'a t
  val length : 'a t -> Z.t
  val priorities : 'a t -> Z.t list
  val to_list : 'a t -> (Z.t * 'a list) list
  val of_list : armed:bool -> (Z.t * 'a list) list -> 'a t
end

(* The one place a priority is refused, shared by both carriers. `Dispatcher.enqueue` takes a
   `Nat` (Dispatcher.enqueue (src/Effect4/Machine/Fibers.lean)), so a negative priority cannot arise from the generated code; it is
   a violated precondition, hence an exception and not a `result` (Mirage's rule, survey §7). *)
let check_priority p = if Z.sign p < 0 then invalid_arg "E4_buckets: negative priority"

let rec check_ascending : (Z.t * _) list -> unit = function
  | [] | [ _ ] -> ()
  | (p, _) :: ((q, _) :: _ as rest) ->
    if Z.geq p q
    then invalid_arg "E4_buckets.of_list: priorities are not strictly ascending";
    check_ascending rest
;;

(* ============================================================ the default carrier *)

module Assoc : S = struct
  (* A bucket: its priority and its deque as a front/back pair. Contents = front @ rev back. *)
  type 'a bucket =
    { priority : Z.t
    ; front : 'a list
    ; back : 'a list
    }

  type 'a t =
    { buckets : 'a bucket list
    ; is_armed : bool
    }

  let empty = { buckets = []; is_armed = false }
  let armed t = t.is_armed
  let arm t = if t.is_armed then t else { t with is_armed = true }
  let disarm t = if t.is_armed then { t with is_armed = false } else t

  let bucket_is_empty b =
    match b.front, b.back with
    | [], [] -> true
    | _ -> false
  ;;

  let is_empty t = List.for_all bucket_is_empty t.buckets

  (* `Dispatcher.insert` (Dispatcher.insert (src/Effect4/Machine/Fibers.lean)), with `tasks ++ [task]` replaced by a cons onto
     the back list. The recursion depth is the number of priorities, 1..16 in a real
     dispatcher and 256 in the tripwire bench. *)
  let rec insert p x = function
    | [] -> [ { priority = p; front = [ x ]; back = [] } ]
    | b :: rest ->
      if Z.equal b.priority p
      then { b with back = x :: b.back } :: rest
      else if Z.lt p b.priority
      then { priority = p; front = [ x ]; back = [] } :: b :: rest
      else b :: insert p x rest
  ;;

  let enqueue t ~priority x =
    check_priority priority;
    { buckets = insert priority x t.buckets; is_armed = true }
  ;;

  (* B3: front @ rev back, bucket by bucket, ascending. `List.fold_right` is not tail
     recursive, and deliberately so: it recurses over the PRIORITIES (few), never over the
     tasks (many), and it builds the answer with one traversal of each list. *)
  let drain t =
    let tasks =
      List.fold_right (fun b acc -> b.front @ List.rev_append b.back acc) t.buckets []
    in
    tasks, empty
  ;;

  let length t =
    Z.of_int
      (List.fold_left
         (fun n b -> n + List.length b.front + List.length b.back)
         0
         t.buckets)
  ;;

  let priorities t = List.map (fun b -> b.priority) t.buckets
  let to_list t = List.map (fun b -> b.priority, b.front @ List.rev b.back) t.buckets

  let of_list ~armed l =
    List.iter (fun (p, _) -> check_priority p) l;
    check_ascending l;
    { buckets = List.map (fun (p, xs) -> { priority = p; front = xs; back = [] }) l
    ; is_armed = armed
    }
  ;;
end

(* ============================================================ the tripwire carrier *)

module Map_variant : S = struct
  module ZMap = Map.Make (Z)

  (* The same deque, under a balanced tree instead of an assoc list. R-A3-4: measured slower at
     every priority count >= 4 and every drain depth >= 8 (design §6.2), kept behind the same
     signature so the switch is one line if a program ever uses many priorities. *)
  type 'a t =
    { buckets : ('a list * 'a list) ZMap.t
    ; is_armed : bool
    }

  let empty = { buckets = ZMap.empty; is_armed = false }
  let armed t = t.is_armed
  let arm t = if t.is_armed then t else { t with is_armed = true }
  let disarm t = if t.is_armed then { t with is_armed = false } else t

  let is_empty t =
    ZMap.for_all
      (fun _ q ->
         match q with
         | [], [] -> true
         | _ -> false)
      t.buckets
  ;;

  let enqueue t ~priority x =
    check_priority priority;
    let buckets =
      ZMap.update
        priority
        (function
          | None -> Some ([ x ], [])
          | Some (f, b) -> Some (f, x :: b))
        t.buckets
    in
    { buckets; is_armed = true }
  ;;

  let drain t =
    (* `ZMap.fold` visits in increasing key order, so this list is descending; folding it left
       while prepending each bucket's contents rebuilds the ascending concatenation. *)
    let descending = ZMap.fold (fun _ q acc -> q :: acc) t.buckets [] in
    let tasks =
      List.fold_left (fun acc (f, b) -> f @ List.rev_append b acc) [] descending
    in
    tasks, empty
  ;;

  let length t =
    Z.of_int (ZMap.fold (fun _ (f, b) n -> n + List.length f + List.length b) t.buckets 0)
  ;;

  let priorities t = List.map fst (ZMap.bindings t.buckets)

  let to_list t =
    List.map (fun (p, (f, b)) -> p, f @ List.rev b) (ZMap.bindings t.buckets)
  ;;

  let of_list ~armed l =
    List.iter (fun (p, _) -> check_priority p) l;
    check_ascending l;
    { buckets = List.fold_left (fun m (p, xs) -> ZMap.add p (xs, []) m) ZMap.empty l
    ; is_armed = armed
    }
  ;;
end

(* D-A3-1: the assoc list is the dispatcher. One line switches the estate to the tripwire
   carrier, and no caller changes. *)
include Assoc
