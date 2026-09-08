(* E4_fibers_view_list — the LIST twin of E4_fibers_view: the same signature (`FIBERS`, the
   text the generator emits and e4_fibers_view.mli's own), backed by an association list held
   in ALLOCATION order and reproducing Lean's carrier operation for operation.  It is the
   `Ref` instance's fiber table (api_engine_ref.ml) and the differential's left-hand side.

   The point of the twin: `completed` here MAINTAINS NOTHING.  It is Lean's
   `m.fibers.filterMap (fun f => f.exit.map ((f.id, ·)))` (src/Effect4/Machine/Fibers.lean:
   1543), walked at read time, exactly as the generated engine did before lane G3.  So
   `Ref` vs `Fast` — 74 306 replay positions of lane X's differential — is precisely the
   question "does the maintained view answer what the scan answers", at every step of every
   tape of every corpus program.  If the twin maintained a view too, that question would not
   be asked anywhere.

   The projection is not an argument of `completed` (the seam's `completedExits` row takes the
   machine and nothing else), so the twin REMEMBERS the `exit_of` its last write was given.
   That is sound: it is `None` only while no write has happened, and then the list is empty
   and the answer is `[]` whatever the projection is.  It is a pure value — a closure inside
   an immutable record, never a mutable cell (brief §2.3).

   Depends on: the OCaml standard library only.

   The Lean operation each function reproduces:
     find_opt   `List.find?`                     (Fibers.lean:573-575 fiber?)
     set        replace-by-key `List.map`, a NO-OP on an absent key   (:577-579 update)
     add        `xs ++ [(k, v)]` when fresh                           (:877 spawn)
     map        `List.map`                                           (:1256, :1344)
     for_all    `List.all`                                           (:608-609 finished)
     completed  `List.filterMap`                                     (:1541-1543)

   Behaviours:
   TFV1 the internal list is in ALLOCATION order, exactly Lean's carrier   by construction
   TFV2 `bindings`, `to_list` and `completed` are ASCENDING by key.  For every table the
        machine can build the two orders COINCIDE (ids are minted monotonically, Fibers.lean:
        867, :877; lane C's licence, re-verified)                          by construction
   TFV3 at most one binding per key                                        by construction
   TFV4 no polymorphic comparison touches a value: every comparison is on an int key
        (ocaml/STANDARDS.md §4)                                            by construction *)

type ('a, 'x) t = { l : (int * 'a) list; ex : ('a -> 'x option) option }

let empty : ('a, 'x) t = { l = []; ex = None }
let is_empty (t : ('a, 'x) t) : bool = match t.l with [] -> true | _ :: _ -> false
let mem (k : int) (t : ('a, 'x) t) : bool = List.exists (fun (k', _) -> k' = k) t.l

let find_opt (k : int) (t : ('a, 'x) t) : 'a option =
  let rec go = function
    | [] -> None
    | (k', v) :: r -> if k' = k then Some v else go r
  in
  go t.l

let set ~(exit_of : 'a -> 'x option) (k : int) (v : 'a) (t : ('a, 'x) t) : ('a, 'x) t =
  if mem k t then
    { l = List.map (fun (k', v') -> if k' = k then (k', v) else (k', v')) t.l;
      ex = Some exit_of }
  else t

let add ~(exit_of : 'a -> 'x option) (k : int) (v : 'a) (t : ('a, 'x) t) : ('a, 'x) t =
  if mem k t then set ~exit_of k v t else { l = t.l @ [ (k, v) ]; ex = Some exit_of }

let map ~(exit_of : 'a -> 'x option) (f : 'a -> 'a) (t : ('a, 'x) t) : ('a, 'x) t =
  { l = List.map (fun (k, v) -> (k, f v)) t.l; ex = Some exit_of }

let cardinal (t : ('a, 'x) t) : int = List.length t.l

let bindings (t : ('a, 'x) t) : (int * 'a) list =
  List.stable_sort (fun (a, _) (b, _) -> compare (a : int) b) t.l

let to_list (t : ('a, 'x) t) : 'a list = List.map snd (bindings t)
let for_all (f : int -> 'a -> bool) (t : ('a, 'x) t) : bool =
  List.for_all (fun (k, v) -> f k v) t.l

(* Lean's filterMap, walked — no maintenance, no cache. *)
let completed (t : ('a, 'x) t) : (int * 'x) list =
  match t.ex with
  | None -> []
  | Some exit_of ->
    List.filter_map
      (fun (k, v) -> match exit_of v with None -> None | Some x -> Some (k, x))
      (bindings t)

let of_list ~(exit_of : 'a -> 'x option) (l : (int * 'a) list) : ('a, 'x) t =
  List.fold_left (fun t (k, v) -> add ~exit_of k v t) empty l

(* --- the twin's own windows (TFV1) and the E4_fibers_view extras. --- *)
let raw (t : ('a, 'x) t) : (int * 'a) list = t.l
let insertion_order (t : ('a, 'x) t) : 'a list = List.map snd t.l
