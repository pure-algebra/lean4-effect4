(* E4_table_list — the LIST twin of E4_table: the same signature (`TABLE`, 2026-09-08-engine-
   a1-state.md §1.5), backed by an association list held in ALLOCATION ORDER, reproducing
   Lean's List carriers operation for operation.  It is the differential's left-hand side
   (A1 §4.7) and the proof that the signature is Lean-shaped: if a signature cannot be
   implemented as Lean's list, the signature is wrong.  It is excluded from the bench except
   as the baseline the fast carrier is measured against.

   Depends on: the OCaml standard library only (List).

   The Lean operation each function reproduces:
     find_opt   `List.find?`                    (Stores.lean:1568 ScopeStore.entryAt)
     set        replace-by-key `List.map`, a NO-OP on an absent key
                                                (Stores.lean:1572, Fibers.lean:579)
     add        `xs ++ [(k, v)]` when fresh     (Stores.lean:1150, :1366, :1576,
                                                 Fibers.lean:877)
     remove     `List.filter`                   (Stores.lean:886's shape)
     map        `List.map`                      (Fibers.lean:1256)
     for_all    `List.all`                      (Fibers.lean:609)
     filter_map `List.filterMap`                (Fibers.lean:1543)

   Behaviours:
   TL1 the internal list is in ALLOCATION order, exactly Lean's carrier; `raw` and
       `insertion_order` expose it                                     by construction
   TL2 `bindings` and `to_list` are ASCENDING by key, so that the twin answers the same
       questions as E4_table.  For every table the machine can build the two orders
       COINCIDE — keys are allocated monotonically (A1 §4.2's licence, re-verified at
       Fibers.lean:867, :877; Stores.lean:1150, :1366) — and the property test checks
       exactly that on monotone sequences.                             tested (prop_table)
   TL3 at most one binding per key: `add` replaces in place rather than appending a
       duplicate, which is what Lean's allocate-then-set discipline guarantees for these
       four carriers.  (The memo world is the ONE carrier where Lean does append a
       duplicate; that is e4_memo_list.ml, not this file.)             by construction
   TL4 no polymorphic comparison touches a value: every comparison is on an int key
       (ocaml/STANDARDS.md §4)                                         by construction *)

type 'a t = (int * 'a) list

let empty : 'a t = []
let is_empty (t : 'a t) : bool = match t with [] -> true | _ :: _ -> false
let mem (k : int) (t : 'a t) : bool = List.exists (fun (k', _) -> k' = k) t

let find_opt (k : int) (t : 'a t) : 'a option =
  let rec go = function
    | [] -> None
    | (k', v) :: r -> if k' = k then Some v else go r
  in
  go t

let find_opt' (t : 'a t) (k : int) : 'a option = find_opt k t

let set (k : int) (v : 'a) (t : 'a t) : 'a t =
  if mem k t then List.map (fun (k', v') -> if k' = k then (k', v) else (k', v')) t else t

let add (k : int) (v : 'a) (t : 'a t) : 'a t = if mem k t then set k v t else t @ [ (k, v) ]
let remove (k : int) (t : 'a t) : 'a t = List.filter (fun (k', _) -> k' <> k) t
let cardinal (t : 'a t) : int = List.length t
let map (f : 'a -> 'a) (t : 'a t) : 'a t = List.map (fun (k, v) -> (k, f v)) t
let bindings (t : 'a t) : (int * 'a) list = List.stable_sort (fun (a, _) (b, _) -> compare (a : int) b) t
let to_list (t : 'a t) : 'a list = List.map snd (bindings t)
let filter_map (f : int -> 'a -> 'b option) (t : 'a t) : 'b list =
  List.filter_map (fun (k, v) -> f k v) (bindings t)
let for_all (f : int -> 'a -> bool) (t : 'a t) : bool = List.for_all (fun (k, v) -> f k v) t
let fold (f : int -> 'a -> 'b -> 'b) (t : 'a t) (init : 'b) : 'b =
  List.fold_left (fun acc (k, v) -> f k v acc) init (bindings t)
let of_list (l : (int * 'a) list) : 'a t = List.fold_left (fun t (k, v) -> add k v t) empty l
let singleton (k : int) (v : 'a) : 'a t = [ (k, v) ]

(* --- the twin's own windows: the Lean list itself (TL1). --- *)
let raw (t : 'a t) : (int * 'a) list = t
let insertion_order (t : 'a t) : 'a list = List.map snd t

(* --- the E4_table extras, so the twin can stand in everywhere the fast carrier does. --- *)
let small_max = max_int
let is_small (_ : 'a t) : bool = true
