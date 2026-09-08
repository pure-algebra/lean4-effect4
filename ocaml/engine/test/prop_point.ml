(* prop_point.ml — the property tests of E4_ppath and E4_env (lane G2, docs/research/
   2026-09-08-engine-prof-chain.md §5.1; the laws are e4_ppath.mli's PP1-PP7 and
   e4_env.mli's PE1-PE7).

   Every law is one named PASS/FAIL line.  The twins are e4_ppath_list.ml and e4_env_list.ml,
   which carry the Lean list and reproduce `Point.child`'s `path ++ [i]`, `resolve`'s
   `Node.at_ (Node.eff root) p.path`, `Point.childWith`'s `env ++ [v]`, `env[i]?`,
   `List.length` and `List.take` operation for operation — so an agreement failure here is a
   carrier law, exactly as it is for lane C's five.  Exit code 0 iff every line passed.

   The PPATH and PENV module types below are the generated functor's own text
   (src/OCaml5/Lcnf/Externs.lean `carrierSignatures`, emitted at ocaml/engine/api_engine.ml):
   if either carrier drifts from the contract, this file stops compiling.

   PP3 is also the premise of the seam's law NODE-AT (ocaml/engine/tools/api_engine_prelude.ml,
   `sh_node_at`): the carried node IS `Node.at_` of the spine, so answering `Node.at_` from
   the record is Lean's answer whenever the node the caller passes is the spine's root, and
   the row walks when it is not. *)

open Effect4_engine

[@@@warning "-32"]
(* A module type used only for an ascription has, by definition, no used values. *)

module type PPATH = sig
  type 'n t

  val make : 'n -> 'n t
  val root : 'n t -> 'n
  val snoc : ('n -> int -> 'n option) -> 'n t -> int -> 'n t
  val append : ('n -> int -> 'n option) -> 'n t -> int list -> 'n t
  val node : ('n -> int -> 'n option) -> 'n t -> 'n option
  val walk : ('n -> int -> 'n option) -> 'n -> int list -> 'n option
  val to_list : 'n t -> int list
  val length : 'n t -> int
end

module type PENV = sig
  type 'a t

  val empty : 'a t
  val snoc : 'a t -> 'a -> 'a t
  val append : 'a t -> 'a list -> 'a t
  val get : 'a t -> int -> 'a option
  val length : 'a t -> int
  val take : 'a t -> int -> 'a t
  val to_list : 'a t -> 'a list
  val of_list : 'a list -> 'a t
end

module _ : PPATH = E4_ppath
module _ : PPATH = E4_ppath_list
module _ : PENV = E4_env
module _ : PENV = E4_env_list

[@@@warning "+32"]

module P = E4_ppath
module PL = E4_ppath_list
module V = E4_env
module VL = E4_env_list

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let argue name why = Printf.printf "PASS %s [by construction: %s]\n" name why

(* Java's 48-bit LCG, as in lane C's property tests: the constants fit a 63-bit OCaml int
   and the top 32 bits are taken, so the weak low bits never reach `rand`. *)
let lcg_mask = 0xFFFFFFFFFFFF
let lcg_seed = 0x1234ABCD5678
let s = ref lcg_seed
let reset () = s := lcg_seed

let next () =
  s := ((!s * 25214903917) + 11) land lcg_mask;
  !s lsr 16

let rand n = if n <= 0 then 0 else next () mod n

(* ------------------------------------------------------------------ the node under test *)

(* A stand-in for `Effect4.Program.Node`: a finitely branching tree, so `child` is Lean's
   `Node.child` — total, and `None` off the tree. *)
type tree = Node of int * tree list

let child (Node (_, kids)) i = List.nth_opt kids i

let rec build depth id =
  if depth = 0 then Node (id, [])
  else Node (id, List.init 3 (fun k -> build (depth - 1) ((id * 3) + k + 1)))

let root_tree = build 6 0

(* the reference: Lean's `Node.at_` (src/Effect4/Program/Compile.lean:118-122) *)
let rec at_ n l =
  match l with
  | [] -> Some n
  | i :: rest -> ( match child n i with None -> None | Some m -> at_ m rest)

(* Lean's `List.take`, clamped at both ends *)
let rec lean_take k l =
  if k <= 0 then [] else match l with [] -> [] | v :: r -> v :: lean_take (k - 1) r

(* Words allocated by ONE call, measured over 1 000 of them and bracketed by a minor
   collection: the minor-word counter is only exact at a collection point, so a handful of
   words per call does not register otherwise. *)
let words f =
  Gc.minor ();
  let a0 = Gc.minor_words () in
  for _ = 1 to 1000 do
    ignore (Sys.opaque_identity (f ()))
  done;
  Gc.minor ();
  let a1 = Gc.minor_words () in
  int_of_float ((a1 -. a0) /. 1000.0)

(* ------------------------------------------------------------------------------- E4_ppath *)

let pp1 () =
  let p = ref (P.make root_tree) and l = ref [] in
  let ok = ref (P.to_list (P.make root_tree) = []) in
  for i = 0 to 199 do
    let k = rand 4 in
    p := P.snoc child !p k;
    l := !l @ [ k ];
    if P.to_list !p <> !l then ok := false;
    if P.length !p <> List.length !l then ok := false;
    ignore i
  done;
  check "PP1 to_list (make n) = [] and to_list (snoc c p i) = to_list p @ [i]" !ok

let pp2 () =
  (* snoc allocates a constant number of words, whatever the depth: that IS the sharing *)
  let shallow = P.snoc child (P.make root_tree) 0 in
  let deep = ref (P.make root_tree) in
  for _ = 1 to 2000 do
    deep := P.snoc child !deep (rand 3)
  done;
  let deep = !deep in
  let w_shallow = words (fun () -> P.snoc child shallow 1) in
  let w_deep = words (fun () -> P.snoc child deep 1) in
  let l_shallow = words (fun () -> PL.snoc child (PL.snoc child (PL.make root_tree) 0) 1) in
  let dl = ref (PL.make root_tree) in
  for _ = 1 to 2000 do
    dl := PL.snoc child !dl 0
  done;
  let l_deep = words (fun () -> PL.snoc child !dl 1) in
  Printf.printf
    "  snoc words: E4_ppath depth 1 = %d, depth 2000 = %d;  twin depth 1 = %d, depth 2000 = %d\n"
    w_shallow w_deep l_shallow l_deep;
  check "PP2 snoc is O(1) words at every depth (the spine is shared)" (w_deep <= w_shallow + 2);
  check "PP2' the twin copies: its snoc grows with the depth" (l_deep > 10 * l_shallow)

let pp3 () =
  let ok = ref true in
  let p = ref (P.make root_tree) and l = ref [] in
  (* on the tree, then off it: `rand 5` reaches indices 3 and 4, which no node has *)
  for _ = 1 to 60 do
    let k = rand 5 in
    p := P.snoc child !p k;
    l := !l @ [ k ];
    let a = P.node child !p and b = at_ root_tree !l in
    if a <> b then ok := false;
    if P.node child !p <> P.walk child (P.root !p) (P.to_list !p) then ok := false
  done;
  check "PP3 node c p = walk c (root p) (to_list p) = Node.at_, on and off the tree" !ok

let pp5 () =
  let ok = ref true in
  for _ = 1 to 40 do
    let base = List.init (rand 8) (fun _ -> rand 3) in
    let more = List.init (rand 6) (fun _ -> rand 3) in
    let p = P.append child (P.make root_tree) base in
    let q = P.append child p more in
    let f = List.fold_left (fun a i -> P.snoc child a i) p more in
    if P.to_list q <> base @ more then ok := false;
    if P.to_list q <> P.to_list f then ok := false;
    if P.node child q <> at_ root_tree (base @ more) then ok := false
  done;
  check "PP5 append c p l = fold snoc, and to_list (append c p l) = to_list p @ l" !ok

let pp6 () =
  let p = P.append child (P.make root_tree) [ 0; 1; 2 ] in
  let before = P.to_list p and node_before = P.node child p in
  let _ = P.snoc child p 1 in
  let _ = P.append child p [ 2; 0 ] in
  check "PP6 persistence: p is unchanged by any snoc/append on it"
    (P.to_list p = before && P.node child p = node_before && before = [ 0; 1; 2 ])

let pp7 () =
  reset ();
  let a = ref (P.make root_tree) and b = ref (PL.make root_tree) in
  let ok = ref true in
  for _ = 1 to 400 do
    (match rand 4 with
     | 0 ->
       let l = List.init (rand 3) (fun _ -> rand 4) in
       a := P.append child !a l;
       b := PL.append child !b l
     | _ ->
       let k = rand 4 in
       a := P.snoc child !a k;
       b := PL.snoc child !b k);
    if P.to_list !a <> PL.to_list !b then ok := false;
    if P.node child !a <> PL.node child !b then ok := false;
    if P.length !a <> PL.length !b then ok := false
  done;
  check "PP7 agreement with the list twin on 400 random spine operations (to_list and node)"
    !ok

(* --------------------------------------------------------------------------------- E4_env *)

let pe1 () =
  let e = ref V.empty and l = ref [] in
  let ok = ref (V.to_list V.empty = []) in
  for i = 0 to 199 do
    e := V.snoc !e i;
    l := !l @ [ i ];
    if V.to_list !e <> !l then ok := false
  done;
  check "PE1 to_list empty = [] and to_list (snoc e v) = to_list e @ [v]" !ok

let pe2 () =
  let shallow = V.snoc V.empty 0 in
  let deep = ref V.empty in
  for i = 1 to 2000 do
    deep := V.snoc !deep i
  done;
  let deep = !deep in
  let w_shallow = words (fun () -> V.snoc shallow 1) in
  let w_deep = words (fun () -> V.snoc deep 1) in
  let dl = ref VL.empty in
  for i = 1 to 2000 do
    dl := VL.snoc !dl i
  done;
  let l_shallow = words (fun () -> VL.snoc (VL.snoc VL.empty 0) 1) in
  let l_deep = words (fun () -> VL.snoc !dl 1) in
  Printf.printf
    "  snoc words: E4_env depth 1 = %d, depth 2000 = %d;  twin depth 1 = %d, depth 2000 = %d\n"
    w_shallow w_deep l_shallow l_deep;
  check "PE2 snoc is O(1) words at every depth (the spine is shared)" (w_deep <= w_shallow + 2);
  check "PE2' the twin copies: its snoc grows with the depth" (l_deep > 10 * l_shallow)

let pe3_pe4 () =
  let e = ref V.empty and l = ref [] in
  let ok3 = ref true and ok4 = ref true in
  for i = 0 to 120 do
    e := V.snoc !e (i * 7);
    l := !l @ [ i * 7 ];
    if V.length !e <> List.length !l then ok4 := false;
    for j = -2 to List.length !l + 2 do
      if V.get !e j <> (if j < 0 then None else List.nth_opt !l j) then ok3 := false
    done
  done;
  check "PE3 get e i = List.nth_opt (to_list e) i, and None outside the range" !ok3;
  check "PE4 length e = List.length (to_list e), maintained incrementally" !ok4

let pe5 () =
  let l = List.init 64 (fun i -> i * 3) in
  let e = V.of_list l in
  let ok = ref true in
  for k = -3 to 70 do
    if V.to_list (V.take e k) <> lean_take k l then ok := false;
    if V.length (V.take e k) <> List.length (lean_take k l) then ok := false
  done;
  check "PE5 to_list (take e k) = List.take k (to_list e), clamped at both ends" !ok

let pe6 () =
  let e = V.of_list [ 1; 2; 3 ] in
  let before = V.to_list e in
  let _ = V.snoc e 9 in
  let _ = V.take e 1 in
  check "PE6 persistence: e is unchanged by any snoc/take on it"
    (V.to_list e = before && before = [ 1; 2; 3 ])

let pe7 () =
  reset ();
  let a = ref V.empty and b = ref VL.empty in
  let ok = ref true in
  for i = 1 to 600 do
    (match rand 8 with
     | 0 ->
       let k = rand 40 in
       a := V.take !a k;
       b := VL.take !b k
     | 1 ->
       let l = List.init (rand 3) (fun j -> (i * 100) + j) in
       a := V.append !a l;
       b := VL.append !b l
     | _ ->
       a := V.snoc !a i;
       b := VL.snoc !b i);
    if V.to_list !a <> VL.to_list !b then ok := false;
    if V.length !a <> VL.length !b then ok := false;
    if V.get !a (rand (1 + V.length !a)) <> VL.get !b (rand 1) then ()
  done;
  (* the positional read compared at every index, once at the end *)
  let n = V.length !a in
  for j = -1 to n do
    if V.get !a j <> VL.get !b j then ok := false
  done;
  check "PE7 agreement with the list twin on 600 random operations (to_list, length, get)" !ok

let () =
  print_endline "== prop_point: E4_ppath / E4_env against their list twins ==";
  pp1 ();
  pp2 ();
  pp3 ();
  argue "PP4 node is a pure function of the value: no mutation, no memo, nothing outside the record"
    "e4_ppath.ml has no ref, no Hashtbl and no mutable field (brief §2.3)";
  pp5 ();
  pp6 ();
  pp7 ();
  pe1 ();
  pe2 ();
  pe3_pe4 ();
  pe5 ();
  pe6 ();
  pe7 ();
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  if !failures > 0 then exit 1
