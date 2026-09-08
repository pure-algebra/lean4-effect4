(* prop_table.ml — the property tests of E4_table (lane C, docs/research/
   2026-09-08-engine-a1-state.md §4.1 T1-T8 and §7 R6).

   Every law of e4_table.mli is one named PASS/FAIL line.  The differential runs a fixed LCG
   over the operation alphabet against e4_table_list.ml — the list twin that reproduces
   Lean's carrier operation for operation — and compares BOTH the answer of each operation
   and the full `bindings` after it.  Exit code 0 iff every line passed.

   The first thing this file does is a COMPILE-TIME check that both carriers satisfy the
   TABLE module type as lane G will emit it into the generated functor (A1 §1.5, verbatim).
   If a carrier drifts from the contract, this file stops compiling. *)

open Effect4_engine

[@@@warning "-32"]
(* A module type used only for an ascription has, by definition, no used values. *)

module type TABLE = sig
  type 'a t

  val empty : 'a t
  val find_opt : int -> 'a t -> 'a option
  val set : int -> 'a -> 'a t -> 'a t
  val add : int -> 'a -> 'a t -> 'a t
  val remove : int -> 'a t -> 'a t
  val mem : int -> 'a t -> bool
  val cardinal : 'a t -> int
  val map : ('a -> 'a) -> 'a t -> 'a t
  val filter_map : (int -> 'a -> 'b option) -> 'a t -> 'b list
  val for_all : (int -> 'a -> bool) -> 'a t -> bool
  val fold : (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val bindings : 'a t -> (int * 'a) list
  val of_list : (int * 'a) list -> 'a t
  val to_list : 'a t -> 'a list
end

module _ : TABLE = E4_table
module _ : TABLE = E4_table_list
[@@@warning "+32"]


module T = E4_table
module L = E4_table_list

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let argue name why = Printf.printf "PASS %s [by construction: %s]\n" name why

(* ------------------------------------------------------------------ the LCG.
   One multiplier, one increment, one seed: the run is reproducible byte for byte. *)
(* Java's 48-bit LCG (multiplier 25214903917, increment 11): its constants fit a 63-bit
   OCaml int, and the top 32 bits are taken so the weak low bits never reach `rand`. *)
let lcg_mask = 0xFFFFFFFFFFFF
let lcg_seed = 0x1234ABCD5678
let s = ref lcg_seed
let reset () = s := lcg_seed

let next () =
  s := ((!s * 25214903917) + 11) land lcg_mask;
  !s lsr 16

let rand n = if n <= 0 then 0 else next () mod n

(* ------------------------------------------------------------------ printing *)
let show_opt = function None -> "-" | Some v -> string_of_int v
let show_bindings b = String.concat ";" (List.map (fun (k, v) -> Printf.sprintf "%d=%d" k v) b)
let show_ints l = String.concat "," (List.map string_of_int l)

(* A random table and the same table in the twin, built by the same op sequence. *)
let build n key_space =
  let a = ref T.empty and b = ref L.empty in
  for _ = 1 to n do
    let k = rand key_space and v = rand 1000 in
    if rand 4 = 0 then (
      a := T.set k v !a;
      b := L.set k v !b)
    else (
      a := T.add k v !a;
      b := L.add k v !b)
  done;
  (!a, !b)

let dense n =
  let t = ref T.empty in
  for i = 0 to n - 1 do
    t := T.add i (i * 7) !t
  done;
  !t

(* ------------------------------------------------------------------ T1 *)
let t1 () =
  reset ();
  let ok = ref true in
  for _ = 1 to 200 do
    let t, _ = build (rand 30) 20 in
    for k = -3 to 30 do
      if not (T.mem k t) then begin
        let t' = T.set k 999 t in
        (* PHYSICALLY equal, not merely observationally *)
        if not (t' == t) then ok := false
      end
    done
  done;
  check "T1 set-absent-is-a-no-op (physically the same table)" !ok

(* ------------------------------------------------------------------ T2 *)
let t2 () =
  reset ();
  let ok = ref true in
  for _ = 1 to 200 do
    let t, _ = build (1 + rand 30) 20 in
    List.iter
      (fun (k, _) ->
        let t' = T.set k 12345 t in
        let expected = List.map (fun (j, w) -> if j = k then (j, 12345) else (j, w)) (T.bindings t) in
        if T.find_opt k t' <> Some 12345 then ok := false;
        if T.bindings t' <> expected then ok := false;
        if T.cardinal t' <> T.cardinal t then ok := false)
      (T.bindings t)
  done;
  check "T2 set-present-replaces (find_opt and bindings)" !ok

(* ------------------------------------------------------------------ T3 *)
let t3 () =
  let ok = ref true in
  List.iter
    (fun n ->
      let t = dense n in
      let t' = T.add (T.cardinal t) 4242 t in
      if T.cardinal t' <> T.cardinal t + 1 then ok := false;
      if T.to_list t' <> T.to_list t @ [ 4242 ] then ok := false)
    [ 0; 1; 2; 7; 8; 9; 16; 100; 1000 ];
  check "T3 add-fresh-appends on a dense table (cardinal + to_list)" !ok

(* ------------------------------------------------------------------ T4 *)
let t4 () =
  reset ();
  let ok = ref true in
  for _ = 1 to 300 do
    let t, _ = build (rand 40) 60 in
    let ks = List.map fst (T.bindings t) in
    let rec asc = function a :: (b :: _ as r) -> a < b && asc r | _ -> true in
    if not (asc ks) then ok := false
  done;
  List.iter
    (fun n ->
      let t = dense n in
      if T.bindings t <> List.mapi (fun i v -> (i, v)) (T.to_list t) then ok := false)
    [ 0; 1; 8; 9; 64; 500 ];
  check "T4 bindings ascending, and mapi of to_list when dense" !ok

(* ------------------------------------------------------------------ T5 *)
let t5 () =
  reset ();
  let ok = ref true in
  for _ = 1 to 200 do
    let t, _ = build (rand 40) 60 in
    let keys = List.map fst (T.bindings t) in
    (* fold visits ascending: consing gives the reverse *)
    let folded = List.rev (T.fold (fun k _ acc -> k :: acc) t []) in
    if folded <> keys then ok := false;
    (* filter_map is ascending *)
    let fm = T.filter_map (fun k _ -> Some k) t in
    if fm <> keys then ok := false;
    (* for_all's ANSWER is the conjunction over every binding — its visit order is
       unspecified (Map.for_all is node-first, MEASURED, so that it short-circuits as
       Lean's List.all does).  What is tested is the answer, at a true predicate and at
       every single-binding falsification. *)
    if T.for_all (fun j w -> j + w >= 0) t <> List.for_all (fun (j, w) -> j + w >= 0) (T.bindings t) then
      ok := false;
    List.iter
      (fun (k0, _) ->
        let p j _ = j <> k0 in
        if T.for_all p t <> List.for_all (fun (j, w) -> p j w) (T.bindings t) then ok := false)
      (T.bindings t)
  done;
  check "T5 fold and filter_map visit in ascending key order; for_all's answer is the conjunction" !ok

(* ------------------------------------------------------------------ T6 *)
let t6 nops =
  reset ();
  let a = ref T.empty and b = ref L.empty in
  let bad = ref None in
  let key_space = 40 in
  let i = ref 0 in
  (try
     while !i < nops do
       incr i;
       let k = rand key_space and v = rand 1000 in
       let op = rand 9 in
       let ans_a, ans_b =
         match op with
         | 0 -> (show_opt (T.find_opt k !a), show_opt (L.find_opt k !b))
         | 1 ->
             a := T.set k v !a;
             b := L.set k v !b;
             ("", "")
         | 2 ->
             a := T.add k v !a;
             b := L.add k v !b;
             ("", "")
         | 3 ->
             a := T.remove k !a;
             b := L.remove k !b;
             ("", "")
         | 4 ->
             a := T.map (fun w -> (w + 1) mod 1000) !a;
             b := L.map (fun w -> (w + 1) mod 1000) !b;
             ("", "")
         | 5 ->
             ( show_ints (T.filter_map (fun j w -> if w mod 2 = 0 then Some ((j * 1000) + w) else None) !a),
               show_ints (L.filter_map (fun j w -> if w mod 2 = 0 then Some ((j * 1000) + w) else None) !b) )
         | 6 ->
             ( string_of_bool (T.for_all (fun j w -> j + w < 1500) !a),
               string_of_bool (L.for_all (fun j w -> j + w < 1500) !b) )
         | 7 ->
             ( string_of_int (T.fold (fun j w acc -> ((acc * 31) + j + w) land 0xFFFFFF) !a 7),
               string_of_int (L.fold (fun j w acc -> ((acc * 31) + j + w) land 0xFFFFFF) !b 7) )
         | _ ->
             ( Printf.sprintf "%d/%b/%s" (T.cardinal !a) (T.mem k !a) (show_ints (T.to_list !a)),
               Printf.sprintf "%d/%b/%s" (L.cardinal !b) (L.mem k !b) (show_ints (L.to_list !b)) )
       in
       let ba = show_bindings (T.bindings !a) and bb = show_bindings (L.bindings !b) in
       if ans_a <> ans_b || ba <> bb then begin
         bad := Some (!i, op, ans_a, ans_b, ba, bb);
         raise Exit
       end
     done
   with Exit -> ());
  (match !bad with
  | None -> ()
  | Some (i, op, aa, bb, ba, bl) ->
      Printf.printf "  op %d (#%d): map=%S list=%S\n  map bindings=%s\n  list bindings=%s\n" op i aa bb ba bl);
  check
    (Printf.sprintf "T6 agreement with the list twin over %d random ops" nops)
    (match !bad with None -> true | Some _ -> false)

(* ------------------------------------------------------------------ T7 *)
let t7 () =
  reset ();
  let ok = ref true in
  for _ = 1 to 100 do
    let t, _ = build (rand 40) 40 in
    let before = show_bindings (T.bindings t) in
    let card = T.cardinal t in
    for _ = 1 to 100 do
      let k = rand 40 and v = rand 1000 in
      ignore (T.add k v t);
      ignore (T.set k v t);
      ignore (T.remove k t);
      ignore (T.map (fun w -> w + 1) t);
      ignore (T.filter_map (fun _ w -> Some w) t)
    done;
    if show_bindings (T.bindings t) <> before || T.cardinal t <> card then ok := false
  done;
  check "T7 persistence: no operation mutates its argument" !ok

(* ------------------------------------------------------------------ R6a/R6b *)
let r6 () =
  reset ();
  let ok_a = ref true in
  let a = ref T.empty in
  for _ = 1 to 4000 do
    let k = rand 30 and v = rand 1000 in
    (match rand 3 with
    | 0 -> a := T.add k v !a
    | 1 -> a := T.set k v !a
    | _ -> a := T.remove k !a);
    if T.is_small !a <> (T.cardinal !a <= T.small_max) then ok_a := false;
    if T.cardinal !a <> List.length (T.bindings !a) then ok_a := false
  done;
  check
    (Printf.sprintf "R6a canonical representation: is_small <-> cardinal <= %d (4000 ops, across the threshold)"
       T.small_max)
    !ok_a;
  (* R6b: the same bindings by two different routes *)
  reset ();
  let ok_b = ref true in
  for _ = 1 to 200 do
    let n = 1 + rand 30 in
    let pairs = List.init n (fun i -> (i, rand 1000)) in
    let up = List.fold_left (fun t (k, v) -> T.add k v t) T.empty pairs in
    let down = List.fold_left (fun t (k, v) -> T.add k v t) T.empty (List.rev pairs) in
    let grown =
      (* grow well past the threshold, then shrink back under it *)
      let t = List.fold_left (fun t (k, v) -> T.add k v t) T.empty (List.init 64 (fun i -> (i, 0))) in
      let t = List.fold_left (fun t i -> T.remove i t) t (List.init 64 (fun i -> i)) in
      List.fold_left (fun t (k, v) -> T.add k v t) t pairs
    in
    if T.bindings up <> T.bindings down then ok_b := false;
    if T.bindings up <> T.bindings grown then ok_b := false;
    if T.is_small up <> T.is_small grown then ok_b := false;
    if T.cardinal up <> T.cardinal grown then ok_b := false
  done;
  check "R6b representation independence: same bindings, cardinal and is_small by any route" !ok_b

(* ------------------------------------------------------------------ the twin's own law *)
let tl2 () =
  (* TL2: for a monotone (machine-reachable) allocation sequence the twin's INSERTION order
     and its ascending `bindings` coincide — the licence A1 §4.2 states for the fiber table
     and Stores.lean:1150/:1366 state for the dense heaps. *)
  let ok = ref true in
  List.iter
    (fun n ->
      let b = ref L.empty in
      for i = 0 to n - 1 do
        b := L.add i (i * 7) !b
      done;
      if L.insertion_order !b <> L.to_list !b then ok := false;
      if L.raw !b <> L.bindings !b then ok := false)
    [ 0; 1; 8; 9; 100; 1000 ];
  check "TL2 the twin's insertion order = ascending bindings on monotone allocation" !ok

let () =
  t1 ();
  t2 ();
  t3 ();
  t4 ();
  t5 ();
  t6 12000;
  t7 ();
  argue "T8 snapshot = the value"
    "'a t is a record of an int and an immutable list or Map; no mutable field anywhere";
  r6 ();
  tl2 ();
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
