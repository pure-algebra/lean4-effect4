(* prop_store.ml — the property tests of E4_store (lane C, docs/research/
   2026-09-08-engine-a1-state.md §4.4 ST1-ST8).

   Every law of e4_store.mli is one named PASS/FAIL line, and the right-hand side of every
   law is the LEAN LIST OPERATION, written out at the top of this file from
   src/Effect4/Machine/Stores.lean.  That is what "exactness" means here: the carrier is not
   compared with a plausible OCaml equivalent, it is compared with Lean's own definition.

   Exit code 0 iff every line passed. *)

open Effect4_engine
module S = E4_store
module T = E4_table

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let argue name why = Printf.printf "PASS %s [by construction: %s]\n" name why

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

(* ------------------------------------------------------------- Lean, written out.

   List.get?      xs[i]?                              — refPeek (Stores.lean:1116),
                                                        DeferredStore.cellAt (:1369-1370)
   List.set       xs.set i v, a NO-OP when i is out of range (Lean core; Stores.lean:1120
                  refPoke, :1374 setCell)
   xs ++ [v]      refMake (:1150), DeferredStore.make (:1366), ScopeStore.make (:1576)
   List.find?     ScopeStore.entryAt (:1568), by the entry's own `key` field
   replace-by-key ScopeStore.setEntry (:1572): `entries.map (fun e => if e.key = k then v
                  else e)`, a NO-OP when no entry matches *)

(* `List.nth_opt` RAISES Invalid_argument on a negative index; Lean's `xs[i]?` is total
   because a `Nat` index cannot be negative.  The guard is the difference, not a repair. *)
let lean_get (xs : 'a list) (i : int) : 'a option = if i < 0 then None else List.nth_opt xs i

let lean_set (xs : 'a list) (i : int) (v : 'a) : 'a list =
  if i < 0 || i >= List.length xs then xs else List.mapi (fun j x -> if j = i then v else x) xs

let lean_append (xs : 'a list) (v : 'a) : 'a list = xs @ [ v ]

let lean_find (es : (int * 'a) list) (k : int) : 'a option =
  match List.find_opt (fun (j, _) -> j = k) es with Some (_, v) -> Some v | None -> None

let lean_replace (es : (int * 'a) list) (k : int) (v : 'a) : (int * 'a) list =
  List.map (fun (j, w) -> if j = k then (j, v) else (j, w)) es

(* ------------------------------------------------------------ dense heaps: ST1-ST4 *)

let dense_pair n =
  let h = ref S.empty and l = ref [] in
  for i = 0 to n - 1 do
    let v = (i * 37) mod 991 in
    let k, h' = S.grow v !h in
    if k <> i then failwith "grow allocated the wrong key";
    h := h';
    l := lean_append !l v
  done;
  (!h, !l)

let st1 () =
  let ok = ref true in
  List.iter
    (fun n ->
      let h, l = dense_pair n in
      for i = -3 to n + 3 do
        if S.peek i h <> lean_get l i then ok := false
      done)
    [ 0; 1; 8; 9; 64; 500 ];
  check "ST1 peek is refPeek: peek k h = heap[k]? on a dense heap" !ok

let st2 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
      let h, l = dense_pair n in
      for _ = 1 to 200 do
        let i = rand (n + 6) - 3 and v = rand 991 in
        let h' = S.poke i v h and l' = lean_set l i v in
        if S.to_list h' <> l' then ok := false;
        if S.cardinal h' <> List.length l' then ok := false;
        (* out of range: no insertion, and physically the same heap *)
        if (i < 0 || i >= n) && not (h' == h) then ok := false
      done)
    [ 0; 1; 8; 9; 64; 200 ];
  check "ST2 poke is refPoke and is a NO-OP out of range (no insertion, same heap)" !ok

let st3 () =
  let ok = ref true in
  List.iter
    (fun n ->
      let h, l = dense_pair n in
      let k, h' = S.grow 4242 h in
      if k <> List.length l then ok := false;
      if S.to_list h' <> lean_append l 4242 then ok := false;
      if S.cardinal h' <> n + 1 then ok := false)
    [ 0; 1; 7; 8; 9; 64; 500 ];
  check "ST3 grow is refMake: fresh key = heap.length, to_list = heap ++ [v]" !ok

let st4 () =
  reset ();
  let ok = ref true in
  let d = ref S.empty and l = ref [] in
  for i = 0 to 199 do
    let k, d' = S.make_cell i !d in
    if k <> i then ok := false;
    d := d';
    l := lean_append !l i;
    (* cellAt everywhere, including out of range *)
    for j = -2 to i + 2 do
      if S.cell_at j !d <> lean_get !l j then ok := false
    done;
    (* setCell, in and out of range *)
    let j = rand (i + 5) - 2 and v = rand 1000 in
    let d2 = S.set_cell j v !d and l2 = lean_set !l j v in
    if S.to_list d2 <> l2 then ok := false
  done;
  check "ST4 cell_at / set_cell / make_cell are DeferredStore.cellAt / setCell / make" !ok

(* ---------------------------------------------------- sparse scopes: ST5, ST6b, ST7 *)

let st5_st6 () =
  reset ();
  let ok5 = ref true and ok6 = ref true in
  let sc = ref S.empty and l = ref [] in
  (* The supply is Stores.nextName: keys jump, they are never `cardinal`. *)
  let next_name = ref 3 in
  for _ = 1 to 400 do
    (match rand 3 with
    | 0 ->
        (* scopeMake / scopeFork: a supply-drawn key, appended *)
        let k = !next_name in
        next_name := !next_name + 1 + rand 3;
        sc := S.add_entry k (k * 10) !sc;
        l := lean_append !l (k, k * 10);
        (* ST6: the fresh key is NOT the cardinal *)
        if k = S.cardinal !sc - 1 && k > 4 then ok6 := false
    | 1 ->
        let k = rand (!next_name + 3) in
        let v = rand 1000 in
        let a = S.set_entry k v !sc and b = lean_replace !l k v in
        sc := a;
        l := b
    | _ -> ());
    let k = rand (!next_name + 5) in
    if S.entry_at k !sc <> lean_find !l k then ok5 := false;
    if S.bindings !sc <> List.sort (fun (a, _) (b, _) -> compare (a : int) b) !l then ok5 := false
  done;
  check "ST5 entry_at is ScopeStore.entryAt (find? by key); set_entry is the replace-by-key map" !ok5;
  check "ST6b scope keys are supply-drawn: the fresh key is never the cardinal" !ok6

(* -------------------------------------------------------------------------- ST7 *)

let show_list l = String.concat "," (List.map string_of_int l)

let st7 nops =
  reset ();
  let h = ref S.empty and l = ref [] in
  let bad = ref None in
  let i = ref 0 in
  (try
     while !i < nops do
       incr i;
       let v = rand 991 in
       let k = rand 40 - 4 in
       (match rand 4 with
       | 0 ->
           let _, h' = S.grow v !h in
           h := h';
           l := lean_append !l v
       | 1 | 2 ->
           h := S.poke k v !h;
           l := lean_set !l k v
       | _ ->
           let a = show_list (match S.peek k !h with None -> [] | Some x -> [ x ]) in
           let b = show_list (match lean_get !l k with None -> [] | Some x -> [ x ]) in
           if a <> b then begin
             bad := Some (!i, "peek", a, b);
             raise Exit
           end);
       if S.to_list !h <> !l then begin
         bad := Some (!i, "heap", show_list (S.to_list !h), show_list !l);
         raise Exit
       end
     done
   with Exit -> ());
  (match !bad with
  | None -> ()
  | Some (n, what, a, b) -> Printf.printf "  #%d %s: map=%s lean=%s\n" n what a b);
  check
    (Printf.sprintf "ST7 agreement with Lean's list operations over %d random heap ops" nops)
    (match !bad with None -> true | Some _ -> false)

let () =
  st1 ();
  st2 ();
  st3 ();
  st4 ();
  st5_st6 ();
  st7 20000;
  argue "ST6 the scope store is sparse: no allocate-by-cardinal is offered for scopes"
    "e4_store.mli exposes add_entry (supplied key) for scopes and grow/make_cell only for the dense families";
  argue "ST8 KeysBelow is preserved"
    "the carrier neither mints nor drops keys; every key it holds was supplied by Stores.nextName";
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
