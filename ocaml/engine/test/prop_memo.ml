(* prop_memo.ml — the property tests of E4_memo (lane C, docs/research/
   2026-09-08-engine-a1-state.md §4.6 MM1-MM7, and risk R5).

   MM2 is the reason this file exists.  Lean's `insertEntry` APPENDS a duplicate
   (src/Effect4/Machine/Stores.lean:876-880) and `find?` answers the FIRST (:867), while
   `updateEntry` (:873) and `deleteEntry` (:886) touch ALL matching entries.  The map carrier
   keeps the existing binding instead of appending — a different VALUE, the same
   OBSERVATIONS.  The twin e4_memo_list.ml reproduces Lean's list, duplicates included, and
   the differential below asserts the observations agree at EVERY key after EVERY operation.

   The LAYERS module type below is lane G's text (A1 §1.5), verbatim: if either carrier
   drifts from the contract, this file stops compiling.

   Exit code 0 iff every line passed. *)

open Effect4_engine

[@@@warning "-32"]
(* A module type used only for an ascription has, by definition, no used values. *)

module type LAYERS = sig
  type 'a t

  val empty : 'a t
  val find_opt : int list -> 'a t -> 'a option
  val insert : int list -> 'a -> 'a t -> 'a t
  val update : int list -> ('a -> 'a) -> 'a t -> 'a t
  val delete : int list -> 'a t -> 'a t
  val bindings : 'a t -> (int list * 'a) list
end

module _ : LAYERS = E4_memo
module _ : LAYERS = E4_memo_list
[@@@warning "+32"]


module M = E4_memo
module L = E4_memo_list

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

(* The universe of layer paths: `LayerId := List Nat` (Stores.lean:176) — the layer's path
   from the root program.  Short, overlapping, with prefixes, so `compare_path`'s
   prefix-first arm is exercised. *)
let universe =
  [ []; [ 0 ]; [ 1 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ]; [ 0; 0; 0 ]; [ 0; 0; 1 ]; [ 2 ]; [ 1; 0; 3 ] ]

let show_path p = "[" ^ String.concat ";" (List.map string_of_int p) ^ "]"
let show_opt = function None -> "-" | Some v -> string_of_int v

let show_bindings b =
  String.concat "," (List.map (fun (p, v) -> show_path p ^ "=" ^ string_of_int v) b)

(* ------------------------------------------------------------------------ MM1 *)
let mm1 () =
  reset ();
  let ok = ref true in
  for _ = 1 to 200 do
    let m = ref M.empty and l = ref L.empty in
    for _ = 1 to 20 do
      let p = List.nth universe (rand (List.length universe)) and v = rand 1000 in
      m := M.insert p v !m;
      l := L.insert p v !l
    done;
    List.iter (fun p -> if M.find_opt p !m <> L.find_opt p !l then ok := false) universe
  done;
  check "MM1 find_opt is entryAt: the FIRST binding under the path" !ok

(* ------------------------------------------------------------------------ MM2 *)
let mm2 () =
  let ok = ref true in
  let p = [ 0; 1 ] in
  let m = M.insert p 1 M.empty and l = L.insert p 1 L.empty in
  let m = M.insert p 2 m and l = L.insert p 2 l in
  let m = M.insert p 3 m and l = L.insert p 3 l in
  (* the VALUES differ: the twin holds three entries, the map one *)
  if L.raw_length l <> 3 then ok := false;
  if M.cardinal m <> 1 then ok := false;
  (* the OBSERVATIONS agree: find_opt is the first insert on both sides *)
  if M.find_opt p m <> Some 1 then ok := false;
  if L.find_opt p l <> Some 1 then ok := false;
  (* an update touches all duplicates on the twin; the first is still what is observed *)
  let m2 = M.update p (fun v -> v + 100) m and l2 = L.update p (fun v -> v + 100) l in
  if M.find_opt p m2 <> L.find_opt p l2 then ok := false;
  if M.find_opt p m2 <> Some 101 then ok := false;
  (* a delete removes ALL duplicates, so the two carriers are equal again *)
  let m3 = M.delete p m2 and l3 = L.delete p l2 in
  if L.raw_length l3 <> 0 then ok := false;
  if M.find_opt p m3 <> None || L.find_opt p l3 <> None then ok := false;
  (* and an insert after the delete binds afresh on both sides *)
  let m4 = M.insert p 9 m3 and l4 = L.insert p 9 l3 in
  if M.find_opt p m4 <> Some 9 || L.find_opt p l4 <> Some 9 then ok := false;
  (* insert over a bound path returns the table physically *)
  if not (M.insert p 42 m4 == m4) then ok := false;
  check "MM2 insert KEEPS the existing binding; the twin appends and observes the same" !ok

(* ------------------------------------------------------------------- MM3, MM4 *)
let mm3_mm4 () =
  let ok3 = ref true and ok4 = ref true in
  let m = M.insert [ 0 ] 5 (M.insert [ 1 ] 6 M.empty) in
  let l = L.insert [ 0 ] 5 (L.insert [ 1 ] 6 L.empty) in
  let m' = M.update [ 9; 9 ] (fun v -> v + 1) m and l' = L.update [ 9; 9 ] (fun v -> v + 1) l in
  if M.bindings m' <> M.bindings m then ok3 := false;
  if L.bindings l' <> L.bindings l then ok3 := false;
  if not (M.update [ 9; 9 ] (fun v -> v) m == m) then ok3 := false;
  (* delete removes every matching entry, including the duplicates Lean appended *)
  let ld = L.insert [ 0 ] 7 (L.insert [ 0 ] 8 l) in
  if L.raw_length ld <> 4 then ok4 := false;
  let ld = L.delete [ 0 ] ld in
  if L.raw_length ld <> 1 then ok4 := false;
  if L.find_opt [ 0 ] ld <> None then ok4 := false;
  if M.bindings (M.delete [ 0 ] m) <> L.bindings ld then ok4 := false;
  check "MM3 update is a no-op on an absent key (physically the same table)" !ok3;
  check "MM4 delete removes EVERY matching entry" !ok4

(* ------------------------------------------------------------------------ MM5 *)
type mmap = { mid : int; parent : int option; entries : int M.t }
type lmap = { lid : int; lparent : int option; lentries : int L.t }

let mm5 () =
  let ok = ref true in
  (* a well-formed chain: 0 <- 1 <- 2, the entry only in the root *)
  let world =
    [ { mid = 0; parent = None; entries = M.insert [ 7 ] 70 M.empty };
      { mid = 1; parent = Some 0; entries = M.empty };
      { mid = 2; parent = Some 1; entries = M.empty } ]
  in
  let lk w layer start =
    M.lookup ~parent:(fun m -> m.parent) ~id:(fun m -> m.mid) ~entries:(fun m -> m.entries) w layer start
  in
  if lk world [ 7 ] 2 <> Some (0, 70) then ok := false;
  if lk world [ 7 ] 0 <> Some (0, 70) then ok := false;
  if lk world [ 8 ] 2 <> None then ok := false;
  if lk world [ 7 ] 99 <> None then ok := false;
  (* the nearer map wins over the parent's (`own map first`, Stores.lean:893) *)
  let shadow =
    [ { mid = 0; parent = None; entries = M.insert [ 7 ] 70 M.empty };
      { mid = 1; parent = Some 0; entries = M.insert [ 7 ] 71 M.empty } ]
  in
  if lk shadow [ 7 ] 1 <> Some (1, 71) then ok := false;
  (* a FORGED cyclic chain (Stores.lean:906-910): the fuel is what makes lookup total *)
  let cyclic =
    [ { mid = 0; parent = Some 1; entries = M.empty }; { mid = 1; parent = Some 0; entries = M.empty } ]
  in
  if lk cyclic [ 7 ] 0 <> None then ok := false;
  (* the twin agrees, with the same fuel *)
  let lworld =
    [ { lid = 0; lparent = None; lentries = L.insert [ 7 ] 70 L.empty };
      { lid = 1; lparent = Some 0; lentries = L.empty };
      { lid = 2; lparent = Some 1; lentries = L.empty } ]
  in
  let lk' w layer start =
    L.lookup ~parent:(fun m -> m.lparent) ~id:(fun m -> m.lid) ~entries:(fun m -> m.lentries) w layer start
  in
  if lk' lworld [ 7 ] 2 <> Some (0, 70) then ok := false;
  if lk' lworld [ 8 ] 2 <> None then ok := false;
  check "MM5 lookup is MemoWorld.get: own map first, parent chain, fuel = |world| + 1 (a forged cycle answers None)" !ok

(* ------------------------------------------------------------------ MM6a/MM6b *)
let mm6 () =
  let ok_a = ref true and ok_b = ref true in
  (* MM6a: bindings is ascending lexicographic on the path, prefix first *)
  let m = List.fold_left (fun t p -> M.insert p (List.length p) t) M.empty (List.rev universe) in
  let ks = List.map fst (M.bindings m) in
  let rec asc = function
    | a :: (b :: _ as r) -> M.compare_path a b < 0 && asc r
    | _ -> true
  in
  if not (asc ks) then ok_a := false;
  if ks <> List.sort M.compare_path universe then ok_a := false;
  (* MM6b: the twin's bindings — insertion order deduped and sorted — is the same list *)
  let l = List.fold_left (fun t p -> L.insert p (List.length p) t) L.empty (List.rev universe) in
  if M.bindings m <> L.bindings l then ok_b := false;
  check "MM6a bindings is ascending by path (lexicographic, prefix first), NOT insertion order" !ok_a;
  check "MM6b the twin's observable bindings is the same list" !ok_b

(* ------------------------------------------------------------------------ MM7 *)
let mm7 nops =
  reset ();
  let m = ref M.empty and l = ref L.empty in
  let bad = ref None in
  let i = ref 0 in
  let u = Array.of_list universe in
  (try
     while !i < nops do
       incr i;
       let p = u.(rand (Array.length u)) and v = rand 1000 in
       (match rand 4 with
       | 0 | 1 ->
           m := M.insert p v !m;
           l := L.insert p v !l
       | 2 ->
           m := M.update p (fun w -> (w + v) mod 1000) !m;
           l := L.update p (fun w -> (w + v) mod 1000) !l
       | _ ->
           m := M.delete p !m;
           l := L.delete p !l);
       (* every observation the machine can make, at every path *)
       let am = String.concat "|" (List.map (fun q -> show_opt (M.find_opt q !m)) universe) in
       let al = String.concat "|" (List.map (fun q -> show_opt (L.find_opt q !l)) universe) in
       let bm = show_bindings (M.bindings !m) and bl = show_bindings (L.bindings !l) in
       if am <> al || bm <> bl then begin
         bad := Some (!i, am, al, bm, bl);
         raise Exit
       end
     done
   with Exit -> ());
  (match !bad with
  | None -> ()
  | Some (n, am, al, bm, bl) ->
      Printf.printf "  #%d find map=%s list=%s\n  bindings map=%s\n  bindings list=%s\n" n am al bm bl);
  check
    (Printf.sprintf "MM7 agreement with the Lean list at every path over %d random ops" nops)
    (match !bad with None -> true | Some _ -> false)

let () =
  mm1 ();
  mm2 ();
  mm3_mm4 ();
  mm5 ();
  mm6 ();
  mm7 12000;
  argue "MM6 the order difference is unobservable"
    "entryAt, updateEntry and deleteEntry are all BY KEY; no run-path reader iterates entries (Stores.lean:866-886)";
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
