(* prop_fibers.ml — the property tests of E4_fibers (lane C, docs/research/
   2026-09-08-engine-a1-state.md §4.2 FB1-FB9).

   Every law of e4_fibers.mli is one named PASS/FAIL line.  The twin is the LEAN LIST
   ITSELF: `fiber?`, `update`, `spawn`'s append, `finished`, `completedExits` and
   `dropObservers` are written out at the top of this file from
   src/Effect4/Machine/Fibers.lean, and the carrier is compared against them.

   FB1 (agreement with `api_gen`'s `m.fibers` over the corpus) cannot run in this lane — the
   substituted engine does not exist yet — and is owed to lane X.  FB8, the twin
   differential over random operation sequences, stands in for it here.

   Exit code 0 iff every line passed. *)

open Effect4_engine
module F = E4_fibers

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let argue name why = Printf.printf "PASS %s [%s]\n" name why

(* Not a PASS and not a FAIL: a law this lane cannot reach, named so it is not forgotten. *)
let owed name why = Printf.printf "OWED %s [%s]\n" name why

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

(* ------------------------------------------------------- the smallest fiber record.
   The generated `run_fiber` has 15 fields; the three the carrier's laws touch are the id
   (Fibers.lean:573), the exit (:609, :1543) and the observers (:1256, :1344). *)
type fiber = { id : int; exit_ : int option; observers : int list }

let id_of f = f.id
let exit_of f = f.exit_

(* ------------------------------------------------------------- Lean, written out *)

(* RunMachine.fiber? (Fibers.lean:573-575) *)
let lean_fiber (fs : fiber list) (id : int) : fiber option = List.find_opt (fun f -> f.id = id) fs

(* RunMachine.update (Fibers.lean:577-579) *)
let lean_update (fs : fiber list) (f : fiber) : fiber list =
  List.map (fun g -> if g.id = f.id then f else g) fs

(* spawn (Fibers.lean:867, :877): `m.fibers ++ [child]` at `⟨m.nextId⟩` *)
let lean_spawn (fs : fiber list) (child : fiber) : fiber list = fs @ [ child ]

(* RunMachine.finished (Fibers.lean:608-609) *)
let lean_finished (fs : fiber list) : bool =
  List.for_all (fun f -> match f.exit_ with Some _ -> true | None -> false) fs

(* RunMachine.completedExits (Fibers.lean:1541-1543) *)
let lean_completed (fs : fiber list) : (int * int) list =
  List.filter_map (fun f -> match f.exit_ with Some e -> Some (f.id, e) | None -> None) fs

(* dropObservers (Fibers.lean:1254-1260, :1344-1348): a key-preserving `fibers.map` whose
   body filters each fiber's observer list by token *)
let drop_step (token : int) (g : fiber) : fiber =
  { g with observers = List.filter (fun t -> t <> token) g.observers }

let lean_drop (fs : fiber list) (token : int) : fiber list = List.map (drop_step token) fs

(* --------------------------------------------------------------- a random machine *)

let mk_fiber i =
  { id = i; exit_ = (if rand 3 = 0 then Some (i * 11) else None); observers = List.init (rand 4) (fun j -> (i + j) mod 7) }

let build n =
  let t = ref F.empty and l = ref [] in
  for i = 0 to n - 1 do
    let f = mk_fiber i in
    t := F.append i f !t;
    l := lean_spawn !l f
  done;
  (!t, !l)

(* ------------------------------------------------------------------------ FB2 *)
let fb2 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
      let t, l = build n in
      for id = -2 to n + 2 do
        if F.find id t <> lean_fiber l id then ok := false;
        if F.find_opt' t id <> lean_fiber l id then ok := false
      done)
    [ 0; 1; 8; 9; 64; 300 ];
  check "FB2 find (and find_opt') is RunMachine.fiber?" !ok

(* ------------------------------------------------------------------- FB3, FB4 *)
let fb3_fb4 () =
  reset ();
  let ok3 = ref true and ok4 = ref true in
  List.iter
    (fun n ->
      let t, l = build n in
      for id = 0 to n - 1 do
        let f = { id; exit_ = Some 777; observers = [ 1; 2 ] } in
        if F.to_list (F.update ~id_of f t) <> lean_update l f then ok3 := false;
        if F.to_list (F.update_at id f t) <> lean_update l f then ok3 := false
      done;
      List.iter
        (fun id ->
          let f = { id; exit_ = Some 1; observers = [] } in
          let t' = F.update ~id_of f t in
          if F.to_list t' <> lean_update l f then ok4 := false;
          if F.cardinal t' <> n then ok4 := false;
          if not (t' == t) then ok4 := false)
        [ -1; n; n + 5; 100000 ])
    [ 0; 1; 8; 9; 64; 200 ];
  check "FB3 update is RunMachine.update (replace by id, order preserved)" !ok3;
  check "FB4 update on an unknown id is a no-op (physically the same table)" !ok4

(* ------------------------------------------------------------------------ FB5 *)
let fb5 () =
  reset ();
  let ok = ref true in
  let t = ref F.empty and l = ref [] in
  for i = 0 to 499 do
    let f = mk_fiber i in
    (* the monotone-allocation licence: the fresh id IS the cardinal *)
    if F.cardinal !t <> i then ok := false;
    t := F.append i f !t;
    l := lean_spawn !l f;
    if F.to_list !t <> !l then ok := false
  done;
  check "FB5 append is spawn's `fibers ++ [child]`, and the fresh id is the cardinal" !ok

(* ------------------------------------------------------------------------ FB6 *)
let fb6 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
      let t, l = build n in
      if F.finished ~exit_of t <> lean_finished l then ok := false;
      if F.completed_exits ~id_of ~exit_of t <> lean_completed l then ok := false;
      (* and once every fiber has exited *)
      let t' = F.map (fun f -> { f with exit_ = Some f.id }) t in
      let l' = List.map (fun f -> { f with exit_ = Some f.id }) l in
      if F.finished ~exit_of t' <> lean_finished l' then ok := false;
      if not (F.finished ~exit_of t') then ok := false;
      if F.completed_exits ~id_of ~exit_of t' <> lean_completed l' then ok := false)
    [ 0; 1; 8; 9; 64; 300 ];
  check "FB6 finished is `fibers.all (·.exit.isSome)`; completed_exits is the ascending filterMap" !ok

(* ------------------------------------------------------------------------ FB7 *)
let fb7 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
      let t, l = build n in
      for token = 0 to 7 do
        let t' = F.drop_observers (drop_step token) t in
        if F.to_list t' <> lean_drop l token then ok := false;
        if List.map fst (F.bindings t') <> List.map fst (F.bindings t) then ok := false
      done)
    [ 0; 1; 8; 9; 64; 200 ];
  check "FB7 drop_observers is the id-preserving bulk map" !ok

(* ------------------------------------------------------------------------ FB8 *)
let show_fibers fs =
  String.concat ";"
    (List.map
       (fun f ->
         Printf.sprintf "%d/%s/[%s]" f.id
           (match f.exit_ with None -> "-" | Some e -> string_of_int e)
           (String.concat "," (List.map string_of_int f.observers)))
       fs)

let fb8 nops =
  reset ();
  let t = ref F.empty and l = ref [] in
  let bad = ref None in
  let i = ref 0 in
  (try
     while !i < nops do
       incr i;
       let n = List.length !l in
       let a, b =
         match rand 6 with
         | 0 ->
             let f = mk_fiber n in
             t := F.append n f !t;
             l := lean_spawn !l f;
             ("", "")
         | 1 ->
             let id = rand (n + 3) - 1 in
             let f = { id; exit_ = (if rand 2 = 0 then Some (rand 100) else None); observers = List.init (rand 3) (fun j -> j) } in
             t := F.update ~id_of f !t;
             l := lean_update !l f;
             ("", "")
         | 2 ->
             let token = rand 7 in
             t := F.drop_observers (drop_step token) !t;
             l := lean_drop !l token;
             ("", "")
         | 3 ->
             let id = rand (n + 3) - 1 in
             ( (match F.find id !t with None -> "-" | Some f -> show_fibers [ f ]),
               match lean_fiber !l id with None -> "-" | Some f -> show_fibers [ f ] )
         | 4 -> (string_of_bool (F.finished ~exit_of !t), string_of_bool (lean_finished !l))
         | _ ->
             ( String.concat ";" (List.map (fun (a, b) -> Printf.sprintf "%d=%d" a b) (F.completed_exits ~id_of ~exit_of !t)),
               String.concat ";" (List.map (fun (a, b) -> Printf.sprintf "%d=%d" a b) (lean_completed !l)) )
       in
       let sa = show_fibers (F.to_list !t) and sb = show_fibers !l in
       if a <> b || sa <> sb then begin
         bad := Some (!i, a, b, sa, sb);
         raise Exit
       end
     done
   with Exit -> ());
  (match !bad with
  | None -> ()
  | Some (n, a, b, sa, sb) ->
      Printf.printf "  #%d answer map=%S lean=%S\n  map   =%s\n  lean  =%s\n" n a b sa sb);
  check
    (Printf.sprintf "FB8 agreement with the Lean list over %d random fiber-table ops" nops)
    (match !bad with None -> true | Some _ -> false)

let () =
  fb2 ();
  fb3_fb4 ();
  fb5 ();
  fb6 ();
  fb7 ();
  fb8 12000;
  owed "FB1 to_list = api_gen's m.fibers over the corpus"
    "lane X (A1 §6.3 D1/D2); the substituted engine does not exist yet, FB8 stands in";
  argue "FB9 to_list is a READ, 4-5x a list walk"
    "argued; the number is in test/bench_carriers.ml (case C6)";
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
