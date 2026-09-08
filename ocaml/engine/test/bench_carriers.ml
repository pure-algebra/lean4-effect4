(* bench_carriers.ml — per-carrier isolation for lane C's carriers (docs/research/
   2026-09-08-engine-a1-state.md §6.2, cases C1-C6, plus the memo and the small-size
   crossover of §7 R6).

   What it measures, and how, so the numbers can be reproduced or refuted:
     * `list_ms` is the LEAN carrier as the LCNF backend emits it — `List.set`, `List.get?`,
       `find? + map`, `xs ++ [v]` — written out in this file.
       `map_ms` is lane C's carrier.  The ratio is list/map: > 1 means the carrier wins.
     * ops = 10 000 per cell, except C6, whose unit is a READ of the whole table and which
       therefore runs ops/100 = 100 reads (that is A1's "100 reads per 10 000 steps").
     * C1 poke, C2 peek, C3 fiber and C6 read hold the carrier at a FIXED size n; C4 emit
       and C5 grow ACCUMULATE, because emitting and allocating are what make the Lean
       carrier quadratic and the accumulation is the effect being measured.
     * best of `reps` runs (default 5), Unix.gettimeofday, native code.
     * one fixed LCG for every index sequence, so two runs of this binary compare.

   It is an EXECUTABLE, not a test: `dune test` does not run it.  Build and run it with
     dune build engine && ./_build/default/engine/test/bench_carriers.exe [reps]
   Usage: bench_carriers [reps]  (default 5) *)

open Effect4_engine

let reps = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 5
let ops = 10_000
let sizes = [ 100; 1_000; 10_000 ]

(* ------------------------------------------------------------------ the LCG *)
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

(* --------------------------------------------------- Lean's carriers, written out *)

(* List.set (Lean core; refPoke Stores.lean:1119-1120, setCell :1374) *)
let rec list_set (xs : 'a list) (i : int) (v : 'a) : 'a list =
  match xs with [] -> [] | x :: r -> if i = 0 then v :: r else x :: list_set r (i - 1) v

(* xs[i]? (refPeek Stores.lean:1116) *)
let list_get (xs : 'a list) (i : int) : 'a option = List.nth_opt xs i

(* xs ++ [v] (refMake Stores.lean:1150, RunMachine.emit Fibers.lean:587, spawn :877) *)
let list_append_one (xs : 'a list) (v : 'a) : 'a list = xs @ [ v ]

type fiber = { id : int; w : int }

(* RunMachine.fiber? then RunMachine.update (Fibers.lean:573-579) *)
let list_fiber_touch (fs : fiber list) (id : int) : fiber list =
  match List.find_opt (fun f -> f.id = id) fs with
  | None -> fs
  | Some f ->
      let f' = { f with w = f.w + 1 } in
      List.map (fun g -> if g.id = f'.id then f' else g) fs

(* ------------------------------------------------------------------- timing *)

let time (f : unit -> unit) : float =
  let best = ref infinity in
  for _ = 1 to reps do
    let t0 = Unix.gettimeofday () in
    f ();
    let dt = (Unix.gettimeofday () -. t0) *. 1000.0 in
    if dt < !best then best := dt
  done;
  !best

let rows : (string * (int * float * float) list) list ref = ref []

let row name cells = rows := (name, cells) :: !rows

let cell n (lean : unit -> unit) (fast : unit -> unit) : int * float * float =
  reset ();
  let a = time lean in
  reset ();
  let b = time fast in
  (n, a, b)

(* --------------------------------------------------------------- the six cases *)

let build_list n = List.init n (fun i -> i)
let build_table n = List.fold_left (fun t i -> E4_table.add i i t) E4_table.empty (List.init n (fun i -> i))
let build_fibers_list n = List.init n (fun i -> { id = i; w = 0 })

let build_fibers_table n =
  List.fold_left (fun t i -> E4_fibers.append i { id = i; w = 0 } t) E4_fibers.empty (List.init n (fun i -> i))

let c1 n =
  let xs = build_list n and t = build_table n in
  cell n
    (fun () ->
      for _ = 1 to ops do
        ignore (list_set xs (rand n) 7)
      done)
    (fun () ->
      for _ = 1 to ops do
        ignore (E4_store.poke (rand n) 7 t)
      done)

let c2 n =
  let xs = build_list n and t = build_table n in
  cell n
    (fun () ->
      for _ = 1 to ops do
        ignore (list_get xs (rand n))
      done)
    (fun () ->
      for _ = 1 to ops do
        ignore (E4_store.peek (rand n) t)
      done)

let c3 n =
  let xs = build_fibers_list n and t = build_fibers_table n in
  cell n
    (fun () ->
      for _ = 1 to ops do
        ignore (list_fiber_touch xs (rand n))
      done)
    (fun () ->
      for _ = 1 to ops do
        let id = rand n in
        match E4_fibers.find id t with
        | None -> ()
        | Some f -> ignore (E4_fibers.update_at id { f with w = f.w + 1 } t)
      done)

(* C4 and C5 ACCUMULATE: the growth is the measurement. *)
let c4 n =
  let base_l = build_list n in
  let base_t = List.fold_left (fun t e -> E4_trace.emit [ e ] t) E4_trace.empty (build_list n) in
  cell n
    (fun () ->
      let acc = ref base_l in
      for i = 1 to ops do
        acc := list_append_one !acc i
      done;
      ignore (List.length !acc))
    (fun () ->
      let acc = ref base_t in
      for i = 1 to ops do
        acc := E4_trace.emit [ i ] !acc
      done;
      ignore (E4_trace.length !acc))

let c5 n =
  let base_l = build_list n and base_t = build_table n in
  cell n
    (fun () ->
      let acc = ref base_l in
      for i = 1 to ops do
        acc := list_append_one !acc i
      done;
      ignore (List.length !acc))
    (fun () ->
      let acc = ref base_t in
      for i = 1 to ops do
        let _, t' = E4_store.grow i !acc in
        acc := t'
      done;
      ignore (E4_table.cardinal !acc))

(* C6: the READ side — the honest cost of the ordering argument.  ops/100 whole-table
   reads, which is A1's "100 reads per 10 000 steps". *)
let c6 n =
  let reads = ops / 100 in
  let xs = build_list n and t = build_table n in
  cell n
    (fun () ->
      for _ = 1 to reads do
        ignore (List.fold_left ( + ) 0 xs)
      done)
    (fun () ->
      for _ = 1 to reads do
        ignore (List.fold_left (fun a (_, v) -> a + v) 0 (E4_table.bindings t))
      done)

(* --------------------------------------------------------------------- the memo *)

let path i = [ i / 10; i mod 10 ]

let build_memo n =
  List.fold_left (fun t i -> E4_memo.insert (path i) i t) E4_memo.empty (List.init n (fun i -> i))

let build_memo_list n =
  List.fold_left (fun t i -> E4_memo_list.insert (path i) i t) E4_memo_list.empty (List.init n (fun i -> i))

(* M1: insert, ACCUMULATING — Lean's `entries ++ [(layer, entry)]` (Stores.lean:880). *)
let m1 n =
  let base_l = build_memo_list n and base_m = build_memo n in
  cell n
    (fun () ->
      let acc = ref base_l in
      for i = 1 to ops / 10 do
        acc := E4_memo_list.insert (path (n + i)) i !acc
      done;
      ignore (E4_memo_list.raw_length !acc))
    (fun () ->
      let acc = ref base_m in
      for i = 1 to ops / 10 do
        acc := E4_memo.insert (path (n + i)) i !acc
      done;
      ignore (E4_memo.cardinal !acc))

(* M2: find, at a FIXED size — Lean's `entries.find? (·.1 = layer)` (Stores.lean:867). *)
let m2 n =
  let l = build_memo_list n and m = build_memo n in
  cell n
    (fun () ->
      for _ = 1 to ops do
        ignore (E4_memo_list.find_opt (path (rand n)) l)
      done)
    (fun () ->
      for _ = 1 to ops do
        ignore (E4_memo.find_opt (path (rand n)) m)
      done)

(* ------------------------------------------- the small-size crossover (R6, AC9).
   A sorted assoc list against Map.Make(Int) at small cardinals: where the two lines cross
   is what `E4_table.small_max` must be. *)

module IMap = Map.Make (Int)

let rec assoc_find k = function
  | [] -> None
  | (k', v) :: r -> if k' = k then Some v else if k' > k then None else assoc_find k r

let rec assoc_add k v = function
  | [] -> [ (k, v) ]
  | (k', v') :: r as l ->
      if k' = k then (k, v) :: r
      else if k' > k then (k, v) :: l
      else (k', v') :: assoc_add k v r

(* Replace-if-present over a sorted assoc list: E4_table's `set` on the Small arm. *)
let rec assoc_set k v = function
  | [] -> []
  | (k', v') :: r -> if k' = k then (k, v) :: r else (k', v') :: assoc_set k v r

let crossover () =
  Printf.printf "\n-- the small-size crossover (R6/AC9): a sorted assoc list vs Map.Make(Int),\n";
  Printf.printf "   per operation, %d ops per cell, best of %d.  E4_table.small_max = %d.\n" ops reps
    E4_table.small_max;
  Printf.printf "   ratio = assoc_ms / map_ms; > 1 means the Map wins at that size.\n\n";
  Printf.printf "  %5s  %8s %8s %6s  %8s %8s %6s  %8s %8s %6s\n" "n" "find_a" "find_m" "r"
    "set_a" "set_m" "r" "add_a" "add_m" "r";
  List.iter
    (fun n ->
      let l = List.init n (fun i -> (i, i)) in
      let m = List.fold_left (fun m (k, v) -> IMap.add k v m) IMap.empty l in
      let cellf lean fast =
        reset ();
        let a = time lean in
        reset ();
        let b = time fast in
        (a, b)
      in
      let fa, fm =
        cellf
          (fun () -> for _ = 1 to ops do ignore (assoc_find (rand n) l) done)
          (fun () -> for _ = 1 to ops do ignore (IMap.find_opt (rand n) m) done)
      in
      let sa, sm =
        cellf
          (fun () -> for _ = 1 to ops do ignore (assoc_set (rand n) 1 l) done)
          (fun () -> for _ = 1 to ops do let k = rand n in ignore (if IMap.mem k m then IMap.add k 1 m else m) done)
      in
      let aa, am =
        cellf
          (fun () -> for _ = 1 to ops do ignore (assoc_add (rand n) 1 l) done)
          (fun () -> for _ = 1 to ops do ignore (IMap.add (rand n) 1 m) done)
      in
      Printf.printf "  %5d  %8.3f %8.3f %6.2f  %8.3f %8.3f %6.2f  %8.3f %8.3f %6.2f\n" n fa fm
        (fa /. fm) sa sm (sa /. sm) aa am (aa /. am))
    [ 1; 2; 3; 4; 6; 8; 12; 16; 32; 64 ]

(* What the carrier's own wrapper costs over a raw Map: the {cardinal; representation}
   record is what makes `cardinal` O(1), which is what keeps `grow` out of the quadratic.
   AC9 (no W1 regression) is decided by these three columns at n = 1. *)
let wrapper () =
  Printf.printf "\n-- E4_table's wrapper over a raw Map.Make(Int), %d ops per cell, best of %d.\n" ops
    reps;
  Printf.printf "   ratio = e4_ms / map_ms; the price of an O(1) cardinal and the set/add split.\n\n";
  Printf.printf "  %5s  %8s %8s %6s  %8s %8s %6s  %8s %8s %6s\n" "n" "find_e4" "find_m" "r" "set_e4"
    "set_m" "r" "add_e4" "add_m" "r";
  List.iter
    (fun n ->
      let t = build_table n in
      let m = List.fold_left (fun m i -> IMap.add i i m) IMap.empty (List.init n (fun i -> i)) in
      let cellf lean fast =
        reset ();
        let a = time lean in
        reset ();
        let b = time fast in
        (a, b)
      in
      let fe, fm =
        cellf
          (fun () -> for _ = 1 to ops do ignore (E4_table.find_opt (rand n) t) done)
          (fun () -> for _ = 1 to ops do ignore (IMap.find_opt (rand n) m) done)
      in
      let se, sm =
        cellf
          (fun () -> for _ = 1 to ops do ignore (E4_table.set (rand n) 1 t) done)
          (fun () -> for _ = 1 to ops do let k = rand n in ignore (if IMap.mem k m then IMap.add k 1 m else m) done)
      in
      let ae, am =
        cellf
          (fun () -> for _ = 1 to ops do ignore (E4_table.add (rand n) 1 t) done)
          (fun () -> for _ = 1 to ops do ignore (IMap.add (rand n) 1 m) done)
      in
      Printf.printf "  %5d  %8.3f %8.3f %6.2f  %8.3f %8.3f %6.2f  %8.3f %8.3f %6.2f\n" n fe fm
        (fe /. fm) se sm (se /. sm) ae am (ae /. am))
    [ 1; 2; 4; 8; 100; 1000 ]

(* ------------------------------------------------------------------------ main *)

let print_rows () =
  Printf.printf
    "\n-- per-carrier isolation, %d ops per cell (C6: %d whole-table reads), best of %d.\n"
    ops (ops / 100) reps;
  Printf.printf "   list_ms is the Lean carrier as the LCNF backend emits it; map_ms is lane C's.\n\n";
  Printf.printf "  %-28s" "case";
  List.iter (fun n -> Printf.printf "  %22s" (Printf.sprintf "n=%d" n)) sizes;
  Printf.printf "\n";
  List.iter
    (fun (name, cells) ->
      Printf.printf "  %-28s" name;
      List.iter
        (fun (_, a, b) ->
          let r = if b > 0.0 then a /. b else infinity in
          Printf.printf "  %9.3f / %-6.3f %5.1fx" a b r)
        (List.rev cells);
      Printf.printf "\n")
    (List.rev !rows)

let () =
  let run name f = row name (List.rev_map f sizes) in
  run "C1 poke   List.set / set" c1;
  run "C2 peek   List.get? / find_opt" c2;
  run "C3 fiber  find?+map / find+set" c3;
  run "C4 emit   t ++ ev / emit" c4;
  run "C5 grow   xs ++ [v] / grow" c5;
  run "C6 read   list walk / bindings" c6;
  run "M1 memo insert (acc, ops/10)" m1;
  run "M2 memo find" m2;
  print_rows ();
  crossover ();
  wrapper ()
