(* test_buckets.ml — lane Q1's checks of E4_buckets (the dispatcher's priority buckets).

   What it checks, and against what:
     P-B1..P-B6  the property statements of docs/research/2026-09-08-engine-a3-queue-query.md
                 §2.1, one per Lean theorem in src/OCaml5/Lib/Deque.lean, over pseudo-random
                 states (a fixed LCG, so the run is reproducible);
     B6, B7      the armed flag (a host fact with no Lean counterpart, refusal W4-DEQ-ARMED)
                 and persistence;
     DIFF        a differential against Dispatcher_ref -- the literal transcription of
                 Fibers.lean:115-155 -- over 100 000 random enqueue/drain/arm/disarm
                 operations: `to_list` and `armed` must be equal after EVERY operation, and a
                 drain must deliver the same list;
     BENCH       the B-Q1a / B-Q1b cells at p in {1, 4, 16, 256} and drain intervals
                 {1, 8, 64, 1024, 100000}: the tripwire of R-A3-4 (if the Map carrier ever
                 wins, the default carrier changes and no caller does).

   Every test runs over BOTH carriers -- E4_buckets.Assoc (the default) and
   E4_buckets.Map_variant -- through the one signature E4_buckets.S, so the tripwire carrier
   is not a second, untested implementation.
   Exit code 0 iff every check passed. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* A fixed linear congruential generator: the run is reproducible. *)
let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n

(* Both carriers, through the one signature: the tripwire is not a second untested
   implementation. *)
let for_each_carrier (f : string -> (module E4_buckets.S) -> unit) =
  f "Assoc" (module E4_buckets.Assoc);
  f "Map_variant" (module E4_buckets.Map_variant)

(* ============================================================ the reference observations *)

(* The right-hand side of P-B2: append [x] at priority [p] of an assoc list, creating the
   bucket in ascending position if there is none. This is `insertIn` of Lib/Map.lean read at
   the observation level. *)
let rec upd p x = function
  | [] -> [ (p, [ x ]) ]
  | (q, xs) :: rest ->
    if q = p then (q, xs @ [ x ]) :: rest
    else if p < q then (p, [ x ]) :: (q, xs) :: rest
    else (q, xs) :: upd p x rest

let rec strictly_ascending = function
  | [] | [ _ ] -> true
  | a :: (b :: _ as rest) -> a < b && strictly_ascending rest

let flatten l = List.concat (List.map snd l)

(* ============================================================ P-B1 .. P-B6, B6, B7 *)

let test_properties (module B : E4_buckets.S) label =
  Printf.printf "-- E4_buckets.%s: the property statements of A3 §2.1\n" label;
  (* A pseudo-random state: [n] enqueues over [p] priorities, with a drain every so often. The
     task values are distinct, so `mem` and multiset checks mean something. *)
  let random_state ~p ~n ~tag =
    let t = ref B.empty in
    for i = 0 to n - 1 do
      t := B.enqueue !t ~priority:(rand p) ((tag * 1_000_000) + i);
      if rand 8 = 0 then t := snd (B.drain !t)
    done;
    !t
  in
  let states =
    List.init 200 (fun k -> random_state ~p:(1 + (k mod 8)) ~n:(k mod 40) ~tag:k)
  in
  (* P-B1 [drain_priority_ascending, keys_sorted, keys_nodup] *)
  let b1 =
    List.for_all
      (fun t ->
        strictly_ascending (B.priorities t)
        && B.priorities t = List.map fst (B.to_list t)
        && strictly_ascending (B.priorities (B.enqueue t ~priority:(rand 10) 7)))
      states
  in
  check (label ^ " buckets-ascending  P-B1") b1;

  (* P-B2 [bucketPairs_enqueue, drain_fifo_within_bucket] and
     P-B6 [enqueue_find_other] *)
  let b2 =
    List.for_all
      (fun t ->
        let p = rand 10 in
        let x = -1 in
        fst (B.drain (B.enqueue t ~priority:p x)) = flatten (upd p x (B.to_list t)))
      states
  in
  let b6 =
    List.for_all
      (fun t ->
        let p = rand 10 in
        let q = rand 10 in
        q = p
        || List.assoc_opt q (B.to_list (B.enqueue t ~priority:p (-2)))
           = List.assoc_opt q (B.to_list t))
      states
  in
  check (label ^ " buckets-fifo  P-B2 (tail of its own bucket) and P-B6 (others untouched)")
    (b2 && b6);

  (* P-B3 [drain_eq_flatten, drain_projection] *)
  let b3 = List.for_all (fun t -> fst (B.drain t) = flatten (B.to_list t)) states in
  check (label ^ " buckets-drain-order  P-B3") b3;

  (* P-B4 [drained_once, drain_snd_empty] *)
  let b4 =
    List.for_all
      (fun t ->
        let _, t' = B.drain t in
        B.to_list t' = [] && B.armed t' = false && B.is_empty t' && B.length t' = 0
        && fst (B.drain t') = [])
      states
  in
  check (label ^ " buckets-drained-once  P-B4") b4;

  (* P-B5 [drain_enqueue_length, drain_enqueue_mem] *)
  let b5 =
    List.for_all
      (fun t ->
        let p = rand 10 in
        let x = -3 in
        let before = fst (B.drain t) in
        let after = fst (B.drain (B.enqueue t ~priority:p x)) in
        List.length after = List.length before + 1
        && List.mem x after
        && B.length t = List.length before)
      states
  in
  check (label ^ " buckets-exactly-once  P-B5") b5;

  (* B6: enqueue arms, drain disarms, arm arms without enqueueing, disarm disarms without
     touching the buckets. *)
  let armed_ok =
    B.armed B.empty = false
    && List.for_all
         (fun t ->
           let e = B.enqueue t ~priority:0 (-4) in
           B.armed e
           && B.armed (snd (B.drain t)) = false
           && B.armed (B.arm t)
           && B.to_list (B.arm t) = B.to_list t
           && B.armed (B.disarm t) = false
           && B.to_list (B.disarm t) = B.to_list t
           && B.armed (B.arm (B.disarm t))
           && B.armed (B.disarm (B.arm t)) = false)
         states
  in
  check (label ^ " buckets-armed  B6 (enqueue arms, drain disarms, arm/disarm are the flag)")
    armed_ok;

  (* B7: an old value still answers the old questions after work on a derived one. *)
  let persistent =
    List.for_all
      (fun t ->
        let before = B.to_list t in
        let n = B.length t in
        let a = B.armed t in
        let _ = B.enqueue (B.enqueue t ~priority:3 (-5)) ~priority:0 (-6) in
        let _ = B.drain t in
        let _ = B.arm (B.disarm t) in
        B.to_list t = before && B.length t = n && B.armed t = a)
      states
  in
  check (label ^ " buckets-persistent  B7") persistent;

  (* to_list / of_list, and the refusals of of_list. *)
  let roundtrip =
    List.for_all
      (fun t ->
        let l = B.to_list t in
        let t' = B.of_list ~armed:(B.armed t) l in
        B.to_list t' = l && B.armed t' = B.armed t && fst (B.drain t') = fst (B.drain t))
      states
  in
  let refuses f = try f () |> ignore; false with Invalid_argument _ -> true in
  let refusals =
    refuses (fun () -> B.of_list ~armed:false [ (1, []); (1, []) ])
    && refuses (fun () -> B.of_list ~armed:false [ (2, []); (1, []) ])
    && refuses (fun () -> B.of_list ~armed:false [ (-1, []) ])
    && refuses (fun () -> B.enqueue B.empty ~priority:(-1) 0)
  in
  check (label ^ " buckets-of-list  to_list/of_list round trip, and the four refusals")
    (roundtrip && refusals)

(* ============================================================ the differential *)

type op =
  | Enq of int * int
  | Drain
  | Arm
  | Disarm

let differential_ops = 100_000

let gen_ops n =
  List.init n (fun i ->
      let r = rand 100 in
      if r < 80 then Enq (rand 16, i) else if r < 90 then Drain else if r < 95 then Arm
      else Disarm)

let differential (module B : E4_buckets.S) label ops =
  let bad = ref 0 in
  let first_bad = ref (-1) in
  let step = ref 0 in
  let r = ref Dispatcher_ref.empty in
  let b = ref B.empty in
  List.iter
    (fun op ->
      let same_drain =
        match op with
        | Enq (p, x) ->
          r := Dispatcher_ref.enqueue !r p x;
          b := B.enqueue !b ~priority:p x;
          true
        | Drain ->
          let rl, r' = Dispatcher_ref.drain !r in
          let bl, b' = B.drain !b in
          r := r';
          b := b';
          rl = bl
        | Arm ->
          r := Dispatcher_ref.arm !r;
          b := B.arm !b;
          true
        | Disarm ->
          r := Dispatcher_ref.disarm !r;
          b := B.disarm !b;
          true
      in
      let ok =
        same_drain
        && Dispatcher_ref.to_list !r = B.to_list !b
        && Dispatcher_ref.armed !r = B.armed !b
      in
      if not ok then begin
        incr bad;
        if !first_bad < 0 then first_bad := !step
      end;
      incr step)
    ops;
  check
    (Printf.sprintf "%s buckets-differential  %d ops against Dispatcher_ref (Fibers.lean:115-155)"
       label differential_ops)
    (!bad = 0);
  if !bad <> 0 then note "%s: %d divergences, first at op %d" label !bad !first_bad

(* ============================================================ the bench (B-Q1a / B-Q1b) *)

let bench_n = 100_000
let bench_priorities = [ 1; 4; 16; 256 ]
let bench_drains = [ 1; 8; 64; 1024; 100_000 ]
let bench_repeats = 3

let bench_carrier (module B : E4_buckets.S) label =
  let cell ~p ~d =
    let best = ref infinity in
    for _ = 1 to bench_repeats do
      Gc.compact ();
      let t0 = Unix.gettimeofday () in
      let t = ref B.empty in
      for i = 0 to bench_n - 1 do
        t := B.enqueue !t ~priority:(i mod p) i;
        if (i + 1) mod d = 0 then t := snd (B.drain !t)
      done;
      let leftover = fst (B.drain !t) in
      let t1 = Unix.gettimeofday () in
      ignore (Sys.opaque_identity leftover : int list);
      let ms = (t1 -. t0) *. 1000.0 in
      if ms < !best then best := ms
    done;
    !best
  in
  List.iter
    (fun p ->
      let cells = List.map (fun d -> cell ~p ~d) bench_drains in
      let at_1024 = List.nth cells 3 in
      Printf.printf "   %-11s %3d |%s | %8.1f M/s\n" label p
        (String.concat "" (List.map (fun ms -> Printf.sprintf " %7.2f" ms) cells))
        (float_of_int bench_n /. (at_1024 /. 1000.0) /. 1e6))
    bench_priorities

let bench () =
  print_endline
    "-- BENCH B-Q1a/B-Q1b: 100 000 enqueues, a drain every d, p priorities (ms, best of 3)";
  print_endline
    "   carrier      p |     d=1     d=8    d=64  d=1024   d=1e5 |  enq/s at d=1024";
  for_each_carrier (fun label m -> bench_carrier m label);
  note
    "the Lean carrier (Dispatcher_ref, tasks ++ [t]) needs 79 619 ms for the p=1 d=1e5 cell \
     (design §6.2); B-Q1b asks for that cell under 10 ms";
  let lean_1e5 =
    Gc.compact ();
    let t0 = Unix.gettimeofday () in
    let t = ref Dispatcher_ref.empty in
    for i = 0 to 9_999 do
      t := Dispatcher_ref.enqueue !t 0 i
    done;
    let l = fst (Dispatcher_ref.drain !t) in
    let t1 = Unix.gettimeofday () in
    ignore (Sys.opaque_identity l : int list);
    (t1 -. t0) *. 1000.0
  in
  note "Dispatcher_ref at ONE TENTH the depth (1e4 enqueues, one drain, p=1): %.2f ms"
    lean_1e5

(* ============================================================ *)

let () =
  for_each_carrier (fun label m -> test_properties m label);
  print_endline "-- the differential against the Lean transcription";
  let ops = gen_ops differential_ops in
  for_each_carrier (fun label m -> differential m label ops);
  bench ();
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
