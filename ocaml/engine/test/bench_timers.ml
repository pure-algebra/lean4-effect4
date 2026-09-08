(* bench_timers.ml — bench cells B-Q2a..B-Q2d of the timer store (lane Q2, 2026-09-08).

   The cells and their acceptance numbers are
   docs/research/2026-09-08-engine-a3-queue-query.md §4.3:

     B-Q2a  timers, register   insert 1e3 / 1e5        >= 5 M/s at 1e3, >= 1.2 M/s at 1e5
     B-Q2b  timers, cancel     cancel n/2 by key       >= 4 M/s at 1e3, >= 0.9 M/s at 1e5
     B-Q2c  timers, advance    pop_due firing ~10 %    >= 1.0 M fires/s at 1e5
     B-Q2d  timers, footprint  live words per timer    <= 16 words/timer at 1e5

   The floors are the numbers §6.1 measured on the `twomap` probe candidate (the carrier this
   module is), rounded down, so a regression is visible. The harness is that probe's
   (scratchpad/a3/bench_psq.ml): best of 3, `Gc.compact ()` between runs, `Sys.opaque_identity`
   on every result, one deterministic RNG (seed 20260908), deadlines uniform in [0, 1e6).
   The footprint is `Gc.full_major` + `Gc.stat` live-word deltas around one built table, with
   the key array live on both sides of the delta so that it cancels.

   Not wired into `dune runtest`: a bench is a measurement, not a gate. It exits non-zero if a
   cell is under its floor, so that a lane can gate on it when it wants to.

   Run:
     cd ocaml && dune build engine
     ./engine/_build/default/test/bench_timers.exe        (or _build/default/engine/test/...) *)

open Effect4_engine

let seed = 20260908
let wall () = Unix.gettimeofday ()

let best3 f =
  let a = ref infinity in
  for _ = 1 to 3 do
    Gc.compact ();
    let t0 = wall () in
    let r = f () in
    let t1 = wall () in
    ignore (Sys.opaque_identity r);
    if t1 -. t0 < !a then a := t1 -. t0
  done;
  !a *. 1000.

(* (deadline, key) pairs; the key is also the waiter, as in the machine the waiter is
   (fiber, token) and the token IS the registration number. *)
let mk_keys n =
  Random.init seed;
  Array.init n (fun i -> (Random.int 1_000_000, i))

let build ks =
  Array.fold_left
    (fun t (d, _) -> fst (E4_timers.sleep t (E4_timers.Fin d) d))
    E4_timers.empty ks

type cell = {
  id : string;
  what : string;
  n : int;
  ms : float;
  rate : float;  (** ops/s, or words/timer for B-Q2d *)
  unit_ : string;
  floor : float;
  higher_is_better : bool;
}

let cells : cell list ref = ref []
let add c = cells := c :: !cells

let verdict c =
  if c.higher_is_better then c.rate >= c.floor else c.rate <= c.floor

(* ---------------------------------------------------------------- B-Q2a register *)

let bq2a n floor =
  let ks = mk_keys n in
  let ms = best3 (fun () -> build ks) in
  add
    {
      id = "B-Q2a";
      what = "register (sleep) n timers";
      n;
      ms;
      rate = float_of_int n /. (ms /. 1000.);
      unit_ = "inserts/s";
      floor;
      higher_is_better = true;
    }

(* ---------------------------------------------------------------- B-Q2b cancel *)

let bq2b n floor =
  let ks = mk_keys n in
  let q = build ks in
  let ms =
    best3 (fun () ->
        let r = ref q in
        Array.iteri (fun i (_, k) -> if i land 1 = 0 then r := E4_timers.cancel !r k) ks;
        !r)
  in
  add
    {
      id = "B-Q2b";
      what = "cancel n/2 by key";
      n;
      ms;
      rate = float_of_int (n / 2) /. (ms /. 1000.);
      unit_ = "cancels/s";
      floor;
      higher_is_better = true;
    }

(* ---------------------------------------------------------------- B-Q2c pop_due *)

let bq2c n floor =
  let ks = mk_keys n in
  let q = build ks in
  let upto = 100_000 (* deadlines are uniform in [0, 1e6): ~10 % due *) in
  let drain q0 =
    let rec go q k =
      match E4_timers.pop_due q ~upto with None -> (q, k) | Some (_, q') -> go q' (k + 1)
    in
    go q0 0
  in
  let fires = snd (drain q) in
  let ms = best3 (fun () -> drain q) in
  add
    {
      id = "B-Q2c";
      what = Printf.sprintf "pop_due ~upto (staged, fires %d)" fires;
      n;
      ms;
      rate = float_of_int fires /. (ms /. 1000.);
      unit_ = "fires/s";
      floor;
      higher_is_better = true;
    };
  (* the batched form, for the record: no floor of its own *)
  let ms_b = best3 (fun () -> E4_timers.advance_to q ~target:upto) in
  add
    {
      id = "B-Q2c'";
      what = "advance_to (batched, same fires)";
      n;
      ms = ms_b;
      rate = float_of_int fires /. (ms_b /. 1000.);
      unit_ = "fires/s";
      floor = 0.;
      higher_is_better = true;
    }

(* ---------------------------------------------------------------- B-Q2d footprint *)

let bq2d n ceiling =
  let ks = mk_keys n in
  Gc.full_major ();
  let b0 = (Gc.stat ()).live_words in
  let q = build ks in
  Gc.full_major ();
  let b1 = (Gc.stat ()).live_words in
  let words = b1 - b0 in
  ignore (Sys.opaque_identity q);
  ignore (Sys.opaque_identity ks);
  add
    {
      id = "B-Q2d";
      what = "live words retained by the table";
      n;
      ms = 0.;
      rate = float_of_int words /. float_of_int n;
      unit_ = "words/timer";
      floor = ceiling;
      higher_is_better = false;
    }

(* ---------------------------------------------------------------- *)

let () =
  Printf.printf
    "== lane Q2 bench: the timer store (OCaml %s, int_size %d, best of 3, seed %d) ==\n%!"
    Sys.ocaml_version Sys.int_size seed;
  bq2a 1_000 5_000_000.;
  bq2a 100_000 1_200_000.;
  bq2b 1_000 4_000_000.;
  bq2b 100_000 900_000.;
  bq2c 100_000 1_000_000.;
  bq2d 100_000 16.;
  let rows = List.rev !cells in
  Printf.printf "\n%-7s %-38s %8s %10s %14s %14s %14s  %s\n" "cell" "workload" "n" "ms" "measured"
    "floor" "unit" "verdict";
  print_endline (String.make 130 '-');
  let failed = ref 0 in
  List.iter
    (fun c ->
      let ok = verdict c || c.floor = 0. in
      if not ok then incr failed;
      Printf.printf "%-7s %-38s %8d %10.3f %14.0f %14.0f %14s  %s\n" c.id c.what c.n c.ms c.rate
        c.floor c.unit_
        (if c.floor = 0. then "(no floor)" else if ok then "PASS" else "FAIL"))
    rows;
  print_endline (String.make 130 '-');
  Printf.printf "%d of %d cells with a floor met it\n"
    (List.length (List.filter (fun c -> c.floor <> 0. && verdict c) rows))
    (List.length (List.filter (fun c -> c.floor <> 0.) rows));
  exit (if !failed = 0 then 0 else 1)
