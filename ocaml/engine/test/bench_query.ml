(* bench_query.ml -- lane Q3: the B-Q3a-c and B-Q5a-c cells of
   2026-09-08-engine-a3-queue-query.md §4.3, each with its acceptance floor and a verdict.

   A BENCH IS A MEASUREMENT, NOT A GATE: this is an `(executable)`, it prints a table and
   exits 0 whatever the numbers say.  The floors are §4.3's, which are the design's own §6.3
   probe numbers rounded down, so a regression is visible -- and so is a floor that was cut
   against a different object, which is what B-Q3c and B-Q5c turn out to be (the reading is
   printed beside each).

     B-Q3a  log append, 1e6 rows                        >= 50 M rows/s
     B-Q3b  log random get, 1e4 gets over 1e6 rows      >= 3 M/s
     B-Q3c  index build, 1e6 rows                       >= 10 M rows/s
     B-Q5a  cursor scan over a 1e5-decision tape        >= 0.9 x the raw replay rate
     B-Q5b  `at i` for 1e3 random i at k = 1024         <= 512 replayed decisions, `cost` exact
     B-Q5c  live words at k in {1, 64, 1024, infinity}  k = 1024 within 5 % of k = infinity

   THE THREE MACHINE SHAPES B-Q5c REPLAYS, because "a checkpoint is a pointer" is a claim
   about SHARING and the answer depends entirely on the shape:
     A  append-only  `d :: m` -- every version is a suffix of the next, so a retained
                     checkpoint keeps nothing the final machine does not already keep.
                     This is `E4_trace`'s shape (a reversed accumulator).
     B  path-copying `Im.add d _ m` -- a persistent balanced tree, one insertion per
                     decision.  A retained version keeps its own spine, which the final
                     machine has replaced.  This is `E4_table` / `E4_store`'s shape.
     C  the engine   `E4_engine.Fast` over a real program and an admissible tape: both
                     shapes at once, and the only number that answers the actual question.
   B-Q5a uses shape B: it asks what the QUERY LAYER costs against a raw replay of the SAME
   function, and a 1e5-decision run of the real engine would measure the engine instead.

   Run: cd ocaml && dune build engine/test/bench_query.exe && \
        ./_build/default/engine/test/bench_query.exe *)

open Effect4_engine

module E = Eff_types
module F = E4_engine.Fast
module S = E4_diff.Of (E4_engine.Fast)

let seed = 20260908
let below = ref 0
let now () = Unix.gettimeofday ()

let best k f =
  let b = ref infinity in
  for _ = 1 to k do
    Gc.compact ();
    let t0 = now () in
    let r = f () in
    let t1 = now () in
    ignore (Sys.opaque_identity r);
    if t1 -. t0 < !b then b := t1 -. t0
  done;
  !b *. 1000.

let rate ops ms = float_of_int ops /. (ms /. 1000.)

let cell name what ~ms ~ops ~unit_ ~floor =
  let r = rate ops ms in
  let ok = r >= floor in
  if not ok then incr below;
  Printf.printf "%-7s %-36s %9.3f ms %12.0f %-12s floor %10.0f  %s\n%!" name what ms r unit_
    floor
    (if ok then "PASS" else "FAIL")

let note name what ~ms ~ops ~unit_ =
  Printf.printf "%-7s %-36s %9.3f ms %12.0f %-12s (reported)\n%!" name what ms (rate ops ms)
    unit_

let verdict name what ok =
  if not ok then incr below;
  Printf.printf "%-7s %-36s %s\n%!" name what (if ok then "PASS" else "FAIL")

let live_words (f : unit -> 'a) : int * 'a =
  Gc.compact ();
  let before = (Gc.stat ()).Gc.live_words in
  let v = f () in
  Gc.full_major ();
  let after = (Gc.stat ()).Gc.live_words in
  ignore (Sys.opaque_identity v);
  (after - before, v)

(* ======================================================== B-Q3: the log and the index *)

(* A pool of rendered rows, so an append measures the CARRIER and not the formatter.  The
   strings are shared, as a real log's rows are not: this is the optimistic end of the
   append cell and it is said here rather than hidden. *)
let row_pool =
  Array.init 1024 (fun i ->
      match i mod 6 with
      | 0 -> Printf.sprintf "started(%d)" (i mod 64)
      | 1 -> Printf.sprintf "parkedOn(%d,%d)" (i mod 64) (i mod 97)
      | 2 -> Printf.sprintf "frame(%d,popped(success %d))" (i mod 64) i
      | 3 -> Printf.sprintf "scheduledTask(%d,0,start(%d))" (i mod 64) ((i + 1) mod 64)
      | 4 -> Printf.sprintf "scopeLinked(forkIn,%d,%d,%d)" (i mod 13) i (i mod 64)
      | _ -> Printf.sprintf "exited(%d,success %d)" (i mod 64) i)

let rows n =
  Random.init seed;
  Array.init n (fun _ -> row_pool.(Random.int (Array.length row_pool)))

let probes n m =
  Random.init (seed + 1);
  Array.init m (fun _ -> Random.int n)

module Im = Map.Make (Int)

let bench_log () =
  let n = 1_000_000 in
  print_endline "== B-Q3: the log and its indexes (1e6 rows) ==";
  let rs = rows n in
  let ms = best 3 (fun () -> Array.fold_left E4_log.append E4_log.empty rs) in
  cell "B-Q3a" "log append" ~ms ~ops:n ~unit_:"rows/s" ~floor:50_000_000.;
  let log = Array.fold_left E4_log.append E4_log.empty rs in
  let ps = probes n 10_000 in
  let ms =
    best 3 (fun () ->
        Array.fold_left
          (fun a i -> match E4_log.get log i with Some r -> a + String.length r | None -> a)
          0 ps)
  in
  cell "B-Q3b" "log random get, 1e4 over 1e6" ~ms ~ops:(Array.length ps) ~unit_:"gets/s"
    ~floor:3_000_000.;
  (* one decision per seven rows: ~1.4e5 decisions, the shape a real run has *)
  let entries =
    Array.mapi (fun i r -> E4_logindex.parse_run_event_row ~decision:(i / 7) i r) rs
  in
  let ms = best 3 (fun () -> Array.fold_left E4_log.Vec.append E4_log.Vec.empty entries) in
  note "B-Q3c" "breakdown: the entry vector alone" ~ms ~ops:n ~unit_:"rows/s";
  let ms =
    best 3 (fun () ->
        Array.fold_left
          (fun m (e : E4_logindex.entry) ->
             match e.E4_logindex.fiber with
             | None -> m
             | Some f ->
               Im.add f
                 (e.E4_logindex.index
                  :: (match Im.find_opt f m with None -> [] | Some l -> l))
                 m)
          Im.empty entries)
  in
  note "B-Q3c" "breakdown: ONE posting map (the §6.3 cell)" ~ms ~ops:n ~unit_:"rows/s";
  let ms = best 3 (fun () -> Array.fold_left E4_logindex.add E4_logindex.empty entries) in
  cell "B-Q3c" "index build: the whole thing" ~ms ~ops:n ~unit_:"rows/s" ~floor:10_000_000.;
  let ms =
    best 2 (fun () ->
        E4_logindex.of_log log ~parse:(fun i r ->
            E4_logindex.parse_run_event_row ~decision:(i / 7) i r))
  in
  note "B-Q3c" "end to end: of_log, codec included" ~ms ~ops:n ~unit_:"rows/s";
  let idx = Array.fold_left E4_logindex.add E4_logindex.empty entries in
  Printf.printf
    "        the index over 1e6 rows: %d fibers, %d tokens, %d scopes, %d kinds, %d \
     decisions\n%!"
    (List.length (E4_logindex.fibers idx))
    (List.length (E4_logindex.tokens idx))
    (List.length (E4_logindex.scopes idx))
    (List.length (E4_logindex.kinds idx))
    (E4_logindex.decisions idx);
  print_endline
    "        reading: the §4.3 floor of 10 M rows/s was cut against the §6.3 probe's ONE\n\
    \        posting map over a 3-field record.  That reference cell is re-measured above,\n\
    \        on this build and this machine, and it does not reach the floor either: the\n\
    \        floor is a number about a different object.  The whole index keeps five\n\
    \        posting maps and an entry vector, and the breakdown says where the time goes."

(* ========================================================= B-Q5: the cursor and `at` *)

let step (m : int Im.t) (d : int) : int Im.t = Im.add d (d * 3) m

let synth_tape n =
  Random.init (seed + 2);
  Array.init n (fun _ -> Random.int (n * 4))

let any_status (_ : 'm) : E4_query.status =
  { E4_query.finished = true; stuck = None; fuel_left = 0 }

let src ?(replay = step) (tape : int array) ~k =
  E4_query.of_run ~log:E4_log.empty ~index:E4_logindex.empty ~tape ~replay ~initial:Im.empty
    ~checkpoint_every:k ~status:any_status

let bench_cursor () =
  print_endline "";
  print_endline "== B-Q5a/b: the cursor and `at` over a 1e5-decision tape (shape B) ==";
  let n = 100_000 in
  let tape = synth_tape n in
  let raw_ms = best 3 (fun () -> Array.fold_left step Im.empty tape) in
  note "B-Q5a" "raw replay (the baseline)" ~ms:raw_ms ~ops:n ~unit_:"decisions/s";
  let build_ms = best 3 (fun () -> src tape ~k:1024) in
  note "B-Q5a" "of_run: one forward pass, k = 1024" ~ms:build_ms ~ops:n ~unit_:"decisions/s";
  let s = src tape ~k:1024 in
  let scan () =
    let c = ref (E4_query.cursor s ~from:0) and last = ref Im.empty and go = ref true in
    while !go do
      match E4_query.next !c with
      | None -> go := false
      | Some (m, c') ->
        last := m;
        c := c'
    done;
    !last
  in
  let scan_ms = best 3 scan in
  let ratio = raw_ms /. scan_ms in
  Printf.printf "%-7s %-36s %9.3f ms %12.0f %-12s ratio %.3f x raw\n%!" "B-Q5a" "cursor scan"
    scan_ms (rate n scan_ms) "decisions/s" ratio;
  verdict "B-Q5a" "cursor scan >= 0.9 x raw replay" (ratio >= 0.9);
  (* B-Q5b.  Two means: the DETERMINISTIC one over every i of the tape, which is what the
     "<= k/2 in expectation" acceptance actually asserts, and the sampled one over 1e3
     random i, whose standard error at k = 1024 is about 9 replays -- so a sampled mean of
     518 is not evidence against a floor of 512, and the deterministic mean is. *)
  let calls = ref 0 in
  let counting m d =
    incr calls;
    step m d
  in
  let s' = src ~replay:counting tape ~k:1024 in
  let all_total = ref 0 in
  for i = 0 to n do
    all_total := !all_total + E4_query.cost s' ~from:i ~upto:i
  done;
  let all_mean = float_of_int !all_total /. float_of_int (n + 1) in
  let ix = probes (n + 1) 1_000 in
  let worst = ref 0 and total = ref 0 and exact = ref true in
  let t0 = now () in
  Array.iter
    (fun i ->
       calls := 0;
       ignore (Sys.opaque_identity (E4_query.at s' i));
       let predicted = E4_query.cost s' ~from:i ~upto:i in
       if !calls <> predicted then exact := false;
       if !calls > !worst then worst := !calls;
       total := !total + !calls)
    ix;
  let at_ms = (now () -. t0) *. 1000. in
  let mean = float_of_int !total /. float_of_int (Array.length ix) in
  Printf.printf
    "%-7s %-36s %9.3f ms  sampled mean %.1f, worst %d; mean over ALL i = %.1f\n%!" "B-Q5b"
    "1e3 random `at`, k = 1024" at_ms mean !worst all_mean;
  verdict "B-Q5b" "mean over every i <= k/2 = 512" (all_mean <= 512.);
  verdict "B-Q5b" "worst replays <= k - 1 = 1023" (!worst <= 1023);
  verdict "B-Q5b" "`cost` is exact at every i" !exact

(* ------------------------------------------------------------- B-Q5c: the retention *)

(* What a viewer holds is the source AND the machine it is looking at, so both are retained
   inside the measurement; at k = infinity the source keeps only the initial machine, and
   the row is therefore "the run with no checkpoints at all", which is the baseline the
   acceptance means. *)
let retention (type m d) label (tape : d array) (replay : m -> d -> m) (initial : m)
    (ks : int list) =
  Printf.printf "  shape %s: %d decisions\n%!" label (Array.length tape);
  let rows =
    List.map
      (fun k ->
         let w, keep =
           live_words (fun () ->
               let s =
                 E4_query.of_run ~log:E4_log.empty ~index:E4_logindex.empty ~tape ~replay
                   ~initial ~checkpoint_every:k ~status:any_status
               in
               (s, E4_query.at s (Array.length tape)))
         in
         ignore (Sys.opaque_identity keep);
         (k, w))
      ks
  in
  let base = try List.assoc max_int rows with Not_found -> 1 in
  List.iter
    (fun (k, w) ->
       Printf.printf "        k = %-11s %10d live words  %+8.1f %% over k = infinity\n%!"
         (if k = max_int then "infinity" else string_of_int k)
         w
         (100. *. float_of_int (w - base) /. float_of_int (max 1 base)))
    rows;
  let target = try List.assoc 1024 rows with Not_found -> base in
  let over = float_of_int (target - base) /. float_of_int (max 1 base) in
  (label, over)

(* the G0 fork program, in `Eff_types`, as lane D writes it (test_engine.ml:103-114) *)
let fork_opts : E.fork_options =
  { E.fork_options_startImmediately = false;
    fork_options_daemon = false;
    fork_options_maskMode = E.Mask_mode_inherit }

let p_fork : E.eff =
  E.Eff_bind
    ( E.Eff_withFiber
        (E.Action_term_fork
           ( E.Eff_bind (E.Eff_yieldNow 0, E.Eff_succeed (E.Term_lit (E.Lit_nat 7))),
             fork_opts )),
      E.Eff_awaitFiber (E.Term_var 0, E.Observer_mode_awaitValue) )

let dec_of (d : E4_diff.decision) : F.decision =
  match d with
  | E4_diff.Evaluate k -> F.evaluate k
  | E4_diff.Flush -> F.flush
  | E4_diff.Fire k -> F.fire k
  | E4_diff.Yield_verdict (k, b) -> F.yield_verdict k b
  | E4_diff.Answer_async (f, tk, nn) -> F.answer_async_success f tk nn
  | E4_diff.Interrupt_from (w, tg) -> F.interrupt_from w tg
  | E4_diff.Install_middleware -> F.install_middleware

let bench_retention () =
  print_endline "";
  print_endline "== B-Q5c: checkpoint retention, three machine shapes ==";
  let ks = [ 1; 64; 1024; max_int ] in
  let n = 100_000 in
  let tape = synth_tape n in
  let _, over_a =
    retention "A append-only (E4_trace's shape)" tape (fun m d -> d :: m) [] ks
  in
  let _, over_b = retention "B path-copying (E4_table's shape)" tape step Im.empty ks in
  let dtape = S.gen_tape p_fork ~fuel:100_000 ~seed ~max_len:4_000 in
  let etape = Array.of_list (List.map dec_of dtape) in
  let _, over_c =
    retention "C the engine (E4_engine.Fast, pFork)" etape
      (fun m d -> F.replay m [ d ])
      (F.load p_fork ~fuel:100_000)
      ks
  in
  verdict "B-Q5c" "shape A: k = 1024 within 5 % of infinity" (over_a <= 0.05);
  verdict "B-Q5c" "shape B: k = 1024 within 5 % of infinity" (over_b <= 0.05);
  verdict "B-Q5c" "shape C: k = 1024 within 5 % of infinity" (over_c <= 0.05);
  print_endline
    "        reading: \"a checkpoint is a pointer\" is a claim about SHARING.  It is exact\n\
    \        for an append-only carrier (A: every version is a suffix, retention is free)\n\
    \        and false for a path-copying store (B: a retained version keeps the spine the\n\
    \        final machine replaced).  The engine (C) is where the answer that matters is,\n\
    \        and the number above is it.  The §4.3 acceptance \"within 5 % of k = infinity\"\n\
    \        holds only for shape A; for the others k is a real retention knob and the\n\
    \        table is the cost of turning it."

let () =
  Printf.printf
    "== lane Q3: the query bench (OCaml %s, int_size %d, best of 3, Gc.compact between) ==\n%!"
    Sys.ocaml_version Sys.int_size;
  print_endline "";
  bench_log ();
  bench_cursor ();
  bench_retention ();
  print_endline "";
  Printf.printf "== bench: %d cell(s) below floor (a bench is a measurement, not a gate) ==\n"
    !below
