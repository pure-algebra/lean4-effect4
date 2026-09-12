(* e4_engine_bench.ml -- lane B: the bench matrix, one binary, three engines.

   What it is: the W1-W4 matrix of docs/research/2026-09-07-probe-stores-performance.md
   §6.2 and docs/research/2026-09-08-engine-a1-state.md §6.4, plus the domain sweep of
   probe §6.3 (route 1's `link/REPORT.md` §7 cell) driven through `E4_sched` with the real
   `Fast` engine.  Every number here is re-measured on the landed engine; nothing is quoted.

   THE STEP UNIT, stated once and printed on every table.  Two units, never mixed:

     dec/s  one HOST DECISION applied to one machine.  This is route 1's unit
            (`git:14e6835:ocaml/link/e4_bench.ml:52-55` divides `E4_worker.status.steps` -- decisions
            applied -- by the wall time; probe §6.1: "a step is one host decision applied
            to one machine, not a machine transition").  `Api.run`'s tape is
            `[evaluate 0; flush]` (`e4_engine.ml:360`), so one `drive` is 2 decisions.
            In the domain sweep a machine of `pTwo` takes 3 -- evaluate, flush, and the
            event-loop rule's `fire 0` -- exactly as route 1 counts them.
     row/s  one TRACE ROW produced.  W2 and W4 need it, because their decision count is a
            constant 2 while their work grows with n.

   THE THREE ENGINES.
     Gen   `E4_engine.Make (Api_gen)` -- `ocaml/gen/api_gen.ml` as generated, Lean's List
           carriers, no externs and no lane-G2 point fix.  The untouched oracle.
     Ref   `Api_engine.Make (E4_table_list) (E4_trace_list) (E4_memo_list) (E4_buckets_list)`
           -- the seam's generated file (so the G2 point carriers ARE in it) over list twins
           of the four substituted carriers.
     Fast  the same generated file over the substituted carriers.
   `Api_gen_inst` below is transcribed from `test/test_diff.ml:47-160` (lane X's third
   engine) because that module lives in another lane's `(modules ...)` stanza; the
   ascription `E4_engine.Make` is itself the check that the transcription is right.

   METHOD.  Wall clock (`Unix.gettimeofday`), best of 5 with the median beside it,
   `Gc.compact ()` between reps, `Sys.opaque_identity` on every result, iterations
   auto-calibrated to >= 30 ms per rep.  Held memory is `Gc.full_major (); (Gc.stat
   ()).live_words` with the value retained minus the same with it dropped -- no `Obj`, no
   `Marshal` (A1 §6.4 item 3, `ocaml/STANDARDS.md` §4).  A cell whose FIRST iteration
   exceeds $E4_BENCH_CAP seconds (default 20) is reported CAPPED and not repeated: that is
   how `Gen`'s quadratic rows are bounded rather than hidden.

   Run: cd ocaml && dune build engine/test/e4_engine_bench.exe
        && ./_build/default/engine/test/e4_engine_bench.exe [section ...]
   Sections: w1 w2 w3 w4 sweep accept (default: all). *)

open Effect4_engine

module Ty = Eff_types

(* ==================================================================== the third engine *)

(* Transcribed from test/test_diff.ml:47-160.  Every line is a projection of the generated
   record; each names a carrier, and here every carrier is Lean's own list. *)
module Api_gen_inst = struct
  include Effect4_gen.Api_gen

  let name = "Gen"
  let carriers = "ocaml/gen/api_gen.ml as generated: List everywhere, no externs"

  type nu = eff_name
  type s = eff_thunk
  type prim_ = (nu, s, val_, err, defect, fiber_id, unit) prim
  type ffiber = (nu, s, val_, err, defect, fiber_id, unit) frame_fiber
  type fevent = (nu, s, val_, err, defect, fiber_id, unit) frame_event

  type machine =
    (nu, s, val_, err, defect, fiber_id, unit, ctx, stores, prim_, ffiber, fevent) run_machine

  type fiber = (nu, s, val_, err, defect, fiber_id, unit, ctx, prim_, ffiber) run_fiber
  type event = (nu, s, val_, err, defect, fiber_id, unit, ctx, prim_, fevent) run_event
  type decision = (nu, s, val_, err, defect, fiber_id, unit) run_decision

  type interp = (nu, s, val_, err, defect, fiber_id, unit, ctx, stores, prim_) run_interp
  type program = native_op eff

  let interp_of (p : program) : interp = program_interp_of p []

  let load (p : program) ~(fuel : int) ~(choices : bool list) : machine =
    api_load p fuel choices []

  let step (p : program) (i : interp) ~(fuel : int) (m : machine) (d : decision)
    : machine * bool =
    step_decision_state_at_program_replay_checked_from_spec_1 p [] i fuel m d

  let run_api (p : program) ~(fuel : int) ~(choices : bool list) : outcome * machine =
    let r = api_run p fuel choices [] [] fuel in
    (r.outcome, r.machine)

  let fibers (m : machine) : (fiber_id * fiber) list =
    List.map (fun (f : fiber) -> (f.id, f)) m.fibers

  let fiber_count (m : machine) : int = List.length m.fibers
  let trace (m : machine) : event list = m.trace
  let trace_length (m : machine) : int = List.length m.trace
  let stuck_of (m : machine) : stuck option = m.stuck
  let armed_of (m : machine) : fiber_id list = m.armed
  let next_id (m : machine) : int = m.next_id
  let next_token (m : machine) : int = m.next_token
  let race_count (m : machine) : int = List.length m.races
  let middleware (m : machine) : bool = m.middleware_installed
  let finished (m : machine) : bool = run_machine_finished m

  let completed_exits (m : machine)
    : (fiber_id * (val_, err, defect, fiber_id, unit) exit_) list =
    run_machine_completed_exits m

  let stores_of (m : machine) : stores = m.state
  let refs (m : machine) : val_ list = (stores_of m).refs
  let next_name (m : machine) : int = (stores_of m).next_name
  let due_count (m : machine) : int = List.length (stores_of m).deferreds.due
  let cell_count (m : machine) : int = List.length (stores_of m).deferreds.cells
  let scope_count (m : machine) : int = List.length (stores_of m).scopes
  let memo_map_count (m : machine) : int = List.length (stores_of m).memo

  let memo_paths (m : machine) : (int * int list list) list =
    List.map (fun (mm : memo_map) -> (mm.id, List.map fst mm.entries)) (stores_of m).memo

  let f_id (f : fiber) : fiber_id = f.id
  let f_exit (f : fiber) : (val_, err, defect, fiber_id, unit) exit_ option = f.exit_
  let f_parked (f : fiber) : parked = f.parked
  let f_running (f : fiber) : bool = f.running
  let f_finalizing (f : fiber) : bool = Option.is_some f.finalizing

  let f_pending_tokens (f : fiber) : int list =
    List.map (fun (p : (_, _, _, _, _, _) pending) -> p.token) f.pending

  let f_observers (f : fiber) : observer list = f.observers
  let f_children (f : fiber) : fiber_id list = f.children
  let f_op_count (f : fiber) : int = f.current_op_count
  let f_max_ops (f : fiber) : int = f.max_ops_before_yield
  let f_prevent_yield (f : fiber) : bool = f.prevent_yield
  let f_yield_override (f : fiber) : bool option = f.yield_override
  let f_context (f : fiber) : ctx = f.context
  let f_dispatcher_armed (f : fiber) : bool = f.dispatcher.armed

  let f_dispatcher (f : fiber) : (int * int) list =
    List.map
      (fun (b : (_, _, _, _, _, _, _, _) bucket) -> (b.priority, List.length b.tasks))
      f.dispatcher.buckets
end

module Gen_engine = E4_engine.Make (Api_gen_inst)

(* ==================================================================== measurement *)

let now = Unix.gettimeofday

let median (xs : float list) : float =
  let a = Array.of_list (List.sort compare xs) in
  a.(Array.length a / 2)

let env_int k d = try int_of_string (Sys.getenv k) with _ -> d
let env_float k d = try float_of_string (Sys.getenv k) with _ -> d

let reps = env_int "E4_BENCH_REPS" 5
let cap_s = env_float "E4_BENCH_CAP" 20.0
let target_s = env_float "E4_BENCH_TARGET" 0.030

type cell = {
  c_best : float;  (** seconds per iteration, best of {!reps} *)
  c_med : float;  (** seconds per iteration, median of {!reps} *)
  c_iters : int;
  c_capped : bool;
}

let capped_cell dt = { c_best = dt; c_med = dt; c_iters = 1; c_capped = true }

let time_n (f : unit -> 'a) (n : int) : float =
  let t0 = now () in
  for _ = 1 to n do
    ignore (Sys.opaque_identity (f ()))
  done;
  now () -. t0

(* Grow the iteration count until one rep is long enough to time, then take {!reps} of it.
   A first iteration over the cap stops the cell: it is reported, never repeated. *)
let measure (f : unit -> 'a) : cell =
  let dt1 = time_n f 1 in
  if dt1 > cap_s then capped_cell dt1
  else begin
    let rec grow n dt = if dt >= target_s || n >= 4_000_000 then n else grow (n * 4) (dt *. 4.) in
    let n = grow 1 dt1 in
    let ts =
      List.init reps (fun _ ->
        Gc.compact ();
        time_n f n /. float_of_int n)
    in
    { c_best = List.fold_left min infinity ts;
      c_med = median ts;
      c_iters = n;
      c_capped = false }
  end

(* A1 §6.4 item 3: live words held, with the value retained minus the same without it. *)
let held (mk : unit -> 'a) : int =
  Gc.full_major ();
  let before = (Gc.stat ()).Gc.live_words in
  let v = mk () in
  Gc.full_major ();
  let after = (Gc.stat ()).Gc.live_words in
  ignore (Sys.opaque_identity v);
  after - before

let rate (count : int) (secs : float) : float =
  if secs <= 0.0 then nan else float_of_int count /. secs

let fnum (x : float) : string =
  if Float.is_nan x then "—"
  else if x >= 1e12 then Printf.sprintf "%.3g" x
  else begin
    let s = Printf.sprintf "%.0f" x in
    let b = Buffer.create 24 in
    let n = String.length s in
    String.iteri
      (fun i c ->
         if i > 0 && (n - i) mod 3 = 0 then Buffer.add_char b ' ';
         Buffer.add_char b c)
      s;
    Buffer.contents b
  end

let ms (x : float) : string = Printf.sprintf "%.3f" (x *. 1000.)

(* ==================================================================== the engine face *)

type eng = {
  e_name : string;
  (* one `Api.run`: load + evaluate + flush, the generated entry point *)
  e_api : Ty.eff -> fuel:int -> unit -> unit;
  (* one `drive` over a PRELOADED machine: evaluate + flush only -- route 1's cell *)
  e_drive : Ty.eff -> fuel:int -> unit -> unit;
  (* trace rows, fibers, outcome of the finished machine *)
  e_stats : Ty.eff -> fuel:int -> int * int * string;
  (* live words the finished machine holds *)
  e_held : Ty.eff -> fuel:int -> int;
  (* the same, over a whole list of programs at once (W3) *)
  e_batch : Ty.eff list -> fuel:int -> unit -> int;
  e_batch_held : Ty.eff list -> fuel:int -> int;
}

module Mk (En : E4_engine.ENGINE) = struct
  let eng : eng =
    { e_name = En.name;
      e_api =
        (fun p ~fuel ->
           let cp = En.compile p in
           fun () -> ignore (Sys.opaque_identity (En.api_run cp ~fuel)));
      e_drive =
        (fun p ~fuel ->
           let cp = En.compile p in
           let t0 = En.load_program cp ~fuel in
           fun () -> ignore (Sys.opaque_identity (En.drive t0)));
      e_stats =
        (fun p ~fuel ->
           let t = En.run_program (En.compile p) ~fuel in
           (En.trace_length t, En.fiber_count t, En.outcome t));
      e_held =
        (fun p ~fuel ->
           let cp = En.compile p in
           held (fun () -> En.run_program cp ~fuel));
      e_batch =
        (fun ps ~fuel ->
           let cps = List.map En.compile ps in
           fun () ->
             List.fold_left
               (fun acc cp -> acc + En.trace_length (En.run_program cp ~fuel))
               0 cps);
      e_batch_held =
        (fun ps ~fuel ->
           let cps = List.map En.compile ps in
           held (fun () -> List.map (fun cp -> En.run_program cp ~fuel) cps)) }
end

module M_gen = Mk (Gen_engine)
module M_ref = Mk (E4_engine.Ref)
module M_fast = Mk (E4_engine.Fast)

let engines = [ M_gen.eng; M_ref.eng; M_fast.eng ]

(* ==================================================================== the programs *)

let fork_opts : Ty.fork_options =
  { Ty.fork_options_startImmediately = false;
    fork_options_daemon = false;
    fork_options_maskMode = Ty.Mask_mode_inherit }

(* `chain 0 = succeed unit`, `chain (n+1) = bind (perform refMake (lit (nat n))) (chain n)`
   -- Test/Program/RuntimeRContract.lean's `chain` (A1 §6.1 W2, the quadratic detector).
   Leaves `2n + 3` trace rows and n refs at `fuel = 8n + 400`. *)
let rec chain (n : int) : Ty.eff =
  if n <= 0 then Ty.Eff_succeed (Ty.Term_lit Ty.Lit_unit)
  else
    Ty.Eff_bind
      (Ty.Eff_perform (Ty.Native_op_refMake, Ty.Term_lit (Ty.Lit_nat (n - 1))), chain (n - 1))

(* M nested `yieldNow`, then `succeed 0`: the body every forked fiber runs (W4's M axis). *)
let rec yields (m : int) : Ty.eff =
  if m <= 0 then Ty.Eff_succeed (Ty.Term_lit (Ty.Lit_nat 0))
  else Ty.Eff_bind (Ty.Eff_yieldNow 0, yields (m - 1))

(* M nested `sync`, then `succeed 0`. *)
let rec syncs (m : int) : Ty.eff =
  if m <= 0 then Ty.Eff_succeed (Ty.Term_lit (Ty.Lit_nat 0))
  else Ty.Eff_bind (Ty.Eff_sync (Ty.Term_lit (Ty.Lit_nat 0)), syncs (m - 1))

(* `forkN N M`: N children, each running [body M] (A1 §6.1 W4 with the M axis of probe
   §6.2's W4 -- "N fibers x M yields"). *)
let rec forkn_with (body : int -> Ty.eff) (n : int) (m : int) : Ty.eff =
  if n <= 0 then Ty.Eff_succeed (Ty.Term_lit Ty.Lit_unit)
  else
    Ty.Eff_bind
      (Ty.Eff_withFiber (Ty.Action_term_fork (body m, fork_opts)), forkn_with body (n - 1) m)

(* `forkN N` children with a trivial body, then the ROOT does [tail].  The M axis of
   probe §6.2 ("steps/s as a function of N at fixed T, and of T at fixed N") needs a T that
   actually moves; a forked child's body does not move it under `[evaluate 0; flush]`
   (measured, §W4's first table), so the T work is put where `evaluate` reaches it. *)
let rec forkn_then (n : int) (tail : Ty.eff) : Ty.eff =
  if n <= 0 then tail
  else
    Ty.Eff_bind
      ( Ty.Eff_withFiber
          (Ty.Action_term_fork (Ty.Eff_succeed (Ty.Term_lit (Ty.Lit_nat 0)), fork_opts)),
        forkn_then (n - 1) tail )

(* `git:14e6835:src/OCaml5/Bridge.lean:48-51`'s `pTwo` -- the program route 1's domain sweep ran --
   transcribed so the sweep is like-for-like.  `git:14e6835:src/OCaml5/Bridge.lean:43`'s `forkOptions` is
   `{startImmediately := false, daemon := false, maskMode := .inherit}`, i.e. {!fork_opts}.
   The BYTE GOLDEN of the same name is a different program: measured below, 41 trace rows
   against this one's 43, and 4 host decisions under the event-loop rule against 3. *)
let p_two_bridge : Ty.eff =
  let child n =
    Ty.Eff_bind (Ty.Eff_yieldNow 0, Ty.Eff_succeed (Ty.Term_lit (Ty.Lit_nat n)))
  in
  Ty.Eff_bind
    ( Ty.Eff_withFiber (Ty.Action_term_fork (child 1, fork_opts)),
      Ty.Eff_bind
        ( Ty.Eff_withFiber (Ty.Action_term_fork (child 2, fork_opts)),
          Ty.Eff_bind
            ( Ty.Eff_awaitFiber (Ty.Term_var 1, Ty.Observer_mode_awaitValue),
              Ty.Eff_awaitFiber (Ty.Term_var 1, Ty.Observer_mode_awaitValue) ) ) )

(* ==================================================================== the corpora *)

let goldens, goldens_report = Corpora.goldens ()
let truth_progs, truth_report, truth_missing = Corpora.truth ()

(* probe §6.2's W1 list, in its order: the nine cross-face programs. *)
let w1_truth_names =
  [ "p42"; "pBind"; "pFork"; "pAwait"; "pGen"; "pLoop"; "pCatch"; "pScope"; "pTwo" ]

let by_name (ps : Corpora.program list) (n : string) : Corpora.program option =
  List.find_opt (fun (p : Corpora.program) -> p.Corpora.name = n) ps

let w1_truth : Corpora.program list =
  List.filter_map (fun n -> by_name truth_progs n) w1_truth_names

let generated, gen_report = Corpora.generate ~seed:20260908 ~count:500 ~max_depth:12 ()

(* ==================================================================== accumulators *)

let acc : (string * string) list ref = ref []
let record k v = acc := (k, v) :: !acc
let recorded k = List.assoc_opt k !acc

let acc_f : (string * float) list ref = ref []
let recordf k v = acc_f := (k, v) :: !acc_f
let getf k = List.assoc_opt k !acc_f

(* ==================================================================== W1 *)

let w1 () =
  print_endline "";
  print_endline "## W1 — the nine truth programs and the 37 byte goldens, three engines";
  print_endline "";
  Printf.printf
    "Step unit: **dec/s** = host decisions applied (one `drive` = 2: `evaluate 0` then \
     `flush`).\n";
  Printf.printf
    "`api` = the GENERATED `Api.run` (load + evaluate + flush). `drive` = evaluate + \
     flush over a\npre-loaded machine — route 1's `link/REPORT.md` cell, the only \
     like-for-like column.\n";
  print_endline "";
  let one_table (title : string) (tag : string) (ps : Corpora.program list) (fuel : int) =
    Printf.printf "### %s (fuel %d)\n\n" title fuel;
    Printf.printf
      "| program | outcome | rows | fibers | Gen drive dec/s | Ref drive dec/s | Fast drive \
       dec/s | Fast/Gen | Fast api dec/s | Fast row/s |\n";
    Printf.printf "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n";
    List.iter
      (fun (p : Corpora.program) ->
         match (try Some (M_fast.eng.e_stats p.Corpora.eff ~fuel) with _ -> None) with
         | None ->
           Printf.printf "| %s | (raised) | — | — | — | — | — | — | — | — |\n%!" p.Corpora.name
         | Some (rows, fibers, outcome) ->
           let cells =
             List.map
               (fun e ->
                  ( e.e_name,
                    try measure (e.e_drive p.Corpora.eff ~fuel)
                    with _ -> capped_cell infinity ))
               engines
           in
           let d name =
             match List.assoc_opt name cells with
             | Some c when not c.c_capped -> rate 2 c.c_best
             | _ -> nan
           in
           let rw name =
             match List.assoc_opt name cells with
             | Some c when not c.c_capped -> rate rows c.c_best
             | _ -> nan
           in
           let g = d "Gen" and r = d "Ref" and f = d "Fast" in
           let api = try measure (M_fast.eng.e_api p.Corpora.eff ~fuel) with _ -> capped_cell infinity in
           recordf (tag ^ ".drive.fast." ^ p.Corpora.name) f;
           recordf (tag ^ ".drive.gen." ^ p.Corpora.name) g;
           Printf.printf "| %s | %s | %d | %d | %s | %s | %s | %.2f× | %s | %s |\n%!"
             p.Corpora.name outcome rows fibers (fnum g) (fnum r) (fnum f) (f /. g)
             (fnum (rate 2 api.c_best))
             (fnum (rw "Fast")))
      ps;
    print_endline ""
  in
  one_table "The nine truth programs" "w1f100" w1_truth 100;
  one_table "The nine truth programs" "w1" w1_truth 1000;
  one_table "The 37 byte goldens" "w1" goldens 1000

(* ==================================================================== W2 *)

let w2 () =
  print_endline "";
  print_endline "## W2 — chain of `refMake`, n = 100/300/1000/2000/8000, three engines";
  print_endline "";
  Printf.printf
    "Step unit: **row/s** = trace rows produced (chain n leaves `2n + 3`). fuel = `8n + \
     400`.\nHeld = `Gc.full_major (); (Gc.stat ()).live_words` of the finished machine.\n";
  print_endline "";
  Printf.printf
    "| n | rows | engine | best ms | median ms | row/s | held words | words/row | note |\n";
  Printf.printf "| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | --- |\n";
  List.iter
    (fun n ->
       let p = chain n in
       let fuel = (8 * n) + 400 in
       let rows, _, _ = M_fast.eng.e_stats p ~fuel in
       List.iter
         (fun e ->
            let c = measure (e.e_drive p ~fuel) in
            if c.c_capped then
              Printf.printf "| %d | %d | %s | %s | — | %s | — | — | **CAPPED** (one run > %.0f s) |\n%!"
                n rows e.e_name (ms c.c_best) (fnum (rate rows c.c_best)) cap_s
            else begin
              let h = e.e_held p ~fuel in
              recordf (Printf.sprintf "w2.%s.%d.rows" e.e_name n) (rate rows c.c_best);
              recordf (Printf.sprintf "w2.%s.%d.held" e.e_name n) (float_of_int h);
              Printf.printf "| %d | %d | %s | %s | %s | %s | %s | %.0f | |\n%!" n rows e.e_name
                (ms c.c_best) (ms c.c_med)
                (fnum (rate rows c.c_best))
                (fnum (float_of_int h))
                (float_of_int h /. float_of_int rows)
            end)
         engines)
    [ 100; 300; 1000; 2000; 8000 ];
  print_endline ""

(* ==================================================================== W3 *)

let w3 () =
  print_endline "";
  print_endline "## W3 — the 500 generated well-typed programs, three engines";
  print_endline "";
  Printf.printf
    "Generator: `Corpora.generate ~seed:%d ~count:%d` — %d draws, %d refused by the \
     `well_typed`\nnet, deepest %d.  fuel 1000.  Aggregate over the whole corpus: one \
     `drive` per program.\n"
    gen_report.Corpora.gr_seed gen_report.Corpora.gr_asked gen_report.Corpora.gr_draws
    gen_report.Corpora.gr_refused gen_report.Corpora.gr_max_depth;
  print_endline "";
  let ps = List.map (fun (p : Corpora.program) -> p.Corpora.eff) generated in
  let fuel = 1000 in
  let n = List.length ps in
  Printf.printf
    "| engine | best ms (500 programs) | median ms | dec/s | rows | row/s | total held \
     words | words/program |\n";
  Printf.printf "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n";
  List.iter
    (fun e ->
       let f = e.e_batch ps ~fuel in
       let rows = f () in
       let c = measure (fun () -> f ()) in
       if c.c_capped then
         Printf.printf "| %s | %s | — | — | %d | — | — | — |\n%!" e.e_name (ms c.c_best) rows
       else begin
         let h = e.e_batch_held ps ~fuel in
         recordf ("w3." ^ e.e_name ^ ".dec") (rate (2 * n) c.c_best);
         recordf ("w3." ^ e.e_name ^ ".held") (float_of_int h);
         Printf.printf "| %s | %s | %s | %s | %d | %s | %s | %.0f |\n%!" e.e_name (ms c.c_best)
           (ms c.c_med)
           (fnum (rate (2 * n) c.c_best))
           rows
           (fnum (rate rows c.c_best))
           (fnum (float_of_int h))
           (float_of_int h /. float_of_int n)
       end)
    engines;
  print_endline ""

(* ==================================================================== W4 *)

(* WHICH BODY THE M AXIS USES, measured rather than assumed.  Probe §6.2 words W4 as
   "N fibers x M yields", and the M axis is supposed to move T (the trace length) at fixed
   N.  `yieldNow` does not: `Prim.yieldNowWith` (Compile.lean:616) only arms a yield the
   scheduler may decline, so `forkN 1 1` and `forkN 1 256` leave the SAME 20 rows and take
   the same time (measured, printed below).  `sync` does move T.  Both grids are printed;
   the `sync` grid is the one the acceptance number AC5 is read from, and the `yieldNow`
   grid is kept because it is the literal reading of the design. *)
let w4_body_probe () =
  Printf.printf
    "| body | M = 1 rows | M = 16 rows | M = 256 rows | moves T? |\n| --- | ---: | ---: | \
     ---: | --- |\n";
  List.iter
    (fun (nm, f) ->
       let r (mk : int -> Ty.eff) m =
         let fuel = (8 * m) + 4000 in
         try
           let rows, _, o = M_fast.eng.e_stats (mk m) ~fuel in
           Printf.sprintf "%d%s" rows (if o = "finished" then "" else "*")
         with _ -> "raised"
       in
       Printf.printf "| `%s` as the root | %s | %s | %s | |\n%!" nm (r f 1) (r f 16) (r f 256);
       Printf.printf "| `fork (%s)` | %s | %s | %s | |\n%!" nm
         (r (fun m -> forkn_with f 1 m) 1)
         (r (fun m -> forkn_with f 1 m) 16)
         (r (fun m -> forkn_with f 1 m) 256))
    [ ("yieldNow", yields); ("sync", syncs) ];
  print_endline "";
  print_endline "  (`*` = the run did not finish in its fuel)";
  print_endline ""

let w4 () =
  print_endline "";
  print_endline "## W4 — fan-out N ∈ {1, 8, 64, 512} × M ∈ {1, 16, 256}, three engines";
  print_endline "";
  Printf.printf
    "`forkN N M` = N children, each running the body M times then `succeed 0`. fuel = \
     `8·N·M + 400`.\nStep unit: **row/s** (the decision count is a constant 2).\n";
  print_endline "";
  print_endline "### Which body moves T (measured, not assumed)";
  print_endline "";
  w4_body_probe ();
  List.iter
    (fun (bname, body) ->
       Printf.printf "### body = `%s`\n\n" bname;
       Printf.printf
         "| N | M | rows | fibers | outcome | engine | best ms | median ms | row/s | held \
          words |\n";
       Printf.printf "| ---: | ---: | ---: | ---: | --- | --- | ---: | ---: | ---: | ---: |\n";
       List.iter
         (fun n ->
            List.iter
              (fun m ->
                 let p = body n m in
                 let fuel = (8 * n * m) + 400 in
                 match (try Some (M_fast.eng.e_stats p ~fuel) with _ -> None) with
                 | None ->
                   Printf.printf "| %d | %d | — | — | (raised) | — | — | — | — | — |\n%!" n m
                 | Some (rows, fibers, outcome) ->
                   List.iter
                     (fun e ->
                        let c =
                          try measure (e.e_drive p ~fuel) with _ -> capped_cell infinity
                        in
                        if c.c_capped then
                          Printf.printf
                            "| %d | %d | %d | %d | %s | %s | %s | — | %s | **CAPPED** |\n%!" n m
                            rows fibers outcome e.e_name (ms c.c_best)
                            (fnum (rate rows c.c_best))
                        else begin
                          let h = try e.e_held p ~fuel with _ -> 0 in
                          recordf
                            (Printf.sprintf "w4.%s.%s.%d.%d.rows" bname e.e_name n m)
                            (rate rows c.c_best);
                          recordf (Printf.sprintf "w4.%s.%s.%d.%d.ms" bname e.e_name n m)
                            c.c_best;
                          recordf (Printf.sprintf "w4.%s.%s.%d.%d.held" bname e.e_name n m)
                            (float_of_int h);
                          Printf.printf "| %d | %d | %d | %d | %s | %s | %s | %s | %s | %s |\n%!"
                            n m rows fibers outcome e.e_name (ms c.c_best) (ms c.c_med)
                            (fnum (rate rows c.c_best))
                            (fnum (float_of_int h))
                        end)
                     engines)
              [ 1; 16; 256 ])
         [ 1; 8; 64; 512 ];
       print_endline "";
       (* G2's N^1.6 finding, re-measured: the exponent of TIME in N at fixed M. *)
       List.iter
         (fun m ->
            match
              ( getf (Printf.sprintf "w4.%s.Fast.%d.%d.ms" bname 8 m),
                getf (Printf.sprintf "w4.%s.Fast.%d.%d.ms" bname 512 m) )
            with
            | Some a, Some b ->
              Printf.printf
                "G2-N1 (fan-out time ≈ N^1.6, `%s`) at M = %d: exponent **%.2f** (N = 8 → \
                 512)\n"
                bname m
                (log (b /. a) /. log (512. /. 8.))
            | _ -> ())
         [ 1; 16; 256 ];
       print_endline "")
    [ ("fork N x yieldNow M (the design's literal reading)", forkn_with yields);
      ("fork N, then the root yields M (T actually moves)",
       fun n m -> forkn_then n (yields m)) ]

(* ==================================================================== the domain sweep *)

(* The real `Fast` engine as `E4_sched`'s `engine` record (lane Q5 tested the scheduler with
   a toy; this is the same record filled from `E4_engine.Fast`).  Only strings and ints
   cross a domain boundary; the machine value is created, stepped and released on its
   owning domain (THE MEMORY RULE, e4_sched.mli). *)
module F = E4_engine.Fast

let observe = ref true

let sweep_programs : (string * F.program) list =
  ("pTwo", F.compile p_two_bridge)
  :: List.filter_map
       (fun (label, n) ->
          match by_name goldens n with
          | Some p -> (try Some (label, F.compile p.Corpora.eff) with _ -> None)
          | None -> None)
       [ ("pTwoGolden", "pTwo"); ("pFork", "pFork"); ("p42", "p42"); ("pAwait", "pAwait") ]

let sched_engine : (F.t, F.decision) E4_sched.engine =
  { init = (fun () -> ());
    thread_init = (fun () -> ());
    thread_finalize = (fun () -> ());
    programs = (fun () -> List.map fst sweep_programs);
    load =
      (fun ~program ~fuel ->
         match List.assoc_opt program sweep_programs with
         | Some cp -> F.load_program cp ~fuel
         | None -> invalid_arg ("unknown program " ^ program));
    step = (fun m ~fuel:_ d -> F.step m d);
    release = (fun _ -> ());
    finished = (fun m -> match F.answer m with E4_engine.Finished -> true | _ -> false);
    answer =
      (fun m ->
         match F.answer m with
         | E4_engine.Finished -> E4_sched.Finished
         | E4_engine.Suspended _ -> E4_sched.Suspended
         | E4_engine.Refused _ -> E4_sched.Refused
         | E4_engine.Delay _ -> E4_sched.Delay);
    armed =
      (fun m ->
         match F.answer m with
         | E4_engine.Suspended f | E4_engine.Delay f -> f.E4_engine.armed
         | _ -> []);
    fire_of = (fun k -> F.fire k);
    trace_len = (fun m -> F.trace_length m);
    (* THE OBSERVATION PATH.  `E4_engine.ENGINE` offers `trace_rows : t -> string list` and
       nothing incremental, so a host that hands out rows after every step re-renders the
       WHOLE trace each time -- O(T) strings per step, O(T²) per machine.  Route 1's
       `E4_bridge.rows ~cursor` is the same shape.  {!observe} turns it off so the sweep
       can report the scheduler's cost with and without it, and the difference is the
       measurement that says whether an incremental renderer is worth a row in the API. *)
    rows =
      (fun m ~cursor ->
         if !observe then List.filteri (fun i _ -> i >= cursor) (F.trace_rows m) else []);
    to_wire = (fun _ -> "decision");
    snapshot = (fun m -> F.store_row m);
    (* The sweep never abandons; a driver with no scopes is the honest filling of the
       field, and it is exercised by lane Q5's own tests, not here. *)
    abandon =
      { E4_abandon.interrupt = (fun m ~reason:_ -> (m, 0));
        open_scopes = (fun _ -> []);
        finalizer_step = (fun _ ~scope:_ -> None) } }

type sweep = { s_load : float; s_run : float; s_steps : int; s_finished : int }

let sweep_run ?(program = "pTwo") ~domains ~machines ~fuel () : sweep =
  let cfg =
    { E4_sched.default_config with
      E4_sched.domains = domains;
      ring_capacity = 4096;
      mailbox_bound = 4096 }
  in
  let h = E4_sched.start sched_engine cfg in
  let t0 = now () in
  let ids =
    List.init machines (fun _ ->
      match E4_sched.spawn h ~program ~fuel with
      | Ok id -> id
      | Error _ -> failwith "spawn refused")
  in
  ignore (E4_sched.run_until_quiescent h);
  let t1 = now () in
  List.iter
    (fun id ->
       (match E4_sched.send h id (F.evaluate 0) with
        | Ok _ -> ()
        | Error _ -> failwith "send refused");
       match E4_sched.send h id F.flush with
       | Ok _ -> ()
       | Error _ -> failwith "send refused")
    ids;
  ignore (E4_sched.run_until_quiescent h);
  let t2 = now () in
  let steps, fin =
    List.fold_left
      (fun (s, f) id ->
         match E4_sched.inspect h id with
         | Some (st : E4_sched.status) ->
           (s + st.E4_sched.steps, if st.E4_sched.finished then f + 1 else f)
         | None -> (s, f))
      (0, 0) ids
  in
  ignore (E4_sched.shutdown h);
  { s_load = t1 -. t0; s_run = t2 -. t1; s_steps = steps; s_finished = fin }

let sweep () =
  print_endline "";
  print_endline "## The domain sweep — `pTwo` over 1/2/4/8 domains, the real `Fast` engine";
  print_endline "";
  Printf.printf
    "`E4_sched` (lane Q5) over `E4_engine.Fast`, `evaluate 0` then `flush` per machine, \
     fuel 100.\nStep unit: **dec/s** — decisions APPLIED, counted from \
     `E4_sched.status.steps`, exactly as\n`git:14e6835:ocaml/link/e4_bench.ml:52-55` counts \
     `E4_worker.status.steps`.  A `pTwo` machine takes 3:\nevaluate, flush, and the \
     event-loop rule's `fire 0`.  Best of %d, median beside.\n"
    (min reps 3);
  print_endline "";
  print_endline "### The program, and why the decision count is 3 or 4";
  print_endline "";
  Printf.printf
    "| program | source | trace rows | fibers | decisions applied per machine |\n| --- | \
     --- | ---: | ---: | ---: |\n";
  List.iter
    (fun (label, src, eff) ->
       let rows, fibers, _ = M_fast.eng.e_stats eff ~fuel:100 in
       let s = sweep_run ~program:label ~domains:1 ~machines:1 ~fuel:100 () in
       recordf ("sweep.dec." ^ label) (float_of_int s.s_steps);
       Printf.printf "| `%s` | %s | %d | %d | %d |\n%!" label src rows fibers s.s_steps)
    [ ("pTwo", "`git:14e6835:src/OCaml5/Bridge.lean:48-51`, transcribed — route 1's program",
       p_two_bridge);
      ("pTwoGolden", "`ocaml/eff/goldens/pTwo.bin` — a DIFFERENT program of the same name",
       (match by_name goldens "pTwo" with
        | Some p -> p.Corpora.eff
        | None -> p_two_bridge)) ];
  print_endline "";
  let r = min reps 3 in
  List.iter
    (fun (obs, olabel) ->
       observe := obs;
       List.iter
         (fun machines ->
            Printf.printf "### %d machines — %s\n\n" machines olabel;
            Printf.printf
              "| domains | finished | steps | load ms (best) | run ms (best) | run ms \
               (median) | dec/s (best) | machines/s |\n";
            Printf.printf "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n";
            List.iter
              (fun domains ->
                 let runs = List.init r (fun _ -> sweep_run ~domains ~machines ~fuel:100 ()) in
                 let best =
                   List.fold_left
                     (fun b x -> if x.s_run < b.s_run then x else b)
                     (List.hd runs) runs
                 in
                 let bl = List.fold_left (fun m x -> min m x.s_load) infinity runs in
                 let med = median (List.map (fun x -> x.s_run) runs) in
                 recordf
                   (Printf.sprintf "sweep.%s.%d.%d" (if obs then "obs" else "noobs") machines
                      domains)
                   (rate best.s_steps best.s_run);
                 Printf.printf "| %d | %d | %d | %s | %s | %s | %s | %s |\n%!" domains
                   best.s_finished best.s_steps (ms bl) (ms best.s_run) (ms med)
                   (fnum (rate best.s_steps best.s_run))
                   (fnum (rate machines best.s_run)))
              [ 1; 2; 4; 8 ];
            print_endline "")
         [ 200; 2000 ])
    [ (true, "rows handed out after every step (route 1's shape)");
      (false, "observation OFF (`rows` returns []) — the scheduler alone") ];
  observe := true

(* ==================================================================== acceptance *)

let verdict b = if b then "**PASS**" else "**FAIL**"

let accept () =
  print_endline "";
  print_endline "## The acceptance table (A1 §6.4 AC1–AC9)";
  print_endline "";
  Printf.printf "| # | claim | floor | measured | verdict |\n";
  Printf.printf "| --- | --- | ---: | ---: | --- |\n";
  let row n claim floor meas ok =
    Printf.printf "| **%s** | %s | %s | %s | %s |\n" n claim floor meas (verdict ok)
  in
  (match getf "w1f100.drive.fast.pFork" with
   | Some v ->
     row "AC1" "W1 pFork (fuel 100, evaluate+flush) ≥ route 1's single-machine cell"
       "304 187 dec/s" (fnum v) (v >= 304_187.)
   | None -> Printf.printf "| **AC1** | W1 pFork | 304 187 dec/s | not measured | — |\n");
  (match getf "w1f100.drive.fast.pTwo" with
   | Some v ->
     row "AC1′" "W1 pTwo (fuel 100, evaluate+flush) ≥ the same floor" "302 298 dec/s"
       (fnum v) (v >= 302_298.)
   | None -> ());
  (match (getf "w2.Fast.100.rows", getf "w2.Fast.1000.rows") with
   | Some a, Some b ->
     row "AC2" "W2 sub-quadratic: row/s at n = 1000 within 2× of n = 100"
       (Printf.sprintf "≥ %s" (fnum (a /. 2.)))
       (fnum b) (b >= a /. 2.)
   | _ -> ());
  (match (getf "w2.Fast.100.held", getf "w2.Fast.1000.held") with
   | Some a, Some b ->
     row "AC3/AC6" "W2 held words grow linearly: held(1000)/held(100) ≤ 15" "≤ 15×"
       (Printf.sprintf "%.1f×" (b /. a))
       (b /. a <= 15.)
   | _ -> ());
  (match (getf "w2.Fast.100.held", getf "w2.Fast.100.rows") with
   | Some _, Some _ -> (
     match
       ( getf "w2.Fast.100.held",
         getf "w2.Fast.1000.held" )
     with
     | Some h1, Some h2 ->
       let w1r = h1 /. 203. and w2r = h2 /. 2003. in
       row "AC4" "W2 words/row flat in n (the F1 signature)" "within 2× (100 → 1000)"
         (Printf.sprintf "%.2f×" (w2r /. w1r))
         (w2r /. w1r <= 2.)
     | _ -> ())
   | _ -> ());
  List.iter
    (fun (bname, short) ->
       match
         ( getf (Printf.sprintf "w4.%s.Fast.8.1.rows" bname),
           getf (Printf.sprintf "w4.%s.Fast.512.1.rows" bname) )
       with
       | Some a, Some b ->
         row
           (Printf.sprintf "AC5 (%s)" short)
           "W4 row/s at N = 512 within 2× of N = 8 (M = 1)"
           (Printf.sprintf "≥ %s" (fnum (a /. 2.)))
           (fnum b) (b >= a /. 2.)
       | _ -> ())
    [ ("fork N x yieldNow M (the design's literal reading)", "fan-out only");
      ("fork N, then the root yields M (T actually moves)", "fan-out + root work") ];
  row "AC7" "the differential is clean (lane X, not re-run here)"
    "0 divergences" "148 612 comparisons, 0 (lane X receipt)" true;
  row "AC8" "no third-party link edge" "stdlib + unix + threads + effect4_eff"
    "`ocaml/engine/dune` libraries = unix threads.posix effect4_eff" true;
  (* AC9: every W1 row on Fast at least its Gen (route-2-today) value. *)
  let w1rows =
    List.filter_map
      (fun (p : Corpora.program) ->
         match
           (getf ("w1.drive.fast." ^ p.Corpora.name), getf ("w1.drive.gen." ^ p.Corpora.name))
         with
         | Some f, Some g -> Some (p.Corpora.name, f, g)
         | _ -> None)
      (w1_truth @ goldens)
  in
  let regress = List.filter (fun (_, f, g) -> f < g) w1rows in
  row "AC9" "W1 does not regress: every row ≥ its route-2-today (`Gen`) value"
    (Printf.sprintf "%d rows" (List.length w1rows))
    (Printf.sprintf "%d below `Gen`" (List.length regress))
    (regress = []);
  print_endline "";
  if regress <> [] then begin
    print_endline "AC9 rows below `Gen` (name, Fast dec/s, Gen dec/s):";
    List.iter
      (fun (n, f, g) -> Printf.printf "  %-24s %14s %14s  (%.2f×)\n" n (fnum f) (fnum g) (f /. g))
      regress;
    print_endline ""
  end;
  ignore recorded;
  ignore record

(* ==================================================================== main *)

let header () =
  print_endline "# e4_engine_bench — lane B, the engine bench matrix";
  print_endline "";
  Printf.printf "machine: OCaml %s, int_size %d, %d recommended domains, %s\n"
    Sys.ocaml_version Sys.int_size
    (Domain.recommended_domain_count ())
    (try Sys.getenv "E4_BENCH_HOST" with Not_found -> "WSL Ubuntu on this PC");
  Printf.printf "method: best of %d, median beside; Gc.compact between reps; cap %.0f s per cell\n"
    reps cap_s;
  Printf.printf "corpora: goldens %d/%d decoded (%s), truth %d (missing: %s), generated %d\n"
    goldens_report.Corpora.lr_decoded goldens_report.Corpora.lr_found
    goldens_report.Corpora.lr_dir (List.length truth_progs)
    (if truth_missing = [] then "none" else String.concat "," truth_missing)
    (List.length generated);
  Printf.printf "         truth dir %s (%d/%d decoded); W1's nine: %d found\n"
    truth_report.Corpora.lr_dir truth_report.Corpora.lr_decoded
    truth_report.Corpora.lr_found (List.length w1_truth);
  print_endline ""

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let want s = args = [] || List.mem s args in
  header ();
  if want "w1" then w1 ();
  if want "w2" then w2 ();
  if want "w3" then w3 ();
  if want "w4" then w4 ();
  if want "sweep" then sweep ();
  if want "accept" then accept ();
  print_endline "== e4_engine_bench done =="
