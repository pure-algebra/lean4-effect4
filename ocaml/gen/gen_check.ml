(* gen_check.ml -- exercises the GENERATED machine_gen.ml (the LCNF route) and compares its
   dispatcher against the hand-written avatar functions copied into avatar_reference.ml.

   What it checks, and how:
     1. `dispatcher_insert` on a hand-made bucket list, printed next to the avatar's
        `Dispatcher.insert` on the same input;
     2. `dispatcher_enqueue` / `dispatcher_drain` versus the avatar's `enqueue` / `drain`
        over 200 pseudo-random enqueue sequences (a fixed LCG, so the run is reproducible),
        comparing the (priority, task ids) projection of the buckets after EVERY enqueue,
        the `armed` flag, the drained task order, and the reset dispatcher;
     3. the `RunMachine` functions (`fiber?`, `update`, `emit`, `finished`) and
        `countdownWalk` on a three-fiber machine, against the values Fibers.lean's
        definitions give by hand;
     4. `interruptRecord` on a live interruptible fiber, with and without a previous
        cause, against the cause `Supervision.interruptCause`/`Cause.combine` give by hand.
   Exit code 0 iff every check passed. *)

open Effect4_gen
module G = Machine_gen
module R = Avatar_reference

let failures = ref 0
let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* ---------------------------------------------------------------- projections *)

let task_id_g = function G.Task_start c -> c | G.Task_resume (t, _, _) -> -t
let task_id_r = function R.Tstart c -> c | R.Tresume (t, _, _) -> -t

let proj_g (bs : (_, _, _, _, _, _, _) G.bucket list) : (int * int list) list =
  List.map (fun (b : (_, _, _, _, _, _, _) G.bucket) -> (b.G.priority, List.map task_id_g b.G.tasks)) bs

let proj_r (bs : R.bucket list) : (int * int list) list =
  List.map (fun (b : R.bucket) -> (b.R.priority, List.map task_id_r b.R.tasks)) bs

let show_proj p =
  String.concat "; "
    (List.map (fun (pr, ids) -> Printf.sprintf "%d:[%s]" pr (String.concat "," (List.map string_of_int ids))) p)

let show_ids ids = "[" ^ String.concat ";" (List.map string_of_int ids) ^ "]"

(* ---------------------------------------------------------------- 1. insert *)

let () =
  print_endline "== 1. Dispatcher.insert on a hand-made bucket list ==";
  let base_g : (_, _, _, _, _, _, _) G.bucket list =
    [ { G.priority = 1; tasks = [ G.Task_start 1 ] }; { G.priority = 3; tasks = [ G.Task_start 2; G.Task_start 3 ] } ]
  in
  let base_r : R.bucket list =
    [ { R.priority = 1; tasks = [ R.Tstart 1 ] }; { R.priority = 3; tasks = [ R.Tstart 2; R.Tstart 3 ] } ]
  in
  List.iter
    (fun pr ->
      let g = proj_g (G.dispatcher_insert pr (G.Task_start 9) base_g) in
      (* the avatar mutates the bucket it appends to: rebuild the input each time *)
      let base_r' = List.map (fun (b : R.bucket) -> { R.priority = b.R.priority; tasks = b.R.tasks }) base_r in
      let r = proj_r (R.Dispatcher.insert pr (R.Tstart 9) base_r') in
      Printf.printf "  insert priority=%d: generated %s | avatar %s\n" pr (show_proj g) (show_proj r);
      check (Printf.sprintf "insert priority=%d agrees" pr) (g = r))
    [ 0; 1; 2; 3; 4 ]

(* ---------------------------------------------------------------- 2. enqueue / drain *)

let seed = ref 20260904
let rand n =
  seed := (!seed * 1103515245 + 12345) land 0x3fffffff;
  (!seed lsr 8) mod n

let () =
  print_endline "== 2. enqueue/drain differential, 200 random sequences ==";
  let mismatches = ref 0 in
  let steps = ref 0 in
  let next_id = ref 0 in
  for _ = 1 to 200 do
    let dg = ref { G.buckets = []; armed = false } in
    let dr = R.Dispatcher.empty () in
    let n = rand 13 in
    for _ = 1 to n do
      let pr = rand 5 in
      incr next_id;
      dg := G.dispatcher_enqueue !dg pr (G.Task_start !next_id);
      R.Dispatcher.enqueue dr pr (R.Tstart !next_id);
      incr steps;
      if proj_g !dg.G.buckets <> proj_r dr.R.buckets || !dg.G.armed <> dr.R.armed then begin
        incr mismatches;
        Printf.printf "  MISMATCH after enqueue %d@%d: generated %s armed=%b | avatar %s armed=%b\n" !next_id pr
          (show_proj (proj_g !dg.G.buckets)) !dg.G.armed (show_proj (proj_r dr.R.buckets)) dr.R.armed
      end
    done;
    let tasks_g, dg' = G.dispatcher_drain !dg in
    let tasks_r = R.Dispatcher.drain dr in
    incr steps;
    if List.map task_id_g tasks_g <> List.map task_id_r tasks_r
       || proj_g dg'.G.buckets <> proj_r dr.R.buckets || dg'.G.armed <> dr.R.armed then begin
      incr mismatches;
      Printf.printf "  MISMATCH on drain: generated %s | avatar %s\n"
        (show_ids (List.map task_id_g tasks_g)) (show_ids (List.map task_id_r tasks_r))
    end
  done;
  Printf.printf "  %d steps compared, %d mismatches\n" !steps !mismatches;
  check "enqueue/drain differential" (!mismatches = 0);
  (* one worked example, printed *)
  let d = List.fold_left (fun d (pr, id) -> G.dispatcher_enqueue d pr (G.Task_start id))
      { G.buckets = []; armed = false } [ (2, 1); (0, 2); (2, 3); (1, 4); (0, 5); (3, 6); (1, 7) ] in
  let tasks, d' = G.dispatcher_drain d in
  Printf.printf "  example: buckets %s armed=%b; drain -> %s, then buckets %s armed=%b\n"
    (show_proj (proj_g d.G.buckets)) d.G.armed (show_ids (List.map task_id_g tasks))
    (show_proj (proj_g d'.G.buckets)) d'.G.armed;
  check "example drain order" (List.map task_id_g tasks = [ 2; 5; 4; 7; 1; 3; 6 ]);
  check "example drain resets" (d'.G.buckets = [] && d'.G.armed = false)

(* ---------------------------------------------------------------- 3. RunMachine *)

(* Type parameters for the machine: nu=string s=unit b=unit e=string d=string i=int a=unit
   ch=unit st=unit. Placeholder types (frame contents aside) take their one constructor. *)
let mk_fiber id exited : (string, unit, unit, string, string, int, unit, unit) G.run_fiber =
  { G.id;
    frame = { G.current = G.Prim_success (); stack = []; interruptible = true;
              interrupted_cause = None; deferred_interrupt = false };
    running = false; parked = G.Parked_notParked; pending = []; finalizing = None;
    exit_ = (if exited then Some G.Placeholder_exit_ else None);
    current_op_count = 0; max_ops_before_yield = 2048; prevent_yield = false;
    yield_override = None; observers = []; children = [];
    dispatcher = { G.buckets = []; armed = false }; context = () }

let mk_machine fibers : (string, unit, unit, string, string, int, unit, unit, unit) G.run_machine =
  { G.fibers; races = []; next_id = List.length fibers; next_token = 0; next_race = 0;
    middleware_installed = false; armed = []; state = (); trace = []; stuck = None }

let () =
  print_endline "== 3. RunMachine.fiber?/update/emit/finished, countdownWalk ==";
  let m = mk_machine [ mk_fiber 0 true; mk_fiber 1 false; mk_fiber 2 false ] in
  let ids (m : (_, _, _, _, _, _, _, _, _) G.run_machine) =
    List.map (fun (f : (_, _, _, _, _, _, _, _) G.run_fiber) -> f.G.id) m.G.fibers in
  check "fiber? finds 1" (match G.run_machine_fiber_opt m 1 with Some f -> f.G.id = 1 | None -> false);
  check "fiber? misses 9" (G.run_machine_fiber_opt m 9 = None);
  let f1 = { (mk_fiber 1 false) with G.running = true; current_op_count = 5 } in
  let m' = G.run_machine_update m f1 in
  check "update replaces fiber 1 in place"
    (ids m' = [ 0; 1; 2 ]
    && (match G.run_machine_fiber_opt m' 1 with Some f -> f.G.running && f.G.current_op_count = 5 | None -> false)
    && (match G.run_machine_fiber_opt m' 2 with Some f -> not f.G.running | None -> false));
  let m'' = G.run_machine_emit m' [ G.Placeholder_run_event; G.Placeholder_run_event ] in
  check "emit appends two events" (List.length m''.G.trace = 2 && m''.G.next_id = 3);
  check "finished is false with a live fiber" (not (G.run_machine_finished m));
  let all_done = mk_machine [ mk_fiber 0 true; mk_fiber 1 true ] in
  check "finished is true when every fiber exited" (G.run_machine_finished all_done);
  check "finished is true on the empty machine" (G.run_machine_finished (mk_machine []));
  (* countdownWalk: exited targets collected in input order, up to the first live one *)
  let exits, rest = G.countdown_walk m [ 0; 1; 2; 9 ] [] in
  check "countdownWalk stops at the first live target"
    (List.length exits = 1 && rest = Some (1, [ 2; 9 ]));
  let exits, rest = G.countdown_walk all_done [ 0; 9; 1 ] [] in
  check "countdownWalk collects every exit, skipping an unknown fiber"
    (List.length exits = 2 && rest = None)

(* ---------------------------------------------------------------- 4. interruptRecord *)

let interp : (string, unit, unit, string, string, int, unit, unit, unit) G.run_interp =
  { G.to_prim_interp = G.Placeholder_prim_interp;
    park_of = (fun _ -> None);
    with_fiber_of = (fun _ -> None);
    sync_state = (fun _ _ -> None);
    register_async = (fun _ _ _ st -> (st, None));
    due_resumes = (fun st -> ([], st));
    cancel_name = (fun n _ _ -> n);
    abort_name = "abort";
    park_cancel_name = "park";
    race_cancel_name = (fun _ -> "race");
    race_settle = (fun _ _ -> G.Prim_success ());
    finalizer_program = (fun _ _ -> None);
    restore_name = (fun _ -> "restore");
    merge_name = (fun _ -> "merge");
    scope_status = (fun _ _ -> None);
    scope_link_fiber = (fun _ _ _ _ _ -> None);
    drop_finalizer = (fun _ _ _ -> None);
    close_scope = (fun _ _ _ _ _ -> None);
    ambient_scope = (fun _ -> None);
    budget_of = (fun _ -> (2048, false));
    empty_context = ();
    context_value = (fun _ -> ());
    exit_value = (fun _ _ -> G.Prim_success ());
    fiber_value = (fun _ -> ());
    fibers_value = (fun _ -> ());
    exits_value = (fun _ -> ());
    void_value = ();
    encode_fiber = (fun id -> id);
    stack_annotations = (fun _ -> []);
    async_fiber_error = "async";
    missing_scope = "missing" }

let show_reason = function
  | G.Reason_fail (e, _) -> "fail(" ^ e ^ ")"
  | G.Reason_die (d, _) -> "die(" ^ d ^ ")"
  | G.Reason_interrupt (None, _) -> "interrupt(None)"
  | G.Reason_interrupt (Some i, _) -> Printf.sprintf "interrupt(Some %d)" i

let show_cause c = "[" ^ String.concat "; " (List.map show_reason c) ^ "]"

let () =
  print_endline "== 4. interruptRecord ==";
  let eq = ( = ) in
  (* a live, interruptible, not-running fiber: the interrupt applies now *)
  let f = mk_fiber 4 false in
  let f', apply_now = G.interrupt_record eq eq eq eq interp (Some 7) [] f in
  let cause = [ G.Reason_interrupt (Some 7, []) ] in
  Printf.printf "  live fiber: applyNow=%b cause=%s current=%s parked=%s\n" apply_now
    (match f'.G.frame.G.interrupted_cause with Some c -> show_cause c | None -> "None")
    (match f'.G.frame.G.current with G.Prim_failure c -> "failure " ^ show_cause c | _ -> "other")
    (match f'.G.parked with G.Parked_notParked -> "notParked" | G.Parked_withGuard t -> "withGuard " ^ string_of_int t);
  check "live fiber: applies now, cause recorded, current := failure cause, unparked"
    (apply_now
    && f'.G.frame.G.interrupted_cause = Some cause
    && f'.G.frame.G.current = G.Prim_failure cause
    && f'.G.parked = G.Parked_notParked && f'.G.pending = []);
  (* an exited fiber: untouched *)
  let g = mk_fiber 5 true in
  let g', apply_now = G.interrupt_record eq eq eq eq interp (Some 7) [] g in
  check "exited fiber: untouched, not applied" ((not apply_now) && g' = g);
  (* a running fiber: deferred *)
  let h = { (mk_fiber 6 false) with G.running = true } in
  let h', apply_now = G.interrupt_record eq eq eq eq interp None [] h in
  check "running fiber: deferred, cause recorded"
    ((not apply_now) && h'.G.frame.G.deferred_interrupt
    && h'.G.frame.G.interrupted_cause = Some [ G.Reason_interrupt (None, []) ]);
  (* a masked fiber: recorded only *)
  let k = { (mk_fiber 7 false) with G.frame = { (mk_fiber 7 false).G.frame with G.interruptible = false } } in
  let k', apply_now = G.interrupt_record eq eq eq eq interp (Some 1) [] k in
  check "masked fiber: recorded, not applied"
    ((not apply_now) && k'.G.frame.G.interrupted_cause = Some [ G.Reason_interrupt (Some 1, []) ]
    && k'.G.frame.G.current = G.Prim_success ());
  (* a previous cause: combined through Cause.combine/dedup *)
  let prev = [ G.Reason_interrupt (Some 3, []) ] in
  let p = { (mk_fiber 8 false) with G.frame = { (mk_fiber 8 false).G.frame with G.interrupted_cause = Some prev } } in
  let p', _ = G.interrupt_record eq eq eq eq interp (Some 7) [] p in
  Printf.printf "  previous cause: accumulated=%s\n"
    (match p'.G.frame.G.interrupted_cause with Some c -> show_cause c | None -> "None");
  check "previous cause: combined, previous first"
    (p'.G.frame.G.interrupted_cause = Some (prev @ cause));
  (* the same interruptor twice: dedup keeps one *)
  let q = { (mk_fiber 9 false) with G.frame = { (mk_fiber 9 false).G.frame with G.interrupted_cause = Some cause } } in
  let q', _ = G.interrupt_record eq eq eq eq interp (Some 7) [] q in
  Printf.printf "  duplicate cause: accumulated=%s\n"
    (match q'.G.frame.G.interrupted_cause with Some c -> show_cause c | None -> "None");
  check "duplicate cause: dedup keeps one" (q'.G.frame.G.interrupted_cause = Some cause);
  (* caller annotations reach the reason *)
  let r = mk_fiber 10 false in
  let r', _ = G.interrupt_record eq eq eq eq interp (Some 2) [ ("k", ()) ] r in
  check "annotations reach the reason"
    (r'.G.frame.G.interrupted_cause = Some [ G.Reason_interrupt (Some 2, [ ("k", ()) ]) ])

let () =
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
