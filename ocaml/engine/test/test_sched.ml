(* test_sched.ml — the property tests behind the `tested` marks of lane Q5: E4_sched,
   E4_shutdown, E4_abandon.

   THE TOY ENGINE. The scheduler is polymorphic in the machine: it takes an `engine` record
   of functions, so it compiles and is tested today against the counter machine defined
   below, and the real instance arrives from lane D later. The toy finishes after n steps,
   arms dispatchers so the event-loop rule (W3) has something to fire, parks on a token so a
   cross-machine answer (H4) has something to answer, blocks on a gate so a full mailbox
   (R2/S5) is deterministic rather than racy, and carries a scope stack with per-scope
   finalizer costs so the abandon budget (AB1-AB5) is exercised on real arithmetic. It holds
   no mutable structure: every step returns a fresh record (brief rule 3).

   Where the checks come from:
     - `sched-*` are `git:14e6835:ocaml/link/e4_test.ml`'s host tests (7d53312, lines 477-564) ported
       against the toy engine: `sched-four-machines`, `sched-rule-alone`, `sched-refusals`,
       `sched-stopped`, `sched-cross-machine` are host-four-machines, host-rule-alone,
       host-refusals, host-stopped, host-cross-machine with `E4_bridge` replaced by the
       engine record. `sched-placement`, `sched-memory-rule`, `sched-admit`,
       `sched-send-many`, `sched-trigger-once` are new, for S1, the memory rule, S2, the
       `send_many` result contract and S4.
     - `shutdown-order`, `shutdown-deadline`, `abandon-budget`, `abandon-accounts` are the
       four names the design's §4.1 gives this lane; `shutdown-seal`, `shutdown-failed`,
       `shutdown-recurse`, `shutdown-double-signal`, `shutdown-forced`, `abandon-order`,
       `abandon-max-scopes`, `sched-abandon-idempotent` and `sched-shutdown-report` are the
       remaining arms of SD1-SD6 and AB1-AB5.
     - `abandon-budget-mutation` is the mutation test of §4.1: it asserts that the SAME
       scenario under an effectively unbounded budget gives a DIFFERENT report, so deleting
       the fuel check in E4_abandon.close_scope turns it red.
     - `bench-q4b` is the B-Q4b MEASUREMENT (design §4.3, "reported, no floor yet"): a push
       on the main domain against a worker on another domain, resuming from
       `Condition.wait`. Reported, never asserted.

   One line per check, `PASS <name>` or `FAIL <name>`; the last line is
   `== ALL PASS: 0 failure(s) ==` and the exit code is 0 iff every check passed.
   Run: `dune build @engine/test/runtest --force` from ocaml. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n%!" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let raises_invalid f = match f () with exception Invalid_argument _ -> true | _ -> false
let rec await_flag a = if Atomic.get a then () else (Thread.delay 0.0002; await_flag a)

(* ---------------------------------------------------------------- the toy engine ---- *)

type decision =
  | Evaluate
  | Flush
  | Fire of int
  | Answer of { fiber : int; token : int; value : int }
  | Ping

type toy = {
  t_program : string;
  t_rows : string list; (* newest first *)
  t_len : int;
  t_armed : int list;
  t_finished : bool;
  t_parked : int option;
  t_exit : string option;
  t_refused : bool;
  t_scopes : (int * int) list; (* scope key -> finalizer steps still owed, OUTERMOST first *)
  t_interrupted : bool;
}

let park_token = 42
let toy_programs = [ "pFork"; "pTwo"; "pAwait"; "pPing"; "pScopes"; "pBlock" ]

(* pBlock's gate: the worker enters a step and stops there until the test releases it, so
   "the mailbox is full" is a fact and not a race. *)
let gate_open = Atomic.make false
let gate_entered = Atomic.make false

(* B-Q4b: the instant the worker domain entered the step for the last `Ping`. *)
let wake_at = Atomic.make 0.0

let toy_load ~program ~fuel:_ =
  {
    t_program = program;
    t_rows = [];
    t_len = 0;
    t_armed = [];
    t_finished = false;
    t_parked = None;
    t_exit = None;
    t_refused = false;
    t_scopes = (if program = "pScopes" then [ (1, 2); (2, 5); (3, 0) ] else []);
    t_interrupted = false;
  }

let emit m row = { m with t_rows = row :: m.t_rows; t_len = m.t_len + 1 }

let toy_step m ~fuel:_ d =
  if m.t_finished then m (* a decision after the end is a no-op and emits no row *)
  else
    match d with
    | Ping ->
        Atomic.set wake_at (Unix.gettimeofday ());
        emit m "pinged"
    | Evaluate -> (
        match m.t_program with
        | "pFork" | "pTwo" -> emit { m with t_armed = [ 0 ] } "evaluated"
        | "pAwait" -> emit { m with t_parked = Some park_token } "parked"
        | "pBlock" ->
            Atomic.set gate_entered true;
            let rec wait () = if Atomic.get gate_open then () else (Thread.delay 0.0002; wait ()) in
            wait ();
            emit m "evaluated"
        | _ -> emit m "evaluated")
    | Flush ->
        if m.t_parked <> None then emit { m with t_armed = [] } "flushed"
        else emit { m with t_armed = []; t_finished = true } "flushed"
    | Fire k -> (
        let row = "fired:" ^ string_of_int k in
        match (m.t_program, k) with
        | "pFork", 0 -> emit { m with t_armed = [ 1 ] } row
        | "pFork", 1 -> emit { m with t_armed = []; t_finished = true } row
        | _ -> emit { m with t_armed = [] } row)
    | Answer { fiber = _; token; value } ->
        if m.t_parked = Some token then
          emit
            { m with t_parked = None; t_finished = true; t_exit = Some ("nat " ^ string_of_int value) }
            "answered"
        else { m with t_refused = true }

let toy_rows m ~cursor =
  let ordered = List.rev m.t_rows in
  List.filteri (fun i _ -> i >= cursor) ordered

let toy_answer m =
  if m.t_finished then E4_sched.Finished
  else if m.t_parked <> None then E4_sched.Suspended
  else if m.t_refused then E4_sched.Refused
  else if m.t_armed <> [] then E4_sched.Delay
  else E4_sched.Suspended

let toy_snapshot m =
  Printf.sprintf "program=%s;steps=%d;parked=%d;exit=%s;finished=%b" m.t_program m.t_len
    (match m.t_parked with Some tk -> tk | None -> -1)
    (match m.t_exit with Some e -> e | None -> "-")
    m.t_finished

(* The one field of the snapshot the cross-machine test needs. Only strings cross domains,
   so the test parses one back out: THE MEMORY RULE, exercised rather than asserted. *)
let snapshot_field s key =
  let parts = String.split_on_char ';' s in
  let prefix = key ^ "=" in
  let n = String.length prefix in
  List.fold_left
    (fun acc p ->
      if String.length p >= n && String.sub p 0 n = prefix then
        Some (String.sub p n (String.length p - n))
      else acc)
    None parts

let toy_to_wire = function
  | Evaluate -> "evaluate"
  | Flush -> "flush"
  | Fire k -> "fire:" ^ string_of_int k
  | Answer { fiber; token; value } -> Printf.sprintf "answer:%d:%d:%d" fiber token value
  | Ping -> "ping"

(* The abandon driver: interrupt, the open scopes outermost-first, and one command step of
   one scope's finalizers. Each step appends a row, so the rows an abandon produces reach
   the ring exactly as a decision's rows do. *)
let toy_driver : toy E4_abandon.driver =
  {
    interrupt =
      (fun m ~reason -> (emit { m with t_interrupted = true } ("interrupt:" ^ reason), 1));
    open_scopes = (fun m -> List.map fst m.t_scopes);
    finalizer_step =
      (fun m ~scope ->
        match List.assoc_opt scope m.t_scopes with
        | None | Some 0 -> None
        | Some owed ->
            let scopes = List.map (fun (k, n) -> if k = scope then (k, n - 1) else (k, n)) m.t_scopes in
            let exits = if owed = 1 then [ "scope:" ^ string_of_int scope ^ " closed" ] else [] in
            (Some (emit { m with t_scopes = scopes } ("fin:" ^ string_of_int scope), exits, 1)));
  }

let toy_engine : (toy, decision) E4_sched.engine =
  {
    init = (fun () -> ());
    thread_init = (fun () -> ());
    thread_finalize = (fun () -> ());
    programs = (fun () -> toy_programs);
    load = toy_load;
    step = toy_step;
    release = (fun _ -> ());
    finished = (fun m -> m.t_finished);
    answer = toy_answer;
    armed = (fun m -> m.t_armed);
    fire_of = (fun k -> Fire k);
    trace_len = (fun m -> m.t_len);
    rows = toy_rows;
    to_wire = toy_to_wire;
    snapshot = toy_snapshot;
    abandon = toy_driver;
  }

let fuel = 100
let start ?(domains = 2) ?(mailbox_bound = 1024) () =
  E4_sched.start toy_engine
    { E4_sched.default_config with domains; mailbox_bound; spin_budget = 32 }

let spawn_ok ?domain h ~program = Result.get_ok (E4_sched.spawn ?domain h ~program ~fuel)

(* ------------------------------------------------- E4_sched: W3 W4 R1 R2 R3 H2 H4 H5 ---- *)

let () =
  let h = start () in
  let ids = List.map (fun program -> spawn_ok h ~program) [ "pFork"; "pTwo"; "pFork"; "pTwo" ] in
  List.iter
    (fun id ->
      ignore (E4_sched.send h id Evaluate);
      ignore (E4_sched.send h id Flush))
    ids;
  let quiescent = E4_sched.run_until_quiescent ~timeout:10.0 h in
  let statuses = List.filter_map (fun id -> E4_sched.inspect h id) ids in
  let entries, gap = E4_sched.events h in
  let of_machine id = List.filter (fun (e : E4_ring.entry) -> e.machine = id) entries in
  let per_machine_monotone =
    List.for_all
      (fun id ->
        let seqs = List.map (fun (e : E4_ring.entry) -> e.seq) (of_machine id) in
        seqs = List.sort compare seqs)
      ids
  in
  let rows_match =
    List.for_all (fun (s : E4_sched.status) -> List.length (of_machine s.id) = s.trace_len) statuses
  in
  let domains_ok =
    List.for_all
      (fun (s : E4_sched.status) ->
        List.for_all (fun (e : E4_ring.entry) -> e.domain = s.domain) (of_machine s.id))
      statuses
  in
  (* three steps each: evaluate, flush, and the rule's fire:0 (queued after evaluate armed
     the dispatcher; a no-op by then, since flush finished the run, so it emits no row) *)
  check "sched-four-machines"
    (quiescent && List.length statuses = 4
    && List.for_all (fun (s : E4_sched.status) -> s.finished && s.steps = 3) statuses
    && (not gap) && per_machine_monotone && rows_match && domains_ok
    && E4_sched.refusals h = 0
    && E4_sched.last_seq h >= 12
    && E4_sched.machines h = List.sort compare ids);
  check "sched-placement"
    (List.sort compare (List.map (fun id -> Option.get (E4_sched.domain_of h id)) ids) = [ 0; 0; 1; 1 ]
    && E4_sched.domain_of (start ~domains:1 ()) 0 = None
    && E4_sched.domains h = 2);
  check "sched-memory-rule"
    (List.for_all
       (fun (s : E4_sched.status) ->
         match E4_sched.inspect ~snapshot:true h s.id with
         | Some { snapshot = Some snap; _ } -> snapshot_field snap "finished" = Some "true"
         | _ -> false)
       statuses
    && (Option.get (E4_sched.inspect h (List.hd ids))).snapshot = None);
  (* the rule alone: evaluate only, and pFork finishes through fire:0 then fire:1 (W3) *)
  let r = spawn_ok h ~program:"pFork" in
  ignore (E4_sched.send h r Evaluate);
  let quiescent = E4_sched.run_until_quiescent ~timeout:10.0 h in
  let entries, _ = E4_sched.events h in
  let decisions =
    List.sort_uniq compare
      (List.map
         (fun (e : E4_ring.entry) -> (e.seq, e.decision))
         (List.filter (fun (e : E4_ring.entry) -> e.machine = r) entries))
  in
  check "sched-rule-alone"
    (quiescent
    && (match E4_sched.inspect h r with
       | Some { finished = true; steps = 3; status_answer = E4_sched.Finished; _ } -> true
       | _ -> false)
    && List.map snd decisions = [ "evaluate"; "fire:0"; "fire:1" ]);
  check "sched-refusals"
    (E4_sched.send h 999 Evaluate = Error `Unknown
    && E4_sched.spawn h ~program:"nope" ~fuel = Error (`Unknown_program "nope")
    && E4_sched.inspect h 999 = None
    && E4_sched.send_many h 999 [ Evaluate ] = Error `Unknown
    && E4_sched.abandon h 999 ~reason:"x" ~budget:E4_abandon.default_budget = Error `Unknown
    && raises_invalid (fun () -> E4_sched.spawn h ~program:"pFork" ~fuel:(-1))
    && raises_invalid (fun () -> start ~domains:0 ()));
  check "sched-admit"
    (E4_sched.admit h (List.hd ids) = E4_admit.Any && E4_sched.admit h 999 = E4_admit.None_now);
  let report = E4_sched.shutdown h in
  check "sched-shutdown-report"
    (report.exit_code = E4_shutdown.exit_clean
    && List.map (fun (i, _) -> E4_shutdown.name i) report.ran
       = [ "seal-router"; "drain-machines"; "stop-workers"; "join-domains" ]
    && report.failed = [] && report.unfinished = [] && report.passes = 1
    && E4_sched.shutdown h == report (* SD6: the same report, not an equal one *));
  check "sched-stopped"
    (E4_sched.send h (List.hd ids) Evaluate = Error `Stopped
    && E4_sched.spawn h ~program:"pFork" ~fuel = Error `Stopped
    && E4_sched.pending h = 0)

(* H4: a finish hook runs on the finishing machine's domain and may `send`. *)

let () =
  let h = start () in
  let a = spawn_ok ~domain:0 h ~program:"pAwait" in
  ignore (E4_sched.send h a Evaluate);
  ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
  let token =
    match E4_sched.inspect ~snapshot:true h a with
    | Some { snapshot = Some s; _ } -> (
        match snapshot_field s "parked" with Some tk -> int_of_string tk | None -> -1)
    | _ -> -1
  in
  let b = spawn_ok ~domain:1 h ~program:"pFork" in
  let sent = ref None in
  E4_sched.subscribe_finished h (fun id ->
      if id = b then
        match E4_sched.send h a (Answer { fiber = 0; token; value = 7 }) with
        | Ok seq -> sent := Some seq
        | Error _ -> ());
  ignore (E4_sched.send h b Evaluate);
  ignore (E4_sched.send h b Flush);
  let quiescent = E4_sched.run_until_quiescent ~timeout:10.0 h in
  let a_ok =
    match E4_sched.inspect ~snapshot:true h a with
    | Some { finished = true; snapshot = Some s; _ } -> snapshot_field s "exit" = Some "nat 7"
    | _ -> false
  in
  let entries, _ = E4_sched.events h in
  let answer_logged =
    List.exists
      (fun (e : E4_ring.entry) ->
        e.machine = a && e.decision = Printf.sprintf "answer:0:%d:7" token)
      entries
  in
  ignore (E4_sched.shutdown h);
  check "sched-cross-machine" (quiescent && token = park_token && !sent <> None && a_ok && answer_logged)

(* S5 / R2: the `send_many` result contract, against a worker stopped inside a step. *)

let () =
  Atomic.set gate_open false;
  Atomic.set gate_entered false;
  let h = start ~domains:2 ~mailbox_bound:4 () in
  let p = spawn_ok ~domain:0 h ~program:"pPing" in
  let ok = E4_sched.send_many h p [ Ping; Ping; Ping ] in
  let consecutive = match ok with Ok [ a; b; c ] -> b = a + 1 && c = b + 1 | _ -> false in
  ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
  let blocked = spawn_ok ~domain:1 h ~program:"pBlock" in
  ignore (E4_sched.send h blocked Evaluate);
  await_flag gate_entered;
  let full = E4_sched.send_many h blocked (List.init 10 (fun _ -> Ping)) in
  let one_more = E4_sched.send h blocked Ping in
  Atomic.set gate_open true;
  let quiescent = E4_sched.run_until_quiescent ~timeout:10.0 h in
  let pings_applied = match E4_sched.inspect h p with Some { steps = 3; _ } -> true | _ -> false in
  ignore (E4_sched.shutdown h);
  check "sched-send-many"
    (consecutive && full = Error (`Full 4) && one_more = Error `Full && quiescent && pings_applied)

(* S4: the three-state trigger. Two signals of one awaited trigger post exactly one row. *)

let () =
  let h = start ~domains:1 () in
  let a = spawn_ok h ~program:"pAwait" in
  ignore (E4_sched.send h a Evaluate);
  ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
  let fresh = E4_sched.trigger h a ~fiber:0 ~token:park_token in
  let not_awaited = E4_sched.signal_once h fresh (Answer { fiber = 0; token = park_token; value = 1 }) in
  let tr = E4_sched.trigger h a ~fiber:0 ~token:(park_token + 1) in
  let same = E4_sched.trigger h a ~fiber:0 ~token:(park_token + 1) == tr in
  let awaited = E4_trigger.await tr { E4_trigger.machine = a; fiber = 0; token = park_token } in
  let first = E4_sched.signal_once h tr (Answer { fiber = 0; token = park_token; value = 9 }) in
  let second = E4_sched.signal_once h tr (Answer { fiber = 0; token = park_token; value = 9 }) in
  ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
  let entries, _ = E4_sched.events h in
  let answers =
    List.length
      (List.filter
         (fun (e : E4_ring.entry) -> e.machine = a && e.decision = Printf.sprintf "answer:0:%d:9" park_token)
         entries)
  in
  ignore (E4_sched.shutdown h);
  check "sched-trigger-once"
    (not_awaited = Error `Not_awaited && same && awaited = `Awaiting
    && (match first with Ok _ -> true | _ -> false)
    && second = Error `Already && answers = 1)

(* --------------------------------------------------------- E4_abandon: AB1-AB5 ---- *)

let scopes_machine () = toy_load ~program:"pScopes" ~fuel
let budget3 = { E4_abandon.finalizer_fuel = 3; max_scopes = E4_abandon.default_max_scopes }
let budget_unbounded = { E4_abandon.finalizer_fuel = 1000; max_scopes = E4_abandon.default_max_scopes }

let () =
  let _, r = E4_abandon.run toy_driver (scopes_machine ()) ~reason:"stop" ~budget:budget3 in
  (* innermost-first: 3 (0 steps, closes at once), 2 (5 owed > 3 fuel: unfinished), 1 (2) *)
  check "abandon-order" (r.closed = [ 3; 1 ] && r.unfinished = [ 2 ]);
  check "abandon-budget" (r.fuel_left = 4 && r.exits = [ "scope:1 closed" ]);
  check "abandon-accounts"
    (E4_abandon.accounted r ~at_entry:[ 1; 2; 3 ]
    && r.decisions = 6 (* 1 interrupt + 0 + 3 spent on scope 2 + 2 on scope 1 *)
    && List.length (r.closed @ r.unfinished) = 3);
  let _, big = E4_abandon.run toy_driver (scopes_machine ()) ~reason:"stop" ~budget:budget_unbounded in
  (* THE MUTATION TEST (§4.1). Drop the budget -- delete the `left <= 0` guard in
     E4_abandon.close_scope -- and this goes red on `r.unfinished <> []`, together with
     abandon-order, abandon-budget, abandon-accounts and sched-abandon-idempotent
     (measured: 4 checks red with the guard disabled). *)
  check "abandon-budget-mutation"
    (big.closed = [ 3; 2; 1 ]
    && big.unfinished = []
    && big.decisions = 8
    && r.unfinished <> []
    && big <> r);
  let _, capped =
    E4_abandon.run toy_driver (scopes_machine ()) ~reason:"stop"
      ~budget:{ E4_abandon.finalizer_fuel = 1000; max_scopes = 2 }
  in
  check "abandon-max-scopes"
    (capped.closed = [ 3; 2 ]
    && capped.unfinished = [ 1 ]
    && E4_abandon.accounted capped ~at_entry:[ 1; 2; 3 ]
    && raises_invalid (fun () ->
           E4_abandon.run toy_driver (scopes_machine ()) ~reason:"x"
             ~budget:{ E4_abandon.finalizer_fuel = -1; max_scopes = 1 }))

(* S3 + AB5: abandon as a message run on the owning domain, and idempotent. *)

let () =
  let h = start ~domains:2 () in
  let m = spawn_ok ~domain:1 h ~program:"pScopes" in
  ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
  let first = E4_sched.abandon h m ~reason:"stop" ~budget:budget3 in
  let second = E4_sched.abandon h m ~reason:"again" ~budget:budget_unbounded in
  ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
  let entries, _ = E4_sched.events h in
  let mine = List.filter (fun (e : E4_ring.entry) -> e.machine = m) entries in
  let rows = List.map (fun (e : E4_ring.entry) -> e.row) mine in
  let latched = match E4_sched.inspect h m with Some { abandoned = Some _; _ } -> true | _ -> false in
  ignore (E4_sched.shutdown h);
  check "sched-abandon-idempotent"
    ((match (first, second) with
     | Ok a, Ok b -> a = b && a.closed = [ 3; 1 ] && a.unfinished = [ 2 ]
     | _ -> false)
    && rows = [ "interrupt:stop"; "fin:2"; "fin:2"; "fin:2"; "fin:1"; "fin:1" ]
    && List.for_all (fun (e : E4_ring.entry) -> e.decision = "abandon:stop") mine
    && latched)

(* --------------------------------------------------------- E4_shutdown: SD1-SD6 ---- *)

let () =
  let reg = E4_shutdown.Registry.create () in
  let log = ref [] in
  let say s = log := s :: !log in
  let a = E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"a" (fun () -> say "a") in
  let _b = E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"b" (fun () -> say "b") in
  let _c = E4_shutdown.Registry.register reg ~after:[ a ] ~loc:__LOC__ ~name:"c" (fun () -> say "c") in
  let r = E4_shutdown.Registry.run reg ~deadline:E4_shutdown.no_deadline in
  (* no edges would give LIFO c,b,a; the `after` edge forces a before c, so b,a,c *)
  check "shutdown-order"
    (List.rev !log = [ "b"; "a"; "c" ]
    && List.map (fun (i, _) -> E4_shutdown.name i) r.ran = [ "b"; "a"; "c" ]
    && r.failed = [] && r.unfinished = [] && r.passes = 1
    && r.exit_code = E4_shutdown.exit_clean
    && List.length (E4_shutdown.Registry.registered reg) = 3
    && E4_shutdown.index a = 0);
  check "shutdown-double-signal"
    (E4_shutdown.Registry.run reg ~deadline:E4_shutdown.no_deadline == r
    && E4_shutdown.Registry.report reg = Some r
    && List.rev !log = [ "b"; "a"; "c" ]
    && raises_invalid (fun () ->
           E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"late" (fun () -> ())));
  (* an `after` id from another registry is refused at register, never at run (SD2) *)
  let other = E4_shutdown.Registry.create () in
  check "shutdown-foreign-id"
    (raises_invalid (fun () ->
         E4_shutdown.Registry.register other ~after:[ a ] ~loc:__LOC__ ~name:"x" (fun () -> ())))

let () =
  (* SD1 + SD3 + SD4: a hook that raises is recorded and the pass continues; a hook that
     registers more work is picked up by the NEXT pass, never by the one in flight. *)
  let reg = E4_shutdown.Registry.create () in
  let log = ref [] in
  let say s = log := s :: !log in
  let seen_in_pass1 = ref 0 in
  let _boom =
    E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"boom" (fun () ->
        say "boom";
        failwith "boom")
  in
  let _spawner =
    E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"spawner" (fun () ->
        say "spawner";
        seen_in_pass1 := List.length !log;
        ignore
          (E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"child" (fun () -> say "child")))
  in
  let r = E4_shutdown.Registry.run reg ~deadline:E4_shutdown.no_deadline in
  check "shutdown-failed"
    (List.map (fun (i, _) -> E4_shutdown.name i) r.failed = [ "boom" ]
    && (match r.failed with [ (_, e) ] -> Printexc.to_string e = "Failure(\"boom\")" | _ -> false)
    && List.mem "boom" !log);
  check "shutdown-seal"
    (List.rev !log = [ "spawner"; "boom"; "child" ] && !seen_in_pass1 = 1);
  check "shutdown-recurse"
    (r.passes = 2
    && List.map (fun (i, _) -> E4_shutdown.name i) r.ran = [ "spawner"; "child" ]
    && r.unfinished = []
    && r.exit_code = E4_shutdown.exit_cleanup_failed)

let () =
  (* SD5: a hook that blocks past the deadline is reported, not waited on forever, and the
     hooks it would have preceded are reported too. Reverse registration is slow,fast, so
     `slow` runs first and eats the deadline. *)
  let reg = E4_shutdown.Registry.create () in
  let ran_fast = ref false in
  let _fast = E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"fast" (fun () -> ran_fast := true) in
  let _slow = E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"slow" (fun () -> Thread.delay 30.0) in
  let t0 = Unix.gettimeofday () in
  let r = E4_shutdown.Registry.run reg ~deadline:(t0 +. 0.25) in
  let elapsed = Unix.gettimeofday () -. t0 in
  check "shutdown-deadline"
    (r.ran = [] && r.failed = []
    && List.map E4_shutdown.name r.unfinished = [ "fast"; "slow" ]
    && r.exit_code = E4_shutdown.exit_cleanup_unfinished
    && (not !ran_fast)
    && elapsed < 5.0);
  (* a deadline already in the past: nothing is attempted, and the code says forced *)
  let reg2 = E4_shutdown.Registry.create () in
  let touched = ref false in
  let _h = E4_shutdown.Registry.register reg2 ~loc:__LOC__ ~name:"h" (fun () -> touched := true) in
  let r2 = E4_shutdown.Registry.run reg2 ~deadline:(Unix.gettimeofday () -. 1.0) in
  check "shutdown-forced"
    (r2.ran = [] && (not !touched)
    && List.map E4_shutdown.name r2.unfinished = [ "h" ]
    && r2.exit_code = E4_shutdown.exit_forced
    && r2.passes = 0)

let () =
  (* the process registry: the same laws through lwt-exit's own entry points *)
  let log = ref [] in
  let p = E4_shutdown.register ~loc:__LOC__ ~name:"p" (fun () -> log := "p" :: !log) in
  let _q = E4_shutdown.register ~after:[ p ] ~loc:__LOC__ ~name:"q" (fun () -> log := "q" :: !log) in
  let r = E4_shutdown.run ~deadline:E4_shutdown.no_deadline in
  check "shutdown-process-registry"
    (List.rev !log = [ "p"; "q" ]
    && E4_shutdown.report () = Some r
    && E4_shutdown.run ~deadline:E4_shutdown.no_deadline == r
    && E4_shutdown.loc p <> ""
    && E4_shutdown.equal p p
    && r.exit_code = E4_shutdown.exit_clean)

(* ---------------------------------------------- B-Q4b: the wake latency, reported ---- *)

let measure_wake ~spin ~rounds =
  let h =
    E4_sched.start toy_engine { E4_sched.default_config with domains = 2; spin_budget = spin }
  in
  let id = spawn_ok ~domain:1 h ~program:"pPing" in
  ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
  let samples = Array.make rounds 0.0 in
  for i = 0 to rounds - 1 do
    Atomic.set wake_at 0.0;
    let t0 = Unix.gettimeofday () in
    ignore (E4_sched.send h id Ping);
    ignore (E4_sched.run_until_quiescent ~timeout:10.0 h);
    samples.(i) <- (Atomic.get wake_at -. t0) *. 1e6
  done;
  ignore (E4_sched.shutdown h);
  Array.sort compare samples;
  let mean = Array.fold_left ( +. ) 0.0 samples /. float_of_int rounds in
  (mean, samples.(rounds / 2), samples.(rounds * 99 / 100), samples.(rounds - 1))

let () =
  let rounds = 1000 in
  List.iter
    (fun spin ->
      let mean, p50, p99, worst = measure_wake ~spin ~rounds in
      Printf.printf
        "B-Q4b wake latency (push on the main domain -> worker on domain 1), spin_budget=%d, \
         n=%d: mean %.2f us, p50 %.2f us, p99 %.2f us, max %.2f us\n\
         %!"
        spin rounds mean p50 p99 worst)
    [ 0; E4_sched.default_config.spin_budget ];
  check "bench-q4b-reported" true

let () =
  if !failures = 0 then Printf.printf "== ALL PASS: 0 failure(s) ==\n%!"
  else Printf.printf "== %d failure(s) ==\n%!" !failures;
  exit !failures
