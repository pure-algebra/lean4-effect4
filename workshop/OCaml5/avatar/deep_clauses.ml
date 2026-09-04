(* `Effect4/Deep/Clauses.lean` → `deep_clauses.ml`: the mechanism clauses of the reference
   machine, one OCaml entry per Lean theorem, in the Lean order, each with the line it is the
   port of and the census rows it is tagged with (`census:` in the Lean docstring).

   Seat F1, 2026-09-04. Report: `docs/research/2026-09-04-seat-w1-deep-port.md`.

   A Lean clause is an equation on the machine's own definition, proved by the definition
   computing. Its avatar counterpart is an *executable check* over the avatar's machine
   (`deep_fibers.ml`), in one of three shapes:

   * `Pure`: the clause is about a function of the machine (`interruptRecord`, `spawn`,
     `Dispatcher.enqueue`, ...). The check constructs the shape the Lean statement fixes by
     construction -- a fiber whose current primitive is the arm's, a machine whose fiber
     table holds the target -- calls the avatar's function, and reads the equation off the
     result. Evaluated once; the avatar is its own instance.
   * `Run`: the clause is also a predicate on the machine at the moment an event is emitted
     (`RunMachine.emit`, `Fibers.lean:476`, is the one place the trace grows; under
     DIVERGENCE 3 the live machine is the snapshot at that step). Evaluated on every
     witness of `deep_witnesses.ml` that exercises the clause (the census join,
     `deep_census.ml`), answering the first violating step.
   * `Refused`: the clause speaks about a shape the avatar does not have -- `Cmd.loop`
     (DIVERGENCE 2), a `Prim` in `frame.current` (DIVERGENCE 1), the ambient context
     (`χ = unit`, A0 §18). Not portable, with why.

   Behavioural properties of this module (packages plan §4.5): (1) every check is total and
   deterministic -- a fresh machine per check, no ambient state read but the store it seeds;
   (2) a check never emits an event, so a `Run` check cannot re-enter the probe; (3) the
   entry order is the Lean order, and `count` is the number of `theorem`s in
   `Clauses.lean`, guarded by `run-witnesses.sh`. *)

open Deep_fibers
open Deep_stores

(* ---------------------------------------------------------------------- the shapes *)

type verdict = Holds | Fails of string | Not_portable of string

(* `Some msg` is a violation; `None` holds. *)
type step_check = run_machine -> int -> run_event -> string option

type check =
  | Pure of (unit -> string option)
  | Run of step_check
  | Both of (unit -> string option) * step_check
  | Refused of string

type clause = {
  name : string;          (* the Lean theorem, e.g. `runloopTop_deferred` *)
  lean : string;          (* `Clauses.lean:<line>` *)
  census : string list;   (* the census rows the docstring tags *)
  check : check;
}

(* ---------------------------------------------------------------------- helpers *)

let fail msg = Some msg
let ok = None
let expect (b : bool) (msg : string) : string option = if b then None else Some msg

(* The first violation of a list of expectations. *)
let all (checks : string option list) : string option =
  List.fold_left (fun acc c -> match acc with Some _ -> acc | None -> c) None checks

(* A fresh machine over reset global state: the store, the wire's handle space, the row
   sink, the installed program, the fixture arrays. *)
let setup () : run_machine =
  store_reset ();
  Hashtbl.reset handles;
  Hashtbl.reset handle_owner;
  next_handle := 0;
  sink := [];
  current_program := None;
  state.started <- [];
  state.cleanups <- [];
  max_ops_before_yield := max_int;
  let m = machine_empty state in
  (* the fuel an arm called outside `exec` hands to the nested commands it drives *)
  m.drive_fuel <- 400;
  m

let fuel = 400

(* A fiber appended to `m`, unstarted, over a program. *)
let add_fiber ?(program = fun () -> Vunit) ?(interruptible = true) m : run_fiber =
  let f = run_fiber_make m.next_id program interruptible (!max_ops_before_yield, !prevent_yield) () in
  m.fibers <- m.fibers @ [ f ];
  m.next_id <- m.next_id + 1;
  f

(* What a continuation was resumed with. *)
type got = Ret of value | Thr of exn | Exits of exitv list

let recorder () : value kops * got list ref =
  let got = ref [] in
  ({ ret = (fun v -> got := !got @ [ Ret v ]); thr = (fun e -> got := !got @ [ Thr e ]) }, got)

let recorder_exits () : exitv list kops * got list ref =
  let got = ref [] in
  ({ ret = (fun v -> got := !got @ [ Exits v ]); thr = (fun e -> got := !got @ [ Thr e ]) }, got)

(* Park `f` behind `token` on a captured continuation that records its answer: the shape
   `Parked.withGuard token` with `Suspended k` (DIVERGENCE 1). *)
let park_recorder (f : run_fiber) (token : int) : answer list ref =
  let got = ref [] in
  f.frame.control <- Suspended { ktoken = token; kresume = (fun a -> got := !got @ [ a ]) };
  f.parked <- WithGuard token;
  f.pending <-
    f.pending @ [ { token; waiting_on = None; remaining = 0; collected = []; resume_with = Rvoid } ];
  f.running <- false;
  got

let trace_after m (n : int) : run_event list =
  let rec drop k = function [] -> [] | _ :: r when k > 0 -> drop (k - 1) r | l -> l in
  drop n m.trace

let count_events (p : run_event -> bool) m : int = List.length (List.filter p m.trace)

let has_event (p : run_event -> bool) m : bool = List.exists p m.trace

let the_cause = cause_fail 7

let handle_of = function Vhandle h -> h | _ -> -1

(* An open sequential scope `key` in the store, seeded directly. *)
let seed_scope (key : int) : unit =
  scope_store_make store.scopes key Fssequential;
  if store.next_name <= key then store.next_name <- key + 1

let seed_closed_scope (key : int) : unit =
  seed_scope key;
  scope_store_close_state store.scopes key (Esuccess Vunit)

let scope_keys (key : int) : int list =
  match scope_store_entry_at store.scopes key with
  | Some e -> List.map fst (scope_finalizers e.scope)
  | None -> []

(* ---------------------------------------------------------------------- the clauses *)

let clauses : clause list =
  [
    (* ------------------------------------------- the run-loop top and the per-entry budget *)
    { name = "runloopTop_deferred"; lean = "Clauses.lean:42"; census = [ "checkpoint.runloop-top" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let f = add_fiber m in
              f.frame.deferred_interrupt <- true;
              f.frame.interrupted_cause <- Some the_cause;
              let r = runloop_top f in
              all [ expect (r = Some the_cause) "the pending cause is not the failure installed";
                    expect (not f.frame.deferred_interrupt) "deferredInterrupt not cleared" ]),
            fun m _ e ->
              (* `interruptDeferred` names the fiber the next loop top will fail. *)
              match e with
              | InterruptDeferred t -> (
                match fiber_opt m t with
                | Some f ->
                  expect (f.frame.deferred_interrupt && f.frame.interrupted_cause <> None)
                    "interruptDeferred on a fiber with no pending cause"
                | None -> ok)
              | _ -> ok ) };
    { name = "runloopTop_idle"; lean = "Clauses.lean:50"; census = [ "checkpoint.runloop-top" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let before = (f.frame.interruptible, f.frame.interrupted_cause, f.current_op_count) in
            let r = runloop_top f in
            all [ expect (r = None) "an idle top installed a failure";
                  expect (before = (f.frame.interruptible, f.frame.interrupted_cause, f.current_op_count))
                    "an idle top changed the fiber" ]) };
    { name = "runloopTop_clears"; lean = "Clauses.lean:55"; census = [ "checkpoint.runloop-top" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m and g = add_fiber m in
            f.frame.deferred_interrupt <- true;
            ignore (runloop_top f);
            ignore (runloop_top g);
            expect ((not f.frame.deferred_interrupt) && not g.frame.deferred_interrupt)
              "deferredInterrupt survives the top") };
    { name = "countOp_count"; lean = "Clauses.lean:61"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.current_op_count <- 4;
            count_op f;
            expect (f.current_op_count = 5) "countOp is not +1") };
    { name = "drive_evaluate_enters"; lean = "Clauses.lean:66"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let seen = ref None in
              let f = add_fiber m in
              f.frame.control <-
                Program (fun () -> seen := Some (f.running, f.current_op_count, f.parked); Vunit);
              f.current_op_count <- 9;
              f.parked <- WithGuard 3;
              exec m fuel (Cevaluate f.id);
              all [ expect (!seen = Some (true, 0, NotParked)) "entry did not set running/count 0/unparked";
                    expect (List.nth_opt m.trace 0 = Some (Started f.id)) "no `started` at entry" ]),
            fun m _ e ->
              match e with
              | Started id -> (
                match fiber_opt m id with
                | Some f -> expect (f.running && f.current_op_count = 0) "`started` with a stale counter"
                | None -> fail "`started` on an unknown fiber")
              | _ -> ok ) };
    { name = "drive_evaluate_exited"; lean = "Clauses.lean:79"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let ran = ref false in
            let f = add_fiber ~program:(fun () -> ran := true; Vunit) m in
            f.exit_ <- Some (Esuccess Vunit);
            exec m fuel (Cevaluate f.id);
            all [ expect (not !ran) "an exited fiber was evaluated";
                  expect (m.trace = []) "an exited fiber's evaluate emitted" ]) };
    { name = "drive_evaluate_running"; lean = "Clauses.lean:87"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let ran = ref false in
            let f = add_fiber ~program:(fun () -> ran := true; Vunit) m in
            f.running <- true;
            exec m fuel (Cevaluate f.id);
            all [ expect (not !ran) "a running fiber was re-entered";
                  expect (m.trace = []) "a running fiber's evaluate emitted" ]) };
    { name = "yieldVerdict_default"; lean = "Clauses.lean:96"; census = [ "scheduler.should-yield" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.max_ops_before_yield <- 3;
            f.current_op_count <- 2;
            let a = yield_verdict f in
            f.current_op_count <- 3;
            let b = yield_verdict f in
            expect ((not a) && b) "the default verdict is not `count >= budget`") };
    { name = "yieldVerdict_override"; lean = "Clauses.lean:101"; census = [ "scheduler.should-yield" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.max_ops_before_yield <- 3;
            f.current_op_count <- 0;
            f.yield_override <- Some true;
            let a = yield_verdict f in
            f.current_op_count <- 9;
            f.yield_override <- Some false;
            let b = yield_verdict f in
            expect (a && not b) "the override does not answer instead") };
    { name = "injectYield_latched"; lean = "Clauses.lean:107"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.max_ops_before_yield <- 1;
            f.current_op_count <- 5;
            f.yielding <- true;
            let fired = inject_yield m f (fun () -> ()) (fun _ -> ()) in
            expect ((not fired) && f.parked = NotParked) "a second injection in one entry") };
    { name = "injectYield_prevented"; lean = "Clauses.lean:113"; census = [ "scheduler.prevent-yield-default" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.max_ops_before_yield <- 1;
            f.current_op_count <- 5;
            f.prevent_yield <- true;
            let fired = inject_yield m f (fun () -> ()) (fun _ -> ()) in
            expect ((not fired) && f.parked = NotParked) "`PreventSchedulerYield` did not bypass") };
    { name = "injectYield_no_verdict"; lean = "Clauses.lean:118"; census = [ "scheduler.should-yield" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.max_ops_before_yield <- 10;
            f.current_op_count <- 1;
            let fired = inject_yield m f (fun () -> ()) (fun _ -> ()) in
            expect ((not fired) && f.parked = NotParked) "an injection without a verdict") };
    { name = "injectYield_fires"; lean = "Clauses.lean:125"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let f = add_fiber m in
              f.max_ops_before_yield <- 2;
              f.current_op_count <- 2;
              f.yield_override <- Some true;
              let token = m.next_token in
              let fired = inject_yield m f (fun () -> ()) (fun _ -> ()) in
              let task = match f.dispatcher.buckets with [ { priority = 0; tasks = [ t ] } ] -> Some t | _ -> None in
              all [ expect fired "no injection on the verdict";
                    expect (f.yielding) "the latch is not set";
                    expect (f.parked = WithGuard token) "not parked behind the fresh guard";
                    expect (f.yield_override = None) "the override was not consumed";
                    expect (task = Some (Tresume (f.id, token, Aval Vunit)))
                      "the resume is not queued at priority 0 on the fiber's own dispatcher";
                    expect (m.next_token = token + 1) "the token counter did not advance";
                    expect (m.trace = [ YieldInjected (f.id, 2); ScheduledTask (f.id, 0, Tresume (f.id, token, Aval Vunit)); ParkedOn (f.id, token) ])
                      "the injection's events differ" ]),
            fun m _ e ->
              match e with
              | YieldInjected (id, at_op) -> (
                match fiber_opt m id with
                | Some f -> expect (f.yielding && at_op = f.current_op_count) "yieldInjected without the latch or at another count"
                | None -> fail "yieldInjected on an unknown fiber")
              | _ -> ok ) };
    { name = "iteration_injected"; lean = "Clauses.lean:145"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.max_ops_before_yield <- 1;
            let ran = ref false in
            let ko, _ = recorder () in
            guard m f ko (fun () -> ran := true);
            all [ expect (not !ran) "the primitive ran in the iteration that injected";
                  expect (f.parked <> NotParked) "the injecting iteration did not park" ]) };
    { name = "iteration_evaluates"; lean = "Clauses.lean:153"; census = [ "rule.budget-per-runloop-entry" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let ran = ref false in
            let ko, _ = recorder () in
            guard m f ko (fun () -> ran := true);
            all [ expect !ran "the primitive did not run";
                  expect (f.current_op_count = 1) "the counter did not count the iteration";
                  expect (f.parked = NotParked) "an iteration under budget parked" ]) };
    (* ------------------------------------------- the dispatcher *)
    { name = "Dispatcher.enqueue_same_bucket"; lean = "Clauses.lean:163"; census = [ "scheduler.priority-buckets" ];
      check =
        Pure
          (fun () ->
            let d = { buckets = [ { priority = 2; tasks = [ Tstart 1 ] } ]; armed = false } in
            Dispatcher.enqueue d 2 (Tstart 2);
            expect (List.map (fun b -> (b.priority, b.tasks)) d.buckets = [ (2, [ Tstart 1; Tstart 2 ]) ])
              "a task did not join its bucket at the end") };
    { name = "Dispatcher.enqueue_lower_priority"; lean = "Clauses.lean:171"; census = [ "scheduler.priority-buckets" ];
      check =
        Pure
          (fun () ->
            let d = { buckets = [ { priority = 5; tasks = [ Tstart 1 ] } ]; armed = false } in
            Dispatcher.enqueue d 2 (Tstart 2);
            expect (List.map (fun b -> (b.priority, b.tasks)) d.buckets = [ (2, [ Tstart 2 ]); (5, [ Tstart 1 ]) ])
              "a lower priority did not open a bucket in front") };
    { name = "Dispatcher.enqueue_empty"; lean = "Clauses.lean:178"; census = [ "scheduler.priority-buckets" ];
      check =
        Pure
          (fun () ->
            let d = Dispatcher.empty () in
            Dispatcher.enqueue d 3 (Tstart 7);
            expect (List.map (fun b -> (b.priority, b.tasks)) d.buckets = [ (3, [ Tstart 7 ]) ])
              "the empty dispatcher did not take the task as its one bucket") };
    { name = "Dispatcher.enqueue_arms"; lean = "Clauses.lean:184"; census = [ "scheduler.dispatcher-arming" ];
      check =
        Both
          ( (fun () ->
              let d = Dispatcher.empty () in
              Dispatcher.enqueue d 0 (Tstart 1);
              let a = d.armed in
              Dispatcher.enqueue d 0 (Tstart 2);
              expect (a && d.armed) "enqueue did not arm, or did not stay armed"),
            fun m _ e ->
              match e with
              | ScheduledTask (owner, _, _) -> (
                match fiber_opt m owner with
                | Some o -> expect o.dispatcher.armed "scheduledTask on a disarmed dispatcher"
                | None -> fail "scheduledTask on an unknown owner")
              | _ -> ok ) };
    { name = "Dispatcher.drain_eq"; lean = "Clauses.lean:189"; census = [ "scheduler.run-tasks-drain-once" ];
      check =
        Pure
          (fun () ->
            let d = { buckets = [ { priority = 0; tasks = [ Tstart 1; Tstart 2 ] }; { priority = 4; tasks = [ Tstart 3 ] } ]; armed = true } in
            let tasks = Dispatcher.drain d in
            all [ expect (tasks = [ Tstart 1; Tstart 2; Tstart 3 ]) "the snapshot is not in bucket order";
                  expect (d.buckets = []) "the drained dispatcher is not idle" ]) };
    { name = "Dispatcher.drain_disarms"; lean = "Clauses.lean:194"; census = [ "scheduler.run-tasks-drain-once" ];
      check =
        Pure
          (fun () ->
            let d = { buckets = [ { priority = 0; tasks = [ Tstart 1 ] } ]; armed = true } in
            ignore (Dispatcher.drain d);
            expect (not d.armed) "the drained dispatcher is still armed") };
    { name = "fire_unknown"; lean = "Clauses.lean:197"; census = [ "scheduler.host-loop" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            fire m fuel 99;
            expect (m.trace = [] && m.fibers = []) "a fire on an unknown owner did something") };
    { name = "fire_eq"; lean = "Clauses.lean:206"; census = [ "scheduler.host-loop" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let o = add_fiber m in
              let c = add_fiber m in
              let t = add_fiber m in
              let got = park_recorder t 5 in
              Dispatcher.enqueue o.dispatcher 0 (Tstart c.id);
              Dispatcher.enqueue o.dispatcher 0 (Tresume (t.id, 5, Aval (Vnat 1)));
              fire m fuel o.id;
              let ran = List.filter_map (function RanTask (own, task) -> Some (own, task) | _ -> None) m.trace in
              all [ expect (ran = [ (o.id, Tstart c.id); (o.id, Tresume (t.id, 5, Aval (Vnat 1))) ])
                      "the snapshot did not run in order";
                    expect (List.nth_opt m.trace 1 = Some (Started c.id)) "a start task is not an `evaluate`";
                    expect (!got = [ Aval (Vnat 1) ]) "a resume task is not a `resume`";
                    expect (o.dispatcher.buckets = [] && not o.dispatcher.armed) "the owner's dispatcher was not drained" ]),
            fun m _ e ->
              match e with
              | RanTask (owner, _) -> (
                match fiber_opt m owner with
                | Some o -> expect (not o.dispatcher.armed) "ranTask while the owner is still armed: the drain was not taken once"
                | None -> fail "ranTask on an unknown owner")
              | _ -> ok ) };
    { name = "flushAll_idle"; lean = "Clauses.lean:223"; census = [ "scheduler.flush" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            ignore (add_fiber m);
            flush_all m fuel 10;
            expect (m.trace = []) "a flush with no armed dispatcher ran something") };
    { name = "flushAll_round"; lean = "Clauses.lean:231"; census = [ "scheduler.flush" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let a = add_fiber m and b = add_fiber m in
            let ca = add_fiber m and cb = add_fiber m in
            Dispatcher.enqueue b.dispatcher 0 (Tstart cb.id);
            Dispatcher.enqueue a.dispatcher 0 (Tstart ca.id);
            flush_all m fuel 10;
            let owners = List.filter_map (function RanTask (own, _) -> Some own | _ -> None) m.trace in
            expect (owners = [ a.id; b.id ]) "armed dispatchers were not fired in fiber order") };
    { name = "budget_defaults"; lean = "Clauses.lean:245"; census = [ "scheduler.max-ops-default" ];
      check =
        Pure
          (fun () ->
            expect (default_budget = 2048 && empty_ctx.max_ops_before_yield = 2048 && not empty_ctx.prevent_yield)
              "the budget defaults are not 2048 / false") };
    (* ------------------------------------------- yield now and the resume guard *)
    { name = "evaluatePrim_yieldNowWith"; lean = "Clauses.lean:256"; census = [ "scheduler.yield-now-resume-guard" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let token = m.next_token in
            let ko, _ = recorder () in
            arm_yield m f 3 ko;
            let task = match f.dispatcher.buckets with [ { priority = 3; tasks = [ t ] } ] -> Some t | _ -> None in
            all [ expect (f.parked = WithGuard token) "not parked behind the fresh guard";
                  expect (task = Some (Tresume (f.id, token, Aval Vunit))) "the resume is not queued at the given priority with the void success";
                  expect (m.next_token = token + 1) "the token counter did not advance" ]) };
    { name = "drive_loop_parked"; lean = "Clauses.lean:274"; census = [ "rule.yield-is-overloaded" ];
      check = Refused "`Cmd.loop` has no OCaml existence: `continue k` runs the fiber to its next `perform` (DIVERGENCE 2)" };
    { name = "drive_loop_continues"; lean = "Clauses.lean:288"; census = [ "rule.yield-is-overloaded" ];
      check = Refused "`Cmd.loop` has no OCaml existence (DIVERGENCE 2)" };
    { name = "drive_resume_wrong_token"; lean = "Clauses.lean:302"; census = [ "scheduler.yield-now-resume-guard" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let t = add_fiber m in
            let got = park_recorder t 5 in
            exec m fuel (Cresume (t.id, 4, Aval Vunit));
            all [ expect (!got = []) "a resume on the wrong token reached the continuation";
                  expect (t.parked = WithGuard 5 && m.trace = []) "a dropped resume changed the fiber" ]) };
    { name = "drive_resume_guard"; lean = "Clauses.lean:312"; census = [ "scheduler.yield-now-resume-guard" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let t = add_fiber m in
              let got = park_recorder t 5 in
              exec m fuel (Cresume (t.id, 5, Aval (Vnat 2)));
              all [ expect (!got = [ Aval (Vnat 2) ]) "the answer was not installed";
                    expect (t.parked = NotParked && t.pending = []) "the fiber was not unparked or its pending entry not dropped";
                    expect (m.trace = [ ResumedWith (t.id, 5, Aval (Vnat 2)); Started t.id ]) "the resume's events differ" ]),
            fun m _ e ->
              match e with
              | ResumedWith (id, token, _) -> (
                match fiber_opt m id with
                | Some t -> expect (t.parked = NotParked && not (List.exists (fun p -> p.token = token) t.pending))
                              "resumedWith while still parked or with the pending entry kept"
                | None -> fail "resumedWith on an unknown fiber")
              | _ -> ok ) };
    { name = "drive_resume_not_parked"; lean = "Clauses.lean:326"; census = [ "scheduler.yield-now-resume-guard" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let t = add_fiber m in
            let got = park_recorder t 5 in
            t.parked <- NotParked;
            exec m fuel (Cresume (t.id, 5, Aval Vunit));
            expect (!got = [] && m.trace = []) "a resume on an unparked fiber was not dropped") };
    (* ------------------------------------------- the interrupt entry *)
    { name = "interruptRecord_exited"; lean = "Clauses.lean:336"; census = [ "interrupt.unsafe-entry" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.exit_ <- Some (Esuccess Vunit);
            let apply = interrupt_record m (Some 0) [] f in
            expect ((not apply) && f.frame.interrupted_cause = None) "an interrupt after the exit did something") };
    { name = "interruptRecord_records"; lean = "Clauses.lean:354"; census = [ "rule.record-and-apply-separate" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let f = add_fiber m in
              f.running <- true;
              ignore (interrupt_record m (Some 0) [ "extra" ] f);
              let expected = cause_annotate (cause_interrupt (Some 0)) (!interp.stack_annotations f.id @ [ "extra" ]) in
              expect (f.frame.interrupted_cause = Some expected) "the recorded cause is not the interruptor's, annotated by the target's stack and the caller"),
            fun m _ e ->
              match e with
              | InterruptRecorded (who, target) -> (
                match fiber_opt m target with
                | Some t when t.exit_ = None -> (
                  match t.frame.interrupted_cause with
                  | Some c -> expect (List.exists (fun r -> r = Rinterrupt who) c.reasons) "interruptRecorded without the interruptor's reason"
                  | None -> fail "interruptRecorded but no cause recorded")
                | _ -> ok)
              | _ -> ok ) };
    { name = "interruptRecord_accumulates"; lean = "Clauses.lean:365"; census = [ "interrupt.accumulate" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.running <- true;
            f.frame.interrupted_cause <- Some the_cause;
            ignore (interrupt_record m (Some 3) [] f);
            let fresh = cause_annotate (cause_interrupt (Some 3)) (!interp.stack_annotations f.id) in
            expect (f.frame.interrupted_cause = Some (cause_combine the_cause fresh)) "successive interruptors do not combine") };
    { name = "interruptRecord_running_defers"; lean = "Clauses.lean:378"; census = [ "rule.record-and-apply-separate" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let f = add_fiber m in
              f.running <- true;
              let apply = interrupt_record m (Some 0) [] f in
              expect ((not apply) && f.frame.deferred_interrupt) "a running interruptible fiber was not deferred"),
            fun m _ e ->
              match e with
              | InterruptDeferred t -> (
                match fiber_opt m t with
                | Some f -> expect (f.running && f.frame.deferred_interrupt) "interruptDeferred on an idle fiber"
                | None -> fail "interruptDeferred on an unknown fiber")
              | _ -> ok ) };
    { name = "interruptRecord_idle_applies"; lean = "Clauses.lean:390"; census = [ "rule.record-and-apply-separate" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.parked <- WithGuard 2;
            f.pending <- [ { token = 2; waiting_on = None; remaining = 0; collected = []; resume_with = Rvoid } ];
            let apply = interrupt_record m (Some 0) [] f in
            let expected = cause_annotate (cause_interrupt (Some 0)) (!interp.stack_annotations f.id) in
            all [ expect apply "an idle interruptible fiber was not applied now";
                  expect (f.parked = NotParked && f.pending = []) "not unparked / pending not dropped";
                  expect (f.frame.control = Failing expected) "the current primitive is not the accumulated cause's failure" ]) };
    { name = "interruptRecord_masked"; lean = "Clauses.lean:404"; census = [ "rule.record-and-apply-separate" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber ~interruptible:false m in
            let apply = interrupt_record m (Some 0) [] f in
            all [ expect (not apply) "a masked fiber was applied";
                  expect (f.frame.interrupted_cause <> None) "a masked fiber did not record";
                  expect ((not f.frame.deferred_interrupt) && (match f.frame.control with Program _ -> true | _ -> false))
                    "a masked fiber's frame changed" ]) };
    { name = "interruptRecord_parked_applies"; lean = "Clauses.lean:419"; census = [ "checkpoint.post-yield-cancel" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let got = park_recorder f 1 in
            let apply = interrupt_record m (Some 0) [] f in
            exec m fuel (Cevaluate f.id);
            all [ expect (apply && f.parked = NotParked && f.pending = []) "a parked fiber was not applied now";
                  expect (match !got with [ Acause _ ] -> true | _ -> false) "the park was not discontinued with the cause" ]) };
    (* ------------------------------------------- fork *)
    { name = "spawn_eq"; lean = "Clauses.lean:447"; census = [ "fork.unsafe" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let p = add_fiber m in
              let next = m.next_id in
              let c = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
              all [ expect (c = next && m.next_id = next + 1) "the child does not take the next id";
                    expect (List.map (fun f -> f.id) m.fibers = [ p.id; c ]) "the child is not appended";
                    expect (p.children = [ c ]) "the parent does not track the child";
                    expect (m.trace = [ Forked (p.id, c, false) ]) "the fork's event differs" ]),
            fun m _ e ->
              match e with
              | Forked (parent, child, daemon) -> (
                match (fiber_opt m parent, fiber_opt m child) with
                | Some p, Some _ -> expect (List.mem child p.children = not daemon) "forked: tracking disagrees with daemon"
                | _ -> fail "forked names an unknown fiber")
              | _ -> ok ) };
    { name = "spawnChild_fields"; lean = "Clauses.lean:458"; census = [ "fork.unsafe" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let p = add_fiber ~interruptible:false m in
            let mk mode daemon = spawn_child m p (fun () -> Vunit) { start_immediately = true; daemon; mask_mode = mode } in
            let a = mk Minterruptible false and b = mk Muninterruptible false and c = mk Minherit true in
            all [ expect (a.id = m.next_id) "the child's id is not the next id";
                  expect (a.frame.interruptible && (not b.frame.interruptible) && not c.frame.interruptible) "the mask by options differs";
                  expect (a.observers = [ UntrackChild p.id ] && c.observers = []) "the untrack observer disagrees with daemon" ]) };
    { name = "spawn_daemon_untracked"; lean = "Clauses.lean:474"; census = [ "rule.only-fork-child-tracks" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let p = add_fiber m in
            ignore (spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:true));
            expect (p.children = []) "a daemon joined the parent's children") };
    { name = "start_eq"; lean = "Clauses.lean:483"; census = [ "rule.start-is-asymmetric" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let p = add_fiber m in
            let now = start m p 7 ~immediately:true in
            let later = start m p 8 ~immediately:false in
            all [ expect (now = [ Cevaluate 7 ]) "an immediate start is not an `evaluate` command";
                  expect (later = [] && m.trace = [ ScheduledTask (p.id, 0, Tstart 8) ]) "a deferred start is not a start task at priority 0";
                  expect (List.map (fun b -> (b.priority, b.tasks)) p.dispatcher.buckets = [ (0, [ Tstart 8 ]) ]) "the deferred start is not on the parent's dispatcher" ]) };
    { name = "runFork_eq"; lean = "Clauses.lean:494"; census = [ "entry.run-fork-with" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let seen = ref false in
            let root = run_fork m fuel (fun () -> seen := true; Vnat 1) in
            let f = fiber_exn m root in
            all [ expect (root = 0 && m.next_id = 1) "the root is not the next id";
                  expect (f.frame.interruptible && f.max_ops_before_yield = !max_ops_before_yield) "the root's mask or budget differ";
                  expect (!seen && List.nth_opt m.trace 0 = Some (Started root)) "the root was not evaluated at once" ]) };
    (* ------------------------------------------- join and await *)
    { name = "evaluatePrim_join_done"; lean = "Clauses.lean:508"; census = [ "fork.join" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m and t = add_fiber m in
            t.exit_ <- Some (Efailure the_cause);
            let ko1, got1 = recorder () in
            arm_join_on m f t.id MAwait ko1;
            let ko2, got2 = recorder () in
            arm_join_on m f t.id MJoin ko2;
            all [ expect (!got1 = [ Ret Vnone ]) "`await` on an exited target is not the exit as a value";
                  expect (match !got2 with [ Thr (Einterrupt_exn c) ] -> c = the_cause | _ -> false) "`join` on an exited target is not the exit as an effect";
                  expect (f.parked = NotParked && m.trace = []) "a join on an exited target parked" ]) };
    { name = "evaluatePrim_join_live"; lean = "Clauses.lean:522"; census = [ "fork.await" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let f = add_fiber m and t = add_fiber m in
              let token = m.next_token in
              let ko, got = recorder () in
              arm_join_on m f t.id MAwait ko;
              all [ expect (t.observers = [ ResumeAwait (f.id, token, MAwait) ]) "no observer on the live target";
                    expect (f.parked = WithGuard token && m.next_token = token + 1) "not parked behind a fresh guard";
                    expect (m.trace = [ ParkedOn (f.id, token) ] && !got = []) "a join on a live target answered" ]),
            fun m _ e ->
              match e with
              | ParkedOn (id, token) -> (
                match fiber_opt m id with
                | Some f -> expect (f.parked = WithGuard token) "parkedOn without the guard"
                | None -> fail "parkedOn on an unknown fiber")
              | _ -> ok ) };
    { name = "evaluatePrim_join_unknown"; lean = "Clauses.lean:539"; census = [ "fork.join" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let ko, got = recorder () in
            arm_join_on m f 42 MJoin ko;
            expect (m.stuck = Some (UnknownFiber 42) && !got = []) "a join on an unknown handle is not stuck") };
    (* ------------------------------------------- children *)
    { name = "withFiber_snapshotChildren"; lean = "Clauses.lean:552"; census = [ "fork.await-all-children" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let a = spawn m f (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            let b = spawn m f (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            let ko, got = recorder () in
            arm_snapshot_children m f ko;
            let expected = Vlist [ Vhandle (handle_index "fiber" a); Vhandle (handle_index "fiber" b) ] in
            expect (!got = [ Ret expected ]) "the snapshot is not the tracked children as a value") };
    { name = "withFiber_awaitNewChildren"; lean = "Clauses.lean:560"; census = [ "fork.await-all-children" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let a = spawn m f (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            let b = spawn m f (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            let ko, _ = recorder () in
            arm_await_new_children m f (Vlist [ Vhandle (handle_index "fiber" a) ]) ko;
            let has_countdown g = List.exists (function Countdown (w, _) -> w = f.id | _ -> false) (fiber_exn m g).observers in
            expect ((not (has_countdown a)) && has_countdown b) "the countdown is not over the children added since the snapshot only") };
    { name = "withFiber_runIn"; lean = "Clauses.lean:572"; census = [ "fork.fiber-run-in" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            seed_scope 0;
            let f = add_fiber m and t = add_fiber m in
            let ko, got = recorder () in
            arm_run_in m f t.id 0 100 ko;
            all [ expect (!got = [ Ret Vunit ]) "the caller does not answer void";
                  expect (List.mem (DropScopeFinalizer (0, 100)) t.observers) "the run-in fiber carries no key-dropping observer";
                  expect (scope_keys 0 = [ 100 ]) "the keyed finalizer was not registered";
                  expect (m.trace = [ ScopeLinked (0, 100, t.id) ]) "the link's event differs" ]) };
    { name = "linkScope_closed"; lean = "Clauses.lean:585"; census = [ "fork.fiber-run-in" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            seed_closed_scope 1;
            let t = add_fiber m in
            let cmds = link_scope m 0 1 100 t.id (Some 0) [ "caller" ] in
            all [ expect (cmds = [ Cevaluate t.id ]) "the closed link did not apply the interrupt now";
                  expect (m.trace = [ ScopeClosedOnLink (1, t.id); InterruptRecorded (Some 0, t.id) ]) "the closed link's events differ";
                  expect (match t.frame.interrupted_cause with Some c -> List.mem "caller" c.annotations | None -> false) "the caller's annotations are missing" ]) };
    { name = "linkScope_unknown"; lean = "Clauses.lean:598"; census = [ "fork.fiber-run-in" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let t = add_fiber m in
            let cmds = link_scope m 0 99 100 t.id (Some 0) [] in
            expect (cmds = [] && m.stuck = Some (UnknownScope 99)) "an unknown scope did not halt the machine") };
    (* ------------------------------------------- the runtime entries *)
    { name = "runCallback_eq"; lean = "Clauses.lean:609"; census = [ "entry.run-callback-with" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let root = run_callback m fuel (fun () -> Vnat 3) 77 in
            expect (has_event (fun e -> e = ObserverFired (root, Callback 77)) m) "the root does not carry the callback observer under its key") };
    { name = "fireObserver_callback"; lean = "Clauses.lean:622"; census = [ "entry.run-callback-with" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let cmds = fire_observer m 4 (Esuccess (Vnat 1)) [] (Callback 9) in
              expect (cmds = [] && m.trace = [ ObserverFired (4, Callback 9); CallbackEv (9, Esuccess (Vnat 1)) ]) "the callback observer's delivery differs"),
            fun m i e ->
              match e with
              | CallbackEv (key, _) ->
                expect (List.nth_opt m.trace (i - 1) = Some (ObserverFired (List.length m.fibers - List.length m.fibers + (match List.nth_opt m.trace (i - 1) with Some (ObserverFired (f, _)) -> f | _ -> -1), Callback key)))
                  "callback not delivered by its observer"
              | _ -> ok ) };
    { name = "stepDecision_abort"; lean = "Clauses.lean:630"; census = [ "entry.abort-signal" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let t = add_fiber m in
            let got = park_recorder t 0 in
            step_decision m fuel (DinterruptFrom (None, [], t.id));
            all [ expect (List.nth_opt m.trace 0 = Some (InterruptRecorded (None, t.id))) "the abort is not an interrupt with no interruptor";
                  expect (match !got with [ Acause c ] -> List.mem (Rinterrupt None) c.reasons | _ -> false) "the abort did not apply now to the parked fiber" ]) };
    { name = "runSyncExit_exited"; lean = "Clauses.lean:644"; census = [ "entry.run-sync-exit-with" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            expect (run_sync_exit m fuel (fun () -> Vnat 3) = Esuccess (Vnat 3)) "the root's exit is not the answer") };
    { name = "runSyncExit_survives"; lean = "Clauses.lean:654"; census = [ "entry.async-fiber-error" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            expect (run_sync_exit m fuel (fun () -> Effect.perform (Op_never ())) = Efailure (cause_die "AsyncFiberError"))
              "a root that survives the flush is not the `AsyncFiberError` defect") };
    { name = "promiseOutcome_eq"; lean = "Clauses.lean:663"; census = [ "entry.run-promise-exit-with" ];
      check =
        Pure
          (fun () ->
            expect (promise_outcome (Esuccess (Vnat 1)) = Ok (Vnat 1) && promise_outcome (Efailure the_cause) = Error (Sq_error 7))
              "resolve/reject differ from the exit and its squash") };
    { name = "promiseOutcome_failure"; lean = "Clauses.lean:669"; census = [ "entry.run-promise-with" ];
      check =
        Pure
          (fun () ->
            expect (promise_outcome (Efailure (cause_combine (cause_fail 4) (cause_die "badName"))) = Error (Sq_error 4))
              "the squash is not the first typed failure") };
    (* ------------------------------------------- second pass: emit *)
    { name = "fiber?_emit"; lean = "Clauses.lean:684"; census = [];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            emit m [ Started 0 ];
            expect (match fiber_opt m f.id with Some g -> g == f | None -> false) "emit touched the fiber table") };
    { name = "race?_emit"; lean = "Clauses.lean:687"; census = [];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let before = m.races in
            emit m [ Started 0 ];
            expect (m.races == before) "emit touched the races") };
    { name = "state_emit"; lean = "Clauses.lean:690"; census = [];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let before = (store.refs, List.length store.scopes.entries, m.state.started) in
            emit m [ Started 0 ];
            expect (before = (store.refs, List.length store.scopes.entries, m.state.started)) "emit touched the store") };
    { name = "stuck_emit"; lean = "Clauses.lean:693"; census = [];
      check =
        Pure
          (fun () ->
            let m = setup () in
            halt m (UnknownScope 9);
            emit m [ Started 0 ];
            expect (m.stuck = Some (UnknownScope 9)) "emit touched the stuck marker") };
    (* ------------------------------------------- interruptEach *)
    { name = "interruptEach_nil"; lean = "Clauses.lean:715"; census = [ "fork.interrupt-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let cmds = interrupt_each m 0 [] [ CdrainDue ] in
            expect (cmds = [ CdrainDue ] && m.trace = []) "an empty request list recorded something") };
    { name = "interruptEach_cons"; lean = "Clauses.lean:722"; census = [ "fork.interrupt-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let who = add_fiber m in
            let a = add_fiber m and b = add_fiber m in
            ignore (park_recorder a 0);
            b.running <- true;
            let cmds = interrupt_each m who.id [ a.id; 99; b.id ] [] in
            all [ expect (m.trace = [ InterruptRecorded (Some who.id, a.id); InterruptRecorded (Some who.id, b.id) ]) "the requests did not run in list order, skipping the unknown";
                  expect (cmds = [ Cevaluate a.id ]) "only the target that applies now is queued" ]) };
    { name = "interruptEach_known"; lean = "Clauses.lean:735"; census = [ "fork.interrupt-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let who = add_fiber m in
            let a = add_fiber m in
            a.running <- true;
            ignore (interrupt_each m who.id [ a.id ] []);
            let expected = cause_annotate (cause_interrupt (Some who.id)) (!interp.stack_annotations a.id) in
            expect (a.frame.interrupted_cause = Some expected) "a known target is not recorded with `who` and no extra annotations") };
    (* ------------------------------------------- the exit path *)
    { name = "exitFiber_eq"; lean = "Clauses.lean:785"; census = [ "rule.children-interrupted-after-exit" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            m.middleware_installed <- true;
            let p = add_fiber m in
            let c = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            ignore (park_recorder (fiber_exn m c) 0);
            let n = List.length m.trace in
            ignore (exit_fiber m p (Esuccess Vunit));
            let a = has_event (function ChildrenInterrupted (x, _) -> x = p.id | _ -> false) m in
            let m2 = setup () in
            let q = add_fiber m2 in
            ignore (exit_fiber m2 q (Esuccess Vunit));
            let b = m2.trace = [ Exited (q.id, Esuccess Vunit) ] in
            all [ expect (a && List.length (trace_after m n) > 0) "with the middleware and tracked children the children clause did not run";
                  expect b "without them the exit was not stored at once" ]) };
    { name = "exitFiber_no_middleware"; lean = "Clauses.lean:794"; census = [ "fork.child" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let p = add_fiber m in
            let c = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            ignore (park_recorder (fiber_exn m c) 0);
            ignore (exit_fiber m p (Esuccess Vunit));
            all [ expect (p.exit_ = Some (Esuccess Vunit)) "the exit was not stored at once";
                  expect ((fiber_exn m c).exit_ = None && not (has_event (function InterruptRecorded _ -> true | _ -> false) m)) "the children did not survive" ]) };
    { name = "exitFiber_no_children"; lean = "Clauses.lean:803"; census = [ "fork.detach" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            m.middleware_installed <- true;
            let p = add_fiber m in
            let d = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:true) in
            ignore (park_recorder (fiber_exn m d) 0);
            ignore (exit_fiber m p (Esuccess Vunit));
            expect (p.exit_ = Some (Esuccess Vunit) && (fiber_exn m d).exit_ = None) "a daemon child was reached by its parent's exit") };
    { name = "exitFiber_finalizing"; lean = "Clauses.lean:813"; census = [];
      check =
        Pure
          (fun () ->
            let m = setup () in
            m.middleware_installed <- true;
            let p = add_fiber m in
            ignore (spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false));
            p.finalizing <- Some (Esuccess (Vnat 1));
            ignore (exit_fiber m p (Efailure the_cause));
            expect (p.exit_ = Some (Efailure the_cause) && p.finalizing = None) "a finalizing fiber did not store the exit it is now given") };
    { name = "exitFiber_children"; lean = "Clauses.lean:821"; census = [ "rule.children-interrupted-after-exit" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              m.middleware_installed <- true;
              let p = add_fiber m in
              let c = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
              ignore (park_recorder (fiber_exn m c) 0);
              ignore (exit_fiber m p (Esuccess Vunit));
              expect (has_event (fun e -> e = ChildrenInterrupted (p.id, [ c ])) m && p.exit_ = None) "the children clause did not run"),
            fun m _ e ->
              match e with
              | ChildrenInterrupted (parent, children) -> (
                match fiber_opt m parent with
                | Some p -> expect (m.middleware_installed && p.children = children && p.exit_ = None) "childrenInterrupted without the middleware, or with other children, or after the exit"
                | None -> fail "childrenInterrupted on an unknown parent")
              | _ -> ok ) };
    { name = "exitStore_fiber"; lean = "Clauses.lean:830"; census = [ "fork.child" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            f.observers <- [ Callback 1; Callback 2 ];
            ignore (exit_store m f (Esuccess Vunit));
            expect (f.observers = []) "the observer list was not emptied") };
    { name = "exitStore_fields"; lean = "Clauses.lean:835"; census = [ "fork.child" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let f = add_fiber m in
              f.children <- [ 5 ];
              f.finalizing <- Some (Esuccess Vunit);
              ignore (park_recorder f 0);
              ignore (exit_store m f (Efailure the_cause));
              all [ expect (f.exit_ = Some (Efailure the_cause)) "exit not set";
                    expect (f.finalizing = None) "finalizing not cleared";
                    expect (f.frame.control = Ended) "the stack is not cleared";
                    expect (f.children = [] && f.parked = NotParked && f.pending = []) "children/parks not cleared";
                    expect (f.context = ()) "context not emptied" ]),
            fun m _ e ->
              match e with
              | Exited (id, exit_) -> (
                match fiber_opt m id with
                | Some f -> expect (f.exit_ = Some exit_ && f.children = [] && f.parked = NotParked && f.pending = [] && f.finalizing = None)
                              "exited with the fiber not stored as the exit path stores it"
                | None -> fail "exited on an unknown fiber")
              | _ -> ok ) };
    { name = "exitStore_fires"; lean = "Clauses.lean:850"; census = [ "fork.child" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let f = add_fiber m in
              f.observers <- [ ResumeAwait (7, 3, MAwait); Callback 9 ];
              let cmds = exit_store m f (Esuccess (Vnat 1)) in
              all [ expect (cmds = [ Cresume (7, 3, Aval (Vsome (Vnat 1))) ]) "the commands are not what the observers asked for";
                    expect (m.trace = [ Exited (f.id, Esuccess (Vnat 1)); ObserverFired (f.id, ResumeAwait (7, 3, MAwait)); ObserverFired (f.id, Callback 9); CallbackEv (9, Esuccess (Vnat 1)) ])
                      "the observers did not fire in index order after the stored exit" ]),
            fun m _ e ->
              match e with
              | ObserverFired (id, _) -> (
                match fiber_opt m id with
                | Some f -> expect (f.exit_ <> None) "an observer fired before its fiber's exit was stored"
                | None -> ok)
              | _ -> ok ) };
    { name = "exitInterruptChildren_eq"; lean = "Clauses.lean:859"; census = [ "rule.children-interrupted-after-exit" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let p = add_fiber m in
            let c = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            ignore (park_recorder (fiber_exn m c) 0);
            let n = List.length m.trace in
            let token = m.next_token in
            ignore (exit_interrupt_children m p (Esuccess Vunit));
            expect (trace_after m n = [ InterruptRecorded (Some p.id, c); ChildrenInterrupted (p.id, [ c ]); ParkedOn (p.id, token) ])
              "the children clause is not the interrupt fold, the event, then the countdown") };
    { name = "exitInterruptChildren_interrupts"; lean = "Clauses.lean:870"; census = [ "fork.detach" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let p = add_fiber m in
            let a = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            let b = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
            ignore (park_recorder (fiber_exn m a) 0);
            (fiber_exn m b).running <- true;
            let cmds = exit_interrupt_children m p (Esuccess Vunit) in
            expect (cmds = [ Cevaluate a ]) "the owed commands are not the fold's apply-now children in child order") };
    { name = "countdownPark_finalizing"; lean = "Clauses.lean:876"; census = [];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m and t = add_fiber m in
            f.finalizing <- Some (Esuccess (Vnat 2));
            ignore (countdown_park m f [ t.id ] Rvoid);
            ignore (countdown_park m f [] Rvoid);
            expect (f.finalizing = Some (Esuccess (Vnat 2))) "a countdown changed the finalizing flag") };
    { name = "exitInterruptChildren_finalizing"; lean = "Clauses.lean:886"; census = [ "rule.children-interrupted-after-exit" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let p = add_fiber m in
              let c = spawn m p (fun () -> Vunit) (fixture_fork_options ~daemon:false) in
              ignore (park_recorder (fiber_exn m c) 0);
              ignore (exit_interrupt_children m p (Esuccess (Vnat 3)));
              expect (p.finalizing = Some (Esuccess (Vnat 3))) "the parent does not remember the exit it is finalizing"),
            fun m _ e ->
              match e with
              | ParkedOn (id, _) -> (
                match fiber_opt m id with
                | Some f when has_event (function ChildrenInterrupted (x, _) -> x = id | _ -> false) m && f.exit_ = None ->
                  expect (f.finalizing <> None) "the exit path parked without remembering its exit"
                | _ -> ok)
              | _ -> ok ) };
    { name = "resumePrim_continueWith"; lean = "Clauses.lean:894"; census = [ "rule.children-interrupted-after-exit" ];
      check =
        Pure
          (fun () ->
            (* DIVERGENCE 1: the restoring name applied to the collected exits is, on this
               stack, the restored exit delivered directly. *)
            expect (resume_prim (RcontinueWith (Esuccess (Vnat 4))) [ Esuccess Vunit ] = Aval (Vnat 4)
                    && resume_prim (RcontinueWith (Efailure the_cause)) [] = Acause the_cause)
              "the finished countdown does not continue with the restored exit") };
    { name = "stepDecision_installMiddleware"; lean = "Clauses.lean:901"; census = [ "fork.child" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            step_decision m fuel DinstallMiddleware;
            expect (m.middleware_installed && m.trace = []) "installing the middleware is not a flag") };
    { name = "fireObserver_resumeAwait"; lean = "Clauses.lean:908"; census = [ "fork.child" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let cmds = fire_observer m 4 (Efailure the_cause) [ CdrainDue ] (ResumeAwait (2, 6, MJoin)) in
            expect (cmds = [ CdrainDue; Cresume (2, 6, Acause the_cause) ] && m.trace = [ ObserverFired (4, ResumeAwait (2, 6, MJoin)) ])
              "the awaiter is not resumed with the exit in its mode, as a command") };
    { name = "fireObserver_untrackChild"; lean = "Clauses.lean:917"; census = [ "rule.only-fork-child-tracks" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let p = add_fiber m in
              p.children <- [ 3; 4 ];
              let cmds = fire_observer m 3 (Esuccess Vunit) [] (UntrackChild p.id) in
              expect (cmds = [] && p.children = [ 4 ]) "the child was not removed from its parent"),
            fun m _ e ->
              match e with
              | ObserverFired (id, UntrackChild parent) -> (
                match fiber_opt m parent with
                | Some p -> expect (p.exit_ <> None || List.mem id p.children) "untrackChild fired for a child a live parent did not track"
                | None -> ok)
              | _ -> ok ) };
    { name = "fireObserver_dropScopeFinalizer"; lean = "Clauses.lean:926"; census = [ "fork.in" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            seed_scope 0;
            ignore (scope_store_add_finalizer store.scopes 0 100 (FininterruptFiber (1, true)));
            ignore (scope_store_add_finalizer store.scopes 0 101 (FininterruptFiber (2, true)));
            let cmds = fire_observer m 1 (Esuccess Vunit) [] (DropScopeFinalizer (0, 100)) in
            expect (cmds = [] && scope_keys 0 = [ 101 ] && m.stuck = None) "the keyed finalizer was not dropped from the scope") };
    { name = "fireObserver_countdown_last"; lean = "Clauses.lean:937"; census = [ "fork.interrupt-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let w = add_fiber m in
            w.parked <- WithGuard 2;
            w.pending <- [ { token = 2; waiting_on = None; remaining = 1; collected = [ Esuccess (Vnat 1) ]; resume_with = RexitsValue } ];
            let cmds = fire_observer m 8 (Efailure the_cause) [] (Countdown (w.id, 2)) in
            let p = List.hd w.pending in
            all [ expect (cmds = [ Cresume (w.id, 2, Aexits [ Esuccess (Vnat 1); Efailure the_cause ]) ]) "the last target does not resume the awaiter with every collected exit in completion order";
                  expect (p.remaining = 0 && p.collected = [ Esuccess (Vnat 1); Efailure the_cause ]) "the pending entry was not closed" ]) };
    { name = "fireObserver_countdown_more"; lean = "Clauses.lean:954"; census = [ "fork.interrupt-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let w = add_fiber m in
            w.parked <- WithGuard 2;
            w.pending <- [ { token = 2; waiting_on = None; remaining = 2; collected = []; resume_with = RexitsValue } ];
            let cmds = fire_observer m 8 (Esuccess (Vnat 5)) [] (Countdown (w.id, 2)) in
            let p = List.hd w.pending in
            expect (cmds = [] && p.remaining = 1 && p.collected = [ Esuccess (Vnat 5) ] && w.parked = WithGuard 2)
              "before the last target the countdown did not collect and wait on") };
    (* ------------------------------------------- races *)
    { name = "fireObserver_raceCallback_settles"; lean = "Clauses.lean:995"; census = [ "fork.race-all" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let host = add_fiber m in
              let ko, _ = recorder () in
              arm_race_all_prog m host [ (fun () -> Effect.perform (Op_never ())); (fun () -> Effect.perform (Op_never ())) ] ko;
              let r = List.hd m.races in
              let e1 = List.nth r.live 0 and e2 = List.nth r.live 1 in
              let n = List.length m.trace in
              (fiber_exn m e1).exit_ <- Some (Esuccess (Vnat 1));
              r.live <- List.filter (fun x -> x <> e1) r.live;
              (* the entrant's exit fires its `raceCallback` observer; `race_complete` reads the
                 exit and the callback settles *)
              r.live <- e1 :: r.live;
              let _ = fire_observer m e1 (Esuccess (Vnat 1)) [] (RaceCallback r.rid) in
              all [ expect (r.settled && r.accepted = Some (Esuccess (Vnat 1))) "the first accepted callback did not settle";
                    expect (List.nth_opt (trace_after m n) 1 = Some (RaceSettled (r.rid, Esuccess (Vnat 1)))) "no raceSettled after the observer";
                    expect (has_event (fun e -> e = InterruptRecorded (Some host.id, e2)) m) "the live loser was not interrupted with the host's id";
                    expect (host.parked <> WithGuard r.rtoken && host.parked <> NotParked) "the host was not moved from its race guard to the countdown" ]),
            fun m _ e ->
              match e with
              | RaceSettled (rid, _) -> (
                match race_opt m rid with
                | Some r -> expect (r.settled && r.accepted <> None) "raceSettled on an unsettled race"
                | None -> fail "raceSettled on an unknown race")
              | _ -> ok ) };
    { name = "fireObserver_raceCallback_late"; lean = "Clauses.lean:1012"; census = [ "fork.race-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let host = add_fiber m in
            let ko, _ = recorder () in
            arm_race_all_prog m host [ (fun () -> Effect.perform (Op_never ())); (fun () -> Effect.perform (Op_never ())) ] ko;
            let r = List.hd m.races in
            let e2 = List.nth r.live 1 in
            r.settled <- true;
            r.accepted <- Some (Esuccess (Vnat 1));
            let n = List.length m.trace in
            let cmds = fire_observer m e2 (Efailure the_cause) [] (RaceCallback r.rid) in
            all [ expect (cmds = [] && trace_after m n = [ ObserverFired (e2, RaceCallback r.rid) ]) "a late callback did more than update the bookkeeping";
                  expect (r.accepted = Some (Esuccess (Vnat 1)) && not (List.mem e2 r.live)) "the first accepted result did not stay stable" ]) };
    { name = "fireObserver_raceCallback_pending"; lean = "Clauses.lean:1024"; census = [ "fork.race-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let host = add_fiber m in
            let ko, _ = recorder () in
            arm_race_all_prog m host [ (fun () -> Effect.perform (Op_never ())); (fun () -> Effect.perform (Op_never ())) ] ko;
            let r = List.hd m.races in
            let e1 = List.nth r.live 0 in
            let n = List.length m.trace in
            let cmds = fire_observer m e1 (Efailure the_cause) [] (RaceCallback r.rid) in
            all [ expect (cmds = [] && trace_after m n = [ ObserverFired (e1, RaceCallback r.rid) ]) "a loser before the winner did more than update the bookkeeping";
                  expect (r.accepted = None && (not r.settled) && r.failures = the_cause.reasons) "the frozen bookkeeping differs" ]) };
    { name = "drive_launch_skipped"; lean = "Clauses.lean:1036"; census = [ "fork.race-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let host = add_fiber m in
            let e = add_fiber m in
            m.races <- [ { rid = 0; host = host.id; rtoken = 0; settled = true; live = []; unstarted = [ e.id ]; remaining = 1; failures = []; accepted = Some (Esuccess (Vnat 1)); cleanup_needed = false } ];
            exec m fuel (Claunch (0, e.id));
            all [ expect (List.nth_opt m.trace 0 = Some (RaceSkipped (0, e.id)) && List.nth_opt m.trace 1 = Some (InterruptRecorded (Some host.id, e.id))) "a launch after acceptance was not skipped with the host's interrupt";
                  expect (match e.exit_ with Some (Efailure c) -> cause_has_interrupt c | _ -> false) "the skipped entrant was not interrupted and kept";
                  expect (List.exists (fun f -> f.id = e.id) m.fibers) "the skipped entrant was deleted" ]) };
    { name = "drive_launch_runs"; lean = "Clauses.lean:1051"; census = [ "fork.race-all" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let host = add_fiber m in
              let e = add_fiber ~program:(fun () -> Effect.perform (Op_never ())) m in
              let r = { rid = 0; host = host.id; rtoken = 0; settled = false; live = []; unstarted = [ e.id ]; remaining = 1; failures = []; accepted = None; cleanup_needed = false } in
              m.races <- [ r ];
              exec m fuel (Claunch (0, e.id));
              all [ expect (r.unstarted = [] && r.live = [ e.id ]) "the entrant did not move from unstarted to live";
                    expect (List.nth_opt m.trace 0 = Some (RaceLaunched (0, e.id)) && List.nth_opt m.trace 1 = Some (Started e.id)) "the launch did not evaluate the entrant" ]),
            fun m _ e ->
              match e with
              | RaceLaunched (rid, entrant) -> (
                match race_opt m rid with
                | Some r -> expect (List.mem entrant r.live && not (List.mem entrant r.unstarted)) "raceLaunched with the entrant not in the live set"
                | None -> fail "raceLaunched on an unknown race")
              | _ -> ok ) };
    (* ------------------------------------------- the fork arms *)
    { name = "withFiber_fork"; lean = "Clauses.lean:1066"; census = [ "fork.child" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let ko, got = recorder () in
            let child = m.next_id in
            arm_fork_prog m f (fun () -> Vunit) { start_immediately = false; daemon = false; mask_mode = Minherit } ko;
            let ko2, got2 = recorder () in
            let child2 = m.next_id in
            arm_fork_prog m f (fun () -> Vunit) { start_immediately = true; daemon = true; mask_mode = Minherit } ko2;
            all [ expect (!got = [ Ret (Vhandle (handle_index "fiber" child)) ] && !got2 = [ Ret (Vhandle (handle_index "fiber" child2)) ]) "the fork does not answer the child's handle";
                  expect (has_event (fun e -> e = ScheduledTask (f.id, 0, Tstart child)) m) "a deferred start is not a task";
                  expect ((fiber_exn m child2).exit_ <> None) "an immediate start did not run the child now";
                  expect (f.children = [ child ]) "tracking differs from the options" ]) };
    { name = "withFiber_forkIn"; lean = "Clauses.lean:1079"; census = [ "fork.in" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              seed_scope 0;
              let f = add_fiber m in
              let ko, got = recorder () in
              let child = m.next_id in
              arm_fork_in m f (fun () -> Effect.perform (Op_never ())) { start_immediately = true; daemon = false; mask_mode = Minherit } 0 100 ko;
              let c = fiber_exn m child in
              all [ expect (f.children = [] && c.observers = [ DropScopeFinalizer (0, 100) ]) "the child is not a daemon linked by the key-dropping observer";
                    expect (has_event (fun e -> e = ScopeLinked (0, 100, child)) m && scope_keys 0 = [ 100 ]) "the scope link is missing";
                    expect (!got = [ Ret (Vhandle (handle_index "fiber" child)) ] && has_event (fun e -> e = Started child) m) "the child was not started and answered" ]),
            fun m _ e ->
              match e with
              | ScopeLinked (scope, key, fiber) -> (
                match fiber_opt m fiber with
                | Some t -> expect (List.mem (DropScopeFinalizer (scope, key)) t.observers) "scopeLinked without the key-dropping observer"
                | None -> fail "scopeLinked on an unknown fiber")
              | _ -> ok ) };
    { name = "withFiber_forkScoped_ambient"; lean = "Clauses.lean:1097"; census = [ "fork.scoped" ];
      check = Refused "`χ = unit`: the avatar's context carries no ambient `Scope` service (A0 §18), so the `_ambient` arm has no instance" };
    { name = "withFiber_forkScoped_none"; lean = "Clauses.lean:1118"; census = [ "fork.scoped" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let ko, got = recorder () in
            arm_fork_scoped m f (fun () -> Vunit) (fixture_fork_options ~daemon:false) 100 ko;
            expect (match !got with [ Thr (Einterrupt_exn c) ] -> c = cause_die "notImplemented" | _ -> false) "without an ambient scope the fork is not the `notImplemented` defect") };
    { name = "linkScope_open"; lean = "Clauses.lean:1130"; census = [ "fork.in" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            seed_scope 0;
            let t = add_fiber m in
            let cmds = link_scope m 0 0 100 t.id (Some 0) [] in
            let fin = match scope_store_entry_at store.scopes 0 with Some e -> List.map snd (scope_finalizers e.scope) | None -> [] in
            all [ expect (cmds = [] && fin = [ FininterruptFiber (t.id, true) ]) "the keyed self-guarded finalizer was not registered";
                  expect (t.observers = [ DropScopeFinalizer (0, 100) ] && m.trace = [ ScopeLinked (0, 100, t.id) ]) "the observer or the event is missing" ]) };
    { name = "withFiber_closeScope"; lean = "Clauses.lean:1145"; census = [ "scope.close-sequential" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            seed_scope 0;
            let f = add_fiber m in
            let ko, got = recorder () in
            arm_close_scope m f 0 (Esuccess Vunit) ko;
            all [ expect (!current_program <> None) "the close program was not installed as the closer's next primitive";
                  expect (!got = [ Ret Vunit ]) "the closer was not resumed";
                  expect (scope_store_status store.scopes 0 = Some (Some (Esuccess Vunit))) "the state was not written first" ]) };
    { name = "withFiber_closeScope_unknown"; lean = "Clauses.lean:1155"; census = [ "scope.close-sequential" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let ko, got = recorder () in
            arm_close_scope m f 99 (Esuccess Vunit) ko;
            expect (m.stuck = Some (UnknownScope 99) && !got = []) "closing an unknown scope did not halt the machine") };
    { name = "withFiber_interrupt"; lean = "Clauses.lean:1165"; census = [ "fork.interrupt" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m and t = add_fiber ~program:(fun () -> Effect.perform (Op_never ())) m in
            t.running <- true;
            let ko, _ = recorder () in
            let token = m.next_token in
            arm_interrupt_then_join m f t.id (Some f.id) ko;
            expect (m.trace = [ InterruptRecorded (Some f.id, t.id); ParkedOn (f.id, token) ]) "`interrupt` is not record-with-the-caller then await") };
    { name = "withFiber_interruptScoped_self"; lean = "Clauses.lean:1173"; census = [ "fork.interrupt" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let ko, got = recorder () in
            arm_interrupt_scoped m f f.id ko;
            expect (!got = [ Ret Vunit ] && m.trace = [] && f.frame.interrupted_cause = None) "interrupting oneself through the scoped entry is not a void no-op") };
    { name = "withFiber_interruptScoped_other"; lean = "Clauses.lean:1182"; census = [ "fork.interrupt" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m and t = add_fiber m in
            t.running <- true;
            let ko, _ = recorder () in
            arm_interrupt_scoped m f t.id ko;
            expect (List.nth_opt m.trace 0 = Some (InterruptRecorded (Some f.id, t.id))) "another target through the scoped entry is not the plain interrupt") };
    { name = "interruptThenJoin_eq"; lean = "Clauses.lean:1192"; census = [ "fork.interrupt" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m and t = add_fiber ~program:(fun () -> Effect.perform (Op_never ())) m in
            exec m fuel (Cevaluate t.id);
            let n = List.length m.trace in
            let ko, got = recorder () in
            arm_interrupt_then_join m f t.id (Some f.id) ko;
            all [ expect (List.nth_opt (trace_after m n) 0 = Some (InterruptRecorded (Some f.id, t.id))) "the request is not delivered first";
                  expect (has_event (function ParkedOn (id, _) -> id = f.id | _ -> false) m) "the caller did not await the target on a countdown";
                  expect (match t.exit_ with Some (Efailure c) -> cause_has_interrupt c | _ -> false) "the evaluation the record owed now did not run";
                  expect (!got = [ Ret Vunit ]) "the caller was not resumed after the target's exit" ]) };
    { name = "interruptThenJoin_unknown"; lean = "Clauses.lean:1206"; census = [ "fork.interrupt" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let ko, got = recorder () in
            arm_interrupt_then_join m f 42 (Some f.id) ko;
            expect (m.stuck = Some (UnknownFiber 42) && !got = []) "an unknown target is not stuck") };
    { name = "withFiber_interruptAll"; lean = "Clauses.lean:1216"; census = [ "fork.interrupt-all" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let a = add_fiber m and b = add_fiber m in
            a.running <- true;
            b.running <- true;
            let ko, _ = recorder () in
            let token = m.next_token in
            arm_interrupt_all m f [ handle_index "fiber" a.id; handle_index "fiber" b.id ] ko;
            let evs = List.filter (function InterruptRecorded _ | ParkedOn _ -> true | _ -> false) m.trace in
            expect (evs = [ InterruptRecorded (Some f.id, a.id); InterruptRecorded (Some f.id, b.id); ParkedOn (f.id, token) ])
              "every request in list order, then one await over all of them: differs") };
    { name = "raceEntrant_options"; lean = "Clauses.lean:1241"; census = [ "rule.only-fork-child-tracks" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber ~interruptible:false m in
            let e = race_entrant m f 5 (fun () -> Vunit) in
            let c = fiber_exn m e in
            expect (f.children = [] && (not c.frame.interruptible) && c.observers = [ RaceCallback 5 ]) "the entrant is not an immediate daemon inheriting the host's mask with the race callback") };
    { name = "withFiber_raceAll"; lean = "Clauses.lean:1253"; census = [ "fork.race-all" ];
      check =
        Both
          ( (fun () ->
              let m = setup () in
              let host = add_fiber m in
              let ko, _ = recorder () in
              let token = m.next_token in
              arm_race_all_prog m host [ (fun () -> Effect.perform (Op_never ())); (fun () -> Effect.perform (Op_never ())) ] ko;
              let r = List.hd m.races in
              let evs = List.filter (function RaceStarted _ | RaceLaunched _ -> true | ParkedOn (id, _) -> id = host.id | _ -> false) m.trace in
              all [ expect (r.host = host.id && r.rtoken = token) "the race is not recorded with its host and guard";
                    expect (evs = [ RaceStarted (0, host.id, r.live); ParkedOn (host.id, token); RaceLaunched (0, List.nth r.live 0); RaceLaunched (0, List.nth r.live 1) ])
                      "the entrants do not exist before any launch, or the launches are not in entrant order";
                    let m2 = setup () in
                    let h2 = add_fiber m2 in
                    let ko2, got2 = recorder () in
                    arm_race_all_prog m2 h2 [] ko2;
                    expect (h2.parked = WithGuard 0 && !got2 = []) "the empty race did not stay parked" ]),
            fun m _ e ->
              match e with
              | RaceStarted (rid, host, _) -> (
                match (race_opt m rid, fiber_opt m host) with
                | Some r, Some _ -> expect (r.host = host && not r.settled) "raceStarted on a race with another host"
                | _ -> fail "raceStarted names an unknown race or host")
              | _ -> ok ) };
    (* ------------------------------------------- Async *)
    { name = "evaluatePrim_async_immediate"; lean = "Clauses.lean:1271"; census = [ "op.Async" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let cell = deferred_store_make store.deferreds in
            ignore (deferred_store_complete store.deferreds cell (CoofExit (Esuccess (Vnat 9))));
            let token = m.next_token in
            let ko, got = recorder () in
            arm_def_await m f (handle_index "deferred" cell.index) `Value ko;
            all [ expect (!got = [ Ret (Vnat 9) ]) "a register that answers at once did not install the answer";
                  expect (f.parked = NotParked && m.next_token = token + 1) "the fiber parked, or the token did not advance";
                  expect (store.deferreds.due = []) "the store's due resumes were not drained" ]) };
    { name = "evaluatePrim_async_parks"; lean = "Clauses.lean:1289"; census = [ "op.Async" ];
      check =
        Pure
          (fun () ->
            let m = setup () in
            let f = add_fiber m in
            let cell = deferred_store_make store.deferreds in
            let token = m.next_token in
            let ko, got = recorder () in
            arm_def_await m f (handle_index "deferred" cell.index) `Value ko;
            let waiters = match deferred_store_cell_at store.deferreds cell with Some c -> c.waiters | None -> [] in
            let got_before = !got in
            let parked = f.parked = WithGuard token && m.next_token = token + 1 && m.trace = [ ParkedOn (f.id, token) ] in
            (* M3: an interrupt while parked runs the cancel through the frame's `contE` *)
            ignore (interrupt_record m (Some 0) [] f);
            exec m fuel (Cevaluate f.id);
            let after = match deferred_store_cell_at store.deferreds cell with Some c -> c.waiters | None -> [] in
            all [ expect (waiters = [ (f.id, token) ] && parked && got_before = []) "a register that parks did not register the waiter and park on the fresh guard";
                  expect (after = [] && (match !got with [ Thr (Einterrupt_exn _) ] -> true | _ -> false)) "the interrupt while parked did not run the cancel and re-fail" ]) };
  ]

let count = List.length clauses

let find (name : string) : clause option = List.find_opt (fun c -> c.name = name) clauses

(* The Lean name of a clause as the census cites it. *)
let lean_name (c : clause) : string = "Effect4.Deep." ^ c.name

(* Evaluate the once-only part of a clause. *)
let evaluate (c : clause) : verdict =
  match c.check with
  | Refused why -> Not_portable why
  | Run _ -> Holds
  | Pure f | Both (f, _) -> (
    match (try f () with e -> Some ("raised " ^ Printexc.to_string e)) with
    | None -> Holds
    | Some msg -> Fails msg)

let step_check (c : clause) : step_check option =
  match c.check with Run s | Both (_, s) -> Some s | _ -> None
