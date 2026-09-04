(* `Effect4/Deep/Witnesses.lean` → `deep_witnesses.ml`: the executable witnesses, one OCaml
   entry per Lean theorem, in the Lean order, each running the machine(s) the theorem reads
   through the avatar (`replay` over an explicit decision tape, as `replayEval` does) and
   stating the theorem at the avatar's alphabet.

   Seat F1, 2026-09-04. Report: `docs/research/2026-09-04-seat-w1-deep-port.md`.

   A witness `def` (`w1DeferredJoin`, ...) is a function here, because the avatar's machine
   is mutable and every run starts from reset global state (`Deep_clauses.setup`). A
   witness theorem is a record: the machines it reads, run under the clause probe, and its
   statement as a check over the snapshots. The clauses a witness exercises are read off the
   census join (`deep_census.ml`): the rows that cite `Effect4.Deep.Witnesses.<name>`, and
   the `Clauses.lean` clauses those rows cite -- the same join `RuntimeCoverage.lean` makes.

   Where the statement depends on the value alphabet, the avatar's spelling is used and the
   report row is named: `Val.fiber` is the wire handle (W1-1), `Val.exitErr` is `Vnone`
   (W1-1/W1-8), a `Completion` stands where Lean stores a `Program` (W1-2), `Err.boom` is
   the code `100` of `Witnesses.lean`'s `reasonCode`, `Defect.asyncFiber` is the string
   the avatar dies with.

   Behavioural properties (packages plan §4.5): (1) every witness is deterministic: same
   tape, same machine, same snapshot on the three hosts; (2) a witness never reads state
   another witness left: `replay` resets the store, the handle space and the row sink;
   (3) the entry order is the Lean order and `count` is the number of `theorem`s in
   `Witnesses.lean`. *)

open Deep_fibers
open Deep_stores
open Deep_clauses

(* ---------------------------------------------------------------------- harness *)

(* What a witness reads after a run: the machine, and the store as the run left it. *)
type snap = {
  m : run_machine;
  arm : int;                                       (* `replayArm`: 0 finished, 1 frontier, 2 stuck *)
  refs : value list;
  cells : (completion option * waiter_pair list) list;
  scopes : (int * bool * int list) list;           (* key, closed, finalizer keys *)
  handle_of_fiber : int -> int;                    (* the wire handle a fiber id took *)
}

let snapshot (m : run_machine) (arm : int) : snap =
  let table = Hashtbl.copy handles in
  { m; arm;
    refs = store.refs;
    cells = List.map (fun (c : deferred_cell) -> (c.completion, c.waiters)) store.deferreds.cells;
    scopes =
      List.map
        (fun (e : scope_entry) -> (e.key, scope_is_closed e.scope, List.map fst (scope_finalizers e.scope)))
        store.scopes.entries;
    handle_of_fiber = (fun id -> match Hashtbl.find_opt table ("fiber", id) with Some h -> h | None -> -1) }

(* The fuel every witness runs with (`Witnesses.lean:34`). *)
let fuel = 400

(* `spawnRoot` + `replay` (`Witnesses.lean:38-49`): one root fiber over the empty context,
   not yet evaluated, and the tape replayed. *)
let replay ?(seed = fun () -> ()) (program : prog_name) (tape : run_decision list) : snap =
  let m = setup () in
  seed ();
  let root = m.next_id in
  let f = run_fiber_make root (prog_of program) true (!max_ops_before_yield, !prevent_yield) () in
  m.fibers <- m.fibers @ [ f ];
  m.next_id <- root + 1;
  let arm =
    match replay_eval m fuel tape with Rfinished _ -> 0 | Rfrontier -> 1 | Rstuck _ -> 2
  in
  snapshot m arm

let exit_of (s : snap) (id : int) : exitv option =
  match fiber_opt s.m id with Some f -> f.exit_ | None -> None

let parked_of (s : snap) (id : int) : parked option =
  match fiber_opt s.m id with Some f -> Some f.parked | None -> None

let fiber_count (s : snap) : int = List.length s.m.fibers

(* `interruptedWith`/`interruptedBy` (`Witnesses.lean:74-82`): the cause the machine records
   for `target` interrupted by `who`, annotated from the target's own stack frame and then
   from the caller's argument. *)
let interrupted_with (who : int) (target : int) (extra : string list) : exitv =
  Efailure (cause_annotate (cause_interrupt (Some who)) (stack_annotations_of target @ extra))

let interrupted_by (who : int) (target : int) : exitv = interrupted_with who target []

(* `causeKeys`: the annotation keys of a failed exit's cause. The avatar annotates the cause,
   not each reason (`deep_fibers.ml:77`), so this is one list rather than one per reason. *)
let cause_keys : exitv -> string list = function
  | Esuccess _ -> []
  | Efailure c -> c.annotations

let trace_events (s : snap) = s.m.trace

let interrupt_rows (s : snap) : (int option * int) list =
  List.filter_map (function InterruptRecorded (who, t) -> Some (who, t) | _ -> None) s.m.trace

let children_interrupted_rows (s : snap) : (int * int list) list =
  List.filter_map (function ChildrenInterrupted (p, cs) -> Some (p, cs) | _ -> None) s.m.trace

(* `scopeRows`: `scopeLinked` (`0`) and `scopeClosedOnLink` (`1`). The avatar's
   `ScopeLinked` erases the mode (`Render.lean`, `Avatar.runEvent.erasures`), so a linked row
   is `[0; scope; key; fiber]` where Lean's carries the mode second. *)
let scope_rows (s : snap) : int list list =
  List.filter_map
    (function
      | ScopeLinked (scope, key, fiber) -> Some [ 0; scope; key; fiber ]
      | ScopeClosedOnLink (scope, fiber) -> Some [ 1; scope; fiber ]
      | _ -> None)
    s.m.trace

let race_rows (s : snap) : int list list =
  List.filter_map
    (function
      | RaceLaunched (r, e) -> Some [ 0; r; e ]
      | RaceSkipped (r, e) -> Some [ 1; r; e ]
      | RaceSettled (r, _) -> Some [ 2; r ]
      | _ -> None)
    s.m.trace

let resume_and_exit_order (s : snap) : int list list =
  List.filter_map
    (function
      | ResumedWith (f, token, _) -> Some [ 0; f; token ]
      | Exited (f, _) -> Some [ 1; f ]
      | _ -> None)
    s.m.trace

let callback_rows (s : snap) : (int * exitv) list =
  List.filter_map (function CallbackEv (k, e) -> Some (k, e) | _ -> None) s.m.trace

let armed_of (s : snap) (id : int) : bool option =
  match fiber_opt s.m id with Some f -> Some f.dispatcher.armed | None -> None

let queued_of (s : snap) (id : int) : int option =
  match fiber_opt s.m id with
  | Some f -> Some (List.length (List.concat_map (fun b -> b.tasks) f.dispatcher.buckets))
  | None -> None

let scope_keys (s : snap) (key : int) : int list option =
  List.find_map (fun (k, _, keys) -> if k = key then Some keys else None) s.scopes

let scope_closed (s : snap) (key : int) : bool option =
  List.find_map (fun (k, closed, _) -> if k = key then Some closed else None) s.scopes

let waiters_of (s : snap) (cell : int) : waiter_pair list option =
  Option.map snd (List.nth_opt s.cells cell)

let completion_of (s : snap) (cell : int) : completion option option =
  Option.map fst (List.nth_opt s.cells cell)

let finalizer_runs (s : snap) (id : int) : int =
  List.length (List.filter (function FinalizerProgram (f, _, _) -> f = id | _ -> false) s.m.trace)

(* Pass A forbidden examples 1 and 5 (`traceWellFormed`): an observer never fires before its
   fiber's `exited` row, and no fiber exits twice. *)
let trace_well_formed (s : snap) : bool =
  let rec go seen = function
    | [] -> true
    | ObserverFired (f, _) :: rest -> List.mem f seen && go seen rest
    | Exited (f, _) :: rest -> (not (List.mem f seen)) && go (seen @ [ f ]) rest
    | _ :: rest -> go seen rest
  in
  go [] s.m.trace

(* Forbidden 3: no fiber exits with the `notImplemented` defect. *)
let no_not_implemented_defect (s : snap) : bool =
  List.for_all
    (fun f ->
      match f.exit_ with
      | Some (Efailure c) -> not (List.mem (Rdie "notImplemented") c.reasons)
      | _ -> true)
    s.m.fibers

let fiber_value (s : snap) (id : int) : value = Vhandle (s.handle_of_fiber id)

(* `Err.boom` at this alphabet: the code `reasonCode` gives it (`Witnesses.lean:96`). *)
let boom = 100

(* ---------------------------------------------------------------------- fork options *)

let immediate_child = { start_immediately = true; daemon = false; mask_mode = Minherit }
let deferred_child = { start_immediately = false; daemon = false; mask_mode = Minherit }
let scoped_child = { start_immediately = true; daemon = true; mask_mode = Minherit }

let d0 : deferred_key = { index = 0 }

(* ---------------------------------------------------------------------- the seeds *)

let one_cell () = store.deferreds.cells <- [ { completion = None; waiters = [] } ]

let scope_state () =
  scope_store_make store.scopes 0 Fssequential;
  scope_store_make store.scopes 1 Fssequential;
  scope_store_close_state store.scopes 1 (Esuccess Vunit);
  scope_store_make store.scopes 2 Fssequential;
  ignore (scope_store_add_finalizer store.scopes 2 101 (FininterruptFiber (0, true)))

let close_stores () =
  scope_store_make store.scopes 3 Fssequential;
  ignore (scope_store_add_finalizer store.scopes 3 200 (Finrelease (1, false)));
  ignore (scope_store_add_finalizer store.scopes 3 201 (Finrelease (2, true)));
  scope_store_make store.scopes 4 Fsparallel;
  ignore (scope_store_add_finalizer store.scopes 4 300 (Finrelease (3, false)));
  ignore (scope_store_add_finalizer store.scopes 4 301 (Finrelease (4, true)))

let one_ref () = store.refs <- [ Vnat 1 ]
let three_ref () = store.refs <- [ Vnat 3 ]

(* ---------------------------------------------------------------------- the defs *)

(* W1 *)
let w1_deferred_join () =
  replay (PforkThen (Pvalue (Vnat 42), deferred_child, MJoin)) [ Devaluate 0; Dfire 0 ]
let w1_deferred_join_no_fire () =
  replay (PforkThen (Pvalue (Vnat 42), deferred_child, MJoin)) [ Devaluate 0 ]
let w1_immediate_join () =
  replay (PforkThen (Pvalue (Vnat 42), immediate_child, MJoin)) [ Devaluate 0 ]
let w1_await_failing () =
  replay (PforkThen (PfailCause (cause_fail 7), immediate_child, MAwait)) [ Devaluate 0 ]
let w1_join_failing () =
  replay (PforkThen (PfailCause (cause_fail 7), immediate_child, MJoin)) [ Devaluate 0 ]

(* W2 *)
let w2_child = PonExitOf (Pvalue (Vnat 7), FinparkThen 1, false)
let w2 () =
  replay (PforkOnly (w2_child, immediate_child))
    [ Devaluate 0; DinterruptFrom (Some 0, [], 1); DanswerAsync (1, 0, Aval Vunit) ]
let w2_pending () =
  replay (PforkOnly (w2_child, immediate_child)) [ Devaluate 0; DinterruptFrom (Some 0, [], 1) ]

(* W3 *)
let w3_empty_pending () = replay (PraceOf Rnempty) [ Devaluate 0 ]
let w3_empty_interrupted () = replay (PraceOf Rnempty) [ Devaluate 0; DinterruptFrom (Some 0, [], 0) ]
let w3_stops_launch () = replay (PraceOf RnsuccessThenSecond) [ Devaluate 0 ]
let w3_next_launch () = replay (PraceOf RnfailThenSuccess) [ Devaluate 0 ]
let w3_all_fail () = replay (PraceOf RnfailThenFail) [ Devaluate 0 ]

(* W4 *)
let complete_seven = PsyncOp (SdeferredCompleteWith (d0, CoofExit (Esuccess (Vnat 7))))
let w4_sibling () =
  replay ~seed:one_cell
    (PseqOf (PforkOnly (PawaitDeferred d0, immediate_child), PforkOnly (complete_seven, immediate_child)))
    [ Devaluate 0 ]
let w4_complete_twice () =
  replay ~seed:one_cell
    (PseqOf (complete_seven, PsyncOp (SdeferredCompleteWith (d0, CoofExit (Esuccess (Vnat 8))))))
    [ Devaluate 0 ]
let w4_sibling_then_more () =
  replay ~seed:one_cell
    (PseqOf
       ( PforkOnly (PawaitDeferred d0, immediate_child),
         PforkOnly (PseqOf (complete_seven, Pvalue Vunit), immediate_child) ))
    [ Devaluate 0 ]
let w4_interrupt_waiter () =
  replay ~seed:one_cell
    (PseqOf (PforkOnly (PawaitDeferred d0, immediate_child), PforkOnly (PinterruptDeferred d0, immediate_child)))
    [ Devaluate 0 ]

(* W5 *)
let w5_program = PseqOf (PforkOnly (Ppark 1, immediate_child), Pvalue Vunit)
let w5_with_middleware () = replay w5_program [ DinstallMiddleware; Devaluate 0 ]
let w5_without_middleware () = replay w5_program [ Devaluate 0 ]
let w5_await_all_children () =
  replay
    (PseqOf (PforkOnly (Ppark 1, immediate_child), PawaitAllNew (PforkOnly (Pvalue (Vnat 5), deferred_child))))
    [ Devaluate 0; Dfire 0 ]

(* W6 *)
let w6_link_then_close () =
  replay ~seed:scope_state
    (PseqOf (PforkInScope (Ppark 1, scoped_child, 0, 100), PcloseScopeOf (0, Esuccess Vunit)))
    [ Devaluate 0 ]
let w6_closed_scope () =
  replay ~seed:scope_state (PforkInScope (Ppark 1, scoped_child, 1, 100)) [ Devaluate 0 ]
let w6_drops_key () =
  replay ~seed:scope_state (PforkInScope (Pvalue (Vnat 3), scoped_child, 0, 100)) [ Devaluate 0 ]
let w6_self_interruptor_skipped () =
  replay ~seed:scope_state (PcloseScopeOf (2, Esuccess Vunit)) [ Devaluate 0 ]
let w6_closed_run_in () =
  replay ~seed:scope_state
    (PseqOf (PforkOnly (Ppark 1, immediate_child), PrunInScope (1, 1, 100)))
    [ Devaluate 0 ]

(* W6b *)
let w6_sequential () = replay ~seed:close_stores (PcloseScopeOf (3, Esuccess Vunit)) [ Devaluate 0 ]
let w6_parallel () = replay ~seed:close_stores (PcloseScopeOf (4, Esuccess Vunit)) [ Devaluate 0 ]

(* W10 *)
let w10_masked_child = PmaskedPark 1
let w10_masked () =
  replay (PforkOnly (w10_masked_child, immediate_child))
    [ Devaluate 0; DinterruptFrom (Some 0, [], 1); DanswerAsync (1, 0, Aval Vunit) ]
let w10_masked_pending () =
  replay (PforkOnly (w10_masked_child, immediate_child))
    [ Devaluate 0; DinterruptFrom (Some 0, [], 1) ]
let w10_into () =
  replay ~seed:one_cell (PintoDeferred (PfailCause (cause_fail boom), d0)) [ Devaluate 0 ]

(* W11 *)
let w11_parked () =
  replay ~seed:one_cell (PforkOnly (PawaitDeferred d0, immediate_child)) [ Devaluate 0 ]
let w11_cancelled () =
  replay ~seed:one_cell (PforkOnly (PawaitDeferred d0, immediate_child))
    [ Devaluate 0; DinterruptFrom (Some 0, [], 1) ]

(* W12 *)
let w12_await_all () =
  replay
    (PseqOf
       ( PforkOnly (Pvalue (Vnat 4), deferred_child),
         PseqOf (PforkOnly (PfailCause (cause_fail 5), deferred_child), PawaitFibers [ 1; 2 ]) ))
    [ Devaluate 0; Dfire 0 ]

(* W13 *)
let w13_unknown_scope () =
  replay ~seed:scope_state (PcloseScopeOf (99, Esuccess Vunit)) [ Devaluate 0 ]
let w13_unknown_link () =
  replay ~seed:scope_state (PforkInScope (Ppark 1, scoped_child, 99, 100)) [ Devaluate 0 ]

(* W7 *)
let r0 : ref_key = { index = 0 }
let w7_set () = replay ~seed:one_ref (PsyncOp (SrefSet (r0, Vnat 5))) [ Devaluate 0 ]
let w7_update () = replay ~seed:one_ref (PsyncOp (SrefUpdate (r0, Fnincr))) [ Devaluate 0 ]
let w7_modify_some () = replay ~seed:one_ref (PsyncOp (SrefModifySome (r0, FnnoChange))) [ Devaluate 0 ]
let w7_update_some_and_get () =
  replay ~seed:three_ref (PsyncOp (SrefUpdateSomeAndGet (r0, FnzeroWhenPositive))) [ Devaluate 0 ]
let w7_get_and_update_some () =
  replay ~seed:three_ref (PsyncOp (SrefGetAndUpdateSome (r0, FnzeroWhenPositive))) [ Devaluate 0 ]

(* W8 *)
let w8_sync_exit () : exitv =
  let m = setup () in
  run_sync_exit m fuel (prog_of (Ppark 1))
let w8_sync_value () : exitv =
  let m = setup () in
  run_sync_exit m fuel (prog_of (Pvalue (Vnat 3)))
let w8_callback () : snap =
  let m = setup () in
  ignore (run_callback m fuel (prog_of (Pvalue (Vnat 3))) 77);
  snapshot m 0
let w8_promise () = promise_outcome (Efailure (cause_combine (cause_fail 4) (cause_die "badName")))

(* W9 *)
let w9_two_yields = PseqOf (PyieldNow 0, PseqOf (PyieldNow 0, Pvalue (Vnat 1)))
let w9_after_one_fire () = replay w9_two_yields [ Devaluate 0; Dfire 0 ]
let w9_after_two_fires () = replay w9_two_yields [ Devaluate 0; Dfire 0; Dfire 0 ]

(* DB-07 *)
let db_seven () =
  replay ~seed:one_ref (PseqOf (PsyncOp (SrefSet (r0, Vnat 5)), PfailCause (cause_fail boom))) [ Devaluate 0 ]

(* ---------------------------------------------------------------------- the theorems *)

(* How a witness theorem is stated here: the machines it reads (run under the clause probe,
   in this order, each a named def above) and the statement over their snapshots. *)
type witness = {
  name : string;                                (* the Lean theorem *)
  lean : string;                                (* `Witnesses.lean:<line>` *)
  defs : (string * (unit -> snap)) list;        (* the defs the statement reads *)
  state : (string -> snap) -> string option;    (* the statement; `None` holds *)
  portable : string option;                     (* `Some why` when it has no avatar instance *)
}

let theorem ?portable name lean defs state = { name; lean; defs; state; portable }

let witnesses : witness list =
  [
    (* W1 -- fork and join *)
    theorem "w1_deferred_join_parent" "Witnesses.lean:267" [ ("w1DeferredJoin", w1_deferred_join) ]
      (fun d -> expect (exit_of (d "w1DeferredJoin") 0 = Some (Esuccess (Vnat 42))) "the parent does not exit with the joined child's success");
    theorem "w1_deferred_join_child" "Witnesses.lean:271" [ ("w1DeferredJoin", w1_deferred_join) ]
      (fun d ->
        let s = d "w1DeferredJoin" in
        expect (exit_of s 1 = Some (Esuccess (Vnat 42)) && fiber_count s = 2) "the child does not exit with 42 in a two-fiber machine");
    theorem "w1_deferred_start_is_a_task" "Witnesses.lean:277" [ ("w1DeferredJoin[evaluate 0]", w1_deferred_join_no_fire) ]
      (fun d ->
        let s = d "w1DeferredJoin[evaluate 0]" in
        expect (exit_of s 1 = None && armed_of s 0 = Some true) "before the fire the child ran, or the parent's dispatcher is not armed");
    theorem "w1_immediate_join" "Witnesses.lean:287" [ ("w1ImmediateJoin", w1_immediate_join) ]
      (fun d ->
        let s = d "w1ImmediateJoin" in
        expect (exit_of s 0 = Some (Esuccess (Vnat 42)) && exit_of s 1 = Some (Esuccess (Vnat 42))) "the same exits with no fire: differ");
    theorem "w1_await_is_a_value" "Witnesses.lean:293" [ ("w1AwaitFailing", w1_await_failing) ]
      (fun d ->
        (* W1-1/W1-8: `Val.exitErr (Cause.fail (Err.tag 7))` is the wire's `Vnone`. *)
        expect (exit_of (d "w1AwaitFailing") 0 = Some (Esuccess Vnone)) "the parent did not succeed with the child's failed exit as a value");
    theorem "w1_join_is_an_effect" "Witnesses.lean:299" [ ("w1JoinFailing", w1_join_failing) ]
      (fun d -> expect (exit_of (d "w1JoinFailing") 0 = Some (Efailure (cause_fail 7))) "the parent did not fail with the child's cause");
    (* W2 -- masked interrupt *)
    theorem "w2_delivered_at_unmask" "Witnesses.lean:325" [ ("w2", w2) ]
      (fun d -> expect (exit_of (d "w2") 1 = Some (interrupted_by 0 1)) "the child does not exit with the interrupt cause at the unmask");
    theorem "w2_recorded_once" "Witnesses.lean:329" [ ("w2", w2) ]
      (fun d -> expect (interrupt_rows (d "w2") = [ (Some 0, 1) ]) "the interrupt is not recorded exactly once");
    theorem "w2_finalizer_runs_once" "Witnesses.lean:332" [ ("w2", w2) ]
      (fun d -> expect (finalizer_runs (d "w2") 1 = 1) "the finalizer did not run exactly once");
    theorem "w2_masked_interrupt_does_not_apply" "Witnesses.lean:336" [ ("w2[pending]", w2_pending) ]
      (fun d -> expect (exit_of (d "w2[pending]") 1 = None) "the masked child exited before the async was answered");
    (* W3 -- raceAll *)
    theorem "w3_empty_is_a_frontier" "Witnesses.lean:363" [ ("w3EmptyPending", w3_empty_pending) ]
      (fun d ->
        let s = d "w3EmptyPending" in
        expect (exit_of s 0 = None && parked_of s 0 = Some (WithGuard 0) && fiber_count s = 1) "the empty race is not a live frontier on its race token");
    theorem "w3_empty_until_interrupted" "Witnesses.lean:369" [ ("w3EmptyInterrupted", w3_empty_interrupted) ]
      (fun d -> expect (exit_of (d "w3EmptyInterrupted") 0 = Some (interrupted_by 0 0)) "the empty race did not end with the host's interruption");
    theorem "w3_immediate_success_stops_launch" "Witnesses.lean:376" [ ("w3StopsLaunch", w3_stops_launch) ]
      (fun d ->
        let s = d "w3StopsLaunch" in
        all [ expect (exit_of s 0 = Some (Esuccess (Vnat 1))) "the host did not answer the first entrant's success";
              expect (race_rows s = [ [ 0; 0; 1 ]; [ 2; 0 ]; [ 1; 0; 2 ] ]) "the race rows differ (launch, settle, skip)";
              expect (fiber_count s = 3) "not three fibers";
              expect (interrupt_rows s = [ (Some 0, 2) ]) "the unlaunched entrant was not interrupted with the host's id";
              expect (exit_of s 2 = Some (interrupted_by 0 2)) "the unlaunched entrant was not kept, interrupted" ]);
    theorem "w3_failure_allows_next_launch" "Witnesses.lean:386" [ ("w3NextLaunch", w3_next_launch) ]
      (fun d ->
        let s = d "w3NextLaunch" in
        expect (exit_of s 0 = Some (Esuccess (Vnat 9)) && race_rows s = [ [ 0; 0; 1 ]; [ 0; 0; 2 ]; [ 2; 0 ] ]) "a failure settled the race, or the next entrant did not launch");
    theorem "w3_all_failures_retain_order" "Witnesses.lean:393" [ ("w3AllFail", w3_all_fail) ]
      (fun d -> expect (exit_of (d "w3AllFail") 0 = Some (Efailure { reasons = [ Rfail 1; Rfail 2 ]; annotations = [] })) "the all-failed race does not fail with the retained causes in launch order");
    (* W4 -- a sibling completes a Deferred *)
    theorem "w4_sibling_resumes" "Witnesses.lean:451" [ ("w4Sibling", w4_sibling) ]
      (fun d ->
        let s = d "w4Sibling" in
        all [ expect (exit_of s 1 = Some (Esuccess (Vnat 7))) "A was not resumed with the stored 7";
              expect (exit_of s 2 = Some (Esuccess (Vbool true))) "B's completion did not answer true";
              expect (exit_of s 0 = Some (Esuccess (fiber_value s 2))) "the parent's answer is not B's handle (W1-1)" ]);
    theorem "w4_completion_resumes_on_the_spot" "Witnesses.lean:460" [ ("w4SiblingThenMore", w4_sibling_then_more); ("w4Sibling", w4_sibling) ]
      (fun d ->
        let a = d "w4SiblingThenMore" and b = d "w4Sibling" in
        all [ expect (resume_and_exit_order a = [ [ 0; 1; 0 ]; [ 1; 1 ]; [ 1; 2 ]; [ 1; 0 ] ]) "M1: the waiter is not resumed inside the completion when it is not the last primitive";
              expect (exit_of a 1 = Some (Esuccess (Vnat 7))) "A's exit differs";
              expect (resume_and_exit_order b = [ [ 0; 1; 0 ]; [ 1; 1 ]; [ 1; 2 ]; [ 1; 0 ] ]) "M1: the waiter is not resumed inside the completion when it is the last primitive" ]);
    theorem "w4_complete_twice_answers_false" "Witnesses.lean:467" [ ("w4CompleteTwice", w4_complete_twice) ]
      (fun d -> expect (exit_of (d "w4CompleteTwice") 0 = Some (Esuccess (Vbool false))) "the second completion did not answer false");
    theorem "w4_interrupt_reaches_the_waiter" "Witnesses.lean:472" [ ("w4InterruptWaiter", w4_interrupt_waiter) ]
      (fun d ->
        let s = d "w4InterruptWaiter" in
        expect (exit_of s 1 = Some (Efailure (cause_interrupt (Some 2))) && exit_of s 2 = Some (Esuccess (Vbool true))) "the recorded interruptor is not the completing fiber, or the waiter was not resumed with it");
    (* W5 -- children after the parent's exit *)
    theorem "w5_middleware_interrupts_children" "Witnesses.lean:501" [ ("w5WithMiddleware", w5_with_middleware) ]
      (fun d ->
        let s = d "w5WithMiddleware" in
        all [ expect (exit_of s 1 = Some (interrupted_by 0 1)) "the child was not interrupted with the parent's id";
              expect (children_interrupted_rows s = [ (0, [ 1 ]) ]) "no childrenInterrupted row";
              expect (interrupt_rows s = [ (Some 0, 1) ]) "the interrupt rows differ";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the parent's exit differs" ]);
    theorem "w5_no_middleware_leaves_children" "Witnesses.lean:509" [ ("w5WithoutMiddleware", w5_without_middleware) ]
      (fun d ->
        let s = d "w5WithoutMiddleware" in
        expect (exit_of s 1 = None && children_interrupted_rows s = [] && interrupt_rows s = [] && exit_of s 0 = Some (Esuccess Vunit)) "without the middleware the child did not survive");
    theorem "w5_await_all_children_awaits_only_new" "Witnesses.lean:518" [ ("w5AwaitAllChildren", w5_await_all_children) ]
      (fun d ->
        let s = d "w5AwaitAllChildren" in
        expect (exit_of s 2 = Some (Esuccess (Vnat 5)) && exit_of s 1 = None && exit_of s 0 = Some (Esuccess Vunit)) "`awaitAllChildren` did not await only the children added during its body");
    (* W6 -- scope linkage *)
    theorem "w6_link_then_close" "Witnesses.lean:571" [ ("w6LinkThenClose", w6_link_then_close) ]
      (fun d ->
        let s = d "w6LinkThenClose" in
        all [ expect (scope_rows s = [ [ 0; 0; 100; 1 ] ]) "the linkage row differs (mode erased)";
              expect (exit_of s 1 = Some (interrupted_by 0 1)) "the child was not interrupted by the closer";
              expect (scope_keys s 0 = Some []) "the key was not dropped by the child's exit observer";
              expect (scope_closed s 0 = Some true) "the scope did not end Closed";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the closer's exit differs" ]);
    theorem "w6_closed_scope_interrupts_now" "Witnesses.lean:590" [ ("w6ClosedScope", w6_closed_scope) ]
      (fun d ->
        let s = d "w6ClosedScope" in
        all [ expect (scope_rows s = [ [ 1; 1; 1 ] ]) "no scopeClosedOnLink row";
              expect (exit_of s 1 = Some (interrupted_with 0 1 (stack_annotations_of 0))) "the child was not interrupted at once with the parent's id and annotations";
              expect (Option.map cause_keys (exit_of s 1) = Some [ "stack1"; "stack0" ]) "the cause does not carry the child's key then the parent's (M10)" ]);
    theorem "w6_runIn_closed_scope_uses_no_caller_annotations" "Witnesses.lean:600" [ ("w6ClosedRunIn", w6_closed_run_in) ]
      (fun d ->
        let s = d "w6ClosedRunIn" in
        all [ expect (scope_rows s = [ [ 1; 1; 1 ] ]) "no scopeClosedOnLink row";
              expect (exit_of s 1 = Some (interrupted_by 1 1)) "the run-in fiber was not interrupted with its own id";
              expect (Option.map cause_keys (exit_of s 1) = Some [ "stack1" ]) "the cause carries caller annotations (M10)";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the caller's exit differs" ]);
    theorem "w6_child_exit_drops_key" "Witnesses.lean:608" [ ("w6DropsKey", w6_drops_key) ]
      (fun d ->
        let s = d "w6DropsKey" in
        expect (exit_of s 1 = Some (Esuccess (Vnat 3)) && scope_keys s 0 = Some []) "a child that exits normally did not drop its key");
    theorem "w6_self_interruptor_skipped" "Witnesses.lean:614" [ ("w6SelfInterruptorSkipped", w6_self_interruptor_skipped) ]
      (fun d ->
        let s = d "w6SelfInterruptorSkipped" in
        expect (interrupt_rows s = [] && exit_of s 0 = Some (Esuccess Vunit)) "the self-interruptor was not skipped");
    (* W6b -- the two close strategies *)
    theorem "w6_sequential_captures_and_merges" "Witnesses.lean:645" [ ("w6Sequential", w6_sequential) ]
      (fun d ->
        let s = d "w6Sequential" in
        all [ expect (exit_of s 0 = Some (Efailure { reasons = [ Rfail 2 ]; annotations = [] })) "the sequential close did not capture the failing finalizer and answer the merge";
              expect (fiber_count s = 1) "the sequential close forked";
              expect (scope_closed s 3 = Some true) "the scope did not close" ]);
    theorem "w6_parallel_forks_and_merges" "Witnesses.lean:653" [ ("w6Parallel", w6_parallel) ]
      (fun d ->
        let s = d "w6Parallel" in
        all [ expect (fiber_count s = 3) "the parallel close did not fork one daemon per finalizer";
              expect (exit_of s 1 = Some (Efailure { reasons = [ Rfail 4 ]; annotations = [] })) "the first finalizer's exit differs";
              expect (exit_of s 2 = Some (Esuccess Vunit)) "the second finalizer's exit differs";
              expect (exit_of s 0 = Some (Efailure { reasons = [ Rfail 4 ]; annotations = [] })) "every awaited exit was not merged (M6)";
              expect (scope_closed s 4 = Some true) "the scope did not close" ]);
    (* W10 -- a program that masks its own fiber *)
    theorem "w10_program_masks_its_own_fiber" "Witnesses.lean:689" [ ("w10MaskedPending", w10_masked_pending); ("w10Masked", w10_masked) ]
      (fun d ->
        let p = d "w10MaskedPending" and s = d "w10Masked" in
        all [ expect (exit_of p 1 = None) "the masked fiber exited while masked";
              expect (interrupt_rows s = [ (Some 0, 1) ]) "the interrupt was not recorded once";
              expect (exit_of s 1 = Some (interrupted_by 0 1)) "the cause was not delivered by the restoring frame" ]);
    theorem "w10_into_completes_on_failure" "Witnesses.lean:704" [ ("w10Into", w10_into) ]
      (fun d ->
        let s = d "w10Into" in
        (* W1-2: the slot holds the `Completion`, where Lean holds `Prim.failure (Cause.fail Err.boom)`. *)
        expect (exit_of s 0 = Some (Esuccess (Vbool true)) && completion_of s 0 = Some (Some (CoofExit (Efailure (cause_fail boom))))) "`into` did not answer true and store the failed exit");
    (* W11 -- an interrupted Async runs its cancel *)
    theorem "w11_cancel_splices_the_waiter" "Witnesses.lean:736" [ ("w11Parked", w11_parked); ("w11Cancelled", w11_cancelled) ]
      (fun d ->
        let p = d "w11Parked" and c = d "w11Cancelled" in
        all [ expect (waiters_of p 0 = Some [ (1, 0) ]) "parking did not register the waiter";
              expect (waiters_of c 0 = Some []) "the cancel did not splice the waiter out (M3)";
              expect (exit_of c 1 = Some (interrupted_by 0 1)) "the cancel did not re-fail with the passing cause" ]);
    (* W12 -- awaitAll answers the exits it collected *)
    theorem "w12_awaitAll_answers_the_exits" "Witnesses.lean:758" [ ("w12AwaitAll", w12_await_all) ]
      (fun d ->
        (* W1-8: `exitsVal` at this alphabet is `[some 4; none]`; the failure's reasons do not survive. *)
        expect (exit_of (d "w12AwaitAll") 0 = Some (Esuccess (exits_val [ Esuccess (Vnat 4); Efailure (cause_fail 5) ]))) "the parent's answer is not the two exits in collection order");
    (* W13 -- an unknown scope key halts the machine *)
    theorem "w13_unknown_scope_is_stuck" "Witnesses.lean:781" [ ("w13UnknownScope", w13_unknown_scope) ]
      (fun d ->
        let s = d "w13UnknownScope" in
        expect (s.m.stuck = Some (UnknownScope 99) && exit_of s 0 = None && s.arm = 2) "closing an unknown scope is not a stuck machine with the fiber unexited");
    theorem "w13_unknown_link_is_stuck" "Witnesses.lean:789" [ ("w13UnknownLink", w13_unknown_link) ]
      (fun d ->
        let s = d "w13UnknownLink" in
        expect (s.m.stuck = Some (UnknownScope 99) && s.arm = 2) "linking into an unknown scope is not a stuck machine");
    (* W7 -- the ref.* quirks *)
    theorem "w7_set_answers_the_cell" "Witnesses.lean:821" [ ("w7Set", w7_set) ]
      (fun d ->
        let s = d "w7Set" in
        expect (exit_of s 0 = Some (Esuccess (Vhandle 0)) && s.refs = [ Vnat 5 ]) "`set` did not answer the cell and write the value");
    theorem "w7_update_answers_void" "Witnesses.lean:827" [ ("w7Update", w7_update) ]
      (fun d ->
        let s = d "w7Update" in
        expect (exit_of s 0 = Some (Esuccess Vunit) && s.refs = [ Vnat 2 ]) "`update` did not answer void with the function applied once");
    theorem "w7_modify_some_writes_back_the_read" "Witnesses.lean:833" [ ("w7ModifySome", w7_modify_some) ]
      (fun d ->
        let s = d "w7ModifySome" in
        expect (exit_of s 0 = Some (Esuccess (Vnat 1)) && s.refs = [ Vnat 1 ]) "`modifySome` on `None` did not write back the read");
    theorem "w7_update_some_and_get_rereads" "Witnesses.lean:840" [ ("w7UpdateSomeAndGet", w7_update_some_and_get); ("w7GetAndUpdateSome", w7_get_and_update_some) ]
      (fun d ->
        expect (exit_of (d "w7UpdateSomeAndGet") 0 = Some (Esuccess (Vnat 0)) && exit_of (d "w7GetAndUpdateSome") 0 = Some (Esuccess (Vnat 3))) "the fresh read after the write / the read before it differ");
    (* W8 -- the runtime entries *)
    theorem "w8_sync_exit_async_fiber_error" "Witnesses.lean:867" []
      (fun _ -> expect (w8_sync_exit () = Efailure (cause_die "AsyncFiberError")) "a root that survives the flush is not the `AsyncFiberError` defect");
    theorem "w8_sync_exit_value" "Witnesses.lean:871" []
      (fun _ -> expect (w8_sync_value () = Esuccess (Vnat 3)) "a root that finishes does not answer its exit");
    theorem "w8_callback_fires" "Witnesses.lean:874" [ ("w8Callback", w8_callback) ]
      (fun d -> expect (callback_rows (d "w8Callback") = [ (77, Esuccess (Vnat 3)) ]) "the callback observer did not deliver the root's exit under its key");
    theorem "w8_promise_squashes" "Witnesses.lean:877" []
      (fun _ -> expect (w8_promise () = Error (Sq_error 4)) "`promiseOutcome` does not squash to the first `Fail` ahead of the defect");
    (* the five forbidden examples *)
    theorem "forbidden_observers_and_double_exit" "Witnesses.lean:900"
      [ ("w1DeferredJoin", w1_deferred_join); ("w2", w2); ("w3AllFail", w3_all_fail); ("w3StopsLaunch", w3_stops_launch);
        ("w4Sibling", w4_sibling); ("w4InterruptWaiter", w4_interrupt_waiter); ("w5WithMiddleware", w5_with_middleware);
        ("w5AwaitAllChildren", w5_await_all_children); ("w6LinkThenClose", w6_link_then_close); ("w6Parallel", w6_parallel);
        ("w9AfterTwoFires", w9_after_two_fires); ("w10Masked", w10_masked); ("w11Cancelled", w11_cancelled); ("w12AwaitAll", w12_await_all) ]
      (fun d ->
        all
          (List.map
             (fun n -> expect (trace_well_formed (d n)) (n ^ ": an observer fired before its fiber's exit, or a fiber exited twice"))
             [ "w1DeferredJoin"; "w2"; "w3AllFail"; "w3StopsLaunch"; "w4Sibling"; "w4InterruptWaiter"; "w5WithMiddleware";
               "w5AwaitAllChildren"; "w6LinkThenClose"; "w6Parallel"; "w9AfterTwoFires"; "w10Masked"; "w11Cancelled"; "w12AwaitAll" ]));
    theorem "forbidden_interrupt_while_running" "Witnesses.lean:921" []
      (fun _ ->
        let m = setup () in
        let f = add_fiber m in
        f.running <- true;
        let apply = interrupt_record m (Some 0) [] f in
        expect ((not apply) && f.frame.deferred_interrupt) "an interrupt of a running interruptible fiber was applied, or not deferred");
    theorem "forbidden_setInterruptible_as_current" "Witnesses.lean:932" []
      ~portable:"`Prim.setInterruptible` never sits in `frame.current` here: the avatar's frame is the OCaml stack (DIVERGENCE 1) and the mask change is the `Op_set_interruptible` arm, so the forbidden step has no shape to reach"
      (fun _ -> None);
    theorem "forbidden_no_notImplemented_defect" "Witnesses.lean:940"
      [ ("w1DeferredJoin", w1_deferred_join); ("w2", w2); ("w3AllFail", w3_all_fail); ("w4Sibling", w4_sibling);
        ("w5WithMiddleware", w5_with_middleware); ("w6LinkThenClose", w6_link_then_close); ("w9AfterTwoFires", w9_after_two_fires);
        ("w10Masked", w10_masked); ("w11Cancelled", w11_cancelled); ("w12AwaitAll", w12_await_all) ]
      (fun d ->
        all
          (List.map
             (fun n -> expect (no_not_implemented_defect (d n)) (n ^ ": a fiber exited with the `notImplemented` defect"))
             [ "w1DeferredJoin"; "w2"; "w3AllFail"; "w4Sibling"; "w5WithMiddleware"; "w6LinkThenClose"; "w9AfterTwoFires"; "w10Masked"; "w11Cancelled"; "w12AwaitAll" ]));
    theorem "forbidden_task_enqueued_during_drain" "Witnesses.lean:955" [ ("w9AfterOneFire", w9_after_one_fire) ]
      (fun d ->
        let s = d "w9AfterOneFire" in
        expect (exit_of s 0 = None && armed_of s 0 = Some true && queued_of s 0 = Some 1) "after one fire the task enqueued during the drain did not wait, armed, for the next");
    theorem "w9_next_fire_runs_it" "Witnesses.lean:961" [ ("w9AfterTwoFires", w9_after_two_fires) ]
      (fun d -> expect (exit_of (d "w9AfterTwoFires") 0 = Some (Esuccess (Vnat 1))) "the next fire did not run it");
    (* DB-07 *)
    theorem "db07_store_survives_failure" "Witnesses.lean:978" [ ("dbSeven", db_seven) ]
      (fun d ->
        let s = d "dbSeven" in
        expect (exit_of s 0 = Some (Efailure (cause_fail boom)) && s.refs = [ Vnat 5 ]) "the store the failing fiber reached was restored");
    (* the two projections *)
    theorem "toSched_computes" "Witnesses.lean:990" []
      ~portable:"`RunMachine.toSched` (the old scheduler's `Event` alphabet) is not ported; only `RunFiber.status` is (`run_fiber_status`)"
      (fun _ -> None);
    theorem "toSup_computes" "Witnesses.lean:998" [ ("w1DeferredJoin", w1_deferred_join) ]
      (fun d ->
        (* `toSup` is computed from the record; the avatar checks the fields it is computed from. *)
        match fiber_opt (d "w1DeferredJoin").m 1 with
        | Some f ->
          expect (run_fiber_status f = Sdone && f.exit_ = Some (Esuccess (Vnat 42)) && f.children = [] && f.observers = [] && f.frame.interrupted_cause = None)
            "the child's supervision face differs: done, its exit, no children, no subscriptions, no recorded interrupt"
        | None -> fail "no child");
    theorem "toSup_records_the_interrupt" "Witnesses.lean:1008" [ ("w2", w2) ]
      (fun d ->
        match fiber_opt (d "w2").m 1 with
        | Some f -> expect (f.frame.interrupted_cause = Some (cause_annotate (cause_interrupt (Some 0)) (stack_annotations_of 1))) "the recorded cause on the supervision face differs"
        | None -> fail "no child");
  ]

let count = List.length witnesses
