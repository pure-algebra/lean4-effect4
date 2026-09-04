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

(* `raceRows`: `raceLaunched` (`0`) and `raceSettled` (`2`); `1` was `raceSkipped`, retired
   with R2-11 (`57924eb`). *)
let race_rows (s : snap) : int list list =
  List.filter_map
    (function
      | RaceLaunched (r, e) -> Some [ 0; r; e ]
      | RaceSettled (r, _) -> Some [ 2; r ]
      | _ -> None)
    s.m.trace

(* `unlaunchedOf` (`Witnesses.lean`): how many entrants of a race were never forked. *)
let unlaunched_of (s : snap) (race : int) : int option =
  match race_opt s.m race with Some r -> Some (List.length r.programs) | None -> None

let resume_and_exit_order (s : snap) : int list list =
  List.filter_map
    (function
      | ResumedWith (f, token, _) -> Some [ 0; f; token ]
      | Exited (f, _) -> Some [ 1; f ]
      | _ -> None)
    s.m.trace

let callback_rows (s : snap) : (int * exitv) list =
  List.filter_map (function CallbackEv (k, e) -> Some (k, e) | _ -> None) s.m.trace

(* `armedQueueOf` (`Witnesses.lean`): the host callbacks scheduled, in arming order (R2-15). *)
let armed_queue_of (s : snap) : int list = s.m.armed

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

(* `observersOf` (`Witnesses.lean:165`). *)
let observers_of (s : snap) (id : int) : observer list option =
  match fiber_opt s.m id with Some f -> Some f.observers | None -> None

let finalizer_runs (s : snap) (id : int) : int =
  List.length (List.filter (function FinalizerProgram (f, _, _) -> f = id | _ -> false) s.m.trace)

(* `finalizerExits` (`Witnesses.lean:158`): what each finalizer program of `id` was handed. *)
let finalizer_exits (s : snap) (id : int) : exitv list =
  List.filter_map (function FinalizerProgram (f, _, e) when f = id -> Some e | _ -> None) s.m.trace

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
(* `daemonChild` (`Witnesses.lean:232`): `forkDetach`'s child (`:5288-5294`), immediate and
   untracked; since a non-daemon `fork` latches the interrupt-children middleware (R2-6,
   `:5253`) it is the only child that outlives its parent's exit. *)
let daemon_child = { start_immediately = true; daemon = true; mask_mode = Minherit }

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
(* The child is a daemon since R2-6: the root's exit leaves it (`Witnesses.lean:319-322`). *)
let w2 () =
  replay (PforkOnly (w2_child, daemon_child))
    [ Devaluate 0; DinterruptFrom (Some 0, [], 1); DanswerAsync (1, 0, Aval Vunit) ]
let w2_pending () =
  replay (PforkOnly (w2_child, daemon_child)) [ Devaluate 0; DinterruptFrom (Some 0, [], 1) ]

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
(* `w5ForkLatches` (`Witnesses.lean:497`): nothing on the tape but the root's start; the
   `fork` itself latches the middleware (R2-6). *)
let w5_fork_latches () = replay w5_program [ Devaluate 0 ]
(* `w5Daemon` (`:502`): one parked *daemon* child, then return (`daemonSurvivesParentExit`). *)
let w5_daemon () =
  replay (PseqOf (PforkOnly (Ppark 1, daemon_child), Pvalue Vunit)) [ Devaluate 0 ]
let w5_await_all_children () =
  replay
    (PseqOf (PforkOnly (Ppark 1, immediate_child), PawaitAllNew (PforkOnly (Pvalue (Vnat 5), deferred_child))))
    [ Devaluate 0; Dfire 0 ]
(* `w5AwaitAllChildrenFails` (`57924eb`, R2-7): the await is `onExit`'s finalizer, so it runs
   on the body's failure too. *)
let w5_await_all_children_fails_program =
  PawaitAllNew (PseqOf (PforkOnly (Pvalue (Vnat 5), deferred_child), PfailCause (cause_fail boom)))
let w5_await_all_children_fails () = replay w5_await_all_children_fails_program [ Devaluate 0 ]
let w5_await_all_children_fails_fired () = replay w5_await_all_children_fails_program [ Devaluate 0; Dfire 0 ]

(* W6 *)
let w6_link_then_close () =
  replay ~seed:scope_state
    (PseqOf (PforkInScope (Ppark 1, scoped_child, 0, 100), PcloseScopeOf (0, Esuccess Vunit)))
    [ Devaluate 0 ]
let w6_closed_scope () =
  replay ~seed:scope_state (PforkInScope (Ppark 1, scoped_child, 1, 100)) [ Devaluate 0 ]
let w6_drops_key () =
  replay ~seed:scope_state (PforkInScope (Pvalue (Vnat 3), scoped_child, 0, 100)) [ Devaluate 0 ]
(* `w6DeferredLinked` (`57924eb`, R2-8): the same child started on the parent's dispatcher. *)
let deferred_scoped_child = { start_immediately = false; daemon = true; mask_mode = Minherit }
let w6_deferred_linked () =
  replay ~seed:scope_state (PforkInScope (Pvalue (Vnat 3), deferred_scoped_child, 0, 100)) [ Devaluate 0 ]
let w6_deferred_linked_fired () =
  replay ~seed:scope_state (PforkInScope (Pvalue (Vnat 3), deferred_scoped_child, 0, 100)) [ Devaluate 0; Dfire 0 ]
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
  replay (PforkOnly (w10_masked_child, daemon_child))
    [ Devaluate 0; DinterruptFrom (Some 0, [], 1); DanswerAsync (1, 0, Aval Vunit) ]
let w10_masked_pending () =
  replay (PforkOnly (w10_masked_child, daemon_child))
    [ Devaluate 0; DinterruptFrom (Some 0, [], 1) ]
let w10_into () =
  replay ~seed:one_cell (PintoDeferred (PfailCause (cause_fail boom), d0)) [ Devaluate 0 ]

(* W11 *)
let w11_parked () =
  replay ~seed:one_cell (PforkOnly (PawaitDeferred d0, daemon_child)) [ Devaluate 0 ]
let w11_cancelled () =
  replay ~seed:one_cell (PforkOnly (PawaitDeferred d0, daemon_child))
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

(* W8, continued -- R2-14: a child that yields parks on its own dispatcher, which
   `runSyncExit` does not flush. *)
let w8_sync_child_yield () : exitv * snap =
  let m = setup () in
  let e = run_sync_exit m fuel (prog_of (PforkThen (PyieldNow 0, immediate_child, MJoin))) in
  (e, snapshot m 0)

(* W15 -- R2-15: the host runs scheduled callbacks in arming order. *)
let w15_program =
  PseqOf (PforkOnly (PseqOf (Ppark 1, PyieldNow 0), daemon_child), PforkOnly (PyieldNow 0, daemon_child))
let w15_armed () = replay w15_program [ Devaluate 0; DanswerAsync (1, 0, Aval Vunit) ]
let w15_flushed () = replay w15_program [ Devaluate 0; DanswerAsync (1, 0, Aval Vunit); Dflush ]

(* W9 *)
let w9_two_yields = PseqOf (PyieldNow 0, PseqOf (PyieldNow 0, Pvalue (Vnat 1)))
let w9_after_one_fire () = replay w9_two_yields [ Devaluate 0; Dfire 0 ]
let w9_after_two_fires () = replay w9_two_yields [ Devaluate 0; Dfire 0; Dfire 0 ]

(* W12, continued -- `fiberAwaitAll` in input order (R2-4) *)
let w12_input_order_program =
  PseqOf (PforkOnly (Ppark 1, deferred_child), PseqOf (PforkOnly (Pvalue (Vnat 4), deferred_child), PawaitFibers [ 1; 2 ]))
let w12_input_order () =
  replay w12_input_order_program [ Devaluate 0; Dfire 0; DanswerAsync (1, 1, Aval (Vnat 3)) ]
let w12_input_order_parked () = replay w12_input_order_program [ Devaluate 0; Dfire 0 ]

(* W14 -- a join park's cleanup drops the observer (R2-3) *)
let w14_program = PseqOf (PforkOnly (Ppark 1, daemon_child), PforkOnly (PjoinFiber (1, MJoin), daemon_child))
let w14_parked () = replay w14_program [ Devaluate 0 ]
let w14_cancelled () = replay w14_program [ Devaluate 0; DinterruptFrom (Some 0, [], 2) ]

(* W3, continued -- the race park's cleanup and the masked settle (R2-12, R2-13) *)
let w3_host_interrupted () = replay (PraceOf RnparkOnly) [ Devaluate 0; DinterruptFrom (Some 0, [], 0) ]
let w3_host_parked () = replay (PraceOf RnparkOnly) [ Devaluate 0 ]
let w3_parked_loser () = replay (PraceOf RnparkThenSuccess) [ Devaluate 0 ]

(* W13 -- a completing `sync` sees the interrupt its waiter records (R2-1) *)
let w13_waiter = PseqOf (PawaitDeferred d0, PfinalizerOf (FininterruptFiber (0, false), Esuccess Vunit))
let w13 () =
  replay ~seed:one_cell
    (PseqOf
       ( PforkOnly (w13_waiter, daemon_child),
         PonExitOf (PsyncOp (SdeferredCompleteWith (d0, CoofExit (Esuccess (Vnat 7)))), Finrelease (9, false), false) ))
    [ Devaluate 0 ]
let w13_sync_under_on_exit () =
  replay ~seed:one_cell
    (PonExitOf (PsyncOp (SdeferredCompleteWith (d0, CoofExit (Esuccess (Vnat 7)))), FinparkThen 1, false))
    [ Devaluate 0 ]
let w13_sync_under_on_exit_answered () =
  replay ~seed:one_cell
    (PonExitOf (PsyncOp (SdeferredCompleteWith (d0, CoofExit (Esuccess (Vnat 7)))), FinparkThen 1, false))
    [ Devaluate 0; DanswerAsync (0, 0, Aval Vunit) ]

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
    theorem "w1_deferred_join_parent" "Witnesses.lean:290" [ ("w1DeferredJoin", w1_deferred_join) ]
      (fun d -> expect (exit_of (d "w1DeferredJoin") 0 = Some (Esuccess (Vnat 42))) "the parent does not exit with the joined child's success");
    theorem "w1_deferred_join_child" "Witnesses.lean:294" [ ("w1DeferredJoin", w1_deferred_join) ]
      (fun d ->
        let s = d "w1DeferredJoin" in
        expect (exit_of s 1 = Some (Esuccess (Vnat 42)) && fiber_count s = 2) "the child does not exit with 42 in a two-fiber machine");
    theorem "w1_deferred_start_is_a_task" "Witnesses.lean:300" [ ("w1DeferredJoin[evaluate 0]", w1_deferred_join_no_fire) ]
      (fun d ->
        let s = d "w1DeferredJoin[evaluate 0]" in
        expect (exit_of s 1 = None && armed_of s 0 = Some true) "before the fire the child ran, or the parent's dispatcher is not armed");
    theorem "w1_immediate_join" "Witnesses.lean:310" [ ("w1ImmediateJoin", w1_immediate_join) ]
      (fun d ->
        let s = d "w1ImmediateJoin" in
        expect (exit_of s 0 = Some (Esuccess (Vnat 42)) && exit_of s 1 = Some (Esuccess (Vnat 42))) "the same exits with no fire: differ");
    theorem "w1_await_is_a_value" "Witnesses.lean:316" [ ("w1AwaitFailing", w1_await_failing) ]
      (fun d ->
        (* W1-1/W1-8: `Val.exitErr (Cause.fail (Err.tag 7))` is the wire's `Vnone`. *)
        expect (exit_of (d "w1AwaitFailing") 0 = Some (Esuccess Vnone)) "the parent did not succeed with the child's failed exit as a value");
    theorem "w1_join_is_an_effect" "Witnesses.lean:322" [ ("w1JoinFailing", w1_join_failing) ]
      (fun d -> expect (exit_of (d "w1JoinFailing") 0 = Some (Efailure (cause_fail 7))) "the parent did not fail with the child's cause");
    (* W2 -- masked interrupt *)
    theorem "w2_delivered_at_unmask" "Witnesses.lean:348" [ ("w2", w2) ]
      (fun d -> expect (exit_of (d "w2") 1 = Some (interrupted_by 0 1)) "the child does not exit with the interrupt cause at the unmask");
    theorem "w2_recorded_once" "Witnesses.lean:352" [ ("w2", w2) ]
      (fun d -> expect (interrupt_rows (d "w2") = [ (Some 0, 1) ]) "the interrupt is not recorded exactly once");
    theorem "w2_finalizer_runs_once" "Witnesses.lean:355" [ ("w2", w2) ]
      (fun d -> expect (finalizer_runs (d "w2") 1 = 1) "the finalizer did not run exactly once");
    theorem "w2_masked_interrupt_does_not_apply" "Witnesses.lean:359" [ ("w2[pending]", w2_pending) ]
      (fun d -> expect (exit_of (d "w2[pending]") 1 = None) "the masked child exited before the async was answered");
    (* W3 -- raceAll *)
    theorem "w3_empty_is_a_frontier" "Witnesses.lean:386" [ ("w3EmptyPending", w3_empty_pending) ]
      (fun d ->
        let s = d "w3EmptyPending" in
        expect (exit_of s 0 = None && parked_of s 0 = Some (WithGuard 0) && fiber_count s = 1) "the empty race is not a live frontier on its race token");
    theorem "w3_empty_until_interrupted" "Witnesses.lean:392" [ ("w3EmptyInterrupted", w3_empty_interrupted) ]
      (fun d -> expect (exit_of (d "w3EmptyInterrupted") 0 = Some (interrupted_by 0 0)) "the empty race did not end with the host's interruption");
    theorem "w3_immediate_success_stops_launch" "Witnesses.lean:400" [ ("w3StopsLaunch", w3_stops_launch) ]
      (fun d ->
        let s = d "w3StopsLaunch" in
        (* R2-11 (`57924eb`, `E4-RUN-CE-035`): the register loop breaks once done -- two
           fibers, one entrant program never forked, nothing interrupted *)
        all [ expect (exit_of s 0 = Some (Esuccess (Vnat 1))) "the host did not answer the first entrant's success";
              expect (race_rows s = [ [ 0; 0; 1 ]; [ 2; 0 ] ]) "the race rows differ (launch, settle)";
              expect (fiber_count s = 2) "not two fibers";
              expect (unlaunched_of s 0 = Some 1) "one entrant program was not left unlaunched";
              expect (interrupt_rows s = []) "something was interrupted";
              expect (exit_of s 2 = None) "a third fiber exists" ]);
    theorem "w3_failure_allows_next_launch" "Witnesses.lean:411" [ ("w3NextLaunch", w3_next_launch) ]
      (fun d ->
        let s = d "w3NextLaunch" in
        expect (exit_of s 0 = Some (Esuccess (Vnat 9)) && race_rows s = [ [ 0; 0; 1 ]; [ 0; 0; 2 ]; [ 2; 0 ] ]) "a failure settled the race, or the next entrant did not launch");
    theorem "w3_all_failures_retain_order" "Witnesses.lean:418" [ ("w3AllFail", w3_all_fail) ]
      (fun d -> expect (exit_of (d "w3AllFail") 0 = Some (Efailure { reasons = [ Rfail 1; Rfail 2 ]; annotations = [] })) "the all-failed race does not fail with the retained causes in launch order");
    (* W4 -- a sibling completes a Deferred *)
    theorem "w4_sibling_resumes" "Witnesses.lean:476" [ ("w4Sibling", w4_sibling) ]
      (fun d ->
        let s = d "w4Sibling" in
        all [ expect (exit_of s 1 = Some (Esuccess (Vnat 7))) "A was not resumed with the stored 7";
              expect (exit_of s 2 = Some (Esuccess (Vbool true))) "B's completion did not answer true";
              expect (exit_of s 0 = Some (Esuccess (fiber_value s 2))) "the parent's answer is not B's handle (W1-1)" ]);
    theorem "w4_completion_resumes_on_the_spot" "Witnesses.lean:485" [ ("w4SiblingThenMore", w4_sibling_then_more); ("w4Sibling", w4_sibling) ]
      (fun d ->
        let a = d "w4SiblingThenMore" and b = d "w4Sibling" in
        all [ expect (resume_and_exit_order a = [ [ 0; 1; 0 ]; [ 1; 1 ]; [ 1; 2 ]; [ 1; 0 ] ]) "M1: the waiter is not resumed inside the completion when it is not the last primitive";
              expect (exit_of a 1 = Some (Esuccess (Vnat 7))) "A's exit differs";
              expect (resume_and_exit_order b = [ [ 0; 1; 0 ]; [ 1; 1 ]; [ 1; 2 ]; [ 1; 0 ] ]) "M1: the waiter is not resumed inside the completion when it is the last primitive" ]);
    theorem "w4_complete_twice_answers_false" "Witnesses.lean:492" [ ("w4CompleteTwice", w4_complete_twice) ]
      (fun d -> expect (exit_of (d "w4CompleteTwice") 0 = Some (Esuccess (Vbool false))) "the second completion did not answer false");
    theorem "w4_interrupt_reaches_the_waiter" "Witnesses.lean:497" [ ("w4InterruptWaiter", w4_interrupt_waiter) ]
      (fun d ->
        let s = d "w4InterruptWaiter" in
        expect (exit_of s 1 = Some (Efailure (cause_interrupt (Some 2))) && exit_of s 2 = Some (Esuccess (Vbool true))) "the recorded interruptor is not the completing fiber, or the waiter was not resumed with it");
    (* W5 -- children after the parent's exit *)
    theorem "w5_middleware_interrupts_children" "Witnesses.lean:537" [ ("w5WithMiddleware", w5_with_middleware) ]
      (fun d ->
        let s = d "w5WithMiddleware" in
        all [ expect (exit_of s 1 = Some (interrupted_with 0 1 (stack_annotations_of 0))) "the child was not interrupted with the parent's id and stack annotations (R2-5)";
              expect (children_interrupted_rows s = [ (0, [ 1 ]) ]) "no childrenInterrupted row";
              expect (interrupt_rows s = [ (Some 0, 1) ]) "the interrupt rows differ";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the parent's exit differs" ]);
    theorem "w5_fork_latches_the_middleware" "Witnesses.lean:547" [ ("w5ForkLatches", w5_fork_latches); ("w5WithMiddleware", w5_with_middleware) ]
      (fun d ->
        let s = d "w5ForkLatches" and w = d "w5WithMiddleware" in
        all [ expect s.m.middleware_installed "the fork did not latch the middleware (R2-6)";
              expect (exit_of s 1 = exit_of w 1) "the child's exit differs from the tape-installed run";
              expect (children_interrupted_rows s = [ (0, [ 1 ]) ]) "no childrenInterrupted row";
              expect (interrupt_rows s = [ (Some 0, 1) ]) "the interrupt rows differ";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the parent's exit differs" ]);
    theorem "w5_daemon_child_survives_parent_exit" "Witnesses.lean:557" [ ("w5Daemon", w5_daemon) ]
      (fun d ->
        let s = d "w5Daemon" in
        all [ expect (not s.m.middleware_installed) "a daemon fork latched the middleware";
              expect (exit_of s 1 = None) "the daemon child did not survive the parent's exit";
              expect (children_interrupted_rows s = [] && interrupt_rows s = []) "the daemon child was interrupted";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the parent's exit differs" ]);
    theorem "w5_await_all_children_on_failure" "Witnesses.lean:583" [ ("w5AwaitAllChildrenFails", w5_await_all_children_fails); ("w5AwaitAllChildrenFailsFired", w5_await_all_children_fails_fired) ]
      (fun d ->
        let p = d "w5AwaitAllChildrenFails" and s = d "w5AwaitAllChildrenFailsFired" in
        all [ expect (exit_of p 0 = None && exit_of p 1 = None) "the failing parent did not await its new child (R2-7)";
              expect (parked_of p 0 = Some (WithGuard 0)) "the parent is not parked on token 0";
              expect (exit_of s 1 = Some (Esuccess (Vnat 5))) "the child did not end by its own exit";
              expect (exit_of s 0 = Some (Efailure (cause_fail boom))) "the parent did not fail with its body's failure after the await";
              expect (finalizer_runs s 0 = 1) "the await finalizer did not run once" ]);
    theorem "w5_await_all_children_awaits_only_new" "Witnesses.lean:595" [ ("w5AwaitAllChildren", w5_await_all_children) ]
      (fun d ->
        let s = d "w5AwaitAllChildren" in
        all [ expect (exit_of s 2 = Some (Esuccess (Vnat 5))) "the new child's exit differs";
              (* R2-7: `awaitAllChildren(self)` answers the body's own value, the fork's handle (W1-1) *)
              expect (exit_of s 0 = Some (Esuccess (fiber_value s 2))) "the parent did not answer its body's value (the handle) although child 1 never exits";
              (* R2-6: the pre-existing tracked child is then interrupted by the parent's exit path *)
              expect (children_interrupted_rows s = [ (0, [ 1 ]) ]) "the parent's exit did not interrupt its tracked child";
              expect (exit_of s 1 = Some (interrupted_with 0 1 (stack_annotations_of 0))) "child 1 was not interrupted with the parent's id and annotations" ]);
    (* W6 -- scope linkage *)
    theorem "w6_link_then_close" "Witnesses.lean:651" [ ("w6LinkThenClose", w6_link_then_close) ]
      (fun d ->
        let s = d "w6LinkThenClose" in
        all [ expect (scope_rows s = [ [ 0; 0; 100; 1 ] ]) "the linkage row differs (mode erased)";
              expect (exit_of s 1 = Some (interrupted_with 0 1 (stack_annotations_of 0))) "the child was not interrupted by the closer with the closer's stack annotations (R2-5)";
              expect (scope_keys s 0 = Some []) "the key was not dropped by the child's exit observer";
              expect (scope_closed s 0 = Some true) "the scope did not end Closed";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the closer's exit differs" ]);
    theorem "w6_close_interrupt_carries_closer_annotations" "Witnesses.lean:664" [ ("w6LinkThenClose", w6_link_then_close); ("w2", w2) ]
      (fun d ->
        (* R2-5 (`E4-RUN-CE-030`); F1-4: the avatar annotates the cause, so one key list per exit *)
        all [ expect (Option.map cause_keys (exit_of (d "w6LinkThenClose") 1) = Some [ "stack1"; "stack0" ]) "the close's interrupt does not carry the closer's key on top of the child's";
              expect (Option.map cause_keys (exit_of (d "w2") 1) = Some [ "stack1" ]) "a tape interrupt with empty annotations carries more than the child's own key" ]);
    theorem "w6_closed_scope_interrupts_now" "Witnesses.lean:680" [ ("w6ClosedScope", w6_closed_scope) ]
      (fun d ->
        let s = d "w6ClosedScope" in
        all [ expect (scope_rows s = [ [ 1; 1; 1 ] ]) "no scopeClosedOnLink row";
              expect (exit_of s 1 = Some (interrupted_with 0 1 (stack_annotations_of 0))) "the child was not interrupted at once with the parent's id and annotations";
              expect (Option.map cause_keys (exit_of s 1) = Some [ "stack1"; "stack0" ]) "the cause does not carry the child's key then the parent's (M10)" ]);
    theorem "w6_runIn_closed_scope_uses_no_caller_annotations" "Witnesses.lean:690" [ ("w6ClosedRunIn", w6_closed_run_in) ]
      (fun d ->
        let s = d "w6ClosedRunIn" in
        all [ expect (scope_rows s = [ [ 1; 1; 1 ] ]) "no scopeClosedOnLink row";
              expect (exit_of s 1 = Some (interrupted_by 1 1)) "the run-in fiber was not interrupted with its own id";
              expect (Option.map cause_keys (exit_of s 1) = Some [ "stack1" ]) "the cause carries caller annotations (M10)";
              expect (exit_of s 0 = Some (Esuccess Vunit)) "the caller's exit differs" ]);
    theorem "w6_child_exit_drops_key" "Witnesses.lean:700" [ ("w6DropsKey", w6_drops_key) ]
      (fun d ->
        let s = d "w6DropsKey" in
        (* R2-8 (`E4-RUN-CE-036`): an immediately finished child is never linked *)
        all [ expect (exit_of s 1 = Some (Esuccess (Vnat 3))) "the child's exit differs";
              expect (scope_rows s = []) "an immediately finished child was linked";
              expect (scope_keys s 0 = Some []) "a key was left on the scope" ]);
    theorem "w6_deferred_child_is_linked" "Witnesses.lean:718" [ ("w6DeferredLinked", w6_deferred_linked); ("w6DeferredLinkedFired", w6_deferred_linked_fired) ]
      (fun d ->
        let p = d "w6DeferredLinked" and s = d "w6DeferredLinkedFired" in
        all [ expect (scope_rows p = [ [ 0; 0; 100; 1 ] ]) "a deferred child was not linked (mode erased, F1-1)";
              expect (scope_keys p 0 = Some [ 100 ] && exit_of p 1 = None) "the key is not registered while the child has not run";
              expect (exit_of s 1 = Some (Esuccess (Vnat 3)) && scope_keys s 0 = Some []) "the child's later exit did not drop the key" ]);
    theorem "w6_self_interruptor_skipped" "Witnesses.lean:727" [ ("w6SelfInterruptorSkipped", w6_self_interruptor_skipped) ]
      (fun d ->
        let s = d "w6SelfInterruptorSkipped" in
        expect (interrupt_rows s = [] && exit_of s 0 = Some (Esuccess Vunit)) "the self-interruptor was not skipped");
    (* W6b -- the two close strategies *)
    theorem "w6_sequential_captures_and_merges" "Witnesses.lean:758" [ ("w6Sequential", w6_sequential) ]
      (fun d ->
        let s = d "w6Sequential" in
        all [ expect (exit_of s 0 = Some (Efailure { reasons = [ Rfail 2 ]; annotations = [] })) "the sequential close did not capture the failing finalizer and answer the merge";
              expect (fiber_count s = 1) "the sequential close forked";
              expect (scope_closed s 3 = Some true) "the scope did not close" ]);
    theorem "w6_parallel_forks_and_merges" "Witnesses.lean:766" [ ("w6Parallel", w6_parallel) ]
      (fun d ->
        let s = d "w6Parallel" in
        all [ expect (fiber_count s = 3) "the parallel close did not fork one daemon per finalizer";
              expect (exit_of s 1 = Some (Efailure { reasons = [ Rfail 4 ]; annotations = [] })) "the first finalizer's exit differs";
              expect (exit_of s 2 = Some (Esuccess Vunit)) "the second finalizer's exit differs";
              expect (exit_of s 0 = Some (Efailure { reasons = [ Rfail 4 ]; annotations = [] })) "every awaited exit was not merged (M6)";
              expect (scope_closed s 4 = Some true) "the scope did not close" ]);
    (* W10 -- a program that masks its own fiber *)
    theorem "w10_program_masks_its_own_fiber" "Witnesses.lean:803" [ ("w10MaskedPending", w10_masked_pending); ("w10Masked", w10_masked) ]
      (fun d ->
        let p = d "w10MaskedPending" and s = d "w10Masked" in
        all [ expect (exit_of p 1 = None) "the masked fiber exited while masked";
              expect (interrupt_rows s = [ (Some 0, 1) ]) "the interrupt was not recorded once";
              expect (exit_of s 1 = Some (interrupted_by 0 1)) "the cause was not delivered by the restoring frame" ]);
    theorem "w10_into_completes_on_failure" "Witnesses.lean:818" [ ("w10Into", w10_into) ]
      (fun d ->
        let s = d "w10Into" in
        (* W1-2: the slot holds the `Completion`, where Lean holds `Prim.failure (Cause.fail Err.boom)`. *)
        expect (exit_of s 0 = Some (Esuccess (Vbool true)) && completion_of s 0 = Some (Some (CoofExit (Efailure (cause_fail boom))))) "`into` did not answer true and store the failed exit");
    (* W11 -- an interrupted Async runs its cancel *)
    theorem "w11_cancel_splices_the_waiter" "Witnesses.lean:851" [ ("w11Parked", w11_parked); ("w11Cancelled", w11_cancelled) ]
      (fun d ->
        let p = d "w11Parked" and c = d "w11Cancelled" in
        all [ expect (waiters_of p 0 = Some [ (1, 0) ]) "parking did not register the waiter";
              expect (waiters_of c 0 = Some []) "the cancel did not splice the waiter out (M3)";
              expect (exit_of c 1 = Some (interrupted_by 0 1)) "the cancel did not re-fail with the passing cause" ]);
    (* W12 -- awaitAll answers the exits it collected *)
    theorem "w12_awaitAll_answers_the_exits" "Witnesses.lean:873" [ ("w12AwaitAll", w12_await_all) ]
      (fun d ->
        (* W1-8: `exitsVal` at this alphabet is `[some 4; none]`; the failure's reasons do not survive. *)
        expect (exit_of (d "w12AwaitAll") 0 = Some (Esuccess (exits_val [ Esuccess (Vnat 4); Efailure (cause_fail 5) ]))) "the parent's answer is not the two exits in collection order");
    theorem "w12_awaitAll_input_order" "Witnesses.lean:906" [ ("w12InputOrder", w12_input_order); ("w12InputOrderParked", w12_input_order_parked) ]
      (fun d ->
        let s = d "w12InputOrder" and p = d "w12InputOrderParked" in
        all [ expect (exit_of s 0 = Some (Esuccess (exits_val [ Esuccess (Vnat 3); Esuccess (Vnat 4) ]))) "the exits are not answered in input order (R2-4)";
              expect (exit_of p 2 = Some (Esuccess (Vnat 4))) "the second child did not finish first";
              expect (observers_of p 1 = Some [ UntrackChild 0; Countdown (0, 0) ]) "the awaiter does not observe the first live target only";
              expect (observers_of p 2 = Some []) "the exited target carries an observer";
              expect (parked_of p 0 = Some (WithGuard 0)) "the awaiter is not parked on token 0" ]);
    (* W13 -- an unknown scope key halts the machine *)
    theorem "w13_unknown_scope_is_stuck" "Witnesses.lean:932" [ ("w13UnknownScope", w13_unknown_scope) ]
      (fun d ->
        let s = d "w13UnknownScope" in
        expect (s.m.stuck = Some (UnknownScope 99) && exit_of s 0 = None && s.arm = 2) "closing an unknown scope is not a stuck machine with the fiber unexited");
    theorem "w13_unknown_link_is_stuck" "Witnesses.lean:940" [ ("w13UnknownLink", w13_unknown_link) ]
      (fun d ->
        let s = d "w13UnknownLink" in
        expect (s.m.stuck = Some (UnknownScope 99) && s.arm = 2) "linking into an unknown scope is not a stuck machine");
    (* W7 -- the ref.* quirks *)
    theorem "w7_set_answers_the_cell" "Witnesses.lean:972" [ ("w7Set", w7_set) ]
      (fun d ->
        let s = d "w7Set" in
        expect (exit_of s 0 = Some (Esuccess (Vhandle 0)) && s.refs = [ Vnat 5 ]) "`set` did not answer the cell and write the value");
    theorem "w7_update_answers_void" "Witnesses.lean:978" [ ("w7Update", w7_update) ]
      (fun d ->
        let s = d "w7Update" in
        expect (exit_of s 0 = Some (Esuccess Vunit) && s.refs = [ Vnat 2 ]) "`update` did not answer void with the function applied once");
    theorem "w7_modify_some_writes_back_the_read" "Witnesses.lean:984" [ ("w7ModifySome", w7_modify_some) ]
      (fun d ->
        let s = d "w7ModifySome" in
        expect (exit_of s 0 = Some (Esuccess (Vnat 1)) && s.refs = [ Vnat 1 ]) "`modifySome` on `None` did not write back the read");
    theorem "w7_update_some_and_get_rereads" "Witnesses.lean:991" [ ("w7UpdateSomeAndGet", w7_update_some_and_get); ("w7GetAndUpdateSome", w7_get_and_update_some) ]
      (fun d ->
        expect (exit_of (d "w7UpdateSomeAndGet") 0 = Some (Esuccess (Vnat 0)) && exit_of (d "w7GetAndUpdateSome") 0 = Some (Esuccess (Vnat 3))) "the fresh read after the write / the read before it differ");
    (* W8 -- the runtime entries *)
    theorem "w8_sync_exit_async_fiber_error" "Witnesses.lean:1025" []
      (fun _ -> expect (w8_sync_exit () = Efailure (cause_die "AsyncFiberError")) "a root that survives the flush is not the `AsyncFiberError` defect");
    theorem "w8_sync_child_yield_is_async" "Witnesses.lean:1032" []
      (fun _ ->
        let e, s = w8_sync_child_yield () in
        let root_exit = exit_of s 0 and queue = armed_queue_of s in
        step_decision s.m fuel Dflush;
        let after = exit_of s 0 in
        all [ expect (e = Efailure (cause_die "AsyncFiberError")) "the entry did not answer AsyncFiberError (R2-14)";
              expect (root_exit = None) "the root exited";
              expect (queue = [ 1 ]) "the child's callback is not the one scheduled";
              expect (after = Some (Esuccess Vunit)) "once the host runs the callback the root did not complete" ]);
    theorem "w8_sync_exit_value" "Witnesses.lean:1041" []
      (fun _ -> expect (w8_sync_value () = Esuccess (Vnat 3)) "a root that finishes does not answer its exit");
    theorem "w8_callback_fires" "Witnesses.lean:1044" [ ("w8Callback", w8_callback) ]
      (fun d -> expect (callback_rows (d "w8Callback") = [ (77, Esuccess (Vnat 3)) ]) "the callback observer did not deliver the root's exit under its key");
    theorem "w8_promise_squashes" "Witnesses.lean:1047" []
      (fun _ -> expect (w8_promise () = Error (Sq_error 4)) "`promiseOutcome` does not squash to the first `Fail` ahead of the defect");
    (* W15 -- R2-15 *)
    theorem "w15_flush_runs_callbacks_in_arming_order" "Witnesses.lean:1089" [ ("w15Armed", w15_armed); ("w15Flushed", w15_flushed) ]
      (fun d ->
        let a = d "w15Armed" and f = d "w15Flushed" in
        all [ expect (armed_queue_of a = [ 2; 1 ]) "the schedule is not [2; 1] (2 armed before 1)";
              expect (armed_of a 1 = Some true && armed_of a 2 = Some true) "both dispatchers are not armed";
              expect (armed_queue_of f = []) "the flush left callbacks scheduled";
              expect (resume_and_exit_order f = [ [ 1; 0 ]; [ 0; 1; 0 ]; [ 0; 2; 1 ]; [ 1; 2 ]; [ 0; 1; 2 ]; [ 1; 1 ] ]) "the flush did not run 2's callback before 1's (arming order)" ]);
    (* W13 -- R2-1 *)
    theorem "w13_completion_pop_sees_the_waiter_interrupt" "Witnesses.lean:1147" [ ("w13", w13) ]
      (fun d ->
        let s = d "w13" in
        let by_waiter = interrupted_with 1 0 (stack_annotations_of 1) in
        all [ expect (finalizer_runs s 0 = 1) "the finalizer under the completing sync did not run exactly once";
              expect (finalizer_exits s 0 = [ by_waiter ]) "the finalizer was not handed the interrupt the waiter recorded during the sync (R2-1)";
              expect (exit_of s 0 = Some by_waiter) "the completer did not exit with the waiter's interrupt";
              expect (Option.map cause_keys (exit_of s 0) = Some [ "stack0"; "stack1" ]) "the cause is not annotated from 0's stack then 1's (R2-5)";
              expect (interrupt_rows s = [ (Some 1, 0) ]) "the interrupt rows differ";
              expect (exit_of s 1 = Some (Esuccess Vunit)) "the waiter's `fiberInterrupt` did not answer void after the target's exit";
              expect (resume_and_exit_order s = [ [ 0; 1; 0 ]; [ 1; 0 ]; [ 0; 1; 1 ]; [ 1; 1 ] ]) "the resume/exit order differs" ]);
    theorem "w13_sync_meets_the_finalizer_program" "Witnesses.lean:1160" [ ("w13SyncUnderOnExit", w13_sync_under_on_exit); ("w13SyncUnderOnExitAnswered", w13_sync_under_on_exit_answered) ]
      (fun d ->
        let p = d "w13SyncUnderOnExit" and a = d "w13SyncUnderOnExitAnswered" in
        (* The avatar's `onExit` always ran the finalizer *program* (`on_exit_program`,
           `deep_stores.ml`): R2-1's second half never had a pure stand-in here. *)
        all [ expect (finalizer_runs p 0 = 1) "the finalizer program did not run once";
              expect (finalizer_exits p 0 = [ Esuccess (Vbool true) ]) "the finalizer was not handed the thunk's success";
              expect (exit_of p 0 = None && parked_of p 0 = Some (WithGuard 0)) "the finalizer's park did not park the fiber on token 0";
              expect (exit_of a 0 = Some (Esuccess (Vbool true)) && finalizer_runs a 0 = 1) "the answer did not restore the thunk's exit" ]);
    (* W14 -- R2-3 *)
    theorem "w14_join_cleanup_drops_the_observer" "Witnesses.lean:1190" [ ("w14Parked", w14_parked); ("w14Cancelled", w14_cancelled) ]
      (fun d ->
        let p = d "w14Parked" and c = d "w14Cancelled" in
        (* `(stackOf w14Parked 2).map List.length = some 1`: the cleanup frame is the `Acause`
           arm of the closure the joiner parked on (DIVERGENCE 1), not a stack entry; the
           conjunct has no avatar shape and the rest is stated. *)
        all [ expect (observers_of p 1 = Some [ ResumeAwait (2, 1, MJoin) ]) "the target does not carry the joiner's resume observer";
              expect (parked_of p 2 = Some (WithGuard 1)) "the joiner is not parked on token 1";
              expect (observers_of c 1 = Some []) "the cleanup did not drop the observer (R2-3)";
              expect (exit_of c 2 = Some (interrupted_by 0 2)) "the joiner did not re-fail with the interrupt";
              expect (exit_of c 1 = None) "the target was touched";
              expect (interrupt_rows c = [ (Some 0, 2) ]) "the interrupt rows differ" ]);
    (* W3, continued -- R2-12, R2-13 *)
    theorem "w3_host_interrupt_cancels_entrants" "Witnesses.lean:1218" [ ("w3HostParked", w3_host_parked); ("w3HostInterrupted", w3_host_interrupted) ]
      (fun d ->
        let p = d "w3HostParked" and s = d "w3HostInterrupted" in
        (* the `stackOf` conjunct: as in W14, the cleanup is the closure's arm *)
        all [ expect (exit_of p 1 = None) "the entrant did not park";
              expect (exit_of s 1 = Some (interrupted_with 0 1 (stack_annotations_of 0))) "the cleanup did not interrupt the live entrant with the host's id and annotations (R2-13)";
              expect (exit_of s 0 = Some (interrupted_by 0 0)) "the host did not re-fail with its own interrupt";
              expect (interrupt_rows s = [ (Some 0, 0); (Some 0, 1) ]) "the interrupt rows differ";
              expect (race_rows s = [ [ 0; 0; 1 ]; [ 2; 0 ] ]) "the race rows differ (launch, settle by the entrant's exit)" ]);
    theorem "w3_settle_interrupts_the_parked_loser" "Witnesses.lean:1231" [ ("w3ParkedLoser", w3_parked_loser) ]
      (fun d ->
        let s = d "w3ParkedLoser" in
        all [ expect (exit_of s 0 = Some (Esuccess (Vnat 2))) "the host did not exit with the winner's value";
              expect (exit_of s 1 = Some (interrupted_with 0 1 (stack_annotations_of 0))) "the host did not interrupt the parked loser itself (R2-12)";
              expect (interrupt_rows s = [ (Some 0, 1) ]) "the interrupt rows differ";
              expect (race_rows s = [ [ 0; 0; 1 ]; [ 0; 0; 2 ]; [ 2; 0 ] ]) "the race rows differ" ]);
    (* the five forbidden examples *)
    theorem "forbidden_observers_and_double_exit" "Witnesses.lean:1242"
      [ ("w1DeferredJoin", w1_deferred_join); ("w2", w2); ("w3AllFail", w3_all_fail); ("w3StopsLaunch", w3_stops_launch);
        ("w4Sibling", w4_sibling); ("w4InterruptWaiter", w4_interrupt_waiter); ("w5WithMiddleware", w5_with_middleware);
        ("w5AwaitAllChildren", w5_await_all_children); ("w6LinkThenClose", w6_link_then_close); ("w6Parallel", w6_parallel);
        ("w9AfterTwoFires", w9_after_two_fires); ("w10Masked", w10_masked); ("w11Cancelled", w11_cancelled); ("w12AwaitAll", w12_await_all);
        ("w13", w13) ]
      (fun d ->
        all
          (List.map
             (fun n -> expect (trace_well_formed (d n)) (n ^ ": an observer fired before its fiber's exit, or a fiber exited twice"))
             [ "w1DeferredJoin"; "w2"; "w3AllFail"; "w3StopsLaunch"; "w4Sibling"; "w4InterruptWaiter"; "w5WithMiddleware";
               "w5AwaitAllChildren"; "w6LinkThenClose"; "w6Parallel"; "w9AfterTwoFires"; "w10Masked"; "w11Cancelled"; "w12AwaitAll"; "w13" ]));
    theorem "forbidden_interrupt_while_running" "Witnesses.lean:1264" []
      (fun _ ->
        let m = setup () in
        let f = add_fiber m in
        f.running <- true;
        let apply = interrupt_record m (Some 0) [] f in
        expect ((not apply) && f.frame.deferred_interrupt) "an interrupt of a running interruptible fiber was applied, or not deferred");
    theorem "forbidden_setInterruptible_as_current" "Witnesses.lean:1275" []
      ~portable:"`Prim.setInterruptible` never sits in `frame.current` here: the avatar's frame is the OCaml stack (DIVERGENCE 1) and the mask change is the `Op_set_interruptible` arm, so the forbidden step has no shape to reach"
      (fun _ -> None);
    theorem "forbidden_no_notImplemented_defect" "Witnesses.lean:1283"
      [ ("w1DeferredJoin", w1_deferred_join); ("w2", w2); ("w3AllFail", w3_all_fail); ("w4Sibling", w4_sibling);
        ("w5WithMiddleware", w5_with_middleware); ("w6LinkThenClose", w6_link_then_close); ("w9AfterTwoFires", w9_after_two_fires);
        ("w10Masked", w10_masked); ("w11Cancelled", w11_cancelled); ("w12AwaitAll", w12_await_all); ("w13", w13) ]
      (fun d ->
        all
          (List.map
             (fun n -> expect (no_not_implemented_defect (d n)) (n ^ ": a fiber exited with the `notImplemented` defect"))
             [ "w1DeferredJoin"; "w2"; "w3AllFail"; "w4Sibling"; "w5WithMiddleware"; "w6LinkThenClose"; "w9AfterTwoFires"; "w10Masked"; "w11Cancelled"; "w12AwaitAll"; "w13" ]));
    theorem "forbidden_task_enqueued_during_drain" "Witnesses.lean:1299" [ ("w9AfterOneFire", w9_after_one_fire) ]
      (fun d ->
        let s = d "w9AfterOneFire" in
        expect (exit_of s 0 = None && armed_of s 0 = Some true && queued_of s 0 = Some 1) "after one fire the task enqueued during the drain did not wait, armed, for the next");
    theorem "w9_next_fire_runs_it" "Witnesses.lean:1305" [ ("w9AfterTwoFires", w9_after_two_fires) ]
      (fun d -> expect (exit_of (d "w9AfterTwoFires") 0 = Some (Esuccess (Vnat 1))) "the next fire did not run it");
    (* DB-07 *)
    theorem "db07_store_survives_failure" "Witnesses.lean:1322" [ ("dbSeven", db_seven) ]
      (fun d ->
        let s = d "dbSeven" in
        expect (exit_of s 0 = Some (Efailure (cause_fail boom)) && s.refs = [ Vnat 5 ]) "the store the failing fiber reached was restored");
    (* `toSched_computes`, `toSup_computes`, `toSup_records_the_interrupt` were retired with the
       old fiber machines (`72698bb`, "Deep is the only fiber machine"): no `Witnesses.lean`
       theorem names them any more, so no entry does. Seat F2. *)
  ]

let count = List.length witnesses
