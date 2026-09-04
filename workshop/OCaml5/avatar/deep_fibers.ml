(* The avatar: `workshop/Deep/Fibers.lean` transcribed into OCaml 5 effect handlers.

   Spike A0, 2026-09-04. One OCaml module for the one Lean file. Every carrier keeps the
   Lean name, the Lean field order and the Lean arm order; every arm cites the same rc.112
   line the Lean arm cites. The places where the OCaml spelling had to differ from the Lean
   one are marked `DIVERGENCE n` and listed in the spike report.

   DIVERGENCE 1 (the frame pair). `RunFiber.frame` is `FrameFiber` (`Runtime.lean:269`), five
   fields: `current`, `stack`, `interruptible`, `interruptedCause`, `deferredInterrupt`. The
   last three are transcribed literally. The first two -- a `Prim` and a `Prim list` -- are
   the OCaml 5 stack itself: an unstarted fiber holds its whole program as a closure, a
   running one is `Onstack`, a parked one is a captured one-shot continuation, and an
   interrupt recorded on an unstarted fiber is `Failing cause` (Lean's
   `current := Prim.failure` over an empty stack). This is the one substitution the thesis is
   about, and the only field pair whose simulation relation is not an equality.

   DIVERGENCE 2 (`Cmd.loop`). Lean's `drive` runs one `iteration` per `Cmd.loop`; in OCaml
   `continue k` runs the fiber to its next `perform`, so `Cmd.loop` has no separate
   existence. `iteration`'s prelude (the deferred-interrupt check, the op counter, the yield
   injection) is `iteration_prelude` below, run at the head of every handler arm -- so the op
   counter counts performs, not `Prim` nodes.

   DIVERGENCE 3 (in place). Lean's machine is a value threaded through pure updates
   (`RunMachine.update`, `modify`, `emit`); the OCaml carrier is the same record with
   `mutable` fields, so `update` and `modify` are the identity.

   DIVERGENCE 4 (nested commands). Lean's `drive` returns the commands a step owes and runs
   them before the rest of the list. The OCaml arms run them inline, at the same point in the
   order, because `retc`/`exnc` execute on the resumed stack rather than inside the
   `match_with` call that installed them. *)

(* ------------------------------------------------------------------------- the tape *)

(* The decision tape, in the golden's own spelling (`harness/trace/fiber-tail.ts`). *)
module Tape = struct
  let entries : (int * bool) list ref = ref []
  let cursor = ref 0

  let load (s : string) =
    entries :=
      String.split_on_char ',' s
      |> List.filter (fun e -> String.length e > 0)
      |> List.map (fun e ->
             match String.split_on_char ':' e with
             | [ site; branch ] -> (int_of_string site, branch = "1")
             | _ -> failwith ("bad tape entry " ^ e));
    cursor := 0

  let site () = !cursor

  let decide () =
    match List.nth_opt !entries !cursor with
    | None -> failwith (Printf.sprintf "TAPE_EXHAUSTED: fork site %d past the end" !cursor)
    | Some (site, branch) ->
      if site <> !cursor then
        failwith (Printf.sprintf "TAPE_SITE_MISMATCH: wanted %d, tape has %d" !cursor site);
      incr cursor;
      branch
end

(* ------------------------------------------------------------------ values and causes *)

(* The one value alphabet the trace wire describes (`Effect4/Target/TypeScript/Trace.lean`). *)
type value =
  | Vunit
  | Vnat of int
  | Vhandle of int
  | Vnone
  | Vsome of value
  | Vlist of value list

(* `Cause ε δ ι α` with ε = δ = nat, ι = fiber id, α the annotation map. *)
type reason = Rfail of int | Rdie of string | Rinterrupt of int option
type cause = { reasons : reason list; annotations : string list }

let cause_empty = { reasons = []; annotations = [] }
let cause_fail e = { reasons = [ Rfail e ]; annotations = [] }
let cause_die d = { reasons = [ Rdie d ]; annotations = [] }
let cause_interrupt who = { reasons = [ Rinterrupt who ]; annotations = [] }

let cause_combine a b =
  { reasons = a.reasons @ b.reasons; annotations = a.annotations @ b.annotations }

let cause_annotate c extra = { c with annotations = c.annotations @ extra }

let cause_fail_of c =
  List.fold_left (fun acc r -> match (acc, r) with None, Rfail e -> Some e | _ -> acc) None
    c.reasons

type exitv = Esuccess of value | Efailure of cause

(* -------------------------------------------------- parking, tasks, observers, dispatcher *)

(* `Supervision.ObserverMode`; `ParkKind` (`Fibers.lean:56`). *)
type observer_mode = MJoin | MAwait
type park_kind = Pjoin of int * observer_mode

(* `Parked` (`:62`): rc.112 `_yielded` absent, or the resume guard as a token. *)
type parked = NotParked | WithGuard of int

(* `Resume ν` (`:68`). *)
type resume_with = RexitsValue | Rvoid | RcontinueWith of exitv

(* `Pending` (`:81`), field for field. *)
type pending = {
  token : int;
  waiting_on : int option;
  mutable remaining : int;
  mutable collected : exitv list;
  resume_with : resume_with;
}

(* `Observer` (`:93`), all six shapes. *)
type observer =
  | ResumeAwait of int * int * observer_mode
  | UntrackChild of int
  | DropScopeFinalizer of int * int
  | Countdown of int * int
  | RaceCallback of int
  | Callback of int

(* The answer a resume carries. Lean carries a whole `Prim`; every `Prim` the machine builds
   in that position is `Prim.success v` or `Prim.failure c`, so the OCaml answer is
   restricted to those two. *)
type answer = Aval of value | Acause of cause

(* `Task` (`:104`), `Bucket` (`:110`), `Dispatcher` (`:117`). *)
type task = Tstart of int | Tresume of int * int * answer
type bucket = { priority : int; mutable tasks : task list }
type dispatcher = { mutable buckets : bucket list; mutable armed : bool }

module Dispatcher = struct
  let empty () = { buckets = []; armed = false }

  (* `Scheduler.ts:105-131`: ascending priority, FIFO within a bucket. *)
  let rec insert priority task = function
    | [] -> [ { priority; tasks = [ task ] } ]
    | b :: rest ->
      if b.priority = priority then (
        b.tasks <- b.tasks @ [ task ];
        b :: rest)
      else if priority < b.priority then { priority; tasks = [ task ] } :: b :: rest
      else b :: insert priority task rest

  (* enqueue plus arming on the first task (`Scheduler.ts:207-212`). *)
  let enqueue d priority task =
    d.buckets <- insert priority task d.buckets;
    d.armed <- true

  (* `runTasks` drains the snapshot once (`Scheduler.ts:225-233`): a task enqueued during
     the drain waits for the next host task. *)
  let drain d =
    let tasks = List.concat_map (fun b -> b.tasks) d.buckets in
    d.buckets <- [];
    d.armed <- false;
    tasks
end

(* ------------------------------------------------------------------------- the fiber *)

(* DIVERGENCE 1: `FrameFiber.current` and `.stack` as the OCaml stack. *)
type control =
  | Program of (unit -> value)  (* current = the program, stack = [] *)
  | Onstack                     (* this fiber is the one running *)
  | Suspended of kont           (* current + stack captured, one-shot *)
  | Failing of cause            (* current = Prim.failure c, stack = [] *)
  | Ended

and kont = { ktoken : int; kresume : answer -> unit }

(* The two halves of a captured one-shot continuation, closed over at the `effc` branch so
   that no GADT-refined type crosses into the mutually recursive machine functions:
   `ret v` is `ko.ret v`, `thr e` is `Effect.Deep.discontinue k e`. *)
type kops = { ret : value -> unit; thr : exn -> unit }

(* `FrameFiber` (`Runtime.lean:269`), five fields. *)
type frame_fiber = {
  mutable control : control;  (* current + stack, DIVERGENCE 1 *)
  mutable interruptible : bool;
  mutable interrupted_cause : cause option;
  mutable deferred_interrupt : bool;
}

let frame_pending_cause f = match f.interrupted_cause with Some c -> c | None -> cause_empty

(* `RunFiber` (`:157`), fifteen fields in the Lean order. `context` is `unit` in this
   profile: the fiber family declares no context service. *)
type run_fiber = {
  id : int;
  frame : frame_fiber;
  mutable running : bool;
  mutable parked : parked;
  mutable pending : pending list;
  mutable finalizing : exitv option;
  mutable exit_ : exitv option;
  mutable current_op_count : int;
  mutable max_ops_before_yield : int;
  mutable prevent_yield : bool;
  mutable yield_override : bool option;
  mutable observers : observer list;
  mutable children : int list;
  mutable dispatcher : dispatcher;
  mutable context : unit;
}

(* `RunFiber.make` (`:225`). *)
let run_fiber_make id program interruptible (max_ops, prevent) context =
  {
    id;
    frame =
      { control = Program program; interruptible; interrupted_cause = None;
        deferred_interrupt = false };
    running = false;
    parked = NotParked;
    pending = [];
    finalizing = None;
    exit_ = None;
    current_op_count = 0;
    max_ops_before_yield = max_ops;
    prevent_yield = prevent;
    yield_override = None;
    observers = [];
    children = [];
    dispatcher = Dispatcher.empty ();
    context;
  }

(* `RunFiber.park` (`:246`). *)
let run_fiber_park f p =
  f.parked <- WithGuard p.token;
  f.pending <- f.pending @ [ p ]

(* `RunFiber.status` (`:180`), computed, for the report's projection check. *)
type fiber_status = Sdone | Sfinalizing | Srunning | Swaiting of int | Srunnable

let run_fiber_status f =
  if f.exit_ <> None then Sdone
  else if f.finalizing <> None then Sfinalizing
  else if f.running then Srunning
  else
    match f.parked with
    | NotParked -> Srunnable
    | WithGuard token -> (
      match List.find_opt (fun p -> p.token = token) f.pending with
      | Some { waiting_on = Some t; _ } -> Swaiting t
      | _ -> Srunnable)

(* --------------------------------------------------------------- events, races, machine *)

(* `RunEvent` (`:305`), one constructor per Lean constructor. *)
type run_event =
  | Forked of int * int * bool
  | Started of int
  | ScheduledTask of int * int * task
  | RanTask of int * task
  | YieldInjected of int * int
  | ParkedOn of int * int
  | ResumedWith of int * int * answer
  | InterruptRecorded of int option * int
  | InterruptDeferred of int
  | ChildrenInterrupted of int * int list
  | ObserverFired of int * observer
  | FrameEv of int * string
  | FinalizerProgram of int * string * exitv
  | ScopeLinked of int * int * int
  | ScopeClosedOnLink of int * int
  | RaceStarted of int * int * int list
  | RaceLaunched of int * int
  | RaceSkipped of int * int
  | RaceSettled of int * exitv
  | ContextSet of int
  | CallbackEv of int * exitv
  | Exited of int * exitv

(* `Stuck` (`:332`). *)
type stuck = UnknownFiber of int | UnknownScope of int

(* `Race` over `Supervision.RaceAllState` (`:339`). Declared; the `raceAll` arm refuses in
   this pass, so no race is ever created (see the report's scope table). *)
type race = {
  rid : int;
  host : int;
  rtoken : int;
  mutable settled : bool;
  mutable live : int list;
  mutable unstarted : int list;
  mutable accepted : exitv option;
}

(* The store `St` of this profile: the two arrays the fixture's bodies append to. *)
type st = { mutable started : int list; mutable cleanups : int list }

(* `RunMachine` (`:349`), field for field. *)
type run_machine = {
  mutable fibers : run_fiber list;
  mutable races : race list;
  mutable next_id : int;
  mutable next_token : int;
  mutable next_race : int;
  mutable middleware_installed : bool;
  state : st;
  mutable trace : run_event list;
  mutable stuck : stuck option;
}

let machine_empty state =
  { fibers = []; races = []; next_id = 0; next_token = 0; next_race = 0;
    middleware_installed = false; state; trace = []; stuck = None }

let fiber_opt m id = List.find_opt (fun f -> f.id = id) m.fibers

let fiber_exn m id =
  match fiber_opt m id with
  | Some f -> f
  | None -> failwith (Printf.sprintf "unknown fiber %d" id)

let emit m events = m.trace <- m.trace @ events
let halt m why = m.stuck <- Some why

(* `RunMachine.finished` (`:504`). *)
let machine_finished m = List.for_all (fun f -> f.exit_ <> None) m.fibers

(* ---------------------------------------------------------------------------- commands *)

(* `Cmd` (`:526`). `Cmd.loop` is absent by DIVERGENCE 2. *)
type cmd = Cevaluate of int | Cresume of int * int * answer | Claunch of int * int | CdrainDue

(* `RunDecision` (`:362`). *)
type run_decision =
  | Dfire of int
  | Dflush
  | Devaluate of int
  | DyieldVerdict of int * bool
  | DanswerAsync of int * int * answer
  | DinterruptFrom of int option * string list * int
  | DinstallMiddleware

(* ------------------------------------------------------------- the service alphabet

   The `Fibers` family's eight operations (`harness/trace/fiber-fixture.ts`), plus the two
   machine-level parks the bodies need. Each is a `Prim` the Lean `iteration` intercepts:
   `Op_yield_now` is `Prim.yieldNowWith`, `Op_never` is a `Prim.async` registering no resume,
   and the six fiber operations are `Prim.withFiber` thunks whose `RunInterp.withFiberOf` is
   the named `WithFiberAction`. *)
type _ Effect.t +=
  | Op_fork : int * bool -> value Effect.t     (* WithFiberAction.fork *)
  | Op_join : int -> value Effect.t            (* ParkKind.join _ MJoin *)
  | Op_await_value : int -> value Effect.t     (* ParkKind.join _ MAwait *)
  | Op_await_error : int -> value Effect.t     (* ParkKind.join _ MAwait *)
  | Op_interrupt : int -> value Effect.t       (* WithFiberAction.interrupt *)
  | Op_started : unit -> value Effect.t        (* Prim.sync, RunInterp.syncState *)
  | Op_cleanups : unit -> value Effect.t       (* Prim.sync, RunInterp.syncState *)
  | Op_yield_now : int -> value Effect.t       (* Prim.yieldNowWith *)
  | Op_never : unit -> value Effect.t          (* Prim.async, never resumed *)

(* A typed failure raised by a fiber body: `Prim.yieldableError`. *)
exception Efail_exn of int

(* What a `discontinue` at a park delivers: `Prim.failure accumulated`. *)
exception Einterrupt_exn of cause

(* The body of a child, resolved through the fixture's table -- a fork names a declared
   root, never a closure (`fork-lowering.md` §(b)). Set by the fixture module. *)
let body_of_code : (int -> unit -> value) ref =
  ref (fun _ () -> failwith "no root table installed")

(* -------------------------------------------------------------- the service trace rows *)

type row =
  | Rop of string * value
  | Ranswer of string * value
  | Rfailed of string * int
  | Rdecide of int * bool
  | Rdone of exitv

let sink : row list ref = ref []
let push_row r = sink := !sink @ [ r ]

(* -------------------------------------------------------------- the machine operations *)

let fresh_token m =
  let t = m.next_token in
  m.next_token <- m.next_token + 1;
  t

(* `interruptRecord` (`:550`), arm for arm. Returns whether to evaluate the target now. *)
let interrupt_record _m interruptor (extra : string list) (f : run_fiber) : bool =
  if f.exit_ <> None then false (* :575-577 *)
  else begin
    let cause =
      cause_annotate (cause_interrupt interruptor) ((Printf.sprintf "stack:%d" f.id) :: extra)
    in
    let accumulated =
      match f.frame.interrupted_cause with (* :585-587 *)
      | None -> cause
      | Some previous -> cause_combine previous cause
    in
    f.frame.interrupted_cause <- Some accumulated;
    if f.frame.interruptible then (* :588 *)
      if f.running then begin
        f.frame.deferred_interrupt <- true;
        false
      end
      else begin
        (* :591-594. The OCaml spelling of `current := Prim.failure` depends on where the
           program lives (DIVERGENCE 1): a captured continuation is discontinued by the
           `Cmd.evaluate` this returns true for; an unstarted program is replaced. *)
        (match f.frame.control with
         | Suspended _ -> ()
         | Program _ | Failing _ -> f.frame.control <- Failing accumulated
         | Onstack | Ended -> ());
        f.parked <- NotParked;
        f.pending <- [];
        true
      end
    else false
  end

(* `countdownPark.resumePrim` (`:598`). *)
let resume_prim resume_with (exits : exitv list) : answer =
  match resume_with with
  | RexitsValue -> Aval (Vlist (List.map (function Esuccess v -> v | Efailure _ -> Vnone) exits))
  | Rvoid -> Aval Vunit
  | RcontinueWith e -> ( match e with Esuccess v -> Aval v | Efailure c -> Acause c)

(* `countdownPark` (`:576`). Returns the token it parked on, or `None` when nothing was
   live and the continuation is applied at once. *)
let countdown_park m (f : run_fiber) (targets : int list) resume_with : int option =
  let token = fresh_token m in
  let exited =
    List.filter_map (fun t -> match fiber_opt m t with Some g -> g.exit_ | None -> None) targets
  in
  let live =
    List.filter (fun t -> match fiber_opt m t with Some g -> g.exit_ = None | None -> false) targets
  in
  if live = [] then None
  else begin
    List.iter
      (fun t ->
        let g = fiber_exn m t in
        g.observers <- g.observers @ [ Countdown (f.id, token) ])
      live;
    run_fiber_park f
      { token; waiting_on = None; remaining = List.length live; collected = exited; resume_with };
    emit m [ ParkedOn (f.id, token) ];
    Some token
  end

(* `spawn` (`:622`): mask by the options, the parent's context, tracked unless daemon. *)
let spawn m (parent : run_fiber) (program : unit -> value) ~daemon : int =
  let child_id = m.next_id in
  let child = run_fiber_make child_id program parent.frame.interruptible (max_int, false) () in
  if not daemon then begin
    child.observers <- [ UntrackChild parent.id ];
    parent.children <- parent.children @ [ child_id ]
  end;
  m.fibers <- m.fibers @ [ child ];
  m.next_id <- m.next_id + 1;
  emit m [ Forked (parent.id, child_id, daemon) ];
  child_id

(* `start` (`:644`): immediately on the caller stack, or deferred at priority 0 (`:5277`). *)
let start m (parent : run_fiber) (child : int) ~immediately : cmd list =
  if immediately then [ Cevaluate child ]
  else begin
    Dispatcher.enqueue parent.dispatcher 0 (Tstart child);
    emit m [ ScheduledTask (parent.id, 0, Tstart child) ];
    []
  end

(* `RunInterp.exitValue` (`:437`): the exit as a value (`await`) or as an effect (`join`). *)
let exit_value (e : exitv) (mode : observer_mode) : answer =
  match mode with
  | MAwait -> Aval (match e with Esuccess v -> Vsome v | Efailure _ -> Vnone)
  | MJoin -> ( match e with Esuccess v -> Aval v | Efailure c -> Acause c)

(* `iteration` (`:683`) lines :639-652: the deferred interrupt, the op counter, the yield
   injection. DIVERGENCE 2: run at the head of every handler arm. *)
let iteration_prelude m (f : run_fiber) : cause option =
  if f.frame.deferred_interrupt then begin
    f.frame.deferred_interrupt <- false;
    Some (frame_pending_cause f.frame)
  end
  else begin
    f.current_op_count <- f.current_op_count + 1;
    let verdict =
      match f.yield_override with
      | Some v -> v
      | None -> f.current_op_count >= f.max_ops_before_yield
    in
    if (not f.prevent_yield) && verdict then begin
      f.yield_override <- None;
      emit m [ YieldInjected (f.id, f.current_op_count) ]
    end;
    None
  end

(* ------------------------------------------------------------- exit, observers, drive *)

let rec fire_observer m (id : int) (exit_ : exitv) (acc : cmd list) (o : observer) : cmd list =
  emit m [ ObserverFired (id, o) ];
  match o with
  | ResumeAwait (waiter, token, mode) -> acc @ [ Cresume (waiter, token, exit_value exit_ mode) ]
  | UntrackChild parent ->
    (match fiber_opt m parent with
     | Some p -> p.children <- List.filter (fun c -> c <> id) p.children
     | None -> ());
    acc
  | DropScopeFinalizer (scope, _key) ->
    halt m (UnknownScope scope);
    acc
  | Countdown (waiter, token) -> (
    match fiber_opt m waiter with
    | None -> acc
    | Some w -> (
      match List.find_opt (fun p -> p.token = token) w.pending with
      | None -> acc
      | Some p ->
        p.collected <- p.collected @ [ exit_ ];
        if p.remaining <= 1 then begin
          p.remaining <- 0;
          acc @ [ Cresume (waiter, token, resume_prim p.resume_with p.collected) ]
        end
        else begin
          p.remaining <- p.remaining - 1;
          acc
        end))
  | RaceCallback _ -> acc
  | Callback key ->
    emit m [ CallbackEv (key, exit_) ];
    acc

(* `exitFiber` (`:992`). *)
and exit_fiber m (f : run_fiber) (exit_ : exitv) : cmd list =
  if m.middleware_installed && f.finalizing = None && f.children <> [] then begin
    let nested =
      List.fold_left
        (fun acc child ->
          match fiber_opt m child with
          | None -> acc
          | Some c ->
            let apply_now = interrupt_record m (Some f.id) [] c in
            emit m [ InterruptRecorded (Some f.id, child) ];
            acc @ if apply_now then [ Cevaluate child ] else [])
        [] f.children
    in
    emit m [ ChildrenInterrupted (f.id, f.children) ];
    f.finalizing <- Some exit_;
    (match countdown_park m f f.children (RcontinueWith exit_) with
     | Some _ -> ()
     | None -> f.finalizing <- None);
    nested
  end
  else begin
    (* :619-627 *)
    f.exit_ <- Some exit_;
    f.finalizing <- None;
    f.frame.control <- Ended;
    f.children <- [];
    f.parked <- NotParked;
    f.pending <- [];
    f.context <- ();
    emit m [ Exited (f.id, exit_) ];
    let observers = f.observers in
    let nested = List.fold_left (fire_observer m f.id exit_) [] observers in
    f.observers <- [];
    nested
  end

(* `drive` (`:1025`). *)
and drive m (cmds : cmd list) : unit =
  match cmds with
  | [] -> ()
  | _ when m.stuck <> None -> ()
  | c :: rest ->
    exec m c;
    drive m rest

and exec m (c : cmd) : unit =
  match c with
  | Cevaluate id -> (
    (* :599-628 *)
    match fiber_opt m id with
    | None -> ()
    | Some f ->
      if f.exit_ <> None || f.running then () (* :600-601 *)
      else begin
        f.running <- true;
        f.current_op_count <- 0;
        f.parked <- NotParked;
        emit m [ Started id ];
        run_control m f
      end)
  | Cresume (id, token, answer) -> (
    (* :602-606, :1121 *)
    match fiber_opt m id with
    | None -> ()
    | Some t -> (
      match t.parked with
      | WithGuard parked_token when parked_token = token -> (
        t.parked <- NotParked;
        t.pending <- List.filter (fun p -> p.token <> token) t.pending;
        emit m [ ResumedWith (id, token, answer) ];
        match t.frame.control with
        | Suspended k ->
          t.frame.control <- Onstack;
          t.running <- true;
          t.current_op_count <- 0;
          emit m [ Started id ];
          k.kresume answer
        | _ -> ())
      | _ -> () (* the token guard: a stale resume is dropped *)))
  | Claunch _ -> ()  (* the race arm refuses in this pass *)
  | CdrainDue -> ()  (* `RunInterp.dueResumes` is empty in this St *)

(* What `Cmd.evaluate` finds in `current`. *)
and run_control m (f : run_fiber) : unit =
  match f.frame.control with
  | Program body ->
    f.frame.control <- Onstack;
    run_under_handler m f body
  | Failing cause ->
    (* current = Prim.failure over an empty stack: the frame machine's `resumeCause` walks
       nothing and finishes. The body never ran, so no finalizer frame exists. *)
    f.frame.control <- Onstack;
    finish m f (Efailure cause)
  | Suspended k ->
    (* An interrupt applied to a parked fiber: Lean reaches the stack through
       `current := Prim.failure accumulated`; OCaml's spelling is `discontinue`. *)
    f.frame.control <- Onstack;
    k.kresume (Acause (frame_pending_cause f.frame))
  | Onstack | Ended -> ()

(* `retc` / `exnc`: this fiber's own stack has finished. *)
and finish m (f : run_fiber) (exit_ : exitv) : unit =
  f.running <- false;
  let nested = exit_fiber m f exit_ in
  drive m nested

(* The scheduler handler: `match_with` over the fiber body. Every `effc` arm is one
   `iteration` arm of `Fibers.lean:683`. *)
and run_under_handler m (f : run_fiber) (body : unit -> value) : unit =
  let open Effect.Deep in
  match_with body ()
    {
      retc = (fun v -> finish m f (Esuccess v));
      exnc =
        (fun e ->
          let exit_ =
            match e with
            | Efail_exn code -> Efailure (cause_fail code)
            | Einterrupt_exn c -> Efailure c
            | other -> Efailure (cause_die (Printexc.to_string other))
          in
          finish m f exit_);
      effc =
        (fun (type a) (eff : a Effect.t) : ((a, unit) continuation -> unit) option ->
          match eff with
          | Op_fork (code, daemon) ->
            Some (fun k -> arm_fork m f code daemon { ret = continue k; thr = discontinue k })
          | Op_join h -> Some (fun k -> arm_join m f h { ret = continue k; thr = discontinue k })
          | Op_await_value h ->
            Some (fun k -> arm_await m f h `Value { ret = continue k; thr = discontinue k })
          | Op_await_error h ->
            Some (fun k -> arm_await m f h `Error { ret = continue k; thr = discontinue k })
          | Op_interrupt h ->
            Some (fun k -> arm_interrupt m f h { ret = continue k; thr = discontinue k })
          | Op_started () ->
            Some (fun k ->
                arm_sync m f "started" (fun st -> st.started)
                  { ret = continue k; thr = discontinue k })
          | Op_cleanups () ->
            Some (fun k ->
                arm_sync m f "cleanups" (fun st -> st.cleanups)
                  { ret = continue k; thr = discontinue k })
          | Op_yield_now p ->
            Some (fun k -> arm_yield m f p { ret = continue k; thr = discontinue k })
          | Op_never () -> Some (fun k -> arm_never m f { ret = continue k; thr = discontinue k })
          | _ -> None);
    }

(* Every arm runs `iteration_prelude` first; a deferred interrupt replaces the primitive. *)
and prelude_or_fail m (f : run_fiber) (ko : kops) : bool =
  match iteration_prelude m f with
  | None -> false
  | Some cause ->
    f.running <- false;
    ko.thr (Einterrupt_exn cause);
    true

(* `WithFiberAction.fork` (`:5264-5284`) followed by `start` (`:5277`). *)
and arm_fork m f code daemon (ko : kops) : unit =
  if prelude_or_fail m f ko then ()
  else begin
    let name = if daemon then "forkDetach" else "fork" in
    push_row (Rop (name, Vnat code));
    (* rc.112 adds the `interruptChildren` middleware in `Effect.forkChild` (`:612-614`). *)
    if not daemon then m.middleware_installed <- true;
    let child = spawn m f (!body_of_code code) ~daemon in
    let nested = start m f child ~immediately:false in
    let handle = child - 1 in
    let site = Tape.site () in
    let branch = Tape.decide () in
    push_row (Rdecide (site, branch));
    push_row (Ranswer (name, Vhandle handle));
    drive m nested;
    (* On `true` the parent spends one primitive with the scheduler armed, so the run loop
       takes the processor away and drains its queue: `Prim.yieldNowWith 0`. *)
    if branch then park_yield m f 0 (fun () -> ko.ret (Vhandle handle))
        (fun c -> ko.thr (Einterrupt_exn c))
    else ko.ret (Vhandle handle)
  end

(* `Prim.yieldNowWith` (`:982-990`): enqueue the resume on this fiber's own dispatcher at
   the given priority, then park on the guard token. *)
and park_yield m f priority (on_value : unit -> unit) (on_cause : cause -> unit) : unit =
  let token = fresh_token m in
  Dispatcher.enqueue f.dispatcher priority (Tresume (f.id, token, Aval Vunit));
  emit m [ ScheduledTask (f.id, priority, Tresume (f.id, token, Aval Vunit)) ];
  run_fiber_park f
    { token; waiting_on = None; remaining = 0; collected = []; resume_with = Rvoid };
  emit m [ ParkedOn (f.id, token) ];
  f.frame.control <-
    Suspended
      { ktoken = token;
        kresume = (fun a -> match a with Aval _ -> on_value () | Acause c -> on_cause c) };
  f.running <- false

and arm_yield m f priority (ko : kops) : unit =
  if prelude_or_fail m f ko then ()
  else
    park_yield m f priority
      (fun () -> ko.ret Vunit)
      (fun c -> ko.thr (Einterrupt_exn c))

(* `Prim.async` registering no resume: rc.112's `Effect.never`. *)
and arm_never m f (ko : kops) : unit =
  if prelude_or_fail m f ko then ()
  else begin
    let token = fresh_token m in
    run_fiber_park f
      { token; waiting_on = None; remaining = 0; collected = []; resume_with = Rvoid };
    emit m [ ParkedOn (f.id, token) ];
    f.frame.control <-
      Suspended
        { ktoken = token;
          kresume =
            (fun a ->
              match a with
              | Aval v -> ko.ret v
              | Acause c -> ko.thr (Einterrupt_exn c)) };
    f.running <- false
  end

(* `ParkKind.join _ MJoin` (`:5291`): the child's exit continues this fiber as an effect. *)
and arm_join m f handle (ko : kops) : unit =
  if prelude_or_fail m f ko then ()
  else begin
    push_row (Rop ("join", Vhandle handle));
    let target = handle + 1 in
    match fiber_opt m target with
    | None -> halt m (UnknownFiber target)
    | Some t -> (
      match t.exit_ with
      | Some e -> answer_join ko e (* :561-562 *)
      | None ->
        let token = fresh_token m in
        t.observers <- t.observers @ [ ResumeAwait (f.id, token, MJoin) ];
        run_fiber_park f
          { token; waiting_on = Some target; remaining = 0; collected = []; resume_with = Rvoid };
        emit m [ ParkedOn (f.id, token) ];
        f.frame.control <-
          Suspended
            { ktoken = token;
              kresume =
                (fun a ->
                  match a with
                  | Aval v ->
                    push_row (Ranswer ("join", v));
                    ko.ret v
                  | Acause c -> fail_op "join" ko c) })
  end

and answer_join ko (e : exitv) : unit =
  match e with
  | Esuccess v ->
    push_row (Ranswer ("join", v));
    ko.ret v
  | Efailure c -> fail_op "join" ko c

(* A service operation that fails: the `failed` row, then the cause into the fiber. *)
and fail_op name (ko : kops) (c : cause) : unit =
  (match cause_fail_of c with
   | Some e -> push_row (Rfailed (name, e))
   | None -> push_row (Rfailed (name, 0)));
  ko.thr (Einterrupt_exn c)

(* `awaitValue` / `awaitError`: both `Fiber.await` (`:5304`), projected. *)
and arm_await m f handle which (ko : kops) : unit =
  if prelude_or_fail m f ko then ()
  else begin
    let name = match which with `Value -> "awaitValue" | `Error -> "awaitError" in
    push_row (Rop (name, Vhandle handle));
    let project (e : exitv) : value =
      match (which, e) with
      | `Value, Esuccess v -> Vsome v
      | `Value, Efailure _ -> Vnone
      | `Error, Esuccess _ -> Vnone
      | `Error, Efailure c -> (
        match cause_fail_of c with Some x -> Vsome (Vnat x) | None -> Vnone)
    in
    let target = handle + 1 in
    match fiber_opt m target with
    | None -> halt m (UnknownFiber target)
    | Some t -> (
      match t.exit_ with
      | Some e ->
        let v = project e in
        push_row (Ranswer (name, v));
        ko.ret v
      | None ->
        let token = fresh_token m in
        t.observers <- t.observers @ [ ResumeAwait (f.id, token, MAwait) ];
        run_fiber_park f
          { token; waiting_on = Some target; remaining = 0; collected = []; resume_with = Rvoid };
        emit m [ ParkedOn (f.id, token) ];
        (* `exit_value _ MAwait` loses the typed error, which `awaitError` needs, so the
           projection re-reads the target's exit. Recorded: the observer's answer is the
           machine's, the projection is the family's. *)
        f.frame.control <-
          Suspended
            { ktoken = token;
              kresume =
                (fun _ ->
                  let e =
                    match (fiber_exn m target).exit_ with Some e -> e | None -> Esuccess Vunit
                  in
                  let v = project e in
                  push_row (Ranswer (name, v));
                  ko.ret v) })
  end

(* `WithFiberAction.interrupt` (`:859`) = `interruptThenJoin`. *)
and arm_interrupt m f handle (ko : kops) : unit =
  if prelude_or_fail m f ko then ()
  else begin
    push_row (Rop ("interrupt", Vhandle handle));
    let target = handle + 1 in
    match fiber_opt m target with
    | None -> halt m (UnknownFiber target)
    | Some t ->
      let apply_now = interrupt_record m (Some f.id) [] t in
      emit m [ InterruptRecorded (Some f.id, target) ];
      let nested = if apply_now then [ Cevaluate target ] else [] in
      (match countdown_park m f [ target ] Rvoid with
       | Some token ->
         f.frame.control <-
           Suspended
             { ktoken = token;
               kresume =
                 (fun a ->
                   match a with
                   | Aval _ ->
                     push_row (Ranswer ("interrupt", Vunit));
                     ko.ret Vunit
                   | Acause c -> ko.thr (Einterrupt_exn c)) };
         f.running <- false;
         drive m nested
       | None ->
         drive m nested;
         push_row (Ranswer ("interrupt", Vunit));
         ko.ret Vunit)
  end

(* `Prim.sync` through `RunInterp.syncState` (M1). *)
and arm_sync m f name (read : st -> int list) (ko : kops) : unit =
  if prelude_or_fail m f ko then ()
  else begin
    push_row (Rop (name, Vunit));
    let v = Vlist (List.map (fun n -> Vnat n) (read m.state)) in
    push_row (Ranswer (name, v));
    ko.ret v
  end

(* ------------------------------------------------------------------- runtime entries *)

(* `stepDecision.fire` (`Scheduler.ts:225-233`): drain once, run the tasks in order. *)
let fire m owner =
  match fiber_opt m owner with
  | None -> ()
  | Some o ->
    let tasks = Dispatcher.drain o.dispatcher in
    List.iter
      (fun task ->
        emit m [ RanTask (owner, task) ];
        match task with
        | Tstart child -> drive m [ Cevaluate child; CdrainDue ]
        | Tresume (target, token, answer) -> drive m [ Cresume (target, token, answer); CdrainDue ])
      tasks

(* `stepDecision.flushAll`: armed dispatchers in fiber order until none is armed. *)
let rec flush_all m rounds =
  if rounds = 0 then ()
  else
    let armed = List.filter (fun f -> f.dispatcher.armed) m.fibers in
    if armed = [] || m.stuck <> None then ()
    else begin
      List.iter (fun f -> fire m f.id) armed;
      flush_all m (rounds - 1)
    end

(* `stepDecision` (`:1108`). *)
let step_decision m = function
  | Dfire owner -> fire m owner
  | Dflush -> flush_all m 1000
  | Devaluate id -> drive m [ Cevaluate id; CdrainDue ]
  | DyieldVerdict (id, verdict) -> (
    match fiber_opt m id with Some f -> f.yield_override <- Some verdict | None -> ())
  | DanswerAsync (id, token, answer) -> drive m [ Cresume (id, token, answer); CdrainDue ]
  | DinterruptFrom (interruptor, annotations, target) -> (
    match fiber_opt m target with
    | None -> ()
    | Some t ->
      let apply_now = interrupt_record m interruptor annotations t in
      emit m [ InterruptRecorded (interruptor, target) ];
      if t.frame.deferred_interrupt && t.running then emit m [ InterruptDeferred target ];
      if apply_now then drive m [ Cevaluate target; CdrainDue ])
  | DinstallMiddleware -> m.middleware_installed <- true

(* `runFork` (`:1184`): one root fiber, evaluated synchronously on the caller stack. *)
let run_fork m (program : unit -> value) : int =
  let root = m.next_id in
  let fiber = run_fiber_make root program true (max_int, false) () in
  m.fibers <- m.fibers @ [ fiber ];
  m.next_id <- m.next_id + 1;
  drive m [ Cevaluate root; CdrainDue ];
  root

(* `runCallback` (`:1194`): `runFork` plus an exit observer under `key`. *)
let run_callback m (program : unit -> value) (key : int) : int =
  let root = m.next_id in
  let fiber = run_fiber_make root program true (max_int, false) () in
  fiber.observers <- [ Callback key ];
  m.fibers <- m.fibers @ [ fiber ];
  m.next_id <- m.next_id + 1;
  drive m [ Cevaluate root; CdrainDue ];
  root

(* `runSyncExit` (`:1205`): `runFork`, flush, and the `AsyncFiberError` defect when the root
   survives the flush. *)
let run_sync_exit m (program : unit -> value) : exitv =
  let root = run_fork m program in
  step_decision m Dflush;
  match (fiber_exn m root).exit_ with
  | Some e -> e
  | None -> Efailure (cause_die "AsyncFiberError")

(* `promiseOutcome` (`:1216`). *)
let promise_outcome (e : exitv) : (value, cause) result =
  match e with Esuccess v -> Ok v | Efailure c -> Error c
