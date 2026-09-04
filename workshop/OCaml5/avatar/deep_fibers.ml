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
  | Vbool of bool
  | Vstring of string
  | Vhandle of int
  | Vpair of value * value
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

let cause_has_interrupt c =
  List.exists (function Rinterrupt _ -> true | _ -> false) c.reasons

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
  (* Not a Lean field: `iteration`'s per-entry injection latch is Lean's `yielding` argument
     to `Cmd.loop` (`Fibers.lean:683`, rc.112's `runLoop` local at `internal/effect.ts:634`).
     `Cmd.loop` has no OCaml existence (DIVERGENCE 2), so the latch lives on the fiber and is
     cleared wherever Lean's `Cmd.evaluate` would have passed `false`. *)
  mutable yielding : bool;
  (* Not a Lean field: a `raceAll` host is resumed either by its own race token or by the
     settle path's countdown token, and the OCaml continuation has to survive both. Lean
     keeps the program in `frame.current` instead (DIVERGENCE 1). *)
  mutable race_answer : kops option;
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
    yielding = false;
    race_answer = None;
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
  mutable remaining : int;
  mutable failures : reason list;
  mutable accepted : exitv option;
  mutable cleanup_needed : bool;
}

(* The store the *fixture* owns: the two arrays the fiber family's bodies append to. The
   three stores of `Deep.Stores` -- the Ref heap, the Deferred store and the ScopeStore --
   used to be improvised here as three hashtables of ints; they are the real `Stores.lean`
   carriers now and they live in `deep_stores.ml`, reached through `interp` above, because
   `Deep.Stores` is the module that declares them. *)
type st = {
  mutable started : int list;
  mutable cleanups : int list;
}

let state : st = { started = []; cleanups = [] }

(* The wire's handle space: `registerHandle`/`handleIndex` in `harness/trace/tracer.ts`.
   An object never reaches the wire; it is encoded as its index in first-seen order, over
   every handle kind at once. *)
let handles : (string * int, int) Hashtbl.t = Hashtbl.create 16
let handle_owner : (int, string * int) Hashtbl.t = Hashtbl.create 16
let next_handle = ref 0

let handle_index kind id =
  match Hashtbl.find_opt handles (kind, id) with
  | Some h -> h
  | None ->
    let h = !next_handle in
    incr next_handle;
    Hashtbl.replace handles (kind, id) h;
    Hashtbl.replace handle_owner h (kind, id);
    h

let handle_target kind h =
  match Hashtbl.find_opt handle_owner h with
  | Some (k, id) when k = kind -> id
  | _ -> failwith (Printf.sprintf "handle %d is not a %s" h kind)

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
  (* Not a Lean field: the OCaml spelling of the fuel argument `drive` threads. `exec`
     writes the fuel it was given here so that an arm resumed inside `continue k` can pass
     the same fuel to the nested `drive` Lean's `Outcome.continue_` arm would have run
     (DIVERGENCE 4). *)
  mutable drive_fuel : int;
}

let machine_empty state =
  { fibers = []; races = []; next_id = 0; next_token = 0; next_race = 0;
    middleware_installed = false; state; trace = []; stuck = None; drive_fuel = 0 }

(* The fuel and round bounds the entries use. Lean's `drive` costs one fuel per command and
   `flushAll` one round per sweep of the armed dispatchers. *)
let default_fuel = 100000
let default_rounds = 1000

(* `Scheduler.MaxOpsBeforeYield` as the host tails read it (`EFFECT4_MAX_OPS`,
   `harness/trace/fiber-tail.ts:74`). rc.112 caches it on the fiber at `setContext`
   (`internal/effect.ts:726-727`), which is what `RunFiber.make`'s budget pair is. *)
let max_ops_before_yield = ref max_int
let prevent_yield = ref false

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

(* ------------------------------------------------------------ what is not ported

   The seat rule: anything this avatar does not implement refuses at run time with the Lean
   declaration's name in the message, rather than differing silently. *)
exception Not_ported of string

let refuse (lean_name : string) : 'a =
  raise (Not_ported ("not ported: " ^ lean_name))

(* ------------------------------------------------------------- the service alphabet

   The `Fibers` family's eight operations (`harness/trace/fiber-fixture.ts`), plus the two
   machine-level parks the bodies need. Each is a `Prim` the Lean `iteration` intercepts:
   `Op_yield_now` is `Prim.yieldNowWith`, `Op_never` is a `Prim.async` registering no resume,
   and the six fiber operations are `Prim.withFiber` thunks whose `RunInterp.withFiberOf` is
   the named `WithFiberAction`.

   The store half is not here. `RunMachine` is parametric in `St` and in the `RunInterp` over
   it (`Fibers.lean:349`, `:386`), and `Deep.Stores` supplies both (`Stores.lean:1002`,
   `:1293`); OCaml has no forward reference, so the machine declares `σ` as an *extensible*
   variant, which is what a type parameter it never inspects amounts to, and `deep_stores.ml`
   extends it. Every `Prim.sync (Thunk.op …)`, every `Prim.async` the store answers and every
   `Prim.withFiber (Thunk.act …)` the store owns arrives as one `Op_store`. *)
type store_request = ..

type _ Effect.t +=
  | Op_store : store_request -> value Effect.t
  | Op_fork : int * bool -> value Effect.t     (* WithFiberAction.fork *)
  | Op_join : int -> value Effect.t            (* ParkKind.join _ MJoin *)
  | Op_await_value : int -> value Effect.t     (* ParkKind.join _ MAwait *)
  | Op_await_error : int -> value Effect.t     (* ParkKind.join _ MAwait *)
  | Op_interrupt : int -> value Effect.t       (* WithFiberAction.interrupt *)
  | Op_started : unit -> value Effect.t        (* Prim.sync, RunInterp.syncState *)
  | Op_cleanups : unit -> value Effect.t       (* Prim.sync, RunInterp.syncState *)
  | Op_yield_now : int -> value Effect.t       (* Prim.yieldNowWith *)
  | Op_never : unit -> value Effect.t          (* Prim.async, never resumed *)
  (* Round three: the remaining `WithFiberAction` arms that `countdownPark` reaches. *)
  | Op_await_all : int list -> value Effect.t          (* WithFiberAction.awaitAll *)
  | Op_interrupt_all : int list -> value Effect.t      (* WithFiberAction.interruptAll *)
  | Op_snapshot_children : unit -> value Effect.t      (* WithFiberAction.snapshotChildren *)
  | Op_await_new_children : value -> value Effect.t    (* WithFiberAction.awaitNewChildren *)
  | Op_set_interruptible : bool -> value Effect.t      (* WithFiberAction.setInterruptible *)
  | Op_refuse : string -> value Effect.t               (* WithFiberAction.refuse, S3 §5.2 *)
  (* The `Refs`, `ERefs`, `Deferreds` and `Scopes` families are `Op_store` requests that
     `deep_stores.ml` declares and answers, over the `Deep.Stores` carriers. *)
  (* `WithFiberAction.raceAll` (`Fibers.lean:866-880`). Round five. *)
  | Op_race_all : int list -> value Effect.t

(* A typed failure raised by a fiber body: `Prim.yieldableError`. *)
exception Efail_exn of int

(* What a `discontinue` at a park delivers: `Prim.failure accumulated`. *)
exception Einterrupt_exn of cause

(* ------------------------------------------------------------------------ `RunInterp`

   `RunInterp` (`Fibers.lean:386`), the machine's second parameter. A0 §3 DIVERGENCE 5 said
   it is "not a record: its 25 meanings are handler-arm code"; it is a record now, for the
   slots the machine itself calls. The rest of the arms are still code, because the avatar's
   `ν`/`σ` are OCaml control rather than names (DIVERGENCE 1) -- what a `contA` name means is
   the continuation `continue k` resumes.

   `St` is `unit` here: the store is a module-level record in `deep_stores.ml` and Lean's
   `RunMachine.update`/`modify` are the identity over `mutable` fields (DIVERGENCE 3), so
   every slot below takes the arguments Lean's takes minus the store and answers the answer
   minus the store. `Option St` becomes `bool`/`option`, `Prim` becomes a thunk. *)
type run_interp = {
  (* `RunInterp.syncState` (`Fibers.lean:400`), `registerAsync` (`:406`) and the
     `withFiberOf` (`:398`) arms the store owns, at one entry point: `σ` is `store_request`,
     which the machine cannot inspect. The arm answers through `ko` because a store
     operation may park (`Deferred.await`). *)
  mutable store_arm : run_machine -> run_fiber -> store_request -> kops -> unit;
  (* `RunInterp.dueResumes` (`Fibers.lean:414`). *)
  mutable due_resumes : unit -> (int * int * answer) list;
  (* `RunInterp.scopeStatus` (`Fibers.lean:427`): `None` unknown, `Some None` open,
     `Some (Some exit)` closed. *)
  mutable scope_status : int -> exitv option option;
  (* `RunInterp.scopeLinkFiber` (`Fibers.lean:431`): mode, scope, key, fiber. `false` is
     Lean's `none`, i.e. the scope is unknown. *)
  mutable scope_link_fiber : int -> int -> int -> int -> bool;
  (* `RunInterp.dropFinalizer` (`Fibers.lean:434`): scope, key. *)
  mutable drop_finalizer : int -> int -> bool;
  (* `RunInterp.closeScope` (`Fibers.lean:440`): scope, exit, the closer's `interruptible`,
     the closer's id. `None` is Lean's `none` (an unknown scope, M7). *)
  mutable close_scope : int -> exitv -> bool -> int -> (unit -> value) option;
}

(* The refusing default. Every slot names the `RunInterp` field it stands for, so a program
   that reaches an uninstalled store fails with that name rather than differing. *)
let interp : run_interp ref =
  ref
    { store_arm = (fun _ _ _ _ -> refuse "Effect4.Deep.RunInterp.syncState");
      due_resumes = (fun () -> []);
      scope_status = (fun _ -> None);
      scope_link_fiber = (fun _ _ _ _ -> false);
      drop_finalizer = (fun _ _ -> false);
      close_scope = (fun _ _ _ _ -> None) }

(* The body of a child, resolved through the fixture's table -- a fork names a declared
   root, never a closure (`fork-lowering.md` §(b)). Set by the fixture module. *)
(* P5's generated corpus (`workshop/OCaml5/fuzz/corpus/corpus_fixture.ml`) registers itself
   here, so the avatar's own binary does not depend on a file another spike regenerates. *)
let fuzz_programs : (string * (unit -> value)) list ref = ref []

let body_of_code : (int -> unit -> value) ref =
  ref (fun _ () -> failwith "no root table installed")

(* -------------------------------------------------------------- the service trace rows *)

type row =
  | Rop of string * value
  | Ranswer of string * value
  | Rfailed of string * int
  | Rdecide of int * bool
  | Rdone of exitv
  | Rfrontier

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

(* `Supervision.raceComplete` (`Effect4/Concurrency/Supervision.lean:407-420`): a callback
   preserves the first accepted result while updating the live bookkeeping. *)
let race_complete (r : race) (child : int) (exit_ : exitv) : unit =
  if List.mem child r.live then begin
    r.live <- List.filter (fun id -> id <> child) r.live;
    let reasons = match exit_ with Esuccess _ -> [] | Efailure c -> c.reasons in
    match r.accepted with
    | Some _ ->
      r.remaining <- r.remaining - 1;
      r.failures <- r.failures @ reasons
    | None -> (
      match exit_ with
      | Esuccess value ->
        r.remaining <- r.remaining - 1;
        r.accepted <- Some (Esuccess value);
        r.cleanup_needed <- r.live <> []
      | Efailure c ->
        if r.remaining <= 1 then begin
          r.remaining <- r.remaining - 1;
          r.failures <- r.failures @ c.reasons;
          r.accepted <- Some (Efailure { reasons = r.failures; annotations = [] });
          r.cleanup_needed <- false
        end
        else begin
          r.remaining <- r.remaining - 1;
          r.failures <- r.failures @ c.reasons
        end)
  end

let race_opt m id = List.find_opt (fun r -> r.rid = id) m.races

(* `spawn` (`:622`): mask by the options, the parent's context, tracked unless daemon. *)
let spawn m (parent : run_fiber) (program : unit -> value) ~daemon : int =
  let child_id = m.next_id in
  let child =
    run_fiber_make child_id program parent.frame.interruptible
      (!max_ops_before_yield, !prevent_yield) ()
  in
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

(* Round four: `iteration_prelude` is gone; `guard` below is the whole prelude, and it can
   now park, so the yield injection is a transition rather than an event. *)

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
  | DropScopeFinalizer (scope, key) ->
    (* `forkIn`'s key-dropping observer (`internal/effect.ts:5370-5372`) through
       `RunInterp.dropFinalizer` (`:434`); `none` is `Stuck.unknownScope` (M7). Round six:
       this arm used to halt unconditionally, which is why Deep W6 had no avatar member. *)
    if not (!interp.drop_finalizer scope key) then halt m (UnknownScope scope);
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
  | RaceCallback race_id -> (
    match race_opt m race_id with
    | None -> acc
    | Some r ->
      race_complete r id exit_;
      (match (r.accepted, r.settled) with
       | Some accepted, false ->
         (* settle: interrupt the live entrants with the host's id, then resume the host
            after they have been awaited -- a countdown over them (`:1108-1130`). *)
         r.settled <- true;
         emit m [ RaceSettled (race_id, accepted) ];
         let nested =
           List.fold_left
             (fun a entrant ->
               match fiber_opt m entrant with
               | None -> a
               | Some e ->
                 let apply_now = interrupt_record m (Some r.host) [] e in
                 emit m [ InterruptRecorded (Some r.host, entrant) ];
                 a @ if apply_now then [ Cevaluate entrant ] else [])
             [] r.live
         in
         (match fiber_opt m r.host with
          | None -> acc @ nested
          | Some host ->
            host.parked <- NotParked;
            host.pending <- List.filter (fun p -> p.token <> r.rtoken) host.pending;
            (match countdown_park m host r.live (RcontinueWith accepted) with
             | Some token ->
               host.frame.control <-
                 Suspended { ktoken = token; kresume = (fun a -> race_answer m host a) };
               acc @ nested
             | None ->
               (* Nothing was live: `countdownPark` applies the continuation at once, which
                  for the race host is the accepted exit. Re-evaluating the host instead
                  would deliver its pending cause -- the round-five bug this arm had. *)
               host.frame.control <- Onstack;
               race_answer m host (resume_prim (RcontinueWith accepted) []);
               acc @ nested))
       | _, _ -> acc))
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
     | Some token ->
       (* Lean resumes the fiber with `restoreName exit`, so the frame machine walks back to
          the same exit with `finalizing` set. The avatar's stack is already gone by the time
          `retc`/`exnc` runs (`doReturnToParent_frees`, O1 `:1078`), so the resumption is a
          machine-level closure that re-enters `exit_fiber`; `finalizing` being set now sends
          it down the second branch. *)
       f.frame.control <-
         Suspended
           { ktoken = token;
             kresume =
               (fun _ ->
                 let more = exit_fiber m f exit_ in
                 drive m m.drive_fuel more) }
     | None ->
       (* Nothing was live: the countdown's continuation applies at once. *)
       f.finalizing <- None);
    if f.finalizing = None then nested @ [ Cevaluate f.id ] else nested
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

(* `drive` (`:1025`). Each command costs one fuel; exhaustion is a live frontier, and so is
   a stuck machine. The fuel argument is Lean's, and `m.drive_fuel` carries it to the arms
   that run nested commands from inside `continue k`. *)
and drive m fuel (cmds : cmd list) : unit =
  match (fuel, cmds) with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ when m.stuck <> None -> ()
  | _, c :: rest ->
    exec m (fuel - 1) c;
    drive m (fuel - 1) rest

and exec m fuel (c : cmd) : unit =
  m.drive_fuel <- fuel;
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
        f.yielding <- false;
        f.parked <- NotParked;
        emit m [ Started id ];
        run_control m fuel f
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
          t.yielding <- false;
          emit m [ Started id ];
          k.kresume answer
        | _ -> ())
      | _ -> () (* the token guard: a stale resume is dropped *)))
  | Claunch (race_id, entrant) -> (
    (* `:1082-1101`. M8: once the race is settled an unlaunched entrant is interrupted, not
       deleted. *)
    match race_opt m race_id with
    | None -> ()
    | Some r ->
      if r.accepted <> None then (
        match fiber_opt m entrant with
        | None -> ()
        | Some e ->
          let apply_now = interrupt_record m (Some r.host) [] e in
          emit m [ RaceSkipped (race_id, entrant); InterruptRecorded (Some r.host, entrant) ];
          if apply_now then exec m fuel (Cevaluate entrant))
      else begin
        r.unstarted <- List.filter (fun e -> e <> entrant) r.unstarted;
        r.live <- r.live @ [ entrant ];
        emit m [ RaceLaunched (race_id, entrant) ];
        exec m fuel (Cevaluate entrant)
      end)
  | CdrainDue ->
    (* `RunInterp.dueResumes` (`:414`): the resumes the store owes now, in registration
       order, resumed synchronously inside the completing `sync` (M1). The store is
       `deep_stores.ml`'s; the slot is Lean's field. *)
    let due = !interp.due_resumes () in
    List.iter (fun (target, token, answer) -> exec m fuel (Cresume (target, token, answer))) due

(* What `Cmd.evaluate` finds in `current`. *)
and run_control m fuel (f : run_fiber) : unit =
  match f.frame.control with
  | Program body ->
    f.frame.control <- Onstack;
    run_under_handler m fuel f body
  | Failing cause ->
    (* current = Prim.failure over an empty stack: the frame machine's `resumeCause` walks
       nothing and finishes. The body never ran, so no finalizer frame exists. *)
    f.frame.control <- Onstack;
    finish m fuel f (Efailure cause)
  | Suspended k ->
    (* An interrupt applied to a parked fiber: Lean reaches the stack through
       `current := Prim.failure accumulated`; OCaml's spelling is `discontinue`. *)
    f.frame.control <- Onstack;
    k.kresume (Acause (frame_pending_cause f.frame))
  | Onstack | Ended -> ()

(* `retc` / `exnc`: this fiber's own stack has finished. *)
and finish m fuel (f : run_fiber) (exit_ : exitv) : unit =
  f.running <- false;
  let nested = exit_fiber m f exit_ in
  drive m fuel nested

(* The scheduler handler: `match_with` over the fiber body. Every `effc` arm is one
   `iteration` arm of `Fibers.lean:683`. *)
and run_under_handler m fuel (f : run_fiber) (body : unit -> value) : unit =
  let open Effect.Deep in
  match_with body ()
    {
      retc = (fun v -> finish m fuel f (Esuccess v));
      exnc =
        (fun e ->
          let exit_ =
            match e with
            | Efail_exn code -> Efailure (cause_fail code)
            | Einterrupt_exn c -> Efailure c
            | other -> Efailure (cause_die (Printexc.to_string other))
          in
          finish m fuel f exit_);
      effc =
        (fun (type a) (eff : a Effect.t) : ((a, unit) continuation -> unit) option ->
          (* One primitive, one `runLoop` iteration: `guard` runs `iteration`'s prelude
             (`internal/effect.ts:638-652`) before the arm, and the arm is a thunk because
             rc.112's yield injection re-evaluates the *same* primitive after the yield. *)
          let dispatch (k : (value, unit) continuation) (arm : kops -> unit) : unit =
            let ko = { ret = continue k; thr = discontinue k } in
            guard m f ko (fun () -> arm ko)
          in
          match eff with
          | Op_fork (code, daemon) ->
            Some (fun k -> dispatch k (fun ko -> arm_fork m f code daemon ko))
          | Op_join h -> Some (fun k -> dispatch k (fun ko -> arm_join m f h ko))
          | Op_await_value h ->
            Some (fun k -> dispatch k (fun ko -> arm_await m f h `Value ko))
          | Op_await_error h ->
            Some (fun k -> dispatch k (fun ko -> arm_await m f h `Error ko))
          | Op_interrupt h ->
            Some (fun k -> dispatch k (fun ko -> arm_interrupt m f h ko))
          | Op_started () ->
            Some (fun k -> dispatch k (fun ko -> arm_sync m f "started" (fun st -> st.started) ko))
          | Op_cleanups () ->
            Some (fun k -> dispatch k (fun ko -> arm_sync m f "cleanups" (fun st -> st.cleanups) ko))
          | Op_yield_now p ->
            Some (fun k -> dispatch k (fun ko -> arm_yield m f p ko))
          | Op_never () -> Some (fun k -> dispatch k (fun ko -> arm_never m f ko))
          | Op_await_all hs ->
            Some (fun k -> dispatch k (fun ko -> arm_await_all m f hs ko))
          | Op_interrupt_all hs ->
            Some (fun k -> dispatch k (fun ko -> arm_interrupt_all m f hs ko))
          | Op_snapshot_children () ->
            Some (fun k -> dispatch k (fun ko -> arm_snapshot_children m f ko))
          | Op_await_new_children snap ->
            Some (fun k -> dispatch k (fun ko -> arm_await_new_children m f snap ko))
          | Op_set_interruptible flag ->
            Some (fun k -> dispatch k (fun ko -> arm_set_interruptible m f flag ko))
          | Op_refuse name ->
            Some (fun k -> dispatch k (fun ko -> arm_refuse m f name ko))
          | Op_store req ->
            (* Every `Deep.Stores` operation: `syncState`, `registerAsync` and the
               `withFiberOf` arms the store owns (`Stores.lean:1337-1352`). The machine
               cannot inspect `σ`, so the whole arm is the interp's. *)
            Some (fun k -> dispatch k (fun ko -> !interp.store_arm m f req ko))
          | Op_race_all codes ->
            Some (fun k -> dispatch k (fun ko -> arm_race_all m f codes ko))
          | _ -> None);
    }

(* One `runLoop` iteration's prelude (`internal/effect.ts:638-668`, `Fibers.lean:683`),
   run before every primitive the avatar steps:

     :639-642  a deferred interrupt replaces the current primitive;
     :643      `this.currentOpCount++`, one per iteration over a primitive;
     :644-652  the yield injection, at most once per entry into `evaluate`, spelled by
               rc.112 as `current = flatMap(yieldNow, () => prev)` -- so the *same*
               primitive runs again after the yield, which is why `body` is a thunk.

   Round four makes this a real transition: it can park. Round three only emitted the
   `yieldInjected` event and carried on, so the budget was unobservable. *)
and guard m (f : run_fiber) (ko : kops) (body : unit -> unit) : unit =
  if f.frame.deferred_interrupt then begin
    f.frame.deferred_interrupt <- false;
    f.running <- false;
    ko.thr (Einterrupt_exn (frame_pending_cause f.frame))
  end
  else begin
    f.current_op_count <- f.current_op_count + 1;
    let verdict =
      match f.yield_override with
      | Some v -> v
      | None -> f.current_op_count >= f.max_ops_before_yield
    in
    if (not f.yielding) && (not f.prevent_yield) && verdict then begin
      f.yielding <- true;
      f.yield_override <- None;
      emit m [ YieldInjected (f.id, f.current_op_count) ];
      park_yield m f 0
        (fun () -> guard m f ko body)
        (fun c -> ko.thr (Einterrupt_exn c))
    end
    else body ()
  end

(* The service `answer` row is a further primitive. rc.112's traced service wraps the
   method's effect in `Effect.tap` (`harness/trace/tracer.ts:288-291`), so a whole run-loop
   iteration -- interrupt check, op count, yield check -- sits between the operation's value
   and the row. Round three pushed the row from inside the arm, where nothing could pre-empt
   it, which is the one divergence `extra.siblingCompletesDeferred` reported. *)
and answer_then m (f : run_fiber) name (v : value) (ko : kops) (k : unit -> unit) : unit =
  guard m f ko (fun () ->
      push_row (Ranswer (name, v));
      k ())

and answer_row m (f : run_fiber) name (v : value) (ko : kops) : unit =
  answer_then m f name v ko (fun () -> ko.ret v)

(* `WithFiberAction.fork` (`:5264-5284`) followed by `start` (`:5277`). *)
and arm_fork m f code daemon (ko : kops) : unit =
  begin
    let name = if daemon then "forkDetach" else "fork" in
    push_row (Rop (name, Vnat code));
    (* rc.112 adds the `interruptChildren` middleware in `Effect.forkChild` (`:612-614`). *)
    if not daemon then m.middleware_installed <- true;
    let child = spawn m f (!body_of_code code) ~daemon in
    let nested = start m f child ~immediately:false in
    let handle = handle_index "fiber" child in
    let site = Tape.site () in
    let branch = Tape.decide () in
    push_row (Rdecide (site, branch));
    answer_then m f name (Vhandle handle) ko (fun () ->
        drive m m.drive_fuel nested;
        (* On `true` the parent spends one primitive with the scheduler armed, so the run
           loop takes the processor away and drains its queue: `Prim.yieldNowWith 0`. *)
        if branch then
          park_yield m f 0
            (fun () -> ko.ret (Vhandle handle))
            (fun c -> ko.thr (Einterrupt_exn c))
        else ko.ret (Vhandle handle))
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
  park_yield m f priority
      (fun () -> ko.ret Vunit)
      (fun c -> ko.thr (Einterrupt_exn c))

(* `Prim.async` registering no resume: rc.112's `Effect.never`. *)
and arm_never m f (ko : kops) : unit =
  begin
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
  begin
    push_row (Rop ("join", Vhandle handle));
    let target = handle_target "fiber" handle in
    match fiber_opt m target with
    | None -> halt m (UnknownFiber target)
    | Some t -> (
      match t.exit_ with
      | Some e -> answer_join m f ko e (* :561-562 *)
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
                  | Aval v -> answer_row m f "join" v ko
                  | Acause c -> fail_op "join" ko c) })
  end

and answer_join m f ko (e : exitv) : unit =
  match e with
  | Esuccess v -> answer_row m f "join" v ko
  | Efailure c -> fail_op "join" ko c

(* A service operation that fails: the `failed` row, then the cause into the fiber. *)
and fail_op name (ko : kops) (c : cause) : unit =
  (* Only a typed failure gets a `failed` row: `traceService`'s `Effect.tapError`
     (`harness/trace/tracer.ts:291`) fires on the error channel, and an interruption is not
     on it. Round five: the avatar used to fabricate `failed <op> 0` for an interrupted
     operation, which rc.112 never emits. *)
  (match cause_fail_of c with Some e -> push_row (Rfailed (name, e)) | None -> ());
  ko.thr (Einterrupt_exn c)

(* `awaitValue` / `awaitError`: both `Fiber.await` (`:5304`), projected. *)
and arm_await m f handle which (ko : kops) : unit =
  begin
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
    let target = handle_target "fiber" handle in
    match fiber_opt m target with
    | None -> halt m (UnknownFiber target)
    | Some t -> (
      match t.exit_ with
      | Some e -> answer_row m f name (project e) ko
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
                  answer_row m f name (project e) ko) })
  end

(* `WithFiberAction.interrupt` (`:859`) = `interruptThenJoin`. *)
and arm_interrupt m f handle (ko : kops) : unit =
  begin
    push_row (Rop ("interrupt", Vhandle handle));
    let target = handle_target "fiber" handle in
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
                   | Aval _ -> answer_row m f "interrupt" Vunit ko
                   | Acause c -> ko.thr (Einterrupt_exn c)) };
         f.running <- false;
         drive m m.drive_fuel nested
       | None ->
         drive m m.drive_fuel nested;
         answer_row m f "interrupt" Vunit ko)
  end

(* `Prim.sync` through `RunInterp.syncState` (M1). *)
and arm_sync m f name (read : st -> int list) (ko : kops) : unit =
  begin
    push_row (Rop (name, Vunit));
    let v = Vlist (List.map (fun n -> Vnat n) (read m.state)) in
    drive m m.drive_fuel [ CdrainDue ];
    answer_row m f name v ko
  end

(* The general `Prim.sync` arm: `RunInterp.syncState` answers a value and the resumes the
   store owes are drained on the spot (`iteration`'s `some (state, value)` arm, M1). The
   store is `deep_stores.ml`'s, so `compute` closes over it rather than taking it: `St` is
   not a field of the machine here (DIVERGENCE 3). *)
and arm_state m f name (request : value) (compute : unit -> value) (ko : kops) : unit =
  begin
    push_row (Rop (name, request));
    let v = compute () in
    drive m m.drive_fuel [ CdrainDue ];
    answer_row m f name v ko
  end

(* ------------------------------------------------- the remaining fiber arms *)

(* `WithFiberAction.awaitAll` (`:5318-5322`): a countdown over the targets' exits, answered
   as the list of exits. *)
and arm_await_all m f (hs : int list) (ko : kops) : unit =
  begin
    push_row (Rop ("awaitAll", Vlist (List.map (fun h -> Vhandle h) hs)));
    let targets = List.map (handle_target "fiber") hs in
    match countdown_park m f targets RexitsValue with
    | Some token ->
      f.frame.control <-
        Suspended { ktoken = token; kresume = (fun a -> answer_countdown m f "awaitAll" ko a) };
      f.running <- false
    | None ->
      let exits = List.filter_map (fun t -> (fiber_exn m t).exit_) targets in
      answer_countdown m f "awaitAll" ko (resume_prim RexitsValue exits)
  end

(* `WithFiberAction.interruptAll` (`:895`, `:913`): record on every target first, then await
   them all. *)
and arm_interrupt_all m f (hs : int list) (ko : kops) : unit =
  begin
    push_row (Rop ("interruptAll", Vlist (List.map (fun h -> Vhandle h) hs)));
    let targets = List.map (handle_target "fiber") hs in
    let nested =
      List.fold_left
        (fun acc t ->
          match fiber_opt m t with
          | None -> acc
          | Some g ->
            let apply_now = interrupt_record m (Some f.id) [] g in
            emit m [ InterruptRecorded (Some f.id, t) ];
            acc @ if apply_now then [ Cevaluate t ] else [])
        [] targets
    in
    match countdown_park m f targets Rvoid with
    | Some token ->
      f.frame.control <-
        Suspended { ktoken = token; kresume = (fun a -> answer_countdown m f "interruptAll" ko a) };
      f.running <- false;
      drive m m.drive_fuel nested
    | None ->
      drive m m.drive_fuel nested;
      answer_row m f "interruptAll" Vunit ko
  end

(* `WithFiberAction.raceAll` (`Fibers.lean:866-880`): the entrants exist as fibers before any
   launch, each carrying a `raceCallback` observer; the host parks on the race token and each
   launch is a command. The empty race stays pending until interrupted. *)
and arm_race_all m f (codes : int list) (ko : kops) : unit =
  begin
    push_row (Rop ("raceAll", Vlist (List.map (fun c -> Vnat c) codes)));
    let race_id = m.next_race in
    let token = fresh_token m in
    m.next_race <- race_id + 1;
    let ids =
      List.map
        (fun code ->
          let child = spawn m f (!body_of_code code) ~daemon:true in
          let c = fiber_exn m child in
          c.observers <- c.observers @ [ RaceCallback race_id ];
          child)
        codes
    in
    let r =
      { rid = race_id; host = f.id; rtoken = token; settled = false; live = []; unstarted = ids;
        remaining = List.length ids; failures = []; accepted = None; cleanup_needed = false }
    in
    m.races <- m.races @ [ r ];
    emit m [ RaceStarted (race_id, f.id, ids) ];
    run_fiber_park f
      { token; waiting_on = None; remaining = 0; collected = []; resume_with = Rvoid };
    emit m [ ParkedOn (f.id, token) ];
    f.frame.control <-
      Suspended { ktoken = token; kresume = (fun a -> race_answer m f a) };
    f.race_answer <- Some ko;
    f.running <- false;
    drive m m.drive_fuel (List.map (fun e -> Claunch (race_id, e)) ids)
  end

(* The host's resumption, whichever token it comes back on. *)
and race_answer m (f : run_fiber) (a : answer) : unit =
  match f.race_answer with
  | None -> ()
  | Some ko ->
    f.race_answer <- None;
    (match a with
     | Aval v -> answer_row m f "raceAll" v ko
     | Acause c -> fail_op "raceAll" ko c)

(* `WithFiberAction.snapshotChildren` (`:5318`). *)
and arm_snapshot_children m f (ko : kops) : unit =
  begin
    push_row (Rop ("childrenSnapshot", Vunit));
    let v = Vlist (List.map (fun c -> Vhandle (handle_index "fiber" c)) f.children) in
    answer_row m f "childrenSnapshot" v ko
  end

(* `WithFiberAction.awaitNewChildren snapshot`: await the children added since. *)
and arm_await_new_children m f (snapshot : value) (ko : kops) : unit =
  begin
    push_row (Rop ("awaitChildren", snapshot));
    let seen =
      match snapshot with
      | Vlist items ->
        List.map (function Vhandle h -> handle_target "fiber" h | _ -> -1) items
      | _ -> []
    in
    let fresh = List.filter (fun c -> not (List.mem c seen)) f.children in
    match countdown_park m f fresh Rvoid with
    | Some token ->
      f.frame.control <-
        Suspended { ktoken = token; kresume = (fun a -> answer_countdown m f "awaitChildren" ko a) };
      f.running <- false
    | None -> answer_row m f "awaitChildren" Vunit ko
  end

(* What a finished countdown answers with. *)
and answer_countdown m f name (ko : kops) (a : answer) : unit =
  match a with
  | Aval v -> answer_row m f name v ko
  | Acause c -> fail_op name ko c

(* `WithFiberAction.setInterruptible` (`:4302-4310`, `:4331-4352`, M2): set the flag, and on
   restoring interruptibility fail now if a cause is pending. Answers the previous flag, so a
   program can spell rc.112's `uninterruptible` as a bracket. *)
and arm_set_interruptible m f (flag : bool) (ko : kops) : unit =
  begin
    let previous = f.frame.interruptible in
    f.frame.interruptible <- flag;
    if flag then
      match f.frame.interrupted_cause with
      | Some cause ->
        (* `FrameFiber.ensure` on `setInterruptible true` with a recorded cause returns the
           replacement continuation `failure cause` (`Runtime.lean:650-653`). *)
        f.running <- false;
        ko.thr (Einterrupt_exn cause)
      | None -> ko.ret (Vbool previous)
    else ko.ret (Vbool previous)
  end

(* `WithFiberAction.refuse` (S3 §5.2): the interp refuses this thunk and the fiber fails
   with the cause, visibly. Every `WithFiberAction` arm this pass does not implement is
   reached through here, so an unimplemented arm refuses rather than differing. *)
and arm_refuse m f (name : string) (ko : kops) : unit =
  begin
    f.running <- false;
    ko.thr (Einterrupt_exn (cause_die ("unimplemented WithFiberAction: " ^ name)))
  end

(* ---------------------------------------- the store arms: `deep_stores.ml`, `deep_layer.ml`

   `arm_ref_make`, `arm_def_make`, `arm_scope_make`, `arm_def_complete`, `arm_def_await` and
   the three `*_cell` lookups were here, improvising the three stores as hashtables of ints.
   They are `deep_stores.ml`'s now, on the `Stores.lean` carriers, installed into `interp`
   above. `arm_layer_build` follows into `deep_layer.ml`. *)

(* ------------------------------------------------------------------- runtime entries *)

(* `stepDecision.fire` (`Scheduler.ts:225-233`): drain once, run the tasks in order. *)
let fire m fuel owner =
  match fiber_opt m owner with
  | None -> ()
  | Some o ->
    let tasks = Dispatcher.drain o.dispatcher in
    List.iter
      (fun task ->
        emit m [ RanTask (owner, task) ];
        match task with
        | Tstart child -> drive m fuel [ Cevaluate child; CdrainDue ]
        | Tresume (target, token, answer) ->
          drive m fuel [ Cresume (target, token, answer); CdrainDue ])
      tasks

(* `stepDecision.flushAll`: armed dispatchers in fiber order until none is armed. *)
let rec flush_all m fuel rounds =
  if rounds = 0 then ()
  else
    let armed = List.filter (fun f -> f.dispatcher.armed) m.fibers in
    if armed = [] || m.stuck <> None then ()
    else begin
      List.iter (fun f -> fire m fuel f.id) armed;
      flush_all m fuel (rounds - 1)
    end

(* `stepDecision` (`:1108`). *)
let step_decision m fuel = function
  | Dfire owner -> fire m fuel owner
  | Dflush -> flush_all m fuel default_rounds
  | Devaluate id -> drive m fuel [ Cevaluate id; CdrainDue ]
  | DyieldVerdict (id, verdict) -> (
    match fiber_opt m id with Some f -> f.yield_override <- Some verdict | None -> ())
  | DanswerAsync (id, token, answer) -> drive m fuel [ Cresume (id, token, answer); CdrainDue ]
  | DinterruptFrom (interruptor, annotations, target) -> (
    match fiber_opt m target with
    | None -> ()
    | Some t ->
      let apply_now = interrupt_record m interruptor annotations t in
      emit m [ InterruptRecorded (interruptor, target) ];
      if t.frame.deferred_interrupt && t.running then emit m [ InterruptDeferred target ];
      if apply_now then drive m fuel [ Cevaluate target; CdrainDue ])
  | DinstallMiddleware -> m.middleware_installed <- true

(* `runFork` (`:1184`): one root fiber, evaluated synchronously on the caller stack. *)
let run_fork m fuel (program : unit -> value) : int =
  let root = m.next_id in
  let fiber = run_fiber_make root program true (!max_ops_before_yield, !prevent_yield) () in
  m.fibers <- m.fibers @ [ fiber ];
  m.next_id <- m.next_id + 1;
  drive m fuel [ Cevaluate root; CdrainDue ];
  root

(* `runCallback` (`:1194`): `runFork` plus an exit observer under `key`. *)
let run_callback m fuel (program : unit -> value) (key : int) : int =
  let root = m.next_id in
  let fiber = run_fiber_make root program true (!max_ops_before_yield, !prevent_yield) () in
  fiber.observers <- [ Callback key ];
  m.fibers <- m.fibers @ [ fiber ];
  m.next_id <- m.next_id + 1;
  drive m fuel [ Cevaluate root; CdrainDue ];
  root

(* `runSyncExit` (`:1205`): `runFork`, flush, and the `AsyncFiberError` defect when the root
   survives the flush. *)
let run_sync_exit m fuel (program : unit -> value) : exitv =
  let root = run_fork m fuel program in
  step_decision m fuel Dflush;
  match (fiber_exn m root).exit_ with
  | Some e -> e
  | None -> Efailure (cause_die "AsyncFiberError")

(* `replayEval`'s three results (`:1164`) over the one tape the trace faces use: a run that
   ends with the root exited is `finished`; one that reaches quiescence with the root still
   parked is `frontier` (`harness/trace/tracer.ts:434-442` writes the same row when its
   stall deadline fires); a stuck machine is `stuck`. *)
type replay_result = Rfinished of exitv | Rfrontier | Rstuck of stuck

let run_program m fuel (program : unit -> value) : replay_result =
  let root = run_fork m fuel program in
  step_decision m fuel Dflush;
  match m.stuck with
  | Some why -> Rstuck why
  | None -> ( match (fiber_exn m root).exit_ with Some e -> Rfinished e | None -> Rfrontier)

(* `promiseOutcome` (`:1216`). *)
let promise_outcome (e : exitv) : (value, cause) result =
  match e with Esuccess v -> Ok v | Efailure c -> Error c
