(* E4_engine -- see e4_engine.mli. *)

type frontier = { parked : (int * int) list; armed : int list; due : int }

type answer =
  | Finished
  | Suspended of frontier
  | Refused of string
  | Delay of frontier

module type INSTANCE = sig
  include E4_program.PROGRAM_TYPES

  val name : string
  val carriers : string

  type nu
  type s
  type fiber_id = int
  type ref_key = int
  type 'a reason_annotations = (string * 'a) list

  type ('e, 'd, 'i, 'a) reason =
    | Reason_fail of 'e * 'a reason_annotations
    | Reason_die of 'd * 'a reason_annotations
    | Reason_interrupt of 'i option * 'a reason_annotations

  type ('e, 'd, 'i, 'a) cause = ('e, 'd, 'i, 'a) reason list

  type ('b, 'e, 'd, 'i, 'a) exit_ =
    | Exit_success of 'b
    | Exit_failure of ('e, 'd, 'i, 'a) cause

  type ('b, 'e, 'd, 'i, 'a) completion =
    | Completion_ofExit of ('b, 'e, 'd, 'i, 'a) exit_
    | Completion_ofRefGet of ref_key

  type err = Err_boom | Err_tag of int

  type defect =
    | Defect_notImplemented
    | Defect_asyncFiber
    | Defect_badName
    | Defect_missingService
    | Defect_user of int

  type val_ =
    | Val_unit
    | Val_bool of bool
    | Val_nat of int
    | Val_str of string
    | Val_bytes of int list
    | Val_list of val_ list
    | Val_pair of val_ * val_
    | Val_none
    | Val_some of val_
    | Val_ctor of int * val_ list
    | Val_ref of int * int list
    | Val_handle of int * int

  type stuck =
    | Stuck_unknownFiber of fiber_id
    | Stuck_unknownScope of int
    | Stuck_unknownRace of int

  type parked = Parked_notParked | Parked_withGuard of int

  type observer =
    | Observer_resumeAwait of fiber_id * int * observer_mode
    | Observer_untrackChild of fiber_id
    | Observer_dropScopeFinalizer of int * int
    | Observer_countdown of fiber_id * int
    | Observer_raceCallback of int
    | Observer_callback of int

  type scope_mode = ScopeMode_forkIn | ScopeMode_fiberRunIn
  type outcome = Outcome_finished | Outcome_frontier | Outcome_stuck of stuck
  type 'u service = { key : service_key; value : 'u }
  type 'u context = 'u service list

  type ctx = {
    services : val_ context;
    max_ops_before_yield : int;
    prevent_yield : bool;
  }

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim =
    | Prim_success of 'b
    | Prim_failure of ('e, 'd, 'i, 'a) cause
    | Prim_sync of 's
    | Prim_suspend of 's
    | Prim_withFiber of 's
    | Prim_yieldableError of 'e
    | Prim_iterator of 'nu * 'b
    | Prim_onSuccess of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu
    | Prim_onSuccessConst of
        ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | Prim_onFailure of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu
    | Prim_onSuccessAndFailure of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu * 'nu
    | Prim_exitFrame of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | Prim_onExit of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu * bool
    | Prim_setInterruptible of bool
    | Prim_whileLoop of 'nu * 'b
    | Prim_yieldNowWith of int
    | Prim_async of 'nu * bool * 'nu option
    | Prim_asyncFinalizer of 'nu

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) frame_event =
    | FrameEvent_popped of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | FrameEvent_ranContAll of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | FrameEvent_pushed of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | FrameEvent_ranFinalizer of 'nu * ('b, 'e, 'd, 'i, 'a) exit_
    | FrameEvent_substituted of ('e, 'd, 'i, 'a) cause
    | FrameEvent_deferred of ('e, 'd, 'i, 'a) cause
    | FrameEvent_yielded of ('b, 'e, 'd, 'i, 'a) exit_

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task =
    | Task_start of fiber_id
    | Task_resume of fiber_id * int * 'k

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'ch, 'k, 'h) run_event =
    | RunEvent_forked of fiber_id * fiber_id * bool
    | RunEvent_started of fiber_id
    | RunEvent_scheduledTask of fiber_id * int * ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task
    | RunEvent_ranTask of fiber_id * ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task
    | RunEvent_yieldInjected of fiber_id * int
    | RunEvent_parkedOn of fiber_id * int
    | RunEvent_resumedWith of fiber_id * int * 'k
    | RunEvent_interruptRecorded of fiber_id option * fiber_id
    | RunEvent_interruptDeferred of fiber_id
    | RunEvent_childrenInterrupted of fiber_id * fiber_id list
    | RunEvent_observerFired of fiber_id * observer
    | RunEvent_frame of fiber_id * 'h
    | RunEvent_finalizerProgram of fiber_id * 'nu * ('b, 'e, 'd, 'i, 'a) exit_
    | RunEvent_scopeLinked of scope_mode * int * int * fiber_id
    | RunEvent_scopeClosedOnLink of int * fiber_id
    | RunEvent_raceStarted of int * fiber_id * int
    | RunEvent_raceLaunched of int * fiber_id
    | RunEvent_raceSettled of int * ('b, 'e, 'd, 'i, 'a) exit_
    | RunEvent_contextSet of fiber_id * 'ch
    | RunEvent_callback of int * ('b, 'e, 'd, 'i, 'a) exit_
    | RunEvent_exited of fiber_id * ('b, 'e, 'd, 'i, 'a) exit_

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) run_decision =
    | RunDecision_fire of fiber_id
    | RunDecision_flush
    | RunDecision_evaluate of fiber_id
    | RunDecision_yieldVerdict of fiber_id * bool
    | RunDecision_answerAsync of fiber_id * int * ('b, 'e, 'd, 'i, 'a) completion
    | RunDecision_interruptFrom of fiber_id option * 'a reason_annotations * fiber_id
    | RunDecision_installMiddleware

  type machine
  type fiber
  type interp
  type program = native_op eff

  type event =
    ( nu,
      s,
      val_,
      err,
      defect,
      fiber_id,
      unit,
      ctx,
      (nu, s, val_, err, defect, fiber_id, unit) prim,
      (nu, s, val_, err, defect, fiber_id, unit) frame_event )
    run_event

  type decision = (nu, s, val_, err, defect, fiber_id, unit) run_decision

  val api_evaluate : decision
  val interp_of : program -> interp
  val load : program -> fuel:int -> choices:bool list -> machine
  val step : program -> interp -> fuel:int -> machine -> decision -> machine * bool
  val run_api : program -> fuel:int -> choices:bool list -> outcome * machine
  val fibers : machine -> (fiber_id * fiber) list
  val fiber_count : machine -> int
  val trace : machine -> event list
  val trace_length : machine -> int
  val stuck_of : machine -> stuck option
  val armed_of : machine -> fiber_id list
  val next_id : machine -> int
  val next_token : machine -> int
  val race_count : machine -> int
  val middleware : machine -> bool
  val finished : machine -> bool
  val completed_exits :
    machine -> (fiber_id * (val_, err, defect, fiber_id, unit) exit_) list
  val refs : machine -> val_ list
  val next_name : machine -> int
  val due_count : machine -> int
  val cell_count : machine -> int
  val scope_count : machine -> int
  val memo_map_count : machine -> int
  val memo_paths : machine -> (int * int list list) list
  val f_id : fiber -> fiber_id
  val f_exit : fiber -> (val_, err, defect, fiber_id, unit) exit_ option
  val f_parked : fiber -> parked
  val f_running : fiber -> bool
  val f_finalizing : fiber -> bool
  val f_pending_tokens : fiber -> int list
  val f_observers : fiber -> observer list
  val f_children : fiber -> fiber_id list
  val f_op_count : fiber -> int
  val f_max_ops : fiber -> int
  val f_prevent_yield : fiber -> bool
  val f_yield_override : fiber -> bool option
  val f_context : fiber -> ctx
  val f_dispatcher_armed : fiber -> bool
  val f_dispatcher : fiber -> (int * int) list
end

module type ENGINE = sig
  val name : string
  val carriers : string

  type t
  type decision
  type program

  val evaluate : int -> decision
  val flush : decision
  val fire : int -> decision
  val yield_verdict : int -> bool -> decision
  val answer_async_success : int -> int -> int -> decision
  val interrupt_from : int option -> int -> decision
  val install_middleware : decision
  val compile : Eff_types.eff -> program
  val of_bytes : string -> program option
  val load_program : program -> fuel:int -> t
  val load : Eff_types.eff -> fuel:int -> t
  val load_bytes : string -> fuel:int -> t option
  val step : t -> decision -> t
  val replay : t -> decision list -> t
  val replay_to : t -> decision list -> t * decision list
  val replay_steps : t -> decision list -> t Seq.t
  val replay_positions : t -> decision list -> t Seq.t
  val drive : t -> t
  val run : Eff_types.eff -> fuel:int -> t
  val run_program : program -> fuel:int -> t
  val api_run : program -> fuel:int -> string
  val answer : t -> answer
  val outcome : t -> string
  val exits : t -> (int * string) list
  val root_exit : t -> string option
  val fiber_rows : t -> (int * string) list
  val fiber_count : t -> int
  val trace_rows : t -> string list
  val trace_length : t -> int
  val refs : t -> string list
  val store_row : t -> string
  val snapshot : t -> t
  val fuel : t -> int
end

(* ------------------------------------------------------------------------- the loop *)

module Make (I : INSTANCE) = struct
  module P = E4_program.Make (I)

  let name = I.name
  let carriers = I.carriers

  type program = I.program
  type decision = I.decision

  type t = {
    program : I.program;
    interp : I.interp;
    fuel_ : int;
    m : I.machine;
    settled : bool;  (** the generated `settled` of the LAST step; true after a load *)
  }

  (* -- the tape ------------------------------------------------------------------- *)

  let evaluate id : decision = I.RunDecision_evaluate id
  let flush : decision = I.RunDecision_flush
  let fire id : decision = I.RunDecision_fire id
  let yield_verdict id b : decision = I.RunDecision_yieldVerdict (id, b)

  let answer_async_success fiber token n : decision =
    I.RunDecision_answerAsync
      (fiber, token, I.Completion_ofExit (I.Exit_success (I.Val_nat n)))

  let interrupt_from who target : decision =
    I.RunDecision_interruptFrom (who, [], target)

  let install_middleware : decision = I.RunDecision_installMiddleware

  (* -- loading -------------------------------------------------------------------- *)

  let compile (p : Eff_types.eff) : program = P.load p
  let of_bytes (b : string) : program option = P.of_bytes b

  let load_program (p : program) ~(fuel : int) : t =
    { program = p; interp = I.interp_of p; fuel_ = fuel;
      m = I.load p ~fuel ~choices:[]; settled = true }

  let load (p : Eff_types.eff) ~(fuel : int) : t = load_program (compile p) ~fuel

  let load_bytes (b : string) ~(fuel : int) : t option =
    match of_bytes b with None -> None | Some p -> Some (load_program p ~fuel)

  (* -- driving -------------------------------------------------------------------- *)

  let step (t : t) (d : decision) : t =
    let m, settled = I.step t.program t.interp ~fuel:t.fuel_ t.m d in
    { t with m; settled }

  (* `replayEval` STOPS consuming the tape (Fibers.lean:2028-2040, generated at
     api_engine.ml's `replayEval`): at a stuck machine it answers `stuck why m` WITHOUT
     applying the decision, and at an unsettled step -- a non-empty command residue, i.e. the
     fuel ran out -- it answers `frontier r.1` and reads no further.  Everything after that
     point is not part of the run: Lean does not define a machine there.

     Lane P6 finding F1: `replay_steps` used to be `Seq.scan step_or_hold`, which DID define
     one -- the halted machine, repeated -- so a 64-decision tape at low fuel yielded one
     machine 64 times and a caller measuring "consecutive positions" measured one position
     over and over.  The sequence now ends where the replay ends, and `replay_to` hands back
     the decisions that were never read, whose head is the REFUSED one when the machine is
     stuck. *)
  let halted (t : t) : bool = Option.is_some (I.stuck_of t.m) || not t.settled
  let step_or_hold (t : t) (d : decision) : t = if halted t then t else step t d

  (* The machine and the decisions the replay never read.  `[]` means the tape was spent; a
     non-empty residue means the replay STOPPED, and its head is the decision at the stop —
     the REFUSED one when the machine is stuck, since Lean answers `stuck why m` without
     applying it.  The position of the stop is `|tape| - |residue|`. *)
  let rec replay_to (t : t) (tape : decision list) : t * decision list =
    if halted t then (t, tape)
    else match tape with [] -> (t, []) | d :: rest -> replay_to (step t d) rest

  let replay (t : t) (tape : decision list) : t = fst (replay_to t tape)

  (* TAPE positions: the machine after each PREFIX of the tape, |tape| + 1 of them.  It is
     total by construction — every position is `replay t (the first i decisions)` — and past
     the stop the machine is PHYSICALLY the halted one, which is how a caller tells the
     repetition from a run (`t == u`), and `replay_to` is how it finds where the run ended. *)
  let replay_steps (t : t) (tape : decision list) : t Seq.t =
    Seq.scan step_or_hold t (List.to_seq tape)

  (* RUN positions: the machines the replay actually visits.  It ends where `replayEval` ends
     (Fibers.lean:2028-2040) and repeats nothing, so `Seq.length` of it is the number of
     positions the run has.  Lane P6's finding F1 is exactly the difference between this and
     the sequence above: a 64-decision tape whose fuel runs out at the first decision has
     |tape| + 1 = 65 TAPE positions and 2 RUN positions. *)
  let replay_positions (t : t) (tape : decision list) : t Seq.t =
    let rec go (t : t) (tape : decision list) () =
      if halted t then Seq.Cons (t, Seq.empty)
      else
        match tape with
        | [] -> Seq.Cons (t, Seq.empty)
        | d :: rest -> Seq.Cons (t, go (step t d) rest)
    in
    go t tape

  let drive (t : t) : t = replay t [ I.api_evaluate; flush ]
  let run_program (p : program) ~(fuel : int) : t = drive (load_program p ~fuel)
  let run (p : Eff_types.eff) ~(fuel : int) : t = run_program (compile p) ~fuel

  (* -- the renderers -------------------------------------------------------------- *)

  let rec show_val (v : I.val_) : string =
    match v with
    | I.Val_unit -> "unit"
    | I.Val_bool b -> string_of_bool b
    | I.Val_nat n -> string_of_int n
    | I.Val_str s -> Printf.sprintf "%S" s
    | I.Val_bytes bs ->
      "bytes[" ^ String.concat "," (List.map string_of_int bs) ^ "]"
    | I.Val_list xs -> "list[" ^ String.concat "," (List.map show_val xs) ^ "]"
    | I.Val_pair (a, b) -> "pair(" ^ show_val a ^ "," ^ show_val b ^ ")"
    | I.Val_none -> "none"
    | I.Val_some x -> "some " ^ show_val x
    | I.Val_ctor (i, args) ->
      Printf.sprintf "ctor %d [%s]" i (String.concat ", " (List.map show_val args))
    | I.Val_ref (k, path) ->
      Printf.sprintf "ref %d/[%s]" k (String.concat "," (List.map string_of_int path))
    | I.Val_handle (k, n) -> Printf.sprintf "handle %d/%d" k n

  let show_err (e : I.err) : string =
    match e with I.Err_boom -> "boom" | I.Err_tag t -> Printf.sprintf "tag %d" t

  let show_defect (d : I.defect) : string =
    match d with
    | I.Defect_notImplemented -> "notImplemented"
    | I.Defect_asyncFiber -> "asyncFiber"
    | I.Defect_badName -> "badName"
    | I.Defect_missingService -> "missingService"
    | I.Defect_user n -> Printf.sprintf "user %d" n

  let show_anns (a : unit I.reason_annotations) : string =
    if a = [] then "" else "{" ^ String.concat "," (List.map fst a) ^ "}"

  let show_reason (r : (I.err, I.defect, I.fiber_id, unit) I.reason) : string =
    match r with
    | I.Reason_fail (e, a) -> "fail(" ^ show_err e ^ ")" ^ show_anns a
    | I.Reason_die (d, a) -> "die(" ^ show_defect d ^ ")" ^ show_anns a
    | I.Reason_interrupt (None, a) -> "interrupt(none)" ^ show_anns a
    | I.Reason_interrupt (Some i, a) ->
      Printf.sprintf "interrupt(%d)%s" i (show_anns a)

  let show_cause (c : (I.err, I.defect, I.fiber_id, unit) I.cause) : string =
    "[" ^ String.concat "; " (List.map show_reason c) ^ "]"

  let show_exit (x : (I.val_, I.err, I.defect, I.fiber_id, unit) I.exit_) : string =
    match x with
    | I.Exit_success v -> "success " ^ show_val v
    | I.Exit_failure c -> "failure " ^ show_cause c

  let show_exit_opt = function None -> "-" | Some x -> show_exit x

  let show_observer_mode (m : I.observer_mode) : string =
    match m with
    | I.ObserverMode_awaitValue -> "awaitValue"
    | I.ObserverMode_joinEffect -> "joinEffect"

  let show_observer (o : I.observer) : string =
    match o with
    | I.Observer_resumeAwait (f, t, m) ->
      Printf.sprintf "resumeAwait(%d,%d,%s)" f t (show_observer_mode m)
    | I.Observer_untrackChild f -> Printf.sprintf "untrackChild(%d)" f
    | I.Observer_dropScopeFinalizer (a, b) ->
      Printf.sprintf "dropScopeFinalizer(%d,%d)" a b
    | I.Observer_countdown (f, t) -> Printf.sprintf "countdown(%d,%d)" f t
    | I.Observer_raceCallback n -> Printf.sprintf "raceCallback(%d)" n
    | I.Observer_callback n -> Printf.sprintf "callback(%d)" n

  let show_parked (p : I.parked) : string =
    match p with
    | I.Parked_notParked -> "-"
    | I.Parked_withGuard t -> Printf.sprintf "guard %d" t

  let show_stuck (s : I.stuck) : string =
    match s with
    | I.Stuck_unknownFiber f -> Printf.sprintf "unknownFiber %d" f
    | I.Stuck_unknownScope k -> Printf.sprintf "unknownScope %d" k
    | I.Stuck_unknownRace r -> Printf.sprintf "unknownRace %d" r

  let show_scope_mode (m : I.scope_mode) : string =
    match m with I.ScopeMode_forkIn -> "forkIn" | I.ScopeMode_fiberRunIn -> "fiberRunIn"

  let show_ctx (c : I.ctx) : string =
    Printf.sprintf "ctx(%s;%d;%b)"
      (String.concat ","
         (List.map
            (fun (sv : I.val_ I.service) ->
               Printf.sprintf "%d:%d=%s" sv.I.key.I.name sv.I.key.I.service
                 (show_val sv.I.value))
            c.I.services))
      c.I.max_ops_before_yield c.I.prevent_yield

  (* `nu` (EffName) and `s` (EffThunk) are the two payloads this projection does not
     descend into -- see the header's note on the differential's reach. *)
  let rec show_prim
      (p : (I.nu, I.s, I.val_, I.err, I.defect, I.fiber_id, unit) I.prim) : string =
    match p with
    | I.Prim_success v -> "success " ^ show_val v
    | I.Prim_failure c -> "failure " ^ show_cause c
    | I.Prim_sync _ -> "sync <thunk>"
    | I.Prim_suspend _ -> "suspend <thunk>"
    | I.Prim_withFiber _ -> "withFiber <thunk>"
    | I.Prim_yieldableError e -> "yieldableError " ^ show_err e
    | I.Prim_iterator (_, v) -> "iterator(<name>," ^ show_val v ^ ")"
    | I.Prim_onSuccess (q, _) -> "onSuccess(" ^ show_prim q ^ ",<name>)"
    | I.Prim_onSuccessConst (q, r) ->
      "onSuccessConst(" ^ show_prim q ^ "," ^ show_prim r ^ ")"
    | I.Prim_onFailure (q, _) -> "onFailure(" ^ show_prim q ^ ",<name>)"
    | I.Prim_onSuccessAndFailure (q, _, _) ->
      "onSuccessAndFailure(" ^ show_prim q ^ ",<name>,<name>)"
    | I.Prim_exitFrame q -> "exitFrame(" ^ show_prim q ^ ")"
    | I.Prim_onExit (q, _, b) -> Printf.sprintf "onExit(%s,<name>,%b)" (show_prim q) b
    | I.Prim_setInterruptible b -> Printf.sprintf "setInterruptible(%b)" b
    | I.Prim_whileLoop (_, v) -> "whileLoop(<name>," ^ show_val v ^ ")"
    | I.Prim_yieldNowWith n -> Printf.sprintf "yieldNowWith(%d)" n
    | I.Prim_async (_, b, o) ->
      Printf.sprintf "async(<name>,%b,%s)" b (match o with None -> "none" | Some _ -> "some")
    | I.Prim_asyncFinalizer _ -> "asyncFinalizer(<name>)"

  let show_frame_event
      (e : (I.nu, I.s, I.val_, I.err, I.defect, I.fiber_id, unit) I.frame_event) : string =
    match e with
    | I.FrameEvent_popped p -> "popped(" ^ show_prim p ^ ")"
    | I.FrameEvent_ranContAll p -> "ranContAll(" ^ show_prim p ^ ")"
    | I.FrameEvent_pushed p -> "pushed(" ^ show_prim p ^ ")"
    | I.FrameEvent_ranFinalizer (_, x) -> "ranFinalizer(<name>," ^ show_exit x ^ ")"
    | I.FrameEvent_substituted c -> "substituted " ^ show_cause c
    | I.FrameEvent_deferred c -> "deferred " ^ show_cause c
    | I.FrameEvent_yielded x -> "yielded(" ^ show_exit x ^ ")"

  let show_task
      (t :
        ( I.nu,
          I.s,
          I.val_,
          I.err,
          I.defect,
          I.fiber_id,
          unit,
          (I.nu, I.s, I.val_, I.err, I.defect, I.fiber_id, unit) I.prim )
        I.task) : string =
    match t with
    | I.Task_start f -> Printf.sprintf "start(%d)" f
    | I.Task_resume (f, tok, k) -> Printf.sprintf "resume(%d,%d,%s)" f tok (show_prim k)

  let ids xs = "[" ^ String.concat "," (List.map string_of_int xs) ^ "]"

  let show_event (e : I.event) : string =
    match e with
    | I.RunEvent_forked (p, c, d) -> Printf.sprintf "forked(%d,%d,%b)" p c d
    | I.RunEvent_started f -> Printf.sprintf "started(%d)" f
    | I.RunEvent_scheduledTask (f, pr, t) ->
      Printf.sprintf "scheduledTask(%d,%d,%s)" f pr (show_task t)
    | I.RunEvent_ranTask (f, t) -> Printf.sprintf "ranTask(%d,%s)" f (show_task t)
    | I.RunEvent_yieldInjected (f, n) -> Printf.sprintf "yieldInjected(%d,%d)" f n
    | I.RunEvent_parkedOn (f, tok) -> Printf.sprintf "parkedOn(%d,%d)" f tok
    | I.RunEvent_resumedWith (f, tok, k) ->
      Printf.sprintf "resumedWith(%d,%d,%s)" f tok (show_prim k)
    | I.RunEvent_interruptRecorded (who, target) ->
      Printf.sprintf "interruptRecorded(%s,%d)"
        (match who with None -> "-" | Some i -> string_of_int i)
        target
    | I.RunEvent_interruptDeferred f -> Printf.sprintf "interruptDeferred(%d)" f
    | I.RunEvent_childrenInterrupted (f, cs) ->
      Printf.sprintf "childrenInterrupted(%d,%s)" f (ids cs)
    | I.RunEvent_observerFired (f, o) ->
      Printf.sprintf "observerFired(%d,%s)" f (show_observer o)
    | I.RunEvent_frame (f, h) -> Printf.sprintf "frame(%d,%s)" f (show_frame_event h)
    | I.RunEvent_finalizerProgram (f, _, x) ->
      Printf.sprintf "finalizerProgram(%d,<name>,%s)" f (show_exit x)
    | I.RunEvent_scopeLinked (m, a, b, f) ->
      Printf.sprintf "scopeLinked(%s,%d,%d,%d)" (show_scope_mode m) a b f
    | I.RunEvent_scopeClosedOnLink (k, f) ->
      Printf.sprintf "scopeClosedOnLink(%d,%d)" k f
    | I.RunEvent_raceStarted (r, f, n) -> Printf.sprintf "raceStarted(%d,%d,%d)" r f n
    | I.RunEvent_raceLaunched (r, f) -> Printf.sprintf "raceLaunched(%d,%d)" r f
    | I.RunEvent_raceSettled (r, x) ->
      Printf.sprintf "raceSettled(%d,%s)" r (show_exit x)
    | I.RunEvent_contextSet (f, c) -> Printf.sprintf "contextSet(%d,%s)" f (show_ctx c)
    | I.RunEvent_callback (n, x) -> Printf.sprintf "callback(%d,%s)" n (show_exit x)
    | I.RunEvent_exited (f, x) -> Printf.sprintf "exited(%d,%s)" f (show_exit x)

  let show_outcome (o : I.outcome) : string =
    match o with
    | I.Outcome_finished -> "finished"
    | I.Outcome_frontier -> "frontier"
    | I.Outcome_stuck s -> "stuck " ^ show_stuck s

  let show_fiber (f : I.fiber) : string =
    Printf.sprintf
      "id=%d run=%b park=%s exit=%s fin=%b pend=%s obs=[%s] kids=%s ops=%d/%d py=%b yo=%s \
       disp=%s armed=%b ctx=%s"
      (I.f_id f) (I.f_running f)
      (show_parked (I.f_parked f))
      (show_exit_opt (I.f_exit f))
      (I.f_finalizing f)
      (ids (I.f_pending_tokens f))
      (String.concat "," (List.map show_observer (I.f_observers f)))
      (ids (I.f_children f)) (I.f_op_count f) (I.f_max_ops f) (I.f_prevent_yield f)
      (match I.f_yield_override f with None -> "-" | Some b -> string_of_bool b)
      ("["
       ^ String.concat ","
           (List.map (fun (p, n) -> Printf.sprintf "%d:%d" p n) (I.f_dispatcher f))
       ^ "]")
      (I.f_dispatcher_armed f)
      (show_ctx (I.f_context f))

  (* -- the free rows -------------------------------------------------------------- *)

  let fuel (t : t) : int = t.fuel_
  let snapshot (t : t) : t = t

  let frontier_of (t : t) : frontier =
    { parked =
        List.filter_map
          (fun (id, f) ->
             match I.f_parked f with
             | I.Parked_notParked -> None
             | I.Parked_withGuard tok -> Some (id, tok))
          (I.fibers t.m);
      armed = I.armed_of t.m;
      due = I.due_count t.m }

  let answer (t : t) : answer =
    match I.stuck_of t.m with
    | Some s -> Refused (show_stuck s)
    | None ->
      if not t.settled then Delay (frontier_of t)
      else if I.finished t.m then Finished
      else Suspended (frontier_of t)

  (* Exactly `replayEval`'s verdict (api_engine.ml:11489-11507) read off the same state. *)
  let outcome (t : t) : string =
    match I.stuck_of t.m with
    | Some s -> "stuck " ^ show_stuck s
    | None -> if t.settled && I.finished t.m then "finished" else "frontier"

  let exits (t : t) : (int * string) list =
    List.map (fun (id, x) -> (id, show_exit x)) (I.completed_exits t.m)

  let root_exit (t : t) : string option =
    match List.assoc_opt 0 (I.fibers t.m) with
    | None -> None
    | Some f -> (match I.f_exit f with None -> None | Some x -> Some (show_exit x))

  let fiber_rows (t : t) : (int * string) list =
    List.map (fun (id, f) -> (id, show_fiber f)) (I.fibers t.m)

  let fiber_count (t : t) : int = I.fiber_count t.m
  let trace_rows (t : t) : string list = List.map show_event (I.trace t.m)
  let trace_length (t : t) : int = I.trace_length t.m
  let refs (t : t) : string list = List.map show_val (I.refs t.m)

  let store_row (t : t) : string =
    Printf.sprintf
      "refs=[%s] cells=%d scopes=%d memo=%d paths=%s nextName=%d due=%d nextId=%d \
       nextToken=%d races=%d mw=%b armed=%s"
      (String.concat "," (List.map show_val (I.refs t.m)))
      (I.cell_count t.m) (I.scope_count t.m) (I.memo_map_count t.m)
      ("["
       ^ String.concat ";"
           (List.map
              (fun (id, ps) ->
                 Printf.sprintf "%d:%s" id
                   (String.concat "|" (List.map ids ps)))
              (I.memo_paths t.m))
       ^ "]")
      (I.next_name t.m) (I.due_count t.m) (I.next_id t.m) (I.next_token t.m)
      (I.race_count t.m) (I.middleware t.m)
      (ids (I.armed_of t.m))

  let api_run (p : program) ~(fuel : int) : string =
    let o, _ = I.run_api p ~fuel ~choices:[] in
    show_outcome o
end

module Fast = Make (Api_engine_inst)
module Ref = Make (Api_engine_ref)
