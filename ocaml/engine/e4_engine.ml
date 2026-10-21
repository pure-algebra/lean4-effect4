(* E4_engine -- see e4_engine.mli.  The answer alphabet and the module types INSTANCE and
   ENGINE are e4_engine_intf.ml's, included here as e4_engine.mli includes its module type. *)

open Eff_types
include E4_engine_intf

(* The refusal as a report spells it. A below-bound reason names the negative integer's
   magnitude (`ProfileReason.belowBound`, M4). *)
let outside_text = function
  | Unsupported { Located.site; reason } ->
    let path = "[" ^ String.concat "," (List.map Z.to_string site) ^ "]" in
    (match reason with
     | ProfileReason.AboveBound n ->
       Printf.sprintf
         "the natural %s at %s is above the profile's bound"
         (Z.to_string n)
         path
     | ProfileReason.BelowBound n ->
       Printf.sprintf
         "the integer -%s at %s is below the profile's bound"
         (Z.to_string n)
         path)
  | Not_a_value ->
    "the answer is no Lean value (a natural below zero, or a string not UTF-8)"
  | Crossing why -> Lcnf_crossing.refusal_text why
;;

(* A machine natural the host reads as an int: a fiber id, a token, a row's position. Each
   counts what a run allocated, so it is below max_int; past it the narrowing refuses at the
   index crossing. *)
let host_int (n : Z.t) : int = Lcnf_nat.to_index_exn n
let show_nat = Z.to_string
let show_nats xs = "[" ^ String.concat "," (List.map show_nat xs) ^ "]"

(* ------------------------------------------------------------------------- the loop *)

module Make (I : INSTANCE) = struct
  let () =
    if Sys.int_size <> 63
    then Lcnf_crossing.refuse Lcnf_crossing.Index "a 63-bit integer host is required"
  ;;

  let name = I.name
  let carriers = I.carriers

  type program = I.program
  type decision = I.api_decision

  type t =
    { prepared : I.prepared
    ; fuel_ : int
    ; m : I.machine
    ; settled : bool (** the generated `settled` of the LAST step; true after a load *)
    ; outside_profile : Lcnf_crossing.refusal option
    }

  (* -- the tape ------------------------------------------------------------------- *)

  (* The tape's host ids are ints, each the machine's natural exactly (`Z.of_int`). *)
  let evaluate id : decision = I.RunDecision_evaluate (Z.of_int id)
  let flush : decision = I.RunDecision_flush
  let fire id : decision = I.RunDecision_fire (Z.of_int id)
  let yield_verdict id b : decision = I.RunDecision_yieldVerdict (Z.of_int id, b)

  let answer_async fiber token (answer : (Val.t, Err.t, Defect.t, Z.t, unit) Completion.t)
    : decision
    =
    I.RunDecision_answerAsync (Z.of_int fiber, Z.of_int token, answer)
  ;;

  let answer_async_success fiber token n : decision =
    answer_async fiber token (Completion.OfExit (Exit.Success (Val.Nat (Z.of_int n))))
  ;;

  let answer_async_value fiber token (v : Val.t) : decision =
    answer_async fiber token (Completion.OfExit (Exit.Success v))
  ;;

  let interrupt_from who target : decision =
    I.RunDecision_interruptFrom (Option.map Z.of_int who, [], Z.of_int target)
  ;;

  let install_middleware : decision = I.RunDecision_installMiddleware
  let advance_exact millis : decision = I.RunDecision_advance millis

  (* A duration is a natural: a negative host integer is no Lean value, and the clock would
     move backwards (the timer store's law), so it is refused before any decision exists. *)
  let advance millis : decision =
    if millis < 0
    then invalid_arg "E4_engine.advance: a negative duration"
    else advance_exact (Z.of_int millis)
  ;;

  (* -- ingress -------------------------------------------------------------------- *)

  (* The selected profile, as data: rc.112's (D3; EN8, EN9). *)
  let profile = I.program_rc112

  (* EN8: Lean's profile support of the program's literals, lowered. *)
  let literal_refusal (p : program) : profile_refusal option =
    I.program_profile_data_literal_refusal profile p
  ;;

  (* EN9: the answer's value tree, Lean's (`answerTree`), is a Lean value, and Lean's profile
     support admits it. *)
  let ingress (answer : (Val.t, Err.t, Defect.t, Z.t, unit) Completion.t) : outside option
    =
    let tree = I.program_answer_tree answer in
    if not (Eff_val.valid tree)
    then Some Not_a_value
    else
      Option.map
        (fun why -> Unsupported why)
        (I.program_profile_data_value_refusal profile tree)
  ;;

  (* -- loading -------------------------------------------------------------------- *)

  (* The program type is the instance's own (`Eff_types`, the LCNF route's), so nothing
     converts. *)
  let load_program ?(table = []) (p : program) ~(fuel : int) : t =
    { prepared = I.prepare table p
    ; fuel_ = fuel
    ; m = I.load p ~fuel:(Z.of_int fuel)
    ; settled = true
    ; outside_profile = None
    }
  ;;

  let of_bytes (b : string) : program option = Eff_codec.decode_program b
  let load ?table (p : program) ~(fuel : int) : t = load_program ?table p ~fuel
  let admits (t : t) (d : decision) : bool = I.admit t.prepared t.m d

  (* -- driving -------------------------------------------------------------------- *)

  let step (t : t) (d : decision) : t =
    match t.outside_profile with
    | Some _ -> t
    | None ->
      (match I.step t.prepared ~fuel:(Z.of_int t.fuel_) t.m d with
       | m, settled -> { t with m; settled }
       | exception Lcnf_crossing.Refused why ->
         (* Generated transitions are pure. Keep the input machine when a numeric
           observation leaves the host profile, including a refusal mid-decision.
           This is a host boundary result, not a simulated transition. *)
         { t with outside_profile = Some why })
  ;;

  (* `replayEval` STOPS consuming the tape (replayEval (src/Effect4/Machine/Fibers.lean), generated at
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
  let halted (t : t) : bool =
    Option.is_some t.outside_profile || Option.is_some (I.stuck_of t.m) || not t.settled
  ;;

  let step_or_hold (t : t) (d : decision) : t = if halted t then t else step t d

  (* The machine and the decisions the replay never read.  `[]` means the tape was spent; a
     non-empty residue means the replay STOPPED, and its head is the decision at the stop —
     the REFUSED one when the machine is stuck, since Lean answers `stuck why m` without
     applying it.  The position of the stop is `|tape| - |residue|`. *)
  let rec replay_to (t : t) (tape : decision list) : t * decision list =
    if halted t
    then t, tape
    else (
      match tape with
      | [] -> t, []
      | d :: rest ->
        let next = step t d in
        if Option.is_some next.outside_profile then next, tape else replay_to next rest)
  ;;

  let replay (t : t) (tape : decision list) : t = fst (replay_to t tape)

  (* TAPE positions: the machine after each PREFIX of the tape, |tape| + 1 of them.  It is
     total by construction — every position is `replay t (the first i decisions)` — and past
     the stop the machine is PHYSICALLY the halted one, which is how a caller tells the
     repetition from a run (`t == u`), and `replay_to` is how it finds where the run ended. *)
  let replay_steps (t : t) (tape : decision list) : t Seq.t =
    Seq.scan step_or_hold t (List.to_seq tape)
  ;;

  (* RUN positions: the machines the replay actually visits.  It ends where `replayEval` ends
     (replayEval (src/Effect4/Machine/Fibers.lean)) and repeats nothing, so `Seq.length` of it is the number of
     positions the run has.  Lane P6's finding F1 is exactly the difference between this and
     the sequence above: a 64-decision tape whose fuel runs out at the first decision has
     |tape| + 1 = 65 TAPE positions and 2 RUN positions. *)
  let replay_positions (t : t) (tape : decision list) : t Seq.t =
    let rec go (t : t) (tape : decision list) () =
      if halted t
      then Seq.Cons (t, Seq.empty)
      else (
        match tape with
        | [] -> Seq.Cons (t, Seq.empty)
        | d :: rest -> Seq.Cons (t, go (step t d) rest))
    in
    go t tape
  ;;

  let drive (t : t) : t = replay t [ I.api_evaluate; flush ]

  let run_program ?table (p : program) ~(fuel : int) : t =
    drive (load_program ?table p ~fuel)
  ;;

  let run ?table (p : program) ~(fuel : int) : t = run_program ?table p ~fuel

  (* -- the renderers -------------------------------------------------------------- *)

  let rec show_val (v : Eff_types.Val.t) : string =
    match v with
    | Eff_types.Val.Unit -> "unit"
    | Eff_types.Val.Bool b -> string_of_bool b
    | Eff_types.Val.Nat n -> show_nat n
    | Eff_types.Val.Str s -> Printf.sprintf "%S" s
    | Eff_types.Val.Bytes bs ->
      "bytes[" ^ String.concat "," (List.map string_of_int bs) ^ "]"
    | Eff_types.Val.List xs -> "list[" ^ String.concat "," (List.map show_val xs) ^ "]"
    | Eff_types.Val.Pair (a, b) -> "pair(" ^ show_val a ^ "," ^ show_val b ^ ")"
    | Eff_types.Val.None -> "none"
    | Eff_types.Val.Some x -> "some " ^ show_val x
    | Eff_types.Val.Ctor (i, args) ->
      Printf.sprintf
        "ctor %s [%s]"
        (show_nat i)
        (String.concat ", " (List.map show_val args))
    | Eff_types.Val.Ref (k, path) ->
      Printf.sprintf "ref %d/[%s]" k (String.concat "," (List.map string_of_int path))
    | Eff_types.Val.Handle (k, n) -> Printf.sprintf "handle %d/%s" k (show_nat n)
    (* the signed frame holds -(n+1); the binary64 frame its bits, a word below 2^64 *)
    | Eff_types.Val.NegInt n -> "-" ^ show_nat (Z.succ n)
    | Eff_types.Val.Float bits -> "float " ^ Z.format "%016x" bits
  ;;

  let show_err (e : Eff_types.Err.t) : string =
    match e with
    | Eff_types.Err.Boom -> "boom"
    | Eff_types.Err.Tag t -> "tag " ^ show_nat t
    | Eff_types.Err.Tagged (tag, msg) -> Printf.sprintf "tagged %s: %s" tag msg
    | Eff_types.Err.Text msg -> Printf.sprintf "text %s" msg
    | Eff_types.Err.Payload p -> "payload " ^ show_val p
  ;;

  let show_defect (d : Eff_types.Defect.t) : string =
    match d with
    | Eff_types.Defect.NotImplemented -> "notImplemented"
    | Eff_types.Defect.AsyncFiber -> "asyncFiber"
    | Eff_types.Defect.BadName -> "badName"
    | Eff_types.Defect.MissingService key ->
      (* the engine holds no key names: the key's two numbers, as its runtime text *)
      Printf.sprintf "missingService k%s_%s" (show_nat key.name) (show_nat key.service)
    | Eff_types.Defect.User n -> "user " ^ show_nat n
    | Eff_types.Defect.Error e -> "error(" ^ show_err e ^ ")"
  ;;

  let show_anns (a : unit Eff_types.ReasonAnnotations.t) : string =
    if List.is_empty a then "" else "{" ^ String.concat "," (List.map fst a) ^ "}"
  ;;

  let show_reason
        (r : (Eff_types.Err.t, Eff_types.Defect.t, I.fiber_id, unit) Eff_types.Reason.t)
    : string
    =
    match r with
    | Eff_types.Reason.Fail (e, a) -> "fail(" ^ show_err e ^ ")" ^ show_anns a
    | Eff_types.Reason.Die (d, a) -> "die(" ^ show_defect d ^ ")" ^ show_anns a
    | Eff_types.Reason.Interrupt (None, a) -> "interrupt(none)" ^ show_anns a
    | Eff_types.Reason.Interrupt (Some i, a) ->
      Printf.sprintf "interrupt(%s)%s" (show_nat i) (show_anns a)
  ;;

  let show_cause
        (c : (Eff_types.Err.t, Eff_types.Defect.t, I.fiber_id, unit) Eff_types.Cause.t)
    : string
    =
    "[" ^ String.concat "; " (List.map show_reason c) ^ "]"
  ;;

  let show_exit
        (x :
          ( Eff_types.Val.t
            , Eff_types.Err.t
            , Eff_types.Defect.t
            , I.fiber_id
            , unit )
            Eff_types.Exit.t)
    : string
    =
    match x with
    | Eff_types.Exit.Success v -> "success " ^ show_val v
    | Eff_types.Exit.Failure c -> "failure " ^ show_cause c
  ;;

  let show_exit_opt = function
    | None -> "-"
    | Some x -> show_exit x
  ;;

  let show_observer_mode (m : ObserverMode.t) : string =
    match m with
    | ObserverMode.AwaitValue -> "awaitValue"
    | ObserverMode.JoinEffect -> "joinEffect"
  ;;

  let show_observer (o : I.observer) : string =
    match o with
    | I.Observer_resumeAwait (f, t, m) ->
      Printf.sprintf
        "resumeAwait(%s,%s,%s)"
        (show_nat f)
        (show_nat t)
        (show_observer_mode m)
    | I.Observer_untrackChild f -> Printf.sprintf "untrackChild(%s)" (show_nat f)
    | I.Observer_dropScopeFinalizer (a, b) ->
      Printf.sprintf "dropScopeFinalizer(%s,%s)" (show_nat a) (show_nat b)
    | I.Observer_countdown (f, t) ->
      Printf.sprintf "countdown(%s,%s)" (show_nat f) (show_nat t)
    | I.Observer_raceCallback n -> Printf.sprintf "raceCallback(%s)" (show_nat n)
    | I.Observer_callback n -> Printf.sprintf "callback(%s)" (show_nat n)
  ;;

  let show_parked (p : I.parked) : string =
    match p with
    | I.Parked_notParked -> "-"
    | I.Parked_withGuard t -> "guard " ^ show_nat t
  ;;

  let show_stuck (s : I.stuck) : string =
    match s with
    | I.Stuck_unknownFiber f -> "unknownFiber " ^ show_nat f
    | I.Stuck_unknownScope k -> "unknownScope " ^ show_nat k
    | I.Stuck_unknownRace r -> "unknownRace " ^ show_nat r
  ;;

  let show_scope_mode (m : I.scope_mode) : string =
    match m with
    | I.ScopeMode_forkIn -> "forkIn"
    | I.ScopeMode_fiberRunIn -> "fiberRunIn"
  ;;

  let show_ctx (c : I.ctx) : string =
    Printf.sprintf
      "ctx(%s;%s;%b)"
      (String.concat
         ","
         (List.map
            (fun (sv : Eff_types.Val.t I.service) ->
               Printf.sprintf
                 "%s:%s=%s"
                 (show_nat sv.I.key.ServiceKey.name)
                 (show_nat sv.I.key.ServiceKey.service)
                 (show_val sv.I.value))
            c.I.services))
      (show_nat c.I.max_ops_before_yield)
      c.I.prevent_yield
  ;;

  (* `nu` (EffName) and `s` (EffThunk) are the two payloads this projection does not
     descend into -- see the header's note on the differential's reach. *)
  let rec show_prim
            (p :
              ( I.nu
                , I.s
                , Eff_types.Val.t
                , Eff_types.Err.t
                , Eff_types.Defect.t
                , I.fiber_id
                , unit )
                I.prim)
    : string
    =
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
    | I.Prim_yieldNowWith n -> Printf.sprintf "yieldNowWith(%s)" (show_nat n)
    | I.Prim_async (_, b, o) ->
      Printf.sprintf
        "async(<name>,%b,%s)"
        b
        (match o with
         | None -> "none"
         | Some _ -> "some")
    | I.Prim_asyncFinalizer _ -> "asyncFinalizer(<name>)"
  ;;

  let show_frame_event
        (e :
          ( I.nu
            , I.s
            , Eff_types.Val.t
            , Eff_types.Err.t
            , Eff_types.Defect.t
            , I.fiber_id
            , unit )
            I.frame_event)
    : string
    =
    match e with
    | I.FrameEvent_popped p -> "popped(" ^ show_prim p ^ ")"
    | I.FrameEvent_ranContAll p -> "ranContAll(" ^ show_prim p ^ ")"
    | I.FrameEvent_pushed p -> "pushed(" ^ show_prim p ^ ")"
    | I.FrameEvent_ranFinalizer (_, x) -> "ranFinalizer(<name>," ^ show_exit x ^ ")"
    | I.FrameEvent_substituted c -> "substituted " ^ show_cause c
    | I.FrameEvent_deferred c -> "deferred " ^ show_cause c
    | I.FrameEvent_yielded x -> "yielded(" ^ show_exit x ^ ")"
  ;;

  let show_task
        (t :
          ( I.nu
            , I.s
            , Eff_types.Val.t
            , Eff_types.Err.t
            , Eff_types.Defect.t
            , I.fiber_id
            , unit
            , ( I.nu
                , I.s
                , Eff_types.Val.t
                , Eff_types.Err.t
                , Eff_types.Defect.t
                , I.fiber_id
                , unit )
                I.prim )
            I.task)
    : string
    =
    match t with
    | I.Task_start f -> Printf.sprintf "start(%s)" (show_nat f)
    | I.Task_resume (f, tok, k) ->
      Printf.sprintf "resume(%s,%s,%s)" (show_nat f) (show_nat tok) (show_prim k)
    | I.Task_wake (key, due) ->
      Printf.sprintf "wake(%s,%s)" (show_nat key.index) (show_nat due)
  ;;

  let ids = show_nats

  let show_event (e : I.event) : string =
    match e with
    | I.RunEvent_forked (p, c, d) ->
      Printf.sprintf "forked(%s,%s,%b)" (show_nat p) (show_nat c) d
    | I.RunEvent_started f -> Printf.sprintf "started(%s)" (show_nat f)
    | I.RunEvent_scheduledTask (f, pr, t) ->
      Printf.sprintf "scheduledTask(%s,%s,%s)" (show_nat f) (show_nat pr) (show_task t)
    | I.RunEvent_ranTask (f, t) ->
      Printf.sprintf "ranTask(%s,%s)" (show_nat f) (show_task t)
    | I.RunEvent_yieldInjected (f, n) ->
      Printf.sprintf "yieldInjected(%s,%s)" (show_nat f) (show_nat n)
    | I.RunEvent_parkedOn (f, tok) ->
      Printf.sprintf "parkedOn(%s,%s)" (show_nat f) (show_nat tok)
    | I.RunEvent_resumedWith (f, tok, k) ->
      Printf.sprintf "resumedWith(%s,%s,%s)" (show_nat f) (show_nat tok) (show_prim k)
    | I.RunEvent_interruptRecorded (who, target) ->
      Printf.sprintf
        "interruptRecorded(%s,%s)"
        (match who with
         | None -> "-"
         | Some i -> show_nat i)
        (show_nat target)
    | I.RunEvent_interruptDeferred f ->
      Printf.sprintf "interruptDeferred(%s)" (show_nat f)
    | I.RunEvent_childrenInterrupted (f, cs) ->
      Printf.sprintf "childrenInterrupted(%s,%s)" (show_nat f) (ids cs)
    | I.RunEvent_observerFired (f, o) ->
      Printf.sprintf "observerFired(%s,%s)" (show_nat f) (show_observer o)
    | I.RunEvent_frame (f, h) ->
      Printf.sprintf "frame(%s,%s)" (show_nat f) (show_frame_event h)
    | I.RunEvent_finalizerProgram (f, _, x) ->
      Printf.sprintf "finalizerProgram(%s,<name>,%s)" (show_nat f) (show_exit x)
    | I.RunEvent_scopeLinked (m, a, b, f) ->
      Printf.sprintf
        "scopeLinked(%s,%s,%s,%s)"
        (show_scope_mode m)
        (show_nat a)
        (show_nat b)
        (show_nat f)
    | I.RunEvent_scopeClosedOnLink (k, f) ->
      Printf.sprintf "scopeClosedOnLink(%s,%s)" (show_nat k) (show_nat f)
    | I.RunEvent_raceStarted (r, f, n) ->
      Printf.sprintf "raceStarted(%s,%s,%s)" (show_nat r) (show_nat f) (show_nat n)
    | I.RunEvent_raceLaunched (r, f) ->
      Printf.sprintf "raceLaunched(%s,%s)" (show_nat r) (show_nat f)
    | I.RunEvent_raceSettled (r, x) ->
      Printf.sprintf "raceSettled(%s,%s)" (show_nat r) (show_exit x)
    | I.RunEvent_contextSet (f, c) ->
      Printf.sprintf "contextSet(%s,%s)" (show_nat f) (show_ctx c)
    | I.RunEvent_callback (n, x) ->
      Printf.sprintf "callback(%s,%s)" (show_nat n) (show_exit x)
    | I.RunEvent_exited (f, x) ->
      Printf.sprintf "exited(%s,%s)" (show_nat f) (show_exit x)
  ;;

  let show_outcome (o : I.outcome) : string =
    match o with
    | I.Outcome_finished -> "finished"
    | I.Outcome_frontier -> "frontier"
    | I.Outcome_stuck s -> "stuck " ^ show_stuck s
  ;;

  let show_fiber (f : I.fiber) : string =
    Printf.sprintf
      "id=%s run=%b park=%s exit=%s fin=%b pend=%s obs=[%s] kids=%s ops=%s/%s py=%b \
       yo=%s disp=%s armed=%b ctx=%s"
      (show_nat (I.f_id f))
      (I.f_running f)
      (show_parked (I.f_parked f))
      (show_exit_opt (I.f_exit f))
      (I.f_finalizing f)
      (ids (I.f_pending_tokens f))
      (String.concat "," (List.map show_observer (I.f_observers f)))
      (ids (I.f_children f))
      (show_nat (I.f_op_count f))
      (show_nat (I.f_max_ops f))
      (I.f_prevent_yield f)
      (match I.f_yield_override f with
       | None -> "-"
       | Some b -> string_of_bool b)
      ("["
       ^ String.concat
           ","
           (List.map
              (fun (p, n) -> Printf.sprintf "%s:%d" (show_nat p) n)
              (I.f_dispatcher f))
       ^ "]")
      (not (List.is_empty (I.f_dispatcher f)))
      (show_ctx (I.f_context f))
  ;;

  (* -- the free rows -------------------------------------------------------------- *)

  let fuel (t : t) : int = t.fuel_
  let snapshot (t : t) : t = t

  let frontier_of (t : t) : frontier =
    { parked =
        List.filter_map
          (fun (id, f) ->
             match I.f_parked f with
             | I.Parked_notParked -> None
             | I.Parked_withGuard tok -> Some (host_int id, host_int tok))
          (I.fibers t.m)
    ; armed = List.map host_int (I.armed_of t.m)
    ; due = I.due_count t.m
    }
  ;;

  let answer (t : t) : answer =
    match t.outside_profile with
    | Some why -> Outside_profile why
    | None ->
      (match I.stuck_of t.m with
       | Some s -> Refused (show_stuck s)
       | None ->
         if not t.settled
         then Delay (frontier_of t)
         else if I.finished t.m
         then Finished
         else Suspended (frontier_of t))
  ;;

  (* Exactly `replayEval`'s verdict (api_engine.ml:11489-11507) read off the same state. *)
  let outcome (t : t) : string =
    match t.outside_profile with
    | Some why -> "outside-profile " ^ Lcnf_crossing.refusal_text why
    | None ->
      (match I.stuck_of t.m with
       | Some s -> "stuck " ^ show_stuck s
       | None -> if t.settled && I.finished t.m then "finished" else "frontier")
  ;;

  let exits (t : t) : (int * string) list =
    List.map (fun (id, x) -> host_int id, show_exit x) (I.completed_exits t.m)
  ;;

  let host_calls (t : t) : (int * int * int * Val.t) list =
    List.filter_map
      (fun (a : I.await) ->
         match a.op with
         | NativeOp.External row ->
           Some (host_int a.fiber, host_int a.token, host_int row, a.request)
         | _ -> None)
      (I.program_awaits t.m)
  ;;

  (* The root fiber, id 0. *)
  let root_fiber (t : t) : I.fiber option =
    List.find_map
      (fun (id, f) -> if Z.equal id Z.zero then Some f else None)
      (I.fibers t.m)
  ;;

  let root_exit_of (t : t) : (Val.t, Err.t, Defect.t, Z.t, unit) Exit.t option =
    match root_fiber t with
    | None -> None
    | Some f -> I.f_exit f
  ;;

  let root_exit (t : t) : string option =
    match root_fiber t with
    | None -> None
    | Some f ->
      (match I.f_exit f with
       | None -> None
       | Some x -> Some (show_exit x))
  ;;

  let fiber_rows (t : t) : (int * string) list =
    List.map (fun (id, f) -> host_int id, show_fiber f) (I.fibers t.m)
  ;;

  let fiber_count (t : t) : int = I.fiber_count t.m
  let trace_rows (t : t) : string list = List.map show_event (I.trace t.m)
  let trace_length (t : t) : int = I.trace_length t.m
  let refs (t : t) : string list = List.map show_val (I.refs t.m)

  let store_row (t : t) : string =
    Printf.sprintf
      "refs=[%s] cells=%d scopes=%d memo=%d paths=%s nextName=%s due=%d nextId=%s \
       nextToken=%s races=%d mw=%b armed=%s"
      (String.concat "," (List.map show_val (I.refs t.m)))
      (I.cell_count t.m)
      (I.scope_count t.m)
      (I.memo_map_count t.m)
      ("["
       ^ String.concat
           ";"
           (List.map
              (fun (id, ps) ->
                 Printf.sprintf
                   "%s:%s"
                   (show_nat id)
                   (String.concat
                      "|"
                      (List.map
                         (fun (p, c) ->
                            ids p
                            ^
                            match c with
                            | [] -> ""
                            | _ -> "@" ^ String.concat "/" (List.map ids c))
                         ps)))
              (I.memo_paths t.m))
       ^ "]")
      (show_nat (I.next_name t.m))
      (I.due_count t.m)
      (show_nat (I.next_id t.m))
      (show_nat (I.next_token t.m))
      (I.race_count t.m)
      (I.middleware t.m)
      (ids (I.armed_of t.m))
  ;;

  let api_run ?(table = []) (p : program) ~(fuel : int) : string =
    let o, _ = I.run_api table p ~fuel:(Z.of_int fuel) in
    show_outcome o
  ;;
end

module Fast = Make (Api_engine_inst)
