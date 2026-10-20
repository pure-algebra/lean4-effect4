(* E4_engine -- see e4_engine.mli.  The answer alphabet and the module types INSTANCE and
   ENGINE are e4_engine_intf.ml's, included here as e4_engine.mli includes its module type. *)

open Eff_types
include E4_engine_intf

(* The refusal as a report spells it. *)
let outside_text = function
  | Unsupported { Located.site; reason } ->
    let path = "[" ^ String.concat "," (List.map string_of_int site) ^ "]" in
    (match reason with
     | ProfileReason.AboveBound n ->
       Printf.sprintf "the natural %d at %s is above the profile's bound" n path
     | ProfileReason.BelowBound n ->
       Printf.sprintf "the integer -(%d+1) at %s is below the profile's bound" n path)
  | Not_a_value ->
    "the answer is no Lean value (a natural below zero, or a string not UTF-8)"
  | Crossing why -> E4_clock.refusal_text why
;;

(* ------------------------------------------------------------------------- the loop *)

module Make (I : INSTANCE) = struct
  let () =
    if Sys.int_size <> 63
    then E4_clock.refuse E4_clock.Index "a 63-bit integer host is required"
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
    ; outside_profile : E4_clock.refusal option
    }

  (* -- the tape ------------------------------------------------------------------- *)

  let evaluate id : decision = I.RunDecision_evaluate id
  let flush : decision = I.RunDecision_flush
  let fire id : decision = I.RunDecision_fire id
  let yield_verdict id b : decision = I.RunDecision_yieldVerdict (id, b)

  let answer_async fiber token (answer : (Val.t, Err.t, Defect.t, int, unit) Completion.t)
    : decision
    =
    I.RunDecision_answerAsync (fiber, token, answer)
  ;;

  let answer_async_success fiber token n : decision =
    answer_async fiber token (Completion.OfExit (Exit.Success (Val.Nat n)))
  ;;

  let answer_async_value fiber token (v : Val.t) : decision =
    answer_async fiber token (Completion.OfExit (Exit.Success v))
  ;;

  let interrupt_from who target : decision = I.RunDecision_interruptFrom (who, [], target)
  let install_middleware : decision = I.RunDecision_installMiddleware
  let advance_exact millis : decision = I.RunDecision_advance millis
  let advance millis : decision = advance_exact (E4_clock.of_nat millis)

  (* -- ingress -------------------------------------------------------------------- *)

  (* The selected profile, as data: rc.112's (D3; EN8, EN9). *)
  let profile = I.program_rc112

  (* EN8: Lean's profile support of the program's literals, lowered. *)
  let literal_refusal (p : Eff_wire.program) : profile_refusal option =
    I.program_profile_data_literal_refusal profile p
  ;;

  (* EN9: the answer's value tree, Lean's (`answerTree`), is a Lean value, and Lean's profile
     support admits it. *)
  let ingress (answer : (Val.t, Err.t, Defect.t, int, unit) Completion.t) : outside option
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
    ; m = I.load p ~fuel
    ; settled = true
    ; outside_profile = None
    }
  ;;

  let of_bytes (b : string) : program option = Eff_wire.decode_program_exact b
  let load ?table (p : Eff_wire.program) ~(fuel : int) : t = load_program ?table p ~fuel
  let admits (t : t) (d : decision) : bool = I.admit t.prepared t.m d

  (* -- driving -------------------------------------------------------------------- *)

  let step (t : t) (d : decision) : t =
    match t.outside_profile with
    | Some _ -> t
    | None ->
      (match I.step t.prepared ~fuel:t.fuel_ t.m d with
       | m, settled -> { t with m; settled }
       | exception E4_clock.Profile_refusal why ->
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

  let run ?table (p : Eff_wire.program) ~(fuel : int) : t = run_program ?table p ~fuel

  (* -- the renderers -------------------------------------------------------------- *)

  let rec show_val (v : Eff_types.Val.t) : string =
    match v with
    | Eff_types.Val.Unit -> "unit"
    | Eff_types.Val.Bool b -> string_of_bool b
    | Eff_types.Val.Nat n -> string_of_int n
    | Eff_types.Val.Str s -> Printf.sprintf "%S" s
    | Eff_types.Val.Bytes bs ->
      "bytes[" ^ String.concat "," (List.map string_of_int bs) ^ "]"
    | Eff_types.Val.List xs -> "list[" ^ String.concat "," (List.map show_val xs) ^ "]"
    | Eff_types.Val.Pair (a, b) -> "pair(" ^ show_val a ^ "," ^ show_val b ^ ")"
    | Eff_types.Val.None -> "none"
    | Eff_types.Val.Some x -> "some " ^ show_val x
    | Eff_types.Val.Ctor (i, args) ->
      Printf.sprintf "ctor %d [%s]" i (String.concat ", " (List.map show_val args))
    | Eff_types.Val.Ref (k, path) ->
      Printf.sprintf "ref %d/[%s]" k (String.concat "," (List.map string_of_int path))
    | Eff_types.Val.Handle (k, n) -> Printf.sprintf "handle %d/%d" k n
    (* the signed frame holds -(n+1); the binary64 frame its bits (below 2^62: the carrier) *)
    | Eff_types.Val.NegInt n -> "-" ^ string_of_int (n + 1)
    | Eff_types.Val.Float bits -> Printf.sprintf "float %016x" bits
  ;;

  let show_err (e : Eff_types.Err.t) : string =
    match e with
    | Eff_types.Err.Boom -> "boom"
    | Eff_types.Err.Tag t -> Printf.sprintf "tag %d" t
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
      Printf.sprintf "missingService k%d_%d" key.name key.service
    | Eff_types.Defect.User n -> Printf.sprintf "user %d" n
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
      Printf.sprintf "interrupt(%d)%s" i (show_anns a)
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
      Printf.sprintf "resumeAwait(%d,%d,%s)" f t (show_observer_mode m)
    | I.Observer_untrackChild f -> Printf.sprintf "untrackChild(%d)" f
    | I.Observer_dropScopeFinalizer (a, b) ->
      Printf.sprintf "dropScopeFinalizer(%d,%d)" a b
    | I.Observer_countdown (f, t) -> Printf.sprintf "countdown(%d,%d)" f t
    | I.Observer_raceCallback n -> Printf.sprintf "raceCallback(%d)" n
    | I.Observer_callback n -> Printf.sprintf "callback(%d)" n
  ;;

  let show_parked (p : I.parked) : string =
    match p with
    | I.Parked_notParked -> "-"
    | I.Parked_withGuard t -> Printf.sprintf "guard %d" t
  ;;

  let show_stuck (s : I.stuck) : string =
    match s with
    | I.Stuck_unknownFiber f -> Printf.sprintf "unknownFiber %d" f
    | I.Stuck_unknownScope k -> Printf.sprintf "unknownScope %d" k
    | I.Stuck_unknownRace r -> Printf.sprintf "unknownRace %d" r
  ;;

  let show_scope_mode (m : I.scope_mode) : string =
    match m with
    | I.ScopeMode_forkIn -> "forkIn"
    | I.ScopeMode_fiberRunIn -> "fiberRunIn"
  ;;

  let show_ctx (c : I.ctx) : string =
    Printf.sprintf
      "ctx(%s;%d;%b)"
      (String.concat
         ","
         (List.map
            (fun (sv : Eff_types.Val.t I.service) ->
               Printf.sprintf
                 "%d:%d=%s"
                 sv.I.key.ServiceKey.name
                 sv.I.key.ServiceKey.service
                 (show_val sv.I.value))
            c.I.services))
      c.I.max_ops_before_yield
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
    | I.Prim_yieldNowWith n -> Printf.sprintf "yieldNowWith(%d)" n
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
    | I.Task_start f -> Printf.sprintf "start(%d)" f
    | I.Task_resume (f, tok, k) -> Printf.sprintf "resume(%d,%d,%s)" f tok (show_prim k)
    | I.Task_wake (key, due) -> Printf.sprintf "wake(%d,%d)" key.index due
  ;;

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
      Printf.sprintf
        "interruptRecorded(%s,%d)"
        (match who with
         | None -> "-"
         | Some i -> string_of_int i)
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
    | I.RunEvent_scopeClosedOnLink (k, f) -> Printf.sprintf "scopeClosedOnLink(%d,%d)" k f
    | I.RunEvent_raceStarted (r, f, n) -> Printf.sprintf "raceStarted(%d,%d,%d)" r f n
    | I.RunEvent_raceLaunched (r, f) -> Printf.sprintf "raceLaunched(%d,%d)" r f
    | I.RunEvent_raceSettled (r, x) -> Printf.sprintf "raceSettled(%d,%s)" r (show_exit x)
    | I.RunEvent_contextSet (f, c) -> Printf.sprintf "contextSet(%d,%s)" f (show_ctx c)
    | I.RunEvent_callback (n, x) -> Printf.sprintf "callback(%d,%s)" n (show_exit x)
    | I.RunEvent_exited (f, x) -> Printf.sprintf "exited(%d,%s)" f (show_exit x)
  ;;

  let show_outcome (o : I.outcome) : string =
    match o with
    | I.Outcome_finished -> "finished"
    | I.Outcome_frontier -> "frontier"
    | I.Outcome_stuck s -> "stuck " ^ show_stuck s
  ;;

  let show_fiber (f : I.fiber) : string =
    Printf.sprintf
      "id=%d run=%b park=%s exit=%s fin=%b pend=%s obs=[%s] kids=%s ops=%d/%d py=%b \
       yo=%s disp=%s armed=%b ctx=%s"
      (I.f_id f)
      (I.f_running f)
      (show_parked (I.f_parked f))
      (show_exit_opt (I.f_exit f))
      (I.f_finalizing f)
      (ids (I.f_pending_tokens f))
      (String.concat "," (List.map show_observer (I.f_observers f)))
      (ids (I.f_children f))
      (I.f_op_count f)
      (I.f_max_ops f)
      (I.f_prevent_yield f)
      (match I.f_yield_override f with
       | None -> "-"
       | Some b -> string_of_bool b)
      ("["
       ^ String.concat
           ","
           (List.map (fun (p, n) -> Printf.sprintf "%d:%d" p n) (I.f_dispatcher f))
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
             | I.Parked_withGuard tok -> Some (id, tok))
          (I.fibers t.m)
    ; armed = I.armed_of t.m
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
    | Some why -> "outside-profile " ^ E4_clock.refusal_text why
    | None ->
      (match I.stuck_of t.m with
       | Some s -> "stuck " ^ show_stuck s
       | None -> if t.settled && I.finished t.m then "finished" else "frontier")
  ;;

  let exits (t : t) : (int * string) list =
    List.map (fun (id, x) -> id, show_exit x) (I.completed_exits t.m)
  ;;

  let host_calls (t : t) : (int * int * int * Val.t) list =
    List.filter_map
      (fun (a : I.await) ->
         match a.op with
         | NativeOp.External row -> Some (a.fiber, a.token, row, a.request)
         | _ -> None)
      (I.program_awaits t.m)
  ;;

  let root_exit_of (t : t) : (Val.t, Err.t, Defect.t, int, unit) Exit.t option =
    match List.assoc_opt 0 (I.fibers t.m) with
    | None -> None
    | Some f -> I.f_exit f
  ;;

  let root_exit (t : t) : string option =
    match List.assoc_opt 0 (I.fibers t.m) with
    | None -> None
    | Some f ->
      (match I.f_exit f with
       | None -> None
       | Some x -> Some (show_exit x))
  ;;

  let fiber_rows (t : t) : (int * string) list =
    List.map (fun (id, f) -> id, show_fiber f) (I.fibers t.m)
  ;;

  let fiber_count (t : t) : int = I.fiber_count t.m
  let trace_rows (t : t) : string list = List.map show_event (I.trace t.m)
  let trace_length (t : t) : int = I.trace_length t.m
  let refs (t : t) : string list = List.map show_val (I.refs t.m)

  let store_row (t : t) : string =
    Printf.sprintf
      "refs=[%s] cells=%d scopes=%d memo=%d paths=%s nextName=%d due=%d nextId=%d \
       nextToken=%d races=%d mw=%b armed=%s"
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
                   "%d:%s"
                   id
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
      (I.next_name t.m)
      (I.due_count t.m)
      (I.next_id t.m)
      (I.next_token t.m)
      (I.race_count t.m)
      (I.middleware t.m)
      (ids (I.armed_of t.m))
  ;;

  let api_run ?(table = []) (p : program) ~(fuel : int) : string =
    let o, _ = I.run_api table p ~fuel in
    show_outcome o
  ;;
end

module Fast = Make (Api_engine_inst)
