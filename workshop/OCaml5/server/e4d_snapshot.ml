(* `RunMachine` as JSON: every field of every carrier the avatar transcribes, under the Lean
   name.

   This is the serialiser the `step`, `reachable` and `budget` answers are built from. It
   reads the records `deep_fibers.ml` declares -- nothing is re-derived and nothing is
   copied, so a field seat W1 adds to a carrier is a field this module fails to compile
   against rather than one it silently omits.

   Where a value has a wire form (`avatar_trace.ml`), the JSON carries both: `wire` is the
   string the TSV row would show, and the sibling fields are the structure. *)

open Deep_fibers
open E4d_json

let rec json_of_value (v : value) : E4d_json.t =
  match v with
  | Vunit -> Obj [ ("tag", Str "unit") ]
  | Vnat n -> Obj [ ("tag", Str "nat"); ("value", Int n) ]
  | Vbool b -> Obj [ ("tag", Str "bool"); ("value", Bool b) ]
  | Vstring s -> Obj [ ("tag", Str "string"); ("value", Str s) ]
  | Vhandle h -> Obj [ ("tag", Str "handle"); ("index", Int h) ]
  | Vpair (a, b) -> Obj [ ("tag", Str "pair"); ("fst", json_of_value a); ("snd", json_of_value b) ]
  | Vnone -> Obj [ ("tag", Str "none") ]
  | Vsome v -> Obj [ ("tag", Str "some"); ("value", json_of_value v) ]
  | Vlist xs -> Obj [ ("tag", Str "list"); ("items", List (List.map json_of_value xs)) ]

let value_json (v : value) : E4d_json.t =
  Obj [ ("wire", Str (Avatar_trace.wire v)); ("value", json_of_value v) ]

let json_of_reason (r : reason) : E4d_json.t =
  match r with
  | Rfail e -> Obj [ ("tag", Str "fail"); ("error", Int e) ]
  | Rdie d -> Obj [ ("tag", Str "die"); ("defect", Str d) ]
  | Rinterrupt who ->
    Obj [ ("tag", Str "interrupt");
          ("by", match who with Some f -> Int f | None -> Null) ]

let json_of_cause (c : cause) : E4d_json.t =
  Obj
    [ ("reasons", List (List.map json_of_reason c.reasons));
      ("annotations", of_strings c.annotations);
      ("hasInterrupt", Bool (cause_has_interrupt c));
      ("failure", match cause_fail_of c with Some e -> Int e | None -> Null) ]

let json_of_exit (e : exitv) : E4d_json.t =
  Obj
    ([ ("wire", Str (Avatar_trace.wire_exit e)) ]
    @
    match e with
    | Esuccess v -> [ ("tag", Str "success"); ("value", json_of_value v) ]
    | Efailure c -> [ ("tag", Str "failure"); ("cause", json_of_cause c) ])

let exit_opt = function Some e -> json_of_exit e | None -> Null

let json_of_answer (a : answer) : E4d_json.t =
  match a with
  | Aval v -> Obj [ ("tag", Str "value"); ("value", json_of_value v) ]
  | Acause c -> Obj [ ("tag", Str "cause"); ("cause", json_of_cause c) ]

let json_of_task (t : task) : E4d_json.t =
  Obj
    ([ ("render", Str (Avatar_trace.render_task t)) ]
    @
    match t with
    | Tstart c -> [ ("tag", Str "start"); ("child", Int c) ]
    | Tresume (f, tok, a) ->
      [ ("tag", Str "resume"); ("fiber", Int f); ("token", Int tok); ("answer", json_of_answer a) ])

let json_of_observer (o : observer) : E4d_json.t =
  Obj
    ([ ("render", Str (Avatar_trace.render_observer o)) ]
    @
    match o with
    | ResumeAwait (w, t, m) ->
      [ ("tag", Str "resumeAwait"); ("waiter", Int w); ("token", Int t);
        ("mode", Str (match m with MJoin -> "join" | MAwait -> "await")) ]
    | UntrackChild p -> [ ("tag", Str "untrackChild"); ("parent", Int p) ]
    | DropScopeFinalizer (s, k) ->
      [ ("tag", Str "dropScopeFinalizer"); ("scope", Int s); ("key", Int k) ]
    | Countdown (w, t) -> [ ("tag", Str "countdown"); ("waiter", Int w); ("token", Int t) ]
    | RaceCallback r -> [ ("tag", Str "raceCallback"); ("race", Int r) ]
    | Callback k -> [ ("tag", Str "callback"); ("key", Int k) ])

let json_of_pending (p : pending) : E4d_json.t =
  Obj
    [ ("token", Int p.token);
      ("waitingOn", match p.waiting_on with Some t -> Int t | None -> Null);
      ("remaining", Int p.remaining);
      ("collected", List (List.map json_of_exit p.collected));
      ( "resumeWith",
        Str
          (match p.resume_with with
           | RexitsValue -> "exitsValue"
           | Rvoid -> "void"
           | RcontinueWith _ -> "continueWith") );
      ( "resumeWithExit",
        match p.resume_with with RcontinueWith e -> json_of_exit e | _ -> Null ) ]

let json_of_dispatcher (d : dispatcher) : E4d_json.t =
  Obj
    [ ("armed", Bool d.armed);
      ( "buckets",
        List
          (List.map
             (fun b ->
               Obj [ ("priority", Int b.priority); ("tasks", List (List.map json_of_task b.tasks)) ])
             d.buckets) );
      ("taskCount", Int (List.fold_left (fun n b -> n + List.length b.tasks) 0 d.buckets)) ]

(* `control` is DIVERGENCE 1: `FrameFiber.current` and `.stack` are the OCaml stack, so the
   snapshot reports the constructor and, for a suspended fiber, the token its captured
   one-shot continuation answers to. There is no way to show the stack itself. *)
let json_of_control (c : control) : E4d_json.t =
  match c with
  | Program _ -> Obj [ ("tag", Str "program"); ("note", Str "unstarted: current = the whole body, stack = []") ]
  | Onstack -> Obj [ ("tag", Str "onstack"); ("note", Str "this fiber is the one running") ]
  | Suspended k -> Obj [ ("tag", Str "suspended"); ("token", Int k.ktoken) ]
  | Failing c -> Obj [ ("tag", Str "failing"); ("cause", json_of_cause c) ]
  | Ended -> Obj [ ("tag", Str "ended") ]

let status_name (s : fiber_status) : string =
  match s with
  | Sdone -> "done"
  | Sfinalizing -> "finalizing"
  | Srunning -> "running"
  | Swaiting t -> Printf.sprintf "waiting(%d)" t
  | Srunnable -> "runnable"

let json_of_frame (f : frame_fiber) : E4d_json.t =
  Obj
    [ ("control", json_of_control f.control);
      ("interruptible", Bool f.interruptible);
      ("interruptedCause", match f.interrupted_cause with Some c -> json_of_cause c | None -> Null);
      ("deferredInterrupt", Bool f.deferred_interrupt) ]

let json_of_fiber (f : run_fiber) : E4d_json.t =
  Obj
    [ ("id", Int f.id);
      ("status", Str (status_name (run_fiber_status f)));
      ("frame", json_of_frame f.frame);
      ("running", Bool f.running);
      ("parked", match f.parked with NotParked -> Null | WithGuard t -> Int t);
      ("pending", List (List.map json_of_pending f.pending));
      ("finalizing", exit_opt f.finalizing);
      ("exit", exit_opt f.exit_);
      ("currentOpCount", Int f.current_op_count);
      ( "maxOpsBeforeYield",
        if f.max_ops_before_yield = max_int then Null else Int f.max_ops_before_yield );
      ("preventYield", Bool f.prevent_yield);
      ("yieldOverride", match f.yield_override with Some b -> Bool b | None -> Null);
      ("yielding", Bool f.yielding);
      ("raceAnswerHeld", Bool (f.race_answer <> None));
      ("observers", List (List.map json_of_observer f.observers));
      ("children", of_ints f.children);
      ("dispatcher", json_of_dispatcher f.dispatcher) ]

let json_of_race (r : race) : E4d_json.t =
  Obj
    [ ("id", Int r.rid);
      ("host", Int r.host);
      ("token", Int r.rtoken);
      ("settled", Bool r.settled);
      ("live", of_ints r.live);
      ("unstarted", of_ints r.unstarted);
      ("remaining", Int r.remaining);
      ("failures", List (List.map json_of_reason r.failures));
      ("accepted", exit_opt r.accepted);
      ("cleanupNeeded", Bool r.cleanup_needed) ]

let json_of_stuck (s : stuck option) : E4d_json.t =
  match s with
  | None -> Null
  | Some (UnknownFiber f) -> Obj [ ("tag", Str "unknownFiber"); ("fiber", Int f) ]
  | Some (UnknownScope s) -> Obj [ ("tag", Str "unknownScope"); ("scope", Int s) ]

(* The service state: the three stores of `Effect4/Deep/Stores.lean` and the Layer memo
   world, which seat W1's port moved out of `deep_fibers.ml` into `deep_stores.ml` and
   `deep_layer.ml`. `Deep_fibers.st` is what the fixture itself owns -- the two lists the
   fiber bodies append to -- and nothing else. *)
let json_of_scope_state (s : Deep_stores.scope_state) : E4d_json.t =
  match s with
  | Deep_stores.Ssempty -> Obj [ ("tag", Str "empty") ]
  | Deep_stores.SsopenEmpty -> Obj [ ("tag", Str "openEmpty") ]
  | Deep_stores.SsopenInline (key, _) ->
    Obj [ ("tag", Str "openInline"); ("keys", of_ints [ key ]) ]
  | Deep_stores.SsopenMap table ->
    Obj [ ("tag", Str "openMap"); ("keys", of_ints (List.map fst table)) ]
  | Deep_stores.Ssclosed exit_ -> Obj [ ("tag", Str "closed"); ("exit", json_of_exit exit_) ]

let json_of_completion (c : Deep_stores.completion) : E4d_json.t =
  match c with
  | Deep_stores.CoofExit e -> Obj [ ("tag", Str "exit"); ("exit", json_of_exit e) ]
  | Deep_stores.CoofRefGet key ->
    Obj [ ("tag", Str "refGet"); ("ref", Int key.Deep_stores.index) ]

let json_of_stores (st : Deep_stores.stores) : E4d_json.t =
  Obj
    [ ( "refs",
        List
          (List.mapi
             (fun i v -> Obj [ ("index", Int i); ("cell", json_of_value v) ])
             st.Deep_stores.refs) );
      ( "deferreds",
        List
          (List.mapi
             (fun i (c : Deep_stores.deferred_cell) ->
               Obj
                 [ ("index", Int i);
                   ( "completion",
                     match c.Deep_stores.completion with
                     | Some x -> json_of_completion x
                     | None -> Null );
                   ( "waiters",
                     List
                       (List.map
                          (fun (fid, tok) -> Obj [ ("fiber", Int fid); ("token", Int tok) ])
                          c.Deep_stores.waiters) ) ])
             st.Deep_stores.deferreds.Deep_stores.cells) );
      ( "dueResumes",
        List
          (List.map
             (fun (fid, tok, a) ->
               Obj [ ("fiber", Int fid); ("token", Int tok); ("answer", json_of_answer a) ])
             st.Deep_stores.deferreds.Deep_stores.due) );
      ( "scopes",
        List
          (List.map
             (fun (e : Deep_stores.scope_entry) ->
               Obj
                 [ ("key", Int e.Deep_stores.key);
                   ("state", json_of_scope_state e.Deep_stores.scope.Deep_stores.state) ])
             st.Deep_stores.scopes.Deep_stores.entries) );
      ("nextName", Int st.Deep_stores.next_name) ]

let json_of_layers (ls : Deep_layer.layer_state) : E4d_json.t =
  let table tbl f =
    let items = Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl [] in
    List (List.map f (List.sort (fun (a, _) (b, _) -> compare a b) items))
  in
  Obj
    [ ("rootOpen", Bool ls.Deep_layer.root_open);
      ("registered", of_ints ls.Deep_layer.registered);
      ("releaseLog", of_ints ls.Deep_layer.release_log);
      ("nextService", Int ls.Deep_layer.next_service);
      ("nextLayerScope", Int ls.Deep_layer.next_layer_scope);
      ( "counts",
        table ls.Deep_layer.counts (fun (base, n) ->
            Obj [ ("base", Int base); ("constructions", Int n) ]) );
      ( "memo",
        table ls.Deep_layer.memo (fun (layer, service) ->
            Obj [ ("layer", Int layer); ("service", Int service) ]) ) ]

let json_of_state (st : st) : E4d_json.t =
  Obj
    [ ("started", of_ints st.started);
      ("cleanups", of_ints st.cleanups);
      ("stores", json_of_stores Deep_stores.store);
      ("layers", json_of_layers Deep_layer.layers) ]

let json_of_machine (m : run_machine) : E4d_json.t =
  Obj
    [ ("fibers", List (List.map json_of_fiber m.fibers));
      ("races", List (List.map json_of_race m.races));
      ("nextId", Int m.next_id);
      ("nextToken", Int m.next_token);
      ("nextRace", Int m.next_race);
      ("middlewareInstalled", Bool m.middleware_installed);
      ("stuck", json_of_stuck m.stuck);
      ("finished", Bool (machine_finished m));
      ("driveFuel", Int m.drive_fuel);
      ("state", json_of_state m.state);
      ("eventCount", Int (List.length m.trace)) ]

(* ------------------------------------------------------------------------- events *)

let json_of_event (e : run_event) : E4d_json.t =
  let render = Avatar_trace.render_event e in
  let kind = match String.index_opt render '\t' with Some i -> String.sub render 0 i | None -> render in
  let fields =
    match e with
    | Forked (p, c, d) -> [ ("parent", Int p); ("child", Int c); ("daemon", Bool d) ]
    | Started f -> [ ("fiber", Int f) ]
    | ScheduledTask (o, p, t) -> [ ("owner", Int o); ("priority", Int p); ("task", json_of_task t) ]
    | RanTask (o, t) -> [ ("owner", Int o); ("task", json_of_task t) ]
    | YieldInjected (f, n) -> [ ("fiber", Int f); ("opCount", Int n) ]
    | ParkedOn (f, t) -> [ ("fiber", Int f); ("token", Int t) ]
    | ResumedWith (f, t, a) -> [ ("fiber", Int f); ("token", Int t); ("answer", json_of_answer a) ]
    | InterruptRecorded (i, t) ->
      [ ("interruptor", match i with Some x -> Int x | None -> Null); ("target", Int t) ]
    | InterruptDeferred t -> [ ("target", Int t) ]
    | ChildrenInterrupted (p, cs) -> [ ("parent", Int p); ("children", of_ints cs) ]
    | ObserverFired (f, o) -> [ ("fiber", Int f); ("observer", json_of_observer o) ]
    | FrameEv (f, s) -> [ ("fiber", Int f); ("what", Str s) ]
    | FinalizerProgram (f, n, e) -> [ ("fiber", Int f); ("name", Str n); ("exit", json_of_exit e) ]
    | ScopeLinked (s, k, f) -> [ ("scope", Int s); ("key", Int k); ("fiber", Int f) ]
    | ScopeClosedOnLink (s, f) -> [ ("scope", Int s); ("fiber", Int f) ]
    | RaceStarted (r, h, es) -> [ ("race", Int r); ("host", Int h); ("entrants", of_ints es) ]
    | RaceLaunched (r, e) -> [ ("race", Int r); ("entrant", Int e) ]
    | RaceSkipped (r, e) -> [ ("race", Int r); ("entrant", Int e) ]
    | RaceSettled (r, e) -> [ ("race", Int r); ("exit", json_of_exit e) ]
    | ContextSet f -> [ ("fiber", Int f) ]
    | CallbackEv (k, e) -> [ ("key", Int k); ("exit", json_of_exit e) ]
    | Exited (f, e) -> [ ("fiber", Int f); ("exit", json_of_exit e) ]
  in
  Obj (("kind", Str kind) :: ("render", Str render) :: fields)

(* The event's own fiber, where it has one: `reachable` and `explain` group by it. *)
let event_fiber (e : run_event) : int option =
  match e with
  | Forked (_, c, _) -> Some c
  | Started f | YieldInjected (f, _) | ParkedOn (f, _) | ResumedWith (f, _, _)
  | ObserverFired (f, _) | FrameEv (f, _) | FinalizerProgram (f, _, _) | ContextSet f
  | Exited (f, _) -> Some f
  | ScheduledTask (o, _, _) | RanTask (o, _) -> Some o
  | InterruptRecorded (_, t) | InterruptDeferred t -> Some t
  | ChildrenInterrupted (p, _) -> Some p
  | ScopeLinked (_, _, f) | ScopeClosedOnLink (_, f) -> Some f
  | RaceStarted (_, h, _) -> Some h
  | RaceLaunched _ | RaceSkipped _ | RaceSettled _ | CallbackEv _ -> None
