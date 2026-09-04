(* The wire form of the shared trace alphabet, transcribed from
   `Effect4/Target/TypeScript/Trace.lean:60-75` and matched against `harness/trace/tracer.ts`
   (`wire`). Unit is `[]`, a list is right-nested pairs closed by unit, a handle is its index
   in first-seen order, `none` is `{"none":true}`, `some v` is `{"some":v}`; outcomes are
   `{"success":v}`, `{"failure":e}`, `{"interrupted":true}`. *)

open Deep_fibers

let rec wire (v : value) : string =
  match v with
  | Vunit -> "[]"
  | Vnat n -> string_of_int n
  | Vhandle h -> string_of_int h
  | Vnone -> "{\"none\":true}"
  | Vsome v -> "{\"some\":" ^ wire v ^ "}"
  | Vlist items -> List.fold_right (fun item acc -> "[" ^ wire item ^ ", " ^ acc ^ "]") items "[]"

let wire_exit (e : exitv) : string =
  match e with
  | Esuccess v -> "{\"success\":" ^ wire v ^ "}"
  | Efailure c -> (
    match cause_fail_of c with
    | Some err -> "{\"failure\":" ^ string_of_int err ^ "}"
    | None -> "{\"interrupted\":true}")

let render_row (r : row) : string =
  match r with
  | Rop (name, request) -> Printf.sprintf "op\t%s\t%s" name (wire request)
  | Ranswer (name, v) -> Printf.sprintf "answer\t%s\t%s" name (wire v)
  | Rfailed (name, e) -> Printf.sprintf "failed\t%s\t%d" name e
  | Rdecide (site, branch) -> Printf.sprintf "decide\t%d\t%s" site (if branch then "true" else "false")
  | Rdone e -> Printf.sprintf "done\t%s" (wire_exit e)

(* The header block of `generated/traces/*.tsv`, with `face ocaml`. The provenance rows name
   the avatar's own generator and inputs; `pin`, `program`, `tape` and `rules` are the
   golden's, passed in by the runner so the third face is comparable row for row. *)
let header ~generator_sha ~inputs ~pin ~program ~tape ~rules : string list =
  [ "format\teffect4-trace-golden-v1";
    Printf.sprintf "generator\tworkshop/OCaml5/avatar/build-avatar.sh\tsha256=%s" generator_sha;
    "regenerate\t./workshop/OCaml5/avatar/build-avatar.sh" ]
  @ List.map (fun (path, sha) -> Printf.sprintf "input\t%s\tsha256=%s" path sha) inputs
  @ [ Printf.sprintf "pin\teffects\t%s" pin;
      "format\teffect4-trace-v1";
      "face\tocaml";
      Printf.sprintf "program\t%s" program;
      Printf.sprintf "tape\t%s" tape;
      Printf.sprintf "rules\t%s" rules ]

(* The machine trace (`RunEvent`), printed on demand as evidence that the avatar's internal
   transitions are the Deep alphabet and not a paraphrase. Never compared with a golden. *)
let render_task (t : task) : string =
  match t with
  | Tstart c -> Printf.sprintf "start(%d)" c
  | Tresume (f, tok, _) -> Printf.sprintf "resume(%d,%d)" f tok

let render_observer (o : observer) : string =
  match o with
  | ResumeAwait (w, t, m) ->
    Printf.sprintf "resumeAwait(%d,%d,%s)" w t (match m with MJoin -> "join" | MAwait -> "await")
  | UntrackChild p -> Printf.sprintf "untrackChild(%d)" p
  | DropScopeFinalizer (s, k) -> Printf.sprintf "dropScopeFinalizer(%d,%d)" s k
  | Countdown (w, t) -> Printf.sprintf "countdown(%d,%d)" w t
  | RaceCallback r -> Printf.sprintf "raceCallback(%d)" r
  | Callback k -> Printf.sprintf "callback(%d)" k

let render_event (e : run_event) : string =
  match e with
  | Forked (p, c, d) -> Printf.sprintf "forked\t%d\t%d\t%b" p c d
  | Started f -> Printf.sprintf "started\t%d" f
  | ScheduledTask (o, p, t) -> Printf.sprintf "scheduledTask\t%d\t%d\t%s" o p (render_task t)
  | RanTask (o, t) -> Printf.sprintf "ranTask\t%d\t%s" o (render_task t)
  | YieldInjected (f, n) -> Printf.sprintf "yieldInjected\t%d\t%d" f n
  | ParkedOn (f, t) -> Printf.sprintf "parkedOn\t%d\t%d" f t
  | ResumedWith (f, t, _) -> Printf.sprintf "resumedWith\t%d\t%d" f t
  | InterruptRecorded (i, t) ->
    Printf.sprintf "interruptRecorded\t%s\t%d"
      (match i with Some x -> string_of_int x | None -> "-") t
  | InterruptDeferred t -> Printf.sprintf "interruptDeferred\t%d" t
  | ChildrenInterrupted (p, cs) ->
    Printf.sprintf "childrenInterrupted\t%d\t[%s]" p
      (String.concat ";" (List.map string_of_int cs))
  | ObserverFired (f, o) -> Printf.sprintf "observerFired\t%d\t%s" f (render_observer o)
  | FrameEv (f, s) -> Printf.sprintf "frame\t%d\t%s" f s
  | FinalizerProgram (f, n, _) -> Printf.sprintf "finalizerProgram\t%d\t%s" f n
  | ScopeLinked (s, k, f) -> Printf.sprintf "scopeLinked\t%d\t%d\t%d" s k f
  | ScopeClosedOnLink (s, f) -> Printf.sprintf "scopeClosedOnLink\t%d\t%d" s f
  | RaceStarted (r, h, es) ->
    Printf.sprintf "raceStarted\t%d\t%d\t[%s]" r h (String.concat ";" (List.map string_of_int es))
  | RaceLaunched (r, e) -> Printf.sprintf "raceLaunched\t%d\t%d" r e
  | RaceSkipped (r, e) -> Printf.sprintf "raceSkipped\t%d\t%d" r e
  | RaceSettled (r, e) -> Printf.sprintf "raceSettled\t%d\t%s" r (wire_exit e)
  | ContextSet f -> Printf.sprintf "contextSet\t%d" f
  | CallbackEv (k, e) -> Printf.sprintf "callback\t%d\t%s" k (wire_exit e)
  | Exited (f, e) -> Printf.sprintf "exited\t%d\t%s" f (wire_exit e)
