(* `effect4d`, as a library.

   Every request the daemon answers is a function in this module; `effect4d.ml` and
   `effect4d_js.ml` are the two transports and hold no logic. `handle` is the whole protocol
   in one function, `Json -> Json`, so a caller that already has a request record can skip
   the wire entirely -- which is what `tests/lib_test.ml` does and what the js_of_ocaml build
   exports to JavaScript.

   The avatar is consumed read-only: this module links `Deep_fibers`, `Avatar_trace`, the
   three fixture modules and the corpus interpreter, and never edits them. The one thing it
   does that `avatar_main.ml` does not is reset their module-level state between requests
   (`E4d_reset`), because a daemon is not a one-shot process. *)

open Deep_fibers
open E4d_json

let protocol = "effect4d/1"

(* ------------------------------------------------------------------------- errors *)

type failure = E4d_protocol.failure = { kind : string; message : string }

let bad = E4d_protocol.bad

(* ---------------------------------------------------------------- running a program *)

type outcome = Finished of exitv | Frontier | Stuck of stuck

type run = {
  program : E4d_catalog.program;
  tape : string;
  rules : string;
  max_ops : int;
  fuel : int;
  rounds : int;
  rows : string list;            (* the estate's TSV row vocabulary, verbatim *)
  events : run_event list;
  machine : run_machine;
  outcome : outcome;
  yields : int;
}

let default_fuel = Deep_fibers.default_fuel
let default_rounds = Deep_fibers.default_rounds

(* One run, from a clean avatar. `rounds` is how many sweeps of the armed dispatchers the
   flush is allowed; `fuel` is how many commands one `drive` may execute. `run_program`
   itself is `drive` at full rounds, so `execute` spells the same two steps -- `run_fork`
   then the flush -- in order to expose the round bound to `step`. *)
let execute (program : E4d_catalog.program) ?tape ?max_ops ?(fuel = default_fuel)
    ?(rounds = default_rounds) ?(rules = "") () : run =
  E4d_reset.all ();
  let default_tape, default_max_ops = E4d_catalog.defaults program in
  let thunk = E4d_catalog.thunk program in
  let tape = match tape with Some t -> t | None -> default_tape in
  let max_ops = match max_ops with Some n -> n | None -> default_max_ops in
  Tape.load tape;
  Deep_fibers.max_ops_before_yield := max_ops;
  let m = machine_empty state in
  let outcome =
    let root = run_fork m fuel thunk in
    flush_all m fuel rounds;
    match m.stuck with
    | Some why -> Stuck why
    | None -> (
      match (fiber_exn m root).exit_ with Some e -> Finished e | None -> Frontier)
  in
  (* `avatar_main.ml:64-67`: the outcome is the last service row. A stuck machine writes
     `frontier`, exactly as the avatar does. *)
  (match outcome with
   | Finished e -> push_row (Rdone e)
   | Frontier | Stuck _ -> push_row Rfrontier);
  { program;
    tape;
    rules;
    max_ops;
    fuel;
    rounds;
    rows = List.map Avatar_trace.render_row !sink;
    events = m.trace;
    machine = m;
    outcome;
    yields = List.length (List.filter (function YieldInjected _ -> true | _ -> false) m.trace) }

(* A partial run: no `done`/`frontier` row is appended, because the run is not over. Used by
   `step`, `reachable` and `budget`, which are about the machine rather than the rows. *)
let execute_partial (program : E4d_catalog.program) ?tape ?max_ops ?(fuel = default_fuel)
    ?(rounds = default_rounds) ?(rules = "") () : run =
  E4d_reset.all ();
  let default_tape, default_max_ops = E4d_catalog.defaults program in
  let thunk = E4d_catalog.thunk program in
  let tape = match tape with Some t -> t | None -> default_tape in
  let max_ops = match max_ops with Some n -> n | None -> default_max_ops in
  Tape.load tape;
  Deep_fibers.max_ops_before_yield := max_ops;
  let m = machine_empty state in
  let root = run_fork m fuel thunk in
  if rounds > 0 then flush_all m fuel rounds;
  let outcome =
    match m.stuck with
    | Some why -> Stuck why
    | None -> ( match (fiber_exn m root).exit_ with Some e -> Finished e | None -> Frontier)
  in
  { program;
    tape;
    rules;
    max_ops;
    fuel;
    rounds;
    rows = List.map Avatar_trace.render_row !sink;
    events = m.trace;
    machine = m;
    outcome;
    yields = List.length (List.filter (function YieldInjected _ -> true | _ -> false) m.trace) }

(* -------------------------------------------------------------------- the header

   The golden's header block, with the daemon's own generator and per-file input digests.
   `face` is `ocaml`: the rows are the avatar's, produced by the same modules
   `build-avatar.sh` compiles, so a daemon answer is the avatar's third face and can be
   dropped next to a golden and compared under `masks.tsv` with no translation. *)
let header_lines ~(label : string) ~(tape : string) ~(rules : string) : string list =
  [ "format\teffect4-trace-golden-v1";
    Printf.sprintf "generator\tocaml/server/dune\tsha256=%s" E4d_pins.generator_sha;
    "regenerate\tocaml/server/tools/dune-build.sh" ]
  @ List.map (fun (path, sha) -> Printf.sprintf "input\t%s\tsha256=%s" path sha) E4d_pins.inputs
  @ [ Printf.sprintf "pin\teffects\t%s" E4d_pins.pin;
      "format\teffect4-trace-v1";
      "face\tocaml";
      Printf.sprintf "program\t%s" label;
      Printf.sprintf "tape\t%s" tape;
      Printf.sprintf "rules\t%s" rules ]

let header_json ~label ~tape ~rules : E4d_json.t =
  Obj
    [ ("format", Str "effect4-trace-v1");
      ("goldenFormat", Str "effect4-trace-golden-v1");
      ("generator", Str "ocaml/server/dune");
      ("generatorSha256", Str E4d_pins.generator_sha);
      ("regenerate", Str "ocaml/server/tools/dune-build.sh");
      ( "inputs",
        List
          (List.map
             (fun (path, sha) -> Obj [ ("path", Str path); ("sha256", Str sha) ])
             E4d_pins.inputs) );
      ("pin", Obj [ ("effects", Str E4d_pins.pin) ]);
      ("face", Str "ocaml");
      ("program", Str label);
      ("tape", Str tape);
      ("rules", Str rules) ]

let host_name () =
  match Sys.backend_type with
  | Sys.Native -> "native"
  | Sys.Bytecode -> "bytecode"
  | Sys.Other other -> other

(* -------------------------------------------------------------------- the masks *)

let builtin_masks : E4d_wire.mask list Lazy.t = lazy (E4d_wire.parse_masks E4d_masks_data.text)

(* A request may name masks (`["m1","m2"]`), carry a mask table of its own (`masksText`), or
   say nothing, in which case the committed `generated/traces/masks.tsv` is used whole. *)
let masks_of (request : E4d_json.t) : E4d_wire.mask list =
  match member "masksText" request with
  | Str text -> E4d_wire.parse_masks text
  | _ -> (
    match E4d_json.strings "masks" request with
    | [] -> Lazy.force builtin_masks
    | wanted ->
      List.map
        (fun name ->
          match List.find_opt (fun (m : E4d_wire.mask) -> m.name = name) (Lazy.force builtin_masks) with
          | Some m -> m
          | None -> bad "unknown-mask" ("no mask named " ^ name))
        wanted)

(* -------------------------------------------------------------- resolving a program

   Three source forms, plus a reference to one `load` already resolved. The session table is
   a plain association list: the daemon is single-threaded and a session holds a handful of
   programs, so nothing more is warranted, and it is cleared by `reset`. *)

(* ------------------------------------------------------------------------ the session

   Everything a session remembers, as one record threaded through `step`. There is no ambient
   state and no clock: `step : session -> request -> session * response` is a function, and
   the only mutation in the daemon is the transport's `session ref` at the outermost shell
   (`effect4d.ml`, `effect4d_js.ml`).

   The avatar's own module-level state is the exception, and it is why `E4d_reset.all` runs
   at the head of every `execute`: the avatar is consumed read-only and its state cannot be
   made a parameter from outside. The behavioural consequence is property R1, and the test
   that it holds is `determinism-in-one-session`. *)

type loaded_program = {
  loaded_program : E4d_catalog.program;
  loaded_tape : string;
  loaded_rules : string;
}

type session = {
  loaded : (string * loaded_program) list;
  next_program : int;
  streams : (string * E4d_stream.t) list;   (* most recently opened first *)
  next_stream : int;
  (* The reply journal: the answered request ids, most recent first, so that a client that
     retries gets the recorded reply and changes nothing (property W2). *)
  journal : (string * E4d_protocol.response) list;
}

(* The bounds, stated in `E4d_alphabet.properties` and in README §0. *)
let max_in_flight = 1
let journal_bound = 64
let max_open_streams = 8
let max_stream_items = 100000

let empty_session =
  { loaded = []; next_program = 0; streams = []; next_stream = 0; journal = [] }

let remember (s : session) program tape rules : session * string =
  let id = Printf.sprintf "p%d" s.next_program in
  ( { s with
      next_program = s.next_program + 1;
      loaded =
        (id, { loaded_program = program; loaded_tape = tape; loaded_rules = rules }) :: s.loaded },
    id )

(* `journal_bound` most recent entries, oldest dropped (property W5). *)
let journal_add (s : session) (key : string) (r : E4d_protocol.response) : session =
  let rec take n = function [] -> [] | x :: rest -> if n = 0 then [] else x :: take (n - 1) rest in
  { s with journal = take journal_bound ((key, r) :: List.remove_assoc key s.journal) }

(* An absent `tape`, and an empty one, both mean "the program's own default": a fixture
   program's default is the empty tape, and a corpus program's is its `tape` line or 32
   all-`false` entries. A client that sent `"tape": ""` for a corpus program would otherwise
   have its first fork read past the end of the tape. *)
let tape_of (request : E4d_json.t) : string option =
  match member "tape" request with Str "" -> None | Str t -> Some t | _ -> None

let resolve (s : session) (request : E4d_json.t) : E4d_catalog.program * string option * string =
  let source = str "source" request in
  match source with
  | "" | "loaded" | "id" -> (
    (* `programId`, not `id`: `id` is the *request* id, which the journal keys on (W2). The
       two used to share a key, which made every request naming a loaded program look like a
       replay of the `load` that minted it. *)
    let id = str "programId" request in
    if id = "" then
      bad "no-program"
        "the request names no program: give `programId` from a `load`, or a `source`"
    else
      match List.assoc_opt id s.loaded with
      | Some entry ->
        let tape =
          match tape_of request with Some t -> Some t | None -> Some entry.loaded_tape
        in
        (entry.loaded_program, tape, entry.loaded_rules)
      | None -> bad "unknown-id" ("no program loaded under " ^ id))
  | "fixture" ->
    ( E4d_catalog.of_fixture (str "family" request) (str "program" request),
      tape_of request,
      str "rules" request )
  | "corpus" ->
    let text = match member "text" request with Str t -> Some t | _ -> None in
    ( E4d_catalog.of_corpus ?text (str "program" request),
      tape_of request,
      str "rules" request )
  | "golden" ->
    let text =
      match member "text" request with
      | Str t -> t
      | _ -> bad "no-text" "source `golden` needs the golden's text in `text`"
    in
    let family = match member "family" request with Str f -> Some f | _ -> None in
    let program, tape, rules, _pin = E4d_catalog.of_golden_header ?family text in
    let tape = match member "tape" request with Str t -> t | _ -> tape in
    (program, Some tape, rules)
  | other -> bad "unknown-source" ("unknown source " ^ other)

let run_of (s : session) (request : E4d_json.t) : run =
  let program, tape, rules = resolve s request in
  let max_ops = match to_int_opt (member "maxOps" request) with Some n -> Some n | None -> None in
  let fuel = int_ ~default:default_fuel "fuel" request in
  let rounds = int_ ~default:default_rounds "rounds" request in
  execute program ?tape ?max_ops ~fuel ~rounds ~rules ()

(* ------------------------------------------------------------- rows, events, outcome *)

let json_of_outcome (o : outcome) : E4d_json.t =
  match o with
  | Finished e -> Obj [ ("tag", Str "finished"); ("exit", E4d_snapshot.json_of_exit e) ]
  | Frontier -> Obj [ ("tag", Str "frontier") ]
  | Stuck s -> Obj [ ("tag", Str "stuck"); ("why", E4d_snapshot.json_of_stuck (Some s)) ]

let projections (masks : E4d_wire.mask list) (rows : string list) : E4d_json.t =
  List
    (List.map
       (fun (m : E4d_wire.mask) ->
         let kept = E4d_wire.project m rows in
         Obj [ ("mask", Str m.name); ("rows", of_strings kept); ("count", Int (List.length kept)) ])
       masks)

let run_payload (r : run) (masks : E4d_wire.mask list) : (string * E4d_json.t) list =
  [ ("program", Str r.program.E4d_catalog.label);
    ("family", Str r.program.E4d_catalog.family);
    ("tape", Str r.tape);
    ("maxOps", if r.max_ops = max_int then Null else Int r.max_ops);
    ("fuel", Int r.fuel);
    ("rounds", Int r.rounds);
    ("rows", of_strings r.rows);
    ("rowCount", Int (List.length r.rows));
    ("projections", projections masks r.rows);
    ("outcome", json_of_outcome r.outcome);
    ("yields", Int r.yields);
    ("events", List (List.map E4d_snapshot.json_of_event r.events));
    ("eventCount", Int (List.length r.events));
    ("tsv", Str (String.concat "\n"
                   (header_lines ~label:r.program.E4d_catalog.label ~tape:r.tape ~rules:r.rules
                    @ r.rows))) ]

(* ------------------------------------------------------- the row/event correlation

   The avatar pushes a service row from inside a handler arm and an event from inside the
   machine; nothing records which events belong to which row, and the avatar is read-only, so
   the daemon cannot add a hook. It recovers the correspondence by replay instead: the same
   program is run again under a tightening bound, and the row and event counts recorded at
   each step. Row `i` belongs to the first step at which the row list is longer than `i`, and
   the events of that bucket are the events that appeared at the same step.

   Two bounds can be varied, and the answer says which one it used:

     `flush-round`  the number of sweeps `flushAll` is allowed. A run at `r` rounds is a
                    genuine prefix of the run at `r+1`, because the sweeps are the same
                    deterministic sequence -- so this scan is always sound. It is coarse
                    where a program does all its work on the caller's stack inside `runFork`,
                    which is every single-fiber synchronous program.
     `drive-command` the fuel one `drive` may spend. Finer where it works, but *not*
                    monotone in general: at fuel 3 the interrupt witness below emits 14 rows
                    and at fuel 4 only 11, because a nested `drive` inside `continue k`
                    spends the same budget and a truncation at one point sends the run down a
                    different path (DIVERGENCE 4). The scan checks monotonicity and refuses
                    the result when it fails.

   When neither yields more than one bucket the answer is `coarse`: one bucket for the whole
   run, and `buckets = 1` saying so. *)

type correlation = {
  granularity : string;             (* "flush-round", "drive-command" or "coarse" *)
  buckets : int array;              (* row index -> the bucket it first appeared at *)
  bucket_events : run_event list array; (* bucket -> the events that appeared at it *)
  scanned : int;
}

let scan_limit = 512

(* Two event lists are the same when they render the same. An event can carry a closure
   since the avatar's F2 checkpoint (`ResumedWith` with an `Aprogram` answer, the race
   settle program), and polymorphic equality on one raises `Invalid_argument "compare:
   functional value"`; the rendered form is the wire's own view of the event and total. *)
let same_events (a : run_event list) (b : run_event list) : bool =
  List.length a = List.length b
  && List.for_all2 (fun x y -> Avatar_trace.render_event x = Avatar_trace.render_event y) a b

(* (row count, events) at each value of the bound, up to the point where the run is complete
   or the limit is reached. *)
let scan (r : run) (vary : int -> run) (target_rows : int) =
  let rec go step acc =
    if step > scan_limit then List.rev acc
    else
      let partial = vary step in
      let acc = (List.length partial.rows, partial.events) :: acc in
      if List.length partial.rows >= target_rows && same_events partial.events r.events then
        List.rev acc
      else go (step + 1) acc
  in
  Array.of_list (go 0 [])

let monotone (samples : (int * run_event list) array) =
  let ok = ref true in
  for i = 1 to Array.length samples - 1 do
    if fst samples.(i) < fst samples.(i - 1) then ok := false
  done;
  !ok

let buckets_of (samples : (int * run_event list) array) (total_rows : int) =
  let n = Array.length samples in
  let buckets = Array.make (max total_rows 1) (max 0 (n - 1)) in
  for i = 0 to total_rows - 1 do
    let j = ref 0 in
    while !j < n && fst samples.(!j) <= i do incr j done;
    buckets.(i) <- (if !j < n then !j else max 0 (n - 1))
  done;
  let bucket_events = Array.make (max n 1) [] in
  let previous = ref 0 in
  for i = 0 to n - 1 do
    let events = snd samples.(i) in
    let total = List.length events in
    bucket_events.(i) <-
      (if total <= !previous then [] else List.filteri (fun k _ -> k >= !previous) events);
    previous := max !previous total
  done;
  (buckets, bucket_events)

let distinct (buckets : int array) =
  List.length (List.sort_uniq compare (Array.to_list buckets))

let correlate (r : run) : correlation =
  (* The replay uses `execute_partial`, which appends no `done`/`frontier` row: a truncated
     run would otherwise be one row longer than its own prefix. The terminal row falls in the
     last bucket by construction. *)
  let target_rows = List.length r.rows - 1 in
  let total_rows = List.length r.rows in
  let program = r.program in
  let by_rounds =
    scan r
      (fun rounds ->
        execute_partial program ~tape:r.tape ~max_ops:r.max_ops ~fuel:r.fuel ~rounds
          ~rules:r.rules ())
      target_rows
  in
  let choose name samples =
    let buckets, bucket_events = buckets_of samples total_rows in
    { granularity = name; buckets; bucket_events; scanned = Array.length samples }
  in
  let rounds_result =
    if Array.length by_rounds > 0 && monotone by_rounds then Some (choose "flush-round" by_rounds)
    else None
  in
  match rounds_result with
  | Some c when distinct c.buckets > 1 -> c
  | rounds_result -> (
    let by_fuel =
      scan r
        (fun fuel ->
          execute_partial program ~tape:r.tape ~max_ops:r.max_ops ~fuel:(fuel + 1)
            ~rounds:r.rounds ~rules:r.rules ())
        target_rows
    in
    let fuel_result =
      if Array.length by_fuel > 0 && monotone by_fuel then Some (choose "drive-command" by_fuel)
      else None
    in
    match (fuel_result, rounds_result) with
    | Some c, _ when distinct c.buckets > 1 -> c
    | _, Some c -> c
    | Some c, None -> c
    | None, None ->
      { granularity = "coarse";
        buckets = Array.make (max total_rows 1) 0;
        bucket_events = [| r.events |];
        scanned = Array.length by_rounds + Array.length by_fuel })

(* How many distinct buckets the rows actually fell into. One bucket means the whole run was
   one step of whichever bound the correlation varied -- which is what a single-fiber
   synchronous program is -- and the answer says so rather than implying a per-row
   attribution it does not have. *)
let bucket_count (c : correlation) : int = distinct c.buckets

(* ------------------------------------------------------------------------- explain *)

(* Which avatar arm produced a row, and which Lean line that arm cites. The row name is the
   key: `E4d_armmap.dispatch` and `E4d_armmap.row_names` are generated from the avatar's own
   `effc` table and arm bodies, so a name that several families share (`make`, `close`)
   resolves to several arms and the answer lists all of them, narrowed by the family where
   the family determines it. *)

let arms_for_row ~(family : string) ?(step_ops : string list = []) (name : string) : string list =
  let from_dispatch =
    List.filter_map
      (fun (_ctor, arm, arg) -> if arg = Some name then Some arm else None)
      E4d_armmap.dispatch
  in
  let from_bodies =
    List.filter_map
      (fun (arm, names) -> if List.mem name names then Some arm else None)
      E4d_armmap.row_names
  in
  (* A row a caller module pushes around a `perform` (`op yield` / `answer yield`) resolves
     through the effect constructor it brackets. *)
  let from_callers =
    List.concat_map
      (fun (row, ctor) ->
        if row <> name then []
        else
          List.filter_map
            (fun (c, arm, _) -> if c = ctor then Some arm else None)
            E4d_armmap.dispatch)
      E4d_armmap.caller_rows
  in
  let candidates = List.sort_uniq compare (from_dispatch @ from_bodies @ from_callers) in
  (* Which constructors reach a label, from the dispatch tables. A family is then a
     constructor prefix -- `Rref_`, `Rdef_`, `Rscope_`, `Rlayer_` for the store families,
     `Op_` for the fiber ones -- so `make` is `case Rref_make` in the `ref` family and
     `case Rscope_make` in `scope`, and `awaitValue` is `arm_await` (`Fiber.await`) in a
     fiber program and `arm_def_await` (`Deferred.await`) in a Deferred one. Naming the
     constructors rather than the label spellings means this survives the arms moving
     between avatar modules. *)
  let ctors_of label =
    List.filter_map
      (fun (ctor, arm, _) -> if arm = label then Some ctor else None)
      E4d_armmap.dispatch
  in
  let starts_with prefix s =
    String.length s >= String.length prefix && String.sub s 0 (String.length prefix) = prefix
  in
  let keep_if prefix =
    match
      List.filter (fun label -> List.exists (starts_with prefix) (ctors_of label)) candidates
    with
    | [] -> candidates
    | some -> some
  in
  let by_family =
    match family with
    | "ref" -> keep_if "Rref_"
    | "deferred" -> keep_if "Rdef_"
    | "scope" -> keep_if "Rscope_"
    | "layer" -> keep_if "Rlayer_"
    | "fiber" | "extra" -> keep_if "Op_"
    | _ -> candidates
  in
  (* A corpus program says in its own source which DSL steps it performs, and the DSL step
     table says which effect constructor each performs, so a name two labels could have
     produced is narrowed to the ones the program can have reached. *)
  if step_ops = [] then by_family
  else
    let reachable_ctors =
      List.filter_map (fun step -> List.assoc_opt step E4d_armmap.step_ops) step_ops
    in
    let reachable_arms =
      List.filter_map
        (fun (ctor, arm, _) -> if List.mem ctor reachable_ctors then Some arm else None)
        E4d_armmap.dispatch
    in
    match List.filter (fun a -> List.mem a reachable_arms) by_family with
    | [] -> by_family
    | narrowed -> narrowed

let json_of_citation (c : E4d_armmap.citation) : E4d_json.t =
  Obj
    [ ("token", Str c.E4d_armmap.token);
      ("resolution", Str c.E4d_armmap.resolution);
      ( "sites",
        List
          (List.map
             (fun (s : E4d_armmap.site) ->
               Obj
                 [ ("file", Str s.E4d_armmap.file);
                   ("line", Int s.E4d_armmap.line);
                   ("declaration", match s.E4d_armmap.decl with Some d -> Str d | None -> Null) ])
             c.E4d_armmap.sites) ) ]

let json_of_arm (arm : string) : E4d_json.t =
  let doc_of label =
    match List.find_opt (fun (n, _, _) -> n = label) E4d_armmap.arms with
    | Some (_, doc, cites) -> (doc, cites)
    | None -> ("", [])
  in
  let symbols_of label =
    match List.assoc_opt label E4d_armmap.symbols with Some s -> s | None -> []
  in
  (* A dispatch case with no doc of its own inherits the doc of the function whose match it
     is a case of -- `case Rref_make` is a case of `store_arm`, which cites `Stores.lean`.
     The answer says where the citation came from, so an inherited one is never read as the
     case's own. *)
  let doc, citations, symbols, inherited =
    let doc, citations = doc_of arm in
    let symbols = symbols_of arm in
    if citations <> [] || symbols <> [] then (doc, citations, symbols, None)
    else
      match List.assoc_opt arm E4d_armmap.enclosing with
      | None -> (doc, citations, symbols, None)
      | Some parent ->
        let parent_doc, parent_citations = doc_of parent in
        ((if doc = "" then parent_doc else doc), parent_citations, symbols_of parent, Some parent)
  in
  let constructors =
    List.sort_uniq compare
      (List.filter_map
         (fun (ctor, label, _) -> if label = arm then Some ctor else None)
         E4d_armmap.dispatch)
  in
  Obj
    [ ("arm", Str arm);
      ("constructors", of_strings constructors);
      ("citationsFrom", match inherited with Some parent -> Str parent | None -> Str arm);
      ("avatar", Str ("ocaml/avatar :: " ^ arm));
      ("doc", Str doc);
      ("citations", List (List.map json_of_citation citations));
      ( "leanDeclarations",
        List
          (List.map
             (fun (name, file, line) ->
               Obj [ ("name", Str name); ("file", Str file); ("line", Int line) ])
             symbols) ) ]

let row_kind_and_name (row : string) : string * string =
  match String.split_on_char '\t' row with
  | kind :: name :: _ -> (kind, name)
  | [ kind ] -> (kind, "")
  | [] -> ("", "")

let explain (r : run) (c : correlation) : E4d_json.t =
  let rows = Array.of_list r.rows in
  let step_ops = E4d_catalog.step_ops r.program in
  List
    (Array.to_list
       (Array.mapi
          (fun i row ->
            let kind, name = row_kind_and_name row in
            let arms =
              if kind = "op" || kind = "answer" || kind = "failed" then
                arms_for_row ~family:r.program.E4d_catalog.family ~step_ops name
              else []
            in
            let bucket = if i < Array.length c.buckets then c.buckets.(i) else 0 in
            let events =
              if bucket < Array.length c.bucket_events then c.bucket_events.(bucket) else []
            in
            Obj
              [ ("index", Int i);
                ("row", Str row);
                ("kind", Str kind);
                ("name", Str name);
                ("bucket", Int bucket);
                ("arms", List (List.map json_of_arm arms));
                ("events", List (List.map E4d_snapshot.json_of_event events)) ])
          rows))

(* --------------------------------------------------------------------- reachable *)

(* What the machine can still do, read off a snapshot. A fiber is resumable when it holds a
   captured one-shot continuation whose token is the guard it is parked on; it is armed when
   its own dispatcher has tasks; and it is waiting on a fiber, a Deferred or a race depending
   on where its pending token is registered. *)
let reachable (m : run_machine) : E4d_json.t =
  let waiting_reason (f : run_fiber) (token : int) : E4d_json.t =
    let pending = List.find_opt (fun (p : pending) -> p.token = token) f.pending in
    let on_deferred =
      let rec find index = function
        | [] -> None
        | (cell : Deep_stores.deferred_cell) :: rest ->
          if List.exists (fun (fid, tok) -> fid = f.id && tok = token) cell.Deep_stores.waiters
          then Some index
          else find (index + 1) rest
      in
      find 0 Deep_stores.store.Deep_stores.deferreds.Deep_stores.cells
    in
    let on_race =
      List.find_opt (fun (r : race) -> r.host = f.id && r.rtoken = token) m.races
    in
    match (pending, on_deferred, on_race) with
    | _, Some id, _ ->
      Obj [ ("on", Str "deferred"); ("deferred", Int id) ]
    | _, _, Some r -> Obj [ ("on", Str "race"); ("race", Int r.rid) ]
    (* `remaining` is the list of targets the countdown walk has not visited yet (R2-4):
       the count is its length, and the list itself says which. *)
    | Some { waiting_on = Some target; remaining; _ }, _, _ ->
      Obj
        [ ("on", Str "fiber"); ("fiber", Int target); ("remaining", Int (List.length remaining));
          ("remainingTargets", of_ints remaining) ]
    | Some { waiting_on = None; remaining; _ }, _, _ when remaining <> [] ->
      Obj
        [ ("on", Str "countdown"); ("remaining", Int (List.length remaining));
          ("remainingTargets", of_ints remaining) ]
    | Some _, _, _ -> Obj [ ("on", Str "async"); ("note", Str "registered, no store holds it") ]
    | None, _, _ -> Obj [ ("on", Str "unknown") ]
  in
  let fibers =
    List.map
      (fun (f : run_fiber) ->
        let suspended = match f.frame.control with Suspended k -> Some k.ktoken | _ -> None in
        let guard = match f.parked with WithGuard t -> Some t | NotParked -> None in
        let resumable = f.exit_ = None && suspended <> None && suspended = guard in
        Obj
          [ ("id", Int f.id);
            ("status", Str (E4d_snapshot.status_name (run_fiber_status f)));
            ("resumable", Bool resumable);
            ("resumeToken", match suspended with Some t -> Int t | None -> Null);
            ("armed", Bool f.dispatcher.armed);
            ( "queuedTasks",
              Int (List.fold_left (fun n (b : bucket) -> n + List.length b.tasks) 0
                     f.dispatcher.buckets) );
            ("parkedOn", match guard with Some t -> waiting_reason f t | None -> Null);
            ("interruptible", Bool f.frame.interruptible);
            ( "interruptPending",
              Bool (f.frame.interrupted_cause <> None || f.frame.deferred_interrupt) );
            ("children", of_ints f.children);
            ( "observersHeld",
              List (List.map E4d_snapshot.json_of_observer f.observers) ) ])
      m.fibers
  in
  let observers_pending =
    List.concat_map
      (fun (f : run_fiber) ->
        List.map
          (fun o ->
            Obj [ ("onFiber", Int f.id); ("observer", E4d_snapshot.json_of_observer o) ])
          f.observers)
      m.fibers
  in
  Obj
    [ ("fibers", List fibers);
      ( "resumable",
        of_ints
          (List.filter_map
             (fun (f : run_fiber) ->
               match (f.frame.control, f.parked) with
               | Suspended k, WithGuard t when k.ktoken = t && f.exit_ = None -> Some f.id
               | _ -> None)
             m.fibers) );
      ( "armed",
        of_ints
          (List.filter_map (fun (f : run_fiber) -> if f.dispatcher.armed then Some f.id else None)
             m.fibers) );
      ("observersPending", List observers_pending);
      ( "dueResumes",
        Int (List.length Deep_stores.store.Deep_stores.deferreds.Deep_stores.due) );
      ("finished", Bool (machine_finished m));
      ("stuck", E4d_snapshot.json_of_stuck m.stuck) ]

(* ----------------------------------------------------------------------- budget *)

(* The op counter and the yield injection points. `MaxOpsBeforeYield` is `Scheduler`'s
   budget, cached on the fiber at `RunFiber.make` (`internal/effect.ts:726-727`); `guard`
   increments `currentOpCount` once per primitive and injects a yield at the bound. *)
let budget (r : run) : E4d_json.t =
  let injections =
    List.filter_map
      (function YieldInjected (f, n) -> Some (f, n) | _ -> None)
      r.events
  in
  Obj
    [ ("maxOpsBeforeYield", if r.max_ops = max_int then Null else Int r.max_ops);
      ("preventYield", Bool Deep_fibers.(!prevent_yield));
      ("yields", Int (List.length injections));
      ( "injections",
        List
          (List.mapi
             (fun i (f, n) -> Obj [ ("index", Int i); ("fiber", Int f); ("opCount", Int n) ])
             injections) );
      ( "perFiber",
        List
          (List.map
             (fun (f : run_fiber) ->
               Obj
                 [ ("id", Int f.id);
                   ("currentOpCount", Int f.current_op_count);
                   ( "maxOpsBeforeYield",
                     if f.max_ops_before_yield = max_int then Null else Int f.max_ops_before_yield );
                   ("preventYield", Bool f.prevent_yield);
                   ("yielding", Bool f.yielding);
                   ("yieldOverride", match f.yield_override with Some b -> Bool b | None -> Null);
                   ( "injections",
                     Int (List.length (List.filter (fun (g, _) -> g = f.id) injections)) ) ])
             r.machine.fibers) );
      ( "note",
        Str
          "currentOpCount is reset at every Cmd.evaluate and Cmd.resume, so the per-fiber \
           figure is the count since that fiber was last given the processor, not a total." ) ]

(* --------------------------------------------------------------------------- why *)

(* Given a reference row list -- typically rc.112's, produced by
   `avatar/corpus_rc112.mjs` -- the first row on which the avatar and the reference differ
   under a mask, and the avatar's event trace up to that row. *)
let why (r : run) (reference_rows : string list) (masks : E4d_wire.mask list) : E4d_json.t =
  let c = correlate r in
  let verdicts = E4d_wire.compare_all masks reference_rows r.rows in
  let first_bad = List.find_opt (fun (v : E4d_wire.mask_verdict) -> not v.agree) verdicts in
  let payload =
    match first_bad with
    | None -> [ ("diverges", Bool false) ]
    | Some v ->
      (* the mask index of the first difference, mapped back to an index in the unmasked
         row list, so the event bucket can be found *)
      let mask = List.find (fun (m : E4d_wire.mask) -> m.name = v.mask_name) masks in
      let unmasked_index =
        let kept = ref (-1) in
        let answer = ref (List.length r.rows) in
        List.iteri
          (fun i row ->
            if E4d_wire.keeps mask (fst (row_kind_and_name row)) then begin
              incr kept;
              if !kept = v.first_difference && !answer = List.length r.rows then answer := i
            end)
          r.rows;
        !answer
      in
      let bucket =
        if unmasked_index < Array.length c.buckets then c.buckets.(unmasked_index)
        else Array.length c.bucket_events - 1
      in
      let events_up_to =
        let out = ref [] in
        for i = 0 to min bucket (Array.length c.bucket_events - 1) do
          out := !out @ c.bucket_events.(i)
        done;
        !out
      in
      [ ("diverges", Bool true);
        ("mask", Str v.mask_name);
        ("firstDifference", Int v.first_difference);
        ("rowIndex", if unmasked_index >= List.length r.rows then Null else Int unmasked_index);
        ("expected", match v.expected_row with Some s -> Str s | None -> Null);
        ("actual", match v.actual_row with Some s -> Str s | None -> Null);
        ( "context",
          Obj
            [ ( "referenceBefore",
                of_strings
                  (let kept = E4d_wire.project mask reference_rows in
                   List.filteri (fun i _ -> i >= v.first_difference - 3 && i < v.first_difference)
                     kept) );
              ( "avatarBefore",
                of_strings
                  (let kept = E4d_wire.project mask r.rows in
                   List.filteri (fun i _ -> i >= v.first_difference - 3 && i < v.first_difference)
                     kept) ) ] );
        ("eventsUpToDifference", List (List.map E4d_snapshot.json_of_event events_up_to));
        ("eventsAtDifference",
         List
           (List.map E4d_snapshot.json_of_event
              (if bucket < Array.length c.bucket_events then c.bucket_events.(bucket) else [])));
        ( "arms",
          List
            (if unmasked_index < List.length r.rows then
               let row = List.nth r.rows unmasked_index in
               let kind, name = row_kind_and_name row in
               if kind = "op" || kind = "answer" || kind = "failed" then
                 List.map json_of_arm
                   (arms_for_row ~family:r.program.E4d_catalog.family
                      ~step_ops:(E4d_catalog.step_ops r.program) name)
               else []
             else []) );
        ( "classified",
          match
            List.find_opt
              (fun (k : E4d_wire.known) -> k.program = r.program.E4d_catalog.name)
              (E4d_wire.parse_known E4d_masks_data.known_text)
          with
          | Some k -> Obj [ ("class", Str k.klass); ("why", Str k.why) ]
          | None -> Null ) ]
  in
  Obj
    (payload
    @ [ ("granularity", Str c.granularity);
        ("scannedFuels", Int c.scanned);
        ("buckets", Int (bucket_count c));
        ("verdicts", List (List.map E4d_wire.json_of_verdict verdicts)) ])

(* ------------------------------------------------------------------------ requests *)

(* The request set is `E4d_alphabet`'s: one list, in the OpSpec rows the `schema` request
   answers with, so `version`'s list and the schema can never disagree. *)
let request_names = E4d_alphabet.names

let version_payload () =
  [ ("protocol", Str protocol);
    ("daemon", Str "effect4d");
    ("host", Str (host_name ()));
    ("ocaml", Str Sys.ocaml_version);
    ("build", Str E4d_pins.build_note);
    ("pin", Obj [ ("effects", Str E4d_pins.pin); ("source", Str "ocaml/server/generated/traces/masks.tsv") ]);
    ("generatorSha256", Str E4d_pins.generator_sha);
    ( "inputs",
      List
        (List.map
           (fun (path, sha) -> Obj [ ("path", Str path); ("sha256", Str sha) ])
           E4d_pins.inputs) );
    ("requests", of_strings request_names);
    ( "leanSources",
      List
        (List.map
           (fun (path, lines) -> Obj [ ("file", Str path); ("lines", Int lines) ])
           E4d_armmap.lean_sources) ) ]

let families_payload () =
  [ ( "families",
      List
        (List.map
           (fun (family, rows) ->
             Obj
               [ ("family", Str family);
                 ( "source",
                   match List.assoc_opt family E4d_families_data.sources with
                   | Some s -> Str s
                   | None -> Null );
                 ("avatar",
                  match List.assoc_opt family E4d_catalog.fixture_families with
                  | Some s -> Str s
                  | None -> Null);
                 ("programs", of_strings (try E4d_catalog.fixture_names family with _ -> []));
                 ( "operations",
                   List
                     (List.map
                        (fun (name, params, answer) ->
                          Obj
                            [ ("name", Str name); ("params", Int params); ("answer", Str answer) ])
                        rows) ) ])
           E4d_families_data.families) );
    ( "extra",
      Obj
        [ ("note",
           Str
             "not a family: the avatar's own programs for the WithFiberAction arms no \
              committed golden reaches (avatar/extra_fixture.ml)");
          ("programs", of_strings (E4d_catalog.fixture_names "extra")) ] );
    ( "corpus",
      Obj
        [ ("note",
           Str
             "not a family: the adversarial corpus, whose steps range over all five \
              alphabets (avatar/corpus/programs.txt)");
          ("programs", Int (List.length (E4d_catalog.corpus_names ()))) ] ) ]

(* One request, over the session. Pure in the session: the answer and the next session are
   returned, nothing is written. *)
let dispatch (s : session) (request : E4d_json.t) : session * (string * E4d_json.t) list =
  let keep payload = (s, payload) in
  let what = str "request" request in
  match what with
  | "ping" -> keep [ ("pong", Bool true) ]
  | "version" | "pins" -> keep (version_payload ())
  | "families" -> keep (families_payload ())
  | "masks" ->
    keep
    [ ( "masks",
        List
          (List.map
             (fun (m : E4d_wire.mask) ->
               Obj
                 [ ("name", Str m.name);
                   ( "keeps",
                     Obj (List.map (fun (k, v) -> (k, Bool v)) m.E4d_wire.keeps) ) ])
             (Lazy.force builtin_masks)) );
      ("source", Str "ocaml/server/generated/traces/masks.tsv") ]
  | "programs" ->
    keep
    [ ( "fixtures",
        List
          (List.map
             (fun (family, _) ->
               Obj
                 [ ("family", Str family);
                   ("programs", of_strings (E4d_catalog.fixture_names family)) ])
             E4d_catalog.fixture_families) );
      ("corpus", of_strings (E4d_catalog.corpus_names ())) ]
  | "schema" ->
    keep
      [ ("requests", E4d_alphabet.json);
        ("properties", E4d_alphabet.properties_json);
        ( "bounds",
          Obj
            [ ("maxInFlight", Int max_in_flight);
              ("journal", Int journal_bound);
              ("maxOpenStreams", Int max_open_streams);
              ("maxStreamItems", Int max_stream_items) ] );
        ("shape", Str "git:c407ab7:Effect4/Target/TypeScript/ScriptFlow.lean:39 OpSpec") ]
  | "streams" ->
    keep
      [ ("streams", List (List.map (fun (_, st) -> E4d_stream.json_of_head st) s.streams));
        ("open", Int (List.length s.streams));
        ("max", Int max_open_streams) ]
  | "pull" -> (
    let id = str "stream" request in
    let cursor = int_ ~default:0 "cursor" request in
    match List.assoc_opt id s.streams with
    | None -> bad "unknown-stream" ("no stream " ^ id)
    | Some st ->
      let st, item = E4d_stream.pull st cursor in
      let streams = (id, st) :: List.remove_assoc id s.streams in
      (* A finished stream is closed on the spot: the terminator is the last thing a client
         gets, and the slot is freed (S5, S3). *)
      let streams = if st.E4d_stream.finished then List.remove_assoc id streams else streams in
      ({ s with streams }, [ ("pull", E4d_stream.json_of_item st item) ]))
  | "reset" ->
    E4d_reset.all ();
    ({ empty_session with journal = s.journal }, [ ("reset", Bool true) ])
  | "load" ->
    let program, tape, rules = resolve s request in
    let default_tape, default_max_ops = E4d_catalog.defaults program in
    let tape = match tape with Some t -> t | None -> default_tape in
    let s, id = remember s program tape rules in
    (s,
    [ ("programId", Str id);
      ("program", Str program.E4d_catalog.label);
      ("family", Str program.E4d_catalog.family);
      ("tape", Str tape);
      ("rules", Str rules);
      ("defaultMaxOps", if default_max_ops = max_int then Null else Int default_max_ops) ])
  | "inspect" ->
    let program, tape, _ = resolve s request in
    let default_tape, default_max_ops = E4d_catalog.defaults program in
    keep
    [ ("inspect", E4d_catalog.inspect program);
      ("tape", Str (match tape with Some t -> t | None -> default_tape));
      ("defaultMaxOps", if default_max_ops = max_int then Null else Int default_max_ops) ]
  | "run" ->
    let r = run_of s request in
    let masks = masks_of request in
    let payload = run_payload r masks in
    let payload =
      match member "expect" request with
      | Null -> payload
      | expect ->
        let reference =
          match expect with
          | Str text -> (E4d_wire.parse_trace text).E4d_wire.rows
          | List _ -> List.filter_map to_string_opt (to_list expect)
          | _ -> bad "bad-expect" "`expect` is a golden's text or an array of row lines"
        in
        payload
        @ [ ( "verdicts",
              List (List.map E4d_wire.json_of_verdict (E4d_wire.compare_all masks reference r.rows)) );
            ( "agree",
              Bool
                (List.for_all
                   (fun (v : E4d_wire.mask_verdict) -> v.agree)
                   (E4d_wire.compare_all masks reference r.rows)) ) ]
    in
    (* Streaming (`chunk: n`): the rows are handed over as a stream instead of inline, and
       the reply carries the stream head and its first item. S3's bound is checked before the
       stream is opened, so an oversize reply is refused and not truncated. *)
    (match to_int_opt (member "chunk" request) with
     | None -> keep payload
     | Some chunk ->
       if List.length r.rows > max_stream_items then
         bad "stream-too-large"
           (Printf.sprintf "%d rows exceeds the %d the session will buffer (S3)"
              (List.length r.rows) max_stream_items)
       else if List.length s.streams >= max_open_streams then
         bad "too-many-streams"
           (Printf.sprintf "%d streams are open; the bound is %d (S3)" (List.length s.streams)
              max_open_streams)
       else begin
         let id = Printf.sprintf "s%d" s.next_stream in
         let st =
           E4d_stream.make ~id ~kind:E4d_stream.Rows ~chunk_size:chunk
             ~items:(List.map (fun row -> E4d_json.Str row) r.rows)
             ~terminal:(json_of_outcome r.outcome)
         in
         let st, first = E4d_stream.pull st 0 in
         let streams = if st.E4d_stream.finished then s.streams else (id, st) :: s.streams in
         ( { s with streams; next_stream = s.next_stream + 1 },
           List.filter (fun (k, _) -> k <> "rows") payload
           @ [ ("stream", E4d_stream.json_of_head st);
               ("first", E4d_stream.json_of_item st first) ] )
       end)
  | "step" ->
    let program, tape, rules = resolve s request in
    let max_ops = to_int_opt (member "maxOps" request) in
    let fuel = int_ ~default:default_fuel "fuel" request in
    let rounds = int_ ~default:0 "rounds" request in
    ignore rules;
    let r = execute_partial program ?tape ?max_ops ~fuel ~rounds () in
    keep
    [ ("program", Str r.program.E4d_catalog.label);
      ("fuel", Int fuel);
      ("rounds", Int rounds);
      ("tape", Str r.tape);
      ("machine", E4d_snapshot.json_of_machine r.machine);
      ("rowsSoFar", of_strings r.rows);
      ("events", List (List.map E4d_snapshot.json_of_event r.events));
      ("outcome", json_of_outcome r.outcome);
      ("complete", Bool (machine_finished r.machine)) ]
  | "reachable" ->
    let program, tape, _ = resolve s request in
    let max_ops = to_int_opt (member "maxOps" request) in
    let fuel = int_ ~default:default_fuel "fuel" request in
    let rounds = int_ ~default:0 "rounds" request in
    let r = execute_partial program ?tape ?max_ops ~fuel ~rounds () in
    keep
    [ ("program", Str r.program.E4d_catalog.label);
      ("fuel", Int fuel);
      ("rounds", Int rounds);
      ("reachable", reachable r.machine) ]
  | "budget" ->
    let r = run_of s request in
    keep
    [ ("program", Str r.program.E4d_catalog.label);
      ("budget", budget r);
      ("rowCount", Int (List.length r.rows));
      ("outcome", json_of_outcome r.outcome) ]
  | "explain" ->
    let r = run_of s request in
    let c = correlate r in
    (* How far the citation chain actually reaches, per run, as a number rather than a
       claim. Seat W1's checkpoint-1 store cases carry no Lean citation of their own and
       inherit none from `store_arm`, so a `ref` or `scope` run resolves its rows to an
       avatar arm and no further; a `fiber` run resolves all the way to `Fibers.lean`. *)
    let explained = explain r c in
    let service =
      List.filter
        (fun row -> List.mem (str "kind" row) [ "op"; "answer"; "failed" ])
        (to_list explained)
    in
    let has_arm row = to_list (member "arms" row) <> [] in
    let has_site row =
      List.exists
        (fun arm ->
          to_list (member "leanDeclarations" arm) <> []
          || List.exists
               (fun c -> to_list (member "sites" c) <> [])
               (to_list (member "citations" arm)))
        (to_list (member "arms" row))
    in
    keep
    [ ("program", Str r.program.E4d_catalog.label);
      ( "citations",
        Obj
          [ ("serviceRows", Int (List.length service));
            ("withArm", Int (List.length (List.filter has_arm service)));
            ("withLeanSite", Int (List.length (List.filter has_site service))) ] );
      ("granularity", Str c.granularity);
      ("scannedFuels", Int c.scanned);
      ("buckets", Int (bucket_count c));
      ( "granularityNote",
        Str
          "`granularity` says which bound the correlation varied: `flush-round` is a sweep \
           of the armed dispatchers and is always a genuine prefix; `drive-command` is one \
           unit of `drive` fuel, finer but not monotone in general; `coarse` is one bucket \
           for the whole run. Rows in the same bucket share their events." );
      ("rows", explained);
      ("outcome", json_of_outcome r.outcome) ]
  | "why" ->
    let r = run_of s request in
    let masks = masks_of request in
    let reference =
      match member "reference" request with
      | Str text -> (E4d_wire.parse_trace text).E4d_wire.rows
      | List _ -> List.filter_map to_string_opt (to_list (member "reference" request))
      | _ -> bad "no-reference" "`why` needs `reference`: rc.112's rows, or a golden's text"
    in
    keep
    [ ("program", Str r.program.E4d_catalog.label);
      ("why", why r reference masks);
      ("rows", of_strings r.rows) ]
  | "diff" ->
    let rows key =
      match member key request with
      | Str text -> (E4d_wire.parse_trace text).E4d_wire.rows
      | List _ -> List.filter_map to_string_opt (to_list (member key request))
      | _ -> bad "bad-diff" ("`diff` needs `" ^ key ^ "`: a golden's text or an array of rows")
    in
    let left = rows "left" and right = rows "right" in
    let masks = masks_of request in
    let known =
      match member "knownText" request with
      | Str text -> E4d_wire.parse_known text
      | _ -> E4d_wire.parse_known E4d_masks_data.known_text
    in
    let name = str "program" request in
    let verdicts = E4d_wire.compare_all masks left right in
    keep
    [ ("verdicts", List (List.map E4d_wire.json_of_verdict verdicts));
      ("agree", Bool (List.for_all (fun (v : E4d_wire.mask_verdict) -> v.agree) verdicts));
      ("leftRows", Int (List.length left));
      ("rightRows", Int (List.length right));
      ( "classified",
        match List.find_opt (fun (k : E4d_wire.known) -> k.program = name) known with
        | Some k -> Obj [ ("class", Str k.klass); ("why", Str k.why) ]
        | None -> Null );
      ( "rule",
        Str
          "ocaml/avatar/compare.py, itself a transcription of \
           effect4-tools/packages/harness/trace.mjs" ) ]
  | "" -> bad "no-request" "every request carries a `request` field"
  | other -> bad "unknown-request" ("unknown request " ^ other)

(* The header a response carries. For a request that names a program it is that program's;
   otherwise the program field is empty and only the provenance rows are meaningful. *)
let header_of (s : session) (request : E4d_json.t) : E4d_json.t * E4d_json.t =
  let label, tape, rules =
    match str "request" request with
    | "run" | "step" | "explain" | "why" | "budget" | "reachable" | "inspect" | "load" -> (
      try
        let program, tape, rules = resolve s request in
        let default_tape, _ = E4d_catalog.defaults program in
        ( program.E4d_catalog.label,
          (match tape with Some t -> t | None -> default_tape),
          rules )
      with _ -> ("", "", ""))
    | _ -> ("", "", "")
  in
  (of_strings (header_lines ~label ~tape ~rules), header_json ~label ~tape ~rules)

(* ------------------------------------------------------------ the state machine

   `step : session -> request -> session * response`. No ambient state, no clock, no
   randomness: everything the daemon remembers is in the session, and everything it answers
   is a function of the session and the request. The transports hold a `session ref` and
   nothing else (properties W1-W5).

   Idempotency (W2): a request carrying a non-null `id` that has already been answered in
   this session gets the recorded reply back and changes nothing, so a client may retry
   safely. The journal holds the last `journal_bound` ids (W5). A request with no `id` is
   never journalled and never deduplicated: an `id` is how a client asks for exactly-once. *)

let journal_key (id : E4d_json.t) : string option =
  match id with
  | Null -> None
  | Str text -> Some ("s:" ^ text)
  | Int n -> Some ("i:" ^ string_of_int n)
  | other -> Some ("j:" ^ E4d_json.to_string other)

let answer_request (s : session) (request : E4d_protocol.request) :
    session * E4d_protocol.response =
  let body = request.E4d_protocol.body in
  let what = request.E4d_protocol.what in
  let rid = request.E4d_protocol.id in
  let host = host_name () in
  try
    let s, payload = dispatch s body in
    let header, header_fields = header_of s body in
    ( s,
      E4d_protocol.ok_response ~what ~rid ~host
        ~header:(List.filter_map to_string_opt (to_list header))
        ~header_fields ~payload )
  with
  | E4d_protocol.Bad_request f -> (s, E4d_protocol.error_response ~what ~rid ~host f)
  | E4d_catalog.Unknown message ->
    (s, E4d_protocol.error_response ~what ~rid ~host
          { kind = "unknown-program"; message })
  | E4d_json.Parse_error message ->
    (s, E4d_protocol.error_response ~what ~rid ~host { kind = "bad-json"; message })
  | Failure message ->
    (s, E4d_protocol.error_response ~what ~rid ~host { kind = "avatar-failure"; message })
  | Stack_overflow ->
    (s, E4d_protocol.error_response ~what ~rid ~host
          { kind = "stack-overflow"; message = "the run exhausted the stack" })
  (* Anything else is a defect of the daemon or of the avatar's machinery (an
     `Invalid_argument`, an unhandled effect, a one-shot continuation resumed twice). It is
     reported, with the exception's name, rather than allowed to end the session: a
     malformed or unlucky request is never fatal (README §1), and the session is unchanged. *)
  | exn ->
    (s, E4d_protocol.error_response ~what ~rid ~host
          { kind = "internal-error"; message = Printexc.to_string exn })

let step (s : session) (request : E4d_protocol.request) : session * E4d_protocol.response =
  match journal_key request.E4d_protocol.id with
  | Some key when List.mem_assoc key s.journal ->
    (* W2: the recorded reply, and the session unchanged. *)
    (s, List.assoc key s.journal)
  | Some key ->
    let s, response = answer_request s request in
    (journal_add s key response, response)
  | None -> answer_request s request

(* One line in, one line out. The parse failure is an error object, not an exception: a
   malformed line never ends a session. *)
let answer (s : session) (line : string) : session * string =
  match E4d_protocol.request_of_line line with
  | Ok request ->
    let s, response = step s request in
    (s, E4d_protocol.line_of_response response)
  | Error failure ->
    ( s,
      E4d_protocol.line_of_response
        (E4d_protocol.error_response ~what:"" ~rid:Null ~host:(host_name ()) failure) )

(* The shell's convenience: one session for the process. `effect4d.ml` and `effect4d_js.ml`
   own it; nothing above this line reads it. *)
let shell : session ref = ref empty_session

let handle_line (line : string) : string =
  let s, out = answer !shell line in
  shell := s;
  out

let handle (request : E4d_json.t) : E4d_json.t =
  let s, response = step !shell (E4d_protocol.request_of_json request) in
  shell := s;
  E4d_protocol.json_of_response response

(* ------------------------------------------------------- the library surface (§4)

   The four calls a caller has without the wire. `run_program` is the one the brief names:
   a program, a tape and a mask table in, the rows and their projections out. *)

type result = {
  result_rows : string list;
  result_header : string list;
  result_projections : (string * string list) list;
  result_events : run_event list;
  result_outcome : outcome;
  result_machine : run_machine;
}

let run_program (program : E4d_catalog.program) (tape : string) (masks : E4d_wire.mask list) :
    result =
  (* The empty tape means "the program's own": a fixture program has no tape and a corpus
     program carries one on its `tape` line, or gets 32 all-`false` entries. Passing `""`
     through as a tape would make the first fork read past the end. *)
  let r = if tape = "" then execute program () else execute program ~tape () in
  { result_rows = r.rows;
    result_header =
      header_lines ~label:r.program.E4d_catalog.label ~tape:r.tape ~rules:r.rules;
    result_projections =
      List.map (fun (m : E4d_wire.mask) -> (m.name, E4d_wire.project m r.rows)) masks;
    result_events = r.events;
    result_outcome = r.outcome;
    result_machine = r.machine }

let masks () = Lazy.force builtin_masks
let program_of_fixture = E4d_catalog.of_fixture
let program_of_corpus = E4d_catalog.of_corpus
