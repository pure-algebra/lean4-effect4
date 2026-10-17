(* Kit_serve — the kit's requests and answers, for the command line and its servers (hand-written).

   What it is: one request type for every command (check, admit through check, run, probe,
   frames, outside), its reading from JSON, its answer as JSON, and the two line protocols: JSON
   lines (`eff serve`) and the Model Context Protocol over stdio (`eff mcp`). Each protocol is a
   function from one input line to its output line, so the lane tests it in-process and `eff` is
   a loop around it.
   Depends on: Kit, Kit_machine, Eff_json_text.

   Behaviours it holds itself to:
   S1  Every answer is one JSON object with a "status": the command's own ("ok", "refused",
       "finished", "waiting", "unsettled", "frames", "covered", "outside") or "error" with a
       message.                                                        by construction
   S2  `run` never reports a divergence: a run that the limit leaves cut is "unsettled", a finite
       probe (Kit B2, B3).                                             by construction
   S3  `run` runs the call tree when the program lies in its fragment, and the machine otherwise
       ("via": "machine"). A tree run that settles is run on the machine too, and the answer says
       whether the two agree ("machine": "agrees"); "fast" skips the second run.  tested (T10)
   S4  The MCP protocol answers `initialize`, `ping`, `tools/list` and `tools/call`, replies to no
       notification, and answers any other request with a JSON-RPC error; a tool's answer is the
       command's answer as text, and an unreadable input is the tool's error (`isError`).
                                                                       tested (T10) *)


module J = Eff_json_text

exception Input of string

let input fmt = Printf.ksprintf (fun s -> raise (Input s)) fmt
let read_file f = try In_channel.with_open_bin f In_channel.input_all with Sys_error e -> input "%s" e
let json_of s what = match Kit.Json.parse s with Ok j -> j | Error e -> input "%s: %s" what e

let program_of_json j =
  match Kit.Json.program j with Some p -> p | None -> input "the program's JSON does not read as a program"

let program_of_path path =
  if path = "-" then program_of_json (json_of (In_channel.input_all stdin) "the program")
  else if Filename.check_suffix path ".eff" then
    match Kit.program_of_bytes (read_file path) with
    | Some p -> p
    | None -> input "%s: not the canonical bytes of a program" path
  else program_of_json (json_of (read_file path) path)

let rows_of_json j = match Kit.Json.rows j with Some r -> r | None -> input "the rows do not read as a row table"
let tape_of_json j = match Kit.Json.exits j with Some t -> t | None -> input "the tape does not read as an array of exits"

(* One request: the operation and its fields, from flags or from a JSON line. *)
type request = {
  op : string;
  program : Kit.program option;
  rows : Eff_types.row list;
  tape : Kit.exit list option;
  limit : int;
  budget : int option;
  machine : bool;  (** run on the machine, whatever the fragment *)
  width : int;  (** how many paths `explore` answers *)
  fast : bool;  (** skip the machine's second run *)
}

(* A run's host: the tape when the request gives one, else the host that answers nothing; each
   reply admitted at its call's row (Kit.Host.guarded). The continuation gets the unguarded host
   too, to say why a waiting run waits. *)
type runner = { run : 's. guarded:'s Kit.host -> raw:'s Kit.host -> 's -> J.t }

let with_host app r k =
  match r.tape with
  | Some t -> k.run ~guarded:(Kit.Host.guarded app Kit.Host.tape) ~raw:Kit.Host.tape t
  | None -> k.run ~guarded:Kit.Host.silent ~raw:Kit.Host.silent ()

let path_json path = J.Array (List.map (fun i -> J.Int i) path)

(* A waiting run's answer, with why it waits. *)
let with_wait app raw (run : 's Kit.run) (j : J.t) : J.t =
  match Kit.wait_reason app raw run, j with
  | Some w, J.Object fields -> J.Object (fields @ [ ("why", Kit.Json.wait_json ~app w) ])
  | _ -> j

(* A settled tree run, with the machine's verdict on the same program and host beside it. *)
let cross_checked app r ~raw ~guarded st p (s : 's Kit.settled) (j : J.t) : J.t =
  match s, j with
  | Kit.Settled { run; _ }, J.Object fields when not r.fast ->
    let m = Kit_machine.run app guarded st p in
    let verdict =
      if Kit_machine.agree run m then J.String "agrees"
      else J.Object [ ("disagrees", Kit_machine.json ~app m) ] in
    with_wait app raw run (J.Object (fields @ [ ("machine", verdict) ]))
  | Kit.Settled { run; _ }, _ -> with_wait app raw run j
  | _ -> j

let answer (r : request) : J.t =
  let app = Kit.app ~rows:r.rows () in
  let program () = match r.program with Some p -> p | None -> input "no program" in
  match r.op with
  | "check" -> Kit.Json.check_json app (program ())
  | "outside" ->
    (match Kit.outside (program ()) with
     | None -> J.Object [ ("status", J.String "covered") ]
     | Some path -> J.Object [ ("status", J.String "outside"); ("path", path_json path) ])
  | "run" ->
    let p = program () in
    (match Kit.outside p with
     | Some _ | None when r.machine ->
       with_host app r { run = (fun ~guarded ~raw:_ st -> Kit_machine.json ~app (Kit_machine.run app guarded st p)) }
     | Some path ->
       with_host app r
         { run =
             (fun ~guarded ~raw:_ st ->
               match Kit_machine.json ~app (Kit_machine.run app guarded st p) with
               | J.Object fields ->
                 J.Object (fields @ [ ("outside", path_json path);
                                      ("note", J.String "this node has no arm in the call tree, so the machine ran the program") ])
               | j -> j) }
     | None ->
       with_host app r
         { run =
             (fun ~guarded ~raw st ->
               let s = Kit.settle ~limit:r.limit app guarded st p in
               cross_checked app r ~raw ~guarded st p s (Kit.Json.settled_json ~app s)) })
  | "probe" ->
    let budget = match r.budget with Some k -> k | None -> input "probe needs a budget" in
    with_host app r
      { run =
          (fun ~guarded ~raw st ->
            let run = Kit.probe app ~budget guarded st (program ()) in
            with_wait app raw run (Kit.Json.run_json ~app ~budget run)) }
  | "frames" ->
    with_host app r
      { run =
          (fun ~guarded ~raw:_ st ->
            let frames = Kit.frames app ~limit:r.limit guarded st (program ()) in
            J.Object
              [ ("status", J.String "frames");
                ("frames", J.Array (List.mapi (fun k f -> Kit.Json.run_json ~app ~budget:k f) frames)) ]) }
  | "explore" ->
    let p = program () in
    let budget = match r.budget with Some k -> k | None -> 64 in
    let paths = Kit.explore app ~budget ~width:r.width p in
    let replay (path : Kit.path) =
      (* each finishing or waiting path, replayed on the machine under its own tape *)
      if r.fast then []
      else
        match path.stop with
        | Kit.Stop_cut -> []
        | _ ->
          let tape = Kit.tape_of path in
          let m = Kit_machine.run app (Kit.Host.guarded app Kit.Host.tape) tape p in
          [ ("machine", if Kit_machine.agree_path path m then J.String "agrees" else J.Object [ ("disagrees", Kit_machine.json ~app m) ]) ]
    in
    J.Object
      [ ("status", J.String "paths");
        ("budget", J.Int budget);
        ("paths", J.Array (List.map (fun path ->
             match Kit.Json.path_json ~app path with
             | J.Object fields -> J.Object (fields @ replay path)
             | j -> j) paths)) ]
  | op -> input "unknown operation %S" op

let error_json e = J.Object [ ("status", J.String "error"); ("message", J.String e) ]

(* `eff serve`: one request a line, {"op": …, "program": …, "rows": […], "tape": […], "limit": n,
   "budget": k}; one answer a line. *)
let request_of_json (j : J.t) : request =
  let fields = match j with J.Object f -> f | _ -> input "a request is a JSON object" in
  let field k = List.assoc_opt k fields in
  let int k d = match field k with Some (J.Int n) -> n | None -> d | Some _ -> input "%s is a number" k in
  { op = (match field "op" with Some (J.String s) -> s | _ -> input "a request names its op");
    program = Option.map program_of_json (field "program");
    rows = (match field "rows" with Some j -> rows_of_json j | None -> []);
    tape = Option.map tape_of_json (field "tape");
    limit = int "limit" 1024;
    budget = (match field "budget" with Some (J.Int n) -> Some n | _ -> None);
    machine = (match field "machine" with Some (J.Bool b) -> b | _ -> false);
    width = int "width" 64;
    fast = (match field "fast" with Some (J.Bool b) -> b | _ -> false) }

(* The tools of `eff mcp`, each a command of this module. *)
let tools =
  let obj fields = J.Object fields in
  let str s = J.String s in
  let prop desc ty = obj [ ("type", str ty); ("description", str desc) ] in
  let program = prop "the program as its JSON print, the session tool's form ({\"_tag\":\"bind\",…})" "object" in
  let rows = prop "the application's host rows, an array of row records (name, spelling, shape, kind \"async\", registration \"external\", request, answer, error, …)" "array" in
  let tape = prop "the host's replies in call order, an array of exits ({\"_tag\":\"success\",\"value\":…} or {\"_tag\":\"failure\",\"cause\":…}); with none, every call waits" "array" in
  let schema required props =
    obj [ ("type", str "object");
          ("properties", obj props);
          ("required", J.Array (List.map str required)) ] in
  let tool name desc props required =
    obj [ ("name", str name); ("description", str desc); ("inputSchema", schema required props) ] in
  [ tool "check"
      "Type an Eff program at its application with Lean's checker, natively: its Effect<A, E> type, or the address of the refusing node and why; then program admission (the rows' registration and kind)."
      [ ("program", program); ("rows", rows) ] [ "program" ];
    tool "run"
      "Run an Eff program under a reply tape and report how it stops: finished (with its exit), waiting (the call the host has no reply for, and why), or unsettled (cut at every budget up to the limit: a finite probe, never a divergence). Each call is listed with its request and reply. A program in the call tree's fragment is also run on the machine, and the answer says whether the two agree; any other program runs on the machine."
      [ ("program", program); ("rows", rows); ("tape", tape);
        ("limit", prop "the largest budget to try (default 1024)" "integer");
        ("machine", prop "run on the machine whatever the fragment" "boolean");
        ("fast", prop "skip the machine's second run" "boolean") ] [ "program" ];
    tool "probe"
      "Run an Eff program's call tree at one budget: every loop tests at most `budget` times and definition calls nest at most `budget` deep."
      [ ("program", program); ("rows", rows); ("tape", tape); ("budget", prop "the budget" "integer") ]
      [ "program"; "budget" ];
    tool "frames"
      "The runs of an Eff program at every budget from 0 to `limit`: each frame extends the one before, so they animate as one growing run."
      [ ("program", program); ("rows", rows); ("tape", tape); ("limit", prop "the last budget" "integer") ]
      [ "program"; "limit" ];
    tool "explore"
      "Every path of an Eff program's call tree at a budget, with each host reply drawn from its row's declared types (small members: 0 and 1, \"\" and \"a\", empty and one-item lists, each union member, and failures from the error column). Each path lists its calls, its stop and its tape; each finishing or waiting path is replayed on the machine under its tape, and the answer says whether the two agree."
      [ ("program", program); ("rows", rows);
        ("budget", prop "the budget (default 64)" "integer");
        ("width", prop "the most paths to answer (default 64)" "integer");
        ("fast", prop "skip the machine's replays" "boolean") ] [ "program" ];
    tool "outside"
      "The address of the first node of an Eff program that the call tree has no arm for (a fork, a scope, a service, a layer, a generator), or covered."
      [ ("program", program) ] [ "program" ] ]

(* One JSON-RPC message to its reply, or none for a notification. *)
let mcp_message (msg : J.t) : J.t option =
  let reply id result = J.Object [ ("jsonrpc", J.String "2.0"); ("id", id); ("result", result) ] in
  let failure id code message =
    J.Object [ ("jsonrpc", J.String "2.0"); ("id", id);
               ("error", J.Object [ ("code", J.Int code); ("message", J.String message) ]) ] in
  match msg with
  | J.Object fields ->
    let field k = List.assoc_opt k fields in
    let params = match field "params" with Some (J.Object p) -> p | _ -> [] in
    (match field "method", field "id" with
     | Some (J.String "initialize"), Some id ->
       let version = match List.assoc_opt "protocolVersion" params with Some v -> v | None -> J.String "2025-06-18" in
       Some (reply id (J.Object [ ("protocolVersion", version);
                                  ("capabilities", J.Object [ ("tools", J.Object []) ]);
                                  ("serverInfo", J.Object [ ("name", J.String "effect4-kit"); ("version", J.String "0.1.0") ]) ]))
     | Some (J.String "ping"), Some id -> Some (reply id (J.Object []))
     | Some (J.String "tools/list"), Some id -> Some (reply id (J.Object [ ("tools", J.Array tools) ]))
     | Some (J.String "tools/call"), Some id ->
       let name = match List.assoc_opt "name" params with Some (J.String n) -> n | _ -> "" in
       let args = match List.assoc_opt "arguments" params with Some (J.Object a) -> a | _ -> [] in
       let answer, is_error =
         try (answer (request_of_json (J.Object (("op", J.String name) :: args))), false)
         with Input e -> (error_json e, true)
       in
       Some (reply id (J.Object [ ("content", J.Array [ J.Object [ ("type", J.String "text"); ("text", J.String (Kit.Json.render answer)) ] ]);
                                  ("isError", J.Bool is_error) ]))
     | Some (J.String _), None -> None
     | Some (J.String m), Some id -> Some (failure id (-32601) ("unknown method " ^ m))
     | _, Some id -> Some (failure id (-32600) "not a request")
     | _, None -> None)
  | _ -> Some (failure J.Null (-32600) "not a request")

(* `eff mcp`'s line: one message in, its reply out, or nothing for a notification. *)
let mcp_line (line : string) : string option =
  match Kit.Json.parse line with
  | Error e ->
    Some (Kit.Json.render (J.Object [ ("jsonrpc", J.String "2.0"); ("id", J.Null);
                                      ("error", J.Object [ ("code", J.Int (-32700)); ("message", J.String e) ]) ]))
  | Ok msg -> Option.map Kit.Json.render (mcp_message msg)

(* `eff serve`'s line: one request in, its answer out. *)
let serve_line (line : string) : string =
  Kit.Json.render (try answer (request_of_json (Kit.Json.parse line |> function Ok j -> j | Error e -> raise (Input e))) with Input e -> error_json e)
