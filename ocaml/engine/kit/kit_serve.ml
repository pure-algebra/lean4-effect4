(* Kit_serve — the kit's requests and answers, for the command line and its servers (hand-written).

   What it is: one request type for every command (check, run, explore), its reading from JSON,
   its answer as JSON, and its line protocol, JSON lines (`eff serve`): a function from one input
   line to its output line, so the lane tests it in-process and `eff` is a loop around it. The
   Model Context Protocol face (`eff mcp`) is the authoring tool's (Kit_mcp), not these commands'.
   Depends on: Kit (Kit.Json, the profile's JSON tree).

   Behaviours it holds itself to:
   S1  Every answer is one JSON object with a "status": the command's own ("ok", "refused",
       "finished", "waiting", "unsettled", "stopped", "paths", "outside") or "error" with a
       message.                                                        by construction
   S2  `run` never reports a divergence: a run that the limit leaves cut is "unsettled", a finite
       probe (Kit B2, B3).                                             by construction
   S3  `run` is `Kit.run`: a request never names a runner. The answer says which one answered
       ("via"), and for a settled tree run whether the machine agrees ("machine": "agrees");
       "fast" skips the machine's run.                                 tested (T10) *)

module J = Kit.Json

exception Input of string

let input fmt = Printf.ksprintf (fun s -> raise (Input s)) fmt

let read_file f =
  try In_channel.with_open_bin f In_channel.input_all with
  | Sys_error e -> input "%s" e
;;

let json_of s what =
  match Kit.Json.parse s with
  | Ok j -> j
  | Error e -> input "%s: %s" what e
;;

let program_of_json j =
  match Kit.Json.program j with
  | Some p -> p
  | None -> input "the program's JSON does not read as a program"
;;

let program_of_path path =
  if path = "-"
  then program_of_json (json_of (In_channel.input_all stdin) "the program")
  else if Filename.check_suffix path ".eff"
  then (
    match Kit.program_of_bytes (read_file path) with
    | Some p -> p
    | None -> input "%s: not the canonical bytes of a program" path)
  else program_of_json (json_of (read_file path) path)
;;

let rows_of_json j =
  match Kit.Json.rows j with
  | Some r -> r
  | None -> input "the rows do not read as a row table"
;;

let tape_of_json j =
  match Kit.Json.exits j with
  | Some t -> t
  | None -> input "the tape does not read as an array of exits"
;;

(* One request: the operation and its fields, from flags or from a JSON line. *)
type request =
  { op : string
  ; program : Kit.program option
  ; rows : Eff_types.Row.t list
  ; tape : Kit.exit list option
  ; limit : int
  ; frames : bool (** `run` answers the tree's runs at every budget too *)
  ; budget : int (** the budget `explore` walks the tree at *)
  ; width : int (** how many paths `explore` answers *)
  ; fast : bool (** skip the machine's runs *)
  }

(* A run's host: the tape when the request gives one, else the host that answers nothing. *)
type 'a with_host = { go : 's. 's Kit.reactor -> 's -> 'a }

let with_host r k =
  match r.tape with
  | Some t -> k.go Kit.Reactor.tape t
  | None -> k.go Kit.Reactor.silent ()
;;

let answer (r : request) : J.t =
  let app = Kit.app ~rows:r.rows () in
  let program () =
    match r.program with
    | Some p -> p
    | None -> input "no program"
  in
  match r.op with
  | "check" -> Kit.Json.check_json app (program ())
  | "run" ->
    let p = program () in
    with_host
      r
      { go =
          (fun reactor st ->
            Kit.Json.report_json
              app
              (Kit.run
                 ~limit:r.limit
                 ~frames:r.frames
                 ~check:(not r.fast)
                 app
                 reactor
                 st
                 p))
      }
  | "explore" ->
    let p = program () in
    (match Kit.explore app ~budget:r.budget ~width:r.width p with
     | Error at ->
       J.NatJson_obj
         [ "status", J.NatJson_str "outside"
         ; "path", J.NatJson_arr (List.map (fun i -> J.NatJson_nat i) at)
         ; ( "note"
           , J.NatJson_str
               "explore walks the call tree, and this node has no arm in it (a fork, a \
                scope, a service, a layer); run runs the program on the machine" )
         ]
     | Ok traces ->
       let replay t =
         if r.fast
         then []
         else (
           match Kit.replays app p t with
           | Some b -> [ "machine", J.NatJson_str (if b then "agrees" else "disagrees") ]
           | None -> [])
       in
       J.NatJson_obj
         [ "status", J.NatJson_str "paths"
         ; "budget", J.NatJson_nat r.budget
         ; ( "paths"
           , J.NatJson_arr
               (List.map
                  (fun t ->
                     match Kit.Json.trace_json app t with
                     | J.NatJson_obj fields -> J.NatJson_obj (fields @ replay t)
                     | j -> j)
                  traces) )
         ])
  | op -> input "unknown operation %S (the operations are check, run and explore)" op
;;

let error_json e =
  J.NatJson_obj [ "status", J.NatJson_str "error"; "message", J.NatJson_str e ]
;;

(* `eff serve`: one request a line, {"op": …, "program": …, "rows": […], "tape": […], "limit": n,
   "frames": b, "budget": k, "width": n, "fast": b}; one answer a line. *)
let request_of_json (j : J.t) : request =
  let fields =
    match j with
    | J.NatJson_obj f -> f
    | _ -> input "a request is a JSON object"
  in
  let field k = List.assoc_opt k fields in
  let int k d =
    match field k with
    | Some (J.NatJson_nat n) -> n
    | None -> d
    | Some _ -> input "%s is a number" k
  in
  let flag k =
    match field k with
    | Some (J.NatJson_bool b) -> b
    | None -> false
    | Some _ -> input "%s is true or false" k
  in
  { op =
      (match field "op" with
       | Some (J.NatJson_str s) -> s
       | _ -> input "a request names its op")
  ; program = Option.map program_of_json (field "program")
  ; rows =
      (match field "rows" with
       | Some j -> rows_of_json j
       | None -> [])
  ; tape = Option.map tape_of_json (field "tape")
  ; limit = int "limit" 1024
  ; frames = flag "frames"
  ; budget = int "budget" 64
  ; width = int "width" 64
  ; fast = flag "fast"
  }
;;

(* `eff serve`'s line: one request in, its answer out. *)
let serve_line (line : string) : string =
  Kit.Json.render
    (try
       answer
         (request_of_json
            (Kit.Json.parse line
             |> function
             | Ok j -> j
             | Error e -> raise (Input e)))
     with
     | Input e -> error_json e)
;;
