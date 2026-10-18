(* eff — check, run and watch an Eff program from the command line (a thin driver over Kit).

   What it is: the native kit's command line. Each command reads a program (its JSON print, the
   session tool's form, or its canonical bytes), the application's rows, and a reply tape, and
   answers one JSON object, and `eff serve` answers the same requests as JSON lines. `eff tool`
   serves the authoring tool as JSON lines (Kit_tool), and `eff mcp` serves it as a Model Context
   Protocol server (Kit_mcp), its tool table generated from Lean's request shape.
   Depends on: Effect4_kit.Kit_serve (the commands' requests and answers), Effect4_kit.Kit,
   Effect4_kit.Kit_view, Effect4_kit.Kit_tool, Effect4_kit.Kit_mcp.

   Behaviours it holds itself to:
   E1  Every answer is one JSON object with a "status": the commands' own ("ok", "refused",
       "finished", "waiting", "unsettled", …) or "error" with a message; nothing else is printed
       on stdout.                                                     by construction
   E2  `run` is Kit.run: it never reports a divergence, and a request never names a runner
       (Kit_serve S2, S3).                                            by construction
   E3  The exit code is 0 for an answer, 2 for an "error" (an unreadable input).  by construction
   E4  `eff mcp` is a Model Context Protocol server over stdio (JSON-RPC 2.0, one message a
       line) for the authoring tool: one tool per method, one session for the server's life
       (Kit_mcp M1-M4).                                               tested (test_mcp)

   Usage:
     eff check   PROGRAM [--rows ROWS]
     eff run     PROGRAM [--rows ROWS] [--tape TAPE] [--limit N] [--frames] [--fast]
     eff explore PROGRAM [--rows ROWS] [--budget K] [--width N] [--fast]
     eff view    PROGRAM [--rows ROWS] [--tape TAPE] [--limit N] [--width N] > run.html
     eff serve
     eff tool
     eff mcp
   PROGRAM is a .json file, a .eff file of canonical bytes, or - for JSON on stdin. ROWS is a JSON
   array of row records; TAPE a JSON array of exits (with none, every call waits). *)

open Effect4_kit
open Kit_serve
module J = Eff_json_text

(* `eff view`: the page of a run's frames and the program's paths (Kit_view), on stdout. *)
let view ~title (r : request) : string =
  let app = Kit.app ~rows:r.rows () in
  let p = match r.program with Some p -> p | None -> input "no program" in
  with_host r
    { go = (fun reactor st ->
          let report = Kit.run ~limit:r.limit ~frames:true ~check:false app reactor st p in
          let budget = match report.budget with Some k -> max k 1 | None -> 8 in
          let paths =
            if r.rows = [] then [] else Result.value ~default:[] (Kit.explore app ~budget ~width:r.width p) in
          Kit_view.page (Kit_view.data ~title ~app ~report ~paths ())) }

let lines (f : string -> string option) =
  let rec loop () =
    match In_channel.input_line stdin with
    | None -> ()
    | Some line when String.trim line = "" -> loop ()
    | Some line -> Option.iter (fun out -> print_endline out; flush stdout) (f line); loop ()
  in
  loop ()

let serve () = lines (fun line -> Some (serve_line line))

(* `eff tool`: the authoring tool's JSON lines, served by the generated Tool.serve (Kit_tool). *)
let tool () =
  let session = Kit_tool.create () in
  lines (fun line -> Some (Kit_tool.serve_line session line))
let mcp () =
  let server = Kit_mcp.create () in
  lines (Kit_mcp.line server)

let usage =
  "usage: eff (check|run|explore|view) PROGRAM [--rows ROWS] [--tape TAPE] [--limit N] [--frames] [--budget K] [--width N] [--fast]\n\
  \       eff serve\n\
  \       eff tool\n\
  \       eff mcp"

let () =
  match Array.to_list Sys.argv with
  | [ _; "serve" ] -> serve ()
  | [ _; "tool" ] -> tool ()
  | [ _; "mcp" ] -> mcp ()
  | _ :: op :: path :: flags ->
    let rec parse r = function
      | "--rows" :: f :: rest -> parse { r with rows = rows_of_json (json_of (read_file f) f) } rest
      | "--tape" :: f :: rest -> parse { r with tape = Some (tape_of_json (json_of (read_file f) f)) } rest
      | "--limit" :: n :: rest -> parse { r with limit = int_of_string n } rest
      | "--budget" :: n :: rest -> parse { r with budget = int_of_string n } rest
      | "--frames" :: rest -> parse { r with frames = true } rest
      | "--fast" :: rest -> parse { r with fast = true } rest
      | "--width" :: n :: rest -> parse { r with width = int_of_string n } rest
      | [] -> r
      | flag :: _ -> input "unknown flag %S" flag
    in
    (match
       let r = parse { op; program = Some (program_of_path path); rows = []; tape = None; limit = 1024; frames = false;
                       budget = 64; width = 64; fast = false } flags in
       if op = "view" then `Page (view ~title:(Filename.remove_extension (Filename.basename path)) r) else `Json (answer r)
     with
     | `Page html -> print_string html
     | `Json a -> print_endline (Kit.Json.render a)
     | exception Input e -> print_endline (Kit.Json.render (error_json e)); exit 2
     | exception Failure e -> print_endline (Kit.Json.render (error_json e)); exit 2)
  | _ -> prerr_endline usage; exit 2
