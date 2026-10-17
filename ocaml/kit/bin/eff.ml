(* eff — check, run and watch an Eff program from the command line (a thin driver over Kit).

   What it is: the native kit's command line. Each command reads a program (its JSON print, the
   session tool's form, or its canonical bytes), the application's rows, and a reply tape, and
   answers one JSON object. `eff serve` answers the same requests as JSON lines.
   Depends on: Effect4_kit.Kit_serve (every request and answer), Effect4_kit.Kit.

   Behaviours it holds itself to:
   E1  Every answer is one JSON object with a "status": the commands' own ("ok", "refused",
       "finished", "waiting", "unsettled", …) or "error" with a message; nothing else is printed
       on stdout.                                                     by construction
   E2  `run` never reports a divergence: a run that the limit leaves cut is "unsettled", a finite
       probe (Kit B2, B3).                                            by construction
   E3  The exit code is 0 for an answer, 2 for an "error" (an unreadable input).  by construction
   E5  `eff mcp` is a Model Context Protocol server over stdio (JSON-RPC 2.0, one message a
       line): `initialize`, `tools/list` and `tools/call` for check, run, probe, frames and
       outside, whose arguments are `eff serve`'s request fields; each result is the command's
       answer as text.                                                  by construction
   E4  `run` runs the call tree when the program lies in its fragment, and the machine otherwise
       ("via": "machine"). A tree run that settles is run on the machine too, and the answer says
       whether the two agree ("machine": "agrees"); `--fast` skips the second run.
                                                                        by construction

   Usage:
     eff check  PROGRAM [--rows ROWS]
     eff run    PROGRAM [--rows ROWS] [--tape TAPE] [--limit N] [--machine] [--fast]
     eff probe  PROGRAM --budget K [--rows ROWS] [--tape TAPE]
     eff frames PROGRAM [--rows ROWS] [--tape TAPE] [--limit N]
     eff explore PROGRAM [--rows ROWS] [--budget K] [--width N] [--fast]
     eff outside PROGRAM
     eff serve
     eff mcp
   PROGRAM is a .json file, a .eff file of canonical bytes, or - for JSON on stdin. ROWS is a JSON
   array of row records; TAPE a JSON array of exits (with none, every call waits). *)

open Effect4_kit
open Kit_serve
module J = Eff_json_text

let lines (f : string -> string option) =
  let rec loop () =
    match In_channel.input_line stdin with
    | None -> ()
    | Some line when String.trim line = "" -> loop ()
    | Some line -> Option.iter (fun out -> print_endline out; flush stdout) (f line); loop ()
  in
  loop ()

let serve () = lines (fun line -> Some (serve_line line))
let mcp () = lines mcp_line

let usage =
  "usage: eff (check|run|probe|frames|explore|outside) PROGRAM [--rows ROWS] [--tape TAPE] [--limit N] [--budget K]\n\
  \       eff serve\n\
  \       eff mcp"

let () =
  match Array.to_list Sys.argv with
  | [ _; "serve" ] -> serve ()
  | [ _; "mcp" ] -> mcp ()
  | _ :: op :: path :: flags ->
    let rec parse r = function
      | "--rows" :: f :: rest -> parse { r with rows = rows_of_json (json_of (read_file f) f) } rest
      | "--tape" :: f :: rest -> parse { r with tape = Some (tape_of_json (json_of (read_file f) f)) } rest
      | "--limit" :: n :: rest -> parse { r with limit = int_of_string n } rest
      | "--budget" :: n :: rest -> parse { r with budget = Some (int_of_string n) } rest
      | "--machine" :: rest -> parse { r with machine = true } rest
      | "--fast" :: rest -> parse { r with fast = true } rest
      | "--width" :: n :: rest -> parse { r with width = int_of_string n } rest
      | [] -> r
      | flag :: _ -> input "unknown flag %S" flag
    in
    (match
       answer
         (parse { op; program = Some (program_of_path path); rows = []; tape = None; limit = 1024; budget = None;
                  machine = false; fast = false; width = 64 } flags)
     with
     | a -> print_endline (Kit.Json.render a)
     | exception Input e -> print_endline (Kit.Json.render (error_json e)); exit 2
     | exception Failure e -> print_endline (Kit.Json.render (error_json e)); exit 2)
  | _ -> prerr_endline usage; exit 2
