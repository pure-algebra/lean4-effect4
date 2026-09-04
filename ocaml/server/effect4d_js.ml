(* `effect4d` under js_of_ocaml 5.7.1 `--enable effects`, running on node.

   Two jobs, both of them the same daemon:

   1. the transport. Newline-delimited JSON, read from stdin and written to stdout, exactly
      as `effect4d.ml` does on a POSIX host. The line reader is `fs.readSync` on fd 0, which
      blocks on a pipe, so this is a live session and not a batch; end of file comes back as
      the sentinel "\000", because the boundary carries strings only.

   2. the module. Every request handler is registered as a JavaScript function on
      `module.exports`, so `require("./effect4d.js")` gives a JavaScript caller the same
      surface an OCaml caller has through `Effect4_daemon`. This is the deliverable-4
      demonstration, and it is the interesting one under `--enable effects`: spike A0's
      probe C found that a `perform` inside an OCaml callback invoked from JS is `Unhandled`,
      because `caml_callback` saves and replaces `caml_fiber_stack` with a fresh one-frame
      fiber (`jslib.js:70-113`). It works here because the avatar installs its own handler
      *inside* the callback -- `run_under_handler`'s `match_with` runs on the fresh fiber, and
      every `perform` the fiber bodies make is under it. A JS caller that tried to perform
      across the boundary would still be `Unhandled`; a JS caller that asks the daemon to run
      a program is not crossing it.

   The externals are implemented in `server_runtime.js` and linked with `ocamlc
   -no-check-prims`, the pattern `ocaml/probes/promise/build-ocaml.sh` uses. *)

external register : string -> (string -> string) -> unit = "e4d_register"
external read_line_raw : unit -> string = "e4d_read_line"
external write_line : string -> unit = "e4d_write_line"
external is_main : unit -> bool = "e4d_is_main"

let read_line () : string option =
  match read_line_raw () with
  | "\000" -> None
  | line ->
    let n = String.length line in
    Some (if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line)

(* The exported surface. Each is `string -> string` over JSON text, which is the one shape
   that crosses the boundary without a value-representation question (spike O3 §7: an int or
   a string is the safe profile). A JavaScript caller that wants objects parses the answer
   with `JSON.parse`, which `tests/node_module_demo.mjs` does. *)
let exports () =
  register "request" Effect4_daemon.handle_line;
  register "version" (fun _ -> Effect4_daemon.handle_line "{\"request\":\"version\"}");
  register "families" (fun _ -> Effect4_daemon.handle_line "{\"request\":\"families\"}");
  register "programs" (fun _ -> Effect4_daemon.handle_line "{\"request\":\"programs\"}");
  (* `run_program : program -> tape -> masks -> result`, the library call of deliverable 4,
     with its three arguments in one JSON object so it crosses the boundary as one string. *)
  register "runProgram" (fun argument ->
      let request = E4d_json.of_string argument in
      let family = E4d_json.str "family" request in
      let program = E4d_json.str "program" request in
      let tape = E4d_json.str "tape" request in
      let masks =
        match E4d_json.strings "masks" request with
        | [] -> Effect4_daemon.masks ()
        | wanted ->
          List.filter (fun (m : E4d_wire.mask) -> List.mem m.name wanted) (Effect4_daemon.masks ())
      in
      let result =
        Effect4_daemon.run_program (Effect4_daemon.program_of_fixture family program) tape masks
      in
      E4d_json.to_string
        (Obj
           [ ("ok", Bool true);
             ("host", Str (Effect4_daemon.host_name ()));
             ("header", E4d_json.of_strings result.Effect4_daemon.result_header);
             ("rows", E4d_json.of_strings result.Effect4_daemon.result_rows);
             ( "projections",
               Obj
                 (List.map
                    (fun (name, rows) -> (name, E4d_json.of_strings rows))
                    result.Effect4_daemon.result_projections) );
             ("outcome", Effect4_daemon.json_of_outcome result.Effect4_daemon.result_outcome) ]))

let () =
  exports ();
  (* Required as a module, the program only registers its exports. Run as `node
     effect4d.js`, it also pumps stdin -- through the same `E4d_server_loop.pump` the POSIX
     transport uses, over a transport built from the two JavaScript externals. *)
  if is_main () then begin
    let session = ref Effect4_daemon.empty_session in
    let handle line =
      let next, out = Effect4_daemon.answer !session line in
      session := next;
      out
    in
    E4d_server_loop.pump ~handle
      { read = read_line; write = write_line; close = (fun () -> ()) }
  end
