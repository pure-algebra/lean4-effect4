(* `effect4d` on a POSIX host: the native and bytecode transports.

   Newline-delimited JSON on stdin and stdout, one response per request, in order. With
   `--tcp <port>` the same protocol is served on a TCP socket, one connection at a time, and
   each connection is its own session -- which is what makes the protocol's per-session
   properties (README §0, W1-W5) mean what they say.

   The loop itself is `E4d_server_loop.pump`; this module only builds transports. That is the
   seam the Eio swap goes through (`docs/research/2026-09-04-ocaml-packages-plan.md` §2): the
   `transport` record is what `Eio.Buf_read`/`Eio.Net` would construct instead, and nothing
   above it changes.

   The one mutable cell in the daemon is the `session ref` here: `Effect4_daemon.step` is a
   function `session -> request -> session * response`, and the shell is the only place that
   threads it. *)

let usage =
  "effect4d [--tcp PORT] [--once JSON] [--version] [--schema]\n\
  \  (default)   newline-delimited JSON on stdin, one response per line on stdout\n\
  \  --tcp PORT  serve the same protocol on 127.0.0.1:PORT, one connection at a time,\n\
  \              each connection its own session\n\
  \  --once JSON answer one request and exit\n\
  \  --version   print the version response and exit\n\
  \  --schema    print the request alphabet and the stated properties and exit\n"

(* A session, and the `handle` the loop is given. Every connection gets its own. *)
let session_handler () =
  let session = ref Effect4_daemon.empty_session in
  fun line ->
    let next, out = Effect4_daemon.answer !session line in
    session := next;
    out

let stdio_transport () : E4d_server_loop.transport =
  { read = (fun () -> try Some (input_line stdin) with End_of_file -> None);
    write = (fun s -> print_string s; print_newline (); flush stdout);
    close = (fun () -> ()) }

let stdio () = E4d_server_loop.pump ~handle:(session_handler ()) (stdio_transport ())

let tcp port =
  let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt socket Unix.SO_REUSEADDR true;
  Unix.bind socket (Unix.ADDR_INET (Unix.inet_addr_loopback, port));
  Unix.listen socket 8;
  prerr_endline (Printf.sprintf "effect4d listening on 127.0.0.1:%d" port);
  (* One connection at a time (property W4): the avatar keeps module-level state, so two runs
     must not interleave. `accept` blocks until the previous connection has been served. *)
  let rec forever () =
    let client, _ = Unix.accept socket in
    let inbound = Unix.in_channel_of_descr client in
    let outbound = Unix.out_channel_of_descr client in
    let transport : E4d_server_loop.transport =
      { read = (fun () -> try Some (input_line inbound) with End_of_file -> None);
        write =
          (fun s ->
            output_string outbound s;
            output_char outbound '\n';
            flush outbound);
        close = (fun () -> try close_in inbound with _ -> ()) }
    in
    (* A fresh session per connection: the properties are stated per session. *)
    (try E4d_server_loop.pump ~handle:(session_handler ()) transport
     with Sys_error _ | Unix.Unix_error _ -> ());
    transport.close ();
    forever ()
  in
  forever ()

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] -> stdio ()
  | [ "--version" ] -> print_endline (Effect4_daemon.handle_line "{\"request\":\"version\"}")
  | [ "--schema" ] -> print_endline (Effect4_daemon.handle_line "{\"request\":\"schema\"}")
  | [ "--help" ] | [ "-h" ] -> print_string usage
  | [ "--once"; request ] -> print_endline (Effect4_daemon.handle_line request)
  | [ "--tcp"; port ] -> (
    match int_of_string_opt port with
    | Some port -> tcp port
    | None -> prerr_endline usage; exit 2)
  | _ -> prerr_endline usage; exit 2
