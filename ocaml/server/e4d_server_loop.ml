(* The server loop, with the transport as a parameter.

   The daemon's three transports -- stdin/stdout on a POSIX host, a TCP connection, and
   stdin/stdout under node -- differ only in how a line is read and written. `pump` is the
   loop over any of them, and holds the only rule the protocol has about ordering: one
   request, one response, in order, and a blank line is skipped rather than answered.

   ## The swap to Eio (`docs/research/2026-09-04-ocaml-packages-plan.md`)

   This module is the seam. `Eio` replaces the *construction* of a `transport` and nothing
   else:

     the loop        `pump` stays as it is. It performs no I/O of its own; the transport
                     does. Under Eio it runs inside `Eio_main.run` in a fiber.
     stdio           `{ read; write }` over `Eio.Buf_read.line` and `Eio.Flow.copy_string`
                     on `Eio.Stdenv.stdin`/`stdout`, instead of `input_line`/`print_string`.
     tcp             `Eio.Net.listen` + `Eio.Net.accept_fork` in place of the `Unix.socket`
                     dance in `effect4d.ml`, at which point `serve_forever` below is a
                     `Switch` and several connections can be served at once -- which the
                     avatar's module-level state does not currently allow (README §7.4), so
                     the Eio version must either keep a mutex around `handle` or wait for the
                     avatar's state to become a parameter.
     node            unchanged: Eio has no js_of_ocaml backend, so `effect4d_js.ml` keeps its
                     `fs.readSync` transport and this same `pump`.

   Nothing above `transport` knows which one it has. *)

type transport = {
  read : unit -> string option;  (* `None` at end of input *)
  write : string -> unit;        (* one line, newline and flush included *)
  close : unit -> unit;
}

(* One request, one response, in order. A blank line is skipped; a malformed one is answered
   with an error object by `handle`, never by closing the connection. *)
let pump ~(handle : string -> string) (t : transport) : unit =
  let rec go () =
    match t.read () with
    | None -> ()
    | Some line -> if String.trim line = "" then go () else (t.write (handle line); go ())
  in
  go ()

(* Serve one transport at a time, for as long as `accept` keeps producing them. The avatar
   keeps module-level state, so two runs must not interleave: this is deliberately a
   sequential loop and not a fork per connection. *)
let serve_forever ~(handle : string -> string) ~(accept : unit -> transport option) : unit =
  let rec go () =
    match accept () with
    | None -> ()
    | Some t ->
      (try pump ~handle t with Sys_error _ -> ());
      t.close ();
      go ()
  in
  go ()
