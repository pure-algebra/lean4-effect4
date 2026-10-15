(* Finite probes of native Eio 1.2 provider interfaces.
   Dependencies: Eio_main and Cstruct, OCaml 5.1.1.
   Tested: unchanged standard consumers accept custom providers, and the
   same generic clients accept standard providers; partial I/O is retained.
   This file implements in-memory providers, not an Effect4 machine. *)

let check name condition =
  if not condition then failwith ("FAILED: " ^ name);
  Printf.printf "PASS %s\n%!" name

module Source = struct
  type t = { input : string; limit : int; mutable offset : int; mutable calls : int }
  let make ~limit input =
    if limit < 1 then invalid_arg "source limit";
    { input; limit; offset = 0; calls = 0 }
  let read_methods = []
  let single_read state dst =
    state.calls <- state.calls + 1;
    if state.offset = String.length state.input then raise End_of_file;
    let count = min state.limit
      (min (Cstruct.length dst) (String.length state.input - state.offset)) in
    if count = 0 then invalid_arg "empty read buffer";
    Cstruct.blit_from_string state.input state.offset dst 0 count;
    state.offset <- state.offset + count;
    count
end

module Sink = struct
  type t = { output : Buffer.t; limit : int; mutable calls : int }
  let make ~limit () =
    if limit < 1 then invalid_arg "sink limit";
    { output = Buffer.create 32; limit; calls = 0 }
  let single_write state bufs =
    state.calls <- state.calls + 1;
    let rec send remaining written = function
      | [] -> written
      | _ when remaining = 0 -> written
      | buf :: rest ->
        let count = min remaining (Cstruct.length buf) in
        Buffer.add_string state.output (Cstruct.to_string (Cstruct.sub buf 0 count));
        send (remaining - count) (written + count) rest in
    send state.limit 0 bufs
  let copy state ~src = Eio.Flow.Pi.simple_copy ~single_write state ~src
end

let source state : Eio.Flow.source_ty Eio.Resource.t =
  Eio.Resource.T (state, Eio.Flow.Pi.source (module Source))

let sink state : Eio.Flow.sink_ty Eio.Resource.t =
  Eio.Resource.T (state, Eio.Flow.Pi.sink (module Sink))

(* Both functions retain only the public standard Eio types. *)
let transfer (src : _ Eio.Flow.source) (dst : _ Eio.Flow.sink) = Eio.Flow.copy src dst
let read_line (src : _ Eio.Flow.source) =
  Eio.Buf_read.line (Eio.Buf_read.of_flow ~initial_size:1 ~max_size:1024 src)

type (_, _, _) Eio.Resource.pi +=
  Read_count : ('t, 't -> int, [> `Read_count]) Eio.Resource.pi

let counted_source state : [`R | `Flow | `Read_count] Eio.Resource.t =
  let base = Eio.Resource.bindings (Eio.Flow.Pi.source (module Source)) in
  let ops = Eio.Resource.handler
    (base @ [Eio.Resource.H (Read_count, fun (s : Source.t) -> s.calls)]) in
  Eio.Resource.T (state, ops)

let read_count (Eio.Resource.T (state, ops) : [> `Read_count] Eio.Resource.t) =
  Eio.Resource.get ops Read_count state

module Stream_socket = struct
  type tag = [`Generic]
  type t = {
    input : Source.t;
    output : Sink.t;
    mutable read_closed : bool;
    mutable write_closed : bool;
    mutable closed : bool;
  }
  let make input = {
    input = Source.make ~limit:1 input;
    output = Sink.make ~limit:2 ();
    read_closed = false; write_closed = false; closed = false;
  }
  let ensure_open state = if state.closed then invalid_arg "mock socket closed"
  let read_methods = []
  let single_read state dst =
    ensure_open state;
    if state.read_closed then raise End_of_file;
    Source.single_read state.input dst
  let single_write state bufs =
    ensure_open state;
    if state.write_closed then invalid_arg "mock send side closed";
    Sink.single_write state.output bufs
  let copy state ~src = Eio.Flow.Pi.simple_copy ~single_write state ~src
  let shutdown state = function
    | `Receive -> ensure_open state; state.read_closed <- true
    | `Send -> ensure_open state; state.write_closed <- true
    | `All -> ensure_open state; state.read_closed <- true; state.write_closed <- true
  let close state = state.closed <- true
end

let stream_socket state : [`Generic] Eio.Net.stream_socket_ty Eio.Resource.t =
  Eio.Resource.T (state, Eio.Net.Pi.stream_socket (module Stream_socket))

let () = Eio_main.run (fun _ ->
  let binary = "a\000b\255\194\163\nend" in
  let first = Source.make ~limit:1 binary in
  let output = Buffer.create 32 in
  transfer (source first) (Eio.Flow.buffer_sink output);
  check "custom source to unchanged standard Eio sink" (Buffer.contents output = binary);
  check "custom source actually performs partial reads" (first.calls > 2);

  let second = Sink.make ~limit:2 () in
  transfer (Eio.Flow.string_source binary) (sink second);
  check "unchanged standard Eio source to custom sink" (Buffer.contents second.output = binary);
  check "custom sink actually performs partial writes" (second.calls > 1);

  let third = Source.make ~limit:3 binary and fourth = Sink.make ~limit:1 () in
  transfer (source third) (sink fourth);
  check "same generic client copies between two custom providers"
    (Buffer.contents fourth.output = binary);
  let standard_output = Buffer.create 32 in
  transfer (Eio.Flow.string_source binary) (Eio.Flow.buffer_sink standard_output);
  check "same generic client copies between two standard providers"
    (Buffer.contents standard_output = binary);

  check "standard Buf_read consumes custom one-byte source"
    (read_line (source (Source.make ~limit:1 "\206\177\206\178\n")) = "\206\177\206\178");
  check "same buffered client consumes standard Eio provider"
    (read_line (Eio.Flow.string_source "\206\177\206\178\n") = "\206\177\206\178");

  let short = Source.make ~limit:1 "ab" in
  let dst = Cstruct.of_string "????" in
  let eof = try Eio.Flow.read_exact (source short) dst; false with End_of_file -> true in
  check "read_exact reports EOF while retaining the prefix already read"
    (eof && Cstruct.to_string dst = "ab??");

  let partial = Source.make ~limit:2 "abcdef" in
  let guarded = Cstruct.of_string "??????" in
  let count = Eio.Flow.single_read (source partial) (Cstruct.sub guarded 1 4) in
  check "partial read updates only its written slice"
    (count = 2 && Cstruct.to_string guarded = "?ab???");

  let vector_sink = Sink.make ~limit:2 () in
  Eio.Flow.write (sink vector_sink)
    [Cstruct.of_string "a"; Cstruct.of_string "bc"; Cstruct.of_string "def"];
  check "standard vectored write retries partial provider writes"
    (Buffer.contents vector_sink.output = "abcdef" && vector_sink.calls = 3);

  let observed = counted_source (Source.make ~limit:1 binary) in
  let observed_output = Buffer.create 32 in
  transfer observed (Eio.Flow.buffer_sink observed_output);
  check "custom typed method coexists with unchanged standard Flow consumer"
    (Buffer.contents observed_output = binary && read_count observed > 1);

  let socket_state = Stream_socket.make binary in
  let socket = stream_socket socket_state in
  let socket_output = Buffer.create 32 in
  transfer socket (Eio.Flow.buffer_sink socket_output);
  Eio.Flow.copy_string "request" socket;
  Eio.Flow.shutdown socket `Send;
  check "Net stream provider exposes the standard source sink and shutdown facets"
    (Buffer.contents socket_output = binary &&
      Buffer.contents socket_state.output.output = "request" && socket_state.write_closed);
  Eio.Net.close socket;
  Eio.Net.close socket;
  let closed = try ignore (Eio.Flow.single_read socket (Cstruct.create 1)); false
    with Invalid_argument _ -> true in
  check "standard Net.close dispatches to the mock resource lifecycle" closed;
  print_endline "ALL NATIVE FLOW INTERFACE PROBES PASSED")
