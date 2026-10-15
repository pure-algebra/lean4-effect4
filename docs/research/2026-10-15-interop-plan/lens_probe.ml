(* The interop plan's two adapter shapes, written by hand in the shape the generator would emit.
   1. Provide: a source row that answers a value (bytes or end of input) becomes a real Eio
      source through one generic method lens; the buffer write is the lens's, not the row's.
   2. Consume: any Eio source becomes a source row, behind a stateful monitor of the row's
      protocol (bounded nonempty chunks, end of input absorbing).
   Finite probe: OCaml 5.1.1, Eio 1.2. *)

let check name condition =
  if not condition then failwith ("FAILED: " ^ name);
  Printf.printf "PASS %s\n%!" name

(* A source row: the operation answers a value, never a buffer mutation. *)
module type SOURCE_ROW = sig
  type t
  val read : t -> int -> string option   (* at most [capacity] bytes; [None] at end of input *)
end

(* The source protocol as a monitor: its state is whether end of input has been answered. *)
module Source_protocol = struct
  type state = { mutable ended : bool }
  let init () = { ended = false }
  let admits st capacity = function
    | None -> true
    | Some bytes -> (not st.ended) && String.length bytes > 0 && String.length bytes <= capacity
  let next st = function None -> st.ended <- true | Some _ -> ()
end

exception Protocol_refused of string

(* 1. The method lens: one generic single_read for every source row. *)
module Provide (R : SOURCE_ROW) = struct
  module Pi = struct
    type t = R.t
    let read_methods = []
    let single_read st dst =
      match R.read st (Cstruct.length dst) with
      | None -> raise End_of_file
      | Some bytes ->
        let n = String.length bytes in
        if n = 0 || n > Cstruct.length dst then raise (Protocol_refused "source row chunk");
        Cstruct.blit_from_string bytes 0 dst 0 n;
        n
  end
  let source (st : R.t) : Eio.Flow.source_ty Eio.Resource.t =
    Eio.Resource.T (st, Eio.Flow.Pi.source (module Pi))
end

(* 2. The consuming adapter: an Eio source as a source row, behind the monitor. *)
module Consume = struct
  type t = { flow : Eio.Flow.source_ty Eio.Resource.t; protocol : Source_protocol.state }
  let of_flow flow = { flow; protocol = Source_protocol.init () }
  let read st capacity =
    let buf = Cstruct.create capacity in
    let answer =
      match Eio.Flow.single_read st.flow buf with
      | n -> Some (Cstruct.to_string (Cstruct.sub buf 0 n))
      | exception End_of_file -> None in
    if not (Source_protocol.admits st.protocol capacity answer) then
      raise (Protocol_refused "provider answer outside the source protocol");
    Source_protocol.next st.protocol answer;
    answer
end

(* A row whose logic is a pure step over its state, as a lowered Lean function would be. *)
module Chunked = struct
  type t = { data : string; chunk : int; mutable pos : int }
  let make ~chunk data = { data; chunk; pos = 0 }
  let read st capacity =
    if st.pos >= String.length st.data then None
    else begin
      let n = min st.chunk (min capacity (String.length st.data - st.pos)) in
      let bytes = String.sub st.data st.pos n in
      st.pos <- st.pos + n;
      Some bytes
    end
end

(* A provider that breaks the protocol: it answers bytes after end of input. *)
module Liar = struct
  type t = { mutable calls : int }
  let read_methods = []
  let single_read st dst =
    st.calls <- st.calls + 1;
    if st.calls = 2 then raise End_of_file;
    Cstruct.blit_from_string "x" 0 dst 0 1; 1
end

module Chunked_source = Provide (Chunked)

let rec drain read st acc =
  match read st 4 with None -> String.concat "" (List.rev acc) | Some b -> drain read st (b :: acc)

let () = Eio_main.run (fun _ ->
  let payload = "line one\nline two\n\000\255end" in
  let out = Buffer.create 64 in
  Eio.Flow.copy (Chunked_source.source (Chunked.make ~chunk:3 payload)) (Eio.Flow.buffer_sink out);
  check "a source row behind the lens feeds the unchanged Eio.Flow.copy" (Buffer.contents out = payload);
  let r = Eio.Buf_read.of_flow ~initial_size:1 ~max_size:64
      (Chunked_source.source (Chunked.make ~chunk:1 payload)) in
  check "the unchanged Eio.Buf_read reads lines through one-byte chunks"
    (Eio.Buf_read.line r = "line one" && Eio.Buf_read.line r = "line two");
  let guarded = Cstruct.of_string "??????" in
  let n = Eio.Flow.single_read (Chunked_source.source (Chunked.make ~chunk:2 "abcdef"))
      (Cstruct.sub guarded 1 4) in
  check "the lens writes exactly the answered prefix into the slice"
    (n = 2 && Cstruct.to_string guarded = "?ab???");
  let dst = Cstruct.of_string "????" in
  let eof = try Eio.Flow.read_exact (Chunked_source.source (Chunked.make ~chunk:1 "ab")) dst; false
    with End_of_file -> true in
  check "read_exact keeps the prefix already written when the row ends early"
    (eof && Cstruct.to_string dst = "ab??");
  let consumed = Consume.of_flow (Eio.Flow.string_source payload) in
  check "a standard Eio source, consumed as a row behind the monitor, answers its bytes"
    (drain Consume.read consumed [] = payload);
  check "the monitor keeps end of input absorbing on an honest provider"
    (Consume.read consumed 4 = None);
  let lying = Consume.of_flow (Eio.Resource.T ({ Liar.calls = 0 }, Eio.Flow.Pi.source (module Liar))) in
  let refused =
    match ignore (Consume.read lying 4); ignore (Consume.read lying 4); ignore (Consume.read lying 4) with
    | () -> false
    | exception Protocol_refused _ -> true in
  check "the monitor refuses bytes answered after end of input (red control)" refused;
  print_endline "ALL LENS AND MONITOR PROBES PASSED")
