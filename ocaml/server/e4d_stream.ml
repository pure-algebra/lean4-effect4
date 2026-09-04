(* Streaming replies, as a carrier rather than as an iterator.

   A large reply -- a corpus run's rows, a long event trace -- does not have to arrive as one
   JSON object. This module is the shape it arrives in instead, and it is deliberately
   *data*: a finite sequence of chunks, a terminator, and a delivery high-water mark, with a
   pure step from a numeric cursor. No closure, no library iterator, no mutable position.

   The shape mirrors rc.112's `Channel`, which is a pull of chunks with a done value
   (`Channel.fromPull`, `Channel.transformPull`, `Channel.DefaultChunkSize` --
   `Effect4/StdLib/Rc112.lean:1636-1642`): a pull answers either a chunk and a continuation,
   or a halt carrying the done value, or a failure. The continuation here is the next cursor,
   which is what makes it a carrier: `pull : t -> int -> t * item` is a total function of two
   first-order arguments, so its Lean counterpart is a `List`, an index and a bound, and
   nothing else. A closure-valued `unit -> step` would have been the same protocol and not
   representable.

   ## The behaviour, stated (README §0, properties S1-S5)

   S1  FIFO. `pull s c` is accepted only for `c = s.delivered`; a smaller cursor is
       `chunk-already-delivered`, a larger one is `out-of-order-pull`. So the chunks of a
       stream arrive in index order and in no other.
   S2  At most once per chunk. `delivered` only ever increases, and the check above refuses a
       cursor below it, so no chunk is delivered twice on the same stream.
   S3  Bounded buffer. A stream holds its whole cut reply and nothing more; `capacity` is the
       bound the session enforces before one is opened (`max_stream_items`), and a reply
       larger than it is refused rather than truncated.
   S4  Back-pressure. Nothing is produced until it is pulled: the chunks are cut once, at
       `make`, and `pull` reads. A client that stops pulling costs the session one stream's
       storage and no work.
   S5  Explicit terminator. The last item of every stream is a `Halt` carrying the reply's
       done value, or a `Fail` carrying the reason. A stream never simply ends. *)

open E4d_json

type kind = Rows | Events

type t = {
  id : string;
  kind : kind;
  chunk_size : int;
  chunks : E4d_json.t list;      (* each is a `List` of the items of that chunk *)
  total_items : int;
  terminal : E4d_json.t;
  delivered : int;               (* the next cursor the stream will accept: S1, S2 *)
  finished : bool;               (* the terminator has been delivered: S5 *)
}

type item =
  | Chunk of { index : int; total : int; items : E4d_json.t }
  | Halt of { index : int; terminal : E4d_json.t }
  | Fail of { index : int; kind : string; message : string }

let kind_name = function Rows -> "rows" | Events -> "events"

(* `Chunk.chunk`: cut a list into runs of at most `size`, in order. *)
let cut (size : int) (items : E4d_json.t list) : E4d_json.t list =
  let size = if size < 1 then 1 else size in
  let rec go acc current count = function
    | [] -> List.rev (if current = [] then acc else E4d_json.List (List.rev current) :: acc)
    | x :: rest ->
      if count = size then go (E4d_json.List (List.rev current) :: acc) [ x ] 1 rest
      else go acc (x :: current) (count + 1) rest
  in
  go [] [] 0 items

let make ~id ~kind ~chunk_size ~items ~terminal : t =
  { id;
    kind;
    chunk_size = (if chunk_size < 1 then 1 else chunk_size);
    chunks = cut chunk_size items;
    total_items = List.length items;
    terminal;
    delivered = 0;
    finished = false }

let chunk_count (s : t) = List.length s.chunks

(* The pull. Total: every cursor gets an item, and the stream that comes back is the one the
   next pull must be made against. *)
let pull (s : t) (cursor : int) : t * item =
  if cursor < s.delivered then
    ( s,
      Fail
        { index = cursor;
          kind = "chunk-already-delivered";
          message =
            Printf.sprintf "chunk %d was delivered; this stream is at %d (S2)" cursor
              s.delivered } )
  else if cursor > s.delivered then
    ( s,
      Fail
        { index = cursor;
          kind = "out-of-order-pull";
          message = Printf.sprintf "this stream is at %d, not %d (S1)" s.delivered cursor } )
  else
    match List.nth_opt s.chunks cursor with
    | Some items ->
      ({ s with delivered = cursor + 1 }, Chunk { index = cursor; total = chunk_count s; items })
    | None ->
      ({ s with delivered = cursor + 1; finished = true },
       Halt { index = cursor; terminal = s.terminal })

let json_of_item (s : t) (i : item) : E4d_json.t =
  match i with
  | Chunk c ->
    Obj
      [ ("stream", Str s.id);
        ("kind", Str (kind_name s.kind));
        ("cursor", Int c.index);
        ("chunks", Int c.total);
        ("more", Bool true);
        ("next", Int (c.index + 1));
        ("items", c.items) ]
  | Halt h ->
    Obj
      [ ("stream", Str s.id);
        ("kind", Str (kind_name s.kind));
        ("cursor", Int h.index);
        ("chunks", Int (chunk_count s));
        ("more", Bool false);
        ("next", Null);
        ("items", List []);
        ("terminal", h.terminal) ]
  | Fail f ->
    Obj
      [ ("stream", Str s.id);
        ("kind", Str (kind_name s.kind));
        ("cursor", Int f.index);
        ("more", Bool false);
        ("error", Obj [ ("kind", Str f.kind); ("message", Str f.message) ]) ]

let json_of_head (s : t) : E4d_json.t =
  Obj
    [ ("stream", Str s.id);
      ("kind", Str (kind_name s.kind));
      ("chunkSize", Int s.chunk_size);
      ("chunks", Int (chunk_count s));
      ("items", Int s.total_items);
      ("delivered", Int s.delivered);
      ("finished", Bool s.finished) ]
