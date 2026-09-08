(* E4_node — the node envelope and the flat payload walk.  The property list is in
   e4_node.mli.  Every step below carries the Lean line it transcribes. *)

open Effect4_engine

type t = { version : int; kind : E4_kind.t; spec : string; payload : string }

type decode_error =
  | Trailing
  | Bad_version of int
  | Unregistered_kind of int
  | Short_spec
  | Bad_frame
  | Host_limit

type scan = {
  refs : E4_addr.Ref.t list;
  malformed : bool;
  handles : (int * int) list;
}

type pure_refusal =
  | Oversize of decode_error
  | Bad_version_byte of int
  | Malformed_ref
  | Handle_in_content

(* src/Effect4/Store/Node.lean:276 -- `zeroDigest : Digest := ⟨List.replicate 32 0, _⟩`. *)
let zero_digest = String.make 32 '\000'

let header_length = 34                 (* version 1 + kind 1 + spec 32 *)

let make ~version ~kind ~spec ~payload =
  if String.length spec <> E4_addr.Addr.length then
    invalid_arg "E4_node.make: the spec is exactly 32 bytes";
  if version < 0 || version > 255 then invalid_arg "E4_node.make: the version is not a byte";
  { version; kind; spec; payload }

(* src/Effect4/Store/Node.lean:170-171 --
     `def encode (n : Node) : Bytes := n.version :: n.kind.byte :: (n.spec.bytes ++ Val.encode n.payload)` *)
let encode (n : t) : string =
  if String.length n.spec <> E4_addr.Addr.length then
    invalid_arg "E4_node.encode: the spec is exactly 32 bytes";
  if n.version < 0 || n.version > 255 then
    invalid_arg "E4_node.encode: the version is not a byte";
  let plen = String.length n.payload in
  let b = Bytes.create (header_length + plen) in
  Bytes.unsafe_set b 0 (Char.unsafe_chr n.version);
  Bytes.unsafe_set b 1 (Char.unsafe_chr (E4_kind.byte n.kind));
  Bytes.blit_string n.spec 0 b 2 32;
  Bytes.blit_string n.payload 0 b header_length plen;
  Bytes.unsafe_to_string b

(* ------------------------------------------------------------------ the payload walk

   One frame is `tag :: be64 len :: payload` (src/Effect4/Store/Val.lean:147-159, the
   `framed` rule; E4_be.read_frame is the reader).  A region is a byte range that must hold a
   given number of frames back to back: rem = -1 for "as many as fit exactly" (a list's
   elements, a ctor's arguments, Val.lean's `decodeSeq`), 2 for a pair (:595-601), 1 for a
   `some` (:603-606) and for the payload of a node as a whole (`Val.decode` is one tree and
   nothing else, :985).

   Descend only into tags 4, 5, 7, 10.  Tag 8 (`bytes`) is a LEAF: `Val.refs (.bytes bs) = []`
   (Node.lean:250), so a bytes payload that happens to be a valid ref frame yields no ref
   (L-SCAN-2).  Tags 1, 2, 3, 6, 9, 11 and 12 are leaves too. *)

exception Refuse of decode_error

let walk (s : string) ~(pos : int) ~(limit : int) ~(rem : int)
    ~(on_ref : int -> int -> int -> unit) ~(on_handle : int -> int -> unit) : unit =
  let stack = ref [ (pos, limit, rem) ] in
  let rec go () =
    match !stack with
    | [] -> ()
    | (p, l, rm) :: rest ->
      if rm = 0 then begin
        (* the region owes no more frames: anything left over is unconsumed *)
        if p <> l then raise (Refuse Trailing);
        stack := rest;
        go ()
      end
      else if p >= l then begin
        if rm > 0 then raise (Refuse Bad_frame);   (* too few frames for a pair / a some *)
        stack := rest;
        go ()
      end
      else begin
        if p + E4_be.header_length > l then raise (Refuse Bad_frame);
        (* E4_be.read_be64 refuses a length >= 2^62: amendment M9, ND8. *)
        let flen =
          match E4_be.read_be64 s (p + 1) with
          | None -> raise (Refuse Host_limit)
          | Some n -> n
        in
        let st = p + E4_be.header_length in
        if flen > l - st then raise (Refuse Bad_frame);
        let e = st + flen in
        let tag = Char.code (String.unsafe_get s p) in
        let cont = (e, l, if rm < 0 then -1 else rm - 1) in
        let children =
          (* Val.lean:584-622 `decodeBody`, one arm per tag. *)
          if tag = Eff_frame.tag_unit then begin
            if flen <> 0 then raise (Refuse Bad_frame);
            []
          end
          else if tag = Eff_frame.tag_none then begin
            if flen <> 0 then raise (Refuse Bad_frame);
            []
          end
          else if tag = Eff_frame.tag_bool then begin
            if flen <> 1 then raise (Refuse Bad_frame);
            (match String.unsafe_get s st with
             | '\000' | '\001' -> ()
             | _ -> raise (Refuse Bad_frame));
            []
          end
          else if tag = Eff_frame.tag_nat then begin
            (* Val.lean:591: a leading zero digit is a refusal; the value is unbounded (D1). *)
            if flen > 0 && String.unsafe_get s st = '\000' then raise (Refuse Bad_frame);
            []
          end
          else if tag = Eff_frame.tag_string then begin
            (* Val.lean:592 / Utf8.lean:118-153: strict UTF-8, shortest forms, no surrogates. *)
            if not (Eff_frame.utf8_valid (String.sub s st flen)) then raise (Refuse Bad_frame);
            []
          end
          else if tag = Eff_frame.tag_bytes then []          (* a leaf; ND5 *)
          else if tag = Eff_frame.tag_list then [ (st, e, -1) ]
          else if tag = Eff_frame.tag_pair then [ (st, e, 2) ]
          else if tag = Eff_frame.tag_some then [ (st, e, 1) ]
          else if tag = Eff_frame.tag_ctor then begin
            (* Val.lean:607-612: the index is one `nat` frame in shortest form, then the
               arguments back to back. *)
            if st + E4_be.header_length > e then raise (Refuse Bad_frame);
            if Char.code (String.unsafe_get s st) <> Eff_frame.tag_nat then
              raise (Refuse Bad_frame);
            let ilen =
              match E4_be.read_be64 s (st + 1) with
              | None -> raise (Refuse Host_limit)
              | Some n -> n
            in
            let ist = st + E4_be.header_length in
            if ilen > e - ist then raise (Refuse Bad_frame);
            if ilen > 0 && String.unsafe_get s ist = '\000' then raise (Refuse Bad_frame);
            [ (ist + ilen, e, -1) ]
          end
          else if tag = Eff_frame.tag_ref then begin
            (* Val.lean:614-617: the kind byte, then the digest bytes; an empty payload has no
               kind byte and is refused. *)
            if flen < 1 then raise (Refuse Bad_frame);
            on_ref (Char.code (String.unsafe_get s st)) (st + 1) (flen - 1);
            []
          end
          else if tag = Eff_frame.tag_handle then begin
            (* Val.lean:618-621: the kind byte, then the key's nat digits, shortest form. *)
            if flen < 1 then raise (Refuse Bad_frame);
            let dlen = flen - 1 in
            if dlen > 0 && String.unsafe_get s (st + 1) = '\000' then raise (Refuse Bad_frame);
            let key =
              match E4_be.nat_of_digits (String.sub s (st + 1) dlen) with
              | None -> raise (Refuse Host_limit)   (* an index this host cannot have minted *)
              | Some k -> k
            in
            on_handle (Char.code (String.unsafe_get s st)) key;
            []
          end
          else raise (Refuse Bad_frame)             (* tag 0, or 13..255: no such frame *)
        in
        stack := children @ (cont :: rest);
        go ()
      end
  in
  go ()

let no_ref (_ : int) (_ : int) (_ : int) : unit = ()
let no_handle (_ : int) (_ : int) : unit = ()

let payload_ok (p : string) : (unit, decode_error) result =
  match walk p ~pos:0 ~limit:(String.length p) ~rem:1 ~on_ref:no_ref ~on_handle:no_handle with
  | () -> Ok ()
  | exception Refuse e -> Error e

(* Val.refs (Node.lean:241-255) and Val.malformedRef (:260-266) in one pass: a ref frame
   contributes a Ref exactly when its kind byte is registered AND its digest is 32 bytes, and
   is malformed in every other case. *)
let scan_payload (p : string) : (scan, decode_error) result =
  let refs = ref [] and malformed = ref false and handles = ref [] in
  let on_ref kb dstart dlen =
    match E4_kind.of_byte kb with
    | Some k when dlen = E4_addr.Addr.length ->
      refs :=
        E4_addr.Ref.make k (E4_addr.Addr.of_digest (String.sub p dstart dlen)) :: !refs
    | _ -> malformed := true
  in
  let on_handle kb key = handles := (kb, key) :: !handles in
  match walk p ~pos:0 ~limit:(String.length p) ~rem:1 ~on_ref ~on_handle with
  | () ->
    Ok { refs = List.rev !refs; malformed = !malformed; handles = List.rev !handles }
  | exception Refuse e -> Error e

let scan_refs (p : string) : E4_addr.Ref.t list =
  match scan_payload p with Ok s -> s.refs | Error _ -> []

let scan_malformed_ref (p : string) : bool =
  match scan_payload p with Ok s -> s.malformed | Error _ -> false

let scan_handles (p : string) : (int * int) list =
  match scan_payload p with Ok s -> s.handles | Error _ -> []

let refs (n : t) : E4_addr.Ref.t list = scan_refs n.payload
let malformed_ref (n : t) : bool = scan_malformed_ref n.payload
let handles (n : t) : (int * int) list = scan_handles n.payload

(* Node.lean:175-182 `decode`: two header bytes, version 0, a registered kind byte, thirty-two
   spec bytes, then one value tree and nothing else. *)
let decode (s : string) : (t, decode_error) result =
  let len = String.length s in
  if len < 2 then Error Short_spec
  else
    let v = Char.code (String.unsafe_get s 0) in
    if v <> 0 then Error (Bad_version v)
    else
      let kb = Char.code (String.unsafe_get s 1) in
      match E4_kind.of_byte kb with
      | None -> Error (Unregistered_kind kb)
      | Some kind ->
        if len < header_length then Error Short_spec
        else
          let payload = String.sub s header_length (len - header_length) in
          (match payload_ok payload with
           | Error e -> Error e
           | Ok () -> Ok { version = 0; kind; spec = String.sub s 2 32; payload })

(* Node.lean:354 `address` -- sha256 of the node bytes and of nothing else. *)
let address (n : t) : E4_addr.Addr.t = E4_addr.Addr.of_digest (E4_sha256.digest (encode n))

(* Node.lean:291 IsGenesis, :287 edges, :297 checkedEdges. *)
let is_genesis (n : t) : bool =
  E4_kind.equal n.kind E4_kind.Schema && String.equal n.spec zero_digest

let edges (n : t) : E4_addr.Ref.t list =
  E4_addr.Ref.make E4_kind.Schema (E4_addr.Addr.of_digest n.spec) :: refs n

let checked_edges (n : t) : E4_addr.Ref.t list = if is_genesis n then refs n else edges n

(* Store.lean:262-276 `putNode`, the prefix that is a function of the node alone. *)
let oversize (n : t) : bool =
  match payload_ok n.payload with Ok () -> false | Error _ -> true

let bad_version (n : t) : bool = n.version <> 0

let handle_in_content (n : t) : bool =
  E4_kind.is_content n.kind && handles n <> []

let check_pure (n : t) : (unit, pure_refusal) result =
  match payload_ok n.payload with
  | Error e -> Error (Oversize e)                        (* 1, 1' -- payload.WF / M9 *)
  | Ok () ->
    if n.version <> 0 then Error (Bad_version_byte n.version)   (* 2 *)
    else if malformed_ref n then Error Malformed_ref            (* 3 *)
    else if handle_in_content n then Error Handle_in_content    (* 3' -- M2, OQ4's default *)
    else Ok ()
