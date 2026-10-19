open Effect4_engine_cas
module Real_unix = Unix
let reject_directory_sync = ref false
let reject_write = ref false
let injected_dir_errors = ref 0
module Fault_unix = struct
  include Unix
  let fsync fd =
    if !reject_directory_sync && (Unix.fstat fd).Unix.st_kind = Unix.S_DIR then
      (incr injected_dir_errors; raise (Unix.Unix_error (Unix.EIO, "fsync", "injected directory")))
    else Unix.fsync fd
  let write_substring fd bytes start length =
    if !reject_write then raise (Unix.Unix_error (Unix.EIO, "write", "injected"))
    else Unix.write_substring fd bytes start length
end
module Control = struct
module Unix = Fault_unix
(* Control-file bytes and root moves. Depends on E4_addr and the byte codecs.
   Properties by construction: exact names, fixed policy/kind, stale-first full-head comparison.
   Properties tested by test_control: v2 bytes (v1 refuses as stale), generations, pins, journal parents,
   framing damage, and generated root goldens. The interface states the wire capacity. *)

(* ---------------------------------------------------------------- the plane *)

type root_policy = E4_root_policy.t =
  | Swap
  | Journal
  | Pin

type head =
  { digest : E4_addr.Addr.t
  ; generation : Z.t
  }

type target =
  { kind : E4_kind.t
  ; digest : E4_addr.Addr.t
  }

type root =
  { name : string
  ; policy : root_policy
  ; kind : E4_kind.t
  ; head : head
  }

type move =
  | Create of string * root_policy * target
  | Advance of string * head * target

type status =
  | Fresh
  | Gced
  | Imported
  | Reserved of int * string

type payload =
  { pack_end : int * int
  ; index_end : int * int
  ; generation : int
  ; scheme_version : int
  ; ledger_generation : int
  ; roots : root list
  ; status : status
  }

type t = payload

let initial : t =
  { pack_end = 0, 0
  ; index_end = 0, 0
  ; generation = 0
  ; scheme_version = 0
  ; ledger_generation = 0
  ; roots = []
  ; status = Fresh
  }
;;

(* ---------------------------------------------------------------- constants *)

let magic = "E4CAS\000"
let version_string = "00000002"
let filename = "control"
let tmp_filename = "control.tmp"
let max_name_length = 65535

(* be64 pack_end_seg/off, index_end_seg/off, generation; be32 checksum, scheme_version,
   ledger_generation, root_count. *)
let fixed_payload_length = (5 * 8) + (4 * 4)
let magic_length = String.length magic
let version_length = String.length version_string
let header_length = magic_length + version_length
let checksum_offset = 40 (* inside the payload *)
let control_path ~dir = Filename.concat dir filename
let tmp_path ~path = path ^ ".tmp"

(* The host limit, amendment M9: a be64 at or above 2^62 is refused, never misread.  On the
   READ side that is `E4_be.read_be64`, which refuses a top byte >= 0x40.  On the WRITE side
   it is free: an OCaml int on this host holds -2^62 .. 2^62-1 (`max_int`), so 2^62 is
   not representable and every non-negative int is already below the bound.  What the writer
   must still refuse is a negative one. *)
let max_wire = max_int (* = 2^62 - 1 on a 64-bit host *)
let max_be32 = 0xFFFFFFFF

(* ---------------------------------------------------------------- names and words *)

let normalise_name name = name

(* Names retain their exact UTF-8 bytes. The control framing bounds their byte length. *)
let valid_name s = String.length s <= 65535 && Eff_frame.utf8_valid s
let root_policy_index = E4_root_policy.byte
let root_policy_of_index = E4_root_policy.of_byte
let root_policy_name = E4_root_policy.name

let root_policy_equal a b =
  match a, b with
  | Swap, Swap | Journal, Journal | Pin, Pin -> true
  | (Swap | Journal | Pin), _ -> false
;;

let head_equal (a : head) (b : head) =
  Z.equal a.generation b.generation && E4_addr.Addr.equal a.digest b.digest
;;

(* An operator word never carries a raw byte: a corrupted version field is arbitrary. *)
let printable (s : string) : string =
  String.map (fun c -> if Char.code c >= 0x20 && Char.code c < 0x7f then c else '?') s
;;

(* ---------------------------------------------------------------- the bytes *)

type open_error =
  | Missing
  | Stale_binary of string
  | Corrupt of string
  | Bad_magic
  | Other_scheme of int

let open_error_word = function
  | Missing -> "missing"
  | Bad_magic -> "badMagic"
  | Stale_binary v -> "staleBinary " ^ printable v
  | Corrupt why -> "corrupt " ^ why
  | Other_scheme n -> "otherScheme " ^ string_of_int n
;;

let add_be64 (b : Buffer.t) (what : string) (n : int) : unit =
  if n < 0 || n > max_wire
  then
    invalid_arg
      (Printf.sprintf "E4_control.encode: %s is not a be64 below 2^62 (M9)" what);
  Buffer.add_string b (E4_be.be64 n)
;;

let add_be32 (b : Buffer.t) (what : string) (n : int) : unit =
  if n < 0 || n > max_be32
  then invalid_arg ("E4_control.encode: " ^ what ^ " does not fit in be32");
  Buffer.add_string b (E4_crc.be32 n)
;;

(* D5: two bytes appear exactly once in the CAS grammar, here. *)
let add_be16 (b : Buffer.t) (what : string) (n : int) : unit =
  if n < 0 || n > 0xFFFF
  then invalid_arg ("E4_control.encode: " ^ what ^ " does not fit in be16");
  Buffer.add_char b (Char.chr ((n lsr 8) land 0xff));
  Buffer.add_char b (Char.chr (n land 0xff))
;;

let read_be16 (s : string) (pos : int) : int option =
  if pos < 0 || pos + 2 > String.length s
  then None
  else Some ((Char.code s.[pos] lsl 8) lor Char.code s.[pos + 1])
;;

let add_root (b : Buffer.t) (r : root) : unit =
  if not (valid_name r.name)
  then
    invalid_arg
      (Printf.sprintf
         "E4_control.encode: root name %S is outside its format domain (wire limit %d \
          bytes)"
         r.name
         max_name_length);
  add_be16 b "root name length" (String.length r.name);
  Buffer.add_string b r.name;
  Buffer.add_char b (Char.chr (root_policy_index r.policy));
  Buffer.add_char b (Char.chr (E4_kind.byte r.kind));
  Buffer.add_string b (E4_addr.Addr.bytes r.head.digest);
  if Z.sign r.head.generation < 0 || Z.gt r.head.generation (Z.of_int max_wire)
  then invalid_arg "E4_control.encode: root generation exceeds wire capacity";
  add_be64 b "root generation" (Z.to_int r.head.generation)
;;

let add_status (b : Buffer.t) (st : status) : unit =
  match st with
  | Fresh -> Buffer.add_char b '\000'
  | Gced -> Buffer.add_char b '\001'
  | Imported -> Buffer.add_char b '\002'
  | Reserved (tag, body) ->
    if tag < 3 || tag > 15
    then
      invalid_arg
        (Printf.sprintf "E4_control.encode: a reserved status tag is 3..15, not %d" tag);
    Buffer.add_char b (Char.chr tag);
    Buffer.add_string b body
;;

(* The payload with the checksum field written as four zero bytes: the string the CRC is
   computed over (CF2). *)
let payload_zeroed (p : payload) : string =
  let b = Buffer.create 256 in
  add_be64 b "pack_end_seg" (fst p.pack_end);
  add_be64 b "pack_end_off" (snd p.pack_end);
  add_be64 b "index_end_seg" (fst p.index_end);
  add_be64 b "index_end_off" (snd p.index_end);
  add_be64 b "generation" p.generation;
  Buffer.add_string b "\000\000\000\000";
  add_be32 b "scheme_version" p.scheme_version;
  add_be32 b "ledger_generation" p.ledger_generation;
  add_be32 b "root_count" (List.length p.roots);
  List.iter (add_root b) p.roots;
  add_status b p.status;
  Buffer.contents b
;;

let encode (p : payload) : string =
  let body = payload_zeroed p in
  let crc = E4_crc.string body in
  let out = Bytes.create (header_length + String.length body) in
  Bytes.blit_string magic 0 out 0 magic_length;
  Bytes.blit_string version_string 0 out magic_length version_length;
  Bytes.blit_string body 0 out header_length (String.length body);
  Bytes.blit_string (E4_crc.be32 crc) 0 out (header_length + checksum_offset) 4;
  Bytes.to_string out
;;

exception Bad of string

let decode (s : string) : (payload, open_error) result =
  let len = String.length s in
  if len < magic_length || String.sub s 0 magic_length <> magic
  then Error Bad_magic
  else if len < header_length
  then Error (Corrupt "truncated: no version field")
  else (
    let v = String.sub s magic_length version_length in
    (* CF1: the version is matched as a string before any field is read. *)
    if v <> version_string
    then Error (Stale_binary v)
    else (
      let plen = len - header_length in
      if plen < fixed_payload_length
      then
        Error
          (Corrupt
             (Printf.sprintf
                "payload is %d bytes, shorter than the %d fixed fields"
                plen
                fixed_payload_length))
      else (
        (* CF2: the checksum is verified BEFORE any field is parsed, so every mutation of the
           payload — including one inside the checksum field itself — is a refusal. *)
        let stored =
          match E4_crc.read_be32 s (header_length + checksum_offset) with
          | Some c -> c
          | None -> 0
        in
        let computed =
          let c = E4_crc.update_sub E4_crc.init s header_length checksum_offset in
          let c = E4_crc.update c "\000\000\000\000" in
          E4_crc.update_sub
            c
            s
            (header_length + checksum_offset + 4)
            (plen - checksum_offset - 4)
        in
        if stored <> computed
        then
          Error
            (Corrupt (Printf.sprintf "checksum 0x%08x, computed 0x%08x" stored computed))
        else (
          try
            let pos = ref header_length in
            let u64 what =
              match E4_be.read_be64 s !pos with
              | None ->
                raise
                  (Bad (Printf.sprintf "%s: not a be64 below 2^62 at offset %d" what !pos))
              | Some n ->
                pos := !pos + 8;
                n
            in
            let u32 what =
              match E4_crc.read_be32 s !pos with
              | None ->
                raise (Bad (Printf.sprintf "%s: truncated be32 at offset %d" what !pos))
              | Some n ->
                pos := !pos + 4;
                n
            in
            let pack_end_seg = u64 "pack_end_seg" in
            let pack_end_off = u64 "pack_end_off" in
            let index_end_seg = u64 "index_end_seg" in
            let index_end_off = u64 "index_end_off" in
            let generation = u64 "generation" in
            let _checksum = u32 "checksum" in
            let scheme_version = u32 "scheme_version" in
            let ledger_generation = u32 "ledger_generation" in
            let root_count = u32 "root_count" in
            let read_root () =
              let name_len =
                match read_be16 s !pos with
                | None ->
                  raise (Bad (Printf.sprintf "truncated root name length at %d" !pos))
                | Some n ->
                  pos := !pos + 2;
                  n
              in
              if !pos + name_len + 34 + 8 > len
              then raise (Bad (Printf.sprintf "truncated root at offset %d" !pos));
              let name = String.sub s !pos name_len in
              pos := !pos + name_len;
              if not (valid_name name)
              then
                raise
                  (Bad
                     (Printf.sprintf
                        "root name %S is outside its format domain (wire limit %d bytes)"
                        name
                        max_name_length));
              let rk =
                match root_policy_of_index (Char.code s.[!pos]) with
                | Some k -> k
                | None ->
                  raise
                    (Bad
                       (Printf.sprintf
                          "unregistered root policy byte %d"
                          (Char.code s.[!pos])))
              in
              incr pos;
              let k =
                match E4_kind.of_byte (Char.code s.[!pos]) with
                | Some k -> k
                | None ->
                  raise
                    (Bad (Printf.sprintf "unregistered kind byte %d" (Char.code s.[!pos])))
              in
              incr pos;
              let digest = E4_addr.Addr.of_digest (String.sub s !pos 32) in
              pos := !pos + 32;
              let version = u64 "root version" in
              { name
              ; policy = rk
              ; kind = k
              ; head = { digest; generation = Z.of_int version }
              }
            in
            let rec take n acc =
              if n = 0 then List.rev acc else take (n - 1) (read_root () :: acc)
            in
            if root_count > len then raise (Bad "root_count is larger than the file");
            let roots = take root_count [] in
            if !pos >= len then raise (Bad "truncated: no status tag");
            let tag = Char.code s.[!pos] in
            let body = String.sub s (!pos + 1) (len - !pos - 1) in
            let st =
              match tag with
              | 0 | 1 | 2 ->
                if body <> ""
                then
                  raise
                    (Bad
                       (Printf.sprintf
                          "status tag %d carries a %d-byte body under version %s"
                          tag
                          (String.length body)
                          version_string));
                if tag = 0 then Fresh else if tag = 1 then Gced else Imported
              (* CF3: a tag this reader does not understand round-trips verbatim. *)
              | n when n >= 3 && n <= 15 -> Reserved (n, body)
              | n -> raise (Bad (Printf.sprintf "unknown status tag %d" n))
            in
            (* CF10: scheme 0 is the one this reader knows; any other is refused, not read. *)
            if scheme_version <> 0
            then Error (Other_scheme scheme_version)
            else
              Ok
                { pack_end = pack_end_seg, pack_end_off
                ; index_end = index_end_seg, index_end_off
                ; generation
                ; scheme_version
                ; ledger_generation
                ; roots
                ; status = st
                }
          with
          | Bad why -> Error (Corrupt why)
          | Invalid_argument why -> Error (Corrupt why)))))
;;

(* ---------------------------------------------------------------- I/O *)

let read_whole (path : string) : string =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))
;;

let read ~path =
  match read_whole path with
  | s -> decode s
  | exception Sys_error why ->
    if Sys.file_exists path then Error (Corrupt why) else Error Missing
  | exception End_of_file -> Error (Corrupt "truncated while reading")
;;

let write_all (fd : Unix.file_descr) (s : string) : unit =
  let n = String.length s in
  let rec go off = if off < n then go (off + Unix.write_substring fd s off (n - off)) in
  go 0
;;

(* CF4: tmp, fsync, rename, fsync the directory.  A crash leaves the old file or the new one. *)
let commit ~path (p : payload) : unit =
  let bytes = encode p in
  let tmp = tmp_path ~path in
  let fd = Unix.openfile tmp [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Fun.protect
    ~finally:(fun () ->
      try Unix.close fd with
      | Unix.Unix_error _ -> ())
    (fun () ->
       write_all fd bytes;
       Unix.fsync fd);
  Unix.rename tmp path;
  (* D7: best effort — a platform that cannot open a directory for fsync still has the
     rename, which is the atomic step. *)
  match Unix.openfile (Filename.dirname path) [ Unix.O_RDONLY ] 0 with
  | dfd ->
    (try Unix.fsync dfd with
     | Unix.Unix_error _ -> ());
    (try Unix.close dfd with
     | Unix.Unix_error _ -> ())
  | exception Unix.Unix_error _ -> ()
;;

let write = commit

let cleanup ~dir =
  let tmp = Filename.concat dir tmp_filename in
  if Sys.file_exists tmp
  then (
    try Sys.remove tmp with
    | Sys_error _ -> ())
;;

(* ---------------------------------------------------------------- the plane, read *)

let root (p : payload) (name : string) : root option =
  let name = normalise_name name in
  List.find_opt (fun r -> String.equal r.name name) p.roots
;;

let roots (p : t) = p.roots
let pack_end (p : t) = p.pack_end
let index_end (p : t) = p.index_end
let generation (p : t) = p.generation
let scheme_version (p : t) = p.scheme_version
let ledger_generation (p : t) = p.ledger_generation
let status (p : t) = p.status

(* ---------------------------------------------------------------- the plane, moved *)

type root_error =
  | No_root of string
  | Stale_root of
      { name : string
      ; expected : head option
      ; actual : head option
      }
  | Pinned of string
  | Dangling of E4_addr.Addr.t
  | Wrong_kind of
      { at : E4_addr.Addr.t
      ; expected : E4_kind.t
      ; actual : E4_kind.t
      }
  | Fork of
      { name : string
      ; head : E4_addr.Addr.t
      ; target : E4_addr.Addr.t
      }

let head_word (value : head option) =
  match value with
  | None -> "none"
  | Some h -> E4_addr.Addr.hex h.digest ^ ":" ^ Z.to_string h.generation
;;

let root_error_word = function
  | No_root name -> "noRoot " ^ name
  | Stale_root { name; expected; actual } ->
    "staleRoot " ^ name ^ " " ^ head_word expected ^ " " ^ head_word actual
  | Pinned name -> "pinned " ^ name
  | Dangling d -> "dangling " ^ E4_addr.Addr.hex d
  | Wrong_kind _ -> "wrongKind"
  | Fork { name; head; target } ->
    "fork " ^ name ^ " " ^ E4_addr.Addr.hex head ^ " " ^ E4_addr.Addr.hex target
;;

let advance_root
      (p : payload)
      ~(resolve : E4_addr.Addr.t -> E4_kind.t option)
      ?(parent = fun _ -> None)
      (move : move)
  : (payload, root_error) result
  =
  let install (r : root) =
    Ok
      { p with
        roots = r :: List.filter (fun q -> not (String.equal q.name r.name)) p.roots
      ; generation = p.generation + 1
      }
  in
  let check_target expected (target : target) =
    if not (E4_kind.equal target.kind expected)
    then Error (Wrong_kind { at = target.digest; expected; actual = target.kind })
    else (
      match resolve target.digest with
      | None -> Error (Dangling target.digest)
      | Some actual when not (E4_kind.equal actual expected) ->
        Error (Wrong_kind { at = target.digest; expected; actual })
      | Some _ -> Ok ())
  in
  match move with
  | Create (name, policy, target) ->
    (match root p name with
     | Some old -> Error (Stale_root { name; expected = None; actual = Some old.head })
     | None ->
       (match check_target target.kind target with
        | Error e -> Error e
        | Ok () ->
          install
            { name
            ; policy
            ; kind = target.kind
            ; head = { digest = target.digest; generation = Z.one }
            }))
  | Advance (name, expected, target) ->
    (match root p name with
     | None -> Error (No_root name)
     | Some old when not (head_equal old.head expected) ->
       Error (Stale_root { name; expected = Some expected; actual = Some old.head })
     | Some old
       when E4_kind.equal target.kind old.kind
            && E4_addr.Addr.equal target.digest old.head.digest -> Ok p
     | Some { policy = Pin; _ } -> Error (Pinned name)
     | Some old ->
       (match check_target old.kind target with
        | Error e -> Error e
        | Ok () ->
          let rec reaches seen address =
            E4_addr.Addr.equal address old.head.digest
            || ((not (List.exists (E4_addr.Addr.equal address) seen))
                &&
                match parent address with
                | None -> false
                | Some previous -> reaches (address :: seen) previous)
          in
          let journal =
            match old.policy with
            | Journal -> true
            | Swap | Pin -> false
          in
          if journal && not (reaches [] target.digest)
          then Error (Fork { name; head = old.head.digest; target = target.digest })
          else
            install
              { old with
                head = { digest = target.digest; generation = Z.succ old.head.generation }
              }))
;;

(* ---------------------------------------------------------------- the watermark *)

let bump (p : t) : t = { p with generation = p.generation + 1 }
let set_pack_end (p : t) (e : int * int) : t = bump { p with pack_end = e }
let set_index_end (p : t) (e : int * int) : t = bump { p with index_end = e }
let set_status (p : t) (st : status) : t = bump { p with status = st }
let set_ledger_generation (p : t) (g : int) : t = bump { p with ledger_generation = g }

end
module Wal = struct
module Unix = Fault_unix
(* E4_wal — implementation.  The interface, the grammar and the deviations are in
   e4_wal.mli; this file adds only what a reader of the code needs.

   Shape: one grammar section (encode / decode of the head and of a row), one walker over the
   bytes of a single segment used by BOTH the reader and the writer's recovery, then the
   writer and the reader over it.  The walker is the only place that decides what damage is,
   so `replay`, `end_index` and `open_`'s recovery cannot drift apart. *)

(* ---------------------------------------------------------------- the grammar *)

let magic = "E4LOG\000"
let version = "00000001"
let head_prefix_length = 30 (* magic 6 + version 8 + job_lo 8 + first 8 *)
let head_length = 34 (* + be32 head_crc *)
let row_header_length = 8 (* be32 row_len + be32 row_crc *)
let body_header_length = 9 (* row_tag + be64 index *)
let row_max = 1 lsl 20
let default_seg_max = 64 * 1024 * 1024
let min_seg_max = head_length + row_header_length + body_header_length
let tag_decision = 1
let tag_event = 2
let tag_checkpoint = 3
let tag_seal = 4

type seq = int

type row =
  | Decision of string
  | Event of string
  | Checkpoint_mark of
      { position : seq
      ; addr : E4_addr.Addr.t option
      }
  | Seal of { next_first_seq : seq }

exception Locked of string
exception Row_too_large of int

let segment_name i = Printf.sprintf "%016x.seg" i
let job_dir ~dir ~job = Filename.concat (Filename.concat dir "log") (E4_addr.Addr.hex job)

(* The LAST eight bytes of the address, as raw bytes (deviation D3: never a be64 number). *)
let job_lo job =
  let b = E4_addr.Addr.bytes job in
  String.sub b (String.length b - 8) 8
;;

let encode_head ~job ~first =
  let p = magic ^ version ^ job_lo job ^ E4_be.be64 first in
  p ^ E4_crc.be32 (E4_crc.string p)
;;

(* (job_lo, first_index) of a well-formed head, or None. *)
let decode_head s =
  if String.length s < head_length
  then None
  else (
    let p = String.sub s 0 head_prefix_length in
    match E4_crc.read_be32 s head_prefix_length with
    | None -> None
    | Some c ->
      if c <> E4_crc.string p
      then None
      else if String.sub p 0 6 <> magic
      then None
      else if String.sub p 6 8 <> version
      then None
      else (
        match E4_be.read_be64 p 22 with
        | None -> None
        | Some first -> Some (String.sub p 14 8, first)))
;;

let body_of_row ~index row =
  let tag, payload =
    match row with
    | Decision s -> tag_decision, s
    | Event s -> tag_event, s
    | Checkpoint_mark { position; addr } ->
      ( tag_checkpoint
      , E4_be.be64 position
        ^
          (match addr with
          | None -> "\000"
          | Some a -> "\001" ^ E4_addr.Addr.bytes a) )
    | Seal { next_first_seq } -> tag_seal, E4_be.be64 next_first_seq
  in
  String.concat "" [ String.make 1 (Char.chr tag); E4_be.be64 index; payload ]
;;

let frame_row body =
  E4_crc.be32 (String.length body) ^ E4_crc.be32 (E4_crc.string body) ^ body
;;

let decode_body body =
  let n = String.length body in
  if n < body_header_length
  then None
  else (
    match E4_be.read_be64 body 1 with
    | None -> None
    | Some index ->
      let payload = String.sub body body_header_length (n - body_header_length) in
      let pn = String.length payload in
      (match Char.code body.[0] with
       | 1 -> Some (index, Decision payload)
       | 2 -> Some (index, Event payload)
       | 3 ->
         if pn < 9
         then None
         else (
           match E4_be.read_be64 payload 0 with
           | None -> None
           | Some position ->
             (match payload.[8] with
              | '\000' when pn = 9 ->
                Some (index, Checkpoint_mark { position; addr = None })
              | '\001' when pn = 9 + 32 ->
                let a = E4_addr.Addr.of_digest (String.sub payload 9 32) in
                Some (index, Checkpoint_mark { position; addr = Some a })
              | _ -> None))
       | 4 ->
         if pn <> 8
         then None
         else (
           match E4_be.read_be64 payload 0 with
           | None -> None
           | Some next -> Some (index, Seal { next_first_seq = next }))
       | _ -> None))
;;

(* ---------------------------------------------------------------- verdicts *)

type stop =
  | Eof
  | Short of seq
  | Bad_crc of seq
  | Bad_row of seq
  | Oversize of
      { at : seq
      ; len : int
      }
  | Gap of
      { expected : seq
      ; found : seq
      }
  | Bad_header of { path : string }
  | Wrong_job of { path : string }

let stop_to_string = function
  | Eof -> "eof: every stored row was delivered"
  | Short i ->
    Printf.sprintf "short: the row at index %d is cut off by the end of its segment" i
  | Bad_crc i -> Printf.sprintf "bad-crc: the row at index %d failed its checksum" i
  | Bad_row i ->
    Printf.sprintf
      "bad-row: the row at index %d is not a row (unknown tag or short body)"
      i
  | Oversize { at; len } ->
    Printf.sprintf
      "oversize: the row at index %d declares %d bytes, above row_max %d"
      at
      len
      row_max
  | Gap { expected; found } ->
    Printf.sprintf "gap: index %d is missing; the next stored row is %d" expected found
  | Bad_header { path } ->
    Printf.sprintf "bad-header: %s is not a segment of this log" path
  | Wrong_job { path } -> Printf.sprintf "wrong-job: %s belongs to another job" path
;;

(* ---------------------------------------------------------------- files *)

let rec mkdir_p path =
  if path = "" || path = "." || Sys.file_exists path
  then ()
  else (
    let parent = Filename.dirname path in
    if parent <> path then mkdir_p parent;
    try Unix.mkdir path 0o755 with
    | Unix.Unix_error (Unix.EEXIST, _, _) -> ())
;;

let fsync_dir path =
  match Unix.openfile path [ Unix.O_RDONLY ] 0 with
  | exception Unix.Unix_error _ -> ()
  | fd ->
    (try Unix.fsync fd with
     | Unix.Unix_error _ -> ());
    Unix.close fd
;;

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))
;;

let rec write_all fd s pos len =
  if len > 0
  then (
    let n = Unix.write_substring fd s pos len in
    write_all fd s (pos + n) (len - n))
;;

let write_string fd s = write_all fd s 0 (String.length s)

let segment_files jd =
  let entries =
    try Sys.readdir jd with
    | Sys_error _ -> [||]
  in
  let out = ref [] in
  Array.iter
    (fun e ->
       if Filename.check_suffix e ".seg"
       then (
         let base = Filename.chop_suffix e ".seg" in
         if String.length base = 16
         then (
           match int_of_string_opt ("0x" ^ base) with
           | Some i when i >= 0 -> out := (i, Filename.concat jd e) :: !out
           | _ -> ())))
    entries;
  List.sort (fun (a, _) (b, _) -> compare (a : int) b) !out
;;

(* ---------------------------------------------------------------- the walker

   One segment's bytes, from its head to the first damage.  [f] is called for every DATA row
   whose index is at least [from]; a Seal is consumed and never delivered (D2). *)

type walk =
  { w_next : seq (* the index after the last good data row *)
  ; w_end : int (* the byte offset just past the last good row *)
  ; w_sealed : seq option (* Some next_first_index when a Seal ended the segment *)
  ; w_stop : stop
  }

let walk_segment ~bytes ~path ~job ~from ~f =
  match decode_head bytes with
  | None -> { w_next = 0; w_end = 0; w_sealed = None; w_stop = Bad_header { path } }
  | Some (lo, first) ->
    if lo <> job_lo job
    then { w_next = first; w_end = 0; w_sealed = None; w_stop = Wrong_job { path } }
    else (
      let n = String.length bytes in
      let pos = ref head_length in
      let index = ref first in
      let last_end = ref head_length in
      let sealed = ref None in
      let stop = ref Eof in
      let go = ref true in
      while !go do
        if !pos >= n
        then go := false
        else if n - !pos < row_header_length
        then (
          stop := Short !index;
          go := false)
        else (
          match E4_crc.read_be32 bytes !pos, E4_crc.read_be32 bytes (!pos + 4) with
          | Some len, Some crc ->
            if len > row_max
            then (
              stop := Oversize { at = !index; len };
              go := false)
            else if n - !pos - row_header_length < len
            then (
              stop := Short !index;
              go := false)
            else (
              let body = String.sub bytes (!pos + row_header_length) len in
              if E4_crc.string body <> crc
              then (
                stop := Bad_crc !index;
                go := false)
              else (
                match decode_body body with
                | None ->
                  stop := Bad_row !index;
                  go := false
                | Some (bi, Seal { next_first_seq }) ->
                  if bi <> !index
                  then (
                    stop := Gap { expected = !index; found = bi };
                    go := false)
                  else if next_first_seq <> !index
                  then (
                    stop := Gap { expected = !index; found = next_first_seq };
                    go := false)
                  else (
                    pos := !pos + row_header_length + len;
                    last_end := !pos;
                    sealed := Some next_first_seq;
                    go := false)
                | Some (bi, r) ->
                  if bi <> !index
                  then (
                    stop := Gap { expected = !index; found = bi };
                    go := false)
                  else (
                    if bi >= from then f bi r;
                    pos := !pos + row_header_length + len;
                    last_end := !pos;
                    incr index)))
          | _ ->
            stop := Short !index;
            go := false)
      done;
      { w_next = !index; w_end = !last_end; w_sealed = !sealed; w_stop = !stop })
;;

(* ---------------------------------------------------------------- the reader *)

type reader =
  { r_dir : string
  ; r_job : E4_addr.Addr.t
  }

let open_reader ~dir ~job = { r_dir = job_dir ~dir ~job; r_job = job }

let addr_of_hex_exn where h =
  match E4_addr.Addr.of_hex h with
  | Some a -> a
  | None -> invalid_arg (where ^ ": the job is not a 32-byte digest in hex")
;;

let open_reader_job ~dir ~job =
  open_reader ~dir ~job:(addr_of_hex_exn "E4_wal.open_reader_job" job)
;;

let close_reader (_ : reader) = ()
let segments r = segment_files r.r_dir

(* LG6: the last segment whose first index is at or below [from]. *)
let start_of (arr : (seq * _) array) (from : seq) =
  let lo = ref 0
  and hi = ref (Array.length arr - 1)
  and start = ref 0 in
  while !lo <= !hi do
    let mid = (!lo + !hi) / 2 in
    if fst arr.(mid) <= from
    then (
      start := mid;
      lo := mid + 1)
    else hi := mid - 1
  done;
  !start
;;

(* The one traversal: (the index one past the last good row, why it stopped). *)
let walk_from r ~from ~f =
  let arr = Array.of_list (segments r) in
  let n = Array.length arr in
  if n = 0
  then 0, Eof
  else (
    let i = ref (start_of arr from) in
    let expected = ref (fst arr.(!i)) in
    let result = ref Eof in
    let go = ref true in
    while !go do
      if !i >= n
      then go := false
      else (
        let first, path = arr.(!i) in
        if first <> !expected
        then (
          result := Gap { expected = !expected; found = first };
          go := false)
        else (
          let bytes = read_file path in
          let w = walk_segment ~bytes ~path ~job:r.r_job ~from ~f in
          expected := w.w_next;
          match w.w_stop with
          | Eof -> incr i
          | s ->
            result := s;
            go := false))
    done;
    !expected, !result)
;;

let replay r ~from ~f = snd (walk_from r ~from ~f)
let end_index r = walk_from r ~from:max_int ~f:(fun _ _ -> ())

let replay_seq r ~from ~verdict =
  let arr = Array.of_list (segments r) in
  let n = Array.length arr in
  let rec at i expected () =
    if i >= n
    then (
      verdict := Eof;
      Seq.Nil)
    else (
      let first, path = arr.(i) in
      if first <> expected
      then (
        verdict := Gap { expected; found = first };
        Seq.Nil)
      else (
        let acc = ref [] in
        let bytes = read_file path in
        let w =
          walk_segment ~bytes ~path ~job:r.r_job ~from ~f:(fun j row ->
            acc := (j, row) :: !acc)
        in
        let rows = List.to_seq (List.rev !acc) in
        match w.w_stop with
        | Eof -> Seq.append rows (at (i + 1) w.w_next) ()
        | s ->
          Seq.append
            rows
            (fun () ->
               verdict := s;
               Seq.Nil)
            ()))
  in
  if n = 0
  then (
    fun () ->
      verdict := Eof;
      Seq.Nil)
  else (
    let s = start_of arr from in
    at s (fst arr.(s)))
;;

exception Enough

let tape r ~from ~upto =
  let acc = ref [] in
  (try
     ignore
       (replay r ~from ~f:(fun i row ->
          if i >= upto
          then raise Enough
          else (
            match row with
            | Decision s -> acc := s :: !acc
            | _ -> ())))
   with
   | Enough -> ());
  List.rev !acc
;;

(* ---------------------------------------------------------------- the writer *)

type t =
  { w_dir : string
  ; w_job : E4_addr.Addr.t
  ; w_seg_max : int
  ; mutable w_fd : Unix.file_descr
  ; mutable w_seg_first : seq
  ; mutable w_seg_bytes : int
  ; mutable w_next : seq
  ; mutable w_durable : seq
  ; w_buf : Buffer.t
  ; w_lock : E4_lock.t
  ; mutable w_closed : bool
  }

(* LG7: the single-writer lock is E4_lock's: an in-process table beside the fcntl lock, under
   one mutex, so a second `open_` in this process, from any domain, raises. *)

let create_segment ~path ~job ~first =
  let fd = Unix.openfile path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_APPEND ] 0o644 in
  write_string fd (encode_head ~job ~first);
  Unix.fsync fd;
  fd
;;

let release_claim t = E4_lock.release t.w_lock

let open_ ~dir ~job ~seg_max =
  if seg_max < min_seg_max
  then
    invalid_arg
      (Printf.sprintf
         "E4_wal.open_: seg_max %d is below min_seg_max %d"
         seg_max
         min_seg_max);
  let jd = job_dir ~dir ~job in
  mkdir_p jd;
  let lock =
    match E4_lock.acquire ~dir:jd with
    | Ok lock -> lock
    | Error _ -> raise (Locked jd)
  in
  let fresh ~first =
    let path = Filename.concat jd (segment_name first) in
    let fd = create_segment ~path ~job ~first in
    fsync_dir jd;
    fd, first, head_length, first
  in
  let fd, seg_first, seg_bytes, next =
    match List.rev (segment_files jd) with
    | [] -> fresh ~first:0
    | (first, path) :: _ ->
      let bytes = read_file path in
      let w = walk_segment ~bytes ~path ~job ~from:max_int ~f:(fun _ _ -> ()) in
      (match w.w_stop with
       | Bad_header _ | Wrong_job _ | Gap _ ->
         E4_lock.release lock;
         failwith ("E4_wal.open_: " ^ stop_to_string w.w_stop)
       | Eof | Short _ | Bad_crc _ | Bad_row _ | Oversize _ ->
         (match w.w_sealed with
          | Some first_of_next -> fresh ~first:first_of_next
          | None ->
            if w.w_end < String.length bytes
            then (
              let tfd = Unix.openfile path [ Unix.O_WRONLY ] 0o644 in
              Unix.ftruncate tfd w.w_end;
              Unix.fsync tfd;
              Unix.close tfd);
            let fd = Unix.openfile path [ Unix.O_WRONLY; Unix.O_APPEND ] 0o644 in
            fd, first, w.w_end, w.w_next))
  in
  { w_dir = jd
  ; w_job = job
  ; w_seg_max = seg_max
  ; w_fd = fd
  ; w_seg_first = seg_first
  ; w_seg_bytes = seg_bytes
  ; w_next = next
  ; w_durable = next
  ; w_buf = Buffer.create 65536
  ; w_lock = lock
  ; w_closed = false
  }
;;

let open_job ~dir ~job ~seg_max =
  open_ ~dir ~job:(addr_of_hex_exn "E4_wal.open_job" job) ~seg_max
;;

let job t = t.w_job
let dir_of t = t.w_dir
let next_seq t = t.w_next
let last_index t = if t.w_next = 0 then None else Some (t.w_next - 1)
let durable_upto t = t.w_durable
let staged_bytes t = Buffer.length t.w_buf

let alive t what =
  if t.w_closed then invalid_arg ("E4_wal." ^ what ^ ": the writer is closed")
;;

let stage t row =
  alive t "stage";
  (match row with
   | Seal _ -> invalid_arg "E4_wal.stage: a Seal is written by rotation, never staged"
   | Decision _ | Event _ | Checkpoint_mark _ -> ());
  let index = t.w_next in
  let body = body_of_row ~index row in
  let n = String.length body in
  if n > row_max then raise (Row_too_large n);
  Buffer.add_string t.w_buf (frame_row body);
  t.w_next <- index + 1;
  index
;;

let append = stage

let flush_buf t =
  if Buffer.length t.w_buf > 0
  then (
    let s = Buffer.contents t.w_buf in
    Buffer.clear t.w_buf;
    write_string t.w_fd s;
    Unix.fsync t.w_fd;
    t.w_seg_bytes <- t.w_seg_bytes + String.length s;
    t.w_durable <- t.w_next)
;;

let do_rotate t =
  let s = frame_row (body_of_row ~index:t.w_next (Seal { next_first_seq = t.w_next })) in
  write_string t.w_fd s;
  Unix.fsync t.w_fd;
  Unix.close t.w_fd;
  let path = Filename.concat t.w_dir (segment_name t.w_next) in
  let fd = create_segment ~path ~job:t.w_job ~first:t.w_next in
  fsync_dir t.w_dir;
  t.w_fd <- fd;
  t.w_seg_first <- t.w_next;
  t.w_seg_bytes <- head_length
;;

let commit t =
  alive t "commit";
  flush_buf t;
  if t.w_seg_bytes >= t.w_seg_max then do_rotate t
;;

let sync = commit

let rotate t =
  alive t "rotate";
  flush_buf t;
  do_rotate t
;;

let checkpoint_mark t position =
  ignore (stage t (Checkpoint_mark { position; addr = None }) : seq);
  commit t
;;

let close t =
  if not t.w_closed
  then (
    flush_buf t;
    (try Unix.close t.w_fd with
     | Unix.Unix_error _ -> ());
    release_claim t;
    t.w_closed <- true)
;;

(* The byte offset at which the row of index [target] begins, walking the same grammar. *)
let offset_of_index bytes ~first ~target =
  let n = String.length bytes in
  let pos = ref head_length
  and idx = ref first
  and found = ref None
  and go = ref true in
  while !go do
    if !idx = target
    then (
      found := Some !pos;
      go := false)
    else if !pos + row_header_length > n
    then go := false
    else (
      match E4_crc.read_be32 bytes !pos with
      | None -> go := false
      | Some len ->
        if !pos + row_header_length + len > n
        then go := false
        else (
          let body = String.sub bytes (!pos + row_header_length) len in
          (match decode_body body with
           | Some (_, (Decision _ | Event _ | Checkpoint_mark _)) -> incr idx
           | Some (_, Seal _) | None -> go := false);
          pos := !pos + row_header_length + len))
  done;
  !found
;;

let truncate_to t target =
  alive t "truncate_to";
  if target > t.w_next || target < t.w_seg_first
  then
    invalid_arg
      (Printf.sprintf
         "E4_wal.truncate_to: %d is outside [%d, %d]"
         target
         t.w_seg_first
         t.w_next);
  Buffer.clear t.w_buf;
  let path = Filename.concat t.w_dir (segment_name t.w_seg_first) in
  let bytes = read_file path in
  match offset_of_index bytes ~first:t.w_seg_first ~target with
  | None -> invalid_arg (Printf.sprintf "E4_wal.truncate_to: no row at index %d" target)
  | Some off ->
    Unix.ftruncate t.w_fd off;
    Unix.fsync t.w_fd;
    t.w_seg_bytes <- off;
    t.w_next <- target;
    t.w_durable <- target
;;

end
let () =
  let root = Sys.argv.(1) in
  Unix.mkdir root 0o700;
  let path = Filename.concat root "control" in
  reject_directory_sync := true;
  Control.commit ~path Control.initial;
  Printf.printf "control commit: returned success after %d injected directory EIO; readable=%b\n%!"
    !injected_dir_errors (match Control.read ~path with Ok _ -> true | Error _ -> false);
  reject_directory_sync := false;
  let dir = Filename.concat root "wal" in
  let job = E4_addr.Addr.of_digest (String.make 32 'w') in
  let w = Wal.open_ ~dir ~job ~seg_max:Wal.default_seg_max in
  ignore (Wal.stage w (Wal.Decision "one"));
  ignore (Wal.stage w (Wal.Decision "two"));
  reject_write := true;
  (try Wal.commit w with e -> Printf.printf "WAL commit failure: %s\n%!" (Printexc.to_string e));
  Printf.printf "WAL after failed write: staged=%d next=%d durable=%d\n%!"
    (Wal.staged_bytes w) (Wal.next_seq w) (Wal.durable_upto w);
  reject_write := false;
  ignore (Wal.stage w (Wal.Decision "three")); Wal.commit w;
  let rd = Wal.open_reader ~dir ~job in
  let n = ref 0 in
  let stop = Wal.replay rd ~from:0 ~f:(fun _ _ -> incr n) in
  Printf.printf "WAL later successful commit: durable=%d replayed=%d stop=%s\n%!"
    (Wal.durable_upto w) !n (Wal.stop_to_string stop);
  Wal.close w
