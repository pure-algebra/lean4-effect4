(* E4_control — the control file.  The grammar, the behaviour list and the deviations are in
   e4_control.mli; this file is the transcription and nothing else. *)

open Effect4_engine

(* ---------------------------------------------------------------- the plane *)

type root_kind = Stdlib | Journal | Daemon | Schema | Char | Registry | Pin

type root = {
  name : string;
  root_kind : root_kind;
  kind : E4_kind.t;
  digest : E4_addr.Addr.t;
  version : int;
}

type status = Fresh | Gced | Imported | Reserved of int * string

type payload = {
  pack_end : int * int;
  index_end : int * int;
  generation : int;
  scheme_version : int;
  ledger_generation : int;
  roots : root list;
  status : status;
}

type t = payload

let initial : t =
  {
    pack_end = (0, 0);
    index_end = (0, 0);
    generation = 0;
    scheme_version = 0;
    ledger_generation = 0;
    roots = [];
    status = Fresh;
  }

(* ---------------------------------------------------------------- constants *)

let magic = "E4CAS\000"
let version_string = "00000001"
let filename = "control"
let tmp_filename = "control.tmp"
let max_name_length = 512

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
   it is free: an OCaml int on this host holds -2^62 .. 2^62-1 (`E4_nat.max_nat`), so 2^62 is
   not representable and every non-negative int is already below the bound.  What the writer
   must still refuse is a negative one. *)
let max_wire = max_int (* = 2^62 - 1 on a 64-bit host *)
let max_be32 = 0xFFFFFFFF

(* ---------------------------------------------------------------- names and words *)

let normalise_name = String.lowercase_ascii

let valid_name (s : string) : bool =
  let n = String.length s in
  n >= 1 && n <= max_name_length
  &&
  let ok = ref true in
  String.iter
    (fun c ->
      let b = Char.code c in
      if b < 0x21 || b > 0x7e || (b >= Char.code 'A' && b <= Char.code 'Z') then ok := false)
    s;
  !ok

let root_kind_index = function
  | Stdlib -> 0
  | Journal -> 1
  | Daemon -> 2
  | Schema -> 3
  | Char -> 4
  | Registry -> 5
  | Pin -> 6

let root_kind_of_index = function
  | 0 -> Some Stdlib
  | 1 -> Some Journal
  | 2 -> Some Daemon
  | 3 -> Some Schema
  | 4 -> Some Char
  | 5 -> Some Registry
  | 6 -> Some Pin
  | _ -> None

let root_kind_name = function
  | Stdlib -> "stdlib"
  | Journal -> "journal"
  | Daemon -> "daemon"
  | Schema -> "schema"
  | Char -> "char"
  | Registry -> "registry"
  | Pin -> "pin"

let status_tag = function
  | Fresh -> 0
  | Gced -> 1
  | Imported -> 2
  | Reserved (n, _) -> n

(* An operator word never carries a raw byte: a corrupted version field is arbitrary. *)
let printable (s : string) : string =
  String.map (fun c -> if Char.code c >= 0x20 && Char.code c < 0x7f then c else '?') s

(* ---------------------------------------------------------------- the bytes *)

type open_error =
  | Missing
  | Stale_binary of string
  | Corrupt of string
  | Bad_magic

let open_error_word = function
  | Missing -> "missing"
  | Bad_magic -> "badMagic"
  | Stale_binary v -> "staleBinary " ^ printable v
  | Corrupt why -> "corrupt " ^ why

let add_be64 (b : Buffer.t) (what : string) (n : int) : unit =
  if n < 0 || n > max_wire then
    invalid_arg (Printf.sprintf "E4_control.encode: %s is not a be64 below 2^62 (M9)" what);
  Buffer.add_string b (E4_be.be64 n)

let add_be32 (b : Buffer.t) (what : string) (n : int) : unit =
  if n < 0 || n > max_be32 then
    invalid_arg ("E4_control.encode: " ^ what ^ " does not fit in be32");
  Buffer.add_string b (E4_crc.be32 n)

(* D5: two bytes appear exactly once in the CAS grammar, here. *)
let add_be16 (b : Buffer.t) (what : string) (n : int) : unit =
  if n < 0 || n > 0xFFFF then invalid_arg ("E4_control.encode: " ^ what ^ " does not fit in be16");
  Buffer.add_char b (Char.chr ((n lsr 8) land 0xff));
  Buffer.add_char b (Char.chr (n land 0xff))

let read_be16 (s : string) (pos : int) : int option =
  if pos < 0 || pos + 2 > String.length s then None
  else Some ((Char.code s.[pos] lsl 8) lor Char.code s.[pos + 1])

let add_root (b : Buffer.t) (r : root) : unit =
  if not (valid_name r.name) then
    invalid_arg
      (Printf.sprintf "E4_control.encode: root name %S is not 1..%d lowercase printable ASCII"
         r.name max_name_length);
  add_be16 b "root name length" (String.length r.name);
  Buffer.add_string b r.name;
  Buffer.add_char b (Char.chr (root_kind_index r.root_kind));
  Buffer.add_char b (Char.chr (E4_kind.byte r.kind));
  Buffer.add_string b (E4_addr.Addr.bytes r.digest);
  add_be64 b "root version" r.version

let add_status (b : Buffer.t) (st : status) : unit =
  match st with
  | Fresh -> Buffer.add_char b '\000'
  | Gced -> Buffer.add_char b '\001'
  | Imported -> Buffer.add_char b '\002'
  | Reserved (tag, body) ->
    if tag < 3 || tag > 15 then
      invalid_arg
        (Printf.sprintf "E4_control.encode: a reserved status tag is 3..15, not %d" tag);
    Buffer.add_char b (Char.chr tag);
    Buffer.add_string b body

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

let encode (p : payload) : string =
  let body = payload_zeroed p in
  let crc = E4_crc.string body in
  let out = Bytes.create (header_length + String.length body) in
  Bytes.blit_string magic 0 out 0 magic_length;
  Bytes.blit_string version_string 0 out magic_length version_length;
  Bytes.blit_string body 0 out header_length (String.length body);
  Bytes.blit_string (E4_crc.be32 crc) 0 out (header_length + checksum_offset) 4;
  Bytes.to_string out

exception Bad of string

let decode (s : string) : (payload, open_error) result =
  let len = String.length s in
  if len < magic_length || String.sub s 0 magic_length <> magic then Error Bad_magic
  else if len < header_length then Error (Corrupt "truncated: no version field")
  else
    let v = String.sub s magic_length version_length in
    (* CF1: the version is matched as a string before any field is read. *)
    if v <> version_string then Error (Stale_binary v)
    else
      let plen = len - header_length in
      if plen < fixed_payload_length then
        Error
          (Corrupt
             (Printf.sprintf "payload is %d bytes, shorter than the %d fixed fields" plen
                fixed_payload_length))
      else
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
          E4_crc.update_sub c s
            (header_length + checksum_offset + 4)
            (plen - checksum_offset - 4)
        in
        if stored <> computed then
          Error
            (Corrupt
               (Printf.sprintf "checksum 0x%08x, computed 0x%08x" stored computed))
        else begin
          try
            let pos = ref header_length in
            let u64 what =
              match E4_be.read_be64 s !pos with
              | None ->
                raise (Bad (Printf.sprintf "%s: not a be64 below 2^62 at offset %d" what !pos))
              | Some n ->
                pos := !pos + 8;
                n
            in
            let u32 what =
              match E4_crc.read_be32 s !pos with
              | None -> raise (Bad (Printf.sprintf "%s: truncated be32 at offset %d" what !pos))
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
                | None -> raise (Bad (Printf.sprintf "truncated root name length at %d" !pos))
                | Some n ->
                  pos := !pos + 2;
                  n
              in
              if !pos + name_len + 34 + 8 > len then
                raise (Bad (Printf.sprintf "truncated root at offset %d" !pos));
              let name = String.sub s !pos name_len in
              pos := !pos + name_len;
              if not (valid_name name) then
                raise
                  (Bad
                     (Printf.sprintf "root name %S is not 1..%d lowercase printable ASCII" name
                        max_name_length));
              let rk =
                match root_kind_of_index (Char.code s.[!pos]) with
                | Some k -> k
                | None ->
                  raise (Bad (Printf.sprintf "unregistered root kind byte %d" (Char.code s.[!pos])))
              in
              incr pos;
              let k =
                match E4_kind.of_byte (Char.code s.[!pos]) with
                | Some k -> k
                | None ->
                  raise (Bad (Printf.sprintf "unregistered kind byte %d" (Char.code s.[!pos])))
              in
              incr pos;
              let digest = E4_addr.Addr.of_digest (String.sub s !pos 32) in
              pos := !pos + 32;
              let version = u64 "root version" in
              { name; root_kind = rk; kind = k; digest; version }
            in
            let rec take n acc = if n = 0 then List.rev acc else take (n - 1) (read_root () :: acc) in
            if root_count > len then raise (Bad "root_count is larger than the file");
            let roots = take root_count [] in
            if !pos >= len then raise (Bad "truncated: no status tag");
            let tag = Char.code s.[!pos] in
            let body = String.sub s (!pos + 1) (len - !pos - 1) in
            let st =
              match tag with
              | 0 | 1 | 2 ->
                if body <> "" then
                  raise
                    (Bad
                       (Printf.sprintf "status tag %d carries a %d-byte body under version %s"
                          tag (String.length body) version_string));
                if tag = 0 then Fresh else if tag = 1 then Gced else Imported
              (* CF3: a tag this reader does not understand round-trips verbatim. *)
              | n when n >= 3 && n <= 15 -> Reserved (n, body)
              | n -> raise (Bad (Printf.sprintf "unknown status tag %d" n))
            in
            Ok
              {
                pack_end = (pack_end_seg, pack_end_off);
                index_end = (index_end_seg, index_end_off);
                generation;
                scheme_version;
                ledger_generation;
                roots;
                status = st;
              }
          with
          | Bad why -> Error (Corrupt why)
          | Invalid_argument why -> Error (Corrupt why)
        end

(* ---------------------------------------------------------------- I/O *)

let read_whole (path : string) : string =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let read ~path =
  match read_whole path with
  | s -> decode s
  | exception Sys_error why -> if Sys.file_exists path then Error (Corrupt why) else Error Missing
  | exception End_of_file -> Error (Corrupt "truncated while reading")

let write_all (fd : Unix.file_descr) (s : string) : unit =
  let n = String.length s in
  let rec go off = if off < n then go (off + Unix.write_substring fd s off (n - off)) in
  go 0

(* CF4: tmp, fsync, rename, fsync the directory.  A crash leaves the old file or the new one. *)
let commit ~path (p : payload) : unit =
  let bytes = encode p in
  let tmp = tmp_path ~path in
  let fd = Unix.openfile tmp [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Fun.protect
    ~finally:(fun () -> try Unix.close fd with Unix.Unix_error _ -> ())
    (fun () ->
      write_all fd bytes;
      Unix.fsync fd);
  Unix.rename tmp path;
  (* D7: best effort — a platform that cannot open a directory for fsync still has the
     rename, which is the atomic step. *)
  match Unix.openfile (Filename.dirname path) [ Unix.O_RDONLY ] 0 with
  | dfd ->
    (try Unix.fsync dfd with Unix.Unix_error _ -> ());
    (try Unix.close dfd with Unix.Unix_error _ -> ())
  | exception Unix.Unix_error _ -> ()

let write = commit

let cleanup ~dir =
  let tmp = Filename.concat dir tmp_filename in
  if Sys.file_exists tmp then try Sys.remove tmp with Sys_error _ -> ()

(* ---------------------------------------------------------------- the plane, read *)

let root (p : payload) (name : string) : root option =
  let name = normalise_name name in
  List.find_opt (fun r -> String.equal r.name name) p.roots

let next_version (p : payload) (name : string) : int =
  match root p name with Some old -> old.version + 1 | None -> 1

let roots (p : t) = p.roots
let pack_end (p : t) = p.pack_end
let index_end (p : t) = p.index_end
let generation (p : t) = p.generation
let scheme_version (p : t) = p.scheme_version
let ledger_generation (p : t) = p.ledger_generation
let status (p : t) = p.status

(* ---------------------------------------------------------------- the plane, moved *)

type root_error =
  | Stale_root of { name : string; expected : int; actual : int }
  | Dangling of E4_addr.Addr.t
  | Wrong_kind of { at : E4_addr.Addr.t; expected : E4_kind.t; actual : E4_kind.t }
  | Fork of { name : string; head : E4_addr.Addr.t; prev : E4_addr.Addr.t }

let root_error_word = function
  | Stale_root { name; expected; actual } ->
    Printf.sprintf "staleRoot %s %d %d" name expected actual
  | Wrong_kind _ -> "wrongKind"
  | Dangling d -> "dangling " ^ E4_addr.Addr.hex d
  | Fork { name; head; prev } ->
    Printf.sprintf "fork %s %s %s" name (E4_addr.Addr.hex head) (E4_addr.Addr.hex prev)

(* CF5, in Store.putRoot's order (Store.lean:523-530): version, then resolution, then kind.
   The M7 prev check sits with the version check — both ask "is this move against the head you
   think it is" — and is unreachable for any root kind but Registry (D2). *)
let advance_root (p : payload) ~(resolve : E4_addr.Addr.t -> E4_kind.t option)
    ?(prev : E4_addr.Addr.t option) (r : root) : (payload, root_error) result =
  let name = normalise_name r.name in
  if not (valid_name name) then
    invalid_arg
      (Printf.sprintf "E4_control.advance_root: root name %S is not 1..%d lowercase printable ASCII"
         r.name max_name_length);
  if r.version < 0 then
    invalid_arg "E4_control.advance_root: a root version is a be64 below 2^62 (M9)";
  let r = { r with name } in
  let expected = next_version p name in
  if r.version <> expected then Error (Stale_root { name; expected; actual = r.version })
  else
    let head = match root p name with Some q -> q.digest | None -> E4_addr.Addr.zero in
    let forked =
      match r.root_kind with
      | Registry ->
        let prev = match prev with Some d -> d | None -> E4_addr.Addr.zero in
        if E4_addr.Addr.equal prev head then None else Some (Fork { name; head; prev })
      | _ -> None
    in
    match forked with
    | Some e -> Error e
    | None -> (
      match resolve r.digest with
      | None -> Error (Dangling r.digest)
      | Some k when not (E4_kind.equal k r.kind) ->
        Error (Wrong_kind { at = r.digest; expected = r.kind; actual = k })
      | Some _ ->
        (* CF8: the moved root is the head and the resident of that name is filtered out —
           `r :: s.roots.filter fun q => q.name ≠ r.name` (Store.lean:527). *)
        Ok
          {
            p with
            roots = r :: List.filter (fun q -> not (String.equal q.name name)) p.roots;
            generation = p.generation + 1;
          })

let put_root = advance_root

(* ---------------------------------------------------------------- the watermark *)

let bump (p : t) : t = { p with generation = p.generation + 1 }
let set_pack_end (p : t) (e : int * int) : t = bump { p with pack_end = e }
let set_index_end (p : t) (e : int * int) : t = bump { p with index_end = e }
let set_status (p : t) (st : status) : t = bump { p with status = st }
let set_ledger_generation (p : t) (g : int) : t = bump { p with ledger_generation = g }
