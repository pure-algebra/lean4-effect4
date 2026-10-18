(* Control-file bytes and root moves. Depends on E4_addr and the byte codecs.
   Properties by construction: exact names, fixed policy/kind, stale-first full-head comparison.
   Properties tested by test_control: legacy/v2 bytes, generations, pins, journal parents,
   framing damage, and generated root goldens. The interface states the wire capacity. *)


(* ---------------------------------------------------------------- the plane *)

type root_policy = E4_root_policy.t = Swap | Journal | Pin

type head = { digest : E4_addr.Addr.t; generation : Z.t }
type target = { kind : E4_kind.t; digest : E4_addr.Addr.t }
type root = { name : string; policy : root_policy; kind : E4_kind.t; head : head }
type move = Create of string * root_policy * target | Advance of string * head * target

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

(* A v1 reader retains the old byte-format domain before applying D2. *)
let legacy_valid_name s =
  let length = String.length s in
  length >= 1 && length <= 512 &&
  String.for_all (fun character ->
    let byte = Char.code character in
    byte >= 0x21 && byte <= 0x7e && not (byte >= 0x41 && byte <= 0x5a)) s

let root_policy_index = E4_root_policy.byte
let root_policy_of_index = E4_root_policy.of_byte
let root_policy_name = E4_root_policy.name

(* D2: these are legacy bytes, never the new policy alphabet. *)
let legacy_policy_of_index = function
  | 0 | 1 | 2 | 3 | 4 | 5 -> Some Swap
  | 6 -> Some Pin
  | _ -> None

let head_equal (a : head) (b : head) =
  Z.equal a.generation b.generation && E4_addr.Addr.equal a.digest b.digest

(* An operator word never carries a raw byte: a corrupted version field is arbitrary. *)
let printable (s : string) : string =
  String.map (fun c -> if Char.code c >= 0x20 && Char.code c < 0x7f then c else '?') s

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
      (Printf.sprintf "E4_control.encode: root name %S is outside its format domain (wire limit %d bytes)"
         r.name max_name_length);
  add_be16 b "root name length" (String.length r.name);
  Buffer.add_string b r.name;
  Buffer.add_char b (Char.chr (root_policy_index r.policy));
  Buffer.add_char b (Char.chr (E4_kind.byte r.kind));
  Buffer.add_string b (E4_addr.Addr.bytes r.head.digest);
  if Z.sign r.head.generation < 0 || Z.gt r.head.generation (Z.of_int max_wire) then
    invalid_arg "E4_control.encode: root generation exceeds wire capacity";
  add_be64 b "root generation" (Z.to_int r.head.generation)

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
    if v <> version_string && v <> "00000001" then Error (Stale_binary v)
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
              if not ((if String.equal v "00000001" then legacy_valid_name else valid_name) name) then
                raise
                  (Bad
                     (Printf.sprintf "root name %S is outside its format domain (wire limit %d bytes)" name
                        max_name_length));
              let rk =
                match (if String.equal v "00000001" then legacy_policy_of_index else root_policy_of_index) (Char.code s.[!pos]) with
                | Some k -> k
                | None ->
                  raise (Bad (Printf.sprintf "unregistered root policy byte %d" (Char.code s.[!pos])))
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
              { name; policy = rk; kind = k; head = { digest; generation = Z.of_int version } }
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
            (* CF10: scheme 0 is the one this reader knows; any other is refused, not read. *)
            if scheme_version <> 0 then Error (Other_scheme scheme_version)
            else
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
  | Stale_root of { name : string; expected : head option; actual : head option }
  | Pinned of string
  | Dangling of E4_addr.Addr.t
  | Wrong_kind of { at : E4_addr.Addr.t; expected : E4_kind.t; actual : E4_kind.t }
  | Fork of { name : string; head : E4_addr.Addr.t; target : E4_addr.Addr.t }

let head_word (value : head option) = match value with
  | None -> "none"
  | Some h -> E4_addr.Addr.hex h.digest ^ ":" ^ Z.to_string h.generation

let root_error_word = function
  | No_root name -> "noRoot " ^ name
  | Stale_root {name; expected; actual} -> "staleRoot " ^ name ^ " " ^ head_word expected ^ " " ^ head_word actual
  | Pinned name -> "pinned " ^ name
  | Dangling d -> "dangling " ^ E4_addr.Addr.hex d
  | Wrong_kind _ -> "wrongKind"
  | Fork {name; head; target} -> "fork " ^ name ^ " " ^ E4_addr.Addr.hex head ^ " " ^ E4_addr.Addr.hex target

let advance_root (p : payload) ~(resolve : E4_addr.Addr.t -> E4_kind.t option)
    ?(parent = fun _ -> None) (move : move) : (payload, root_error) result =
  let install (r : root) = Ok {p with roots = r :: List.filter (fun q -> not (String.equal q.name r.name)) p.roots;
    generation = p.generation + 1} in
  let check_target expected (target : target) =
    if not (E4_kind.equal target.kind expected) then
      Error (Wrong_kind {at = target.digest; expected; actual = target.kind})
    else match resolve target.digest with
      | None -> Error (Dangling target.digest)
      | Some actual when not (E4_kind.equal actual expected) ->
        Error (Wrong_kind {at = target.digest; expected; actual})
      | Some _ -> Ok () in
  match move with
  | Create (name, policy, target) ->
    (match root p name with
     | Some old -> Error (Stale_root {name; expected = None; actual = Some old.head})
     | None -> match check_target target.kind target with
       | Error e -> Error e
       | Ok () -> install {name; policy; kind = target.kind; head = {digest = target.digest; generation = Z.one}})
  | Advance (name, expected, target) ->
    (match root p name with
     | None -> Error (No_root name)
     | Some old when not (head_equal old.head expected) ->
       Error (Stale_root {name; expected = Some expected; actual = Some old.head})
     | Some old when E4_kind.equal target.kind old.kind && E4_addr.Addr.equal target.digest old.head.digest -> Ok p
     | Some old when old.policy = Pin -> Error (Pinned name)
     | Some old -> match check_target old.kind target with
       | Error e -> Error e
       | Ok () ->
         let rec reaches seen address =
           E4_addr.Addr.equal address old.head.digest ||
           (not (List.exists (E4_addr.Addr.equal address) seen) &&
            match parent address with None -> false | Some previous -> reaches (address :: seen) previous) in
         if old.policy = Journal && not (reaches [] target.digest) then
           Error (Fork {name; head = old.head.digest; target = target.digest})
         else install {old with head = {digest = target.digest; generation = Z.succ old.head.generation}})

(* ---------------------------------------------------------------- the watermark *)

let bump (p : t) : t = { p with generation = p.generation + 1 }
let set_pack_end (p : t) (e : int * int) : t = bump { p with pack_end = e }
let set_index_end (p : t) (e : int * int) : t = bump { p with index_end = e }
let set_status (p : t) (st : status) : t = bump { p with status = st }
let set_ledger_generation (p : t) (g : int) : t = bump { p with ledger_generation = g }
