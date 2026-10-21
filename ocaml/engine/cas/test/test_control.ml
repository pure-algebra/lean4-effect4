(* Root control bytes and policies.
   Depends on E4_control, node codecs, and generated G3 Move goldens.
   Properties tested: v1 refused as stale; v2 policy bytes; exact names; full-head staleness;
   duplicate generations; journal ancestry; pins; checksum and framing refusals; root goldens. *)

open Effect4_engine_cas

let skips = ref 0
let check = E4_check.check ~gap:Two
let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* ============================================================ scratch files *)

(* The test's scratch directory, under the system's temporary directory (E4_check.temp_dir). *)
let scratch_dir = lazy (E4_check.temp_dir "e4-p3-control-")
let scratch name = Filename.concat (Lazy.force scratch_dir) name

let write_bytes path s =
  let oc = open_out_bin path in
  output_string oc s;
  close_out oc
;;

let read_bytes path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s
;;

let remove_if path =
  if Sys.file_exists path
  then (
    try Sys.remove path with
    | Sys_error _ -> ())
;;

let cleanup_scratch () = E4_check.remove_tree (Lazy.force scratch_dir)

(* ============================================================ payload fixtures *)

let dig i = E4_addr.Addr.of_digest (String.make 32 (Char.chr i))

let mk_root name rk k d v : E4_control.root =
  { E4_control.name
  ; policy = rk
  ; kind = k
  ; head = { digest = d; generation = Z.of_int v }
  }
;;

let empty_payload = E4_control.initial

let one_root_payload =
  { E4_control.pack_end = 3, 4096
  ; index_end = 2, 1024
  ; generation = 7
  ; scheme_version = 0
  ; (* the one scheme a reader opens; CF10 *)
    ledger_generation = 5
  ; roots = [ mk_root "stdlib/rc112" E4_control.Swap E4_kind.Export (dig 0x11) 1 ]
  ; status = E4_control.Gced
  }
;;

let many_root_payload =
  { E4_control.pack_end = 0, 0
  ; index_end = 0, 0
  ; generation = 1
  ; scheme_version = 0
  ; ledger_generation = 0
  ; roots =
      [ mk_root "c" E4_control.Pin E4_kind.Chunk (dig 3) 9
      ; mk_root "b/x" E4_control.Swap E4_kind.Program (dig 2) 2
      ; mk_root "a" E4_control.Journal E4_kind.Schema (dig 1) 1
      ]
  ; status = E4_control.Imported
  }
;;

let reserved_payload =
  { many_root_payload with
    E4_control.status = E4_control.Reserved (7, "a future writer's body")
  }
;;

let long_name = String.make E4_control.max_name_length 'z'

(* max_int is 2^62-1 on this host (max_int): the largest be64 the wire admits (M9). *)
let boundary_payload =
  { E4_control.pack_end = E4_control.max_name_length, max_int
  ; index_end = max_int, 0
  ; generation = max_int
  ; scheme_version = 0
  ; (* the field's other values are CF10's refusals *)
    ledger_generation = 0xFFFFFFFF
  ; roots = [ mk_root long_name E4_control.Swap E4_kind.Table (dig 0xff) max_int ]
  ; status = E4_control.Reserved (15, "")
  }
;;

let root_equal (a : E4_control.root) (b : E4_control.root) =
  String.equal a.E4_control.name b.E4_control.name
  && a.E4_control.policy = b.E4_control.policy
  && E4_kind.equal a.E4_control.kind b.E4_control.kind
  && E4_addr.Addr.equal a.E4_control.head.digest b.E4_control.head.digest
  && Z.equal a.E4_control.head.generation b.E4_control.head.generation
;;

let payload_equal (a : E4_control.payload) (b : E4_control.payload) =
  a.E4_control.pack_end = b.E4_control.pack_end
  && a.E4_control.index_end = b.E4_control.index_end
  && a.E4_control.generation = b.E4_control.generation
  && a.E4_control.scheme_version = b.E4_control.scheme_version
  && a.E4_control.ledger_generation = b.E4_control.ledger_generation
  && a.E4_control.status = b.E4_control.status
  && List.length a.E4_control.roots = List.length b.E4_control.roots
  && List.for_all2 root_equal a.E4_control.roots b.E4_control.roots
;;

(* ============================================================ R: round trip *)

let test_roundtrip () =
  print_endline "-- R: the byte grammar round-trips (CF1, CF3, CF9)";
  let cases =
    [ "empty", empty_payload
    ; "one root", one_root_payload
    ; "three roots", many_root_payload
    ; "a reserved status with a body", reserved_payload
    ; "the be64 and name boundaries", boundary_payload
    ]
  in
  List.iter
    (fun (name, p) ->
       let b = E4_control.encode p in
       match E4_control.decode b with
       | Error e ->
         check (Printf.sprintf "R1 %s: decode (encode p) = Ok p" name) false;
         note "  refused: %s" (E4_control.open_error_word e)
       | Ok q ->
         check (Printf.sprintf "R1 %s: decode (encode p) = Ok p" name) (payload_equal p q);
         check
           (Printf.sprintf "R2 %s: encode is a function of the payload alone" name)
           (String.equal (E4_control.encode q) b))
    cases;
  (* CF10: a store of another scheme is refused at open, with the scheme read exactly. *)
  List.iter
    (fun v ->
       check
         (Printf.sprintf
            "CF10 a scheme_version of %d is refused as Other_scheme %d, never read"
            v
            v)
         (match
            E4_control.decode
              (E4_control.encode { one_root_payload with E4_control.scheme_version = v })
          with
          | Error (E4_control.Other_scheme n) -> n = v
          | Ok _ | Error _ -> false))
    [ 1; 0xFFFFFFFF ];
  check
    "CF10 red control: the same payload at scheme 0 reads"
    (match E4_control.decode (E4_control.encode one_root_payload) with
     | Ok _ -> true
     | Error _ -> false);
  (* The fixed offsets of CF3: magic, version, then the fixed fields. *)
  let b = E4_control.encode one_root_payload in
  check
    "R3 magic is the first six bytes"
    (String.length b > 6 && String.equal (String.sub b 0 6) E4_control.magic);
  check
    "R3 the version is the next eight, ASCII, exact"
    (String.equal (String.sub b 6 8) E4_control.version_string
     && String.equal E4_control.version_string "00000002");
  check
    "R3 the fixed payload is 56 bytes and the header 14"
    (E4_control.fixed_payload_length = 56 && String.length b >= 70);
  (* status is last: the file's last byte is the status tag when the body is empty. *)
  let b0 =
    E4_control.encode { one_root_payload with E4_control.status = E4_control.Fresh }
  in
  check
    "R4 status is LAST: an empty-bodied status is the final byte"
    (Char.code b0.[String.length b0 - 1] = 0);
  let only_checksum_moves =
    let x = String.sub b0 0 (String.length b0 - 1) in
    let y =
      String.sub
        (E4_control.encode { one_root_payload with E4_control.status = E4_control.Gced })
        0
        (String.length b0 - 1)
    in
    let differing = ref [] in
    String.iteri (fun i c -> if c <> y.[i] then differing := i :: !differing) x;
    List.for_all (fun i -> i >= 14 + 40 && i < 14 + 44) !differing
  in
  check
    "R4 changing the status moves the checksum field and nothing else before it"
    only_checksum_moves;
  (* on disk *)
  let path = scratch "control-roundtrip" in
  E4_control.commit ~path many_root_payload;
  check
    "R5 commit then read is the payload"
    (match E4_control.read ~path with
     | Ok q -> payload_equal many_root_payload q
     | Error _ -> false);
  check
    "R5 commit leaves no control.tmp beside it"
    (not (Sys.file_exists (E4_control.tmp_path ~path)));
  E4_control.write ~path reserved_payload;
  check
    "R6 write = commit, and a reserved status survives the file"
    (match E4_control.read ~path with
     | Ok q -> payload_equal reserved_payload q
     | Error _ -> false);
  remove_if path
;;

(* ============================================================ E: every refusal *)

(* A file whose payload is exactly these bytes, with the checksum field filled in — the way to
   hand-build a structurally wrong but checksum-correct control file. *)
let craft
      ?(magic = E4_control.magic)
      ?(version = E4_control.version_string)
      (payload : string)
  =
  let z = Bytes.of_string payload in
  if Bytes.length z >= 44 then Bytes.blit_string "\000\000\000\000" 0 z 40 4;
  let crc = E4_crc.string (Bytes.to_string z) in
  if Bytes.length z >= 44 then Bytes.blit_string (E4_crc.be32 crc) 0 z 40 4;
  magic ^ version ^ Bytes.to_string z
;;

let payload_of (b : string) = String.sub b 14 (String.length b - 14)

let is_corrupt = function
  | Error (E4_control.Corrupt _) -> true
  | _ -> false
;;

let test_refusals () =
  print_endline "-- E: every constructor of open_error (CF1, CF2, D3, CF9)";
  let path = scratch "control-refusals" in
  remove_if path;
  check "E1 Missing: no file" (E4_control.read ~path = Error E4_control.Missing);
  let good = E4_control.encode one_root_payload in
  write_bytes path ("XXXXX\000" ^ String.sub good 6 (String.length good - 6));
  check
    "E2 Bad_magic: the six magic bytes are wrong"
    (E4_control.read ~path = Error E4_control.Bad_magic);
  write_bytes path "E4C";
  check
    "E2 Bad_magic: a file too short to hold the magic"
    (E4_control.read ~path = Error E4_control.Bad_magic);
  write_bytes path (E4_control.magic ^ "00000003" ^ payload_of good);
  check
    "E3 Stale_binary: an unknown ASCII version, never a parse (CF1)"
    (match E4_control.read ~path with
     | Error (E4_control.Stale_binary v) -> String.equal v "00000003"
     | _ -> false);
  write_bytes path (E4_control.magic ^ "0000000" ^ payload_of good);
  check
    "E3 Stale_binary: a version of the right width but the wrong bytes"
    (match E4_control.read ~path with
     | Error (E4_control.Stale_binary _) -> true
     | _ -> false);
  write_bytes path (E4_control.magic ^ "0000");
  check
    "E3 a truncated version field is Corrupt, not Stale_binary"
    (is_corrupt (E4_control.read ~path));
  (* CF2: the checksum, and only the checksum, separates corruption from staleness. *)
  let broken = Bytes.of_string good in
  Bytes.set broken (14 + 40) (Char.chr (Char.code (Bytes.get broken (14 + 40)) lxor 0xff));
  write_bytes path (Bytes.to_string broken);
  check "E4 Corrupt: a flipped checksum field" (is_corrupt (E4_control.read ~path));
  let broken2 = Bytes.of_string good in
  Bytes.set broken2 (14 + 8) (Char.chr (Char.code (Bytes.get broken2 (14 + 8)) lxor 0x01));
  write_bytes path (Bytes.to_string broken2);
  check "E4 Corrupt: a flipped payload byte" (is_corrupt (E4_control.read ~path));
  write_bytes path (E4_control.magic ^ E4_control.version_string ^ String.make 20 '\000');
  check
    "E5 Corrupt: a payload shorter than the fixed fields"
    (is_corrupt (E4_control.read ~path));
  (* Structurally wrong, but with a correct checksum: the parse itself must refuse. *)
  let be64 = Eff_frame.be64 in
  let be32 = E4_crc.be32 in
  let fixed ~roots ~status =
    be64 0
    ^ be64 0
    ^ be64 0
    ^ be64 0
    ^ be64 1
    ^ "\000\000\000\000"
    ^ be32 0
    ^ be32 0
    ^ be32 (List.length roots)
    ^ String.concat "" roots
    ^ status
  in
  let a_root ?(name = "n") ?(rk = 0) ?(kb = 2) ?(vers = be64 1) () =
    "\000"
    ^ String.make 1 (Char.chr (String.length name))
    ^ name
    ^ String.make 1 (Char.chr rk)
    ^ String.make 1 (Char.chr kb)
    ^ String.make 32 '\001'
    ^ vers
  in
  write_bytes path (craft (fixed ~roots:[ a_root ~kb:99 () ] ~status:"\000"));
  check
    "E6 Corrupt: an unregistered kind byte in a root"
    (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[ a_root ~rk:9 () ] ~status:"\000"));
  check "E6 Corrupt: an unregistered root-kind byte" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[ a_root ~name:"Nope" () ] ~status:"\000"));
  check
    "E6 uppercase name retains its bytes"
    (match E4_control.read ~path with
     | Ok state ->
       (match E4_control.roots state with
        | [ root ] -> root.name = "Nope"
        | _ -> false)
     | _ -> false);
  write_bytes path (craft (fixed ~roots:[ a_root ~name:"a b" () ] ~status:"\000"));
  check
    "E6 spaces retain their bytes"
    (match E4_control.read ~path with
     | Ok state ->
       (match E4_control.roots state with
        | [ root ] -> root.name = "a b"
        | _ -> false)
     | _ -> false);
  write_bytes
    path
    (craft ~version:"00000001" (fixed ~roots:[ a_root ~name:"Nope" () ] ~status:"\000"));
  check
    "E6 version-1 bytes refuse as a stale binary"
    (match E4_control.read ~path with
     | Error (E4_control.Stale_binary v) -> String.equal v "00000001"
     | _ -> false);
  write_bytes path (craft (fixed ~roots:[ a_root ~name:"文档/α" () ] ~status:"\000"));
  check
    "E6 UTF-8 names retain exact bytes"
    (match E4_control.read ~path with
     | Ok state ->
       (match E4_control.roots state with
        | [ root ] -> root.name = "文档/α"
        | _ -> false)
     | _ -> false);
  write_bytes path (craft (fixed ~roots:[ a_root ~name:"\255" () ] ~status:"\000"));
  check "E6 invalid UTF-8 is byte damage" (is_corrupt (E4_control.read ~path));
  write_bytes
    path
    (craft (fixed ~roots:[ a_root ~vers:(String.make 8 '\255') () ] ~status:"\000"));
  check
    "E7 Corrupt: a root version at or above 2^62 (CF9, M9)"
    (is_corrupt (E4_control.read ~path));
  write_bytes
    path
    (craft
       (String.make 8 '\255'
        ^ be64 0
        ^ be64 0
        ^ be64 0
        ^ be64 1
        ^ "\000\000\000\000"
        ^ be32 0
        ^ be32 0
        ^ be32 0
        ^ "\000"));
  check
    "E7 Corrupt: pack_end_seg at or above 2^62 (CF9, M9)"
    (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:""));
  check "E8 Corrupt: no status tag at all" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:"\000extra"));
  check "E8 Corrupt: a body at status tag 0" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:"\016"));
  check
    "E8 Corrupt: a status tag above the reserved range"
    (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[ "\000\009truncated" ] ~status:"\000"));
  check "E9 Corrupt: a truncated root" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:"\003" ^ ""));
  check
    "E10 a reserved tag with an empty body is NOT a refusal"
    (match E4_control.read ~path with
     | Ok p -> p.E4_control.status = E4_control.Reserved (3, "")
     | Error _ -> false);
  (* The write side refuses what it cannot represent (D6). *)
  let raises f =
    try
      ignore (f () : string);
      false
    with
    | Invalid_argument _ -> true
  in
  check
    "E11 encode refuses a root name that is too long"
    (raises (fun () ->
       E4_control.encode
         { empty_payload with
           E4_control.roots =
             [ mk_root (String.make 65536 'a') E4_control.Swap E4_kind.Export (dig 1) 1 ]
         }));
  check
    "E11 encode retains an uppercase root name"
    (not
       (raises (fun () ->
          E4_control.encode
            { empty_payload with
              E4_control.roots =
                [ mk_root "Nope" E4_control.Swap E4_kind.Export (dig 1) 1 ]
            })));
  (* CF9: 2^62 is not representable as an OCaml int (max_int = 2^62-1), so
     the write side of M9 can only refuse a negative field; the read side is E7 above. *)
  check
    "E11 encode refuses a negative be64 field (CF9, M9)"
    (raises (fun () ->
       E4_control.encode { empty_payload with E4_control.generation = -1 }));
  check
    "E11 encode accepts the largest be64 the wire admits"
    (not
       (raises (fun () ->
          E4_control.encode { empty_payload with E4_control.generation = max_int })));
  check
    "E11 encode refuses a reserved status tag below 3"
    (raises (fun () ->
       E4_control.encode
         { empty_payload with E4_control.status = E4_control.Reserved (2, "x") }));
  remove_if path
;;

(* ============================================================ X: the crash families *)

let test_crash () =
  print_endline
    "-- X: A2 §4.3 X4 — a torn tmp, a rename that did not happen, a bad checksum";
  let dir = scratch "store" in
  (try Unix.mkdir dir 0o700 with
   | Unix.Unix_error _ -> ());
  let path = E4_control.control_path ~dir in
  let tmp = Filename.concat dir E4_control.tmp_filename in
  let truth = one_root_payload in
  E4_control.commit ~path truth;
  let truth_bytes = read_bytes path in
  (* (a) a torn control.tmp: the writer died between the write and the fsync. *)
  write_bytes tmp (String.sub truth_bytes 0 (String.length truth_bytes / 2));
  check
    "X4a a torn control.tmp does not touch `control`"
    (match E4_control.read ~path with
     | Ok p -> payload_equal truth p
     | Error _ -> false);
  E4_control.cleanup ~dir;
  check
    "X4a cleanup removes the torn tmp and leaves control alone"
    ((not (Sys.file_exists tmp))
     && Sys.file_exists path
     && String.equal (read_bytes path) truth_bytes);
  (* (b) a rename that did not happen: a COMPLETE new control sits in the tmp, unrenamed. *)
  let newer = E4_control.set_pack_end truth (9, 999) in
  write_bytes tmp (E4_control.encode newer);
  check
    "X4b an unrenamed complete tmp is not the truth — the previous control is"
    (match E4_control.read ~path with
     | Ok p -> payload_equal truth p && not (payload_equal newer p)
     | Error _ -> false);
  E4_control.cleanup ~dir;
  check
    "X4b cleanup discards it; `control` still reads as the previous payload"
    ((not (Sys.file_exists tmp))
     &&
     match E4_control.read ~path with
     | Ok p -> payload_equal truth p
     | Error _ -> false);
  (* and the rename, when it does happen, is all-or-nothing *)
  E4_control.commit ~path newer;
  check
    "X4b after the rename the new payload is the truth, and no tmp survives"
    ((not (Sys.file_exists tmp))
     &&
     match E4_control.read ~path with
     | Ok p -> payload_equal newer p
     | Error _ -> false);
  (* (c) a checksum mismatch: the file that is there is refused, and the previous control —
     the bytes a caller kept, or the operator's backup — still reads. *)
  let live = read_bytes path in
  let broken = Bytes.of_string live in
  let i = String.length live - 3 in
  Bytes.set broken i (Char.chr (Char.code (Bytes.get broken i) lxor 0x40));
  write_bytes path (Bytes.to_string broken);
  check
    "X4c a corrupt control is Corrupt, never a half-parse"
    (is_corrupt (E4_control.read ~path));
  write_bytes path truth_bytes;
  check
    "X4c and the previous control is the truth"
    (match E4_control.read ~path with
     | Ok p -> payload_equal truth p
     | Error _ -> false);
  (* The pack_end watermark a crash lowers is lane P4's; what this file owes is that the
     watermark it records is exactly what a re-read gives back. *)
  let w = E4_control.set_pack_end truth (4, 1 lsl 20) in
  E4_control.commit ~path w;
  check
    "W1 pack_end is recorded and read back exactly"
    (match E4_control.read ~path with
     | Ok p -> E4_control.pack_end p = (4, 1 lsl 20)
     | Error _ -> false);
  check
    "W1 set_pack_end bumps the generation (CF7)"
    (E4_control.generation w = E4_control.generation truth + 1);
  remove_if path;
  try Unix.rmdir dir with
  | Unix.Unix_error _ -> ()
;;

(* ============================================================ P9: reserved tags *)

let test_reserved () =
  print_endline
    "-- P9/CF3: reserved status tags survive a reader that does not understand them";
  let path = scratch "control-reserved" in
  let ok = ref true in
  for tag = 3 to 15 do
    let body = Printf.sprintf "tag-%d body \000\255" tag in
    let p =
      { many_root_payload with E4_control.status = E4_control.Reserved (tag, body) }
    in
    E4_control.commit ~path p;
    (* the "older reader": it decodes the tag it does not know, and writes it back unchanged *)
    match E4_control.read ~path with
    | Error _ -> ok := false
    | Ok q ->
      if q.E4_control.status <> E4_control.Reserved (tag, body) then ok := false;
      E4_control.commit ~path q;
      (match E4_control.read ~path with
       | Ok r ->
         if r.E4_control.status <> E4_control.Reserved (tag, body) then ok := false
       | Error _ -> ok := false)
  done;
  check "P9 every reserved tag 3..15 and its body round-trip through a rewrite" !ok;
  (* the format-revision property, stated as bytes: the rewrite is byte-identical *)
  let p =
    { many_root_payload with E4_control.status = E4_control.Reserved (11, "newer") }
  in
  E4_control.commit ~path p;
  let first = read_bytes path in
  (match E4_control.read ~path with
   | Ok q -> E4_control.commit ~path q
   | Error _ -> ());
  check
    "P9 a rewrite by a reader that does not understand tag 11 is byte-identical"
    (String.equal (read_bytes path) first);
  remove_if path
;;

(* ============================================================ C: the roots CAS *)

let table_resolve (tbl : (E4_addr.Addr.t * E4_kind.t) list) (a : E4_addr.Addr.t) =
  match List.find_opt (fun (d, _) -> E4_addr.Addr.equal d a) tbl with
  | Some (_, k) -> Some k
  | None -> None
;;

let outcome_word = function
  | Ok _ -> "ok"
  | Error e -> E4_control.root_error_word e
;;

let test_policy_bytes () =
  let root = mk_root "policy" E4_control.Swap E4_kind.Export (dig 1) 1 in
  let bytes = E4_control.encode { empty_payload with E4_control.roots = [ root ] } in
  let payload = Bytes.of_string (payload_of bytes) in
  let position = E4_control.fixed_payload_length + 2 + String.length root.name in
  Bytes.set payload position '\001';
  check
    "D2 policy byte one is journal"
    (match E4_control.decode (craft (Bytes.to_string payload)) with
     | Ok state ->
       (match E4_control.roots state with
        | [ root ] -> root.policy = E4_control.Journal
        | _ -> false)
     | _ -> false);
  Bytes.set payload position '\006';
  check
    "D2 an unregistered policy byte is corrupt"
    (is_corrupt (E4_control.decode (craft (Bytes.to_string payload))))
;;

let test_cas () =
  print_endline "-- complete-head root moves";
  let d1 = dig 1
  and d2 = dig 2
  and d3 = dig 3 in
  let target digest : E4_control.target = { kind = E4_kind.Export; digest } in
  let head digest generation : E4_control.head =
    { digest; generation = Z.of_int generation }
  in
  let resolve =
    table_resolve [ d1, E4_kind.Export; d2, E4_kind.Export; d3, E4_kind.Export ]
  in
  let run state move = E4_control.advance_root state ~resolve move in
  let get = function
    | Ok state -> state
    | Error error -> failwith (E4_control.root_error_word error)
  in
  let create = E4_control.Create ("docs/a", E4_control.Swap, target d1) in
  let first = get (run empty_payload create) in
  check
    "create generation one"
    (match E4_control.root first "docs/a" with
     | Some root -> E4_control.head_equal root.head (head d1 1)
     | None -> false);
  check
    "duplicate create stale"
    (match run first create with
     | Error (E4_control.Stale_root _) -> true
     | _ -> false);
  let duplicate = get (run first (E4_control.Advance ("docs/a", head d1 1, target d1))) in
  check "identical target retains exact payload" (payload_equal duplicate first);
  let second = get (run first (E4_control.Advance ("docs/a", head d1 1, target d2))) in
  let third = get (run second (E4_control.Advance ("docs/a", head d2 2, target d1))) in
  check
    "ABA retains generation"
    (match E4_control.root third "docs/a" with
     | Some root -> E4_control.head_equal root.head (head d1 3)
     | None -> false);
  check
    "ABA stale expectation refuses"
    (match run third (E4_control.Advance ("docs/a", head d1 1, target d2)) with
     | Error (E4_control.Stale_root _) -> true
     | _ -> false);
  check
    "stale precedes wrong kind"
    (match
       run
         first
         (E4_control.Advance
            ("docs/a", head d2 1, { kind = E4_kind.Schema; digest = E4_addr.Addr.zero }))
     with
     | Error (E4_control.Stale_root _) -> true
     | _ -> false);
  check
    "absent advance precedes target"
    (match run empty_payload (E4_control.Advance ("none", head d1 1, target d3)) with
     | Error (E4_control.No_root "none") -> true
     | _ -> false);
  check
    "target kind remains fixed"
    (match
       run
         first
         (E4_control.Advance ("docs/a", head d1 1, { kind = E4_kind.Schema; digest = d1 }))
     with
     | Error (E4_control.Wrong_kind _) -> true
     | _ -> false);
  check
    "dangling target refuses"
    (match
       run first (E4_control.Advance ("docs/a", head d1 1, target E4_addr.Addr.zero))
     with
     | Error (E4_control.Dangling _) -> true
     | _ -> false);
  let pin =
    get (run empty_payload (E4_control.Create ("pin/a", E4_control.Pin, target d1)))
  in
  check
    "pin duplicate accepted"
    (match run pin (E4_control.Advance ("pin/a", head d1 1, target d1)) with
     | Ok _ -> true
     | _ -> false);
  check
    "pin changed target refuses"
    (match run pin (E4_control.Advance ("pin/a", head d1 1, target d2)) with
     | Error (E4_control.Pinned _) -> true
     | _ -> false);
  let journal =
    get
      (run empty_payload (E4_control.Create ("session/a", E4_control.Journal, target d1)))
  in
  check
    "journal without designated parent refuses"
    (match run journal (E4_control.Advance ("session/a", head d1 1, target d2)) with
     | Error (E4_control.Fork _) -> true
     | _ -> false);
  let parent address =
    if E4_addr.Addr.equal address d3
    then Some d2
    else if E4_addr.Addr.equal address d2
    then Some d1
    else None
  in
  check
    "journal follows transitive designated parents"
    (match
       E4_control.advance_root
         journal
         ~resolve
         ~parent
         (E4_control.Advance ("session/a", head d1 1, target d3))
     with
     | Ok _ -> true
     | _ -> false);
  check
    "fork creates independent journal name"
    (match
       run journal (E4_control.Create ("session/fork", E4_control.Journal, target d2))
     with
     | Ok state -> List.length (E4_control.roots state) = 2
     | _ -> false);
  let exact =
    get (run first (E4_control.Create ("Docs/a", E4_control.Swap, target d2)))
  in
  check "names retain case exactly" (List.length (E4_control.roots exact) = 2);
  let large = Z.shift_left Z.one 100 in
  let old : E4_control.root =
    { name = "large"
    ; policy = E4_control.Swap
    ; kind = E4_kind.Export
    ; head = { digest = d1; generation = large }
    }
  in
  let state = { empty_payload with E4_control.roots = [ old ] } in
  check
    "generation arithmetic is exact beyond machine integers"
    (match run state (E4_control.Advance ("large", old.head, target d2)) with
     | Ok next ->
       (match E4_control.root next "large" with
        | Some root -> Z.equal root.head.generation (Z.succ large)
        | None -> false)
     | _ -> false)
;;

let test_mutation () =
  print_endline "-- M: one flipped byte anywhere in the file, and read must refuse";
  let path = scratch "control-mutation" in
  let good = E4_control.encode one_root_payload in
  let n = String.length good in
  let all_red = ref true in
  let words = Hashtbl.create 8 in
  for i = 0 to n - 1 do
    let m = Bytes.of_string good in
    Bytes.set m i (Char.chr (Char.code (Bytes.get m i) lxor 0x01));
    write_bytes path (Bytes.to_string m);
    let r = E4_control.read ~path in
    (match r with
     | Ok _ -> all_red := false
     | Error _ -> ());
    let w =
      match r with
      | Ok _ -> "ACCEPTED"
      | Error E4_control.Bad_magic -> "badMagic"
      | Error (E4_control.Stale_binary _) -> "staleBinary"
      | Error (E4_control.Corrupt _) -> "corrupt"
      | Error E4_control.Missing -> "missing"
      | Error (E4_control.Other_scheme _) -> "otherScheme"
    in
    Hashtbl.replace
      words
      w
      (1
       +
       try Hashtbl.find words w with
       | Not_found -> 0)
  done;
  check (Printf.sprintf "M1 every one of the %d single-byte flips is refused" n) !all_red;
  note
    "  verdicts: %s"
    (String.concat
       " "
       (List.sort
          compare
          (Hashtbl.fold (fun k v acc -> Printf.sprintf "%s=%d" k v :: acc) words [])));
  write_bytes path good;
  check
    "M1 and the unflipped file still reads"
    (match E4_control.read ~path with
     | Ok p -> payload_equal one_root_payload p
     | Error _ -> false);
  check
    "M2 a repeated create refuses stale absence"
    (let d = dig 0x31 in
     let resolve = table_resolve [ d, E4_kind.Export ] in
     let move =
       E4_control.Create ("a/b", E4_control.Swap, { kind = E4_kind.Export; digest = d })
     in
     match E4_control.advance_root empty_payload ~resolve move with
     | Error _ -> false
     | Ok state ->
       (match E4_control.advance_root state ~resolve move with
        | Error (E4_control.Stale_root _) -> true
        | _ -> false));
  remove_if path
;;

(* ============================================================ G3: the goldens *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s
;;

let strip s =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c ->
       match c with
       | ' ' | '\n' | '\r' | '\t' -> ()
       | _ -> Buffer.add_char b c)
    s;
  Buffer.contents b
;;

(* The same search lane P0 uses (test_bytes.ml:638): only ever ".../cas/goldens". *)
let goldens_dir () =
  let rec ancestors d n acc =
    if n = 0 then List.rev acc else ancestors (Filename.dirname d) (n - 1) (d :: acc)
  in
  let here = Sys.getcwd () in
  let from_env =
    try [ Sys.getenv "E4_CAS_GOLDENS" ] with
    | Not_found -> []
  in
  let per_ancestor a =
    (if Filename.basename a = "cas" then [ Filename.concat a "goldens" ] else [])
    @ [ Filename.concat a (Filename.concat "cas" "goldens")
      ; Filename.concat a (Filename.concat "engine" (Filename.concat "cas" "goldens"))
      ; Filename.concat
          a
          (Filename.concat
             "ocaml"
             (Filename.concat "engine" (Filename.concat "cas" "goldens")))
      ]
  in
  let cands = from_env @ List.concat (List.map per_ancestor (ancestors here 9 [])) in
  List.find_opt
    (fun d ->
       d <> ""
       &&
       try Sys.is_directory d with
       | Sys_error _ -> false)
    cands
;;

let lines_of s =
  List.map
    (fun l ->
       if l <> "" && l.[String.length l - 1] = '\r'
       then String.sub l 0 (String.length l - 1)
       else l)
    (String.split_on_char '\n' s)
;;

(* cases.txt rows: name<TAB>family<TAB>expected *)
let load_cases dir =
  let path = Filename.concat dir "cases.txt" in
  if not (Sys.file_exists path)
  then []
  else
    List.filter_map
      (fun l ->
         if l = "" || l.[0] = '#'
         then None
         else (
           match String.split_on_char '\t' l with
           | [ n; f; e ] -> Some (n, f, e)
           | _ -> None))
      (lines_of (read_file path))
;;

let case_bytes dir name =
  let path = Filename.concat dir (name ^ ".hex") in
  if not (Sys.file_exists path) then None else E4_hex.to_bytes (strip (read_file path))
;;

(* The Val frames of Val.encode (src/Effect4/Store/Carrier/Val.lean), built from Eff_frame.framed alone. *)
let v_nat n = Eff_frame.framed Eff_frame.tag_nat (Eff_frame.nat_digits (Z.of_int n))
let v_str s = Eff_frame.framed Eff_frame.tag_string s
let v_bytes b = Eff_frame.framed Eff_frame.tag_bytes b
let v_list xs = Eff_frame.framed Eff_frame.tag_list (String.concat "" xs)
let v_ctor i args = Eff_frame.framed Eff_frame.tag_ctor (v_nat i ^ String.concat "" args)

(* rootVal r = ctor 0 [str name, nat policyIndex, nat kind.byte, bytes digest, nat generation]
   (2026-09-08-engine-lane-gld-delivery.md §2). *)
let root_val (r : E4_control.root) =
  v_ctor
    0
    [ v_str r.E4_control.name
    ; v_nat (E4_control.root_policy_index r.E4_control.policy)
    ; v_nat (E4_kind.byte r.E4_control.kind)
    ; v_bytes (E4_addr.Addr.bytes r.E4_control.head.digest)
    ; v_nat (Z.to_int r.E4_control.head.generation)
    ]
;;

let resolver_of_goldens dir cases =
  let tbl = ref [] in
  List.iter
    (fun (name, family, expected) ->
       if String.equal family "g1"
       then (
         match case_bytes dir name with
         | Some b when String.length b >= 34 && b.[0] = '\000' ->
           (match E4_kind.of_byte (Char.code b.[1]), E4_addr.Addr.of_hex expected with
            | Some k, Some a -> tbl := (a, k) :: !tbl
            | _ -> ())
         | _ -> ()))
    cases;
  !tbl, table_resolve !tbl
;;

let decode_move bytes =
  let ( let* ) value f = Option.bind value f in
  let read_bytes bytes pos limit =
    let* tag, start, ending, next = Eff_frame.read_frame bytes pos limit in
    if tag = Eff_frame.tag_bytes
    then Some (String.sub bytes start (ending - start), next)
    else None
  in
  (* A natural of the kernel that this log holds as a host int. *)
  let small n = if Z.fits_int n then Some (Z.to_int n) else None in
  let decode bytes pos limit =
    let* tag, start, ending, next = Eff_frame.read_ctor bytes pos limit in
    let* name, p1 = Eff_frame.decode_string bytes start ending in
    let* tag = small tag in
    match tag with
    | 0 ->
      let* policy, p2 = Eff_frame.decode_nat bytes p1 ending in
      let* kind, p3 = Eff_frame.decode_nat bytes p2 ending in
      let* digest, p4 = read_bytes bytes p3 ending in
      let* policy = small policy in
      let* kind = small kind in
      let* policy = E4_control.root_policy_of_index policy in
      let* kind = E4_kind.of_byte kind in
      if p4 = ending && String.length digest = 32
      then
        Some
          ( E4_control.Create
              (name, policy, { kind; digest = E4_addr.Addr.of_digest digest })
          , next )
      else None
    | 1 ->
      let* digest, p2 = read_bytes bytes p1 ending in
      let* generation, p3 = Eff_frame.decode_nat bytes p2 ending in
      let* kind, p4 = Eff_frame.decode_nat bytes p3 ending in
      let* target, p5 = read_bytes bytes p4 ending in
      let* kind = small kind in
      let* kind = E4_kind.of_byte kind in
      if p5 = ending && String.length digest = 32 && String.length target = 32
      then
        Some
          ( E4_control.Advance
              ( name
              , { digest = E4_addr.Addr.of_digest digest; generation }
              , { kind; digest = E4_addr.Addr.of_digest target } )
          , next )
      else None
    | _ -> None
  in
  Eff_frame.exact decode bytes
;;

let test_goldens () =
  match goldens_dir () with
  | None -> check "G3 goldens must be available" false
  | Some dir ->
    let rows = load_cases dir in
    let table, _ = resolver_of_goldens dir rows in
    let extra =
      match case_bytes dir "g3-target-v2" with
      | Some bytes ->
        (match Eff_frame.read_frame bytes 0 (String.length bytes) with
         | Some (tag, start, ending, next)
           when tag = Eff_frame.tag_bytes && next = String.length bytes ->
           let bytes = String.sub bytes start (ending - start) in
           (match E4_node.decode bytes with
            | Ok node -> [ E4_node.address node, node.E4_node.kind ]
            | Error _ -> [])
         | _ -> [])
      | None -> []
    in
    let resolve = table_resolve (extra @ table) in
    let state = ref E4_control.initial in
    List.iter
      (fun name ->
         let expected =
           match List.find_opt (fun (label, _, _) -> label = name) rows with
           | Some (_, _, expected) -> expected
           | None -> "MISSING"
         in
         match case_bytes dir name with
         | None -> check ("G3 missing " ^ name) false
         | Some bytes ->
           if name = "g3-roots-after-v1" || name = "g3-roots-after-v2"
           then
             check
               ("G3 control " ^ name)
               (bytes = v_list (List.map root_val (E4_control.roots !state)))
           else (
             match decode_move bytes with
             | None -> check ("G3 decode " ^ name) false
             | Some move ->
               let result = E4_control.advance_root !state ~resolve move in
               check ("G3 control " ^ name) (outcome_word result = expected);
               (match result with
                | Ok next -> state := next
                | Error _ -> ())))
      [ "g3-v1"
      ; "g3-roots-after-v1"
      ; "g3-stale"
      ; "g3-wrongKind"
      ; "g3-dangling"
      ; "g3-advance-v2"
      ; "g3-roots-after-v2"
      ]
;;

(* ============================================================ *)

let () =
  test_roundtrip ();
  test_refusals ();
  test_crash ();
  test_reserved ();
  test_policy_bytes ();
  test_cas ();
  test_mutation ();
  test_goldens ();
  cleanup_scratch ();
  if !skips > 0 then Printf.printf "== %d skipped ==\n" !skips;
  E4_check.finish ()
;;
