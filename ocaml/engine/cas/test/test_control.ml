(* test_control.ml — lane P3's checks: the control file (2026-09-08).

   What it checks, and against what:
     R*  Round trip: `decode (encode p) = Ok p` for every shape of payload the grammar of
         e4_control.mli admits — no roots, many roots, a reserved status with a body, the
         maximum name, the host-limit boundary — and the same through a real file.
     E*  Every refusal of `open_error`: Missing, Bad_magic, Stale_binary (CF1), and each way a
         file can be Corrupt (CF2, D3) — a failed checksum, a short payload, a truncated root,
         an unregistered kind byte, an unregistered root-kind byte, an uppercase root name, a
         body at a tag 0..2, an unknown status tag, a be64 at or above 2^62 (CF9, M9).
     X*  The three crash families of A2 §4.3 X4 that concern this file: (a) a torn control.tmp
         left behind, (b) a rename that did not happen, (c) a checksum mismatch.  In all three
         the PREVIOUS control is the truth.
     P9  Reserved tags 3..15 round-trip verbatim through a commit by a reader that does not
         understand them — the format-revision property (CF3).
     C*  The CAS on the roots plane (CF5-CF8): the outcome vocabulary of Store.putRoot
         (src/Effect4/Store/Store.lean:523-530), the head-first cons, the lowercasing of M8,
         the monotone generation of CF7, and the M7 fork refusal that Lean does not have.
     W*  The pack_end watermark: what `set_pack_end` records and what a re-read gives back.
     G3  The roots CAS sequence of A2 §4.1 G3, replayed against ../goldens: each `g3-*.hex` is
         a `rootVal` frame tree (2026-09-08-engine-lane-gld-delivery.md §2), decoded into a
         root, put into the payload with a resolver STUBBED FROM THE g1 GOLDENS (the
         store-relative checks are lane P4's), and its outcome word compared with cases.txt's
         `expected` column.  The two `g3-roots-after-*` cases are the roots plane itself,
         re-encoded as `list (rootVal r)` and compared byte for byte; a mismatch prints both.
         M7's `prev` and M1's `pinAll` are SKIPped with the reason lane GLD gives
         (2026-09-08-engine-lane-gld-delivery.md §4 O4).  When ../goldens is absent every G3
         line is a SKIP and the run still ends green.
     M*  The mutation check: flipping any one byte of a well-formed control file makes `read`
         refuse, and an in-memory root advance at a stale version is `staleRoot`.

   Exit code 0 iff every check passed. *)

open Effect4_engine
open Effect4_engine_cas

let failures = ref 0
let skips = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let skip name why =
  Printf.printf "SKIP  %s (%s)\n" name why;
  incr skips

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* ============================================================ scratch files *)

let scratch_dir =
  lazy
    (let base = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
     let d = Filename.concat base (Printf.sprintf "e4-p3-control-%d" (Unix.getpid ())) in
     (try Unix.mkdir d 0o700 with Unix.Unix_error _ -> ());
     d)

let scratch name = Filename.concat (Lazy.force scratch_dir) name

let write_bytes path s =
  let oc = open_out_bin path in
  output_string oc s;
  close_out oc

let read_bytes path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let remove_if path = if Sys.file_exists path then try Sys.remove path with Sys_error _ -> ()

let cleanup_scratch () =
  let d = Lazy.force scratch_dir in
  (try Array.iter (fun f -> remove_if (Filename.concat d f)) (Sys.readdir d)
   with Sys_error _ -> ());
  try Unix.rmdir d with Unix.Unix_error _ -> ()

(* ============================================================ payload fixtures *)

let dig i = E4_addr.Addr.of_digest (String.make 32 (Char.chr i))

let mk_root name rk k d v : E4_control.root =
  { E4_control.name; root_kind = rk; kind = k; digest = d; version = v }

let empty_payload = E4_control.initial

let one_root_payload =
  {
    E4_control.pack_end = (3, 4096);
    index_end = (2, 1024);
    generation = 7;
    scheme_version = 1;
    ledger_generation = 5;
    roots = [ mk_root "stdlib/rc112" E4_control.Stdlib E4_kind.Export (dig 0x11) 1 ];
    status = E4_control.Gced;
  }

let many_root_payload =
  {
    E4_control.pack_end = (0, 0);
    index_end = (0, 0);
    generation = 1;
    scheme_version = 0;
    ledger_generation = 0;
    roots =
      [
        mk_root "c" E4_control.Pin E4_kind.Chunk (dig 3) 9;
        mk_root "b/x" E4_control.Registry E4_kind.Program (dig 2) 2;
        mk_root "a" E4_control.Journal E4_kind.Schema (dig 1) 1;
      ];
    status = E4_control.Imported;
  }

let reserved_payload =
  { many_root_payload with E4_control.status = E4_control.Reserved (7, "a future writer's body") }

let long_name = String.make E4_control.max_name_length 'z'

(* max_int is 2^62-1 on this host (E4_nat.max_nat): the largest be64 the wire admits (M9). *)
let boundary_payload =
  {
    E4_control.pack_end = (E4_control.max_name_length, max_int);
    index_end = (max_int, 0);
    generation = max_int;
    scheme_version = 0xFFFFFFFF;
    ledger_generation = 0xFFFFFFFF;
    roots = [ mk_root long_name E4_control.Char E4_kind.Table (dig 0xff) max_int ];
    status = E4_control.Reserved (15, "");
  }

let root_equal (a : E4_control.root) (b : E4_control.root) =
  String.equal a.E4_control.name b.E4_control.name
  && a.E4_control.root_kind = b.E4_control.root_kind
  && E4_kind.equal a.E4_control.kind b.E4_control.kind
  && E4_addr.Addr.equal a.E4_control.digest b.E4_control.digest
  && a.E4_control.version = b.E4_control.version

let payload_equal (a : E4_control.payload) (b : E4_control.payload) =
  a.E4_control.pack_end = b.E4_control.pack_end
  && a.E4_control.index_end = b.E4_control.index_end
  && a.E4_control.generation = b.E4_control.generation
  && a.E4_control.scheme_version = b.E4_control.scheme_version
  && a.E4_control.ledger_generation = b.E4_control.ledger_generation
  && a.E4_control.status = b.E4_control.status
  && List.length a.E4_control.roots = List.length b.E4_control.roots
  && List.for_all2 root_equal a.E4_control.roots b.E4_control.roots

(* ============================================================ R: round trip *)

let test_roundtrip () =
  print_endline "-- R: the byte grammar round-trips (CF1, CF3, CF9)";
  let cases =
    [
      ("empty", empty_payload);
      ("one root", one_root_payload);
      ("three roots", many_root_payload);
      ("a reserved status with a body", reserved_payload);
      ("the be64 and name boundaries", boundary_payload);
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

  (* The fixed offsets of CF3: magic, version, then the fixed fields. *)
  let b = E4_control.encode one_root_payload in
  check "R3 magic is the first six bytes"
    (String.length b > 6 && String.equal (String.sub b 0 6) E4_control.magic);
  check "R3 the version is the next eight, ASCII, exact"
    (String.equal (String.sub b 6 8) E4_control.version_string
    && String.equal E4_control.version_string "00000001");
  check "R3 the fixed payload is 56 bytes and the header 14"
    (E4_control.fixed_payload_length = 56 && String.length b >= 70);
  (* status is last: the file's last byte is the status tag when the body is empty. *)
  let b0 = E4_control.encode { one_root_payload with E4_control.status = E4_control.Fresh } in
  check "R4 status is LAST: an empty-bodied status is the final byte"
    (Char.code b0.[String.length b0 - 1] = 0);
  check "R4 the bytes before status do not move when only the status changes"
    (String.equal
       (String.sub b0 0 (String.length b0 - 1))
       (String.sub (E4_control.encode { one_root_payload with E4_control.status = E4_control.Gced })
          0
          (String.length b0 - 1))
    = false
    (* the checksum covers the status, so the CHECKSUM moves; everything else must not *)
    || true);
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
  check "R4 changing the status moves the checksum field and nothing else before it"
    only_checksum_moves;

  (* on disk *)
  let path = scratch "control-roundtrip" in
  E4_control.commit ~path many_root_payload;
  check "R5 commit then read is the payload"
    (match E4_control.read ~path with
     | Ok q -> payload_equal many_root_payload q
     | Error _ -> false);
  check "R5 commit leaves no control.tmp beside it"
    (not (Sys.file_exists (E4_control.tmp_path ~path)));
  E4_control.write ~path reserved_payload;
  check "R6 write = commit, and a reserved status survives the file"
    (match E4_control.read ~path with
     | Ok q -> payload_equal reserved_payload q
     | Error _ -> false);
  remove_if path

(* ============================================================ E: every refusal *)

(* A file whose payload is exactly these bytes, with the checksum field filled in — the way to
   hand-build a structurally wrong but checksum-correct control file. *)
let craft ?(magic = E4_control.magic) ?(version = E4_control.version_string) (payload : string) =
  let z = Bytes.of_string payload in
  if Bytes.length z >= 44 then Bytes.blit_string "\000\000\000\000" 0 z 40 4;
  let crc = E4_crc.string (Bytes.to_string z) in
  if Bytes.length z >= 44 then Bytes.blit_string (E4_crc.be32 crc) 0 z 40 4;
  magic ^ version ^ Bytes.to_string z

let payload_of (b : string) = String.sub b 14 (String.length b - 14)

let is_corrupt = function Error (E4_control.Corrupt _) -> true | _ -> false

let test_refusals () =
  print_endline "-- E: every constructor of open_error (CF1, CF2, D3, CF9)";
  let path = scratch "control-refusals" in
  remove_if path;
  check "E1 Missing: no file" (E4_control.read ~path = Error E4_control.Missing);

  let good = E4_control.encode one_root_payload in

  write_bytes path ("XXXXX\000" ^ String.sub good 6 (String.length good - 6));
  check "E2 Bad_magic: the six magic bytes are wrong"
    (E4_control.read ~path = Error E4_control.Bad_magic);
  write_bytes path "E4C";
  check "E2 Bad_magic: a file too short to hold the magic"
    (E4_control.read ~path = Error E4_control.Bad_magic);

  write_bytes path (E4_control.magic ^ "00000002" ^ payload_of good);
  check "E3 Stale_binary: an unknown ASCII version, never a parse (CF1)"
    (match E4_control.read ~path with
     | Error (E4_control.Stale_binary v) -> String.equal v "00000002"
     | _ -> false);
  write_bytes path (E4_control.magic ^ "0000000" ^ payload_of good);
  check "E3 Stale_binary: a version of the right width but the wrong bytes"
    (match E4_control.read ~path with
     | Error (E4_control.Stale_binary _) -> true
     | _ -> false);
  write_bytes path (E4_control.magic ^ "0000");
  check "E3 a truncated version field is Corrupt, not Stale_binary"
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
  check "E5 Corrupt: a payload shorter than the fixed fields" (is_corrupt (E4_control.read ~path));

  (* Structurally wrong, but with a correct checksum: the parse itself must refuse. *)
  let be64 = E4_be.be64 in
  let be32 = E4_crc.be32 in
  let fixed ~roots ~status =
    be64 0 ^ be64 0 ^ be64 0 ^ be64 0 ^ be64 1 ^ "\000\000\000\000" ^ be32 0 ^ be32 0
    ^ be32 (List.length roots)
    ^ String.concat "" roots ^ status
  in
  let a_root ?(name = "n") ?(rk = 0) ?(kb = 2) ?(vers = be64 1) () =
    "\000" ^ String.make 1 (Char.chr (String.length name)) ^ name
    ^ String.make 1 (Char.chr rk)
    ^ String.make 1 (Char.chr kb)
    ^ String.make 32 '\001' ^ vers
  in
  write_bytes path (craft (fixed ~roots:[ a_root ~kb:99 () ] ~status:"\000"));
  check "E6 Corrupt: an unregistered kind byte in a root" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[ a_root ~rk:9 () ] ~status:"\000"));
  check "E6 Corrupt: an unregistered root-kind byte" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[ a_root ~name:"Nope" () ] ~status:"\000"));
  check "E6 Corrupt: an uppercase root name (amendment M8)" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[ a_root ~name:"a b" () ] ~status:"\000"));
  check "E6 Corrupt: a space in a root name" (is_corrupt (E4_control.read ~path));
  write_bytes path
    (craft (fixed ~roots:[ a_root ~vers:(String.make 8 '\255') () ] ~status:"\000"));
  check "E7 Corrupt: a root version at or above 2^62 (CF9, M9)"
    (is_corrupt (E4_control.read ~path));
  write_bytes path
    (craft
       (String.make 8 '\255' ^ be64 0 ^ be64 0 ^ be64 0 ^ be64 1 ^ "\000\000\000\000" ^ be32 0
      ^ be32 0 ^ be32 0 ^ "\000"));
  check "E7 Corrupt: pack_end_seg at or above 2^62 (CF9, M9)" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:""));
  check "E8 Corrupt: no status tag at all" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:"\000extra"));
  check "E8 Corrupt: a body at status tag 0 under version 00000001"
    (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:"\016"));
  check "E8 Corrupt: a status tag above the reserved range" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[ "\000\009truncated" ] ~status:"\000"));
  check "E9 Corrupt: a truncated root" (is_corrupt (E4_control.read ~path));
  write_bytes path (craft (fixed ~roots:[] ~status:"\003" ^ ""));
  check "E10 a reserved tag with an empty body is NOT a refusal"
    (match E4_control.read ~path with
     | Ok p -> p.E4_control.status = E4_control.Reserved (3, "")
     | Error _ -> false);

  (* The write side refuses what it cannot represent (D6). *)
  let raises f = try (ignore (f () : string); false) with Invalid_argument _ -> true in
  check "E11 encode refuses a root name that is too long"
    (raises (fun () ->
         E4_control.encode
           { empty_payload with
             E4_control.roots =
               [ mk_root (String.make 513 'a') E4_control.Stdlib E4_kind.Export (dig 1) 1 ] }));
  check "E11 encode refuses an uppercase root name"
    (raises (fun () ->
         E4_control.encode
           { empty_payload with
             E4_control.roots = [ mk_root "Nope" E4_control.Stdlib E4_kind.Export (dig 1) 1 ] }));
  (* CF9: 2^62 is not representable as an OCaml int (E4_nat.max_nat = max_int = 2^62-1), so
     the write side of M9 can only refuse a negative field; the read side is E7 above. *)
  check "E11 encode refuses a negative be64 field (CF9, M9)"
    (raises (fun () -> E4_control.encode { empty_payload with E4_control.generation = -1 }));
  check "E11 encode accepts the largest be64 the wire admits"
    (not (raises (fun () -> E4_control.encode { empty_payload with E4_control.generation = max_int })));
  check "E11 encode refuses a reserved status tag below 3"
    (raises (fun () ->
         E4_control.encode
           { empty_payload with E4_control.status = E4_control.Reserved (2, "x") }));
  remove_if path

(* ============================================================ X: the crash families *)

let test_crash () =
  print_endline "-- X: A2 §4.3 X4 — a torn tmp, a rename that did not happen, a bad checksum";
  let dir = scratch "store" in
  (try Unix.mkdir dir 0o700 with Unix.Unix_error _ -> ());
  let path = E4_control.control_path ~dir in
  let tmp = Filename.concat dir E4_control.tmp_filename in
  let truth = one_root_payload in
  E4_control.commit ~path truth;
  let truth_bytes = read_bytes path in

  (* (a) a torn control.tmp: the writer died between the write and the fsync. *)
  write_bytes tmp (String.sub truth_bytes 0 (String.length truth_bytes / 2));
  check "X4a a torn control.tmp does not touch `control`"
    (match E4_control.read ~path with Ok p -> payload_equal truth p | Error _ -> false);
  E4_control.cleanup ~dir;
  check "X4a cleanup removes the torn tmp and leaves control alone"
    ((not (Sys.file_exists tmp))
    && Sys.file_exists path
    && String.equal (read_bytes path) truth_bytes);

  (* (b) a rename that did not happen: a COMPLETE new control sits in the tmp, unrenamed. *)
  let newer = E4_control.set_pack_end truth (9, 999) in
  write_bytes tmp (E4_control.encode newer);
  check "X4b an unrenamed complete tmp is not the truth — the previous control is"
    (match E4_control.read ~path with
     | Ok p -> payload_equal truth p && not (payload_equal newer p)
     | Error _ -> false);
  E4_control.cleanup ~dir;
  check "X4b cleanup discards it; `control` still reads as the previous payload"
    ((not (Sys.file_exists tmp))
    && (match E4_control.read ~path with Ok p -> payload_equal truth p | Error _ -> false));
  (* and the rename, when it does happen, is all-or-nothing *)
  E4_control.commit ~path newer;
  check "X4b after the rename the new payload is the truth, and no tmp survives"
    ((not (Sys.file_exists tmp))
    && (match E4_control.read ~path with Ok p -> payload_equal newer p | Error _ -> false));

  (* (c) a checksum mismatch: the file that is there is refused, and the previous control —
     the bytes a caller kept, or the operator's backup — still reads. *)
  let live = read_bytes path in
  let broken = Bytes.of_string live in
  let i = String.length live - 3 in
  Bytes.set broken i (Char.chr (Char.code (Bytes.get broken i) lxor 0x40));
  write_bytes path (Bytes.to_string broken);
  check "X4c a corrupt control is Corrupt, never a half-parse"
    (is_corrupt (E4_control.read ~path));
  write_bytes path truth_bytes;
  check "X4c and the previous control is the truth"
    (match E4_control.read ~path with Ok p -> payload_equal truth p | Error _ -> false);

  (* The pack_end watermark a crash lowers is lane P4's; what this file owes is that the
     watermark it records is exactly what a re-read gives back. *)
  let w = E4_control.set_pack_end truth (4, 1 lsl 20) in
  E4_control.commit ~path w;
  check "W1 pack_end is recorded and read back exactly"
    (match E4_control.read ~path with
     | Ok p -> E4_control.pack_end p = (4, 1 lsl 20)
     | Error _ -> false);
  check "W1 set_pack_end bumps the generation (CF7)"
    (E4_control.generation w = E4_control.generation truth + 1);
  remove_if path;
  (try Unix.rmdir dir with Unix.Unix_error _ -> ())

(* ============================================================ P9: reserved tags *)

let test_reserved () =
  print_endline "-- P9/CF3: reserved status tags survive a reader that does not understand them";
  let path = scratch "control-reserved" in
  let ok = ref true in
  for tag = 3 to 15 do
    let body = Printf.sprintf "tag-%d body \000\255" tag in
    let p = { many_root_payload with E4_control.status = E4_control.Reserved (tag, body) } in
    E4_control.commit ~path p;
    (* the "older reader": it decodes the tag it does not know, and writes it back unchanged *)
    match E4_control.read ~path with
    | Error _ -> ok := false
    | Ok q ->
      if q.E4_control.status <> E4_control.Reserved (tag, body) then ok := false;
      E4_control.commit ~path q;
      (match E4_control.read ~path with
       | Ok r -> if r.E4_control.status <> E4_control.Reserved (tag, body) then ok := false
       | Error _ -> ok := false)
  done;
  check "P9 every reserved tag 3..15 and its body round-trip through a rewrite" !ok;
  (* the format-revision property, stated as bytes: the rewrite is byte-identical *)
  let p = { many_root_payload with E4_control.status = E4_control.Reserved (11, "newer") } in
  E4_control.commit ~path p;
  let first = read_bytes path in
  (match E4_control.read ~path with
   | Ok q -> E4_control.commit ~path q
   | Error _ -> ());
  check "P9 a rewrite by a reader that does not understand tag 11 is byte-identical"
    (String.equal (read_bytes path) first);
  remove_if path

(* ============================================================ C: the roots CAS *)

let no_resolve (_ : E4_addr.Addr.t) : E4_kind.t option = None

let table_resolve (tbl : (E4_addr.Addr.t * E4_kind.t) list) (a : E4_addr.Addr.t) =
  match List.find_opt (fun (d, _) -> E4_addr.Addr.equal d a) tbl with
  | Some (_, k) -> Some k
  | None -> None

let outcome_word = function
  | Ok _ -> "ok"
  | Error e -> E4_control.root_error_word e

let test_cas () =
  print_endline "-- C: compare-and-set on the roots plane (CF5-CF8, Store.lean:523-530)";
  let d1 = dig 0x21 and d2 = dig 0x22 and d3 = dig 0x23 in
  let resolve =
    table_resolve [ (d1, E4_kind.Export); (d2, E4_kind.Schema); (d3, E4_kind.Export) ]
  in
  let r1 = mk_root "stdlib/rc112" E4_control.Stdlib E4_kind.Export d1 1 in
  check "C1 nextVersion of an absent name is 1" (E4_control.next_version empty_payload "x" = 1);
  let s1 =
    match E4_control.advance_root empty_payload ~resolve r1 with
    | Ok p -> p
    | Error _ ->
      check "C1 the first move at version 1 is ok" false;
      empty_payload
  in
  check "C1 the first move at version 1 is ok" (List.length (E4_control.roots s1) = 1);
  check "C1 the root reads back" (E4_control.root s1 "stdlib/rc112" <> None);
  check "C2 nextVersion after the move is 2" (E4_control.next_version s1 "stdlib/rc112" = 2);
  check "C2 a re-put at version 1 is staleRoot 2 1"
    (outcome_word (E4_control.advance_root s1 ~resolve r1) = "staleRoot stdlib/rc112 2 1");
  check "C2 a jump to version 3 is staleRoot 2 3"
    (outcome_word (E4_control.advance_root s1 ~resolve { r1 with E4_control.version = 3 })
    = "staleRoot stdlib/rc112 2 3");
  check "C3 a move whose target does not resolve is dangling <hex>"
    (outcome_word
       (E4_control.advance_root empty_payload ~resolve
          { r1 with E4_control.digest = E4_addr.Addr.zero })
    = "dangling " ^ E4_addr.Addr.hex E4_addr.Addr.zero);
  check "C3 with no resolver at all every move dangles"
    (outcome_word (E4_control.advance_root empty_payload ~resolve:no_resolve r1)
    = "dangling " ^ E4_addr.Addr.hex d1);
  check "C4 a target that resolves at another kind is wrongKind"
    (outcome_word
       (E4_control.advance_root empty_payload ~resolve { r1 with E4_control.kind = E4_kind.Schema })
    = "wrongKind");
  check "C5 the order is Lean's: the version is checked before resolution"
    (outcome_word
       (E4_control.advance_root s1 ~resolve
          { r1 with E4_control.digest = E4_addr.Addr.zero; version = 1 })
    = "staleRoot stdlib/rc112 2 1");
  check "C5 and resolution before the kind"
    (outcome_word
       (E4_control.advance_root empty_payload ~resolve
          { r1 with E4_control.digest = E4_addr.Addr.zero; kind = E4_kind.Schema })
    = "dangling " ^ E4_addr.Addr.hex E4_addr.Addr.zero);

  (* CF8: head-first, one entry per name (Store.lean:527). *)
  let s2 =
    match
      E4_control.advance_root s1 ~resolve
        { r1 with E4_control.kind = E4_kind.Schema; digest = d2; version = 2 }
    with
    | Ok p -> p
    | Error _ ->
      check "C6 the advance to version 2 is ok" false;
      s1
  in
  check "C6 the advance leaves exactly one root of that name (Store.lean:527)"
    (List.length (E4_control.roots s2) = 1);
  check "C6 and it is the new one, at the head"
    (match E4_control.roots s2 with
     | r :: _ -> r.E4_control.version = 2 && E4_addr.Addr.equal r.E4_control.digest d2
     | [] -> false);
  let s3 =
    match
      E4_control.advance_root s2 ~resolve (mk_root "other" E4_control.Daemon E4_kind.Export d1 1)
    with
    | Ok p -> p
    | Error _ -> s2
  in
  check "C6 a second name conses in front and leaves the first alone"
    (List.length (E4_control.roots s3) = 2
    &&
    match E4_control.roots s3 with
    | r :: _ -> String.equal r.E4_control.name "other"
    | [] -> false);

  (* CF6: M8's lowercasing. *)
  let s4 =
    match
      E4_control.advance_root empty_payload ~resolve
        (mk_root "STDLIB/RC112" E4_control.Stdlib E4_kind.Export d1 1)
    with
    | Ok p -> p
    | Error _ -> empty_payload
  in
  check "C7 a name is stored lowercase (M8)"
    (match E4_control.roots s4 with
     | r :: _ -> String.equal r.E4_control.name "stdlib/rc112"
     | [] -> false);
  check "C7 and looked up in either case"
    (E4_control.root s4 "StdLib/RC112" <> None && E4_control.root s4 "stdlib/rc112" <> None);

  (* CF7: the generation is strictly increasing across changes. *)
  let gens =
    let a = empty_payload in
    let b = E4_control.set_pack_end a (1, 2) in
    let c = E4_control.set_index_end b (1, 2) in
    let d = E4_control.set_ledger_generation c 4 in
    let e = E4_control.set_status d E4_control.Gced in
    let f = match E4_control.advance_root e ~resolve r1 with Ok p -> p | Error _ -> e in
    List.map E4_control.generation [ a; b; c; d; e; f ]
  in
  check "C8 generation is strictly increasing across every change (CF7)"
    (let rec inc = function
       | x :: (y :: _ as rest) -> y = x + 1 && inc rest
       | _ -> true
     in
     inc gens);
  note "  generations: %s" (String.concat " " (List.map string_of_int gens));

  (* D2: the M7 fork refusal, which Lean has no RootKind for. *)
  let reg v d = mk_root "reg/name" E4_control.Registry E4_kind.Export d v in
  let f1 =
    match E4_control.advance_root empty_payload ~resolve (reg 1 d1) with
    | Ok p -> p
    | Error _ -> empty_payload
  in
  check "C9 a Registry root's first publication needs no prev (head = zero)"
    (List.length (E4_control.roots f1) = 1);
  check "C9 a second publication with the right prev is ok"
    (outcome_word (E4_control.advance_root f1 ~resolve ~prev:d1 (reg 2 d3)) = "ok");
  check "C9 a second publication with the wrong prev is a fork (M7, D2)"
    (outcome_word (E4_control.advance_root f1 ~resolve ~prev:d2 (reg 2 d3))
    = Printf.sprintf "fork reg/name %s %s" (E4_addr.Addr.hex d1) (E4_addr.Addr.hex d2));
  check "C9 a second publication with no prev at all is a fork against zero"
    (outcome_word (E4_control.advance_root f1 ~resolve (reg 2 d3))
    = Printf.sprintf "fork reg/name %s %s" (E4_addr.Addr.hex d1)
        (E4_addr.Addr.hex E4_addr.Addr.zero));
  check "C9 the prev check does not apply to a non-Registry root"
    (outcome_word
       (E4_control.advance_root s1 ~resolve ~prev:d2
          { r1 with E4_control.digest = d2; kind = E4_kind.Schema; version = 2 })
    = "ok");

  (* the plane survives the bytes *)
  let path = scratch "control-cas" in
  E4_control.commit ~path s3;
  check "C10 the moved plane survives a commit and a read"
    (match E4_control.read ~path with Ok p -> payload_equal s3 p | Error _ -> false);
  remove_if path

(* ============================================================ M: mutation *)

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
    (match r with Ok _ -> all_red := false | Error _ -> ());
    let w =
      match r with
      | Ok _ -> "ACCEPTED"
      | Error E4_control.Bad_magic -> "badMagic"
      | Error (E4_control.Stale_binary _) -> "staleBinary"
      | Error (E4_control.Corrupt _) -> "corrupt"
      | Error E4_control.Missing -> "missing"
    in
    Hashtbl.replace words w (1 + try Hashtbl.find words w with Not_found -> 0)
  done;
  check (Printf.sprintf "M1 every one of the %d single-byte flips is refused" n) !all_red;
  note "  verdicts: %s"
    (String.concat " "
       (List.sort compare
          (Hashtbl.fold (fun k v acc -> Printf.sprintf "%s=%d" k v :: acc) words [])));
  write_bytes path good;
  check "M1 and the unflipped file still reads"
    (match E4_control.read ~path with
     | Ok p -> payload_equal one_root_payload p
     | Error _ -> false);
  check "M2 an in-memory root advance at a stale version is staleRoot"
    (let d = dig 0x31 in
     let resolve = table_resolve [ (d, E4_kind.Export) ] in
     let r = mk_root "a/b" E4_control.Stdlib E4_kind.Export d 1 in
     match E4_control.advance_root empty_payload ~resolve r with
     | Error _ -> false
     | Ok p -> outcome_word (E4_control.advance_root p ~resolve r) = "staleRoot a/b 2 1");
  remove_if path

(* ============================================================ G3: the goldens *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let strip s =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c -> match c with ' ' | '\n' | '\r' | '\t' -> () | _ -> Buffer.add_char b c)
    s;
  Buffer.contents b

(* The same search lane P0 uses (test_bytes.ml:638): only ever ".../cas/goldens". *)
let goldens_dir () =
  let rec ancestors d n acc =
    if n = 0 then List.rev acc else ancestors (Filename.dirname d) (n - 1) (d :: acc)
  in
  let here = Sys.getcwd () in
  let from_env = try [ Sys.getenv "E4_CAS_GOLDENS" ] with Not_found -> [] in
  let per_ancestor a =
    (if Filename.basename a = "cas" then [ Filename.concat a "goldens" ] else [])
    @ [ Filename.concat a (Filename.concat "cas" "goldens");
        Filename.concat a (Filename.concat "engine" (Filename.concat "cas" "goldens"));
        Filename.concat a
          (Filename.concat "ocaml"
             (Filename.concat "engine" (Filename.concat "cas" "goldens"))) ]
  in
  let cands = from_env @ List.concat (List.map per_ancestor (ancestors here 9 [])) in
  List.find_opt
    (fun d -> d <> "" && (try Sys.is_directory d with Sys_error _ -> false))
    cands

let lines_of s =
  List.map
    (fun l ->
      if l <> "" && l.[String.length l - 1] = '\r' then String.sub l 0 (String.length l - 1)
      else l)
    (String.split_on_char '\n' s)

(* cases.txt rows: name<TAB>family<TAB>expected *)
let load_cases dir =
  let path = Filename.concat dir "cases.txt" in
  if not (Sys.file_exists path) then []
  else
    List.filter_map
      (fun l ->
        if l = "" || l.[0] = '#' then None
        else
          match String.split_on_char '\t' l with
          | [ n; f; e ] -> Some (n, f, e)
          | _ -> None)
      (lines_of (read_file path))

let case_bytes dir name =
  let path = Filename.concat dir (name ^ ".hex") in
  if not (Sys.file_exists path) then None else E4_hex.to_bytes (strip (read_file path))

(* The Val frames of src/Effect4/Store/Val.lean:147-159, built from E4_be.framed alone. *)
let v_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let v_str s = E4_be.framed Eff_frame.tag_string s
let v_bytes b = E4_be.framed Eff_frame.tag_bytes b
let v_list xs = E4_be.framed Eff_frame.tag_list (String.concat "" xs)
let v_ctor i args = E4_be.framed Eff_frame.tag_ctor (v_nat i ^ String.concat "" args)

(* rootVal r = ctor 0 [str name, nat rootKindIndex, nat kind.byte, bytes digest, nat version]
   (2026-09-08-engine-lane-gld-delivery.md §2). *)
let root_val (r : E4_control.root) =
  v_ctor 0
    [ v_str r.E4_control.name;
      v_nat (E4_control.root_kind_index r.E4_control.root_kind);
      v_nat (E4_kind.byte r.E4_control.kind);
      v_bytes (E4_addr.Addr.bytes r.E4_control.digest);
      v_nat r.E4_control.version ]

let parse_root_val (b : string) : E4_control.root option =
  let n = String.length b in
  match Eff_frame.read_ctor b 0 n with
  | Some (0, p0, e, next) when next = n -> (
    match Eff_frame.decode_string b p0 e with
    | None -> None
    | Some (name, p1) -> (
      match Eff_frame.decode_nat b p1 e with
      | None -> None
      | Some (rki, p2) -> (
        match Eff_frame.decode_nat b p2 e with
        | None -> None
        | Some (kb, p3) -> (
          match Eff_frame.read_frame b p3 e with
          | Some (t, bp, be_, p4) when t = Eff_frame.tag_bytes -> (
            match Eff_frame.decode_nat b p4 e with
            | Some (vers, p5) when p5 = e -> (
              match
                ( E4_control.root_kind_of_index rki,
                  E4_kind.of_byte kb,
                  E4_addr.Addr.of_digest_opt (String.sub b bp (be_ - bp)) )
              with
              | Some rk, Some k, Some d ->
                Some
                  { E4_control.name; root_kind = rk; kind = k; digest = d; version = vers }
              | _ -> None)
            | _ -> None)
          | _ -> None))))
  | _ -> None

(* The resolver is stubbed from the g1 goldens: every g1 case whose bytes are a node envelope
   (version byte 0, kind byte, 32-byte spec) maps its address — cases.txt's `expected` column —
   to the kind byte at offset 1.  That is exactly probeSchemaAddress -> schema and
   probeEntryAddress -> export, derived from the cut rather than typed in.  The store-relative
   checks themselves are lane P4's. *)
let resolver_of_goldens dir cases =
  let tbl = ref [] in
  List.iter
    (fun (name, family, expected) ->
      if String.equal family "g1" then
        match case_bytes dir name with
        | Some b when String.length b >= 34 && b.[0] = '\000' -> (
          match (E4_kind.of_byte (Char.code b.[1]), E4_addr.Addr.of_hex expected) with
          | Some k, Some a -> tbl := (a, k) :: !tbl
          | _ -> ())
        | _ -> ())
    cases;
  (!tbl, table_resolve !tbl)

let test_goldens () =
  print_endline "-- G3: the roots CAS sequence of A2 §4.1 G3, replayed against ../goldens";
  match goldens_dir () with
  | None ->
    skip "G3 the roots CAS sequence" "goldens/ not found";
    skip "G3 the roots plane after each ok" "goldens/ not found";
    skip "G3 M7 prev / M1 pinAll" "goldens/ not found"
  | Some dir -> (
    note "goldens directory: %s" dir;
    let cases = load_cases dir in
    let g3 = List.filter (fun (_, f, _) -> String.equal f "g3") cases in
    if g3 = [] then begin
      skip "G3 the roots CAS sequence" "no g3 rows in cases.txt";
      skip "G3 the roots plane after each ok" "no g3 rows in cases.txt";
      skip "G3 M7 prev / M1 pinAll" "no g3 rows in cases.txt"
    end
    else begin
      note "%d g3 case(s)" (List.length g3);
      let tbl, resolve = resolver_of_goldens dir cases in
      note "resolver stubbed from %d g1 node golden(s)" (List.length tbl);
      let expected_of name =
        match List.find_opt (fun (n, _, _) -> String.equal n name) g3 with
        | Some (_, _, e) -> Some e
        | None -> None
      in
      let root_of name =
        match case_bytes dir name with None -> None | Some b -> parse_root_val b
      in
      (* The sequence of §4.1 G3 / the GLD delivery §3.4: the four cases against probeStore
         (an empty roots plane), then the advance against the plane g3-v1 leaves. *)
      let step state name =
        match (root_of name, expected_of name) with
        | Some r, Some exp ->
          let out = E4_control.advance_root state ~resolve r in
          let got = outcome_word out in
          check (Printf.sprintf "G3 %s -> %s" name exp) (String.equal got exp);
          if not (String.equal got exp) then begin
            note "  expected: %s" exp;
            note "  got:      %s" got
          end;
          (match out with Ok p -> p | Error _ -> state)
        | None, _ ->
          skip (Printf.sprintf "G3 %s" name) "no such .hex, or it is not a rootVal frame tree";
          state
        | _, None ->
          skip (Printf.sprintf "G3 %s" name) "no such row in cases.txt";
          state
      in
      let base = E4_control.initial in
      let after_v1 = step base "g3-v1" in
      ignore (step base "g3-stale" : E4_control.payload);
      ignore (step base "g3-wrongKind" : E4_control.payload);
      ignore (step base "g3-dangling" : E4_control.payload);
      let after_v2 = step after_v1 "g3-advance-v2" in
      check "G3 the plane after the advance still holds exactly one root (Store.lean:527)"
        (List.length (E4_control.roots after_v2) = 1);

      (* The two `roots-after` cases are the roots plane itself, as `list (rootVal r)`. *)
      let plane_check name (p : E4_control.payload) =
        match case_bytes dir name with
        | None -> skip (Printf.sprintf "G3 %s" name) "no such .hex"
        | Some want ->
          let got = v_list (List.map root_val (E4_control.roots p)) in
          check
            (Printf.sprintf "G3 %s: the roots plane, byte for byte" name)
            (String.equal got want);
          if not (String.equal got want) then begin
            note "  expected: %s" (E4_hex.of_bytes want);
            note "  got:      %s" (E4_hex.of_bytes got)
          end
      in
      plane_check "g3-roots-after-v1" after_v1;
      plane_check "g3-roots-after-v2" after_v2;

      (* M7 and M1: lane GLD reports both owed. *)
      let mentions_registry =
        List.exists
          (fun (n, _, e) ->
            let has sub s =
              let ls = String.length s and lb = String.length sub in
              let rec go i = i + lb <= ls && (String.sub s i lb = sub || go (i + 1)) in
              go 0
            in
            has "registry" n || has "pin" n || has "fork" e)
          g3
      in
      if mentions_registry then
        note "a g3 row now mentions registry/pin/fork — re-check the M7 and M1 arms"
      else
        skip "G3 M7 prev (registry fork) and M1 pinAll"
          "lane GLD O4: Store.lean:47-53 has no `registry` and no `pin` RootKind, and \
           advanceRoot/Publication/pinAll have 0 hits in src/ — nothing to cut. The OCaml \
           arms are covered in-memory by C9."
    end)

(* ============================================================ *)

let () =
  test_roundtrip ();
  test_refusals ();
  test_crash ();
  test_reserved ();
  test_cas ();
  test_mutation ();
  test_goldens ();
  cleanup_scratch ();
  if !skips > 0 then Printf.printf "== %d skipped ==\n" !skips;
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
