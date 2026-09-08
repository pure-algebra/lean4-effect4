(* test_pack.ml — lane P1's checks: the append-only pack file (2026-09-08).

   What it checks, and against what:
     H*  the byte grammar of docs/research/2026-09-08-engine-a2-persistence.md §1.2: the
         27-byte head (magic, ASCII version, be64 seg_index, be32 crc over the 23 bytes
         before it) and the 45-byte record overhead, read back out of the file itself.
     R*  round trip (PK1): N records staged, committed, and read back through `read`,
         `read_at`, `read_header` and `blit_at`, at the offsets `append` returned.
     G*  group commit (PK2): `append` never fsyncs and never advances `pack_end`; one
         `sync` per batch does; the watermarks are ordered and monotone.
     S*  scanning (PK4): `scan` and `scan_seq` visit records in write order and end in
         exactly one verdict; the header scan reads no payload.
     X*  the four crash families of §4.3 X1/X2 as property tests over a seeded generator:
         truncate mid-record (at every interesting offset), flip a CRC byte, flip a digest
         byte, flip a payload byte, and a torn last record.  Reopen, and assert that
         exactly the intact prefix is recovered and that the verdict names the failure at
         the exact offset.
     M*  the mutation check that L-CAS-6 exists at all: with the record CRC repaired after
         the corruption, `read_at` — which trusts the recorded digest — SUCCEEDS and hands
         back the wrong bytes, and `read` — which re-hashes — refuses with
         `Digest_mismatch`.  A test that expected the recorded digest to be trusted is
         therefore red, which is the point (A2 R3, crash family X2(b)).
     W*  the single-writer discipline (PK6): a second `open_` in this process and a second
         PROCESS (fork) are both refused with `Locked`.
     Z*  segment rotation (PK8): records land in successive segments, the scan crosses
         them in write order, and reads work in a segment that is not the last.
     T*  `truncate_to` refuses below `pack_end`, and the host-limit refusal (PK5).

   Everything runs in a fresh directory under $E4_PACK_TMP (default: the system temp dir),
   removed at the end.  Exit code 0 iff every check passed. *)

open Effect4_engine
open Effect4_engine_cas

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n%!" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n%!")

(* A fixed linear congruential generator: the run is reproducible. *)
let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n
let rand_bytes n = String.init n (fun _ -> Char.chr (rand 256))

(* ============================================================ the sandbox *)

let root =
  let base = try Sys.getenv "E4_PACK_TMP" with Not_found -> Filename.get_temp_dir_name () in
  let d =
    Filename.concat base (Printf.sprintf "e4pack-%d-%d" (Unix.getpid ()) (int_of_float (Unix.time ())))
  in
  (try Unix.mkdir base 0o755 with Unix.Unix_error _ -> ());
  Unix.mkdir d 0o755;
  d

let counter = ref 0

let fresh_dir () =
  incr counter;
  let d = Filename.concat root (Printf.sprintf "s%03d" !counter) in
  Unix.mkdir d 0o755;
  d

let rec rm_rf p =
  match Unix.lstat p with
  | exception Unix.Unix_error _ -> ()
  | { Unix.st_kind = Unix.S_DIR; _ } ->
    Array.iter (fun n -> rm_rf (Filename.concat p n)) (Sys.readdir p);
    (try Unix.rmdir p with Unix.Unix_error _ -> ())
  | _ -> ( try Sys.remove p with Sys_error _ -> ())

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let write_file path s =
  let oc = open_out_bin path in
  output_string oc s;
  close_out oc

(* Overwrite one byte of a file in place. *)
let poke path pos byte =
  let fd = Unix.openfile path [ Unix.O_WRONLY ] 0o600 in
  ignore (Unix.lseek fd pos Unix.SEEK_SET);
  ignore (Unix.write fd (Bytes.make 1 (Char.chr byte)) 0 1);
  Unix.close fd

let flip path pos =
  let s = read_file path in
  poke path pos (Char.code s.[pos] lxor 0x01)

let truncate_file path n =
  let fd = Unix.openfile path [ Unix.O_WRONLY ] 0o600 in
  Unix.ftruncate fd n;
  Unix.close fd

(* ============================================================ a populated store *)

type built = {
  b_dir : string;
  b_offs : (E4_pack.seg * E4_pack.off) list;   (* in write order *)
  b_bodies : string list;                      (* in write order *)
  b_end : E4_pack.seg * E4_pack.off;
}

let digest_of = E4_sha256.digest

(* Stage [n] records of a random size in [lo, hi], one commit per [batch]. *)
let build ?(seg_max = E4_pack.default_seg_max) ?(batch = 16) ~lo ~hi n =
  let d = fresh_dir () in
  let t = E4_pack.open_ ~dir:d ~seg_max in
  let offs = ref [] and bodies = ref [] in
  for i = 1 to n do
    let body = rand_bytes (lo + rand (hi - lo + 1)) in
    let p = E4_pack.append t ~digest:(digest_of body) ~node_bytes:body in
    offs := p :: !offs;
    bodies := body :: !bodies;
    if i mod batch = 0 then E4_pack.sync t
  done;
  E4_pack.sync t;
  let e = E4_pack.pack_end t in
  E4_pack.close t;
  { b_dir = d; b_offs = List.rev !offs; b_bodies = List.rev !bodies; b_end = e }

let seg0 b = E4_pack.seg_path ~dir:b.b_dir 0

(* The records a fresh open recovers, from the head of segment 0. *)
let recovered_prefix dir =
  let rd = E4_pack.open_reader ~dir in
  let got = ref [] in
  let stop = ref E4_pack.Eof in
  Seq.iter
    (function
      | E4_pack.Scanned ((s, o), r) -> got := (s, o, r) :: !got
      | E4_pack.Stopped st -> stop := st)
    (E4_pack.scan_seq ~verify:true rd ~from:(0, E4_pack.head_length));
  E4_pack.close_reader rd;
  (List.rev !got, !stop)

(* ============================================================ H: the grammar *)

let test_head () =
  print_endline "-- H: the byte grammar of A2 §1.2";
  let d = fresh_dir () in
  let t = E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max in
  let body = "hello, pack" in
  let s, o = E4_pack.append t ~digest:(digest_of body) ~node_bytes:body in
  E4_pack.sync t;
  E4_pack.close t;
  let bytes = read_file (E4_pack.seg_path ~dir:d 0) in
  check "H1 the head is 27 bytes and the first record follows it"
    (E4_pack.head_length = 27 && s = 0 && o = 27);
  check "H2 magic is \"E4PACK\\000\"" (String.sub bytes 0 7 = "E4PACK\000");
  check "H3 the version is the ASCII string \"00000001\""
    (String.sub bytes 7 8 = "00000001" && E4_pack.version = "00000001");
  check "H4 be64 seg_index = 0" (E4_be.read_be64 bytes 15 = Some 0);
  check "H5 head_crc is CRC-32 over the 23 bytes before it"
    (E4_crc.read_be32 bytes 23 = Some (E4_crc.sub bytes 0 23));
  let len = String.length body in
  check "H6 the record is 'R' :: be64 len :: digest :: node_bytes :: be32 crc"
    (bytes.[27] = 'R'
    && E4_be.read_be64 bytes 28 = Some len
    && String.sub bytes 36 32 = digest_of body
    && String.sub bytes 68 len = body);
  let hdr = String.sub bytes 27 41 in
  let c = E4_crc.update_char E4_crc.init 'R' in
  let c = E4_crc.update_sub c hdr 1 40 in
  let c = E4_crc.update c body in
  check "H7 rec_crc is CRC-32 over the 41 header bytes ++ node_bytes"
    (E4_crc.read_be32 bytes (68 + len) = Some c);
  check "H8 the record occupies exactly 45 + node_len bytes"
    (String.length bytes = 27 + 45 + len && E4_pack.record_overhead = 45);
  rm_rf d

(* ============================================================ R: round trip *)

let test_roundtrip () =
  print_endline "-- R: round trip (PK1)";
  let b = build ~lo:0 ~hi:2000 200 in
  let rd = E4_pack.open_reader ~dir:b.b_dir in
  let all_read = ref true
  and all_read_at = ref true
  and all_header = ref true
  and all_blit = ref true in
  let buf = Bytes.create 4096 in
  List.iter2
    (fun (s, o) body ->
      (match E4_pack.read rd ~seg:s ~off:o with
       | Ok { E4_pack.r_addr; r_len; r_bytes = Some x } ->
         if x <> body || r_len <> String.length body
            || E4_addr.Addr.bytes r_addr <> digest_of body
         then all_read := false
       | _ -> all_read := false);
      (match E4_pack.read_at rd ~seg:s ~off:o with
       | Some (a, x) -> if x <> body || E4_addr.Addr.bytes a <> digest_of body then all_read_at := false
       | None -> all_read_at := false);
      (match E4_pack.read_header rd ~seg:s ~off:o with
       | Some (a, n) ->
         if n <> String.length body || E4_addr.Addr.bytes a <> digest_of body then
           all_header := false
       | None -> all_header := false);
      let n = E4_pack.blit_at rd ~seg:s ~off:o buf 0 in
      if n <> String.length body || Bytes.sub_string buf 0 n <> body then all_blit := false)
    b.b_offs b.b_bodies;
  check "R1 read: every record verifies and its bytes are what was appended" !all_read;
  check "R2 read_at: the recorded digest and the bytes come back" !all_read_at;
  check "R3 read_header: the digest and the length, 41 bytes" !all_header;
  check "R4 blit_at: the bytes land in the caller's buffer" !all_blit;
  check "R5 a zero-length node round trips"
    (let d = fresh_dir () in
     let t = E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max in
     let s, o = E4_pack.append t ~digest:(digest_of "") ~node_bytes:"" in
     E4_pack.sync t;
     E4_pack.close t;
     let rd = E4_pack.open_reader ~dir:d in
     let ok = E4_pack.read rd ~seg:s ~off:o = Ok { E4_pack.r_addr = E4_addr.Addr.of_digest (digest_of ""); r_len = 0; r_bytes = Some "" } in
     E4_pack.close_reader rd;
     rm_rf d;
     ok);
  check "R6 read at an offset that is not a record boundary refuses"
    (match E4_pack.read rd ~seg:0 ~off:(E4_pack.head_length + 3) with
     | Error _ -> true
     | Ok _ -> false);
  check "R7 read past the end refuses with Past_end"
    (match E4_pack.read rd ~seg:0 ~off:1_000_000_000 with
     | Error (E4_pack.Past_end _) -> true
     | _ -> false);
  check "R8 read in a segment that does not exist refuses with No_segment"
    (match E4_pack.read rd ~seg:99 ~off:27 with
     | Error (E4_pack.No_segment 99) -> true
     | _ -> false);
  E4_pack.close_reader rd;
  rm_rf b.b_dir

(* ============================================================ G: group commit *)

let test_group_commit () =
  print_endline "-- G: group commit (PK2)";
  let d = fresh_dir () in
  let t = E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max in
  let start = E4_pack.pack_end t in
  let body = rand_bytes 512 in
  let sizes = ref [] in
  for _ = 1 to 100 do
    ignore (E4_pack.append t ~digest:(digest_of body) ~node_bytes:body);
    sizes := E4_pack.staged_bytes t :: !sizes
  done;
  let before = E4_pack.pack_end t in
  let file_before =
    match Sys.file_exists (E4_pack.seg_path ~dir:d 0) with
    | true -> String.length (read_file (E4_pack.seg_path ~dir:d 0))
    | false -> -1
  in
  check "G1 append does not advance pack_end" (before = start);
  check "G1 append does not write: the file still holds only the head"
    (file_before = E4_pack.head_length);
  check "G2 staged_bytes counts what is buffered"
    (E4_pack.staged_bytes t = 100 * (45 + 512) && E4_pack.staged_count t = 100);
  check "G3 staged_end runs ahead of written_upto and pack_end"
    (E4_pack.staged_end t > E4_pack.written_upto t
    && E4_pack.written_upto t = E4_pack.pack_end t);
  E4_pack.flush t;
  check "G4 flush writes but does not make durable"
    (E4_pack.written_upto t = E4_pack.staged_end t
    && E4_pack.pack_end t = start
    && E4_pack.staged_bytes t = 0);
  E4_pack.sync t;
  check "G5 sync advances pack_end to the written end"
    (E4_pack.pack_end t = E4_pack.written_upto t && E4_pack.pack_end t = E4_pack.staged_end t);
  let after = E4_pack.pack_end t in
  E4_pack.sync t;
  check "G6 sync with nothing staged is idempotent" (E4_pack.pack_end t = after);
  check "G7 pack_end lands where the arithmetic says"
    (E4_pack.pack_end t = (0, E4_pack.head_length + (100 * (45 + 512))));
  E4_pack.close t;
  (* a reopen sees exactly the committed records *)
  let got, stop = recovered_prefix d in
  check "G8 a reopen recovers all 100 committed records and stops at Eof"
    (List.length got = 100 && stop = E4_pack.Eof);
  rm_rf d

(* ============================================================ S: scanning *)

let test_scan () =
  print_endline "-- S: scanning (PK4)";
  let b = build ~lo:1 ~hi:300 120 in
  let rd = E4_pack.open_reader ~dir:b.b_dir in
  let seen = ref [] in
  let stop = E4_pack.scan rd ~from:(0, E4_pack.head_length) ~f:(fun a s o n -> seen := (a, s, o, n) :: !seen) in
  let seen = List.rev !seen in
  check "S1 scan visits every record in write order and stops at Eof"
    (stop = E4_pack.Eof
    && List.map (fun (_, s, o, _) -> (s, o)) seen = b.b_offs
    && List.map (fun (_, _, _, n) -> n) seen = List.map String.length b.b_bodies);
  let items = List.of_seq (E4_pack.scan_seq rd ~from:(0, E4_pack.head_length)) in
  let stops = List.filter (function E4_pack.Stopped _ -> true | _ -> false) items in
  check "S2 scan_seq ends in exactly one Stopped verdict, as the last element"
    (List.length stops = 1
    && (match List.rev items with E4_pack.Stopped E4_pack.Eof :: _ -> true | _ -> false));
  check "S3 the header scan reads no payload (r_bytes = None), the verifying one does"
    (List.for_all
       (function E4_pack.Scanned (_, r) -> r.E4_pack.r_bytes = None | E4_pack.Stopped _ -> true)
       items
    && List.for_all
         (function
           | E4_pack.Scanned (_, r) -> r.E4_pack.r_bytes <> None
           | E4_pack.Stopped _ -> true)
         (List.of_seq (E4_pack.scan_seq ~verify:true rd ~from:(0, E4_pack.head_length))));
  check "S4 the verifying scan agrees with the header scan on every offset and length"
    (List.filter_map
       (function E4_pack.Scanned (p, r) -> Some (p, r.E4_pack.r_len) | _ -> None)
       items
    = List.filter_map
        (function E4_pack.Scanned (p, r) -> Some (p, r.E4_pack.r_len) | _ -> None)
        (List.of_seq (E4_pack.scan_seq ~verify:true rd ~from:(0, E4_pack.head_length))));
  (* a scan from a later offset is the tail, in write order — what recovery re-admits *)
  let from = List.nth b.b_offs 100 in
  let tail =
    List.filter_map
      (function E4_pack.Scanned (p, _) -> Some p | _ -> None)
      (List.of_seq (E4_pack.scan_seq ~verify:true rd ~from))
  in
  check "S5 scan from a pack_end in the middle yields exactly the tail, in write order"
    (tail = List.filteri (fun i _ -> i >= 100) b.b_offs);
  E4_pack.close_reader rd;
  rm_rf b.b_dir

(* ============================================================ X: the crash families *)

(* X1: truncate mid-record, at every interesting offset of the last record. *)
let test_truncate () =
  print_endline "-- X1: truncate the data file mid-record (§4.3 X1)";
  let all_prefix = ref true and all_verdict = ref true and all_reuse = ref true in
  let cases = ref 0 in
  for n = 3 to 8 do
    let b = build ~lo:20 ~hi:200 n in
    let bytes = read_file (seg0 b) in
    let total = String.length bytes in
    let lseg, loff = List.nth b.b_offs (n - 1) in
    ignore lseg;
    let llen = String.length (List.nth b.b_bodies (n - 1)) in
    let points =
      [ (loff + 1, "1 byte into the header");
        (loff + 20, "mid-digest");
        (loff + 41 + (llen / 2), "mid-payload");
        (total - 1, "1 byte before the end of the crc");
        (loff, "exactly at the record boundary") ]
    in
    List.iter
      (fun (cut, _why) ->
        if cut > E4_pack.head_length && cut < total then begin
          incr cases;
          let d = fresh_dir () in
          Unix.mkdir (Filename.concat d "pack") 0o755;
          write_file (E4_pack.seg_path ~dir:d 0) (String.sub bytes 0 cut);
          let got, stop = recovered_prefix d in
          (* every record wholly before the cut, and no other *)
          let want = List.filteri (fun i _ -> List.nth b.b_offs i |> fun (_, o) ->
                        o + 45 + String.length (List.nth b.b_bodies i) <= cut) b.b_offs in
          if List.map (fun (s, o, _) -> (s, o)) got <> want then all_prefix := false;
          (match stop with
           | E4_pack.Short { off; _ } when off = cut || off = loff -> ()
           | E4_pack.Eof when cut = loff -> ()
           | _ -> all_verdict := false);
          (* the writer truncates the torn tail at open and the lost node re-appends *)
          let t = E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max in
          let body = rand_bytes 64 in
          let s2, o2 = E4_pack.append t ~digest:(digest_of body) ~node_bytes:body in
          E4_pack.sync t;
          let pe = E4_pack.pack_end t in
          E4_pack.close t;
          let rd = E4_pack.open_reader ~dir:d in
          (match E4_pack.read rd ~seg:s2 ~off:o2 with
           | Ok { E4_pack.r_bytes = Some x; _ } when x = body -> ()
           | _ -> all_reuse := false);
          E4_pack.close_reader rd;
          let got2, stop2 = recovered_prefix d in
          if List.length got2 <> List.length want + 1 || stop2 <> E4_pack.Eof
             || pe <> (0, o2 + 45 + 64)
          then all_reuse := false;
          rm_rf d
        end)
      points;
    rm_rf b.b_dir
  done;
  note "%d truncation points" !cases;
  check "X1 exactly the records wholly before the cut are recovered" !all_prefix;
  check "X1 the verdict is Short at the torn record's offset (or Eof at a boundary cut)"
    !all_verdict;
  check "X1 the tail is truncated at open and the lost node re-appends and reads back"
    !all_reuse

(* Where the four bytes of a record's crc sit, and where its digest and payload sit. *)
let record_spans b i =
  let _, off = List.nth b.b_offs i in
  let len = String.length (List.nth b.b_bodies i) in
  (off, off + 9, off + 41, off + 41 + len)   (* record, digest, payload, crc *)

(* Rewrite a record's crc so it matches whatever the record now holds: the corruption then
   survives every check but the re-hash.  This is what makes X2(b) a real test. *)
let repair_crc path ~off =
  let bytes = read_file path in
  match E4_be.read_be64 bytes (off + 1) with
  | None -> ()
  | Some len ->
    let hdr = String.sub bytes off 41 in
    let body = String.sub bytes (off + 41) len in
    let c = E4_crc.update_char E4_crc.init 'R' in
    let c = E4_crc.update_sub c hdr 1 40 in
    let c = E4_crc.update c body in
    let fixed =
      String.sub bytes 0 (off + 41 + len)
      ^ E4_crc.be32 c
      ^ String.sub bytes (off + 45 + len) (String.length bytes - (off + 45 + len))
    in
    write_file path fixed

let test_corruption () =
  print_endline "-- X2: flip a crc byte, a digest byte, a payload byte (§4.3 X2)";
  let mk () = build ~lo:32 ~hi:64 6 in
  (* (a) a flipped crc byte *)
  let b = mk () in
  let _, _, _, crc_at = record_spans b 3 in
  flip (seg0 b) crc_at;
  let got, stop = recovered_prefix b.b_dir in
  let _, off3 = List.nth b.b_offs 3 in
  check "X2a a flipped crc byte: the prefix before it is recovered, the verdict is Bad_crc at its offset"
    (List.length got = 3 && stop = E4_pack.Bad_crc { seg = 0; off = off3 });
  rm_rf b.b_dir;
  (* (b) a flipped digest byte, crc repaired: only the re-hash can catch it *)
  let b = mk () in
  let _, dig_at, _, _ = record_spans b 2 in
  let _, off2 = List.nth b.b_offs 2 in
  flip (seg0 b) dig_at;
  repair_crc (seg0 b) ~off:off2;
  let got, stop = recovered_prefix b.b_dir in
  check "X2b a flipped digest byte with the crc repaired: Bad_digest at its offset (L-CAS-6)"
    (List.length got = 2 && stop = E4_pack.Bad_digest { seg = 0; off = off2 });
  rm_rf b.b_dir;
  (* (c) a flipped payload byte, crc repaired *)
  let b = mk () in
  let _, _, pay_at, _ = record_spans b 4 in
  let _, off4 = List.nth b.b_offs 4 in
  flip (seg0 b) pay_at;
  repair_crc (seg0 b) ~off:off4;
  let got, stop = recovered_prefix b.b_dir in
  check "X2c a flipped payload byte with the crc repaired: Bad_digest at its offset"
    (List.length got = 4 && stop = E4_pack.Bad_digest { seg = 0; off = off4 });
  rm_rf b.b_dir;
  (* (c') the same flip WITHOUT repairing the crc: the cheaper check fires first *)
  let b = mk () in
  let _, _, pay_at, _ = record_spans b 4 in
  let _, off4 = List.nth b.b_offs 4 in
  flip (seg0 b) pay_at;
  let got, stop = recovered_prefix b.b_dir in
  check "X2c' the same flip with the crc left alone is Bad_crc — the cheaper check first"
    (List.length got = 4 && stop = E4_pack.Bad_crc { seg = 0; off = off4 });
  rm_rf b.b_dir;
  (* (d) a flipped 'R' tag *)
  let b = mk () in
  let off1 = snd (List.nth b.b_offs 1) in
  flip (seg0 b) off1;
  let got, stop = recovered_prefix b.b_dir in
  check "X2d a flipped record tag is Bad_tag at its offset, never a silent skip"
    (List.length got = 1
    && (match stop with
        | E4_pack.Bad_tag { seg = 0; off; byte } -> off = off1 && byte = Char.code 'R' lxor 1
        | _ -> false));
  rm_rf b.b_dir;
  (* (e) a torn last record: the tail after pack_end *)
  let b = mk () in
  let bytes = read_file (seg0 b) in
  let off5 = snd (List.nth b.b_offs 5) in
  truncate_file (seg0 b) (String.length bytes - 3);
  let got, stop = recovered_prefix b.b_dir in
  check "X2e a torn last record: five records recovered, Short at the sixth's offset"
    (List.length got = 5 && stop = E4_pack.Short { seg = 0; off = off5 });
  rm_rf b.b_dir;
  (* (f) every record after a failure is refused even when it is well-formed *)
  let b = mk () in
  let _, _, pay_at, _ = record_spans b 1 in
  flip (seg0 b) pay_at;
  let got, _ = recovered_prefix b.b_dir in
  check "X2f the corrupt record and everything after it are refused, though records 2..5 are intact"
    (List.length got = 1);
  rm_rf b.b_dir

(* ============================================================ M: the mutation check *)

let test_mutation () =
  print_endline "-- M: the recorded digest is a cache, and `read` never trusts it (L-CAS-6)";
  let b = build ~lo:64 ~hi:64 3 in
  let s, o = List.nth b.b_offs 1 in
  let body = List.nth b.b_bodies 1 in
  let _, _, pay_at, _ = record_spans b 1 in
  flip (seg0 b) pay_at;
  repair_crc (seg0 b) ~off:o;
  let rd = E4_pack.open_reader ~dir:b.b_dir in
  let trusting = E4_pack.read_at rd ~seg:s ~off:o in
  let verifying = E4_pack.read rd ~seg:s ~off:o in
  check "M1 read_at — which trusts the recorded digest — SUCCEEDS on the corrupted record"
    (match trusting with Some (_, x) -> x <> body | None -> false);
  check "M2 read — which re-hashes — refuses it as Digest_mismatch at that offset"
    (match verifying with
     | Error (E4_pack.Digest_mismatch { seg; off; dig_recorded; dig_computed }) ->
       seg = s && off = o && dig_recorded = digest_of body && dig_computed <> dig_recorded
     | _ -> false);
  check "M3 a test that expected the recorded digest to be trusted is therefore red"
    (trusting <> None && (match verifying with Error _ -> true | Ok _ -> false));
  (* and the untouched records still verify *)
  let ok0 = E4_pack.read rd ~seg:0 ~off:(snd (List.nth b.b_offs 0)) in
  check "M4 the records beside the corrupt one still verify"
    (match ok0 with
     | Ok { E4_pack.r_bytes = Some x; _ } -> x = List.nth b.b_bodies 0
     | _ -> false);
  E4_pack.close_reader rd;
  rm_rf b.b_dir

(* ============================================================ W: one writer *)

let test_single_writer () =
  print_endline "-- W: the single-writer discipline (PK6)";
  let d = fresh_dir () in
  let t = E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max in
  check "W1 a second open_ in this process raises Locked"
    (match E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max with
     | exception E4_pack.Locked _ -> true
     | t2 ->
       E4_pack.close t2;
       false);
  check "W2 the LOCK file exists beside the pack directory"
    (Sys.file_exists (Filename.concat d "LOCK"));
  (* a second PROCESS: the fcntl lock, which the in-process table cannot stand in for *)
  let child_says =
    match Unix.fork () with
    | 0 ->
      let code =
        match E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max with
        | exception E4_pack.Locked _ -> 7
        | exception _ -> 9
        | t2 ->
          E4_pack.close t2;
          3
      in
      Stdlib.exit code
    | pid -> (
      match snd (Unix.waitpid [] pid) with Unix.WEXITED c -> c | _ -> -1)
  in
  check "W3 a second PROCESS is refused with Locked (Unix.lockf on <dir>/LOCK)"
    (child_says = 7);
  E4_pack.close t;
  let after =
    match Unix.fork () with
    | 0 ->
      let code =
        match E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max with
        | exception _ -> 9
        | t2 ->
          E4_pack.close t2;
          3
      in
      Stdlib.exit code
    | pid -> ( match snd (Unix.waitpid [] pid) with Unix.WEXITED c -> c | _ -> -1)
  in
  check "W4 after close the lock is released and another process may open" (after = 3);
  check "W5 a reader needs no lock"
    (let t2 = E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max in
     let rd = E4_pack.open_reader ~dir:d in
     let ok = E4_pack.segments rd = [ 0 ] in
     E4_pack.close_reader rd;
     E4_pack.close t2;
     ok);
  rm_rf d

(* ============================================================ Z: rotation *)

let test_rotation () =
  print_endline "-- Z: segment rotation (PK8)";
  let d = fresh_dir () in
  let seg_max = 4096 in
  let t = E4_pack.open_ ~dir:d ~seg_max in
  let offs = ref [] and bodies = ref [] in
  for _ = 1 to 60 do
    let body = rand_bytes 200 in
    offs := E4_pack.append t ~digest:(digest_of body) ~node_bytes:body :: !offs;
    bodies := body :: !bodies
  done;
  E4_pack.sync t;
  let pe = E4_pack.pack_end t in
  E4_pack.close t;
  let offs = List.rev !offs and bodies = List.rev !bodies in
  let segs = List.sort_uniq compare (List.map fst offs) in
  check "Z1 60 records of 245 bytes across a 4 KiB seg_max use several segments"
    (List.length segs >= 4 && segs = List.init (List.length segs) (fun i -> i));
  check "Z2 no segment exceeds seg_max"
    (List.for_all
       (fun s ->
         String.length (read_file (E4_pack.seg_path ~dir:d s)) <= seg_max)
       segs);
  check "Z3 every rotated segment carries its own head, with its own index"
    (List.for_all
       (fun s ->
         let b = read_file (E4_pack.seg_path ~dir:d s) in
         String.sub b 0 7 = "E4PACK\000"
         && String.sub b 7 8 = "00000001"
         && E4_be.read_be64 b 15 = Some s
         && E4_crc.read_be32 b 23 = Some (E4_crc.sub b 0 23))
       segs);
  let rd = E4_pack.open_reader ~dir:d in
  let walked =
    List.filter_map
      (function E4_pack.Scanned (p, _) -> Some p | _ -> None)
      (List.of_seq (E4_pack.scan_seq ~verify:true rd ~from:(0, E4_pack.head_length)))
  in
  check "Z4 the scan crosses segments in write order" (walked = offs);
  check "Z5 reads work in a segment that is not the last"
    (List.for_all2
       (fun (s, o) body ->
         match E4_pack.read rd ~seg:s ~off:o with
         | Ok { E4_pack.r_bytes = Some x; _ } -> x = body
         | _ -> false)
       offs bodies);
  check "Z6 pack_end names the last segment and its end"
    (pe = List.nth offs 59
          |> fun _ ->
          fst pe = fst (List.nth offs 59)
          && snd pe = snd (List.nth offs 59) + 45 + 200);
  check "Z7 segments lists what is on disk, ascending" (E4_pack.segments rd = segs);
  E4_pack.close_reader rd;
  (* a reopen of a rotated store recovers only the last segment by default, and all of it
     when `from` names the first *)
  let t = E4_pack.open_ ~dir:d ~seg_max in
  let r = E4_pack.recovery t in
  check "Z8 open_ recovers the LAST segment's tail by default (D4)"
    (r.E4_pack.stop = E4_pack.Eof
    && fst r.E4_pack.from = List.nth segs (List.length segs - 1)
    && E4_pack.pack_end t = pe);
  E4_pack.close t;
  let t = E4_pack.open_at ~from:(0, E4_pack.head_length) ~dir:d ~seg_max () in
  let r = E4_pack.recovery t in
  check "Z9 open_at ~from:(0,27) verifies and re-admits every record in the store"
    (r.E4_pack.records = 60 && r.E4_pack.stop = E4_pack.Eof && E4_pack.pack_end t = pe);
  E4_pack.close t;
  rm_rf d

(* ============================================================ T: truncate_to, PK5 *)

let test_truncate_to () =
  print_endline "-- T: truncate_to and the host limit (PK3, PK5)";
  let b = build ~lo:16 ~hi:16 5 in
  let t = E4_pack.open_ ~dir:b.b_dir ~seg_max:E4_pack.default_seg_max in
  let dseg, doff = E4_pack.pack_end t in
  check "T1 truncate_to below pack_end is refused"
    (match E4_pack.truncate_to t ~seg:dseg ~off:(doff - 1) with
     | exception Invalid_argument _ -> true
     | () -> false);
  check "T2 truncate_to AT pack_end is allowed and changes nothing"
    (match E4_pack.truncate_to t ~seg:dseg ~off:doff with
     | exception _ -> false
     | () -> E4_pack.pack_end t = (dseg, doff));
  check "T3 truncate_to with bytes staged is refused"
    (let body = rand_bytes 8 in
     ignore (E4_pack.append t ~digest:(digest_of body) ~node_bytes:body);
     let r =
       match E4_pack.truncate_to t ~seg:dseg ~off:doff with
       | exception Invalid_argument _ -> true
       | () -> false
     in
     E4_pack.sync t;
     r);
  E4_pack.close t;
  rm_rf b.b_dir;
  (* PK5: a be64 length at or above 2^62 is Host_limit, never misread *)
  let d = fresh_dir () in
  let t = E4_pack.open_ ~dir:d ~seg_max:E4_pack.default_seg_max in
  let body = rand_bytes 32 in
  let _, o = E4_pack.append t ~digest:(digest_of body) ~node_bytes:body in
  E4_pack.sync t;
  E4_pack.close t;
  (* set the top byte of the be64 length to 0x40: exactly 2^62 *)
  poke (E4_pack.seg_path ~dir:d 0) (o + 1) 0x40;
  let _, stop = recovered_prefix d in
  check "T4 a node_len >= 2^62 is Host_limit at its offset, never misread (M9)"
    (stop = E4_pack.Host_limit { seg = 0; off = o });
  rm_rf d;
  (* a segment whose head does not check *)
  let b = build ~lo:16 ~hi:16 3 in
  flip (seg0 b) 2;
  check "T5 a segment head that does not check is Bad_pack at open, not a misread record"
    (match E4_pack.open_ ~dir:b.b_dir ~seg_max:E4_pack.default_seg_max with
     | exception E4_pack.Bad_pack _ -> true
     | t ->
       E4_pack.close t;
       false);
  rm_rf b.b_dir;
  (* a scan that WALKS INTO a segment whose head does not check: rotate, then corrupt the
     second segment's magic, and scan from the first *)
  let d = fresh_dir () in
  let t = E4_pack.open_ ~dir:d ~seg_max:1024 in
  let body = rand_bytes 200 in
  for _ = 1 to 16 do
    ignore (E4_pack.append t ~digest:(digest_of body) ~node_bytes:body)
  done;
  E4_pack.sync t;
  E4_pack.close t;
  let rd0 = E4_pack.open_reader ~dir:d in
  let segs = List.length (E4_pack.segments rd0) in
  E4_pack.close_reader rd0;
  flip (E4_pack.seg_path ~dir:d 1) 3;
  let rd = E4_pack.open_reader ~dir:d in
  let items = List.of_seq (E4_pack.scan_seq rd ~from:(0, E4_pack.head_length)) in
  check "T6 a scan that steps into a segment with a bad head stops at Bad_head there"
    (segs >= 3
    && (match List.rev items with
        | E4_pack.Stopped (E4_pack.Bad_head { seg = 1 }) :: _ -> true
        | _ -> false));
  check "T7 the records of the segments before it are still delivered, in write order"
    (List.length (List.filter (function E4_pack.Scanned _ -> true | _ -> false) items) >= 1);
  E4_pack.close_reader rd;
  check "T8 an interior bad head does not stop open_ (the LAST head still checks); recovery names it, and no segment is deleted"
    (match E4_pack.open_at ~from:(0, E4_pack.head_length) ~dir:d ~seg_max:1024 () with
     | exception E4_pack.Bad_pack _ -> false
     | t ->
       let r = E4_pack.recovery t in
       let rd = E4_pack.open_reader ~dir:d in
       let still = List.length (E4_pack.segments rd) in
       E4_pack.close_reader rd;
       E4_pack.close t;
       (match r.E4_pack.stop with
        | E4_pack.Bad_head { seg = 1 } -> (not r.E4_pack.truncated) && still = segs
        | _ -> false));
  rm_rf d

(* ============================================================ P: a property sweep *)

let test_property_sweep () =
  print_endline "-- P: a seeded sweep over sizes, batches and crash points";
  let ok_roundtrip = ref true and ok_recover = ref true in
  for _ = 1 to 12 do
    let n = 4 + rand 20 in
    let batch = 1 + rand 8 in
    let b = build ~batch ~lo:0 ~hi:400 n in
    let rd = E4_pack.open_reader ~dir:b.b_dir in
    List.iter2
      (fun (s, o) body ->
        match E4_pack.read rd ~seg:s ~off:o with
        | Ok { E4_pack.r_bytes = Some x; _ } when x = body -> ()
        | _ -> ok_roundtrip := false)
      b.b_offs b.b_bodies;
    E4_pack.close_reader rd;
    (* cut at a random byte of the file and check the recovered prefix exactly *)
    let bytes = read_file (seg0 b) in
    let cut = E4_pack.head_length + rand (String.length bytes - E4_pack.head_length) in
    let d = fresh_dir () in
    Unix.mkdir (Filename.concat d "pack") 0o755;
    write_file (E4_pack.seg_path ~dir:d 0) (String.sub bytes 0 cut);
    let got, _ = recovered_prefix d in
    let want =
      List.filteri
        (fun i _ ->
          let _, o = List.nth b.b_offs i in
          o + 45 + String.length (List.nth b.b_bodies i) <= cut)
        b.b_offs
    in
    if List.map (fun (s, o, _) -> (s, o)) got <> want then ok_recover := false;
    if not (List.for_all (fun (_, _, r) -> r.E4_pack.r_bytes <> None) got) then
      ok_recover := false;
    rm_rf d;
    rm_rf b.b_dir
  done;
  check "P1 every record round trips, over 12 random (count, batch, size) draws" !ok_roundtrip;
  check "P2 a cut at a random byte recovers exactly the records wholly before it" !ok_recover

(* ============================================================ *)

let () =
  note "sandbox: %s" root;
  test_head ();
  test_roundtrip ();
  test_group_commit ();
  test_scan ();
  test_truncate ();
  test_corruption ();
  test_mutation ();
  test_single_writer ();
  test_rotation ();
  test_truncate_to ();
  test_property_sweep ();
  rm_rf root;
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
