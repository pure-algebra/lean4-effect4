(* test_crash.ml — lane P4's crash families: what `open_writer` makes of a store a crash
   left behind (2026-09-08).

   The families are docs/research/2026-09-08-engine-a2-persistence.md §4.3, restricted to the
   ones that concern the store (X6 is the WAL, lane P5's file):

     X1  truncate the pack mid-node, at every interesting offset of every record: one byte
         into the header, mid-digest, mid-payload, one byte before the CRC, exactly at a
         record boundary, one byte past it.  Every record wholly before the cut is recovered,
         every recovered node re-verifies, the pack is truncated to the last good record, and
         a put of the lost node succeeds `Fresh`.
     X2  flip one byte in a record's CRC, in its recorded digest, and in its payload.  There
         are two cases and the difference is the design, not an accident:
           (a) IN THE TAIL, past the control file's `pack_end`: recovery stops AT that record,
               names it `Bad_crc` / `Bad_digest` at the exact offset, admits exactly the
               prefix, and the pack is truncated there.
           (b) BELOW the watermark: those records were admitted when they were written and
               the control commit is the proof, so the writer's open does not re-scan them
               (CS6).  The checked open (`E4_disk.open_`, e4_cas.mli CS7) is what finds the
               corruption — a refusal that names the record, never a silent wrong answer.
     X3  lose the index: delete `index/`, and drop the in-memory table.  Every answer is the
         same, on resident and on absent digests (L-IDX-0).
     X4  the control file: a stale `control.tmp`; a `pack_end` that names bytes that are not
         there; a flipped checksum; an ASCII version this binary does not know; a reserved
         status tag.  The last two are DIFFERENT verdicts because they are different operator
         actions.
     X5  two writers, and a reader's consistent prefix.
     X7  a torn tail whose records are individually valid: re-admitted in write order, and
         `Closed` preserved.  Plus the tail this store REFUSES (a record whose children are
         not there), plus the root race.

   Everything runs in a fresh directory under the system's temporary directory (TMPDIR; made by
   E4_check.temp_dir), removed at the end.  Exit code 0 iff every check passed. *)

open Effect4_engine_cas

let open_writer ~dir opts =
  match E4_cas.open_rw ~dir opts with
  | Ok writer -> writer
  | Error why -> failwith ("open writer: " ^ E4_cas.admission_word why)
;;

(* The store's verification (e4_cas.mli CS7): the checked image of a view. *)
let checked ro = Result.is_ok (E4_cas.checked_image ro)
let check = E4_check.check ~gap:Two
let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n%!")
let skip name why = Printf.printf "SKIP  %s (%s)\n%!" name why

(* ============================================================ the sandbox *)

(* The test's scratch root, a fresh directory under the system's temporary directory
   (E4_check.temp_dir); each store gets a fresh directory below it. *)
let root_dir = E4_check.temp_dir "e4crash-"
let fresh_dir () = E4_check.temp_dir ~under:root_dir "s"
let rm_rf = E4_check.remove_tree

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s
;;

(* Damage bypasses the store's permissions, as a disk fault or an operator would: a sealed
   file (0444; E4_pack PK9, E4_index IX9) is made writable for the write and sealed again
   after it, so the store meets the damage in the state it left the file. *)
let as_writable path f =
  let sealed =
    match Unix.stat path with
    | st when st.Unix.st_perm land 0o200 = 0 -> Some st.Unix.st_perm
    | _ -> None
    | exception Unix.Unix_error _ -> None
  in
  (match sealed with
   | Some p -> Unix.chmod path (p lor 0o200)
   | None -> ());
  Fun.protect
    ~finally:(fun () ->
      match sealed with
      | Some p -> Unix.chmod path p
      | None -> ())
    f
;;

let write_file path s =
  as_writable path (fun () ->
    let oc = open_out_bin path in
    output_string oc s;
    close_out oc)
;;

let file_size path = (Unix.stat path).Unix.st_size

(* ============================================================ nodes and stores *)

let v_nat n = Eff_frame.framed Eff_frame.tag_nat (Eff_frame.nat_digits (Z.of_int n))
let v_str s = Eff_frame.framed Eff_frame.tag_string s
let v_list xs = Eff_frame.framed Eff_frame.tag_list (String.concat "" xs)

let v_ctor i args =
  Eff_frame.framed Eff_frame.tag_ctor (String.concat "" (v_nat i :: args))
;;

let v_ref k d = Eff_frame.framed Eff_frame.tag_ref (String.make 1 (Char.chr k) ^ d)
let zero = E4_node.zero_digest
let node kind spec payload = { E4_node.version = 0; kind; spec; payload }
let genesis = node E4_kind.Schema zero (v_str "schema")
let genesis_addr = E4_node.address genesis
let spec = E4_addr.Addr.bytes genesis_addr

(* A chain: node i names node i-1, so a word is admissible only children-first and a store
   that loses a suffix stays `Closed`. *)
let chain n =
  let acc = ref [ genesis ]
  and prev = ref genesis_addr in
  for i = 1 to n do
    let payload =
      v_ctor
        0
        [ v_nat i
        ; v_list [ v_ref (E4_kind.byte E4_kind.Export) (E4_addr.Addr.bytes !prev) ]
        ]
    in
    let nd = node E4_kind.Export spec payload in
    (* the ref must resolve at kind export; node 1 points at the genesis, which is a schema,
       so node 1 refers to nothing and the chain starts at node 2 *)
    let nd = if i = 1 then node E4_kind.Export spec (v_ctor 0 [ v_nat i ]) else nd in
    acc := nd :: !acc;
    prev := E4_node.address nd
  done;
  List.rev !acc
;;

let opts = { E4_cas.default_opts with seg_max = 1 lsl 20 }

let build dir nodes =
  let s = open_writer ~dir opts in
  List.iter (fun n -> ignore (E4_cas.put s n)) nodes;
  E4_cas.commit s;
  E4_cas.close s
;;

let seg0 dir = E4_pack.seg_path ~dir 0

(* Every record's (offset, node_len), in write order. *)
let records dir =
  let rd = E4_pack.open_reader ~dir in
  let acc = ref [] in
  ignore
    (E4_pack.scan rd ~from:(0, E4_pack.head_length) ~f:(fun _ _ off len ->
       acc := (off, len) :: !acc));
  E4_pack.close_reader rd;
  List.rev !acc
;;

(* Put the control file's watermark back to [pos]: the crash in which the pack was fsynced and
   the control file was not. *)
let set_watermark dir pos =
  match E4_control.read ~path:(E4_control.control_path ~dir) with
  | Ok p ->
    E4_control.commit ~path:(E4_control.control_path ~dir) (E4_control.set_pack_end p pos)
  | Error _ -> failwith "no control file"
;;

let flip_byte path i =
  let s = read_file path in
  let b = Bytes.of_string s in
  Bytes.set b i (Char.chr (Char.code (Bytes.get b i) lxor 1));
  write_file path (Bytes.to_string b)
;;

(* ============================================================ X1: truncate mid-node *)

let test_x1 () =
  print_endline "-- X1: the pack truncated mid-node, at every interesting offset";
  let nodes = chain 6 in
  let d0 = fresh_dir () in
  build d0 nodes;
  let recs = records d0 in
  let full = read_file (seg0 d0) in
  let cuts =
    List.concat
      (List.map
         (fun (off, len) ->
            [ off + 1, "one byte into the header"
            ; off + 20, "mid-digest"
            ; off + E4_pack.record_header_length + max 1 (len / 2), "mid-payload"
            ; ( off + E4_pack.record_header_length + len + 3
              , "one byte before the end of the CRC" )
            ; off, "exactly at a record boundary"
            ; off + 1, "one byte past a record boundary"
            ])
         recs)
  in
  let ok_prefix = ref true
  and ok_verify = ref true
  and ok_trunc = ref true
  and ok_regrow = ref true in
  List.iter
    (fun (cut, _why) ->
       let d = fresh_dir () in
       Unix.mkdir (Filename.concat d "pack") 0o755;
       write_file (seg0 d) (String.sub full 0 (min cut (String.length full)));
       (* A writable uncommitted tail starts after the published empty boundary.
         Published bytes lost are damage, covered by test_disk_damage. *)
       E4_control.commit
         ~path:(E4_control.control_path ~dir:d)
         { E4_control.initial with pack_end = 0, E4_pack.head_length; generation = 1 };
       let s = open_writer ~dir:d opts in
       let ro = E4_cas.read_only s in
       let want =
         List.filter (fun (off, len) -> off + E4_pack.record_overhead + len <= cut) recs
       in
       let got = E4_cas.nodes ro in
       if List.length got <> List.length want then ok_prefix := false;
       if not (checked ro) then ok_verify := false;
       if not (E4_cas.closed ro) then ok_verify := false;
       let ends_at =
         match List.rev want with
         | [] -> E4_pack.head_length
         | (off, len) :: _ -> off + E4_pack.record_overhead + len
       in
       if file_size (seg0 d) <> ends_at then ok_trunc := false;
       (* the lost records go back in, fresh *)
       let lost = List.filteri (fun i _ -> i >= List.length want) nodes in
       List.iter
         (fun n ->
            match E4_cas.put s n with
            | Ok (E4_cas.Fresh, _) -> ()
            | Ok (E4_cas.Duplicate, _) -> ()
            | _ -> ok_regrow := false)
         lost;
       E4_cas.commit s;
       if List.length (E4_cas.nodes ro) <> List.length nodes then ok_regrow := false;
       if not (checked ro) then ok_regrow := false;
       E4_cas.close s;
       rm_rf d)
    cuts;
  check
    (Printf.sprintf
       "X1 over %d cuts: exactly the records wholly before the cut are recovered"
       (List.length cuts))
    !ok_prefix;
  check "X1 every recovered store passes the checked image and is Closed" !ok_verify;
  check "X1 the pack is truncated to the end of the last good record" !ok_trunc;
  check "X1 a put of the lost nodes succeeds and the store verifies again" !ok_regrow;
  rm_rf d0
;;

(* ============================================================ X2: a flipped byte *)

let corrupt_tail_case name field =
  (* Build a chain, then move the watermark back to before the last record and corrupt that
     record: the crash in which the pack was written and the control file was not. *)
  let nodes = chain 4 in
  let d = fresh_dir () in
  build d nodes;
  let recs = records d in
  let off, len = List.nth recs (List.length recs - 1) in
  set_watermark d (0, off);
  let pos =
    match field with
    | `Crc -> off + E4_pack.record_header_length + len (* the first CRC byte *)
    | `Digest -> off + 9 (* the first digest byte *)
    | `Payload -> off + E4_pack.record_header_length (* the first node byte *)
  in
  flip_byte (seg0 d) pos;
  let s = open_writer ~dir:d opts in
  let ro = E4_cas.read_only s in
  let r = E4_cas.recovery s in
  let stop_ok =
    match r.E4_cas.stop with
    | E4_cas.Torn (E4_pack.Bad_crc { off = o; _ }) -> o = off
    | E4_cas.Torn (E4_pack.Bad_digest { off = o; _ }) -> o = off
    | _ ->
      (* the pack's own verifying scan may have refused it first and truncated *)
      (match r.E4_cas.pack.E4_pack.stop with
       | E4_pack.Bad_crc { off = o; _ } | E4_pack.Bad_digest { off = o; _ } -> o = off
       | _ -> false)
  in
  check
    (Printf.sprintf "X2(a) %s: recovery names the failure at the exact offset" name)
    stop_ok;
  check
    (Printf.sprintf "X2(a) %s: exactly the prefix is admitted" name)
    (List.length (E4_cas.nodes ro) = List.length nodes - 1);
  check (Printf.sprintf "X2(a) %s: the prefix passes the checked image" name) (checked ro);
  check
    (Printf.sprintf "X2(a) %s: the pack is truncated at the failure" name)
    (file_size (seg0 d) = off);
  check
    (Printf.sprintf "X2(a) %s: the lost node goes back in fresh" name)
    (match E4_cas.put s (List.nth nodes (List.length nodes - 1)) with
     | Ok (E4_cas.Fresh, _) -> true
     | _ -> false);
  E4_cas.close s;
  rm_rf d
;;

let test_x2 () =
  print_endline "-- X2: one flipped byte, in the tail and below the watermark";
  corrupt_tail_case "a flipped CRC byte" `Crc;
  corrupt_tail_case "a flipped digest byte" `Digest;
  corrupt_tail_case "a flipped payload byte" `Payload;
  (* (b) below the watermark: the record was admitted when it was written and the control
     commit is the proof, so the writer's open does not re-scan it (CS6).  The checked open is
     what finds it.  Two shapes, and they answer differently on purpose:
       b1  the CRC is CONSISTENT with the corrupted bytes — the mutation L-CAS-6 exists for.
           `read_at`, which trusts the recorded digest, hands the bytes back; the checked
           open re-hashes and refuses the address as corrupt.
       b2  a raw flipped byte, so the CRC no longer holds.  The record does not read at all,
           and the checked open refuses it as a record fault at its own offset.  Never a
           silent wrong answer. *)
  let nodes = chain 4 in
  let d0 = fresh_dir () in
  build d0 nodes;
  let originals =
    let rd = E4_pack.open_reader ~dir:d0 in
    let acc = ref [] in
    List.iter
      (fun (off, _) ->
         match E4_pack.read_at rd ~seg:0 ~off with
         | Some (a, b) -> acc := (E4_addr.Addr.bytes a, b) :: !acc
         | None -> ())
      (records d0);
    E4_pack.close_reader rd;
    List.rev !acc
  in
  let flip s i =
    let b = Bytes.of_string s in
    Bytes.set b i (Char.chr (Char.code (Bytes.get b i) lxor 1));
    Bytes.to_string b
  in
  let forge_with records =
    let d = fresh_dir () in
    let p = E4_pack.open_ ~dir:d ~seg_max:(1 lsl 20) in
    List.iter (fun (k, b) -> ignore (E4_pack.append p ~digest:k ~node_bytes:b)) records;
    E4_pack.commit p;
    let pe = E4_pack.pack_end p in
    E4_pack.close p;
    E4_control.commit
      ~path:(E4_control.control_path ~dir:d)
      { E4_control.initial with pack_end = pe; generation = 1 };
    d
  in
  let corrupted =
    List.mapi
      (fun i (k, b) -> if i = 1 then k, flip b (String.length b - 1) else k, b)
      originals
  in
  let d1 = forge_with corrupted in
  let s = open_writer ~dir:d1 opts in
  let ro = E4_cas.read_only s in
  check
    "X2(b1) a record corrupted BELOW the watermark does not stop the open"
    ((E4_cas.recovery s).E4_cas.stop = E4_cas.Clean);
  check
    "X2(b1) the read that trusts the recorded digest hands the bytes back"
    (E4_cas.get_bytes ro (E4_addr.Addr.of_digest (fst (List.nth originals 1)))
     = Some (snd (List.nth corrupted 1)));
  E4_cas.close s;
  let corrupted_addr = E4_addr.Addr.of_digest (fst (List.nth originals 1)) in
  check
    "X2(b1) the checked open re-hashes and refuses the address as corrupt"
    (match E4_disk.open_ ~dir:d1 opts with
     | Error (E4_cas.Fault (E4_fault.Corrupt at)) -> E4_addr.Addr.equal at corrupted_addr
     | Error _ -> false
     | Ok disk ->
       E4_disk.close disk;
       false);
  rm_rf d1;
  let d2 = fresh_dir () in
  build d2 nodes;
  let off, _ = List.nth (records d2) 1 in
  flip_byte (seg0 d2) (off + E4_pack.record_header_length);
  let s = open_writer ~dir:d2 opts in
  let ro = E4_cas.read_only s in
  check
    "X2(b2) a raw flipped byte below the watermark does not stop the open"
    ((E4_cas.recovery s).E4_cas.stop = E4_cas.Clean);
  check
    "X2(b2) the record does not read at all, and the checked image refuses it there"
    (match E4_cas.checked_image ro with
     | Error (E4_cas.Fault (E4_fault.Record { seg = 0; off = at; _ })) -> at = off
     | Ok _ | Error _ -> false);
  E4_cas.close s;
  check
    "X2(b2) the checked open refuses it at the record's own offset"
    (match E4_disk.open_ ~dir:d2 opts with
     | Error (E4_cas.Fault (E4_fault.Record { seg = 0; off = at; _ })) -> at = off
     | Error _ -> false
     | Ok disk ->
       E4_disk.close disk;
       false);
  rm_rf d2;
  rm_rf d0
;;

(* ============================================================ X3: lose the index *)

let test_x3 () =
  print_endline "-- X3: lose the index";
  let nodes = chain 8 in
  let d = fresh_dir () in
  build d nodes;
  let ro0 = E4_cas.open_ro ~dir:d in
  let resident = List.map fst (E4_cas.nodes ro0) in
  let absent =
    List.init 64 (fun i -> E4_addr.Addr.of_digest (E4_sha256.digest (string_of_int i)))
  in
  let answers r =
    ( List.map (fun a -> E4_cas.get_bytes r a) resident
    , List.map (fun a -> E4_cas.mem r a) absent
    , List.map (fun a -> E4_cas.get_kind r a) resident )
  in
  let before = answers ro0 in
  E4_cas.close_ro ro0;
  let idx_dir = Filename.concat d "index" in
  let had_file =
    Sys.file_exists idx_dir
    && Array.exists (fun f -> Filename.check_suffix f ".idx") (Sys.readdir idx_dir)
  in
  check "X3 the writer left an index snapshot behind" had_file;
  if Sys.file_exists idx_dir
  then
    Array.iter
      (fun f ->
         try Sys.remove (Filename.concat idx_dir f) with
         | Sys_error _ -> ())
      (Sys.readdir idx_dir);
  let ro1 = E4_cas.open_ro ~dir:d in
  check "X3 with index/ deleted, every answer is the same" (answers ro1 = before);
  check
    "X3 the rebuilt index holds every record"
    (E4_cas.index_count ro1 = List.length resident);
  E4_cas.drop_index ro1;
  check
    "X3 with the in-memory table dropped, every answer is the same"
    (answers ro1 = before);
  check "X3 the checked image is unchanged by either" (checked ro1);
  E4_cas.close_ro ro1;
  (* an index file whose coverage is past the pack's end is discarded, not believed *)
  let s = open_writer ~dir:d opts in
  E4_cas.close s;
  let idx_file = Filename.concat idx_dir "000000.idx" in
  if Sys.file_exists idx_file
  then (
    flip_byte idx_file (E4_pack.head_length + 3);
    let ro2 = E4_cas.open_ro ~dir:d in
    check "X3 a corrupt index file is discarded and rebuilt" (answers ro2 = before);
    E4_cas.close_ro ro2)
  else skip "X3 a corrupt index file is discarded" "no index snapshot was written";
  rm_rf d
;;

(* ============================================================ X4: the control file *)

let test_x4 () =
  print_endline "-- X4: the control file";
  let nodes = chain 4 in
  (* (a) a stale control.tmp *)
  let d = fresh_dir () in
  build d nodes;
  let tmp = E4_control.tmp_path ~path:(E4_control.control_path ~dir:d) in
  write_file tmp "torn nonsense that never got renamed";
  let s = open_writer ~dir:d opts in
  check
    "X4(a) a stale control.tmp is removed and `control` is used"
    ((not (Sys.file_exists tmp))
     && List.length (E4_cas.nodes (E4_cas.read_only s)) = List.length nodes);
  E4_cas.close s;
  rm_rf d;
  (* (b) the watermark names bytes that are not there *)
  let d = fresh_dir () in
  build d nodes;
  let size = file_size (seg0 d) in
  set_watermark d (0, size + 4096);
  let original_control = read_file (E4_control.control_path ~dir:d) in
  check
    "X4(b) a published boundary past the bytes is a fault value"
    (match E4_cas.open_rw ~dir:d opts with
     | Error (E4_cas.Fault _) -> true
     | Error _ -> false
     | Ok writer ->
       E4_cas.close writer;
       false);
  check
    "X4(b) the published boundary is not silently rewritten"
    (String.equal original_control (read_file (E4_control.control_path ~dir:d)));
  rm_rf d;
  (* (c) a corrupt checksum, and (d) an unknown ASCII version — DIFFERENT verdicts *)
  let d = fresh_dir () in
  build d nodes;
  let path = E4_control.control_path ~dir:d in
  let good = read_file path in
  flip_byte path (String.length good - 1);
  check
    "X4(c) a corrupt control file is `corrupt`, and the store refuses to open"
    (match E4_cas.open_rw ~dir:d opts with
     | Error (E4_cas.Fault (E4_fault.Store m)) ->
       let want = "control: corrupt" in
       String.length m >= String.length want && String.sub m 0 (String.length want) = want
     | Error _ -> false
     | Ok t ->
       E4_cas.close t;
       false);
  write_file
    path
    (String.sub good 0 6 ^ "00000009" ^ String.sub good 14 (String.length good - 14));
  check
    "X4(d) an unknown ASCII version is `staleBinary` — a DIFFERENT verdict, and a \
     different operator action"
    (match E4_cas.open_rw ~dir:d opts with
     | Error (E4_cas.Fault (E4_fault.Store m)) ->
       let want = "control: staleBinary" in
       String.length m >= String.length want && String.sub m 0 (String.length want) = want
     | Error _ -> false
     | Ok t ->
       E4_cas.close t;
       false);
  write_file path good;
  check
    "X4(c/d) the store opens again once the control file is restored"
    (let s = open_writer ~dir:d opts in
     let ok = List.length (E4_cas.nodes (E4_cas.read_only s)) = List.length nodes in
     E4_cas.close s;
     ok);
  rm_rf d;
  (* (e) a reserved status tag round-trips through a commit *)
  let d = fresh_dir () in
  build d nodes;
  let path = E4_control.control_path ~dir:d in
  (match E4_control.read ~path with
   | Error _ -> check "X4(e) the control file reads back" false
   | Ok p ->
     E4_control.commit
       ~path
       (E4_control.set_status p (E4_control.Reserved (7, "a future writer's body")));
     let s = open_writer ~dir:d opts in
     ignore (E4_cas.put s (node E4_kind.Schema zero (v_str "another")));
     E4_cas.commit s;
     E4_cas.close s;
     check
       "X4(e) a reserved status tag survives a commit by a reader that does not know it"
       (match E4_control.read ~path with
        | Ok q -> E4_control.status q = E4_control.Reserved (7, "a future writer's body")
        | Error _ -> false));
  rm_rf d
;;

(* ============================================================ X5: two writers *)

let test_x5 () =
  print_endline "-- X5: two writers, and a reader's consistent prefix";
  let nodes = chain 4 in
  let d = fresh_dir () in
  let s = open_writer ~dir:d opts in
  List.iter (fun n -> ignore (E4_cas.put s n)) nodes;
  E4_cas.commit s;
  check
    "X5 a second open_rw is refused with Locked"
    (match E4_cas.open_rw ~dir:d opts with
     | Error (E4_cas.Fault (E4_fault.Locked _)) -> true
     | Error _ -> false
     | Ok writer ->
       E4_cas.close writer;
       false);
  let ro = E4_cas.open_ro ~dir:d in
  check
    "X5 a reader takes no lock and sees the committed prefix"
    (List.length (E4_cas.nodes ro) = List.length nodes);
  let g0 = E4_cas.generation ro in
  let extra = node E4_kind.Schema zero (v_str "later") in
  ignore (E4_cas.put s extra);
  check
    "X5 the reader does not see a staged record"
    (not (E4_cas.mem ro (E4_node.address extra)));
  E4_cas.commit s;
  check
    "X5 and still does not until it re-reads"
    (not (E4_cas.mem ro (E4_node.address extra)));
  let ro = E4_cas.reopen_ro ro in
  check "X5 after reopen_ro it does" (E4_cas.mem ro (E4_node.address extra));
  check
    "X5 the generation is strictly increasing across the reader's re-reads"
    (E4_cas.generation ro > g0);
  check
    "X5 the reader's store passes the checked image at every prefix it saw"
    (checked ro);
  E4_cas.close_ro ro;
  E4_cas.close s;
  rm_rf d
;;

(* ============================================================ X6: the log *)

let test_x6 () =
  print_endline "-- X6: the log";
  skip "X6 the WAL crash family" "e4_wal.{ml,mli} and test_wal.ml are lane P5's files"
;;

(* ============================================================ X7: the tail, and root races *)

let test_x7 () =
  print_endline "-- X7: a torn tail of valid records, and the root race";
  (* (a) the pack was fsynced, the control file was not: the tail is a children-first word and
     is re-admitted in write order, and `Closed` is preserved at every prefix. *)
  let nodes = chain 10 in
  let d = fresh_dir () in
  build d nodes;
  let recs = records d in
  let ok = ref true
  and ok_closed = ref true
  and ok_order = ref true in
  List.iteri
    (fun i (off, _) ->
       let d2 = fresh_dir () in
       Unix.mkdir (Filename.concat d2 "pack") 0o755;
       write_file (seg0 d2) (read_file (seg0 d));
       E4_control.commit
         ~path:(E4_control.control_path ~dir:d2)
         { E4_control.initial with pack_end = 0, off; generation = 1 };
       let s = open_writer ~dir:d2 opts in
       let ro = E4_cas.read_only s in
       let r = E4_cas.recovery s in
       if r.E4_cas.admitted <> List.length recs - i then ok := false;
       if r.E4_cas.stop <> E4_cas.Clean then ok := false;
       if List.length (E4_cas.nodes ro) <> List.length nodes then ok := false;
       if not (E4_cas.closed ro) then ok_closed := false;
       if not (checked ro) then ok_closed := false;
       (* re-admission is in WRITE order: the addresses come back in the order the pack holds *)
       if List.map fst (E4_cas.nodes ro) <> List.map E4_node.address nodes
       then ok_order := false;
       E4_cas.close s;
       rm_rf d2)
    recs;
  check
    (Printf.sprintf
       "X7(a) over %d watermarks: the whole tail is re-admitted"
       (List.length recs))
    !ok;
  check "X7(a) the recovered store is Closed and verifies" !ok_closed;
  check "X7(a) re-admission is in write order" !ok_order;
  (* the tail this store REFUSES: a record whose children are not there (e4_cas.mli D6) *)
  let d3 = fresh_dir () in
  let orphan = node E4_kind.Export (String.make 32 '\007') (v_str "no schema of mine") in
  let p = E4_pack.open_ ~dir:d3 ~seg_max:(1 lsl 20) in
  List.iter
    (fun n ->
       ignore (E4_pack.stage p ~addr:(E4_node.address n) ~node_bytes:(E4_node.encode n)))
    [ genesis; List.nth nodes 1; orphan ];
  E4_pack.commit p;
  E4_pack.close p;
  E4_control.commit
    ~path:(E4_control.control_path ~dir:d3)
    { E4_control.initial with pack_end = 0, E4_pack.head_length; generation = 1 };
  let s = open_writer ~dir:d3 opts in
  let ro = E4_cas.read_only s in
  let r = E4_cas.recovery s in
  check
    "X7(b) recovery stops at the first record it cannot admit"
    (r.E4_cas.admitted = 2
     &&
     match r.E4_cas.stop with
     | E4_cas.Refused { why = E4_cas.Model (E4_admission.Dangling _); _ } -> true
     | _ -> false);
  check
    "X7(b) the prefix is readable and Closed"
    (List.length (E4_cas.nodes ro) = 2 && E4_cas.closed ro && checked ro);
  check
    "X7(b) the store refuses to GROW until an operator acts (e4_cas.mli D6)"
    (match E4_cas.put s genesis with
     | exception E4_cas.Store_error _ -> true
     | _ -> false);
  note "the refusal reads: %s" (E4_cas.recovery_stop_word r.E4_cas.stop);
  E4_cas.close s;
  rm_rf d3;
  (* (c) the root race: a stale read loses, re-reads, and wins *)
  let d4 = fresh_dir () in
  build d4 nodes;
  let s = open_writer ~dir:d4 opts in
  let ro = E4_cas.read_only s in
  let target = E4_node.address genesis in
  let create =
    E4_control.Create
      ("runs/head", E4_control.Swap, { kind = E4_kind.Schema; digest = target })
  in
  check "X7(c) the first move wins" (E4_cas.advance_root s create = Ok ());
  check
    "X7(c) stale absence refuses"
    (match E4_cas.advance_root s create with
     | Error (E4_control.Stale_root _) -> true
     | _ -> false);
  check
    "X7(c) full-head duplicate retains generation"
    (match E4_cas.root ro "runs/head" with
     | Some root ->
       E4_cas.advance_root
         s
         (E4_control.Advance
            ("runs/head", root.head, { kind = E4_kind.Schema; digest = target }))
       = Ok ()
     | None -> false);
  check
    "X7(c) the plane holds one root of that name, and no node was overwritten"
    (List.length
       (List.filter
          (fun (r : E4_control.root) -> r.E4_control.name = "runs/head")
          (E4_cas.roots ro))
     = 1
     && List.length (E4_cas.nodes ro) = List.length nodes
     && checked ro);
  E4_cas.close s;
  rm_rf d4;
  rm_rf d
;;

(* ============================================================ *)

let () =
  note "sandbox: %s" root_dir;
  test_x1 ();
  test_x2 ();
  test_x3 ();
  test_x4 ();
  test_x5 ();
  test_x6 ();
  test_x7 ();
  rm_rf root_dir;
  E4_check.finish ()
;;
