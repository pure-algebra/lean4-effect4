(* test_wal.ml — lane P5's checks: the write-ahead log (2026-09-08).

   What it checks, and against what:
     W1..W6   the laws LG1-LG9 of ../e4_wal.mli: the round trip over three segments, replay
              from a position, the tape window, the opaque body (including the empty string,
              NUL bytes and today's five decision wire strings — ocaml/link/e4_bridge.ml:75-80),
              group commit and `durable_upto`, and the single-writer claim.
     X6*      the crash families of docs/research/2026-09-08-engine-a2-persistence.md §4.3 X6:
              a torn last row, a flipped row checksum, a missing middle segment, an unsealed
              tail that a reopen recovers, a segment head that fails its CRC, and a segment
              belonging to another job.
     REL      LAW LOG-REL (§1.4, law L-LOG-3): two jobs staged the same rows have the same
              indices, the same segment names and byte-identical rows on disk; the heads
              differ only in `job_lo`, which is the job directory's own identity.
     MUT      the mutation check: the file that replays clean must go red when one bit of one
              row's checksum field is flipped, and the verdict must name that exact index.

   Every file this test makes lives under one directory in the system temp directory and is
   removed at the end; nothing is written into the repository or the store default.

   Exit code 0 iff every check passed. *)

open Effect4_engine_cas

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* ---------------------------------------------------------------- scaffolding *)

let root =
  Filename.concat (Filename.get_temp_dir_name ())
    (Printf.sprintf "e4_wal_test_%d" (Unix.getpid ()))

let counter = ref 0

let fresh_store () =
  incr counter;
  Filename.concat root (Printf.sprintf "store%02d" !counter)

let job_of c = E4_addr.Addr.of_digest (String.make 32 c)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let write_file path s =
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) (fun () -> output_string oc s)

let rec rm_rf path =
  match Sys.is_directory path with
  | exception Sys_error _ -> ()
  | true ->
    Array.iter (fun e -> rm_rf (Filename.concat path e)) (Sys.readdir path);
    (try Unix.rmdir path with Unix.Unix_error _ -> ())
  | false -> ( try Sys.remove path with Sys_error _ -> ())

(* The test's OWN walk of the grammar of e4_wal.mli, so a row's byte offset is not taken
   from the module under test: (offset, length) of every framed row after the head. *)
let row_offsets bytes =
  let n = String.length bytes in
  let rec go pos acc =
    if pos + E4_wal.row_header_length > n then List.rev acc
    else
      match E4_crc.read_be32 bytes pos with
      | None -> List.rev acc
      | Some len ->
        if pos + E4_wal.row_header_length + len > n then List.rev acc
        else go (pos + E4_wal.row_header_length + len) ((pos, len) :: acc)
  in
  go E4_wal.head_length []

let flip_bit s i =
  let b = Bytes.of_string s in
  Bytes.set b i (Char.chr (Char.code (Bytes.get b i) lxor 0x01));
  Bytes.to_string b

let collect r ~from =
  let acc = ref [] in
  let stop = E4_wal.replay r ~from ~f:(fun i row -> acc := (i, row) :: !acc) in
  (List.rev !acc, stop)

let same_rows a b = List.length a = List.length b && List.for_all2 ( = ) a b

(* The row programme every job in this file stages: a mix of kinds and of bodies, including
   the empty one, NULs, and the decision alphabet the bridge writes today. *)
let decisions =
  [ "evaluate"; "flush"; "fire:0"; "evaluate:3"; "answer:2:7:41"; ""; "\000\000\000\001" ]

let programme n =
  List.init n (fun i ->
      if i mod 25 = 24 then E4_wal.Checkpoint_mark { position = i; addr = None }
      else if i mod 3 = 0 then
        E4_wal.Decision (List.nth decisions (i mod List.length decisions))
      else E4_wal.Event (Printf.sprintf "ev:%d:%s" i (String.make (i mod 97) 'e')))

(* Stage the programme with a commit every [every] rows — the group commit of LG3, and what
   makes rotation happen more than once for a small `seg_max`. *)
let stage_indexed w rows ~every =
  let out =
    List.mapi
      (fun i row ->
        let ix = E4_wal.append w row in
        if (i + 1) mod every = 0 then E4_wal.commit w;
        ix)
      rows
  in
  E4_wal.commit w;
  out

let stage_all w rows ~every = ignore (stage_indexed w rows ~every : int list)

(* ---------------------------------------------------------------- W1-W3: the round trip *)

let n_rows = 120
let rows = programme n_rows

let test_roundtrip () =
  print_endline "-- W1 the round trip over three segments";
  let dir = fresh_store () in
  let job = job_of '\001' in
  let w = E4_wal.open_ ~dir ~job ~seg_max:2048 in
  let indices = stage_indexed w rows ~every:8 in
  check "W1 stage hands out contiguous indices from 0"
    (indices = List.init n_rows (fun i -> i));
  check "W1 next_seq is one past the last" (E4_wal.next_seq w = n_rows);
  check "W1 last_index is the last" (E4_wal.last_index w = Some (n_rows - 1));
  check "W1 durable_upto is next_seq after a commit" (E4_wal.durable_upto w = n_rows);
  check "W1 nothing is staged after a commit" (E4_wal.staged_bytes w = 0);
  E4_wal.close w;
  let r = E4_wal.open_reader ~dir ~job in
  let segs = E4_wal.segments r in
  note "W1 %d rows in %d segments" n_rows (List.length segs);
  check "W1 the rows filled at least three segments" (List.length segs >= 3);
  check "W1 the segment names are the first indices, ascending"
    (List.for_all
       (fun (i, p) -> Filename.basename p = E4_wal.segment_name i)
       segs
    && segs = List.sort (fun (a, _) (b, _) -> compare (a : int) b) segs);
  let got, stop = collect r ~from:0 in
  check "W1 replay from 0 is Eof" (stop = E4_wal.Eof);
  check "W1 replay returns every row, in order, with its index"
    (same_rows got (List.mapi (fun i row -> (i, row)) rows));
  check "W1 no Seal is ever delivered"
    (List.for_all (fun (_, row) -> match row with E4_wal.Seal _ -> false | _ -> true) got);
  (* LG8: the body is opaque and exact, the empty string and NULs included *)
  let bodies = List.filter_map (fun (_, row) ->
      match row with E4_wal.Decision s -> Some s | _ -> None) got in
  check "W1 every decision body came back byte for byte"
    (bodies = List.filter_map (function E4_wal.Decision s -> Some s | _ -> None) rows);
  check "W1 the empty body round-tripped" (List.mem "" bodies);
  print_endline "-- W2 replay from a position, and the tape window";
  let ok_from = ref true in
  List.iter
    (fun k ->
      let got_k, stop_k = collect r ~from:k in
      if stop_k <> E4_wal.Eof then ok_from := false;
      let want = List.filteri (fun i _ -> i >= k) (List.mapi (fun i row -> (i, row)) rows) in
      if not (same_rows got_k want) then ok_from := false)
    [ 0; 1; 30; 59; 60; 100; n_rows - 1; n_rows ];
  check "W2 replay ~from:k is exactly the rows at k and above, for eight k" !ok_from;
  let want_tape =
    List.filteri (fun i _ -> i >= 10 && i < 70) rows
    |> List.filter_map (function E4_wal.Decision s -> Some s | _ -> None)
  in
  check "W3 tape is the decision bodies of the window, in order"
    (E4_wal.tape r ~from:10 ~upto:70 = want_tape);
  check "W3 an empty window is the empty tape" (E4_wal.tape r ~from:10 ~upto:10 = []);
  let verdict = ref E4_wal.Eof in
  let seq_rows = List.of_seq (E4_wal.replay_seq r ~from:0 ~verdict) in
  check "W4 replay_seq agrees with replay and sets the verdict"
    (same_rows seq_rows got && !verdict = E4_wal.Eof);
  E4_wal.close_reader r

(* ---------------------------------------------------------------- W5-W6 *)

let test_group_commit () =
  print_endline "-- W5 group commit: staged is not durable";
  let dir = fresh_store () in
  let job = job_of '\002' in
  let w = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
  ignore (E4_wal.append w (E4_wal.Decision "evaluate") : int);
  ignore (E4_wal.append w (E4_wal.Decision "flush") : int);
  check "W5 next_seq counts staged rows" (E4_wal.next_seq w = 2);
  check "W5 durable_upto does not" (E4_wal.durable_upto w = 0);
  check "W5 staged_bytes is positive" (E4_wal.staged_bytes w > 0);
  let r = E4_wal.open_reader ~dir ~job in
  let before, _ = collect r ~from:0 in
  check "W5 a reader sees no staged row" (before = []);
  E4_wal.sync w;
  let after, stop = collect r ~from:0 in
  check "W5 one commit makes both rows durable at once"
    (List.length after = 2 && stop = E4_wal.Eof && E4_wal.durable_upto w = 2);
  check "W5 staged_bytes is zero after the commit" (E4_wal.staged_bytes w = 0);
  print_endline "-- W6 the single-writer claim, and the refusals";
  let locked =
    match E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max with
    | exception E4_wal.Locked d -> d = E4_wal.dir_of w
    | w2 ->
      E4_wal.close w2;
      false
  in
  check "W6 a second writer on one job raises Locked" locked;
  let other_ok =
    match E4_wal.open_ ~dir ~job:(job_of '\003') ~seg_max:E4_wal.default_seg_max with
    | exception E4_wal.Locked _ -> false
    | w2 ->
      E4_wal.close w2;
      true
  in
  check "W6 another job in the same store is not blocked" other_ok;
  let big = String.make (E4_wal.row_max + 1) 'x' in
  let refused =
    match E4_wal.append w (E4_wal.Decision big) with
    | exception E4_wal.Row_too_large n -> n > E4_wal.row_max
    | _ -> false
  in
  check "W6 a body above row_max is refused at stage" refused;
  check "W6 the refused row advanced nothing" (E4_wal.next_seq w = 2);
  let sealed_refused =
    match E4_wal.append w (E4_wal.Seal { next_first_seq = 0 }) with
    | exception Invalid_argument _ -> true
    | _ -> false
  in
  check "W6 staging a Seal is refused: rotation owns it" sealed_refused;
  let exact = String.make (E4_wal.row_max - E4_wal.body_header_length) 'x' in
  ignore (E4_wal.append w (E4_wal.Decision exact) : int);
  E4_wal.commit w;
  let got, stop = collect r ~from:2 in
  check "W6 a body of exactly row_max - 9 is accepted and round-trips"
    (stop = E4_wal.Eof && got = [ (2, E4_wal.Decision exact) ]);
  E4_wal.close_reader r;
  print_endline "-- W7 rotate, checkpoint_mark, truncate_to, end_index";
  let before_segs = List.length (E4_wal.segments (E4_wal.open_reader ~dir ~job)) in
  E4_wal.rotate w;
  let after_segs = List.length (E4_wal.segments (E4_wal.open_reader ~dir ~job)) in
  check "W7 rotate adds one segment and consumes no index"
    (after_segs = before_segs + 1 && E4_wal.next_seq w = 3);
  E4_wal.checkpoint_mark w 3;
  let r2 = E4_wal.open_reader ~dir ~job in
  let got2, stop2 = collect r2 ~from:3 in
  check "W7 checkpoint_mark is a durable row covering the positions below it"
    (stop2 = E4_wal.Eof
    && got2 = [ (3, E4_wal.Checkpoint_mark { position = 3; addr = None }) ]);
  check "W7 the index chain crosses the rotation unbroken" (E4_wal.next_seq w = 4);
  ignore (E4_wal.append w (E4_wal.Decision "fire:1") : int);
  E4_wal.commit w;
  E4_wal.truncate_to w 4;
  check "W7 truncate_to lowers next_seq and durable_upto"
    (E4_wal.next_seq w = 4 && E4_wal.durable_upto w = 4);
  let got3, stop3 = collect r2 ~from:0 in
  check "W7 the truncated row is gone and replay is clean"
    (stop3 = E4_wal.Eof && List.length got3 = 4);
  let bad_truncate =
    match E4_wal.truncate_to w 99 with
    | exception Invalid_argument _ -> true
    | () -> false
  in
  check "W7 truncate_to above next_seq is refused" bad_truncate;
  E4_wal.close w;
  let e, v = E4_wal.end_index r2 in
  check "W7 end_index is one past the last good row" (e = 4 && v = E4_wal.Eof);
  E4_wal.close_reader r2

(* ---------------------------------------------------------------- the crash families *)

let test_crash_torn () =
  print_endline "-- X6(a) a torn last row";
  let dir = fresh_store () in
  let job = job_of '\009' in
  let w = E4_wal.open_ ~dir ~job ~seg_max:2048 in
  stage_all w rows ~every:16;
  let r = E4_wal.open_reader ~dir ~job in
  (* The last commit may have crossed the threshold and left a fresh, empty segment; the tear
     must land on a DATA row, so append until the tail holds one. *)
  let rec ensure k =
    let segs = E4_wal.segments r in
    let _, p = List.nth segs (List.length segs - 1) in
    if row_offsets (read_file p) = [] && k < 8 then begin
      ignore (E4_wal.append w (E4_wal.Decision "flush") : int);
      E4_wal.commit w;
      ensure (k + 1)
    end
  in
  ensure 0;
  let total = E4_wal.next_seq w in
  E4_wal.close w;
  let segs = E4_wal.segments r in
  let path = snd (List.nth segs (List.length segs - 1)) in
  let bytes = read_file path in
  let offs = row_offsets bytes in
  let last_off, last_len = List.nth offs (List.length offs - 1) in
  write_file path (String.sub bytes 0 (String.length bytes - 3));
  let got, stop = collect r ~from:0 in
  let torn_index = total - 1 in
  check "X6(a) replay stops Short at the torn row's index" (stop = E4_wal.Short torn_index);
  check "X6(a) every row before the tear was delivered, and none after"
    (List.length got = torn_index && List.for_all (fun (i, _) -> i < torn_index) got);
  note "X6(a) tore the last row (index %d) at offset %d, len %d, of %s" torn_index last_off
    last_len (Filename.basename path);
  print_endline "-- X6(d) reopening an unsealed, torn tail";
  let w2 = E4_wal.open_ ~dir ~job ~seg_max:2048 in
  check "X6(d) the writer recovered to the last good row"
    (E4_wal.next_seq w2 = torn_index && E4_wal.durable_upto w2 = torn_index);
  let i = E4_wal.append w2 (E4_wal.Decision "evaluate") in
  E4_wal.commit w2;
  E4_wal.close w2;
  let got2, stop2 = collect r ~from:0 in
  check "X6(d) the next row takes the recovered index and replay is clean again"
    (i = torn_index && stop2 = E4_wal.Eof && List.length got2 = total);
  E4_wal.close_reader r

let test_crash_crc () =
  print_endline "-- X6(b) a flipped row checksum (the mutation check)";
  let dir = fresh_store () in
  let job = job_of '\004' in
  let w = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
  stage_all w rows ~every:32;
  E4_wal.close w;
  let r = E4_wal.open_reader ~dir ~job in
  let path = snd (List.hd (E4_wal.segments r)) in
  let clean = read_file path in
  let got, stop = collect r ~from:0 in
  check "X6(b) the unflipped log replays clean"
    (stop = E4_wal.Eof && List.length got = n_rows);
  let offs = row_offsets clean in
  check "X6(b) the test's own walk of the grammar found every row"
    (List.length offs = n_rows);
  let target = 37 in
  let off, _ = List.nth offs target in
  (* the crc field is the second be32 of the row header *)
  write_file path (flip_bit clean (off + 4));
  let got_b, stop_b = collect r ~from:0 in
  check "X6(b) replay stops exactly at the flipped row and names it"
    (stop_b = E4_wal.Bad_crc target);
  check "X6(b) every row before it was delivered and none after"
    (List.length got_b = target && List.for_all (fun (i, _) -> i < target) got_b);
  note "X6(b) verdict: %s" (E4_wal.stop_to_string stop_b);
  (* every one-bit flip of the checksum field must be caught: the check can go red *)
  let all_red = ref true in
  for bit = 0 to 3 do
    let m = flip_bit clean (off + 4 + bit) in
    write_file path m;
    let _, s = collect r ~from:0 in
    if s <> E4_wal.Bad_crc target then all_red := false
  done;
  check "X6(b) a flip in any byte of that checksum is caught at the same index" !all_red;
  (* a flip in the BODY is caught too, at the same index *)
  let body_off, _ = List.nth offs target in
  write_file path (flip_bit clean (body_off + E4_wal.row_header_length + 1));
  let _, s_body = collect r ~from:0 in
  check "X6(b) a flip in the body is caught at the same index"
    (s_body = E4_wal.Bad_crc target);
  write_file path clean;
  let got_c, stop_c = collect r ~from:0 in
  check "X6(b) restoring the bytes restores the clean replay"
    (stop_c = E4_wal.Eof && List.length got_c = n_rows);
  E4_wal.close_reader r

let test_crash_gap () =
  print_endline "-- X6(c) a missing segment in the middle";
  let dir = fresh_store () in
  let job = job_of '\005' in
  let w = E4_wal.open_ ~dir ~job ~seg_max:2048 in
  stage_all w rows ~every:8;
  E4_wal.close w;
  let r = E4_wal.open_reader ~dir ~job in
  let segs = E4_wal.segments r in
  check "X6(c) there are at least three segments to lose the middle of"
    (List.length segs >= 3);
  let missing_first, missing_path = List.nth segs 1 in
  let next_first, _ = List.nth segs 2 in
  Sys.remove missing_path;
  let got, stop = collect r ~from:0 in
  check "X6(c) the refusal names the gap"
    (stop = E4_wal.Gap { expected = missing_first; found = next_first });
  check "X6(c) only the rows before the gap were delivered"
    (List.for_all (fun (i, _) -> i < missing_first) got
    && List.length got = missing_first);
  note "X6(c) verdict: %s" (E4_wal.stop_to_string stop);
  E4_wal.close_reader r

let test_crash_header () =
  print_endline "-- X6(e) a segment head that fails its CRC, and a segment of another job";
  let dir = fresh_store () in
  let job = job_of '\006' in
  let w = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
  ignore (E4_wal.append w (E4_wal.Decision "evaluate") : int);
  E4_wal.commit w;
  E4_wal.close w;
  let r = E4_wal.open_reader ~dir ~job in
  let path = snd (List.hd (E4_wal.segments r)) in
  let clean = read_file path in
  write_file path (flip_bit clean 20);
  let got, stop = collect r ~from:0 in
  check "X6(e) a head whose CRC fails is Bad_header, not a row verdict"
    (stop = E4_wal.Bad_header { path } && got = []);
  let raised =
    match E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max with
    | exception Failure _ -> true
    | w2 ->
      E4_wal.close w2;
      false
  in
  check "X6(e) a writer refuses to open over structural damage rather than truncate it"
    raised;
  write_file path clean;
  (* the same bytes under another job's directory *)
  let job_b = job_of '\007' in
  let w2 = E4_wal.open_ ~dir ~job:job_b ~seg_max:E4_wal.default_seg_max in
  E4_wal.close w2;
  let r_b = E4_wal.open_reader ~dir ~job:job_b in
  let path_b = snd (List.hd (E4_wal.segments r_b)) in
  write_file path_b clean;
  let _, stop_b = collect r_b ~from:0 in
  check "X6(e) a segment moved into another job's directory is Wrong_job"
    (stop_b = E4_wal.Wrong_job { path = path_b });
  note "X6(e) verdict: %s" (E4_wal.stop_to_string stop_b);
  (* a hand-built oversize length field, and an unknown row tag *)
  let dir2 = fresh_store () in
  let job_c = job_of '\008' in
  let w3 = E4_wal.open_ ~dir:dir2 ~job:job_c ~seg_max:E4_wal.default_seg_max in
  ignore (E4_wal.append w3 (E4_wal.Decision "evaluate") : int);
  E4_wal.commit w3;
  E4_wal.close w3;
  let r_c = E4_wal.open_reader ~dir:dir2 ~job:job_c in
  let path_c = snd (List.hd (E4_wal.segments r_c)) in
  let base = read_file path_c in
  write_file path_c
    (base ^ E4_crc.be32 (E4_wal.row_max + 1) ^ E4_crc.be32 0 ^ String.make 16 'x');
  let _, stop_c = collect r_c ~from:0 in
  check "X6(f) a length field above row_max is Oversize, never misread"
    (stop_c = E4_wal.Oversize { at = 1; len = E4_wal.row_max + 1 });
  let bad_body = "\009" ^ String.make 8 '\000' ^ "junk" in
  write_file path_c
    (base ^ E4_crc.be32 (String.length bad_body)
    ^ E4_crc.be32 (E4_crc.string bad_body)
    ^ bad_body);
  let _, stop_d = collect r_c ~from:0 in
  check "X6(f) a well-checksummed row with an unknown tag is Bad_row"
    (stop_d = E4_wal.Bad_row 1);
  note "X6(f) verdicts: %s | %s" (E4_wal.stop_to_string stop_c)
    (E4_wal.stop_to_string stop_d);
  E4_wal.close_reader r;
  E4_wal.close_reader r_b;
  E4_wal.close_reader r_c

(* ---------------------------------------------------------------- LAW LOG-REL *)

let test_log_rel () =
  print_endline "-- REL LAW LOG-REL: two jobs, one row programme";
  let dir = fresh_store () in
  let job_a = job_of '\020' and job_b = job_of '\021' in
  let run job =
    let w = E4_wal.open_ ~dir ~job ~seg_max:2048 in
    let idx = stage_indexed w rows ~every:8 in
    E4_wal.close w;
    let r = E4_wal.open_reader ~dir ~job in
    let segs = E4_wal.segments r in
    let got, stop = collect r ~from:0 in
    E4_wal.close_reader r;
    (idx, segs, got, stop)
  in
  let ia, sa, ga, va = run job_a in
  let ib, sb, gb, vb = run job_b in
  check "REL the two jobs handed out identical indices" (ia = ib);
  check "REL the two jobs replay identical rows in identical order"
    (same_rows ga gb && va = vb && va = E4_wal.Eof);
  check "REL the segment names and first indices are identical"
    (List.map fst sa = List.map fst sb
    && List.map (fun (_, p) -> Filename.basename p) sa
       = List.map (fun (_, p) -> Filename.basename p) sb);
  let rows_bytes p = let b = read_file p in
    String.sub b E4_wal.head_length (String.length b - E4_wal.head_length)
  in
  check "REL the row bytes on disk are identical, segment by segment"
    (List.for_all2 (fun (_, pa) (_, pb) -> rows_bytes pa = rows_bytes pb) sa sb);
  let head p = String.sub (read_file p) 0 E4_wal.head_length in
  let heads_agree_but_job =
    List.for_all2
      (fun (_, pa) (_, pb) ->
        let ha = head pa and hb = head pb in
        (* magic, version and first index agree; job_lo (14..21) and the crc over it differ *)
        String.sub ha 0 14 = String.sub hb 0 14
        && String.sub ha 22 8 = String.sub hb 22 8
        && String.sub ha 14 8 <> String.sub hb 14 8)
      sa sb
  in
  check "REL the heads differ only in job_lo — the job directory's own identity"
    heads_agree_but_job;
  note "REL %d rows, %d segments, identical positions in two jobs" (List.length ga)
    (List.length sa)

(* ---------------------------------------------------------------- *)

let () =
  rm_rf root;
  Fun.protect
    ~finally:(fun () -> rm_rf root)
    (fun () ->
      test_roundtrip ();
      test_group_commit ();
      test_crash_torn ();
      test_crash_crc ();
      test_crash_gap ();
      test_crash_header ();
      test_log_rel ());
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
