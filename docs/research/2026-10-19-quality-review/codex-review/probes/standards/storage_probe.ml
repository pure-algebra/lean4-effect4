(* Host-only corruption and torn-write probes against pinned production libraries.
   Run: python3 ../run_ml.py storage_probe.ml <scratch directory inside this folder> *)
open Effect4_engine_cas
let root = Sys.argv.(1)
let write path bytes = Out_channel.with_open_bin path (fun ch -> output_string ch bytes)
let read path = In_channel.with_open_bin path In_channel.input_all
let mkdir path = Unix.mkdir path 0o700
let () =
  mkdir root;
  let job = E4_addr.Addr.of_digest (String.make 32 'q') in
  let dir = Filename.concat root "wal" in
  let w = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
  ignore (E4_wal.stage w (E4_wal.Decision "one"));
  ignore (E4_wal.stage w (E4_wal.Decision "two"));
  E4_wal.commit w;
  E4_wal.close w;
  let rd = E4_wal.open_reader ~dir ~job in
  let path = snd (List.hd (E4_wal.segments rd)) in
  let pristine = read path in
  (* A finite crash image: one complete frame and three bytes of frame two.
     This is a possible prefix of the single buffered write before fsync. *)
  let first_end = E4_wal.head_length + 8 + 9 + 3 in
  write path (String.sub pristine 0 (first_end + 3));
  let reopened = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
  let rows = ref [] in
  let stop = E4_wal.replay rd ~from:0 ~f:(fun i _ -> rows := i :: !rows) in
  Printf.printf "WAL torn batch: recovered=%d next=%d durable=%d stop=%s\n%!"
    (List.length !rows) (E4_wal.next_seq reopened) (E4_wal.durable_upto reopened)
    (E4_wal.stop_to_string stop);
  E4_wal.close reopened;
  write path "bad stored header";
  (try let x = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
       E4_wal.close x; print_endline "WAL bad header: unexpected success"
   with exn -> Printf.printf "WAL bad header: %s\n%!" (Printexc.to_string exn));
  write path pristine;
  let bak = path ^ ".saved" in
  Unix.rename path bak; mkdir path;
  (try let x = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
       E4_wal.close x; print_endline "WAL failed open: unexpected success"
   with exn -> Printf.printf "WAL failed open: %s\n%!" (Printexc.to_string exn));
  Unix.rmdir path; Unix.rename bak path;
  (try let x = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
       E4_wal.close x; print_endline "WAL repaired retry: success"
   with exn -> Printf.printf "WAL repaired retry: %s\n%!" (Printexc.to_string exn));
  let cd = Filename.concat root "cas" in
  let opts = {E4_cas.default_opts with verify_on_open=false} in
  let w = match E4_cas.open_rw ~dir:cd opts with Ok w -> w | Error e -> failwith (E4_cas.admission_word e) in
  let n = E4_node.make ~version:0 ~kind:E4_kind.Schema ~spec:E4_node.zero_digest
    ~payload:(E4_be.framed Eff_frame.tag_string "schema") in
  (match E4_cas.put w n with Ok _ -> () | Error e -> failwith (E4_cas.admission_word e));
  E4_cas.commit w; E4_cas.close w;
  let good = E4_cas.open_ro ~dir:cd in
  Printf.printf "CAS positive: verify=%s count=%d\n%!"
    (match E4_cas.verify good with Ok () -> "Ok" | Error e -> E4_cas.verify_error_word e)
    (E4_cas.count good);
  E4_cas.close_ro good;
  (match E4_control.read ~path:(E4_control.control_path ~dir:cd) with
   | Ok p -> Printf.printf "CAS unchanged published boundary: %d,%d\n%!" (fst p.pack_end) (snd p.pack_end)
   | Error _ -> failwith "control");
  let cp = E4_pack.seg_path ~dir:cd 0 in
  let bytes = read cp in
  let bad = Bytes.of_string bytes in
  Bytes.set bad E4_pack.head_length 'X';
  write cp (Bytes.to_string bad);
  let ro = E4_cas.open_ro ~dir:cd in
  Printf.printf "CAS corrupt record tag: verify=%s count=%d\n%!"
    (match E4_cas.verify ro with Ok () -> "Ok" | Error e -> E4_cas.verify_error_word e)
    (E4_cas.count ro);
  E4_cas.close_ro ro;
  (match E4_cas.open_rw ~dir:cd {opts with verify_on_open=true} with
   | Ok w -> Printf.printf "CAS verify_on_open=true: Ok\n%!"; E4_cas.close w
   | Error e -> Printf.printf "CAS verify_on_open=true: %s\n%!" (E4_cas.admission_word e));
  (match E4_disk.open_ ~dir:cd opts with
   | Ok _ -> print_endline "Disk checked image: Ok"
   | Error _ -> print_endline "Disk checked image: refused (control)")
