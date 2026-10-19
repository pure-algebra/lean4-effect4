(* Properties: published and sealed damage, and a pack directory that cannot be listed, return a
   fault and retain the evidence. These controls distinguish damage from writable
   uncommitted-tail recovery. *)
open Effect4_engine_cas
open Disk_test_support

let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))
;;

let pack_evidence directory =
  let path = Filename.concat directory "pack" in
  Array.to_list (Sys.readdir path)
  |> List.sort String.compare
  |> List.map (fun name ->
    let file = Filename.concat path name in
    name, read_file file, (Unix.stat file).Unix.st_perm)
;;

let report name directory accept =
  let before = pack_evidence directory in
  let control = E4_control.control_path ~dir:directory in
  let before_control =
    if Sys.file_exists control then Some (read_file control) else None
  in
  let result = E4_disk.open_ ~dir:directory opts in
  let fault =
    match result with
    | Error (E4_admission.Fault why) ->
      Printf.printf "%s: Fault %s\n%!" name (E4_fault.word why);
      accept why
    | Error why ->
      Printf.printf "%s: non-fault %s\n%!" name (E4_cas.admission_word why);
      false
    | Ok disk ->
      Printf.printf
        "%s: accepted %d nodes\n%!"
        name
        (List.length (E4_disk.nodes (snapshot disk)));
      E4_disk.close disk;
      false
  in
  let unchanged = before = pack_evidence directory in
  let after_control =
    if Sys.file_exists control then Some (read_file control) else None
  in
  Printf.printf
    "%s: pack evidence unchanged=%b, control unchanged=%b\n%!"
    name
    unchanged
    (before_control = after_control);
  remove directory;
  fault && unchanged && before_control = after_control
;;

let published () =
  let directory = temp () in
  let disk = open_ directory in
  ignore (get (E4_disk.commit disk (transaction [ schema; a ] [])));
  E4_disk.close disk;
  let file = E4_pack.seg_path ~dir:directory 0 in
  Unix.truncate file ((Unix.stat file).Unix.st_size - 1);
  report "published boundary beyond truncated bytes" directory (fun _ -> true)
;;

let rotated () =
  let directory = temp () in
  let pack = E4_pack.open_ ~dir:directory ~seg_max:128 in
  List.iter
    (fun value ->
       let bytes = E4_node.encode value in
       ignore (E4_pack.append pack ~digest:(E4_sha256.digest bytes) ~node_bytes:bytes))
    [ schema
    ; node E4_kind.Schema E4_node.zero_digest (vstr "schema2")
    ; node E4_kind.Schema E4_node.zero_digest (vstr "schema3")
    ];
  E4_pack.sync pack;
  E4_pack.close pack;
  directory
;;

let short_sealed () =
  let directory = rotated () in
  let reader = E4_pack.open_reader ~dir:directory in
  let segments = E4_pack.segments reader in
  E4_pack.close_reader reader;
  let last = List.fold_left max 0 segments in
  require (last >= 2) "rotation fixture";
  let file = E4_pack.seg_path ~dir:directory last in
  Unix.chmod file 0o600;
  Unix.truncate file 10;
  Unix.chmod file 0o444;
  report "short sealed trailing head" directory (function
    | E4_fault.Sealed_segment { seg; off = 0; _ } -> seg = last
    | _ -> false)
;;

let interior_sealed () =
  let directory = rotated () in
  let file = E4_pack.seg_path ~dir:directory 1 in
  let bytes = Bytes.of_string (read_file file) in
  Bytes.set bytes 3 (Char.chr (Char.code (Bytes.get bytes 3) lxor 1));
  Unix.chmod file 0o600;
  let channel = open_out_bin file in
  output_bytes channel bytes;
  close_out channel;
  Unix.chmod file 0o444;
  report "interior sealed bad head" directory (function
    | E4_fault.Sealed_segment { seg = 1; off = 0; _ } -> true
    | _ -> false)
;;

(* A pack directory the writer cannot list is an I/O fault, never an empty store: a listing that
   failed must not read as "no segments", or the writer recreates segment 0 over committed
   records (found by seat R1, 2026-10-19: segment 0 went from 121 bytes to 27).  The superuser
   ignores permission bits, so the case needs an ordinary user. *)
let unreadable_pack () =
  if Unix.geteuid () = 0
  then (
    print_endline "unreadable pack directory: skipped for the superuser";
    true)
  else (
    let directory = temp () in
    let disk = open_ directory in
    ignore (get (E4_disk.commit disk initial));
    E4_disk.close disk;
    let pack = Filename.concat directory "pack" in
    let before = pack_evidence directory in
    let mode = (Unix.stat pack).Unix.st_perm in
    Unix.chmod pack 0o300;
    let result = E4_disk.open_ ~dir:directory opts in
    Unix.chmod pack mode;
    let fault =
      match result with
      | Error (E4_admission.Fault (E4_fault.Io reason)) ->
        Printf.printf "unreadable pack directory: Fault io %s\n%!" reason;
        true
      | Error why ->
        Printf.printf "unreadable pack directory: %s\n%!" (E4_cas.admission_word why);
        false
      | Ok disk ->
        E4_disk.close disk;
        false
    in
    let unchanged = before = pack_evidence directory in
    Printf.printf "unreadable pack directory: pack evidence unchanged=%b\n%!" unchanged;
    remove directory;
    fault && unchanged)
;;

let () =
  let outcomes =
    [ published (); short_sealed (); interior_sealed (); unreadable_pack () ]
  in
  require (List.for_all Fun.id outcomes) "damage accepted or evidence changed";
  print_endline "published and sealed damage return faults without changing evidence"
;;
