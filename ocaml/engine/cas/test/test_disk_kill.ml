(* Properties: actual process kills at write, sync, and publication hooks reopen to the
   corresponding accepted Cut images emitted by Lean. Process kills are finite host evidence. *)
open Effect4_engine_cas
open Disk_test_support

let expected_rows () =
  let channel = open_in (golden_path "disk-cuts.tsv") in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () ->
       let rec loop rows =
         match input_line channel with
         | exception End_of_file -> List.rev rows
         | line when String.length line > 0 && line.[0] = '#' -> loop rows
         | line ->
           (match String.split_on_char '\t' line with
            | [ name; image ] -> loop ((name, image) :: rows)
            | _ -> failwith "bad cut oracle row")
       in
       loop [])
;;

let target_point = function
  | "before-write0" -> E4_cas.Before_write 0
  | "after-write1" -> E4_cas.After_write 1
  | "after-write2" -> E4_cas.After_write 2
  | "after-sync" -> E4_cas.After_sync
  | "before-publish" -> E4_cas.Before_publish
  | "after-publish" -> E4_cas.After_publish
  | _ -> failwith "unknown cut hook"
;;

let () =
  let rows = expected_rows () in
  require
    (List.equal
       String.equal
       (List.sort String.compare (List.map fst rows))
       (List.sort
          String.compare
          [ "before-write0"
          ; "after-write1"
          ; "after-write2"
          ; "after-sync"
          ; "before-publish"
          ; "after-publish"
          ]))
    "cut census";
  List.iter
    (fun (name, expected) ->
       let directory = temp () in
       let disk = open_ directory in
       ignore (get (E4_disk.commit disk initial));
       E4_disk.close disk;
       let point = target_point name in
       let child = Unix.fork () in
       if child = 0
       then (
         let disk = open_ directory in
         let hook reached =
           if reached = point then Unix.kill (Unix.getpid ()) Sys.sigkill
         in
         ignore
           (get
              (E4_disk.commit
                 ~hook
                 disk
                 (transaction
                    [ a; b; t; u ]
                    [ E4_control.Advance
                        ("docs/a", { digest = aa; generation = Z.one }, target ba)
                    ])));
         E4_disk.close disk;
         Unix._exit 73);
       let _, status = Unix.waitpid [] child in
       require (status = Unix.WSIGNALED Sys.sigkill) ("kill hook not reached: " ^ name);
       let disk =
         match E4_disk.open_ ~dir:directory opts with
         | Ok disk -> disk
         | Error why ->
           remove directory;
           failwith
             ("accepted cut " ^ name ^ " reopen fault: " ^ E4_cas.admission_word why)
       in
       let actual = observation (snapshot disk) in
       require (String.equal actual expected) ("accepted cut mismatch: " ^ name);
       E4_disk.close disk;
       remove directory;
       Printf.printf "PASS actual kill %s matches accepted Cut\n%!" name)
    rows
;;
