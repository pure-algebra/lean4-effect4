(* race_process -- probe (seat 2, 2026-10-18): the parent holds the writer and commits ROUNDS advances;
   a forked child keeps opening the same store for 5 s, refused with Locked. Usage:
   race_process.exe ROUNDS. Rerun: copy this folder to ocaml/engine/test/<name>/ and build it there. *)
open Effect4_engine_cas
open Disk_test_support
let () =
  let rounds = int_of_string Sys.argv.(1) in
  let dir = temp () in
  let disk = open_ dir in
  ignore (E4_disk.commit disk (transaction [schema; a] [E4_control.Create ("docs/a", E4_control.Swap, target aa)]));
  match Unix.fork () with
  | 0 ->
    let locked = ref 0 and other = ref 0 in
    let deadline = Unix.gettimeofday () +. 5.0 in
    while Unix.gettimeofday () < deadline do
      match E4_disk.open_ ~dir opts with
      | Ok d -> incr other; E4_disk.close d
      | Error (E4_admission.Fault (E4_fault.Locked _)) -> incr locked
      | Error _ -> incr other
    done;
    Printf.printf "child: %d refused Locked, %d other\n%!" !locked !other;
    Unix._exit 0
  | child ->
    Unix.sleepf 0.05;
    let faults = ref 0 and oks = ref 0 and first = ref "" in
    for i = 1 to rounds do
      let gen = Z.of_int i in
      let target_digest = if i mod 2 = 1 then ba else aa in
      let from = if i mod 2 = 1 then aa else ba in
      match E4_disk.commit disk (transaction [b] [E4_control.Advance ("docs/a", {digest = from; generation = gen}, target target_digest)]) with
      | Ok _ -> incr oks
      | Error why -> incr faults; if !first = "" then first := transaction_observation (Error why)
    done;
    Printf.printf "parent: %d commits ok, %d failed%s\n%!" !oks !faults (if !first = "" then "" else " (first: " ^ !first ^ ")");
    ignore (Unix.waitpid [] child);
    E4_disk.close disk; remove dir
