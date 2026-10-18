(* race_commit -- probe (seat 2, 2026-10-18): domain A holds the writer and commits ROUNDS advances;
   domain B keeps opening the same store, which must be refused with Locked and change nothing.
   NO_OPENER=1 is the control: A commits alone. Usage: race_commit.exe ROUNDS.
   Rerun: copy this folder to ocaml/engine/test/<name>/ and build it there with dune. *)
open Effect4_engine_cas
open Disk_test_support
let () =
  let rounds = int_of_string Sys.argv.(1) in
  let dir = temp () in
  let disk = open_ dir in
  ignore (E4_disk.commit disk (transaction [schema; a] [E4_control.Create ("docs/a", E4_control.Swap, target aa)]));
  let stop = Atomic.make false in
  let opener () =
    let tally = Hashtbl.create 4 in
    while (Sys.getenv_opt "NO_OPENER" = None) && not (Atomic.get stop) do
      let w = match E4_disk.open_ ~dir opts with
        | Ok d -> E4_disk.close d; "ok (a second writer)"
        | Error why -> admission_observation why
        | exception e -> "raised " ^ Printexc.to_string e in
      let w = if String.length w > 40 then String.sub w 0 40 else w in
      Hashtbl.replace tally w (1 + Option.value ~default:0 (Hashtbl.find_opt tally w))
    done; tally in
  let other = Domain.spawn opener in
  let faults = ref 0 and oks = ref 0 and first = ref "" in
  for i = 1 to rounds do
    let gen = Z.of_int i in
    let target_digest = if i mod 2 = 1 then ba else aa in
    let from = if i mod 2 = 1 then aa else ba in
    match E4_disk.commit disk (transaction [b] [E4_control.Advance ("docs/a", {digest = from; generation = gen}, target target_digest)]) with
    | Ok _ -> incr oks
    | Error why -> incr faults; if !first = "" then first := transaction_observation (Error why)
  done;
  Atomic.set stop true;
  let tally = Domain.join other in
  Printf.printf "A: %d commits ok, %d failed%s\n" !oks !faults (if !first = "" then "" else " (first: " ^ !first ^ ")");
  Hashtbl.iter (fun k n -> Printf.printf "B: %6d  %s\n" n k) tally;
  E4_disk.close disk; remove dir
