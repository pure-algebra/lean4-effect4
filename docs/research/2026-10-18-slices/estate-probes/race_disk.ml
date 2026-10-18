(* race_disk -- probe (seat 2, 2026-10-18): two domains call E4_disk.open_ on one fresh store at once,
   TRIALS times; it tallies what each domain gets. Usage: race_disk.exe TRIALS.
   Rerun: copy this folder to ocaml/engine/test/<name>/ and build it there with dune. *)
open Effect4_engine_cas
let () =
  let trials = int_of_string Sys.argv.(1) in
  let tally = Hashtbl.create 8 in
  let note k = Hashtbl.replace tally k (1 + Option.value ~default:0 (Hashtbl.find_opt tally k)) in
  for _ = 1 to trials do
    let dir = Disk_test_support.temp () in
    let go = Atomic.make false in
    let attempt () =
      while not (Atomic.get go) do Domain.cpu_relax () done;
      match E4_disk.open_ ~dir Disk_test_support.opts with
      | Ok d -> `Ok d
      | Error why -> `Refused (Disk_test_support.admission_observation why)
      | exception e -> `Raised (Printexc.to_string e) in
    let d1 = Domain.spawn attempt and d2 = Domain.spawn attempt in
    Atomic.set go true;
    let r1 = Domain.join d1 and r2 = Domain.join d2 in
    let word = function `Ok _ -> "ok" | `Refused w -> "refused " ^ w | `Raised m -> "raised " ^ m in
    note (word r1 ^ " | " ^ word r2);
    (match r1 with `Ok a -> E4_disk.close a | _ -> ());
    (match r2 with `Ok b -> (try E4_disk.close b with _ -> ()) | _ -> ());
    Disk_test_support.remove dir
  done;
  Hashtbl.iter (fun k n -> Printf.printf "%5d  %s\n" n k) tally
