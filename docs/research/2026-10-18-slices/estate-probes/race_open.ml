(* race_open -- probe (seat 2, 2026-10-18): two domains call E4_pack.open_ on one fresh directory at once,
   TRIALS times; it counts how often both get a writer. Usage: race_open.exe TRIALS (cold|warm).
   Rerun: copy this folder to ocaml/engine/test/<name>/ and build it there with dune. *)
open Effect4_engine_cas
let () =
  let trials = int_of_string Sys.argv.(1) in
  let mode = Sys.argv.(2) in
  let doubles = ref 0 and singles = ref 0 and nones = ref 0 and raised = ref 0 in
  for _ = 1 to trials do
    let dir = Disk_test_support.temp () in
    if mode = "warm" then (Unix.mkdir (Filename.concat dir "pack") 0o700);
    let go = Atomic.make false in
    let attempt () =
      while not (Atomic.get go) do Domain.cpu_relax () done;
      match E4_pack.open_ ~dir ~seg_max:4096 with
      | p -> `Ok p
      | exception E4_pack.Locked _ -> `Refused
      | exception e -> `Raised (Printexc.to_string e) in
    let d1 = Domain.spawn attempt and d2 = Domain.spawn attempt in
    Atomic.set go true;
    let r1 = Domain.join d1 and r2 = Domain.join d2 in
    (match r1, r2 with
     | `Ok a, `Ok b -> incr doubles; E4_pack.close a; (try E4_pack.close b with _ -> ())
     | `Ok a, _ | _, `Ok a -> incr singles; E4_pack.close a
     | _ -> incr nones);
    (match r1, r2 with `Raised m, _ | _, `Raised m -> incr raised; if !raised <= 3 then prerr_endline ("raised: " ^ m) | _ -> ());
    Disk_test_support.remove dir
  done;
  Printf.printf "trials=%d both-opened=%d one-opened=%d none=%d raised=%d\n" trials !doubles !singles !nones !raised
