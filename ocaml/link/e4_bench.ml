(* e4_bench.ml — a thin driver: M machines of pTwo across 1, 2, 4, 8 domains, and the
   single-machine step rate for pFork on the main domain.

     e4_bench.exe [machines=200] [reps=3] [single-iters=20000]

   Every number is a wall-clock measurement (`Unix.gettimeofday`); the best of `reps`
   runs is reported, with the median beside it. *)

let now = Unix.gettimeofday

let median xs =
  let a = Array.of_list (List.sort compare xs) in
  a.(Array.length a / 2)

type run = { load_s : float; run_s : float; steps : int; finished : int }

let one_run ~domains ~machines ~fuel =
  let host = E4_host.start { E4_host.default_config with domains; ring_capacity = 4096 } in
  let t0 = now () in
  let ids = List.init machines (fun _ -> E4_host.spawn host ~program:"pTwo" ~fuel) in
  ignore (E4_host.run_until_quiescent host);
  let t1 = now () in
  List.iter
    (fun id ->
      (match E4_host.send host id E4_bridge.Evaluate with Ok _ -> () | Error _ -> failwith "send refused");
      match E4_host.send host id E4_bridge.Flush with Ok _ -> () | Error _ -> failwith "send refused")
    ids;
  ignore (E4_host.run_until_quiescent host);
  let t2 = now () in
  let steps, finished =
    List.fold_left
      (fun (steps, finished) id ->
        match E4_host.inspect host id with
        | Some (s : E4_worker.status) -> (steps + s.steps, if s.finished then finished + 1 else finished)
        | None -> (steps, finished))
      (0, 0) ids
  in
  E4_host.shutdown host;
  { load_s = t1 -. t0; run_s = t2 -. t1; steps; finished }

let bench_domains ~machines ~reps ~fuel =
  Printf.printf "\n%d machines of pTwo, evaluate + flush each (fires from the event-loop rule), fuel %d, best of %d\n\n"
    machines fuel reps;
  Printf.printf "| domains | machines | finished | steps | load ms (best) | run ms (best) | run ms (median) | steps/s (best) | machines/s (best) |\n";
  Printf.printf "| --- | --- | --- | --- | --- | --- | --- | --- | --- |\n";
  List.iter
    (fun domains ->
      let runs = List.init reps (fun _ -> one_run ~domains ~machines ~fuel) in
      let best = List.fold_left (fun b r -> if r.run_s < b.run_s then r else b) (List.hd runs) runs in
      let best_load = List.fold_left (fun m r -> min m r.load_s) infinity runs in
      let med = median (List.map (fun r -> r.run_s) runs) in
      Printf.printf "| %d | %d | %d | %d | %.2f | %.2f | %.2f | %.0f | %.0f |\n%!" domains machines best.finished
        best.steps (best_load *. 1000.) (best.run_s *. 1000.) (med *. 1000.)
        (float_of_int best.steps /. best.run_s)
        (float_of_int machines /. best.run_s))
    [ 1; 2; 4; 8 ]

let bench_single ~program ~iters ~fuel =
  E4_bridge.init ();
  let bad = ref 0 in
  let t0 = now () in
  for _ = 1 to iters do
    let s0 = E4_bridge.load ~program ~fuel in
    let s1 = E4_bridge.step s0 ~fuel E4_bridge.Evaluate in
    let s2 = E4_bridge.step s1 ~fuel E4_bridge.Flush in
    if not (E4_bridge.finished s2) then incr bad;
    E4_bridge.release s0;
    E4_bridge.release s1;
    E4_bridge.release s2
  done;
  let dt = now () -. t0 in
  (* steps only: the same loads, timed apart, so the step rate can be separated *)
  let t1 = now () in
  let sessions = Array.init iters (fun _ -> E4_bridge.load ~program ~fuel) in
  let t2 = now () in
  let load_s = t2 -. t1 in
  let t3 = now () in
  Array.iteri
    (fun i s0 ->
      let s1 = E4_bridge.step s0 ~fuel E4_bridge.Evaluate in
      let s2 = E4_bridge.step s1 ~fuel E4_bridge.Flush in
      if not (E4_bridge.finished s2) then incr bad;
      E4_bridge.release s1;
      E4_bridge.release s2;
      E4_bridge.release s0;
      sessions.(i) <- s2)
    sessions;
  let step_s = now () -. t3 in
  Printf.printf "\nsingle machine on the main domain, %s, fuel %d, %d iterations (load, evaluate, flush), %d not finished\n\n"
    program fuel iters !bad;
  Printf.printf "| what | wall ms | per second |\n| --- | --- | --- |\n";
  Printf.printf "| load + evaluate + flush | %.1f | %.0f iterations/s (%.0f steps/s) |\n" (dt *. 1000.)
    (float_of_int iters /. dt)
    (float_of_int (2 * iters) /. dt);
  Printf.printf "| load only | %.1f | %.0f loads/s |\n" (load_s *. 1000.) (float_of_int iters /. load_s);
  Printf.printf "| evaluate + flush only | %.1f | %.0f steps/s |\n%!" (step_s *. 1000.)
    (float_of_int (2 * iters) /. step_s)

let () =
  let arg i default = if Array.length Sys.argv > i then int_of_string Sys.argv.(i) else default in
  let machines = arg 1 200 and reps = arg 2 3 and iters = arg 3 20000 in
  let fuel = 100 in
  Printf.printf "e4_bench: %d cpus recommended by the runtime\n" (Domain.recommended_domain_count ());
  bench_domains ~machines ~reps ~fuel;
  bench_single ~program:"pFork" ~iters ~fuel
