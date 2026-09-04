(* e4_probe.ml — the route-1 spike driver (formerly e4.ml), on the typed bridge: one
   program, one decision at a time, the snapshot after each; driving with fuel 1..6 from
   the loaded machine; firing the armed dispatchers by hand; the loaded machine unchanged.

     e4_probe.exe [program=pFork] [fuel=100] *)

let section title = Printf.printf "\n==== %s ====\n%!" title
let show label s = Printf.printf "-- %s\n%s\n%!" label (E4_bridge.snapshot s)

let () =
  E4_bridge.init ();
  section "programs";
  List.iter print_endline (E4_bridge.program_names ());
  let program = if Array.length Sys.argv > 1 then Sys.argv.(1) else "pFork" in
  let fuel = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 100 in

  section (program ^ ": the two-decision tape, one decision at a time");
  let s0 = E4_bridge.load ~program ~fuel in
  show "loaded" s0;
  let s1 = E4_bridge.step s0 ~fuel E4_bridge.Evaluate in
  show "after evaluate root" s1;
  let s2 = E4_bridge.step s1 ~fuel E4_bridge.Flush in
  show "after flush" s2;
  Printf.printf "typed: armed=[%s] finished=%b trace_len=%d\n"
    (String.concat "," (List.map string_of_int (E4_bridge.armed s2)))
    (E4_bridge.finished s2) (E4_bridge.trace_len s2);
  List.iter (fun f -> print_endline ("  " ^ E4_bridge.pp_fiber f)) (E4_bridge.fibers s2);

  section (program ^ ": the same run, driving the root with fuel 1, 2, 3 ... from the loaded machine");
  (* Every intermediate is a genuine machine value; fuel is not monotone (R2), so these are
     reachable states, not prefixes of one run. The loaded machine s0 is untouched: values. *)
  for f = 1 to 6 do
    show (Printf.sprintf "drive fuel=%d" f) (E4_bridge.drive s0 ~fuel:f)
  done;

  section (program ^ ": firing the armed dispatchers by hand instead of flush");
  let rec fire_all s n =
    if n > 0 then
      match E4_bridge.armed s with
      | owner :: _ ->
          let s' = E4_bridge.step s ~fuel (E4_bridge.Fire owner) in
          show (Printf.sprintf "fire:%d" owner) s';
          fire_all s' (n - 1)
      | [] -> ()
  in
  fire_all s1 8;
  section "the original loaded machine is unchanged (values, not state)";
  show "s0 again" s0
