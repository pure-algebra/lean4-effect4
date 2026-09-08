(* bench_trace.ml — lane W, item 2: what `E4_trace` costs now that it is `E4_log.Vec`.

   Three cells, all on the carrier alone (no machine, no tape), so the number is the carrier's
   and nothing else's:

     W2a  the VIEWER'S WALK -- `nth_opt i` for every i of a 6 003-row trace, which is the
          reading axis of 2026-09-08-design-language.md §3 and the Theta(T^2) that lane Q3's
          proposal N2 is about.  6 003 rows is `pStmts`' order of magnitude.
     W2b  `emit` throughput, one event per call, which is the shape `RunMachine.emit` has on
          the innermost step (src/Effect4/Machine/Fibers.lean:1123).
     W2c  `to_list` -- the once-per-run read (`Api.Run.trace`, Api.lean:185-186).

   A bench is a measurement and not a gate: this file prints a table and fails nothing.

   Run: cd ocaml && dune build engine && ./_build/default/engine/test/bench_trace.exe *)

open Effect4_engine

let now () = Unix.gettimeofday ()
let rate n dt = if dt <= 0.0 then infinity else float_of_int n /. dt

let build n =
  let t = ref E4_trace.empty in
  for i = 0 to n - 1 do
    t := E4_trace.emit [ i ] !t
  done;
  !t

let hr () = print_endline (String.make 78 '-')

(* W2a: the walk, forward and backward, plus a strided order so no single direction can
   flatter the carrier. *)
let walk () =
  hr ();
  print_endline "W2a  the viewer's walk: nth_opt at every index";
  List.iter
    (fun n ->
      let t = build n in
      let sink = ref 0 in
      let t0 = now () in
      for i = 0 to n - 1 do
        match E4_trace.nth_opt i t with Some v -> sink := !sink + v | None -> ()
      done;
      let dt_f = now () -. t0 in
      let t1 = now () in
      for i = n - 1 downto 0 do
        match E4_trace.nth_opt i t with Some v -> sink := !sink + v | None -> ()
      done;
      let dt_b = now () -. t1 in
      let j = ref 0 in
      let t2 = now () in
      for _ = 1 to n do
        (match E4_trace.nth_opt !j t with Some v -> sink := !sink + v | None -> ());
        j := (!j + 2731) mod n
      done;
      let dt_s = now () -. t2 in
      Printf.printf
        "  %6d rows  forward %8.3f ms (%10.0f rows/s)  backward %8.3f ms  strided %8.3f ms  \
         [sink %d]\n%!"
        n (dt_f *. 1000.) (rate n dt_f) (dt_b *. 1000.) (dt_s *. 1000.) !sink)
    [ 1_000; 6_003; 20_000 ]

let emit_cell () =
  hr ();
  print_endline "W2b  emit: one event per call";
  List.iter
    (fun n ->
      let t0 = now () in
      let t = build n in
      let dt = now () -. t0 in
      Printf.printf "  %8d emits  %8.3f ms  (%12.0f events/s)  length %d\n%!" n (dt *. 1000.)
        (rate n dt) (E4_trace.length t))
    [ 100_000; 1_000_000 ]

let to_list_cell () =
  hr ();
  print_endline "W2c  to_list: the once-per-run read";
  List.iter
    (fun n ->
      let t = build n in
      let t0 = now () in
      let l = E4_trace.to_list t in
      let dt = now () -. t0 in
      Printf.printf "  %8d rows  %8.3f ms  (%12.0f rows/s)  head %s\n%!" n (dt *. 1000.)
        (rate n dt)
        (match l with [] -> "-" | x :: _ -> string_of_int x))
    [ 6_003; 1_000_000 ]

let () =
  print_endline "bench_trace — lane W item 2 (E4_trace over E4_log.Vec)";
  walk ();
  emit_cell ();
  to_list_cell ();
  hr ()
