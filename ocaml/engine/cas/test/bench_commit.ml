(* bench_commit — what one E4_disk commit costs as the store grows.

   What it measures: a store opened empty, then N one-node transactions (N = argv[1], default 400),
   each a fresh export node; it prints the mean milliseconds of the first and the last 100 commits.
   A commit that costs its transaction stays flat; one that re-reads the store grows with it.
   Writes only under the system temp directory and removes what it made.
   Run: cd ocaml && opam exec --switch=effect4 -- dune exec engine/cas/test/bench_commit.exe -- 400 *)
open Effect4_engine_cas
open Disk_test_support

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 400 in
  let directory = temp () in
  let disk = open_ directory in
  ignore (get (E4_disk.commit disk (transaction [ schema ] [])));
  let times = Array.make n 0.0 in
  for i = 0 to n - 1 do
    let fresh = node E4_kind.Export (E4_addr.Addr.bytes s) (vstr (Printf.sprintf "node-%d" i)) in
    let start = Unix.gettimeofday () in
    ignore (get (E4_disk.commit disk (transaction [ fresh ] [])));
    times.(i) <- (Unix.gettimeofday () -. start) *. 1000.0
  done;
  let mean lo hi =
    let sum = ref 0.0 in
    for i = lo to hi - 1 do sum := !sum +. times.(i) done;
    !sum /. float_of_int (hi - lo)
  in
  let block = min 100 n in
  Printf.printf "commits %d: first %d mean %.3f ms, last %d mean %.3f ms\n" n block (mean 0 block) block
    (mean (n - block) n);
  E4_disk.close disk;
  remove directory
