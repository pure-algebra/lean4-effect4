(* bench_wal.ml — lane P5's numbers: the log's half of the bench matrix
   (docs/research/2026-09-08-engine-a2-persistence.md §4.5, cells B8 and B9).

   What it measures, and why those cells:
     append   rows/s with group commit, at 64 B, 256 B and 1 KB bodies and batch 1 / 64 / 512.
              Every commit is one write(2) and one fsync(2) (LG3), so batch 1 measures the
              fsync latency of the filesystem and batch 512 measures the coalesced path.  B8
              is the 256 B / batch 512 cell: >= 200 000 rows/s.
     replay   rows/s of a full replay from index 0, every checksum verified.  B9: >= 1 000 000
              rows/s.  Reported for the 256 B row set.
     latency  the mean milliseconds per durable commit, which is what B6 bounds for the store.

   It is an executable, not a test: it fsyncs thousands of times and its numbers depend on the
   filesystem, so it is run by hand with the directories to measure as its arguments —

     bench_wal ~/e4bench /mnt/c/Users/.../scratchpad/p5/bench

   with no argument it uses one directory under the system temp directory.  A2 §6.1 measures
   the same shape for the pack and says the store must live on ext4, never on 9p (/mnt/c):
   this bench is what says whether the log agrees. *)

open Effect4_engine_cas

let now () = Unix.gettimeofday ()

let rm_rf path =
  let rec go p =
    match Sys.is_directory p with
    | exception Sys_error _ -> ()
    | true ->
      Array.iter (fun e -> go (Filename.concat p e)) (Sys.readdir p);
      (try Unix.rmdir p with Unix.Unix_error _ -> ())
    | false -> ( try Sys.remove p with Sys_error _ -> ())
  in
  go path

let job_counter = ref 0

let next_job () =
  incr job_counter;
  let b = Bytes.make 32 '\000' in
  Bytes.set b 31 (Char.chr (!job_counter land 0xff));
  Bytes.set b 30 (Char.chr ((!job_counter lsr 8) land 0xff));
  E4_addr.Addr.of_digest (Bytes.to_string b)

(* One cell: n rows of `size` bytes, one commit every `batch` rows. *)
let append_cell ~dir ~size ~batch ~n =
  let job = next_job () in
  let body = String.make size 'r' in
  let w = E4_wal.open_ ~dir ~job ~seg_max:(64 * 1024 * 1024) in
  let commits = ref 0 in
  let t0 = now () in
  for i = 1 to n do
    ignore (E4_wal.append w (E4_wal.Decision body) : int);
    if i mod batch = 0 then begin
      E4_wal.commit w;
      incr commits
    end
  done;
  E4_wal.commit w;
  if n mod batch <> 0 then incr commits;
  let t1 = now () in
  E4_wal.close w;
  let elapsed = t1 -. t0 in
  (job, elapsed, float_of_int n /. elapsed, elapsed *. 1000. /. float_of_int !commits)

let replay_cell ~dir ~job ~n =
  let r = E4_wal.open_reader ~dir ~job in
  let count = ref 0 in
  let t0 = now () in
  let stop = E4_wal.replay r ~from:0 ~f:(fun _ _ -> incr count) in
  let t1 = now () in
  E4_wal.close_reader r;
  if !count <> n || stop <> E4_wal.Eof then
    failwith
      (Printf.sprintf "replay disagreed: %d of %d rows, %s" !count n
         (E4_wal.stop_to_string stop));
  (float_of_int n /. (t1 -. t0), t1 -. t0)

let verdict ok = if ok then "MEET" else "MISS"

let run_dir dir =
  Printf.printf "\n== %s ==\n" dir;
  Printf.printf "%-8s %-7s %-9s %12s %10s %12s\n" "row" "batch" "rows" "rows/s" "MB/s"
    "ms/commit";
  let replay_of = ref None in
  let cells = Hashtbl.create 16 in
  List.iter
    (fun size ->
      List.iter
        (fun (batch, n) ->
          let job, _, rate, ms = append_cell ~dir ~size ~batch ~n in
          Hashtbl.replace cells (size, batch) (rate, ms);
          Printf.printf "%-8d %-7d %-9d %12.1f %10.2f %12.3f\n" size batch n rate
            (rate *. float_of_int size /. 1048576.)
            ms;
          if size = 256 && batch = 512 then replay_of := Some (job, n))
        [ (1, 200); (64, 12800); (512, 51200); (4096, 102400) ])
    [ 64; 256; 1024 ];
  let replay_rate =
    match !replay_of with
    | None -> 0.
    | Some (job, n) ->
      let rate, secs = replay_cell ~dir ~job ~n in
      Printf.printf "replay   %-7s %-9d %12.1f %10s %12.3f\n" "-" n rate "-" (secs *. 1000.);
      rate
  in
  let cell k = try Hashtbl.find cells k with Not_found -> (0., 0.) in
  let b8_rate, b8_ms = cell (256, 512) in
  let b8b_rate, b8b_ms = cell (256, 4096) in
  Printf.printf "\nB8  append 256 B, batch 512   >= 200 000 rows/s : %10.1f  %s  (%.2f ms/commit)\n"
    b8_rate (verdict (b8_rate >= 200000.)) b8_ms;
  Printf.printf "B8' append 256 B, batch 4096  >= 200 000 rows/s : %10.1f  %s  (%.2f ms/commit; B6 bounds a commit at 15 ms)\n"
    b8b_rate (verdict (b8b_rate >= 200000.)) b8b_ms;
  Printf.printf "B9  replay from 0, 51 200 rows >= 1 000 000 rows/s : %8.1f  %s\n" replay_rate
    (verdict (replay_rate >= 1000000.));
  Printf.printf
    "    (durable append is fsync-bound: rows/s = batch / commit latency, so B8 at batch 512\n\
    \     needs a commit under 2.6 ms; this filesystem's fsync is the number that decides it.)\n"

let () =
  let dirs =
    match Array.to_list Sys.argv with
    | _ :: (_ :: _ as ds) -> ds
    | _ ->
      [ Filename.concat (Filename.get_temp_dir_name ())
          (Printf.sprintf "e4_wal_bench_%d" (Unix.getpid ())) ]
  in
  Printf.printf "bench_wal — A2 §4.5 cells B8 (append, 256 B, batch 512: >= 200 000 rows/s)\n";
  Printf.printf "            and B9 (replay from 0, every checksum verified: >= 1 000 000 rows/s)\n";
  List.iter
    (fun d ->
      rm_rf d;
      Fun.protect ~finally:(fun () -> rm_rf d) (fun () -> run_dir d))
    dirs
