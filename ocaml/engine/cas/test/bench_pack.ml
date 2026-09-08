(* bench_pack.ml — lane P1's bench: append + fsync throughput through E4_pack.

   Cells: node size 1 KiB and 64 KiB, group-commit batch 1 / 64 / 512 / 4096.  Each cell
   stages `batch` records, calls `sync` (one write(2) and one fsync(2) per batch, PK2), and
   reports nodes/s, MB/s and the mean and p99 of the per-commit latency.

   Acceptance, from docs/research/2026-09-08-engine-a2-persistence.md §4.5:
     B1  `put` fresh, 1 KiB node, batch 512, one commit per batch   >= 50 000 nodes/s
         (A2 §6.1 measured 90 090 nodes/s for the append+fsync alone; the put path adds one
         SHA-256 of ~1 KiB and one index insert, which is why the acceptance is lower than
         the floor this bench measures)
     B6  durable commit latency                                     <= 15 ms p99

   The digest is precomputed outside the timed loop and the payload string is reused, so
   this measures the PACK — the record framing, the crc, the coalesced write and the fsync —
   and not SHA-256.  That is the same shape as A2's probe `p_append2.ml` (§6.1), so the
   numbers are comparable with its table.

   Usage: bench_pack <dir> [byte-budget-MiB]
   The store is created under <dir>/bench-<pid> and removed at the end. *)

open Effect4_engine
open Effect4_engine_cas

let now () = Unix.gettimeofday ()

let rec rm_rf p =
  match Unix.lstat p with
  | exception Unix.Unix_error _ -> ()
  | { Unix.st_kind = Unix.S_DIR; _ } ->
    Array.iter (fun n -> rm_rf (Filename.concat p n)) (Sys.readdir p);
    (try Unix.rmdir p with Unix.Unix_error _ -> ())
  | _ -> ( try Sys.remove p with Sys_error _ -> ())

let percentile xs p =
  match List.sort compare xs with
  | [] -> 0.0
  | sorted ->
    let a = Array.of_list sorted in
    let i = int_of_float (ceil (p *. float_of_int (Array.length a))) - 1 in
    a.(max 0 (min (Array.length a - 1) i))

type row = {
  node : int;
  batch : int;
  count : int;
  commits : int;
  secs : float;
  nodes_s : float;
  mb_s : float;
  mean_ms : float;
  p99_ms : float;
}

let run ~root ~budget ~node ~batch =
  (* Aim at ~64 durable commits per cell so the p99 has something to stand on, bounded by
     the byte budget; at batch 1 the fsync itself sets the count. *)
  let count =
    let want = max (batch * 64) 200 in
    let cap = budget / node in
    max batch (min want cap)
  in
  let dir = Filename.concat root (Printf.sprintf "n%d-b%d" node batch) in
  rm_rf dir;
  let t = E4_pack.open_ ~dir ~seg_max:(4 * 1024 * 1024 * 1024) in
  let payload = String.make node 'x' in
  (* 256 distinct digests, precomputed: the pack stores what the caller computed (D5). *)
  let digests =
    Array.init 256 (fun i -> E4_sha256.digest (Printf.sprintf "%s%d" payload i))
  in
  let lat = ref [] in
  let t0 = now () in
  let staged = ref 0 in
  for i = 0 to count - 1 do
    ignore (E4_pack.append t ~digest:digests.(i land 255) ~node_bytes:payload);
    incr staged;
    if !staged = batch then begin
      let a = now () in
      E4_pack.sync t;
      lat := (now () -. a) :: !lat;
      staged := 0
    end
  done;
  if !staged > 0 then begin
    let a = now () in
    E4_pack.sync t;
    lat := (now () -. a) :: !lat
  end;
  let t1 = now () in
  E4_pack.close t;
  rm_rf dir;
  let dt = t1 -. t0 in
  let lat = !lat in
  let commits = List.length lat in
  { node;
    batch;
    count;
    commits;
    secs = dt;
    nodes_s = float_of_int count /. dt;
    mb_s = float_of_int (count * (node + 45)) /. dt /. 1_048_576.;
    mean_ms = List.fold_left ( +. ) 0.0 lat /. float_of_int (max 1 commits) *. 1000.;
    p99_ms = percentile lat 0.99 *. 1000. }

let fs_of path =
  (* /mnt/* is drvfs/9p under WSL; everything else on this host is ext4. *)
  let p = try Unix.realpath path with Unix.Unix_error _ | Sys_error _ -> path in
  if String.length p >= 5 && String.sub p 0 5 = "/mnt/" then "9p (drvfs)" else "ext4"

let () =
  let root_arg = if Array.length Sys.argv > 1 then Sys.argv.(1) else Filename.get_temp_dir_name () in
  let budget =
    (if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 512) * 1024 * 1024
  in
  let root = Filename.concat root_arg (Printf.sprintf "e4pack-bench-%d" (Unix.getpid ())) in
  (try Unix.mkdir root_arg 0o755 with Unix.Unix_error _ -> ());
  Unix.mkdir root 0o755;
  Printf.printf "bench_pack  dir=%s  fs=%s  budget=%d MiB\n" root (fs_of root_arg)
    (budget / 1048576);
  Printf.printf
    "%-8s %-6s %-8s %-8s %9s %12s %10s %10s %10s\n" "node" "batch" "count" "commits" "secs"
    "nodes/s" "MB/s" "mean ms" "p99 ms";
  let rows = ref [] in
  List.iter
    (fun node ->
      List.iter
        (fun batch ->
          let r = run ~root ~budget ~node ~batch in
          rows := r :: !rows;
          Printf.printf "%-8d %-6d %-8d %-8d %9.3f %12.1f %10.2f %10.3f %10.3f\n%!" r.node
            r.batch r.count r.commits r.secs r.nodes_s r.mb_s r.mean_ms r.p99_ms)
        [ 1; 64; 512; 4096 ])
    [ 1024; 65536 ];
  rm_rf root;
  let rows = List.rev !rows in
  let find node batch = List.find_opt (fun r -> r.node = node && r.batch = batch) rows in
  print_newline ();
  (match find 1024 512 with
   | Some r ->
     Printf.printf "B1  1 KiB node, batch 512, one commit per batch: %.1f nodes/s  (>= 50 000)  %s\n"
       r.nodes_s
       (if r.nodes_s >= 50_000. then "PASS" else "FAIL");
     Printf.printf "    A2 §6.1 measured 90 090 nodes/s for the same cell as a raw append+fsync probe\n"
   | None -> print_endline "B1  not measured");
  (match find 1024 512 with
   | Some r ->
     Printf.printf "B6  durable commit latency at that cell: p99 %.3f ms  (<= 15 ms)  %s\n"
       r.p99_ms
       (if r.p99_ms <= 15.0 then "PASS" else "FAIL")
   | None -> print_endline "B6  not measured");
  let worst =
    List.fold_left
      (fun acc r -> if r.node = 1024 && r.batch <= 512 && r.p99_ms > acc then r.p99_ms else acc)
      0.0 rows
  in
  Printf.printf "B6' worst p99 over the 1 KiB cells at batch <= 512: %.3f ms  (<= 15 ms)  %s\n"
    worst
    (if worst <= 15.0 then "PASS" else "FAIL");
  print_endline
    "    the 64 KiB rows are reported, not judged: a 32 MB commit is a bandwidth cell, not a\n\
    \    latency one, and A2 §4.5 states B6 for the 1 KiB operating point."
