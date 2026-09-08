(* bench_cas.ml — lane P4's half of docs/research/2026-09-08-engine-a2-persistence.md §4.5:
   the store's own cells.  An executable, not a test: it fsyncs and writes hundreds of MB, so
   it is run by hand with the directories to measure as its arguments.

     put fresh       A2 cell B1, acceptance >= 50 000 nodes/s at 1 KiB nodes, batch 512
     put duplicate   A2 cell B2, acceptance >= 1 000 000 nodes/s
     get_bytes warm  A2 cell B3, acceptance >= 500 000 nodes/s
     index rebuild   A2 cell B4, acceptance >= 1 000 000 nodes/s
     index memory    A2 cell B5, acceptance <= 40 bytes per node
     closure         the lane brief's B4; no A2 acceptance, the number is the deliverable
     verify          the lane brief's B5; no A2 acceptance, the number is the deliverable

   Every cell is run at TWO node sizes, because three of the five acceptances are bounded by
   SHA-256 throughput and are therefore a function of the node size, not of the store: a put
   hashes the node's bytes once (that is what an address IS), so at 1 KiB nodes no put path
   can exceed sha256's own rate.  The `sha256` row measures that ceiling on this host so the
   verdicts can be read against it rather than against a hope.

   Usage:  bench_cas.exe [dir ...]        (default: one directory under the system temp dir)

   A2 §6.2 measures a 72x read penalty on /mnt/c against ext4, so pass BOTH a Linux-side
   directory and one under /mnt/c to see it.  Each directory is removed at the end. *)

open Effect4_engine
open Effect4_engine_cas

let n_nodes = try int_of_string (Sys.getenv "E4_BENCH_N") with _ -> 20_000
let batch = try int_of_string (Sys.getenv "E4_BENCH_BATCH") with _ -> 512
let chain_len = try int_of_string (Sys.getenv "E4_BENCH_CHAIN") with _ -> 2_000

let v_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let v_str s = E4_be.framed Eff_frame.tag_string s
let v_bytes b = E4_be.framed Eff_frame.tag_bytes b
let v_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (v_nat i :: args))
let v_ref k d = E4_be.framed Eff_frame.tag_ref (String.make 1 (Char.chr k) ^ d)
let zero = E4_node.zero_digest
let node kind spec payload = { E4_node.version = 0; kind; spec; payload }
let genesis = node E4_kind.Schema zero (v_str "schema")
let spec = E4_addr.Addr.bytes (E4_node.address genesis)

let flat size i =
  node E4_kind.Export spec (v_ctor 0 [ v_nat i; v_bytes (String.make (max 1 (size - 60)) 'x') ])

let rec rm_rf p =
  match Unix.lstat p with
  | exception Unix.Unix_error _ -> ()
  | { Unix.st_kind = Unix.S_DIR; _ } ->
    Array.iter (fun n -> rm_rf (Filename.concat p n)) (Sys.readdir p);
    (try Unix.rmdir p with Unix.Unix_error _ -> ())
  | _ -> ( try Sys.remove p with Sys_error _ -> ())

let rec mkdir_p d =
  if d <> "" && d <> "/" && d <> Filename.dirname d && not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error _ -> ()
  end

let now () = Unix.gettimeofday ()

let row cell what n secs unit_ verdict =
  Printf.printf "| %-14s | %-30s | %8d | %7.3f s | %10.0f %-8s | %s |\n%!" cell what n secs
    (if secs > 0.0 then float_of_int n /. secs else 0.0)
    unit_ verdict

let plain cell what value verdict =
  Printf.printf "| %-14s | %-30s | %8s | %9s | %19s | %s |\n%!" cell what "-" "-" value verdict

let verdict ok = if ok then "PASS" else "under"

let header () =
  Printf.printf
    "\n| cell           | what                           |        n |      time |         rate        | verdict |\n";
  Printf.printf
    "| -------------- | ------------------------------ | -------- | --------- | ------------------- | ------- |\n"

(* The ceiling every put and every verify sits under: one SHA-256 of the node's bytes. *)
let bench_sha256 size =
  let s = String.make size 'x' in
  let n = 200_000 in
  let t0 = now () in
  for _ = 1 to n do
    ignore (E4_sha256.digest s)
  done;
  let t = now () -. t0 in
  row "sha256" (Printf.sprintf "%d B, the address's own cost" size) n t "hash/s" "ceiling"

let bench_size dir size =
  let dir = Printf.sprintf "%s-%d" dir size in
  mkdir_p dir;
  let opts = { E4_cas.default_opts with seg_max = 1 lsl 30; index_slots = n_nodes } in
  let s = E4_cas.open_rw ~dir opts in
  ignore (E4_cas.put s genesis);
  E4_cas.commit s;
  let nodes = Array.init n_nodes (flat size) in
  let t0 = now () in
  Array.iteri
    (fun i n ->
      ignore (E4_cas.put s n);
      if (i + 1) mod batch = 0 then E4_cas.commit s)
    nodes;
  E4_cas.commit s;
  let t_fresh = now () -. t0 in
  row "B1 put fresh" (Printf.sprintf "%d B nodes, batch %d" size batch) n_nodes t_fresh "nodes/s"
    (verdict (float_of_int n_nodes /. t_fresh >= 50_000.0));
  let t0 = now () in
  Array.iter (fun n -> ignore (E4_cas.put s n)) nodes;
  let t_dup = now () -. t0 in
  row "B2 put dup" (Printf.sprintf "%d B nodes, resident" size) n_nodes t_dup "nodes/s"
    (verdict (float_of_int n_nodes /. t_dup >= 1_000_000.0));
  let ro = E4_cas.read_only s in
  let addrs = Array.map E4_node.address nodes in
  let order = Array.init n_nodes (fun i -> i * 7919 mod n_nodes) in
  let t0 = now () in
  let total = ref 0 in
  Array.iter
    (fun i ->
      match E4_cas.get_bytes ro addrs.(i) with
      | Some b -> total := !total + String.length b
      | None -> ())
    order;
  let t_get = now () -. t0 in
  row "B3 get_bytes" (Printf.sprintf "%d B, warm, scattered" size) n_nodes t_get "nodes/s"
    (verdict (float_of_int n_nodes /. t_get >= 500_000.0));
  if !total = 0 then prerr_endline "the reads answered nothing";
  E4_cas.drop_index ro;
  let t0 = now () in
  let n_idx = E4_cas.index_count ro in
  let t_idx = now () -. t0 in
  row "B4 idx rebuild" "drop, rebuild from the pack" n_idx t_idx "nodes/s"
    (verdict (float_of_int n_idx /. t_idx >= 1_000_000.0));
  let st = E4_cas.stats ro in
  plain "B5 idx memory" "off-heap bytes per node"
    (Printf.sprintf "%.1f B/node" (float_of_int st.E4_cas.index_bytes /. float_of_int (max 1 st.E4_cas.nodes)))
    (verdict (st.E4_cas.index_bytes <= 40 * st.E4_cas.nodes));
  let t0 = now () in
  let v = E4_cas.verify ro in
  let t_verify = now () -. t0 in
  row "verify" "re-read, re-hash, re-resolve" st.E4_cas.nodes t_verify "nodes/s"
    (if v = Ok () then "ok" else "FAILED");
  plain "store bytes" "the pack on disk"
    (Printf.sprintf "%.1f B/node" (float_of_int st.E4_cas.bytes /. float_of_int (max 1 st.E4_cas.nodes)))
    "-";
  E4_cas.close s;
  rm_rf dir

let bench_closure dir =
  let dir = dir ^ "-chain" in
  mkdir_p dir;
  let opts = { E4_cas.default_opts with seg_max = 1 lsl 30; index_slots = chain_len } in
  let s = E4_cas.open_rw ~dir opts in
  ignore (E4_cas.put s genesis);
  let prev = ref (E4_node.address genesis) in
  let tip = ref (E4_node.address genesis) in
  for i = 1 to chain_len do
    let payload =
      if i = 1 then v_ctor 0 [ v_nat i ]
      else v_ctor 0 [ v_nat i; v_ref (E4_kind.byte E4_kind.Export) (E4_addr.Addr.bytes !prev) ]
    in
    let n = node E4_kind.Export spec payload in
    ignore (E4_cas.put s n);
    prev := E4_node.address n;
    tip := !prev
  done;
  E4_cas.commit s;
  let ro = E4_cas.read_only s in
  let t0 = now () in
  let w = E4_cas.closure ro { E4_addr.Ref.kind = E4_kind.Export; addr = !tip } in
  let t_clo = now () -. t0 in
  row "closure" (Printf.sprintf "a chain of %d, children first" chain_len) (List.length w) t_clo
    "nodes/s"
    (if List.length w = chain_len + 1 then "ok" else "SHORT");
  let t0 = now () in
  let ok = E4_cas.word_wf w in
  let t_wf = now () -. t0 in
  row "word_wf" "Word.wf over that closure" (List.length w) t_wf "nodes/s"
    (if ok then "ok" else "FAILED");
  E4_cas.close s;
  rm_rf dir

let bench_dir dir =
  Printf.printf "\n### %s\n" dir;
  header ();
  bench_sha256 1024;
  bench_sha256 64;
  bench_size dir 1024;
  bench_size dir 64;
  bench_closure dir

let () =
  let dirs =
    match Array.to_list Sys.argv with
    | _ :: (_ :: _ as ds) -> ds
    | _ ->
      [ Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "e4bench-%d" (Unix.getpid ())) ]
  in
  Printf.printf "bench_cas: n=%d batch=%d chain=%d\n%!" n_nodes batch chain_len;
  List.iter bench_dir dirs
