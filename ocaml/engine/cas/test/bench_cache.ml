(* bench_cache — lane P7's half of docs/research/2026-09-08-engine-a2-persistence.md §4.5.

   Cells:
     B10   the cache hit ratio against capacity, on a Zipf access pattern over 1e5 distinct
           nodes.  §4.5 gives B10 no acceptance number — "reported, no acceptance; the number
           is the deliverable" — so this prints the curve and the eviction counts and leaves
           the reading to the caller.  It also prints lookups/s, which IS a floor: a cache
           that is slower than the mmap read path it fronts (A2 §6.2: 890 k-946 k reads/s) is
           not a cache.
     P7-S  the subterm index build: subterms/s over ocaml/eff/goldens' 37 programs, and over a
           synthetic balanced `bind` tree of 32 767 nodes, where the constant is not dominated
           by 37 file reads.  The cost is one SHA-256 per subterm by construction (SB3), so
           the number is a SHA-256 rate with a frame walk on top and it is reported as both.
     P7-D  the dependents index: nodes/s for the incremental build (a fold over the store's
           bindings) and for the full pack scan, over a real store.

   An executable, not a test: it fsyncs and writes hundreds of MB, so it is run by hand with
   the directory to measure as its first argument (default: a fresh directory under the system
   temp directory, removed at the end).  On WSL2 it must be pointed at the LINUX filesystem —
   A2 §6.2 measures a 72x read penalty and a 146x append penalty on /mnt/c. *)

open Effect4_engine
open Effect4_engine_cas

let now = Unix.gettimeofday

let rate n dt = if dt <= 0.0 then infinity else float_of_int n /. dt

let hr () = print_endline (String.make 78 '-')

(* ============================================================ the sandbox *)

let base_dir =
  if Array.length Sys.argv > 1 then Sys.argv.(1)
  else
    let d =
      Filename.concat (Filename.get_temp_dir_name ())
        (Printf.sprintf "e4bench-cache-%d" (Unix.getpid ()))
    in
    Unix.mkdir d 0o755;
    d

let owns_dir = Array.length Sys.argv <= 1

let rec rm_rf p =
  match Unix.lstat p with
  | exception Unix.Unix_error _ -> ()
  | { Unix.st_kind = Unix.S_DIR; _ } ->
    Array.iter (fun n -> rm_rf (Filename.concat p n)) (Sys.readdir p);
    (try Unix.rmdir p with Unix.Unix_error _ -> ())
  | _ -> ( try Sys.remove p with Sys_error _ -> ())

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* ============================================================ B10: hit ratio vs capacity *)

(* A Zipf-shaped rank stream over [n] ranks: with u uniform on [0,1),
   rank = floor(exp(u * ln (n+1))) - 1 puts mass ~ 1/(k+1) on rank k, which is Zipf with
   s = 1 to within the discretisation.  It is stated, not fitted: the point of the cell is the
   SHAPE of the hit-ratio curve, and any heavy-tailed stream shows it. *)
let zipf_stream ~(n : int) ~(count : int) : int array =
  let ln = log (float_of_int (n + 1)) in
  let s = ref 0x5eed_2026 in
  let next () =
    s := ((!s * 1103515245) + 12345) land 0x3FFF_FFFF;
    float_of_int !s /. 1073741824.0
  in
  Array.init count (fun _ ->
      let k = int_of_float (exp (next () *. ln)) - 1 in
      if k < 0 then 0 else if k >= n then n - 1 else k)

let bench_hit_ratio () =
  hr ();
  print_endline "B10  cache hit ratio vs capacity — Zipf(s~1) over 1e5 nodes, 256-byte values";
  let n = 100_000 and accesses = 1_000_000 and vsize = 256 in
  let keys =
    Array.init n (fun i ->
        E4_addr.Addr.of_digest (E4_sha256.digest (Printf.sprintf "e4.bench.node.%d" i)))
  in
  let value = String.make vsize 'v' in
  let stream = zipf_stream ~n ~count:accesses in
  Printf.printf "  %-9s %-11s %-9s %-9s %-9s %-9s %s\n" "capacity" "capacity" "hits" "misses"
    "hit" "evictions" "lookups/s";
  Printf.printf "  %-9s %-11s %-9s %-9s %-9s %-9s %s\n" "(entries)" "(bytes)" "" "" "ratio" ""
    "";
  List.iter
    (fun frac ->
      let slots = max 16 (int_of_float (float_of_int n *. frac)) in
      let cap = slots * vsize in
      let c = E4_cache.Bytes_cache.create_sized ~slots ~capacity_bytes:cap in
      let t0 = now () in
      for i = 0 to accesses - 1 do
        let a = keys.(Array.unsafe_get stream i) in
        match E4_cache.Bytes_cache.find c a with
        | Some _ -> ()
        | None -> E4_cache.Bytes_cache.add c a value
      done;
      let dt = now () -. t0 in
      let s = E4_cache.Bytes_cache.stats c in
      Printf.printf "  %-9d %-11d %-9d %-9d %-9.4f %-9d %.0f\n%!" slots cap
        s.E4_cache.Bytes_cache.hits s.E4_cache.Bytes_cache.misses
        (E4_cache.Bytes_cache.hit_ratio s)
        s.E4_cache.Bytes_cache.evictions
        (rate accesses dt))
    [ 0.01; 0.02; 0.05; 0.10; 0.25; 0.50 ];
  (* the warm, all-hits rate: the floor a cache must beat to be worth having *)
  let c = E4_cache.Bytes_cache.create_sized ~slots:1024 ~capacity_bytes:(1024 * vsize) in
  for i = 0 to 1023 do
    E4_cache.Bytes_cache.add c keys.(i) value
  done;
  let t0 = now () in
  for i = 0 to accesses - 1 do
    ignore (Sys.opaque_identity (E4_cache.Bytes_cache.find c keys.(i land 1023)))
  done;
  let dt = now () -. t0 in
  Printf.printf "  warm, 100%% hits, 1024 entries: %.0f lookups/s (A2 §6.2 mmap read path: \
                 890 k-946 k reads/s)\n%!"
    (rate accesses dt)

(* ============================================================ P7-S: the subterm index *)

let eff_goldens_dir () =
  let rec ancestors d k acc =
    if k = 0 then List.rev acc else ancestors (Filename.dirname d) (k - 1) (d :: acc)
  in
  let here = Sys.getcwd () in
  let per a =
    [ Filename.concat a (Filename.concat "eff" "goldens");
      Filename.concat a (Filename.concat "ocaml" (Filename.concat "eff" "goldens")) ]
  in
  List.find_opt
    (fun d -> try Sys.is_directory d with Sys_error _ -> false)
    ((try [ Sys.getenv "E4_EFF_GOLDENS" ] with Not_found -> [])
    @ List.concat (List.map per (ancestors here 9 [])))

let rec bind_tree (d : int) : Eff_types.eff =
  if d = 0 then Eff_types.Eff_succeed (Eff_types.Term_lit (Eff_types.Lit_nat 1))
  else Eff_types.Eff_bind (bind_tree (d - 1), bind_tree (d - 1))

let bench_subterm () =
  hr ();
  print_endline "P7-S  the subterm index build (A2 §4.5 beside B9-B11)";
  (match eff_goldens_dir () with
  | None -> print_endline "  ocaml/eff/goldens not found — the corpus half is skipped"
  | Some dir ->
    let files =
      List.filter (fun f -> Filename.check_suffix f ".bin") (Array.to_list (Sys.readdir dir))
    in
    let programs = List.filter_map (fun f -> Some (read_file (Filename.concat dir f))) files in
    let total_bytes = List.fold_left (fun a s -> a + String.length s) 0 programs in
    (* one pass to learn the size, then the timed passes *)
    let subterms =
      List.fold_left
        (fun a s ->
          match E4_subterm.of_program_opt s with None -> a | Some ix -> a + E4_subterm.count ix)
        0 programs
    in
    let reps = 200 in
    let t0 = now () in
    for _ = 1 to reps do
      List.iter (fun s -> ignore (Sys.opaque_identity (E4_subterm.of_program_opt s))) programs
    done;
    let dt = now () -. t0 in
    Printf.printf
      "  goldens: %d programs, %d bytes, %d subterms; %d passes in %.3f s\n\
      \           %.0f subterms/s, %.0f programs/s, %.1f MB/s\n%!"
      (List.length programs) total_bytes subterms reps dt
      (rate (subterms * reps) dt)
      (rate (List.length programs * reps) dt)
      (float_of_int (total_bytes * reps) /. dt /. 1_048_576.));
  (* the synthetic tree: 2^15 - 1 = 32 767 nodes, so the constant is the walk and not the
     37 file reads *)
  let depth = 14 in
  let prog = bind_tree depth in
  let bytes = Eff_wire.encode_program prog in
  let ix0 = E4_subterm.of_program bytes in
  let nodes = E4_subterm.count ix0 in
  let reps = 20 in
  let t0 = now () in
  for _ = 1 to reps do
    ignore (Sys.opaque_identity (E4_subterm.of_program bytes))
  done;
  let dt = now () -. t0 in
  Printf.printf
    "  balanced bind tree, depth %d: %d subterms, %d bytes; %d builds in %.3f s\n\
    \           %.0f subterms/s, %.1f MB/s\n%!"
    depth nodes (String.length bytes) reps dt
    (rate (nodes * reps) dt)
    (float_of_int (String.length bytes * reps) /. dt /. 1_048_576.);
  (* the SHA-256 half, on its own, so the frame walk's share is visible *)
  let t1 = now () in
  for _ = 1 to reps do
    let ix = E4_subterm.of_program bytes in
    ignore (Sys.opaque_identity (E4_subterm.count ix))
  done;
  ignore (now () -. t1);
  let slices =
    List.map (fun (e : E4_subterm.entry) -> E4_subterm.slice bytes e) (E4_subterm.entries ix0)
  in
  let t2 = now () in
  for _ = 1 to reps do
    List.iter (fun s -> ignore (Sys.opaque_identity (E4_sha256.digest s))) slices
  done;
  let dt2 = now () -. t2 in
  Printf.printf "           of which SHA-256 of every slice alone: %.3f s (%.0f digests/s)\n%!"
    dt2
    (rate (nodes * reps) dt2)

(* ============================================================ P7-D: the dependents index *)

let v_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let v_bytes b = E4_be.framed Eff_frame.tag_bytes b
let v_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (v_nat i :: args))
let v_ref k d = E4_be.framed Eff_frame.tag_ref (String.make 1 (Char.chr k) ^ d)
let node kind spec payload = { E4_node.version = 0; kind; spec; payload }

let bench_deps () =
  hr ();
  print_endline "P7-D  the dependents index: incremental build and full pack scan";
  List.iter
    (fun n ->
      let dir = Filename.concat base_dir (Printf.sprintf "deps%d" n) in
      rm_rf dir;
      Unix.mkdir dir 0o755;
      let st = E4_cas.open_rw ~dir { E4_cas.default_opts with index_slots = 1 lsl 16 } in
      let g = node E4_kind.Schema E4_node.zero_digest (v_ctor 0 [ v_nat 0 ]) in
      ignore (E4_cas.put st g);
      let schema = E4_addr.Addr.bytes (E4_node.address g) in
      let prev = ref E4_addr.Addr.zero in
      let t_put = now () in
      for i = 0 to n - 1 do
        let refs =
          if i = 0 then [] else [ v_ref (E4_kind.byte E4_kind.Entry) (E4_addr.Addr.bytes !prev) ]
        in
        let nd = node E4_kind.Entry schema (v_ctor 0 (v_nat i :: refs)) in
        (match E4_cas.put st nd with Ok _ -> () | Error _ -> ());
        prev := E4_node.address nd
      done;
      for j = 0 to (n / 100) - 1 do
        let cid k =
          E4_addr.Addr.bytes
            (E4_addr.Addr.of_digest (E4_sha256.digest (Printf.sprintf "cid.%d.%d" j k)))
        in
        ignore
          (E4_cas.put st
             (node E4_kind.Job schema
                (v_ctor 0 [ v_bytes (cid 0); v_bytes (cid 1); v_nat j; v_bytes (cid 2) ])))
      done;
      E4_cas.commit st;
      let dt_put = now () -. t_put in
      let ro = E4_cas.read_only st in
      let bindings = E4_cas.nodes ro in
      let total = List.length bindings in
      let t0 = now () in
      let inc = E4_deps.of_nodes bindings in
      let dt_inc = now () -. t0 in
      let t1 = now () in
      let scan, stop = E4_deps.rebuild_dir dir in
      let dt_scan = now () -. t1 in
      Printf.printf
        "  %6d nodes  put %.3f s (%.0f/s)  incremental %.3f s (%.0f nodes/s)  scan %.3f s \
         (%.0f nodes/s)\n\
        \                 %d dependees, %d edges, agree=%b, stop=%s\n%!"
        total dt_put (rate total dt_put) dt_inc (rate total dt_inc) dt_scan (rate total dt_scan)
        (E4_deps.cardinal scan) (E4_deps.edges scan)
        (E4_deps.equal inc scan)
        (E4_pack.scan_stop_to_string stop);
      E4_cas.close st;
      rm_rf dir)
    [ 1_000; 10_000; 50_000 ]

(* ============================================================ main *)

let () =
  Printf.printf "bench_cache — lane P7 (A2 §4.5 B10, plus the subterm and dependents cells)\n";
  Printf.printf "store directory: %s\n%!" base_dir;
  bench_hit_ratio ();
  bench_subterm ();
  bench_deps ();
  hr ();
  if owns_dir then rm_rf base_dir
