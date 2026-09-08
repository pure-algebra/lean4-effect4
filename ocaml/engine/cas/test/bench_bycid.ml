(* bench_bycid — lane W, item 4: what `E4_cas.by_cid` and `E4_cas.pin_all` cost.

   Lane P6's finding F6 (2026-09-08-engine-lane-p6-delivery.md §4): `by_cid` was a full scan
   that re-hashed every resident payload (`e4_cas.ml`, its own D5), so `pin_all` at every
   checkpoint was O(store payload bytes) PER CALL and unusable on a store holding thousands of
   chunk nodes.  A2 §2.4 lists `byCid` as "a cache with a rebuild"; lane W built the cache.

   Cells, on a store of `n` nodes (the same shape as bench_cache's P7-D cell: a chain of
   `entry` nodes under one schema, plus `job` nodes carrying `Cid` fields):
     W4a  the FIRST `by_cid` on a fresh view -- the cold cost, one payload hash per node.
     W4b  1 000 further `by_cid` calls on the warm view -- the number F6 is about.
     W4c  `pin_all` with 8 Cids, repeated -- what a checkpointing publisher pays.
     W4d  the answers, so the cell cannot pass by answering nothing.

   An executable, not a test: it writes and fsyncs, so it is run by hand with the directory to
   measure as its first argument (default: a fresh directory under the system temp directory,
   removed at the end).  On WSL2 point it at the LINUX filesystem — A2 §6.2 measures a 146x
   append penalty on /mnt/c. *)

open Effect4_engine
open Effect4_engine_cas

let now = Unix.gettimeofday
let rate n dt = if dt <= 0.0 then infinity else float_of_int n /. dt
let hr () = print_endline (String.make 78 '-')

let base_dir =
  if Array.length Sys.argv > 1 then Sys.argv.(1)
  else
    let d =
      Filename.concat (Filename.get_temp_dir_name ())
        (Printf.sprintf "e4bench-bycid-%d" (Unix.getpid ()))
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

(* the frame builders bench_cache uses, so the store shape is the same one P7-D measured *)
let v_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let v_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (v_nat i :: args))
let v_ref k d = E4_be.framed Eff_frame.tag_ref (String.make 1 (Char.chr k) ^ d)
let node kind spec payload = { E4_node.version = 0; kind; spec; payload }

let build ~dir ~n =
  let st = E4_cas.open_rw ~dir { E4_cas.default_opts with index_slots = 1 lsl 16 } in
  let g = node E4_kind.Schema E4_node.zero_digest (v_ctor 0 [ v_nat 0 ]) in
  ignore (E4_cas.put st g);
  let schema = E4_addr.Addr.bytes (E4_node.address g) in
  let prev = ref E4_addr.Addr.zero in
  let payloads = ref [] in
  for i = 0 to n - 1 do
    let refs =
      if i = 0 then [] else [ v_ref (E4_kind.byte E4_kind.Entry) (E4_addr.Addr.bytes !prev) ]
    in
    let nd = node E4_kind.Entry schema (v_ctor 0 (v_nat i :: refs)) in
    (match E4_cas.put st nd with Ok _ -> () | Error _ -> ());
    if i mod (max 1 (n / 8)) = 0 then payloads := nd.E4_node.payload :: !payloads;
    prev := E4_node.address nd
  done;
  E4_cas.commit st;
  (st, List.rev !payloads)

let cell n =
  let dir = Filename.concat base_dir (Printf.sprintf "bycid%d" n) in
  rm_rf dir;
  Unix.mkdir dir 0o755;
  let st, payloads = build ~dir ~n in
  let cids = List.map (fun p -> E4_addr.Addr.of_digest (E4_sha256.digest p)) payloads in
  let some_cid = List.hd cids in
  (* W4a: the cold call, on a view that has never answered a by_cid *)
  let ro = E4_cas.open_ro ~dir in
  let t0 = now () in
  let cold = E4_cas.by_cid ro E4_kind.Entry some_cid in
  let dt_cold = now () -. t0 in
  (* W4b: 1 000 warm calls, cycling through the cids so no single hash-table slot is hot *)
  let k = 1000 in
  let arr = Array.of_list cids in
  let found = ref 0 in
  let t1 = now () in
  for i = 0 to k - 1 do
    match E4_cas.by_cid ro E4_kind.Entry arr.(i mod Array.length arr) with
    | [] -> ()
    | _ :: _ -> incr found
  done;
  let dt_warm = now () -. t1 in
  (* W4c: pin_all over the 8 Cids, repeated; each call also commits and moves a root *)
  (* `job` only names the roots (`runs/<job hex>/pin/<cid hex>`, E4_cas D8); it is not
     resolved, so any address will do here.  The FIRST publish is timed on its own: this is
     the writer's own view and it has answered no `by_cid` yet, so round 1 pays the whole
     index build and rounds 2.. pay only the root writes. *)
  let rounds = 20 in
  let ok = ref 0 in
  let pin1 () = match E4_cas.pin_all st ~job:E4_addr.Addr.zero cids with Ok () -> incr ok | Error _ -> () in
  let t2 = now () in
  pin1 ();
  let dt_pin1 = now () -. t2 in
  let t3 = now () in
  for _ = 2 to rounds do
    pin1 ()
  done;
  let dt_pin = now () -. t3 in
  Printf.printf
    "  %6d nodes  W4a cold by_cid %8.3f ms  W4b %d warm calls %8.3f ms (%12.0f calls/s, \
     %8.1f us each)\n\
    \                 W4c pin_all (%d cids each): 1st %8.3f ms, next %d %8.3f ms (%8.3f ms \
     per publish)\n\
    \                 W4d answers: cold %d filing(s), %d of %d warm calls found one, %d \
     publishes ok\n%!"
    n (dt_cold *. 1000.) k (dt_warm *. 1000.) (rate k dt_warm)
    (dt_warm *. 1e6 /. float_of_int k)
    (List.length cids) (dt_pin1 *. 1000.) (rounds - 1) (dt_pin *. 1000.)
    (dt_pin *. 1000. /. float_of_int (rounds - 1))
    (List.length cold) !found k !ok;
  E4_cas.close_ro ro;
  E4_cas.close st;
  rm_rf dir

let () =
  print_endline "bench_bycid — lane W item 4 (E4_cas.by_cid / pin_all; P6 finding F6)";
  Printf.printf "store directory: %s\n%!" base_dir;
  hr ();
  List.iter cell [ 1_000; 10_000; 50_000 ];
  hr ();
  if owns_dir then rm_rf base_dir
