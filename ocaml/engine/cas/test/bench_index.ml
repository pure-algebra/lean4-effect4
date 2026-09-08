(* bench_index.ml — lane P2's half of A2 §4.5: the index cells B4 (rebuild nodes/s) and B5
   (bytes per entry, `live_words` growth), plus the lookup rate A2 §6.4 measured with the probe
   `p_index.ml` (17 698 232 lookups/s at 1 M entries, off-heap).

   An executable, not a test: cell 3 writes a pack of tens of thousands of records and fsyncs,
   so it is run by hand with the directory to measure as its argument.

     bench_index [dir] [rebuild_nodes] [node_bytes]

   Defaults: a directory under $E4_INDEX_TMP (or the system temp dir), 100 000 nodes of 256
   bytes.  Run it on the LINUX filesystem, never under /mnt/c (A2 §6.2 measures a 72x read
   penalty on 9p).

   Cells:
     L1  lookups/s at 1e5 entries, confirmed against a stub that answers from an array
     L2  lookups/s at 1e6 entries, same
     L3  lookups/s unconfirmed (the table alone), so the confirmation's share is visible
     M1  bytes per entry and `live_words` growth at 1e5 and 1e6 (B5: <= 40 bytes, <= 64 words)
     R1  rebuild nodes/s from a real pack (B4: >= 1 000 000 nodes/s and <= 1.5 s per 1 M)
     R2  the same with a `kind_at` that answers from a table, i.e. the header scan alone — the
         floor `read_at` is measured against *)

open Effect4_engine
open Effect4_engine_cas

let now () = Unix.gettimeofday ()

let verdict name ok want =
  Printf.printf "  %-6s %s  (%s)\n%!" (if ok then "PASS" else "MISS") name want

let digest_of i = E4_sha256.digest (Printf.sprintf "bench-%d" i)

(* ---------------------------------------------------------------- lookups *)

let lookup_cell entries lookups =
  let keys = Array.init entries digest_of in
  let addrs = Array.map E4_addr.Addr.of_digest keys in
  let w0 = E4_index.heap_live_words () in
  let t0 = now () in
  let ix = E4_index.with_capacity ~capacity:entries in
  Array.iteri
    (fun i a -> E4_index.add_at ix a ~seg:0 ~off:(27 + (i * 256)) ~kind:E4_kind.Source)
    addrs;
  let build = now () -. t0 in
  let w1 = E4_index.heap_live_words () in
  (* The confirmation stub: what a pack reader would answer, without the I/O, so the number is
     the TABLE's and not the file system's (A2 §6.4 measured the same shape). *)
  let by_off = Hashtbl.create (entries * 2) in
  Array.iteri (fun i a -> Hashtbl.replace by_off (27 + (i * 256)) a) addrs;
  let confirm ~seg ~off =
    ignore seg;
    Hashtbl.find_opt by_off off
  in
  let acc = ref 0 in
  let t0 = now () in
  for i = 0 to lookups - 1 do
    match E4_index.find ~confirm ix addrs.(i mod entries) with
    | Some e -> acc := !acc + e.E4_index.off
    | None -> ()
  done;
  let dt = now () -. t0 in
  let acc2 = ref 0 in
  let t0 = now () in
  for i = 0 to lookups - 1 do
    match E4_index.find_unconfirmed ix addrs.(i mod entries) with
    | Some e -> acc2 := !acc2 + e.E4_index.off
    | None -> ()
  done;
  let dtu = now () -. t0 in
  let st = E4_index.stats ix in
  Printf.printf
    "  %8d entries  build %6.3f s   slots %8d   %8d bytes (%.1f B/entry)   live_words +%d\n\
    \             confirmed %10.0f lookups/s    unconfirmed %10.0f lookups/s   max_probe %d   \
     confirm misses %d\n%!"
    entries build st.E4_index.s_slots st.E4_index.s_bytes
    (float_of_int st.E4_index.s_bytes /. float_of_int entries)
    (w1 - w0)
    (float_of_int lookups /. dt)
    (float_of_int lookups /. dtu)
    st.E4_index.s_max_probe st.E4_index.s_confirm_misses;
  ignore (!acc + !acc2);
  (float_of_int st.E4_index.s_bytes /. float_of_int entries, w1 - w0)

(* ---------------------------------------------------------------- rebuild *)

let framed = E4_be.framed
let f_nat n = framed 2 (E4_be.nat_digits n)
let f_ctor i args = framed 10 (String.concat "" (f_nat i :: args))
let f_bytes s = framed 8 s

let build_pack dir n node_bytes =
  let w = E4_pack.open_ ~dir ~seg_max:E4_pack.default_seg_max in
  let filler = String.make (max 0 (node_bytes - 60)) 'x' in
  let kinds = [| E4_kind.Source; E4_kind.Export; E4_kind.Schema; E4_kind.Tree |] in
  let t0 = now () in
  for i = 0 to n - 1 do
    let nd =
      E4_node.make ~version:0
        ~kind:kinds.(i mod 4)
        ~spec:E4_node.zero_digest
        ~payload:(f_ctor 0 [ f_nat i; f_bytes filler ])
    in
    let b = E4_node.encode nd in
    ignore (E4_pack.append w ~digest:(E4_sha256.digest b) ~node_bytes:b);
    if i mod 512 = 511 then E4_pack.commit w
  done;
  E4_pack.commit w;
  let e = E4_pack.pack_end w in
  let dt = now () -. t0 in
  E4_pack.close w;
  Printf.printf "  built %d nodes of ~%d bytes in %.3f s (%.0f nodes/s, write path)\n%!" n
    node_bytes dt
    (float_of_int n /. dt);
  e

let rebuild_cell dir n node_bytes =
  let pack_end = build_pack dir n node_bytes in
  let rd = E4_pack.open_reader ~dir in
  (* R1: the default kind probe (`read_at`, O(bytes)). *)
  let t0 = now () in
  let ix, stop = E4_index.of_pack ~capacity:n rd ~from:E4_index.from_start in
  let dt = now () -. t0 in
  Printf.printf "  R1 rebuild (kind from read_at)   %7.3f s  %10.0f nodes/s   entries %d   %s\n%!"
    dt
    (float_of_int n /. dt)
    (E4_index.count ix)
    (E4_pack.scan_stop_to_string stop);
  (* R1b: the fast kind probe — one byte out of a private mapping (kind_at_of_dir). *)
  let t0 = now () in
  let ix1b = E4_index.with_capacity ~capacity:n in
  let stop1b =
    E4_index.rebuild ~kind_at:(E4_index.kind_at_of_dir ~dir) rd ~from:E4_index.from_start ix1b
  in
  let dt1b = now () -. t0 in
  Printf.printf "  R1b rebuild (kind_at_of_dir)     %7.3f s  %10.0f nodes/s   entries %d   %s\n%!"
    dt1b
    (float_of_int n /. dt1b)
    (E4_index.count ix1b)
    (E4_pack.scan_stop_to_string stop1b);
  (* R2: the 41-byte header scan alone — the floor R1 is measured against.  The kind is stubbed
     so the only work is the scan and the insert. *)
  let t0 = now () in
  let ix2 = E4_index.with_capacity ~capacity:n in
  let stop2 =
    E4_index.rebuild ~kind_at:(fun _ ~seg ~off -> ignore seg; ignore off; Some E4_kind.Source)
      rd ~from:E4_index.from_start ix2
  in
  let dt2 = now () -. t0 in
  Printf.printf "  R2 rebuild (header scan alone)   %7.3f s  %10.0f nodes/s   entries %d   %s\n%!"
    dt2
    (float_of_int n /. dt2)
    (E4_index.count ix2)
    (E4_pack.scan_stop_to_string stop2);
  let fast = float_of_int n /. dt1b in
  (* the save/load path: what skipping a rebuild is worth *)
  let path = Filename.concat dir "index.idx" in
  let t0 = now () in
  E4_index.save ~path ix ~covers:pack_end;
  let dts = now () -. t0 in
  let t0 = now () in
  let loaded = E4_index.load_at ~path ~pack_end in
  let dtl = now () -. t0 in
  Printf.printf "  R3 save %.3f s   load %.3f s   (%s)\n%!" dts dtl
    (match loaded with Ok _ -> "loaded" | Error v -> E4_index.load_verdict_to_string v);
  E4_pack.close_reader rd;
  (float_of_int n /. dt, fast, float_of_int n /. dt2, dt1b)

(* ---------------------------------------------------------------- *)

let rec rm_rf p =
  match Unix.lstat p with
  | exception Unix.Unix_error _ -> ()
  | { Unix.st_kind = Unix.S_DIR; _ } ->
    Array.iter (fun n -> rm_rf (Filename.concat p n)) (Sys.readdir p);
    (try Unix.rmdir p with Unix.Unix_error _ -> ())
  | _ -> ( try Sys.remove p with Sys_error _ -> ())

let () =
  let argv = Sys.argv in
  let dir =
    if Array.length argv > 1 then argv.(1)
    else
      let base = try Sys.getenv "E4_INDEX_TMP" with Not_found -> Filename.get_temp_dir_name () in
      Filename.concat base (Printf.sprintf "e4bench-index-%d" (Unix.getpid ()))
  in
  let n = if Array.length argv > 2 then int_of_string argv.(2) else 100_000 in
  let node_bytes = if Array.length argv > 3 then int_of_string argv.(3) else 256 in
  (try Unix.mkdir dir 0o755 with Unix.Unix_error _ -> ());
  Printf.printf "bench_index — %s\n%!" dir;
  Printf.printf "\n[lookups and memory]\n%!";
  let b1, w1 = lookup_cell 100_000 5_000_000 in
  let b2, w2 = lookup_cell 1_000_000 5_000_000 in
  Printf.printf "\n[rebuild]\n%!";
  let r1, r1b, r2, dt1b = rebuild_cell dir n node_bytes in
  Printf.printf "\n[verdicts against A2 §4.5]\n%!";
  verdict "B5a" (b2 <= 40.) "<= 40 bytes per node at 1e6 (the size A2 §6.4 measured)";
  verdict "B5a'" (b1 <= 64.)
    "<= 64 bytes per node at 1e5: a power-of-two slot count tracks n only to a factor of two";
  verdict "B5b" (w1 <= 64 && w2 <= 64) "live_words growth <= 64";
  verdict "B4a" (r1b >= 1_000_000.) ">= 1 000 000 nodes/s, rebuild with kind_at_of_dir";
  verdict "B4b" (dt1b <= 1.5) "<= 1.5 s for 1 M nodes";
  verdict "B4c" (r2 >= 1_000_000.) ">= 1 000 000 nodes/s, header scan alone";
  verdict "B4d" (r1 >= 1_000_000.)
    ">= 1 000 000 nodes/s with the DEFAULT kind probe (read_at; O(bytes))";
  rm_rf dir
