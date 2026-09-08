(* bench_checkpoint.ml — lane P6: A2 §4.4's structural-sharing table and bench cell B7.

   What it measures.

     A  The chunking accounting on a SYNTHETIC 64 MB image of 65 536 cells, under the three
        mutations A2 §4.4 names — E1 one cell rewritten in place, E2 one cell appended, E3 one
        cell grows by 7 bytes: the shapes a `Ref.set`, an allocation and a `Deferred` gaining
        a waiter make.  For each plan (whole blob, fixed 4 KB, content-defined at five
        averages) it reports the new bytes the SECOND checkpoint must write given the first is
        stored, the manifest cost flat and with the two-level lever, and the total.  This is
        the table A2 §6.3's `p_share` probe produced, recomputed here through the module that
        actually ships, with SHA-256 addresses instead of the probe's FNV-1a.
     B  B7 through the real store when a directory is given: two consecutive checkpoints of the
        64 MB image with the E1 edit between them, chunking on and off, reporting the
        cumulative pack growth and the ratio.  Acceptance: <= 300 KB new bytes per checkpoint
        and >= 200x against chunking off.
     C  The chunker's throughput: MB/s of `cut` at the default parameters.

   An executable, not a test: A allocates a 64 MB string and B writes and fsyncs hundreds of
   megabytes, so it is run by hand.

     dune exec engine/cas/test/bench_checkpoint.exe            -- A and C only
     dune exec engine/cas/test/bench_checkpoint.exe -- /tmp/b7 -- A, B and C *)

open Effect4_engine_cas
open Effect4_engine
module Ch = E4_chunk
module Ck = E4_checkpoint

let ref_bytes = 42 (* a framed ref: tag + be64 + kind byte + 32 *)

(* ============================================================ the synthetic image *)

(* `cells` records laid back to back — A2 §6.3's p_share shape. *)
let image ~cells ~cell =
  let b = Buffer.create (cells * cell) in
  for i = 0 to cells - 1 do
    Buffer.add_string b (Printf.sprintf "cell:%08d:" i);
    for j = 0 to cell - 16 do
      Buffer.add_char b (Char.chr (33 + (((i * 31) + (j * 17)) mod 90)))
    done;
    Buffer.add_char b '\n'
  done;
  Buffer.contents b

let e1 s cell k =
  (* one cell rewritten in place, same length *)
  let b = Bytes.of_string s in
  for j = 0 to 31 do
    Bytes.set b ((k * cell) + 20 + j) 'Z'
  done;
  Bytes.to_string b

let e2 s cell = s ^ String.make cell 'A'

let e3 s cell k =
  let at = (k * cell) + 40 in
  String.sub s 0 at ^ "0123456" ^ String.sub s at (String.length s - at)

(* ============================================================ A: the accounting *)

let digests p s =
  List.map (fun (o, l) -> E4_sha256.digest_sub s o l) (Ch.cut p s)

let fixed_digests size s =
  let n = String.length s in
  let rec go off acc =
    if off >= n then List.rev acc
    else go (off + size) (E4_sha256.digest_sub s off (min size (n - off)) :: acc)
  in
  go 0 []

let table_of ds =
  let h = Hashtbl.create (List.length ds * 2) in
  List.iter (fun d -> Hashtbl.replace h d ()) ds;
  h

(* the new bytes the second image must write, given the first is stored *)
let new_bytes ~cut1 ~cut2 =
  let tbl = table_of (fst cut1) in
  List.fold_left2
    (fun acc d (_, l) -> if Hashtbl.mem tbl d then acc else acc + l)
    0 (fst cut2) (snd cut2)

let cut_pair p s = (digests p s, Ch.cut p s)
let fixed_pair size s =
  let n = String.length s in
  let rec go off acc = if off >= n then List.rev acc else go (off + size) ((off, min size (n - off)) :: acc) in
  (fixed_digests size s, go 0 [])

(* the manifest cost: flat, and under the two-level lever (CH7) *)
let manifest_cost ds1 ds2 =
  let flat = List.length ds2 * ref_bytes in
  let g = Ch.groups_default in
  let mk ds =
    let refs = List.map (fun d -> E4_addr.Ref.make E4_kind.Chunk (E4_addr.Addr.of_digest d)) ds in
    Ch.group_cut g refs
  in
  let g1 = mk ds1 and g2 = mk ds2 in
  let tbl = Hashtbl.create 64 in
  List.iter (fun x -> Hashtbl.replace tbl (List.map (fun (r : E4_addr.Ref.t) -> E4_addr.Addr.bytes r.E4_addr.Ref.addr) x) ()) g1;
  let rewritten =
    List.fold_left
      (fun acc x ->
        let key = List.map (fun (r : E4_addr.Ref.t) -> E4_addr.Addr.bytes r.E4_addr.Ref.addr) x in
        if Hashtbl.mem tbl key then acc else acc + (List.length x * ref_bytes))
      0 g2
  in
  let root = List.length g2 * ref_bytes in
  (flat, rewritten + root)

let section_a () =
  let cell = 1024 in
  let cells = 65536 in
  Printf.printf "== A. structural sharing, %d-cell image of %d B cells (%.1f MB) ==\n%!" cells cell
    (float_of_int (cells * cell) /. 1_048_576.);
  let s = image ~cells ~cell in
  let n = String.length s in
  let muts =
    [ ("E1 one cell rewritten in place", e1 s cell 30000);
      ("E2 one cell appended", e2 s cell);
      ("E3 one cell grows by 7 bytes", e3 s cell 30000) ]
  in
  let plans =
    ("W whole blob", `Whole)
    :: ("F fixed 4 KB", `Fixed 4096)
    :: List.map (fun a -> (Printf.sprintf "C CDC avg %d KB" (a / 1024), `Cdc a)) [ 4096; 16384; 32768; 65536; 262144 ]
  in
  List.iter
    (fun (mname, s2) ->
      Printf.printf "\n  %s\n" mname;
      Printf.printf "  %-22s %14s %14s %14s %14s\n" "plan" "new chunk B" "manifest B" "2-level B" "total B";
      List.iter
        (fun (pname, plan) ->
          match plan with
          | `Whole ->
            Printf.printf "  %-22s %14d %14s %14s %14d\n" pname (String.length s2) "-" "-"
              (String.length s2)
          | `Fixed size ->
            let c1 = fixed_pair size s and c2 = fixed_pair size s2 in
            let b = new_bytes ~cut1:c1 ~cut2:c2 in
            let flat, two = manifest_cost (fst c1) (fst c2) in
            Printf.printf "  %-22s %14d %14d %14d %14d\n" pname b flat two (b + two)
          | `Cdc a ->
            let p = { Ch.avg = a; min = a / 4; max = a * 4 } in
            let c1 = cut_pair p s and c2 = cut_pair p s2 in
            let b = new_bytes ~cut1:c1 ~cut2:c2 in
            let flat, two = manifest_cost (fst c1) (fst c2) in
            Printf.printf "  %-22s %14d %14d %14d %14d\n" pname b flat two (b + two))
        plans)
    muts;
  Printf.printf "\n  (image %d B; a framed ref is %d B; the two-level column is CH7's lever)\n%!" n
    ref_bytes;
  s

(* ============================================================ B: B7 through the store *)

let f_nat i = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits i)
let f_bytes b = E4_be.framed Eff_frame.tag_bytes b
let f_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (f_nat i :: args))

let section_b dir s =
  Printf.printf "\n== B. bench cell B7: two consecutive checkpoints through the store ==\n%!";
  let cell = 1024 in
  let s2 = e1 s cell 30000 in
  let run ~chunk sub =
    let d = Filename.concat dir sub in
    (try Unix.mkdir d 0o755 with Unix.Unix_error _ -> ());
    let st = E4_cas.open_rw ~dir:d E4_cas.default_opts in
    let spec = Ck.ensure_schema st in
    let job =
      match
        E4_cas.put st
          (E4_node.make ~version:0 ~kind:E4_kind.Job ~spec:(E4_addr.Addr.bytes spec)
             ~payload:(f_ctor 0 [ f_bytes "b7" ]))
      with
      | Ok (_, a) -> a
      | Error e -> failwith (E4_cas.admission_word e)
    in
    E4_cas.commit st;
    let base = (E4_cas.stats (E4_cas.read_only st)).E4_cas.bytes in
    let threshold = if chunk then 0 else max_int in
    let t0 = Unix.gettimeofday () in
    let a1 =
      match Ck.write st ~job ~position:0 ~machine_image:s ~prev:None ~threshold ~pin:false () with
      | Ok a -> a
      | Error e -> failwith (Ck.write_error_word e)
    in
    let after1 = (E4_cas.stats (E4_cas.read_only st)).E4_cas.bytes in
    let t1 = Unix.gettimeofday () in
    let w2 =
      match
        Ck.write_counted st ~job ~position:1 ~machine_image:s2 ~prev:(Some a1) ~threshold
          ~pin:false ()
      with
      | Ok w -> w
      | Error e -> failwith (Ck.write_error_word e)
    in
    let after2 = (E4_cas.stats (E4_cas.read_only st)).E4_cas.bytes in
    let t2 = Unix.gettimeofday () in
    let ok =
      match Ck.read (E4_cas.read_only st) w2.Ck.addr with Ok (_, i) -> i = s2 | Error _ -> false
    in
    E4_cas.close st;
    (after1 - base, after2 - after1, t1 -. t0, t2 -. t1, w2, ok)
  in
  let on1, on2, ont1, ont2, w, ok_on = run ~chunk:true "on" in
  let off1, off2, offt1, offt2, _, ok_off = run ~chunk:false "off" in
  Printf.printf "  %-14s %14s %14s %10s %10s\n" "plan" "1st ckpt B" "2nd ckpt B" "1st s" "2nd s";
  Printf.printf "  %-14s %14d %14d %10.3f %10.3f\n" "chunking on" on1 on2 ont1 ont2;
  Printf.printf "  %-14s %14d %14d %10.3f %10.3f\n" "chunking off" off1 off2 offt1 offt2;
  Printf.printf "  2nd checkpoint: %d chunks cut, %d fresh, %d duplicate; %d manifest nodes, %d fresh\n"
    w.Ck.chunks_cut w.Ck.chunks_fresh w.Ck.chunks_dup w.Ck.manifest_nodes w.Ck.manifest_fresh;
  let ratio = float_of_int off2 /. float_of_int (max 1 on2) in
  Printf.printf "  ratio off/on on the second checkpoint: %.1fx\n" ratio;
  Printf.printf "  B7 <= 300 KB per checkpoint : %s (%d B)\n"
    (if on2 <= 300 * 1024 then "PASS" else "FAIL")
    on2;
  Printf.printf "  B7 >= 200x against off      : %s (%.1fx)\n"
    (if ratio >= 200. then "PASS" else "FAIL")
    ratio;
  Printf.printf "  both stores read the second checkpoint back: %b / %b\n%!" ok_on ok_off

(* ============================================================ C: throughput *)

let section_c s =
  Printf.printf "\n== C. the chunker's throughput ==\n%!";
  let n = String.length s in
  List.iter
    (fun p ->
      let t0 = Unix.gettimeofday () in
      let c = Ch.cut p s in
      let dt = Unix.gettimeofday () -. t0 in
      Printf.printf "  avg %6d B: %6d chunks, %.3f s, %8.1f MB/s\n%!" p.Ch.avg (List.length c) dt
        (float_of_int n /. 1_048_576. /. dt))
    [ { Ch.avg = 4096; min = 1024; max = 16384 };
      Ch.default;
      { Ch.avg = 65536; min = 16384; max = 262144 } ];
  let t0 = Unix.gettimeofday () in
  ignore (E4_sha256.digest s);
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf "  sha256 of the same image: %.3f s, %.1f MB/s (the cost the cut sits beside)\n%!"
    dt
    (float_of_int n /. 1_048_576. /. dt)

let () =
  let s = section_a () in
  (match Sys.argv with
  | [| _; dir |] -> section_b dir s
  | _ -> Printf.printf "\n(section B skipped: pass a directory to run it through the store)\n%!");
  section_c s
