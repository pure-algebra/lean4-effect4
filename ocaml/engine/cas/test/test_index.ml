(* test_index.ml — lane P2's checks: the digest index, the two derived indexes and the per-kind
   field table (2026-09-08).

   What it checks, and against what:
     A*  the slot arithmetic of e4_index.mli's layout (D1): pack/unpack round trips over the
         whole legal range of (seg, off, kind), the refusals past `max_seg` / `max_off`, and the
         fact that no occupied slot can encode as 0 (Kind.byte_pos, Kind.lean:137).
     B*  build and look up (IX1) over a real pack: every staged record is found at the offset
         `append` returned, and every non-resident digest answers None.
     C*  the confirmation, and a HAND-FORCED 62-bit prefix collision (L-IDX-1): two digests
         whose leading 62 bits are equal and whose tails differ are written as two records; each
         `find` returns its own record, the confirmation counter shows the collision was paid
         for with a read, and `find_unconfirmed` — which does not confirm — is shown answering
         the WRONG one, so the test that L-IDX-1 exists is red if the confirmation is removed.
     G*  growth (IX4): the load factor never passes 0.6, growth doubles, and nothing is lost.
     H*  off-heap (IX3): `live_words` grows by at most 64 over a 200 000-entry build.
     F*  the file (IX6): save/load round trip; a flipped body byte, a flipped head byte, a
         truncated file, a wrong version, a `covers` that is not the pack end — each is its own
         verdict, and `open_index` rebuilds in every case and agrees with the loaded table.
     R*  rebuild (IX2): on a 10 000-node pack, `rebuild` equals the incrementally built index
         entry for entry, and answers None for a digest that is not in the pack.
     K*  the by-kind index: `of_index` and `rebuild` agree with each other and with a
         brute-force list, and the kinds are in byte order.
     D*  the dependents index (IX8, IX9): agrees with a brute-force recomputation of
         `Deps.of_node` over every node; is persistent (an old value is unchanged by a later
         `add`); and `find` of a Cid is empty when the table has no row for that kind — the
         negative that shows the Cid graph is table-driven and not guessed.
     S*  the shape table: every row of `E4_kind.all` is present and in byte order (SH2), and
         each row has a POSITIVE case (a payload built to the row's shape, whose cids/refs/
         stamps come back exactly) and a NEGATIVE case (a payload that violates the row, which
         `_checked` refuses and the lenient form drops).  For a `Shared` / `Unused` /
         `Tombstoned` row the positive case is "no field is claimed" and the negative is "a
         payload stuffed with 32-byte bytes frames still yields no Cid".
     P*  the path language (SH5, SH6): `Each` over a list, a path that does not resolve, and the
         proof that the walk never descends into a tag-8 `bytes` frame that contains frames.

   Everything runs in a fresh directory under $E4_INDEX_TMP (default: the system temp dir),
   removed at the end.  Exit code 0 iff every check passed. *)

open Effect4_engine
open Effect4_engine_cas

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n%!" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n%!")

(* A fixed linear congruential generator: the run is reproducible. *)
let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n

(* ============================================================ the sandbox *)

let root =
  let base = try Sys.getenv "E4_INDEX_TMP" with Not_found -> Filename.get_temp_dir_name () in
  let d =
    Filename.concat base
      (Printf.sprintf "e4index-%d-%d" (Unix.getpid ()) (int_of_float (Unix.time ())))
  in
  (try Unix.mkdir base 0o755 with Unix.Unix_error _ -> ());
  Unix.mkdir d 0o755;
  d

let counter = ref 0

let fresh_dir () =
  incr counter;
  let d = Filename.concat root (Printf.sprintf "s%03d" !counter) in
  Unix.mkdir d 0o755;
  d

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

let poke path pos byte =
  let fd = Unix.openfile path [ Unix.O_WRONLY ] 0o600 in
  ignore (Unix.lseek fd pos Unix.SEEK_SET);
  ignore (Unix.write fd (Bytes.make 1 (Char.chr byte)) 0 1);
  Unix.close fd

let flip path pos =
  let s = read_file path in
  poke path pos (Char.code s.[pos] lxor 0x01)

let truncate_file path n =
  let fd = Unix.openfile path [ Unix.O_WRONLY ] 0o600 in
  Unix.ftruncate fd n;
  Unix.close fd

(* ============================================================ payload helpers *)

let framed = E4_be.framed
let f_nat n = framed 2 (E4_be.nat_digits n)
let f_bytes s = framed 8 s
let f_string s = framed 3 s
let f_list xs = framed 4 (String.concat "" xs)
let f_pair a b = framed 5 (a ^ b)
let f_some x = framed 7 x
let f_none = framed 6 ""
let f_ctor i args = framed 10 (String.concat "" (f_nat i :: args))
let f_ref kb d = framed 11 (String.make 1 (Char.chr kb) ^ d)
let f_handle kb n = framed 12 (String.make 1 (Char.chr kb) ^ E4_be.nat_digits n)

let d32 tag = String.init 32 (fun i -> Char.chr ((tag + (i * 7)) land 0xff))
let addr32 tag = E4_addr.Addr.of_digest (d32 tag)

(* A node of a kind with a given payload. *)
let node kind payload =
  E4_node.make ~version:0 ~kind ~spec:E4_node.zero_digest ~payload

(* ============================================================ a populated pack *)

type built = {
  b_dir : string;
  b_places : (E4_addr.Addr.t * (E4_index.seg * E4_index.off) * E4_kind.t) list;
  b_end : E4_pack.seg * E4_pack.off;
}

(* Stage [n] nodes whose kinds cycle over the Lean kinds, one commit per 64. *)
let build_pack ?(seg_max = E4_pack.default_seg_max) n =
  let dir = fresh_dir () in
  let w = E4_pack.open_ ~dir ~seg_max in
  let kinds = [| E4_kind.Source; E4_kind.Export; E4_kind.Schema; E4_kind.Tree;
                 E4_kind.Annotation; E4_kind.Component |] in
  let places = ref [] in
  for i = 0 to n - 1 do
    let kind = kinds.(i mod Array.length kinds) in
    let payload = f_ctor 0 [ f_nat i; f_bytes (d32 (i land 0xff)) ] in
    let nd = node kind payload in
    let b = E4_node.encode nd in
    let a = E4_sha256.digest b in
    let seg, off = E4_pack.append w ~digest:a ~node_bytes:b in
    places := (E4_addr.Addr.of_digest a, (seg, off), kind) :: !places;
    if i mod 64 = 63 then E4_pack.commit w
  done;
  E4_pack.commit w;
  let e = E4_pack.pack_end w in
  E4_pack.close w;
  { b_dir = dir; b_places = List.rev !places; b_end = e }

(* ============================================================ A. the slot *)

let test_slot () =
  let ok = ref true in
  let ks = E4_kind.all in
  List.iter
    (fun k ->
      List.iter
        (fun (seg, off) ->
          let ix = E4_index.create ~slots:64 in
          let a = addr32 (E4_kind.byte k + off) in
          E4_index.add_at ix a ~seg ~off ~kind:k;
          match E4_index.find_unconfirmed ix a with
          | Some e ->
            if e.E4_index.seg <> seg || e.E4_index.off <> off || not (E4_kind.equal e.E4_index.kind k)
            then ok := false
          | None -> ok := false)
        [ (0, 27); (1, 1000); (E4_index.max_seg, E4_index.max_off); (7, 0) ])
    ks;
  check "A1 (seg, off, kind) round trips through a slot over the whole legal range" !ok;
  let refused lo =
    let ix = E4_index.create ~slots:16 in
    match lo with
    | seg, off -> (
      try
        E4_index.add_at ix (addr32 1) ~seg ~off ~kind:E4_kind.Source;
        false
      with Invalid_argument _ -> true)
  in
  check "A2 a segment past max_seg or an offset past max_off is Invalid_argument, never a wrap"
    (refused (E4_index.max_seg + 1, 0)
    && refused (0, E4_index.max_off + 1)
    && refused (0, -1));
  (* No occupied slot can be 0: every kind byte is at least 1 (Kind.byte_pos). *)
  check "A3 every kind byte is >= 1, so an occupied slot is never the empty marker"
    (List.for_all (fun k -> E4_kind.byte k >= 1) E4_kind.all);
  check "A4 the slot is 16 bytes and `bytes` is slots * 16"
    (E4_index.slot_bytes = 16
    && E4_index.bytes (E4_index.create ~slots:1024) = 1024 * 16)

(* ============================================================ B. find over a pack *)

let test_find () =
  let b = build_pack 2000 in
  let rd = E4_pack.open_reader ~dir:b.b_dir in
  let ix = E4_index.with_capacity ~capacity:4096 in
  List.iter (fun (a, (s, o), k) -> E4_index.add_at ix a ~seg:s ~off:o ~kind:k) b.b_places;
  let ok = ref true in
  List.iter
    (fun (a, (s, o), k) ->
      match E4_index.find_in rd ix a with
      | Some e ->
        if e.E4_index.seg <> s || e.E4_index.off <> o || not (E4_kind.equal e.E4_index.kind k) then
          ok := false
      | None -> ok := false)
    b.b_places;
  check "B1 every staged record is found at the place `append` returned" !ok;
  let absent = ref true in
  for i = 0 to 199 do
    let a = E4_addr.Addr.of_digest (E4_sha256.digest (Printf.sprintf "absent-%d" i)) in
    if E4_index.find_in rd ix a <> None then absent := false
  done;
  check "B2 a digest that is not in the pack answers None" !absent;
  check "B3 `count` is the number of distinct entries added"
    (E4_index.count ix = List.length b.b_places
    && E4_index.cardinal ix = E4_index.count ix);
  (* IX7: re-adding the same (address, entry) pair changes nothing. *)
  let before = E4_index.count ix in
  List.iter (fun (a, (s, o), k) -> E4_index.add_at ix a ~seg:s ~off:o ~kind:k) b.b_places;
  check "B4 `add` of an (address, entry) pair already present is idempotent"
    (E4_index.count ix = before);
  let fl = E4_index.find_full rd ix (let a, _, _ = List.hd b.b_places in a) in
  check "B5 `find_full` returns the record's node_len beside the entry"
    (match fl with Some (_, len) -> len > 0 | None -> false);
  E4_pack.close_reader rd;
  b

(* ============================================================ C. the prefix collision *)

(* Two digests whose leading 62 bits agree.  `prefix63` is the leading eight bytes with the top
   TWO bits cleared (e4_addr.mli D1), so copying the first eight bytes and changing the ninth is
   a collision by construction; changing the top two bits of byte 0 is a second, sharper one. *)
let test_collision () =
  let a_bytes = String.init 32 (fun i -> Char.chr ((i * 11) land 0xff)) in
  let b_bytes = String.mapi (fun i c -> if i < 8 then c else Char.chr (Char.code c lxor 0xff)) a_bytes in
  (* `prefix63` is bytes 0..7 with the LOW two bits of byte 7 dropped (e4_addr.ml:30-34), so
     flipping those two bits is a collision that differs inside the key's own eight bytes. *)
  let c_bytes =
    String.mapi (fun i c -> if i = 7 then Char.chr (Char.code c lxor 0x03) else c) a_bytes
  in
  let a = E4_addr.Addr.of_digest a_bytes
  and bb = E4_addr.Addr.of_digest b_bytes
  and c = E4_addr.Addr.of_digest c_bytes in
  check "C1 the three hand-made digests share a 62-bit prefix and differ"
    (E4_addr.Addr.prefix63 a = E4_addr.Addr.prefix63 bb
    && E4_addr.Addr.prefix63 a = E4_addr.Addr.prefix63 c
    && (not (E4_addr.Addr.equal a bb))
    && not (E4_addr.Addr.equal a c));
  (* Three records carrying those digests.  `append` does not re-hash (e4_pack.mli D5), so the
     recorded digest is exactly what we hand it — which is what makes this test possible. *)
  let dir = fresh_dir () in
  let w = E4_pack.open_ ~dir ~seg_max:E4_pack.default_seg_max in
  let mk d k i =
    let nd = node k (f_ctor 0 [ f_nat i ]) in
    let bytes = E4_node.encode nd in
    let place = E4_pack.append w ~digest:d ~node_bytes:bytes in
    (place, k)
  in
  let pa, ka = mk a_bytes E4_kind.Source 1 in
  let pb, kb = mk b_bytes E4_kind.Tree 2 in
  let pc, kc = mk c_bytes E4_kind.Export 3 in
  E4_pack.commit w;
  E4_pack.close w;
  let rd = E4_pack.open_reader ~dir in
  let ix = E4_index.create ~slots:64 in
  E4_index.add_at ix a ~seg:(fst pa) ~off:(snd pa) ~kind:ka;
  E4_index.add_at ix bb ~seg:(fst pb) ~off:(snd pb) ~kind:kb;
  E4_index.add_at ix c ~seg:(fst pc) ~off:(snd pc) ~kind:kc;
  check "C2 three colliding entries occupy three slots" (E4_index.count ix = 3);
  E4_index.reset_counters ix;
  let got x place k =
    match E4_index.find_in rd ix x with
    | Some e -> e.E4_index.seg = fst place && e.E4_index.off = snd place && E4_kind.equal e.E4_index.kind k
    | None -> false
  in
  check "C3 a 62-bit prefix collision is resolved by confirming at the record (L-IDX-1)"
    (got a pa ka && got bb pb kb && got c pc kc);
  let st = E4_index.stats ix in
  check "C4 the collision was PAID FOR with a read: some confirmation failed and probing went on"
    (st.E4_index.s_confirms > 3 && st.E4_index.s_confirm_misses > 0);
  (* The mutation check: without the confirmation, two of the three answers are wrong. *)
  let unconfirmed_wrong =
    let bad =
      List.filter
        (fun (x, place) ->
          match E4_index.find_unconfirmed ix x with
          | Some e -> e.E4_index.seg <> fst place || e.E4_index.off <> snd place
          | None -> true)
        [ (a, pa); (bb, pb); (c, pc) ]
    in
    List.length bad >= 2
  in
  check "C5 `find_unconfirmed` answers the WRONG record for the colliders, so C3 is not vacuous"
    unconfirmed_wrong;
  (* A digest whose prefix collides with a resident but which is not in the pack at all. *)
  let ghost_bytes =
    String.mapi (fun i ch -> if i < 8 then ch else Char.chr ((Char.code ch + 7) land 0xff)) a_bytes
  in
  let ghost = E4_addr.Addr.of_digest ghost_bytes in
  check "C6 a non-resident digest that collides on the prefix still answers None"
    (E4_addr.Addr.prefix63 ghost = E4_addr.Addr.prefix63 a
    && E4_index.find_in rd ix ghost = None);
  E4_pack.close_reader rd;
  rm_rf dir

(* ============================================================ G. growth *)

let test_growth () =
  let ix = E4_index.create ~slots:16 in
  let n = 5000 in
  let addrs = Array.init n (fun i -> E4_addr.Addr.of_digest (E4_sha256.digest (string_of_int i))) in
  let ok_load = ref true in
  Array.iteri
    (fun i a ->
      E4_index.add_at ix a ~seg:(i mod 3) ~off:(27 + (i * 64)) ~kind:E4_kind.Source;
      if E4_index.load_factor ix > E4_index.max_load then ok_load := false)
    addrs;
  check "G1 the load factor never passes max_load" !ok_load;
  check "G2 growth doubled the slot count and the slot count is a power of two"
    (E4_index.slots ix land (E4_index.slots ix - 1) = 0
    && (E4_index.stats ix).E4_index.s_growths > 0);
  check "G3 nothing is lost by a growth: every entry is still there, at its place"
    (E4_index.count ix = n
    && Array.for_all
         (fun a ->
           match E4_index.find_unconfirmed ix a with Some _ -> true | None -> false)
         addrs);
  let seen = ref 0 in
  E4_index.iter ix (fun key _ -> if key >= 0 then incr seen);
  check "G4 `iter` visits every occupied slot exactly once, with a non-negative 62-bit key"
    (!seen = n)

(* ============================================================ H. off-heap *)

let test_offheap () =
  (* 2^18 entries: a power-of-two slot count can only track an arbitrary entry count to within a
     factor of two, so the bytes-per-entry figure of A2 §4.5 B5 is stated at the sizes it was
     measured at.  The structural bound is `slot_bytes / min_load` = 16 / 0.25 = 64 bytes at the
     worst n and 32 at the best; B5's 40 holds at every n whose round-up to a power of two is
     within 2.5x, which 2^18 (and A2's 1e6) both are. *)
  let n = 262_144 in
  let addrs =
    Array.init n (fun i -> E4_addr.Addr.of_digest (E4_sha256.digest (Printf.sprintf "h%d" i)))
  in
  let w0 = E4_index.heap_live_words () in
  let ix = E4_index.with_capacity ~capacity:n in
  Array.iteri (fun i a -> E4_index.add_at ix a ~seg:0 ~off:(27 + (i * 48)) ~kind:E4_kind.Source) addrs;
  let w1 = E4_index.heap_live_words () in
  ignore (Sys.opaque_identity addrs);
  let grown = w1 - w0 in
  note "H1 live_words %d -> %d (%+d) for %d entries in %d off-heap bytes (%.1f B/entry)" w0 w1
    grown n (E4_index.bytes ix)
    (float_of_int (E4_index.bytes ix) /. float_of_int n);
  check "H1 the table is off-heap: live_words grows by at most 64 words (IX3)" (grown <= 64);
  check "H2 the table is at most 40 bytes per entry at this size (A2 §4.5 B5)"
    (E4_index.bytes ix <= 40 * n);
  check
    "H3 the structural bound: never more than 64 bytes per entry above the min_slots floor"
    (List.for_all
       (fun m ->
         E4_index.bytes (E4_index.with_capacity ~capacity:m)
         <= max (E4_index.min_slots * E4_index.slot_bytes) (64 * m))
       [ 1; 17; 1000; 1024; 1025; 100_000; 200_000; 262_144; 1_000_000 ]);
  ignore (Sys.opaque_identity ix)

(* ============================================================ F. the file *)

let test_file b =
  let rd = E4_pack.open_reader ~dir:b.b_dir in
  let ix = E4_index.with_capacity ~capacity:4096 in
  List.iter (fun (a, (s, o), k) -> E4_index.add_at ix a ~seg:s ~off:o ~kind:k) b.b_places;
  let path = Filename.concat (fresh_dir ()) "000000.idx" in
  E4_index.save ~path ix ~covers:b.b_end;
  let same j =
    E4_index.count j = E4_index.count ix
    && List.for_all
         (fun (a, (s, o), k) ->
           match E4_index.find_in rd j a with
           | Some e -> e.E4_index.seg = s && e.E4_index.off = o && E4_kind.equal e.E4_index.kind k
           | None -> false)
         b.b_places
  in
  (match E4_index.load ~path with
  | Some (j, covers) ->
    check "F1 save then load round trips the table and what it covers"
      (covers = b.b_end && same j)
  | None -> check "F1 save then load round trips the table and what it covers" false);
  check "F2 `load_at` at the pack's durable end succeeds"
    (match E4_index.load_at ~path ~pack_end:b.b_end with Ok j -> same j | Error _ -> false);
  check "F3 a `covers` that is not the pack end is Stale, never loaded"
    (match E4_index.load_at ~path ~pack_end:(9, 99) with
    | Error (E4_index.Stale _) -> true
    | _ -> false);
  let size = String.length (read_file path) in
  (* a flipped body byte *)
  let p2 = Filename.concat (Filename.dirname path) "body.idx" in
  let copy dst = let s = read_file path in let oc = open_out_bin dst in output_string oc s; close_out oc in
  copy p2;
  flip p2 (E4_index.head_length + 8);
  check "F4 a flipped body byte fails the body CRC and is Bad_file"
    (match E4_index.load_at ~path:p2 ~pack_end:b.b_end with
    | Error (E4_index.Bad_file _) -> true
    | _ -> false);
  (* a flipped head byte *)
  let p3 = Filename.concat (Filename.dirname path) "head.idx" in
  copy p3;
  flip p3 20;
  check "F5 a flipped head byte fails the head CRC and is Bad_file"
    (match E4_index.load_at ~path:p3 ~pack_end:b.b_end with
    | Error (E4_index.Bad_file _) -> true
    | _ -> false);
  (* a wrong ASCII version *)
  let p4 = Filename.concat (Filename.dirname path) "ver.idx" in
  copy p4;
  poke p4 13 (Char.code '9');
  check "F6 an ASCII version this binary does not know is Bad_file, never a parse"
    (match E4_index.load_at ~path:p4 ~pack_end:b.b_end with
    | Error (E4_index.Bad_file m) -> m <> "magic"
    | _ -> false);
  (* a truncated file *)
  let p5 = Filename.concat (Filename.dirname path) "cut.idx" in
  copy p5;
  truncate_file p5 (size - 9);
  check "F7 a truncated file is Bad_file"
    (match E4_index.load_at ~path:p5 ~pack_end:b.b_end with
    | Error (E4_index.Bad_file _) -> true
    | _ -> false);
  (* the missing file *)
  check "F8 a missing file is No_file"
    (match
       E4_index.load_at ~path:(Filename.concat (Filename.dirname path) "nope.idx")
         ~pack_end:b.b_end
     with
    | Error E4_index.No_file -> true
    | _ -> false);
  (* L-IDX-0: drop the file and rebuild -- no answer changes. *)
  let all_rebuild_agree =
    List.for_all
      (fun p ->
        let j, verdict, stop = E4_index.open_index ~path:p rd ~pack_end:b.b_end in
        verdict <> E4_index.Loaded && stop <> None && same j)
      [ p2; p3; p4; p5; Filename.concat (Filename.dirname path) "nope.idx" ]
  in
  check "F9 a stale or corrupt index file is DISCARDED and rebuilt, and the rebuild agrees (IX6)"
    all_rebuild_agree;
  check "F10 `open_index` on a good file loads it and runs no scan"
    (match E4_index.open_index ~path rd ~pack_end:b.b_end with
    | j, E4_index.Loaded, None -> same j
    | _ -> false);
  E4_pack.close_reader rd

(* ============================================================ R. rebuild *)

let test_rebuild () =
  let b = build_pack 10_000 in
  let rd = E4_pack.open_reader ~dir:b.b_dir in
  let inc = E4_index.with_capacity ~capacity:16384 in
  List.iter (fun (a, (s, o), k) -> E4_index.add_at inc a ~seg:s ~off:o ~kind:k) b.b_places;
  let t0 = Unix.gettimeofday () in
  let reb, stop = E4_index.of_pack ~capacity:16384 rd ~from:E4_index.from_start in
  let dt = Unix.gettimeofday () -. t0 in
  note "R0 rebuild of a %d-node pack in %.3f s (%.0f nodes/s), stop = %s" (List.length b.b_places)
    dt
    (float_of_int (List.length b.b_places) /. dt)
    (E4_pack.scan_stop_to_string stop);
  check "R1 the scan reached the clean end of the pack" (stop = E4_pack.Eof);
  check "R2 `rebuild` has the same cardinality as the incrementally built index"
    (E4_index.count reb = E4_index.count inc);
  let agree =
    List.for_all
      (fun (a, (s, o), k) ->
        match (E4_index.find_in rd reb a, E4_index.find_in rd inc a) with
        | Some x, Some y ->
          x = y && x.E4_index.seg = s && x.E4_index.off = o && E4_kind.equal x.E4_index.kind k
        | _ -> false)
      b.b_places
  in
  check "R3 `rebuild` equals the incrementally built index on every resident digest (IX2)" agree;
  let none_extra = ref true in
  for i = 0 to 99 do
    let a = E4_addr.Addr.of_digest (E4_sha256.digest (Printf.sprintf "not-in-pack-%d" i)) in
    if E4_index.find_in rd reb a <> None then none_extra := false
  done;
  check "R4 the rebuilt index answers None for a digest that is not in the pack" !none_extra;
  (* The fast kind probe must agree with the default one, entry for entry. *)
  let fast = E4_index.with_capacity ~capacity:16384 in
  let stop2 =
    E4_index.rebuild ~kind_at:(E4_index.kind_at_of_dir ~dir:b.b_dir) rd ~from:E4_index.from_start
      fast
  in
  check "R5 `kind_at_of_dir` agrees with the default probe on every record"
    (stop2 = E4_pack.Eof
    && E4_index.count fast = E4_index.count reb
    && List.for_all
         (fun (a, _, _) ->
           match (E4_index.find_in rd fast a, E4_index.find_in rd reb a) with
           | Some x, Some y -> x = y
           | _ -> false)
         b.b_places);
  let viadir, stop3 = E4_index.of_pack ~dir:b.b_dir ~capacity:16384 rd ~from:E4_index.from_start in
  check "R6 `of_pack ~dir` selects the fast probe and gives the same index"
    (stop3 = E4_pack.Eof
    && E4_index.count viadir = E4_index.count reb
    && List.for_all
         (fun (a, _, _) ->
           match (E4_index.find_in rd viadir a, E4_index.find_in rd reb a) with
           | Some x, Some y -> x = y
           | _ -> false)
         b.b_places);
  (rd, b, reb)

(* ============================================================ K. by-kind *)

let test_by_kind rd b reb =
  let from_index = E4_index.By_kind.of_index reb in
  let from_pack, stop = E4_index.By_kind.rebuild rd ~from:E4_index.from_start in
  check "K1 the by-kind rebuild reached the clean end" (stop = E4_pack.Eof);
  let brute k =
    List.filter_map (fun (_, p, kk) -> if E4_kind.equal kk k then Some p else None) b.b_places
  in
  let cmp k =
    let s l = List.sort compare l in
    s (E4_index.By_kind.find from_index k) = s (brute k)
    && s (E4_index.By_kind.find from_pack k) = s (brute k)
  in
  check "K2 by-kind agrees with a brute-force scan, from the index and from the pack"
    (List.for_all cmp E4_kind.all);
  check "K3 `count` and `cardinal` agree with the lists"
    (List.for_all (fun k -> E4_index.By_kind.count from_index k = List.length (brute k)) E4_kind.all
    && E4_index.By_kind.cardinal from_index = List.length b.b_places);
  let ks = E4_index.By_kind.kinds from_index in
  check "K4 `kinds` lists exactly the non-empty kinds, in byte order"
    (ks = List.filter (fun k -> brute k <> []) E4_kind.all
    && List.sort compare (List.map E4_kind.byte ks) = List.map E4_kind.byte ks);
  check "K5 `find` of a kind with no entries is the empty list"
    (E4_index.By_kind.find from_index E4_kind.Job = []);
  check "K6 the by-kind index is off-heap and non-empty" (E4_index.By_kind.bytes from_index > 0)

(* ============================================================ D. dependents *)

let deps_dir () =
  (* A little store whose nodes name each other: two schema leaves, a tree naming both, an
     annotation naming the tree, and a `job` whose THREE Cid fields name the leaves.  The job is
     the only node whose dependees need the shape table (E4_shape finding R1). *)
  let dir = fresh_dir () in
  let w = E4_pack.open_ ~dir ~seg_max:E4_pack.default_seg_max in
  let put nd =
    let bts = E4_node.encode nd in
    let a = E4_sha256.digest bts in
    ignore (E4_pack.append w ~digest:a ~node_bytes:bts);
    (E4_addr.Addr.of_digest a, nd)
  in
  let leaf1 = put (node E4_kind.Schema (f_ctor 0 [ f_nat 1; f_list [] ])) in
  let leaf2 = put (node E4_kind.Schema (f_ctor 0 [ f_nat 2; f_list [] ])) in
  let tree =
    put
      (node E4_kind.Tree
         (f_ctor 0
            [ f_list
                [ f_pair (f_string "a") (f_ref 4 (E4_addr.Addr.bytes (fst leaf1)));
                  f_pair (f_string "b") (f_ref 4 (E4_addr.Addr.bytes (fst leaf2))) ] ]))
  in
  let ann =
    put
      (node E4_kind.Annotation
         (f_ctor 0
            [ f_ref 11 (E4_addr.Addr.bytes (fst tree)); f_string "hello"; f_none ]))
  in
  let job =
    put
      (node E4_kind.Job
         (f_ctor 0
            [ f_bytes (E4_addr.Addr.bytes (fst leaf1));
              f_bytes (E4_addr.Addr.bytes (fst leaf2));
              f_nat 99;
              f_bytes (E4_addr.Addr.bytes (fst tree)) ]))
  in
  E4_pack.commit w;
  E4_pack.close w;
  (dir, [ leaf1; leaf2; tree; ann; job ])

let test_deps () =
  let dir, nodes = deps_dir () in
  let rd = E4_pack.open_reader ~dir in
  let d, stop = E4_index.Deps.rebuild rd ~from:E4_index.from_start in
  check "D1 the dependents rebuild reached the clean end" (stop = E4_pack.Eof);
  (* The brute force: recompute E4_shape / E4_node by hand over the same nodes. *)
  let brute = Hashtbl.create 16 in
  List.iter
    (fun (a, nd) ->
      let by = E4_addr.Ref.make nd.E4_node.kind a in
      let refs = List.map (fun (r : E4_addr.Ref.t) -> r.E4_addr.Ref.addr) (E4_node.checked_edges nd) in
      let cids = E4_shape.cids_of E4_shape.table nd.E4_node.kind ~payload:nd.E4_node.payload in
      List.iter
        (fun dep ->
          let k = E4_addr.Addr.bytes dep in
          let cur = try Hashtbl.find brute k with Not_found -> [] in
          if not (List.exists (fun r -> E4_addr.Ref.equal r by) cur) then
            Hashtbl.replace brute k (cur @ [ by ]))
        (refs @ cids))
    nodes;
  let agree = ref true in
  Hashtbl.iter
    (fun k v ->
      let got = E4_index.Deps.find d (E4_addr.Addr.of_digest k) in
      let s = List.sort E4_addr.Ref.compare in
      if List.length got <> List.length v || not (List.for_all2 E4_addr.Ref.equal (s got) (s v))
      then agree := false)
    brute;
  let sizes = E4_index.Deps.cardinal d = Hashtbl.length brute in
  check "D2 the dependents index agrees with a brute-force scan, entry for entry (IX9)"
    (!agree && sizes);
  (* The job's three Cid fields are edges of the Cid graph only through the table. *)
  let leaf1 = fst (List.nth nodes 0) and job = fst (List.nth nodes 4) in
  let by_job = List.exists (fun (r : E4_addr.Ref.t) -> E4_addr.Addr.equal r.E4_addr.Ref.addr job)
      (E4_index.Deps.find d leaf1) in
  check "D3 a `job`'s Cid field is a dependent edge, and it is found ONLY through E4_shape"
    (by_job
    && E4_shape.cids_of E4_shape.table E4_kind.Job
         ~payload:(let _, nd = List.nth nodes 4 in nd.E4_node.payload)
       <> []);
  (* The same 32-byte bytes frames under a kind with no Cid row yield nothing. *)
  let disguised =
    node E4_kind.Component
      (f_ctor 0 (List.init 10 (fun i -> if i = 0 then f_bytes (d32 1) else f_bytes (d32 i))))
  in
  check "D4 identical 32-byte `bytes` frames under a kind with no Cid row are NOT edges"
    (E4_shape.cids_of E4_shape.table E4_kind.Component ~payload:disguised.E4_node.payload = []
    && List.length (E4_index.Deps.of_node ~fields:E4_shape.table disguised)
       = List.length (E4_node.checked_edges disguised));
  (* Persistence (IX8). *)
  let d0 = E4_index.Deps.empty in
  let d1 = E4_index.Deps.add d0 ~dep:(addr32 5) ~by:(E4_addr.Ref.make E4_kind.Tree (addr32 6)) in
  let d2 = E4_index.Deps.add d1 ~dep:(addr32 5) ~by:(E4_addr.Ref.make E4_kind.Tree (addr32 7)) in
  check "D5 `Deps` is persistent: the old value is unchanged by a later `add`"
    (E4_index.Deps.find d0 (addr32 5) = []
    && List.length (E4_index.Deps.find d1 (addr32 5)) = 1
    && List.length (E4_index.Deps.find d2 (addr32 5)) = 2);
  check "D6 `add` of a pair already present is idempotent"
    (E4_index.Deps.edges (E4_index.Deps.add d2 ~dep:(addr32 5)
                            ~by:(E4_addr.Ref.make E4_kind.Tree (addr32 7)))
    = E4_index.Deps.edges d2);
  E4_pack.close_reader rd;
  rm_rf dir

(* ============================================================ S. the shape table *)

(* For each row: a payload built to the row's shape (positive) and one that violates it
   (negative).  For a row that claims nothing, the positive case is "nothing is claimed" and the
   negative is "a payload stuffed with 32-byte bytes frames still yields no Cid". *)

let stuffed = f_ctor 0 (List.init 6 (fun i -> f_bytes (d32 i)))

(* `Addr.t` and `Ref.t` are abstract in their digest; never polymorphic-compare them
   (ocaml/STANDARDS.md §4). *)
let same_addrs a b =
  List.length a = List.length b && List.for_all2 E4_addr.Addr.equal a b

let same_refs a b = List.length a = List.length b && List.for_all2 E4_addr.Ref.equal a b

let ok_addrs r want = match r with Ok l -> same_addrs l want | Error _ -> false
let ok_refs r want = match r with Ok l -> same_refs l want | Error _ -> false

let positive_payload (r : E4_shape.row) =
  (* Build a frame tree that satisfies every field of the row. *)
  let arg_of f =
    match f with
    | E4_shape.Cid_field _ -> `B
    | E4_shape.Stamp _ -> `B
    | E4_shape.Ref_field (_, k) -> `R k
    | E4_shape.Data_field _ -> `D
  in
  match r.E4_shape.kind with
  | E4_kind.Tree ->
    Some
      (f_ctor 0
         [ f_list
             [ f_pair (f_string "x") (f_ref (E4_kind.byte E4_kind.Schema) (d32 1));
               f_pair (f_string "y") (f_ref (E4_kind.byte E4_kind.Program) (d32 2)) ] ])
  | _ ->
    let top = List.filter (fun f -> List.length (E4_shape.field_path f) = 1) r.E4_shape.fields in
    if top = [] || List.length top <> List.length r.E4_shape.fields then None
    else begin
      let n =
        List.fold_left
          (fun acc f ->
            match E4_shape.field_path f with [ E4_shape.Arg i ] -> max acc (i + 1) | _ -> acc)
          0 top
      in
      let slot = Array.make n `D in
      List.iter
        (fun f ->
          match E4_shape.field_path f with
          | [ E4_shape.Arg i ] -> slot.(i) <- arg_of f
          | _ -> ())
        top;
      Some
        (f_ctor 0
           (Array.to_list
              (Array.mapi
                 (fun i s ->
                   match s with
                   | `B -> f_bytes (d32 (i + 1))
                   | `R k ->
                     f_ref
                       (E4_kind.byte (match k with Some kk -> kk | None -> E4_kind.Schema))
                       (d32 (i + 1))
                   | `D -> f_nat (i + 1))
                 slot)))
    end

let test_shape () =
  let rows = E4_shape.rows E4_shape.table in
  check "S1 the table has one row per registered kind, in byte order (SH2)"
    (List.map (fun (r : E4_shape.row) -> r.E4_shape.kind) rows = E4_kind.all);
  let ok_pos = ref true and ok_neg = ref true and covered = ref [] in
  List.iter
    (fun (r : E4_shape.row) ->
      let k = r.E4_shape.kind in
      (match positive_payload r with
      | None ->
        (* a row that claims nothing: the positive case is that it claims nothing *)
        if
          E4_shape.cids_of E4_shape.table k ~payload:stuffed <> []
          || E4_shape.refs_of E4_shape.table k ~payload:stuffed <> []
          || E4_shape.stamps_of E4_shape.table k ~payload:stuffed <> []
        then ok_pos := false
      | Some payload ->
        covered := k :: !covered;
        let n_cid = List.length (List.filter (function E4_shape.Cid_field _ -> true | _ -> false) r.E4_shape.fields)
        and n_ref = List.length (List.filter (function E4_shape.Ref_field _ -> true | _ -> false) r.E4_shape.fields)
        and n_st = List.length (List.filter (function E4_shape.Stamp _ -> true | _ -> false) r.E4_shape.fields) in
        let cids = E4_shape.cids_of E4_shape.table k ~payload
        and refs = E4_shape.refs_of E4_shape.table k ~payload
        and stamps = E4_shape.stamps_of E4_shape.table k ~payload in
        (* Tree's one Ref_field is under `Each` and yields two refs, not one. *)
        let want_ref = if k = E4_kind.Tree then 2 else n_ref in
        if
          List.length cids <> n_cid || List.length refs <> want_ref
          || List.length stamps <> n_st
          || not (ok_addrs (E4_shape.cids_of_checked E4_shape.table k ~payload) cids)
          || not (ok_refs (E4_shape.refs_of_checked E4_shape.table k ~payload) refs)
          || E4_shape.stamps_of_checked E4_shape.table k ~payload <> Ok stamps
        then ok_pos := false);
      (* the negative case *)
      let bad = f_ctor 0 [ f_nat 0 ] in
      let claims = r.E4_shape.fields <> [] in
      let refuses_cid =
        match E4_shape.cids_of_checked E4_shape.table k ~payload:bad with
        | Error _ -> true
        | Ok l -> l = []
      in
      let refuses_ref =
        match E4_shape.refs_of_checked E4_shape.table k ~payload:bad with
        | Error _ -> true
        | Ok l -> l = []
      in
      if not (refuses_cid && refuses_ref) then ok_neg := false;
      (* a payload of the right arity but the wrong tag in every slot *)
      if claims then begin
        match positive_payload r with
        | None -> ()
        | Some good ->
          ignore good;
          let wrong =
            f_ctor 0
              (List.init (List.length r.E4_shape.fields) (fun _ -> f_string "not-an-address"))
          in
          let cid_row = List.exists (function E4_shape.Cid_field _ -> true | _ -> false) r.E4_shape.fields
          and ref_row = List.exists (function E4_shape.Ref_field _ -> true | _ -> false) r.E4_shape.fields in
          if cid_row then (
            if
              E4_shape.cids_of E4_shape.table k ~payload:wrong <> []
              || (match E4_shape.cids_of_checked E4_shape.table k ~payload:wrong with
                 | Error _ -> false
                 | Ok _ -> true)
            then ok_neg := false);
          if ref_row && k <> E4_kind.Tree then (
            if
              E4_shape.refs_of E4_shape.table k ~payload:wrong <> []
              || (match E4_shape.refs_of_checked E4_shape.table k ~payload:wrong with
                 | Error _ -> false
                 | Ok _ -> true)
            then ok_neg := false)
      end)
    rows;
  check "S2 every row has a positive case: its own payload gives back exactly its fields" !ok_pos;
  check "S3 every row has a negative case: a payload that violates it is refused, never guessed"
    !ok_neg;
  note "S0 rows with a constructible positive payload: %d of %d" (List.length !covered)
    (List.length rows);
  (* SH1: refs_of is a subset of E4_node.scan_refs, which is the exact answer. *)
  let tree_payload =
    f_ctor 0
      [ f_list
          [ f_pair (f_string "x") (f_ref (E4_kind.byte E4_kind.Schema) (d32 1));
            f_pair (f_string "y") (f_ref (E4_kind.byte E4_kind.Program) (d32 2)) ] ]
  in
  check "S4 `refs_of` is a subset of E4_node.scan_refs, which needs no table (SH1)"
    (let tbl = E4_shape.refs_of E4_shape.table E4_kind.Tree ~payload:tree_payload in
     let exact = E4_node.scan_refs tree_payload in
     List.length tbl = 2
     && List.for_all (fun r -> List.exists (fun s -> E4_addr.Ref.equal r s) exact) tbl);
  check "S5 a Shared row claims nothing, and E4_node.scan_refs still finds its refs exactly"
    (E4_shape.refs_of E4_shape.table E4_kind.Annotation
       ~payload:(f_ctor 0 [ f_ref 11 (d32 3); f_string "v"; f_none ])
     = []
    && List.length (E4_node.scan_refs (f_ctor 0 [ f_ref 11 (d32 3); f_string "v"; f_none ])) = 1);
  check "S6 the statuses are what the two findings say they are"
    (E4_shape.status_of E4_shape.table E4_kind.Job = E4_shape.Pending
    && E4_shape.status_of E4_shape.table E4_kind.Fiber = E4_shape.Tombstoned
    && (match E4_shape.status_of E4_shape.table E4_kind.Annotation with
       | E4_shape.Shared l -> List.length l >= 5
       | _ -> false)
    && E4_shape.status_of E4_shape.table E4_kind.Tree = E4_shape.Frozen
    && E4_shape.status_of E4_shape.table E4_kind.Query = E4_shape.Unused);
  check "S7 `class_at` is the four-way view, and Cls_unknown for a path no row mentions"
    (E4_shape.class_at E4_shape.table E4_kind.Job (E4_shape.args [ 0 ]) = E4_shape.Cls_cid
    && E4_shape.class_at E4_shape.table E4_kind.Job (E4_shape.args [ 2 ]) = E4_shape.Cls_data
    && E4_shape.class_at E4_shape.table E4_kind.Checkpoint (E4_shape.args [ 3 ])
       = E4_shape.Cls_stamp
    && E4_shape.class_at E4_shape.table E4_kind.Log (E4_shape.args [ 0 ])
       = E4_shape.Cls_ref (Some E4_kind.Job)
    && E4_shape.class_at E4_shape.table E4_kind.Annotation (E4_shape.args [ 0 ])
       = E4_shape.Cls_unknown);
  check "S8 a Cid field and a Stamp are the SAME bytes, and only the table tells them apart"
    (let cid_payload =
       f_ctor 0 [ f_bytes (d32 9); f_bytes (d32 9); f_nat 0; f_bytes (d32 9) ]
     in
     let stamp_payload =
       f_ctor 0
         [ f_ref (E4_kind.byte E4_kind.Job) (d32 0); f_nat 0;
           f_ref (E4_kind.byte E4_kind.Tape) (d32 0); f_bytes (d32 9); f_bytes "" ]
     in
     List.length (E4_shape.cids_of E4_shape.table E4_kind.Job ~payload:cid_payload) = 3
     && E4_shape.cids_of E4_shape.table E4_kind.Checkpoint ~payload:stamp_payload = []
     && List.length (E4_shape.stamps_of E4_shape.table E4_kind.Checkpoint ~payload:stamp_payload)
        = 1)

(* ============================================================ P. the path language *)

let test_paths () =
  let p = f_ctor 0 [ f_nat 7; f_list [ f_nat 1; f_nat 2; f_nat 3 ]; f_some (f_string "s") ] in
  check "P1 `Arg i` selects the i-th argument of a ctor, and the index frame is not an argument"
    (match E4_shape.resolve ~payload:p (E4_shape.args [ 0 ]) with
    | [ (2, _, _) ] -> true
    | _ -> false);
  check "P2 `Each` selects every element of a list frame (SH5)"
    (List.length (E4_shape.resolve ~payload:p [ E4_shape.Arg 1; E4_shape.Each ]) = 3);
  check "P3 `Arg 0` of a `some` frame is its content"
    (match E4_shape.resolve ~payload:p [ E4_shape.Arg 2; E4_shape.Arg 0 ] with
    | [ (3, _, _) ] -> true
    | _ -> false);
  check "P4 a path that does not resolve gives the empty list, never an exception"
    (E4_shape.resolve ~payload:p (E4_shape.args [ 99 ]) = []
    && E4_shape.resolve ~payload:p (E4_shape.args [ 0; 0 ]) = []
    && E4_shape.resolve ~payload:"" (E4_shape.args [ 0 ]) = []);
  (* SH6: a `bytes` frame that happens to contain frames has no children. *)
  let inner = f_ref (E4_kind.byte E4_kind.Schema) (d32 4) in
  let disguised = f_ctor 0 [ f_bytes inner ] in
  check "P5 the walk never descends into a tag-8 `bytes` payload, even one full of frames (SH6)"
    (E4_shape.resolve ~payload:disguised [ E4_shape.Arg 0; E4_shape.Arg 0 ] = []
    && E4_node.scan_refs disguised = []);
  check "P6 a pair has exactly two children and a handle frame has none"
    (List.length (E4_shape.resolve ~payload:(f_ctor 0 [ f_pair (f_nat 1) (f_nat 2) ])
                    [ E4_shape.Arg 0; E4_shape.Each ])
     = 2
    && E4_shape.resolve ~payload:(f_ctor 0 [ f_handle 1 5 ]) [ E4_shape.Arg 0; E4_shape.Arg 0 ]
       = []);
  check "P7 `path_to_string` prints `Each` as `*` and is not an identity"
    (E4_shape.path_to_string [ E4_shape.Arg 0; E4_shape.Each; E4_shape.Arg 1 ] = "0.*.1")

(* ============================================================ property sweep *)

let test_property_sweep () =
  let ok = ref true in
  for _ = 1 to 8 do
    let n = 200 + rand 400 in
    let b = build_pack n in
    let rd = E4_pack.open_reader ~dir:b.b_dir in
    let reb, stop = E4_index.of_pack rd ~from:E4_index.from_start in
    if stop <> E4_pack.Eof then ok := false;
    if E4_index.count reb <> List.length b.b_places then ok := false;
    List.iter
      (fun (a, (s, o), k) ->
        match E4_index.find_in rd reb a with
        | Some e ->
          if e.E4_index.seg <> s || e.E4_index.off <> o || not (E4_kind.equal e.E4_index.kind k)
          then ok := false
        | None -> ok := false)
      b.b_places;
    (* save, drop, load: no answer changes (L-IDX-0). *)
    let path = Filename.concat b.b_dir "i.idx" in
    E4_index.save ~path reb ~covers:b.b_end;
    (match E4_index.load_at ~path ~pack_end:b.b_end with
    | Ok j ->
      List.iter
        (fun (a, _, _) -> if E4_index.find_in rd j a = None then ok := false)
        b.b_places
    | Error _ -> ok := false);
    E4_pack.close_reader rd;
    rm_rf b.b_dir
  done;
  check "Q1 over 8 random packs: rebuild, save and load all agree with the staged places" !ok

(* ============================================================ *)

let () =
  note "sandbox: %s" root;
  test_slot ();
  let b = test_find () in
  test_collision ();
  test_growth ();
  test_offheap ();
  test_file b;
  rm_rf b.b_dir;
  let rd, b2, reb = test_rebuild () in
  test_by_kind rd b2 reb;
  E4_pack.close_reader rd;
  rm_rf b2.b_dir;
  test_deps ();
  test_shape ();
  test_paths ();
  test_property_sweep ();
  rm_rf root;
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
