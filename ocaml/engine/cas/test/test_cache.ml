(* test_cache — lane P7: E4_cache, E4_subterm, E4_deps.

   What it checks, and against what:

     the caches (E4_cache, A2 §1.10, laws CA1-CA8)
       B1-B5  the bounded-bytes and bounded-slots invariant under a long random sequence of
              put / get / mem / drop, with `invariant` re-checked after EVERY operation, plus
              the two degenerate capacities (0 bytes, 1 slot) and the entry heavier than the
              whole cache, which must be refused and never admitted.
       E1-E3  CLOCK: an entry that was read survives a sweep that evicts one that was not; an
              unread cache evicts in FIFO order; the hand allocates nothing on a hit.
       H1-H3  hit / miss / eviction / admission / refusal accounting, on a scripted sequence
              whose every count is written out by hand.
       M1-M2  `add` of a resident key replaces and does not grow `entries` (CA4).
       I1-I4  identity (CA1) against a real store, and the drop-and-rebuild of L-IDX-0: every
              answer is the same after `drop`, and the counters prove the second round really
              re-read the pack.
       V1-V4  CA6: a POISONED cache — bytes that are not the node's, filed under the node's
              address — changes no answer of `E4_cas.verify`, `verify_node` or `get_bytes`.
              The poison is exhibited first, so the test cannot pass vacuously.
       K1-K2  the decoded tier: `Decoded(V).get` refuses a node whose kind is not `V.kind`
              (D5) and admits nothing for it.

     the subterm index (E4_subterm, cas-repository-algebra §3.5/§6, amendments M3/M18/M5)
       S1     THE SLICE LAW (L-SUB-1, `slice_atPath`) over all 37 goldens of
              ocaml/eff/goldens: for every entry, the slice its (off, len) names equals the
              subterm's OWN encoding, computed independently through the value side
              (`Tree.at_` then `Tree.encode`).  Counts of subterms per program are printed.
       S2     the same over a witness of EVERY constructor of EVERY family — 50 of them, not
              the corpus (L-SUB-3, M3): the arity, the children and the ValPath of each.
       S3-S4  the root is the whole; pre-order; two occurrences of one subterm share a `Cid`
              and differ in `off` (SB3).
       S5-S6  the two path spaces (L-SUB-2, M5): `val_of_prog` / `prog_of_val` round-trip, and
              the divergence is EXACTLY branch, whileLoop, choose and ifElse — enumerated, so
              a fifth divergence or a lost one fails here.
       S7     the child table against the value side at every constructor.
       S9-S11 malformed bytes are refused whole (SB7); the index is a function of the bytes
              (SB8) — building it twice is identical, and flipping one byte changes it.

     the dependents index (E4_deps, a FACE over E4_index.Deps — laws DP1-DP6)
       D1     REBUILD = INCREMENTAL over a 10 000-node store: the fold over `E4_cas.nodes` in
              write order and the full pack scan are equal, dependee for dependee and
              dependent for dependent.
       D2/D4  `of_node` against a brute-force recomputation from `checked_edges` and
              `E4_shape.cids_of`, node by node, including `job` nodes whose three `Cid` fields
              are only visible through the table (finding R1).
       D3     persistence: a `t` held across a hundred additions still answers what it did.
       D6     NOT AN EDGE (M1): `reachable` and `closure` answer the same with the index
              built and with it thrown away.
       D7     a truncated pack stops the scan and the verdict is returned, not swallowed.

     mutation checks (cas-design §11 commit 9: a test nobody can break is not a test)
       X1-X5  one negative control per positive family above.

   Everything that touches the disk runs in a fresh directory under $E4_CACHE_TMP (default:
   the system temp dir) and is removed at the end.  Exit code 0 iff every check passed. *)

open Effect4_engine
open Effect4_engine_cas

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n%!" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n%!")
let skip name why = Printf.printf "SKIP  %s (%s)\n%!" name why

(* ============================================================ the sandbox *)

let root_dir =
  let base = try Sys.getenv "E4_CACHE_TMP" with Not_found -> Filename.get_temp_dir_name () in
  let d =
    Filename.concat base
      (Printf.sprintf "e4cache-%d-%d" (Unix.getpid ()) (int_of_float (Unix.time ())))
  in
  (try Unix.mkdir base 0o755 with Unix.Unix_error _ -> ());
  Unix.mkdir d 0o755;
  d

let counter = ref 0

let fresh_dir () =
  incr counter;
  let d = Filename.concat root_dir (Printf.sprintf "s%03d" !counter) in
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

(* A deterministic generator: the tests must be the same run to run. *)
let seed = ref 0x2026_09_08

let rand n =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFF_FFFF;
  if n <= 0 then 0 else !seed mod n

(* ============================================================ frames and nodes *)

let v_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let v_bytes b = E4_be.framed Eff_frame.tag_bytes b
let v_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (v_nat i :: args))
let v_ref k d = E4_be.framed Eff_frame.tag_ref (String.make 1 (Char.chr k) ^ d)
let node kind spec payload = { E4_node.version = 0; kind; spec; payload }
let addr_of_string s = E4_addr.Addr.of_digest (E4_sha256.digest s)

(* ============================================================================================
   1. the caches
   ============================================================================================ *)

let addr_n i = addr_of_string (Printf.sprintf "e4.test.cache.addr.%d" i)

let cache_invariant_ok name t =
  match E4_cache.Bytes_cache.invariant t with
  | Ok () -> true
  | Error m ->
    Printf.printf "      %s: %s\n%!" name m;
    false

(* ---- B1-B5: the bound, under a long random sequence ---- *)

let test_bound () =
  print_endline "-- E4_cache: the weight and slot bounds (CA2, CA5, CA8)";
  let slots = 48 and cap = 24_000 in
  let c = E4_cache.Bytes_cache.create_sized ~slots ~capacity_bytes:cap in
  let pool = Array.init 400 (fun i -> addr_n i) in
  let ok = ref true and iv = ref true in
  for step = 1 to 20_000 do
    (match rand 10 with
    | 0 | 1 | 2 | 3 ->
      let v = String.make (rand 1200) 'x' in
      E4_cache.Bytes_cache.add c pool.(rand 400) v
    | 4 | 5 | 6 | 7 -> ignore (E4_cache.Bytes_cache.find c pool.(rand 400))
    | 8 -> ignore (E4_cache.Bytes_cache.mem c pool.(rand 400))
    | _ -> if step mod 4000 = 0 then E4_cache.Bytes_cache.drop c);
    if E4_cache.Bytes_cache.bytes c > cap then ok := false;
    if E4_cache.Bytes_cache.entries c > slots then ok := false;
    if !iv then iv := cache_invariant_ok "invariant" c
  done;
  check "B1 bytes <= capacity_bytes and entries <= slots after every operation" !ok;
  check "B2 `invariant` holds after every operation (CA8)" !iv;
  let s = E4_cache.Bytes_cache.stats c in
  note "B1/B2 20000 ops: hits=%d misses=%d admissions=%d evictions=%d (of which slot-bound %d) refusals=%d"
    s.E4_cache.Bytes_cache.hits s.E4_cache.Bytes_cache.misses
    s.E4_cache.Bytes_cache.admissions s.E4_cache.Bytes_cache.evictions
    s.E4_cache.Bytes_cache.slot_bound_evictions s.E4_cache.Bytes_cache.refusals;
  check "B3 the slot array never grew: slots is what `create_sized` was given (CA5)"
    (E4_cache.Bytes_cache.slots c = slots);

  (* the entry heavier than the whole cache *)
  let c2 = E4_cache.Bytes_cache.create_sized ~slots:8 ~capacity_bytes:100 in
  E4_cache.Bytes_cache.add c2 (addr_n 0) (String.make 101 'z');
  let s2 = E4_cache.Bytes_cache.stats c2 in
  check "B4 an entry heavier than the capacity is refused, not admitted (CA2)"
    (E4_cache.Bytes_cache.find c2 (addr_n 0) = None
    && s2.E4_cache.Bytes_cache.refusals = 1
    && s2.E4_cache.Bytes_cache.admissions = 0
    && E4_cache.Bytes_cache.bytes c2 = 0);

  (* the degenerate capacities *)
  let c3 = E4_cache.Bytes_cache.create_sized ~slots:1 ~capacity_bytes:0 in
  E4_cache.Bytes_cache.add c3 (addr_n 1) "";
  let c4 = E4_cache.Bytes_cache.create_sized ~slots:1 ~capacity_bytes:64 in
  E4_cache.Bytes_cache.add c4 (addr_n 1) "aa";
  E4_cache.Bytes_cache.add c4 (addr_n 2) "bb";
  check "B5 capacity 0 and one slot are caches, not errors (CA7)"
    (E4_cache.Bytes_cache.entries c3 <= 1
    && E4_cache.Bytes_cache.entries c4 = 1
    && E4_cache.Bytes_cache.find c4 (addr_n 2) = Some "bb"
    && E4_cache.Bytes_cache.find c4 (addr_n 1) = None)

(* ---- E1-E3: CLOCK ---- *)

let test_clock () =
  print_endline "-- E4_cache: CLOCK eviction (CA3)";
  (* Two slots, plenty of bytes: only the slot bound bites, so the choice of victim is
     visible.  a is read, b is not; the sweep must take b. *)
  let c = E4_cache.Bytes_cache.create_sized ~slots:2 ~capacity_bytes:1_000_000 in
  E4_cache.Bytes_cache.add c (addr_n 1) "a";
  E4_cache.Bytes_cache.add c (addr_n 2) "b";
  ignore (E4_cache.Bytes_cache.find c (addr_n 1));
  E4_cache.Bytes_cache.add c (addr_n 3) "c";
  check "E1 the entry that was read survives; the one that was not is evicted"
    (E4_cache.Bytes_cache.mem c (addr_n 1)
    && (not (E4_cache.Bytes_cache.mem c (addr_n 2)))
    && E4_cache.Bytes_cache.mem c (addr_n 3));

  (* Nothing read: FIFO. *)
  let c2 = E4_cache.Bytes_cache.create_sized ~slots:3 ~capacity_bytes:1_000_000 in
  List.iter (fun i -> E4_cache.Bytes_cache.add c2 (addr_n i) "v") [ 1; 2; 3 ];
  E4_cache.Bytes_cache.add c2 (addr_n 4) "v";
  check "E2 with nothing read the sweep evicts the oldest (FIFO)"
    ((not (E4_cache.Bytes_cache.mem c2 (addr_n 1)))
    && E4_cache.Bytes_cache.mem c2 (addr_n 2)
    && E4_cache.Bytes_cache.mem c2 (addr_n 3)
    && E4_cache.Bytes_cache.mem c2 (addr_n 4));

  (* A hit allocates nothing: minor words must not move across 100 000 hits. *)
  let c3 = E4_cache.Bytes_cache.create_sized ~slots:4 ~capacity_bytes:1_000_000 in
  E4_cache.Bytes_cache.add c3 (addr_n 7) "value";
  let a7 = addr_n 7 in
  ignore (E4_cache.Bytes_cache.find c3 a7);
  let before = Gc.minor_words () in
  for _ = 1 to 100_000 do
    ignore (Sys.opaque_identity (E4_cache.Bytes_cache.find c3 a7))
  done;
  let after = Gc.minor_words () in
  let per_hit = (after -. before) /. 100_000. in
  note "E3 minor words per hit: %.4f" per_hit;
  check "E3 a hit allocates nothing (< 1 minor word per hit, CA3)" (per_hit < 1.0)

(* ---- H1-H3: accounting ---- *)

let test_accounting () =
  print_endline "-- E4_cache: hit / miss / eviction accounting";
  let c = E4_cache.Bytes_cache.create_sized ~slots:2 ~capacity_bytes:1_000_000 in
  ignore (E4_cache.Bytes_cache.find c (addr_n 1));
  (* miss 1 *)
  E4_cache.Bytes_cache.add c (addr_n 1) "aaaa";
  (* admission 1 *)
  ignore (E4_cache.Bytes_cache.find c (addr_n 1));
  (* hit 1 *)
  ignore (E4_cache.Bytes_cache.find c (addr_n 1));
  (* hit 2 *)
  ignore (E4_cache.Bytes_cache.find c (addr_n 2));
  (* miss 2 *)
  E4_cache.Bytes_cache.add c (addr_n 2) "bb";
  (* admission 2 *)
  E4_cache.Bytes_cache.add c (addr_n 3) "ccc";
  (* admission 3, one eviction *)
  let s = E4_cache.Bytes_cache.stats c in
  check "H1 hits, misses, admissions and evictions are exactly the scripted counts"
    (s.E4_cache.Bytes_cache.hits = 2
    && s.E4_cache.Bytes_cache.misses = 2
    && s.E4_cache.Bytes_cache.admissions = 3
    && s.E4_cache.Bytes_cache.evictions = 1
    && s.E4_cache.Bytes_cache.entries = 2);
  check "H2 `bytes` is the sum of the live values' lengths"
    (s.E4_cache.Bytes_cache.bytes = E4_cache.Bytes_cache.bytes c
    && E4_cache.Bytes_cache.bytes c
       = List.fold_left
           (fun acc a ->
             match E4_cache.Bytes_cache.find c a with None -> acc | Some v -> acc + String.length v)
           0
           [ addr_n 1; addr_n 2; addr_n 3 ]);
  check "H3 hit_ratio is hits / (hits + misses)"
    (abs_float (E4_cache.Bytes_cache.hit_ratio (E4_cache.Bytes_cache.stats c) -. (4. /. 7.))
    < 1e-9);
  (* `mem` sets no bit and counts nothing (CA4). *)
  let before = E4_cache.Bytes_cache.stats c in
  ignore (E4_cache.Bytes_cache.mem c (addr_n 2));
  ignore (E4_cache.Bytes_cache.mem c (addr_n 99));
  let after = E4_cache.Bytes_cache.stats c in
  check "H4 `mem` counts neither a hit nor a miss"
    (before.E4_cache.Bytes_cache.hits = after.E4_cache.Bytes_cache.hits
    && before.E4_cache.Bytes_cache.misses = after.E4_cache.Bytes_cache.misses)

(* ---- M1-M2: replace ---- *)

let test_replace () =
  print_endline "-- E4_cache: replace (CA4)";
  let c = E4_cache.Bytes_cache.create_sized ~slots:8 ~capacity_bytes:1_000_000 in
  E4_cache.Bytes_cache.add c (addr_n 1) "aaaa";
  E4_cache.Bytes_cache.add c (addr_n 2) "bb";
  let e1 = E4_cache.Bytes_cache.entries c in
  E4_cache.Bytes_cache.add c (addr_n 1) "zzzzzzzz";
  check "M1 a replace leaves `entries` where it was and moves `bytes` by the difference"
    (E4_cache.Bytes_cache.entries c = e1
    && E4_cache.Bytes_cache.bytes c = 8 + 2
    && E4_cache.Bytes_cache.find c (addr_n 1) = Some "zzzzzzzz");
  check "M2 the invariant survives a replace" (cache_invariant_ok "replace" c)

(* ---- the store the identity tests run against ---- *)

type built = {
  b_dir : string;
  b_store : E4_cas.t;
  b_ro : E4_cas.ro;
  b_schema : E4_addr.Addr.t;
  b_entries : E4_addr.Addr.t array;  (** the `entry` nodes, in write order *)
  b_jobs : E4_addr.Addr.t array;  (** the `job` nodes, in write order *)
}

(* A store of one genesis schema, [n] `entry` nodes each naming the schema and up to two
   earlier entries, and [jobs] `job` nodes whose payload is cas-design §4's shape — three
   32-byte `bytes` frames that ARE addresses and one that is a `Nat`.  The `job` nodes are
   what makes the dependents index's Cid half real: without `E4_shape.table` those three
   frames are indistinguishable from any other blob (finding R1). *)
let build_store ~(n : int) ~(jobs : int) : built =
  let dir = fresh_dir () in
  let st = E4_cas.open_rw ~dir { E4_cas.default_opts with index_slots = 1 lsl 14 } in
  let genesis = node E4_kind.Schema E4_node.zero_digest (v_ctor 0 [ v_nat 0 ]) in
  (match E4_cas.put st genesis with
  | Ok _ -> ()
  | Error _ -> failwith "test_cache: the genesis was refused");
  let schema = E4_node.address genesis in
  let spec = E4_addr.Addr.bytes schema in
  let entries = Array.make n E4_addr.Addr.zero in
  for i = 0 to n - 1 do
    let refs =
      if i = 0 then []
      else if i = 1 then [ v_ref (E4_kind.byte E4_kind.Entry) (E4_addr.Addr.bytes entries.(0)) ]
      else
        [ v_ref (E4_kind.byte E4_kind.Entry) (E4_addr.Addr.bytes entries.(i - 1));
          v_ref (E4_kind.byte E4_kind.Entry) (E4_addr.Addr.bytes entries.(i / 2)) ]
    in
    let nd = node E4_kind.Entry spec (v_ctor 0 (v_nat i :: refs)) in
    (match E4_cas.put st nd with
    | Ok _ -> ()
    | Error a -> failwith ("test_cache: entry refused: " ^ E4_cas.admission_word a));
    entries.(i) <- E4_node.address nd
  done;
  let jb = Array.make jobs E4_addr.Addr.zero in
  for j = 0 to jobs - 1 do
    let cid k = E4_addr.Addr.bytes (addr_of_string (Printf.sprintf "e4.test.cid.%d.%d" j k)) in
    let nd =
      node E4_kind.Job spec
        (v_ctor 0 [ v_bytes (cid 0); v_bytes (cid 1); v_nat (7 + j); v_bytes (cid 2) ])
    in
    (match E4_cas.put st nd with
    | Ok _ -> ()
    | Error a -> failwith ("test_cache: job refused: " ^ E4_cas.admission_word a));
    jb.(j) <- E4_node.address nd
  done;
  E4_cas.commit st;
  { b_dir = dir; b_store = st; b_ro = E4_cas.read_only st; b_schema = schema;
    b_entries = entries; b_jobs = jb }

(* ---- I1-I4: identity and the drop-and-rebuild ---- *)

let test_identity (b : built) =
  print_endline "-- E4_cache: identity and drop-and-rebuild (CA1, L-IDX-0)";
  let addrs = Array.to_list b.b_entries @ Array.to_list b.b_jobs @ [ b.b_schema ] in
  let c = E4_cache.Bytes_cache.create_sized ~slots:64 ~capacity_bytes:32_768 in
  let round () =
    List.map (fun a -> E4_cache.Bytes_cache.get c b.b_ro a) addrs
  in
  let truth = List.map (fun a -> E4_cas.get_bytes b.b_ro a) addrs in
  let r1 = round () in
  check "I1 `get` through the cache is `E4_cas.get_bytes`, address for address (CA1)"
    (r1 = truth);
  let r2 = round () in
  check "I2 a second round, mostly from the cache, answers the same" (r2 = truth);
  let s_before = E4_cache.Bytes_cache.stats c in
  E4_cache.Bytes_cache.drop c;
  check "I3 `drop` empties the cache and keeps the counters"
    (E4_cache.Bytes_cache.entries c = 0
    && E4_cache.Bytes_cache.bytes c = 0
    && (E4_cache.Bytes_cache.stats c).E4_cache.Bytes_cache.hits
       = s_before.E4_cache.Bytes_cache.hits);
  let r3 = round () in
  let s_after = E4_cache.Bytes_cache.stats c in
  let re_read = s_after.E4_cache.Bytes_cache.misses - s_before.E4_cache.Bytes_cache.misses in
  check "I4 after a full drop every answer is the same, and the misses show it re-read"
    (r3 = truth && re_read >= List.length addrs);
  note "I4 %d addresses, %d misses after the drop" (List.length addrs) re_read;
  (* an address the store does not hold *)
  check "I5 an absent address is None through the cache and admits nothing"
    (E4_cache.Bytes_cache.get c b.b_ro (addr_n 999_999) = None
    && not (E4_cache.Bytes_cache.mem c (addr_n 999_999)))

(* ---- V1-V4: CA6, the poisoned cache ---- *)

let test_poison (b : built) =
  print_endline "-- E4_cache: `verify` never consults a cache (CA6, L-CAS-6, risk R3)";
  let victim = b.b_entries.(Array.length b.b_entries / 2) in
  let truth =
    match E4_cas.get_bytes b.b_ro victim with Some s -> s | None -> failwith "no victim"
  in
  let poison = String.make (String.length truth) '\255' in
  let c = E4_cache.Bytes_cache.create_sized ~slots:16 ~capacity_bytes:1_000_000 in
  E4_cache.Bytes_cache.add c victim poison;
  check "V1 the poison is really in the cache (this is what makes V2-V4 mean something)"
    (E4_cache.Bytes_cache.find c victim = Some poison && not (String.equal poison truth));
  check "V2 `E4_cas.verify` is ok with the cache poisoned"
    (match E4_cas.verify b.b_ro with Ok () -> true | Error _ -> false);
  check "V3 `E4_cas.verify_node` on the poisoned address is ok"
    (match E4_cas.verify_node b.b_ro victim with Ok () -> true | Error _ -> false);
  check "V4 `E4_cas.get_bytes` still answers the pack, not the cache"
    (E4_cas.get_bytes b.b_ro victim = Some truth);
  (* And the reverse direction: a cache poisoned in the OTHER direction — a value filed under
     an address the store does not hold — is not a store entry. *)
  E4_cache.Bytes_cache.add c (addr_n 424_242) "not a node";
  check "V5 a cache entry for an absent address does not make it resident"
    ((not (E4_cas.mem b.b_ro (addr_n 424_242)))
    && E4_cas.get_bytes b.b_ro (addr_n 424_242) = None)

(* ---- K1-K2: the decoded tier ---- *)

module Entry_nat = struct
  type t = int

  let kind = E4_kind.Entry

  (* The payload of the `entry` nodes `build_store` writes: ctor 0 whose first argument is the
     node's ordinal.  The whole point of `VALUE.decode` is that it reads the PAYLOAD. *)
  let decode (s : string) : int option =
    match Eff_frame.read_ctor s 0 (String.length s) with
    | Some (0, p, e, next) when next = String.length s -> (
      match Eff_frame.decode_nat s p e with Some (n, _) -> Some n | None -> None)
    | _ -> None

  let weight (_ : t) : int = 24
end

module Entry_cache = E4_cache.Decoded (Entry_nat)

let test_decoded (b : built) =
  print_endline "-- E4_cache: the decoded tier (Decoded(V), CA1, D5)";
  let c = Entry_cache.create_sized ~slots:32 ~capacity_bytes:4096 in
  let want = min 40 (Array.length b.b_entries) in
  let ok = ref true in
  for i = 0 to want - 1 do
    match Entry_cache.get c b.b_ro b.b_entries.(i) with
    | Some n -> if n <> i then ok := false
    | None -> ok := false
  done;
  check "K1 `Decoded(V).get` decodes the payload and answers the value it holds" !ok;
  Entry_cache.drop c;
  let ok2 = ref true in
  for i = 0 to want - 1 do
    match Entry_cache.get c b.b_ro b.b_entries.(i) with
    | Some n -> if n <> i then ok2 := false
    | None -> ok2 := false
  done;
  check "K2 the same after a full drop (the identity is the pack plus V.decode)" !ok2;
  let before = (Entry_cache.stats c).E4_cache.Bytes_cache.admissions in
  let refused =
    Array.length b.b_jobs > 0 && Entry_cache.get c b.b_ro b.b_jobs.(0) = None
  in
  let after = (Entry_cache.stats c).E4_cache.Bytes_cache.admissions in
  check "K3 a node whose kind is not V.kind is refused and admits nothing (D5)"
    (refused && before = after);
  check "K4 the decoded tier's invariant holds"
    (match Entry_cache.invariant c with Ok () -> true | Error _ -> false);
  (* the whole-node instance *)
  let nc = E4_cache.Node_cache.create_sized ~slots:16 ~capacity_bytes:65_536 in
  let n0 = E4_cache.Node_cache.get nc b.b_ro b.b_entries.(0) in
  check "K5 `Node_cache` answers the decoded envelope and it re-encodes to the pack's bytes"
    (match (n0, E4_cas.get_bytes b.b_ro b.b_entries.(0)) with
    | Some n, Some bytes -> String.equal (E4_node.encode n) bytes
    | _ -> false)

(* ============================================================================================
   2. the subterm index
   ============================================================================================ *)

open Eff_types

let t_unit = Term_lit Lit_unit
let t_n i = Term_lit (Lit_nat i)
let ea = Eff_succeed (t_n 1)
let eb = Eff_succeed (t_n 2)
let ec = Eff_succeed (t_n 3)
let sa = Stmt_ret (t_n 1)
let ssa = Stmts_cons (Stmt_ret (t_n 1), Stmts_nil)
let ssb = Stmts_cons (Stmt_ret (t_n 2), Stmts_nil)

let fopts =
  { fork_options_startImmediately = true; fork_options_daemon = false;
    fork_options_maskMode = Mask_mode_inherit }

(* A witness of EVERY constructor of EVERY family (L-SUB-3, M3): fifty of them, with distinct
   children wherever a constructor has more than one, so that a wrong ValPath cannot pass by
   two children happening to be equal. *)
let eff_witnesses : Eff_types.eff list =
  [ Eff_succeed t_unit;
    Eff_fail t_unit;
    Eff_failCause (Cause_term_fail t_unit);
    Eff_yieldError t_unit;
    Eff_sync t_unit;
    Eff_suspend ea;
    Eff_perform (Native_op_refGet, t_unit);
    Eff_bind (ea, eb);
    Eff_gen ssa;
    Eff_catchCause (ea, eb);
    Eff_matchCause (ea, eb, ec);
    Eff_onExit (ea, eb);
    Eff_exit ea;
    Eff_uninterruptible ea;
    Eff_interruptible ea;
    Eff_branch (t_unit, ea, eb);
    Eff_whileLoop (t_n 1, t_n 2, t_n 3, ea);
    Eff_yieldNow 3;
    Eff_callback (Native_op_deferredAwait, t_unit);
    Eff_awaitFiber (t_unit, Observer_mode_awaitValue);
    Eff_withFiber Action_term_getId;
    Eff_scoped ea;
    Eff_acquireRelease (ea, eb);
    Eff_choose (1, ea, eb) ]

let stmt_witnesses : Eff_types.stmt list =
  [ Stmt_bindYield ea; Stmt_yieldDiscard eb; Stmt_ret t_unit; Stmt_ifElse (t_unit, ssa, ssb);
    Stmt_whileTrue ssa; Stmt_breakLoop ]

let stmts_witnesses : Eff_types.stmts list = [ Stmts_nil; Stmts_cons (sa, ssb) ]

let effs_witnesses : Eff_types.effs list =
  [ Effs_nil; Effs_cons (ea, Effs_cons (eb, Effs_nil)) ]

let action_witnesses : Eff_types.action_term list =
  [ Action_term_fork (ea, fopts);
    Action_term_forkIn (ea, fopts, t_unit);
    Action_term_forkScoped (ea, fopts);
    Action_term_runIn (t_unit, t_n 1);
    Action_term_interrupt t_unit;
    Action_term_interruptScoped t_unit;
    Action_term_interruptAll (t_unit, None);
    Action_term_awaitAll t_unit;
    Action_term_awaitAllFailFast t_unit;
    Action_term_snapshotChildren;
    Action_term_awaitNewChildren t_unit;
    Action_term_raceAll (Effs_cons (ea, Effs_nil));
    Action_term_setContext t_unit;
    Action_term_getContext;
    Action_term_getId;
    Action_term_closeScope (t_unit, t_n 1) ]

(* Each witness, embedded in a program, and the ProgPath at which the index must find it. *)
let embedded : (E4_subterm.Tree.node * Eff_types.eff * int list) list =
  List.map (fun e -> (E4_subterm.Tree.N_eff e, Eff_suspend e, [ 0 ])) eff_witnesses
  @ List.map
      (fun s -> (E4_subterm.Tree.N_stmt s, Eff_gen (Stmts_cons (s, Stmts_nil)), [ 0; 0 ]))
      stmt_witnesses
  @ List.map (fun s -> (E4_subterm.Tree.N_stmts s, Eff_gen s, [ 0 ])) stmts_witnesses
  @ List.map
      (fun e ->
        (E4_subterm.Tree.N_effs e, Eff_withFiber (Action_term_raceAll e), [ 0; 0 ]))
      effs_witnesses
  @ List.map (fun a -> (E4_subterm.Tree.N_action a, Eff_withFiber a, [ 0 ])) action_witnesses

let eff_goldens_dir () =
  let rec ancestors d n acc =
    if n = 0 then List.rev acc else ancestors (Filename.dirname d) (n - 1) (d :: acc)
  in
  let here = Sys.getcwd () in
  let from_env = try [ Sys.getenv "E4_EFF_GOLDENS" ] with Not_found -> [] in
  let per_ancestor a =
    [ Filename.concat a (Filename.concat "eff" "goldens");
      Filename.concat a (Filename.concat "ocaml" (Filename.concat "eff" "goldens")) ]
  in
  let cands = from_env @ List.concat (List.map per_ancestor (ancestors here 9 [])) in
  List.find_opt
    (fun d -> d <> "" && (try Sys.is_directory d with Sys_error _ -> false))
    cands

(* ---- S1: the slice law over the goldens ---- *)

let test_slice_goldens () =
  print_endline "-- E4_subterm: the slice law over ocaml/eff/goldens (L-SUB-1, slice_atPath)";
  match eff_goldens_dir () with
  | None ->
    skip "S1 the slice law over the 37 goldens" "ocaml/eff/goldens not found";
    skip "S3 the root is the whole program" "ocaml/eff/goldens not found";
    skip "S8 a parent precedes every descendant" "ocaml/eff/goldens not found"
  | Some dir ->
    let files =
      List.sort compare
        (List.filter
           (fun f -> Filename.check_suffix f ".bin")
           (Array.to_list (Sys.readdir dir)))
    in
    let total = ref 0 and progs = ref 0 and bad = ref 0 and refused = ref 0 in
    let root_ok = ref true and order_ok = ref true in
    List.iter
      (fun f ->
        let bytes = read_file (Filename.concat dir f) in
        match (E4_subterm.of_program_opt bytes, E4_subterm.Tree.of_bytes bytes) with
        | None, _ | _, None ->
          incr refused;
          Printf.printf "      %s: the wire refused it\n%!" f
        | Some ix, Some root ->
          incr progs;
          let es = E4_subterm.entries ix in
          total := !total + List.length es;
          let per = Hashtbl.create 8 in
          List.iter
            (fun (e : E4_subterm.entry) ->
              let fam = E4_subterm.family_name e.E4_subterm.family in
              Hashtbl.replace per fam (1 + try Hashtbl.find per fam with Not_found -> 0);
              (* THE LAW: the byte side's slice is the value side's own encoding. *)
              match E4_subterm.Tree.at_ root e.E4_subterm.prog_path with
              | None ->
                incr bad;
                Printf.printf "      %s: no node at %s\n%!" f
                  (E4_subterm.path_to_string e.E4_subterm.prog_path)
              | Some nd ->
                let sl = E4_subterm.slice bytes e in
                if not (String.equal sl (E4_subterm.Tree.encode nd)) then begin
                  incr bad;
                  Printf.printf "      %s: slice at %s is not the subterm's own bytes\n%!" f
                    (E4_subterm.path_to_string e.E4_subterm.prog_path)
                end;
                if
                  not
                    (E4_subterm.family_eq e.E4_subterm.family (E4_subterm.Tree.family_of nd)
                    && e.E4_subterm.ctor = E4_subterm.Tree.ctor_index nd)
                then begin
                  incr bad;
                  Printf.printf "      %s: family/ctor disagree at %s\n%!" f
                    (E4_subterm.path_to_string e.E4_subterm.prog_path)
                end)
            es;
          let r = E4_subterm.root ix in
          if
            not
              (r.E4_subterm.off = 0
              && r.E4_subterm.len = String.length bytes
              && r.E4_subterm.prog_path = []
              && r.E4_subterm.val_path = [])
          then root_ok := false;
          if E4_subterm.count ix <> E4_subterm.Tree.subtree_count root then begin
            incr bad;
            Printf.printf "      %s: %d entries but %d nodes in the tree\n%!" f
              (E4_subterm.count ix) (E4_subterm.Tree.subtree_count root)
          end;
          (* pre-order: a parent's path is a prefix of every descendant's and comes first *)
          let seen = Hashtbl.create 64 in
          List.iter
            (fun (e : E4_subterm.entry) ->
              let p = e.E4_subterm.prog_path in
              (match List.rev p with
              | [] -> ()
              | _ :: rev_parent ->
                let parent = List.rev rev_parent in
                if not (Hashtbl.mem seen parent) then order_ok := false);
              Hashtbl.replace seen p ())
            es;
          let g k = try Hashtbl.find per k with Not_found -> 0 in
          note "S1 %-16s bytes=%-6d subterms=%-4d eff=%-4d stmt=%-3d stmts=%-3d effs=%-2d action=%d"
            (Filename.remove_extension f) (String.length bytes) (List.length es) (g "eff")
            (g "stmt") (g "stmts") (g "effs") (g "action"))
      files;
    note "S1 %d golden programs, %d refused by the wire, %d subterms in all" !progs !refused
      !total;
    check
      (Printf.sprintf
         "S1 every subterm's own encoding equals the slice its entry names (%d programs, %d \
          subterms)"
         !progs !total)
      (!bad = 0 && !progs = 37 && !refused = 0);
    check "S3 the root entry is the whole program, at path ." !root_ok;
    check "S8 `entries` is a pre-order: a parent precedes every descendant" !order_ok

(* ---- S2, S7: every constructor of every family ---- *)

let test_every_constructor () =
  print_endline "-- E4_subterm: the child table over EVERY constructor (L-SUB-3, M3)";
  let bad = ref 0 and n = ref 0 in
  List.iter
    (fun (w, prog, path) ->
      incr n;
      let bytes = Eff_wire.encode_program prog in
      match E4_subterm.of_program_opt bytes with
      | None ->
        incr bad;
        Printf.printf "      the wire refused a witness program\n%!"
      | Some ix -> (
        match E4_subterm.at_prog_path ix path with
        | None ->
          incr bad;
          Printf.printf "      no entry at %s for %s/%d\n%!" (E4_subterm.path_to_string path)
            (E4_subterm.family_name (E4_subterm.Tree.family_of w))
            (E4_subterm.Tree.ctor_index w)
        | Some e ->
          let fam = E4_subterm.Tree.family_of w and ci = E4_subterm.Tree.ctor_index w in
          let where = Printf.sprintf "%s/%d" (E4_subterm.family_name fam) ci in
          if
            not
              (E4_subterm.family_eq e.E4_subterm.family fam && e.E4_subterm.ctor = ci
              && String.equal (E4_subterm.slice bytes e) (E4_subterm.Tree.encode w))
          then begin
            incr bad;
            Printf.printf "      %s: the entry is not the witness\n%!" where
          end;
          (* the arity of the row, against the value side *)
          let rows = E4_subterm.children fam ci in
          let value_children =
            let rec go k acc =
              if k > 5 then List.rev acc
              else
                match E4_subterm.Tree.child w k with
                | None -> List.rev acc
                | Some c -> go (k + 1) (c :: acc)
            in
            go 0 []
          in
          if List.length rows <> List.length value_children then begin
            incr bad;
            Printf.printf "      %s: table has %d children, Node.child has %d\n%!" where
              (List.length rows) (List.length value_children)
          end
          else
            List.iteri
              (fun k child ->
                let vidx = match List.nth rows k with v, _ -> v in
                match E4_subterm.at_prog_path ix (path @ [ k ]) with
                | None ->
                  incr bad;
                  Printf.printf "      %s: no entry for child %d\n%!" where k
                | Some ce ->
                  if not (String.equal (E4_subterm.slice bytes ce) (E4_subterm.Tree.encode child))
                  then begin
                    incr bad;
                    Printf.printf "      %s: child %d's slice is not its own bytes\n%!" where k
                  end;
                  let last = List.nth ce.E4_subterm.val_path (List.length ce.E4_subterm.val_path - 1) in
                  if last <> vidx then begin
                    incr bad;
                    Printf.printf "      %s: child %d has ValPath tail %d, the table says %d\n%!"
                      where k last vidx
                  end)
              value_children))
    embedded;
  note "S2 %d constructors: 24 eff + 6 stmt + 2 stmts + 2 effs + 16 action" !n;
  check "S2 every constructor of every family: the entry, its slice, its children, its ValPath"
    (!bad = 0 && !n = 50);
  (* the table's alphabet is the wire's alphabet, family for family *)
  check "S7 `children` covers exactly the constructors `Eff_types` declares"
    (E4_subterm.arity E4_subterm.Eff = 24
    && E4_subterm.arity E4_subterm.Stmt = 6
    && E4_subterm.arity E4_subterm.Stmts = 2
    && E4_subterm.arity E4_subterm.Effs = 2
    && E4_subterm.arity E4_subterm.Action = 16
    && List.for_all
         (fun f ->
           List.length (E4_subterm.family_ctor_names f) = E4_subterm.arity f
           && (* no row names a constructor the family does not have *)
           List.for_all
             (fun c -> E4_subterm.children f c = [])
             [ E4_subterm.arity f; E4_subterm.arity f + 1; -1 ])
         E4_subterm.families)

(* ---- S5, S6: the two path spaces ---- *)

let test_path_spaces () =
  print_endline "-- E4_subterm: ProgPath vs ValPath (L-SUB-2, amendment M5)";
  let divergent = ref [] in
  List.iter
    (fun f ->
      for c = 0 to E4_subterm.arity f - 1 do
        List.iteri
          (fun k (v, _) ->
            if v <> k then divergent := (E4_subterm.family_name f, c, k, v) :: !divergent)
          (E4_subterm.children f c)
      done)
    E4_subterm.families;
  let got = List.sort compare !divergent in
  let want =
    List.sort compare
      [ ("eff", 15, 0, 1); ("eff", 15, 1, 2); (* branch *)
        ("eff", 16, 0, 3); (* whileLoop *)
        ("eff", 23, 0, 1); ("eff", 23, 1, 2); (* choose *)
        ("stmt", 3, 0, 1); ("stmt", 3, 1, 2) (* ifElse *) ]
  in
  List.iter (fun (f, c, k, v) -> note "S5 %s ctor %d: program child %d is argument %d" f c k v) got;
  check
    "S5 the two path spaces differ at exactly branch, whileLoop, choose and ifElse — and \
     nowhere else"
    (got = want);
  let rt = ref true in
  List.iter
    (fun f ->
      for c = 0 to E4_subterm.arity f - 1 do
        List.iteri
          (fun k (v, _) ->
            if E4_subterm.val_of_prog f c k <> Some v then rt := false;
            if E4_subterm.prog_of_val f c v <> Some k then rt := false)
          (E4_subterm.children f c)
      done)
    E4_subterm.families;
  check "S6 `val_of_prog` and `prog_of_val` are inverse where both are defined" !rt;
  check "S6b a value argument that is not an addressed child has no program index"
    (E4_subterm.prog_of_val E4_subterm.Eff 15 0 = None
    && E4_subterm.prog_of_val E4_subterm.Eff 16 0 = None
    && E4_subterm.prog_of_val E4_subterm.Eff 16 1 = None
    && E4_subterm.prog_of_val E4_subterm.Eff 16 2 = None
    && E4_subterm.val_of_prog E4_subterm.Eff 0 0 = None)

(* ---- S4, S9-S11: cids, refusals, and the index as a function of the bytes ---- *)

let test_subterm_misc () =
  print_endline "-- E4_subterm: Cids, refusals, and the index as a function of the bytes";
  (* two occurrences of one subterm *)
  let prog = Eff_bind (Eff_scoped ea, Eff_scoped ea) in
  let bytes = Eff_wire.encode_program prog in
  let ix = E4_subterm.of_program bytes in
  let l = E4_subterm.at_prog_path ix [ 0 ] and r = E4_subterm.at_prog_path ix [ 1 ] in
  check "S4 two occurrences of one subterm share a Cid and differ in offset (SB3)"
    (match (l, r) with
    | Some a, Some b ->
      E4_addr.Addr.equal a.E4_subterm.cid b.E4_subterm.cid
      && a.E4_subterm.off <> b.E4_subterm.off
      && a.E4_subterm.len = b.E4_subterm.len
      && String.equal (E4_subterm.slice bytes a) (E4_subterm.slice bytes b)
    | _ -> false);
  check "S4b a Cid is sha256 of the slice and of nothing else"
    (match l with
    | Some a ->
      E4_addr.Addr.equal a.E4_subterm.cid (E4_subterm.cid_of_bytes (E4_subterm.slice bytes a))
    | None -> false);
  (* refusals *)
  let short = String.sub bytes 0 (String.length bytes - 1) in
  let trailing = bytes ^ "\000" in
  let empty = "" in
  check "S9 bytes that are not exactly one program are refused whole (SB7)"
    (E4_subterm.of_program_opt short = None
    && E4_subterm.of_program_opt trailing = None
    && E4_subterm.of_program_opt empty = None
    && (match E4_subterm.of_program short with
       | exception Invalid_argument _ -> true
       | _ -> false));
  (* the index is a function of the bytes *)
  let a = E4_subterm.of_program bytes and b = E4_subterm.of_program bytes in
  let same =
    List.for_all2
      (fun (x : E4_subterm.entry) (y : E4_subterm.entry) ->
        x.E4_subterm.off = y.E4_subterm.off
        && x.E4_subterm.len = y.E4_subterm.len
        && x.E4_subterm.prog_path = y.E4_subterm.prog_path
        && x.E4_subterm.val_path = y.E4_subterm.val_path
        && E4_addr.Addr.equal x.E4_subterm.cid y.E4_subterm.cid)
      (E4_subterm.entries a) (E4_subterm.entries b)
  in
  check "S10 building the index twice from one string is identical (SB8: it is a cache)" same;
  check "S11 `bytes` gives back the identity the index was derived from"
    (String.equal (E4_subterm.bytes a) bytes)

(* ============================================================================================
   3. the dependents index
   ============================================================================================ *)

(* The brute-force specification of DP5, recomputed here so that `of_node` is compared with
   something written separately rather than with itself. *)
let brute_deps (n : E4_node.t) : E4_addr.Addr.t list =
  List.map (fun (r : E4_addr.Ref.t) -> r.E4_addr.Ref.addr) (E4_node.checked_edges n)
  @ E4_shape.cids_of E4_shape.table n.E4_node.kind ~payload:n.E4_node.payload

let test_deps (b : built) =
  print_endline "-- E4_deps: the dependents index (DP1-DP7)";
  let bindings = E4_cas.nodes b.b_ro in
  note "D0 the store holds %d nodes (%d entry, %d job, 1 genesis schema)"
    (List.length bindings) (Array.length b.b_entries) (Array.length b.b_jobs);

  (* D2 / D4: of_node against the brute force *)
  let bad = ref 0 in
  List.iter
    (fun (_, nd) ->
      let got = E4_deps.of_node nd and want = brute_deps nd in
      if
        List.length got <> List.length want
        || not (List.for_all2 E4_addr.Addr.equal got want)
      then incr bad)
    bindings;
  check "D2 `of_node` is `checked_edges` then `E4_shape.cids_of`, node for node (DP5)"
    (!bad = 0);
  (* the Cid half is really exercised *)
  let job_deps =
    if Array.length b.b_jobs = 0 then []
    else
      match E4_cas.get_node b.b_ro b.b_jobs.(0) with
      | Some nd -> E4_deps.of_node nd
      | None -> []
  in
  check "D4 a `job` node contributes its three Cid fields, which no byte scan could see (R1)"
    (List.length job_deps = 4);

  (* D1: rebuild = incremental *)
  let t0 = Unix.gettimeofday () in
  let incr_ix = E4_deps.of_store b.b_ro in
  let t1 = Unix.gettimeofday () in
  let scan_ix, stop = E4_deps.rebuild_dir b.b_dir in
  let t2 = Unix.gettimeofday () in
  note "D1 incremental %.3f s (%.0f nodes/s), full scan %.3f s (%.0f nodes/s)" (t1 -. t0)
    (float_of_int (List.length bindings) /. Float.max 1e-9 (t1 -. t0))
    (t2 -. t1)
    (float_of_int (List.length bindings) /. Float.max 1e-9 (t2 -. t1));
  note "D1 %d dependees, %d edges; the scan stopped at %s" (E4_deps.cardinal scan_ix)
    (E4_deps.edges scan_ix) (E4_pack.scan_stop_to_string stop);
  (match E4_deps.diff incr_ix scan_ix with
  | None -> ()
  | Some m -> Printf.printf "      %s\n%!" m);
  check
    (Printf.sprintf "D1 rebuild = incremental over a %d-node store (dependee for dependee, \
                     dependent for dependent)"
       (List.length bindings))
    (E4_deps.equal incr_ix scan_ix
    && E4_deps.cardinal scan_ix > 0
    && match stop with E4_pack.Eof -> true | _ -> false);

  (* the index against a brute-force recomputation of the whole thing *)
  let brute = Hashtbl.create 1024 in
  List.iter
    (fun (at, nd) ->
      List.iter
        (fun dep ->
          let key = E4_addr.Addr.hex dep in
          let prev = try Hashtbl.find brute key with Not_found -> [] in
          let by = E4_addr.Ref.make nd.E4_node.kind at in
          (* the index is idempotent on a pair already present (E4_index IX8), and a node may
             well name one address twice — `entry 2` names `entry 1` as both of its refs *)
          if not (List.exists (E4_addr.Ref.equal by) prev) then
            Hashtbl.replace brute key (by :: prev))
        (brute_deps nd))
    bindings;
  let all_ok = ref true in
  E4_deps.iter scan_ix (fun dep bys ->
      let want = List.rev (try Hashtbl.find brute (E4_addr.Addr.hex dep) with Not_found -> []) in
      if
        List.length want <> List.length bys
        || not (List.for_all2 E4_addr.Ref.equal want bys)
      then all_ok := false);
  check "D5 the whole index equals a brute-force recomputation, in discovery order"
    (!all_ok && E4_deps.cardinal scan_ix = Hashtbl.length brute);

  (* D3: persistence *)
  let held = E4_deps.empty in
  let d0 = addr_n 1 in
  let grown =
    let r = ref held in
    for i = 0 to 99 do
      r := E4_deps.add !r ~dep:d0 ~by:(E4_addr.Ref.make E4_kind.Entry (addr_n (1000 + i)))
    done;
    !r
  in
  check "D3 persistent: the value held before a hundred additions still answers as it did"
    (E4_deps.cardinal held = 0
    && E4_deps.find held d0 = []
    && E4_deps.cardinal grown = 1
    && List.length (E4_deps.find grown d0) = 100);
  check "D3b `add` of a pair already present is idempotent"
    (let once = E4_deps.add E4_deps.empty ~dep:d0 ~by:(E4_addr.Ref.make E4_kind.Entry d0) in
     let twice = E4_deps.add once ~dep:d0 ~by:(E4_addr.Ref.make E4_kind.Entry d0) in
     E4_deps.edges twice = 1);

  (* D6: not an edge *)
  let reach_before = List.map (fun (at, _) -> E4_cas.reachable b.b_ro at) bindings in
  let closure_before =
    E4_cas.closure b.b_ro (E4_addr.Ref.make E4_kind.Entry b.b_entries.(Array.length b.b_entries - 1))
  in
  ignore (E4_deps.of_store b.b_ro);
  let reach_after = List.map (fun (at, _) -> E4_cas.reachable b.b_ro at) bindings in
  let closure_after =
    E4_cas.closure b.b_ro (E4_addr.Ref.make E4_kind.Entry b.b_entries.(Array.length b.b_entries - 1))
  in
  check "D6 NOT AN EDGE (M1): `reachable` and `closure` answer the same with the index built"
    (reach_before = reach_after
    && List.length closure_before = List.length closure_after
    && List.for_all2
         (fun (x : E4_cas.binding) (y : E4_cas.binding) ->
           E4_addr.Addr.equal x.E4_cas.addr y.E4_cas.addr)
         closure_before closure_after);
  note "D6 the closure of the last entry is %d bindings" (List.length closure_before);
  check "D6b the dependees are sorted and unique, so two indexes compare without an order"
    (let ds = E4_deps.dependees scan_ix in
     let rec sorted = function
       | a :: (b :: _ as rest) -> E4_addr.Addr.compare a b < 0 && sorted rest
       | _ -> true
     in
     sorted ds)

let test_deps_truncated () =
  print_endline "-- E4_deps: a truncated pack (DP6)";
  let b = build_store ~n:60 ~jobs:2 in
  let full, stop_full = E4_deps.rebuild_dir b.b_dir in
  E4_cas.close b.b_store;
  let seg = E4_pack.seg_path ~dir:b.b_dir 0 in
  let len = (Unix.stat seg).Unix.st_size in
  let fd = Unix.openfile seg [ Unix.O_RDWR ] 0o644 in
  Unix.ftruncate fd (len - 20);
  Unix.close fd;
  let cut, stop_cut = E4_deps.rebuild_dir b.b_dir in
  note "D7 whole: %d dependees, stop %s; truncated: %d dependees, stop %s"
    (E4_deps.cardinal full)
    (E4_pack.scan_stop_to_string stop_full)
    (E4_deps.cardinal cut)
    (E4_pack.scan_stop_to_string stop_cut);
  check "D7 a truncated pack stops the scan and the verdict comes back beside the index"
    ((match stop_full with E4_pack.Eof -> true | _ -> false)
    && (match stop_cut with E4_pack.Eof -> false | _ -> true)
    && E4_deps.cardinal cut <= E4_deps.cardinal full
    && not (E4_deps.equal full cut));
  rm_rf b.b_dir

(* ============================================================================================
   4. mutation checks — a test nobody can break is not a test
   ============================================================================================ *)

let test_mutations (b : built) =
  print_endline "-- mutation checks (cas-design §11 commit 9)";
  (* X1: the slice law must go red when the offset is wrong. *)
  let bytes = Eff_wire.encode_program (Eff_bind (ea, eb)) in
  let ix = E4_subterm.of_program bytes in
  let e = match E4_subterm.at_prog_path ix [ 1 ] with Some x -> x | None -> assert false in
  let wrong = { e with E4_subterm.off = e.E4_subterm.off - 1 } in
  check "X1 the slice law is falsifiable: one byte off, and the slice is not the subterm"
    (e.E4_subterm.off > 0
    && (not (String.equal (E4_subterm.slice bytes wrong) (E4_subterm.slice bytes e)))
    &&
    match E4_subterm.Tree.at_ (Option.get (E4_subterm.Tree.of_bytes bytes)) [ 1 ] with
    | Some nd -> not (String.equal (E4_subterm.slice bytes wrong) (E4_subterm.Tree.encode nd))
    | None -> false);
  (* X2: flip one byte of the program and the index changes. *)
  let flipped = Bytes.of_string bytes in
  let at = String.length bytes - 1 in
  Bytes.set flipped at (Char.chr (Char.code (Bytes.get flipped at) lxor 1));
  let f = Bytes.to_string flipped in
  check "X2 the index is a function of the bytes: one bit flipped and it is another index"
    (match E4_subterm.of_program_opt f with
    | None -> true
    | Some ix2 ->
      not
        (List.for_all2
           (fun (x : E4_subterm.entry) (y : E4_subterm.entry) ->
             E4_addr.Addr.equal x.E4_subterm.cid y.E4_subterm.cid)
           (E4_subterm.entries ix) (E4_subterm.entries ix2)));
  (* X3: the child table is falsifiable — a wrong ValPath for `branch` picks a term frame. *)
  check "X3 the ValPath of `branch` is falsifiable: argument 0 is a term, not an eff"
    (let p = Eff_wire.encode_program (Eff_branch (t_unit, ea, eb)) in
     let i = E4_subterm.of_program p in
     match E4_subterm.at_prog_path i [ 0 ] with
     | None -> false
     | Some ent ->
       String.equal (E4_subterm.slice p ent) (Eff_wire.encode_eff ea)
       && (* the naive "child i = argument i" would have taken the term *)
       not (String.equal (E4_subterm.slice p ent) (Eff_wire.encode_term t_unit)));
  (* X4: the poison test is falsifiable — a store whose pack really is damaged fails verify. *)
  let d = fresh_dir () in
  let st = E4_cas.open_rw ~dir:d E4_cas.default_opts in
  let g = node E4_kind.Schema E4_node.zero_digest (v_ctor 0 [ v_nat 1 ]) in
  ignore (E4_cas.put st g);
  let n1 = node E4_kind.Entry (E4_addr.Addr.bytes (E4_node.address g)) (v_ctor 0 [ v_nat 5 ]) in
  ignore (E4_cas.put st n1);
  E4_cas.commit st;
  E4_cas.close st;
  let seg = E4_pack.seg_path ~dir:d 0 in
  let raw = Bytes.of_string (read_file seg) in
  let pos = Bytes.length raw - 6 in
  Bytes.set raw pos (Char.chr (Char.code (Bytes.get raw pos) lxor 0xff));
  let oc = open_out_bin seg in
  output_bytes oc raw;
  close_out oc;
  let damaged =
    match E4_cas.open_ro ~dir:d with
    | ro -> ( match E4_cas.verify ro with Ok () -> false | Error _ -> true)
    | exception _ -> true
  in
  check "X4 the CA6 test is falsifiable: a pack that really is damaged fails `verify`" damaged;
  rm_rf d;
  (* X5: the dependents comparison is falsifiable. *)
  let a = E4_deps.of_store b.b_ro in
  let a' = E4_deps.add a ~dep:(addr_n 7) ~by:(E4_addr.Ref.make E4_kind.Entry (addr_n 8)) in
  check "X5 `E4_deps.equal` is falsifiable: one added edge and the two differ"
    ((not (E4_deps.equal a a')) && E4_deps.diff a a' <> None)

(* ============================================================================================
   main
   ============================================================================================ *)

let () =
  Printf.printf "test_cache — lane P7 (E4_cache, E4_subterm, E4_deps)\n%!";
  test_bound ();
  test_clock ();
  test_accounting ();
  test_replace ();
  let b = build_store ~n:600 ~jobs:8 in
  test_identity b;
  test_poison b;
  test_decoded b;
  test_slice_goldens ();
  test_every_constructor ();
  test_path_spaces ();
  test_subterm_misc ();
  (* the dependents index gets its own, larger store: DP1 is a 10 000-node claim *)
  let big = build_store ~n:9_990 ~jobs:9 in
  test_deps big;
  test_mutations b;
  E4_cas.close big.b_store;
  E4_cas.close b.b_store;
  test_deps_truncated ();
  rm_rf root_dir;
  if !failures = 0 then Printf.printf "== ALL PASS: 0 failure(s) ==\n%!"
  else Printf.printf "== FAIL: %d failure(s) ==\n%!" !failures;
  exit (if !failures = 0 then 0 else 1)
