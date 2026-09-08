(* test_checkpoint.ml — lane P6: E4_chunk and E4_checkpoint.

   What it checks (docs/research/2026-09-08-engine-a2-persistence.md §1.9, §2.3, §4.4, §4.5 B7;
   the lane's acceptance):

     1  E4_chunk: determinism, reassembly = identity, the size bounds CH2, the ONE-BYTE
        INSERTION LAW CH6 (nothing before the edit moves; at most two chunks after it differ)
        with the mutation check that fixed-size chunking FAILS the same property, and the
        parameter refusals.
     2  The manifest: `encode`/`decode` exactness, the content-defined group cut CH7, the
        nesting CH8, `flatten` as the inverse of the build, and `fold_chunks` (CH9).
     3  The checkpoint node: `encode`/`decode` over all three image forms, exactness, and the
        byte table of e4_checkpoint.mli read back field by field.
     4  The store: write/read round trips whole and chunked, CP7's verification, CP2's
        `Dangling` for an unstored job, LAW LOG-REL (two jobs one content: the payloads differ
        in the job's 32 bytes and in nothing else; two positions: two addresses; two store
        layouts: one address), the `prev` chain and CP3's `Fork`, the cycle refusal, and the
        mutation check that a flipped byte inside a stored chunk makes `read` refuse.
     5  CP9 / risk R8: `closure_streaming` visits exactly `E4_cas.closure`'s addresses,
        children first, without materialising the image.
     6  CP10: an ephemeral checkpoint files no node.
     7  CP11: `image_of_machine` / `machine_of_image` round-trip exactly on real `Fast`
        machines, and the decoder is exact.
     8  A2 §4.4 and bench cell B7 on the real thing: 64 consecutive checkpoints of the
        chain-of-refMake run at n = 2000, with chunking on and off, printing the per-checkpoint
        delta and the cumulative store bytes of both.

   Writes only under $E4_CHECKPOINT_TMP (default: the system temp directory) and removes what
   it made.

   Run: cd ocaml && dune build @engine/cas/runtest --force *)

open Effect4_engine_cas
open Effect4_engine

module E = Eff_types
module En = E4_engine.Fast
module Ck = E4_checkpoint
module Ch = E4_chunk

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n%!" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf fmt

(* ============================================================ the sandbox *)

let root_dir =
  let base =
    try Sys.getenv "E4_CHECKPOINT_TMP" with Not_found -> Filename.get_temp_dir_name ()
  in
  let d =
    Filename.concat base
      (Printf.sprintf "e4ckpt-%d-%d" (Unix.getpid ()) (int_of_float (Unix.time ())))
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

(* ============================================================ frames, by hand *)

let f_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let f_bytes b = E4_be.framed Eff_frame.tag_bytes b
let f_list xs = E4_be.framed Eff_frame.tag_list (String.concat "" xs)
let f_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (f_nat i :: args))

let f_ref (r : E4_addr.Ref.t) =
  E4_be.framed Eff_frame.tag_ref
    (String.make 1 (Char.chr (E4_kind.byte r.E4_addr.Ref.kind))
    ^ E4_addr.Addr.bytes r.E4_addr.Ref.addr)

(* ============================================================ a deterministic image *)

(* An LCG, so every number below is reproducible from this file alone. *)
let rng_state = ref 0

let rng_seed s = rng_state := s land 0x3FFFFFFFFFFFFFFF

let rng () =
  rng_state := ((!rng_state * 25214903917) + 11) land 0x3FFFFFFFFFFFFFFF;
  !rng_state lsr 17

let rng_int n = rng () mod n

(* Two images of `cells` records laid back to back — the byte order of a hand Image over a
   persistent list, which is A2 §6.3's `p_share` shape.

   `cell_image`'s filler is (i*31 + j*17) mod 90, so within a cell it has PERIOD 90: there are
   only 90 distinct byte windows of any length, and a rolling hash has that many chances to
   find a boundary however wide its window is.  That is the adversarial case for content-
   defined chunking and it is measured below, deliberately, as a limitation and not as a gate.
   `records_image`'s filler is an LCG stream, which is what a real machine image's varied
   content looks like to a rolling hash; it is what CH6's gate runs on. *)
let cell_image ~cells ~cell =
  let b = Buffer.create (cells * cell) in
  for i = 0 to cells - 1 do
    Buffer.add_string b (Printf.sprintf "cell:%08d:" i);
    let filler = cell - 15 in
    for j = 0 to filler - 1 do
      Buffer.add_char b (Char.chr (33 + ((i * 31) + (j * 17)) mod 90))
    done;
    Buffer.add_char b '\n'
  done;
  Buffer.contents b

let records_image ~cells ~cell =
  let st = ref 987654321 in
  let nxt () =
    st := ((!st * 1103515245) + 12345) land 0x3FFFFFFF;
    33 + ((!st lsr 13) mod 90)
  in
  let b = Buffer.create (cells * cell) in
  for i = 0 to cells - 1 do
    Buffer.add_string b (Printf.sprintf "cell:%08d:" i);
    for _ = 1 to cell - 15 do
      Buffer.add_char b (Char.chr (nxt ()))
    done;
    Buffer.add_char b '\n'
  done;
  Buffer.contents b

let insert_at s k x = String.sub s 0 k ^ x ^ String.sub s k (String.length s - k)
let delete_at s k n = String.sub s 0 k ^ String.sub s (k + n) (String.length s - k - n)

(* fixed-size chunking: the plan A2 §4.4 refuses.  It is here as the mutation check that
   CH6's property has teeth. *)
let fixed_cut size s =
  let n = String.length s in
  let rec go off acc = if off >= n then List.rev acc else go (off + size) ((off, min size (n - off)) :: acc) in
  go 0 []

let chunk_set cuts s =
  let h = Hashtbl.create 256 in
  List.iter (fun (o, l) -> Hashtbl.replace h (String.sub s o l) ()) cuts;
  h

let novel cuts_new s_new tbl_old =
  List.fold_left
    (fun acc (o, l) -> if Hashtbl.mem tbl_old (String.sub s_new o l) then acc else acc + 1)
    0 cuts_new

(* How many BOUNDARIES moved, which is what CH6(b) is a law about.  Boundaries at or before
   the edit are compared directly (CH6(a)); after it, a boundary of the longer string is
   shifted back by the inserted byte before the two sets are compared.  A destroyed boundary
   and the one that replaced it are two moves, and three chunks can be new for two moves. *)
let boundaries_moved cuts_old cuts_new k =
  let after l shift =
    List.filter_map (fun (o, _) -> if o > k then Some (o - shift) else None) l
  in
  let ob = after cuts_old 0 and nb = after cuts_new 1 in
  let t = Hashtbl.create 64 and t2 = Hashtbl.create 64 in
  List.iter (fun o -> Hashtbl.replace t o ()) ob;
  List.iter (fun o -> Hashtbl.replace t2 o ()) nb;
  List.length (List.filter (fun o -> not (Hashtbl.mem t o)) nb)
  + List.length (List.filter (fun o -> not (Hashtbl.mem t2 o)) ob)

(* ============================================================ 1. the chunker *)

let p_small = { Ch.avg = 1024; min = 256; max = 4096 }

let chunker () =
  print_endline "";
  print_endline "== 1. E4_chunk: cutting ==";
  let img = records_image ~cells:2000 ~cell:512 in
  let n = String.length img in
  let cuts = Ch.cut p_small img in
  note "  image %d B, %d chunks, mean %d B\n" n (List.length cuts) (n / max 1 (List.length cuts));
  check "CH1 cut is deterministic (same bytes, same cut)" (Ch.cut p_small img = cuts);
  check "CH1 cut is a function of the bytes, not the string identity"
    (Ch.cut p_small (String.sub img 0 n ^ "") = cuts);
  check "CH1 reassembly is the identity: concat (pieces s) = s"
    (String.concat "" (Ch.pieces p_small img) = img);
  check "CH1 the cut covers the string exactly, in order"
    (let ok = ref true and at = ref 0 in
     List.iter (fun (o, l) -> if o <> !at || l <= 0 then ok := false; at := o + l) cuts;
     !ok && !at = n);
  check "CH2 every chunk but the last is in [min, max]"
    (let rec go = function
       | [] | [ _ ] -> true
       | (_, l) :: rest -> l >= p_small.Ch.min && l <= p_small.Ch.max && go rest
     in
     go cuts);
  check "CH2 the last chunk is non-empty and at most max"
    (match List.rev cuts with (_, l) :: _ -> l > 0 && l <= p_small.Ch.max | [] -> false);
  check "CH2 the empty image cuts to nothing" (Ch.cut p_small "" = []);
  check "CH2 an image below min is one chunk" (List.length (Ch.cut p_small (String.make 100 'x')) = 1);
  check "the window is smaller than min (what makes CH6 hold)" (Ch.window < p_small.Ch.min);
  check "params_ok refuses min <= window" (not (Ch.params_ok { Ch.avg = 1024; min = 8; max = 4096 }));
  check "params_ok refuses an avg that is not a power of two"
    (not (Ch.params_ok { Ch.avg = 1000; min = 256; max = 4096 }));
  check "params_ok refuses max < avg" (not (Ch.params_ok { Ch.avg = 4096; min = 256; max = 1024 }));
  check "params_ok accepts the default" (Ch.params_ok Ch.default);
  check "cut raises Invalid_argument on refused params"
    (match Ch.cut { Ch.avg = 1000; min = 8; max = 16 } img with
     | exception Invalid_argument _ -> true
     | _ -> false);
  (* ---- CH6: the one-byte insertion law ---- *)
  rng_seed 20260908;
  let tbl = chunk_set cuts img in
  let worst_cdc = ref 0 and worst_fixed = ref 0 and prefix_ok = ref true and trials = 200 in
  let worst_k = ref 0 and worst_moved = ref 0 in
  let hist = Array.make 6 0 in
  for _ = 1 to trials do
    let k = 1 + rng_int (n - 2) in
    let s' = insert_at img k "!" in
    let c' = Ch.cut p_small s' in
    (* (a) nothing at or before the edit moves *)
    let old_b = List.filter (fun (o, _) -> o <= k) cuts |> List.map fst in
    let new_b = List.filter (fun (o, _) -> o <= k) c' |> List.map fst in
    let common = List.filter (fun o -> o <= k) old_b in
    if not (List.for_all (fun o -> List.mem o new_b) common) then prefix_ok := false;
    (* (b) resynchronisation *)
    let d = novel c' s' tbl in
    if d > !worst_cdc then (worst_cdc := d; worst_k := k);
    let m = boundaries_moved cuts c' k in
    if m > !worst_moved then worst_moved := m;
    hist.(min m 5) <- hist.(min m 5) + 1;
    let fx = fixed_cut 1024 img in
    let ftbl = chunk_set fx img in
    let fd = novel (fixed_cut 1024 s') s' ftbl in
    if fd > !worst_fixed then worst_fixed := fd
  done;
  note "  %d one-byte insertions (worst at offset %d): worst boundaries moved %d; worst new chunks — content-defined %d, fixed 1 KB %d\n"
    trials !worst_k !worst_moved !worst_cdc !worst_fixed;
  note "  boundaries moved, over %d trials: 0->%d  1->%d  2->%d  3->%d  4->%d  5+->%d\n" trials
    hist.(0) hist.(1) hist.(2) hist.(3) hist.(4) hist.(5);
  check "CH6(a) every boundary at or before a one-byte insertion is unchanged" !prefix_ok;
  check "CH6(b) a one-byte insertion moves boundaries only locally (at most 3)"
    (!worst_moved <= 3);
  check "CH6(b) at most three chunks are rewritten" (!worst_cdc <= 3);
  check "MUTATION: fixed-size chunking fails CH6(b) — the property has teeth"
    (!worst_fixed > 100 * max 1 !worst_cdc);
  (* deletions too *)
  rng_seed 991;
  let worst_del = ref 0 in
  for _ = 1 to 100 do
    let k = 1 + rng_int (n - 4) in
    let s' = delete_at img k 1 in
    let d = novel (Ch.cut p_small s') s' tbl in
    if d > !worst_del then worst_del := d
  done;
  note "  100 one-byte deletions: worst new chunks %d\n" !worst_del;
  check "CH6(b) a one-byte deletion makes at most three new chunks" (!worst_del <= 3);
  (* The adversarial case, measured and NOT hidden: an image whose filler has period 90 gives
     a rolling hash only 90 distinct windows to find a boundary in, however wide its window
     is.  Candidates are then either far too dense or far too rare, most cuts are min- or
     max-forced — which is position-determined, not content-determined — and an insertion
     re-phases the lattice downstream.  Content-defined chunking still beats fixed-size
     chunking by a wide margin there, and that is what is gated. *)
  rng_seed 4242;
  let per = cell_image ~cells:2000 ~cell:512 in
  let pn = String.length per in
  let pcuts = Ch.cut p_small per in
  let ptbl = chunk_set pcuts per in
  let pworst = ref 0 and pfixed = ref 0 in
  let pfx = fixed_cut 1024 per in
  let pftbl = chunk_set pfx per in
  for _ = 1 to 100 do
    let k = 1 + rng_int (pn - 2) in
    let s' = insert_at per k "!" in
    let d = novel (Ch.cut p_small s') s' ptbl in
    if d > !pworst then pworst := d;
    let fd = novel (fixed_cut 1024 s') s' pftbl in
    if fd > !pfixed then pfixed := fd
  done;
  note "  LIMITATION, period-90 image (%d chunks, mean %d B): worst new chunks — content-defined %d, fixed 1 KB %d\n"
    (List.length pcuts) (pn / max 1 (List.length pcuts)) !pworst !pfixed;
  check "on adversarial period-90 content, content-defined chunking still beats fixed-size"
    (!pworst * 4 < !pfixed);
  (* an APPEND touches only the tail *)
  let appended = img ^ "one more cell\n" in
  check "an append rewrites at most one chunk"
    (novel (Ch.cut p_small appended) appended tbl <= 1);
  (* the default parameters on a large image *)
  let big = records_image ~cells:4096 ~cell:1024 in
  let bc = Ch.cut Ch.default big in
  note "  default params on %d B: %d chunks, mean %d B\n" (String.length big) (List.length bc)
    (String.length big / max 1 (List.length bc));
  check "the default params hold CH2 on a 4 MB image"
    (List.for_all (fun (_, l) -> l <= Ch.default.Ch.max) bc
    && (match List.rev bc with (_, l) :: rest -> l > 0 && List.for_all (fun (_, l) -> l >= Ch.default.Ch.min) rest | [] -> false));
  check "the default params reassemble" (String.concat "" (Ch.pieces Ch.default big) = big)

(* ============================================================ 2. the manifest *)

let some_ref kind i =
  E4_addr.Ref.make kind (E4_addr.Addr.of_digest (E4_sha256.digest (string_of_int i)))

let manifest () =
  print_endline "";
  print_endline "== 2. E4_chunk: the manifest ==";
  let refs = List.init 40 (some_ref E4_kind.Chunk) in
  let leaf = Ch.Leaf refs in
  let inter = Ch.Interior (List.init 7 (some_ref E4_kind.Manifest)) in
  check "the leaf manifest round-trips" (Ch.decode_manifest (Ch.encode_manifest leaf) = Some leaf);
  check "the interior manifest round-trips"
    (Ch.decode_manifest (Ch.encode_manifest inter) = Some inter);
  check "a trailing byte is refused" (Ch.decode_manifest (Ch.encode_manifest leaf ^ "\000") = None);
  check "a truncated manifest is refused"
    (let b = Ch.encode_manifest leaf in
     Ch.decode_manifest (String.sub b 0 (String.length b - 1)) = None);
  check "a leaf whose refs are at the wrong kind is refused"
    (Ch.decode_manifest (f_ctor 0 [ f_list [ f_ref (some_ref E4_kind.Manifest 1) ] ]) = None);
  check "an interior whose refs are at the wrong kind is refused"
    (Ch.decode_manifest (f_ctor 1 [ f_list [ f_ref (some_ref E4_kind.Chunk 1) ] ]) = None);
  check "an unknown ctor index is refused"
    (Ch.decode_manifest (f_ctor 2 [ f_list [] ]) = None);
  check "a non-list body is refused" (Ch.decode_manifest (f_ctor 0 [ f_nat 3 ]) = None);
  check "the empty leaf round-trips" (Ch.decode_manifest (Ch.encode_manifest (Ch.Leaf [])) = Some (Ch.Leaf []));
  (* CH7: the content-defined group cut *)
  let many = List.init 5000 (some_ref E4_kind.Chunk) in
  let g = Ch.groups_default in
  let gs = Ch.group_cut g many in
  let sizes = List.map List.length gs in
  note "  5000 refs -> %d groups, sizes min %d max %d mean %d\n" (List.length gs)
    (List.fold_left min max_int sizes) (List.fold_left max 0 sizes)
    (5000 / max 1 (List.length gs));
  check "CH7 the groups concatenate back to the ref list" (List.concat gs = many);
  check "CH7 every group but the last is within [g_min, g_max]"
    (let rec go = function
       | [] | [ _ ] -> true
       | x :: rest -> List.length x >= g.Ch.g_min && List.length x <= g.Ch.g_max && go rest
     in
     go gs);
  check "CH7 the group cut is deterministic" (Ch.group_cut g many = gs);
  check "CH7 inserting one ref changes at most two groups"
    (let many' = List.concat [ List.filteri (fun i _ -> i < 2500) many; [ some_ref E4_kind.Chunk 999999 ];
                               List.filteri (fun i _ -> i >= 2500) many ] in
     let gs' = Ch.group_cut g many' in
     let tbl = Hashtbl.create 64 in
     List.iter (fun x -> Hashtbl.replace tbl x ()) gs;
     List.fold_left (fun a x -> if Hashtbl.mem tbl x then a else a + 1) 0 gs' <= 2)

(* ============================================================ 3. the checkpoint node *)

let addr_of i = E4_addr.Addr.of_digest (E4_sha256.digest ("addr" ^ string_of_int i))

let sample_cp image =
  { Ck.job = E4_addr.Ref.make E4_kind.Job (addr_of 1);
    position = 4321;
    tape_prefix = Some (E4_addr.Ref.make E4_kind.Tape (addr_of 2));
    prev = Some (E4_addr.Ref.make E4_kind.Checkpoint (addr_of 3));
    engine = addr_of 4;
    image_length = 17;
    image }

let node_bytes () =
  print_endline "";
  print_endline "== 3. E4_checkpoint: the byte table ==";
  let forms =
    [ ("whole", Ck.Whole "seventeen bytes!!");
      ("chunked", Ck.Chunked (List.init 3 (some_ref E4_kind.Chunk)));
      ("manifested", Ck.Manifested (some_ref E4_kind.Manifest 9)) ]
  in
  List.iter
    (fun (name, image) ->
      let cp = sample_cp image in
      check (Printf.sprintf "the %s form round-trips" name) (Ck.decode (Ck.encode cp) = Some cp);
      check (Printf.sprintf "the %s form refuses a trailing byte" name)
        (Ck.decode (Ck.encode cp ^ "\000") = None);
      check (Printf.sprintf "the %s form refuses a truncation" name)
        (let b = Ck.encode cp in
         Ck.decode (String.sub b 0 (String.length b - 1)) = None))
    forms;
  let cp = sample_cp (Ck.Whole "seventeen bytes!!") in
  let bare = { cp with Ck.tape_prefix = None; prev = None } in
  check "the optional fields round-trip as none" (Ck.decode (Ck.encode bare) = Some bare);
  check "a job ref at the wrong kind is refused"
    (Ck.decode (Ck.encode { cp with Ck.job = E4_addr.Ref.make E4_kind.Tape (addr_of 1) }) = None);
  check "the payload begins with ctor 0 and the job ref, in that order"
    (let b = Ck.encode cp in
     let inner = f_ref cp.Ck.job in
     String.length b > 9 + String.length inner
     && Char.code b.[0] = Eff_frame.tag_ctor
     && String.sub b (9 + String.length (f_nat 0)) (String.length inner) = inner);
  check "`engine` is a bytes frame, so the edge scan treats it as a leaf (D5, risk R1)"
    (let n = Ck.node ~spec:(addr_of 5) cp in
     let refs = E4_node.scan_refs n.E4_node.payload in
     List.length refs = 3
     && not (List.exists (fun (r : E4_addr.Ref.t) -> E4_addr.Addr.equal r.E4_addr.Ref.addr cp.Ck.engine) refs));
  check "the pending schema is a genesis: kind schema, the zero spec"
    (E4_kind.equal Ck.schema_node.E4_node.kind E4_kind.Schema
    && Ck.schema_node.E4_node.spec = E4_node.zero_digest
    && E4_node.is_genesis Ck.schema_node);
  check "the pending marker is on" (Ck.pending && Ck.image_version = 0)

(* ============================================================ the store fixtures *)

let opts = { E4_cas.default_opts with E4_cas.index_slots = 1 lsl 14 }

let put_ok st n =
  match E4_cas.put st n with
  | Ok (_, a) -> a
  | Error e -> failwith ("put refused: " ^ E4_cas.admission_word e)

let job_node ~spec tag =
  E4_node.make ~version:0 ~kind:E4_kind.Job ~spec:(E4_addr.Addr.bytes spec)
    ~payload:(f_ctor 0 [ f_bytes tag ])

(* a store with the pending schema and one job filed *)
let store_with_job ?(tag = "job-a") dir =
  let st = E4_cas.open_rw ~dir opts in
  let spec = Ck.ensure_schema st in
  let job = put_ok st (job_node ~spec tag) in
  E4_cas.commit st;
  (st, spec, job)

(* ============================================================ 4. write and read *)

let round_trips () =
  print_endline "";
  print_endline "== 4. E4_checkpoint: write, read, LOG-REL, the chain ==";
  let dir = fresh_dir () in
  let st, _spec, job = store_with_job dir in
  let small = cell_image ~cells:8 ~cell:128 in
  let big = cell_image ~cells:4000 ~cell:512 in
  (* whole *)
  let a1 =
    match Ck.write st ~job ~position:0 ~machine_image:small ~prev:None () with
    | Ok a -> a
    | Error e -> failwith (Ck.write_error_word e)
  in
  let ro = E4_cas.read_only st in
  check "a small image is stored Whole"
    (match Ck.read ro a1 with Ok ({ Ck.image = Ck.Whole _; _ }, _) -> true | _ -> false);
  check "CP5 read gives the image back byte for byte (whole)"
    (match Ck.read ro a1 with Ok (_, img) -> img = small | _ -> false);
  (* chunked, through the manifest *)
  let w2 =
    match
      Ck.write_counted st ~job ~position:1 ~machine_image:big ~prev:(Some a1) ~threshold:0 ()
    with
    | Ok w -> w
    | Error e -> failwith (Ck.write_error_word e)
  in
  let ro = E4_cas.read_only st in
  note "  chunked: %d B image, %d chunks (%d fresh, %d dup), %d manifest nodes, payload %d B\n"
    w2.Ck.image_bytes_written w2.Ck.chunks_cut w2.Ck.chunks_fresh w2.Ck.chunks_dup
    w2.Ck.manifest_nodes w2.Ck.payload_bytes;
  check "a large image is stored through a manifest"
    (match Ck.read ro w2.Ck.addr with
     | Ok ({ Ck.image = Ck.Manifested _; _ }, _) -> true
     | _ -> false);
  check "CP5 read gives the image back byte for byte (chunked)"
    (match Ck.read ro w2.Ck.addr with Ok (_, img) -> img = big | _ -> false);
  check "the checkpoint's payload is small and constant: the image is not inside it"
    (w2.Ck.payload_bytes < 400);
  check "CH8 flatten is the inverse of the build"
    (match Ck.read ro w2.Ck.addr with
     | Ok ({ Ck.image = Ck.Manifested r; _ }, _) -> (
       match Ch.flatten ro r with
       | Some refs ->
         List.length refs = w2.Ck.chunks_cut && Ch.reassemble ro refs = Some big
       | None -> false)
     | _ -> false);
  check "CH9 fold_chunks reassembles one chunk at a time"
    (match Ck.read ro w2.Ck.addr with
     | Ok ({ Ck.image = Ck.Manifested r; _ }, _) ->
       Ch.fold_chunks ro r ~init:0 ~f:(fun a s -> a + String.length s) = Some (String.length big)
     | _ -> false);
  check "the one-level form is available and reads back"
    (match Ck.write st ~job ~position:1 ~machine_image:big ~prev:(Some a1) ~threshold:0
             ~manifest:false ~head:false () with
     | Ok a -> (
       let ro = E4_cas.read_only st in
       match Ck.read ro a with Ok ({ Ck.image = Ck.Chunked _; _ }, img) -> img = big | _ -> false)
     | Error _ -> false);
  (* read_parts, the prompt's shape *)
  check "read_parts answers (job, position, prev, image)"
    (let ro = E4_cas.read_only st in
     match Ck.read_parts ro w2.Ck.addr with
     | Ok (j, p, pv, img) ->
       E4_addr.Addr.equal j job && p = 1 && pv = Some a1 && img = big
     | Error _ -> false);
  (* CP2: an unstored job *)
  check "CP2 a checkpoint whose job is not stored is refused Dangling by the STORE"
    (match
       Ck.write st ~job:(addr_of 77) ~position:0 ~machine_image:small ~prev:None ()
     with
     | Error (Ck.Refused (E4_cas.Dangling a)) -> E4_addr.Addr.equal a (addr_of 77)
     | _ -> false);
  check "CP2 a checkpoint whose prev is not stored is refused Dangling"
    (match
       Ck.write st ~job ~position:9 ~machine_image:small ~prev:(Some (addr_of 78)) ~head:false ()
     with
     | Error (Ck.Refused (E4_cas.Dangling _)) -> true
     | _ -> false);
  E4_cas.close st;
  (* ---- LAW LOG-REL ---- *)
  let d2 = fresh_dir () in
  let st2, spec2, job_a = store_with_job ~tag:"job-a" d2 in
  let job_b = put_ok st2 (job_node ~spec:spec2 "job-b") in
  E4_cas.commit st2;
  let img = cell_image ~cells:64 ~cell:256 in
  let mk j pos =
    match Ck.write st2 ~job:j ~position:pos ~machine_image:img ~prev:None ~threshold:0 ~head:false () with
    | Ok a -> a
    | Error e -> failwith (Ck.write_error_word e)
  in
  let aa = mk job_a 7 in
  let ab = mk job_b 7 in
  let aa' = mk job_a 8 in
  let ro2 = E4_cas.read_only st2 in
  let pay a = match E4_cas.get_node ro2 a with Some n -> n.E4_node.payload | None -> "" in
  check "LOG-REL two jobs, same content and position: the addresses differ"
    (not (E4_addr.Addr.equal aa ab));
  check "LOG-REL two jobs differ in the job field's 32 bytes and in nothing else"
    (let x = pay aa and y = pay ab in
     String.length x = String.length y
     &&
     let diff = ref [] in
     String.iteri (fun i c -> if c <> y.[i] then diff := i :: !diff) x;
     let d = List.rev !diff in
     match d with
     | [] -> false
     | first :: _ ->
       List.length d <= 32
       && List.for_all (fun i -> i >= first && i < first + 32) d
       && String.sub x first 32 = E4_addr.Addr.bytes job_a
       && String.sub y first 32 = E4_addr.Addr.bytes job_b);
  check "LOG-REL the same job at two positions: two addresses" (not (E4_addr.Addr.equal aa aa'));
  check "LOG-REL the same job, position and content: one address"
    (E4_addr.Addr.equal aa (mk job_a 7));
  check "LOG-REL the chunk digests are a function of the image alone"
    (let refs = Ch.store st2 ~spec:spec2 Ch.default img in
     let refs' = Ch.store st2 ~spec:spec2 Ch.default (String.sub img 0 (String.length img)) in
     refs = refs');
  E4_cas.close st2;
  (* the same content into a store with a different segment size, index size and insertion
     order must give the same checkpoint address (differential D3 in miniature) *)
  let d3 = fresh_dir () in
  let st3 =
    E4_cas.open_rw ~dir:d3 { E4_cas.seg_max = 4096; index_slots = 8; verify_on_open = false }
  in
  let spec3 = Ck.ensure_schema st3 in
  (* file some unrelated nodes first, so the pack layout and the insertion order differ *)
  for i = 0 to 20 do
    ignore
      (put_ok st3
         (E4_node.make ~version:0 ~kind:E4_kind.Export ~spec:(E4_addr.Addr.bytes spec3)
            ~payload:(f_bytes (Printf.sprintf "noise %d" i))))
  done;
  let job_a3 = put_ok st3 (job_node ~spec:spec3 "job-a") in
  E4_cas.commit st3;
  let aa3 =
    match Ck.write st3 ~job:job_a3 ~position:7 ~machine_image:img ~prev:None ~threshold:0 ~head:false () with
    | Ok a -> a
    | Error e -> failwith (Ck.write_error_word e)
  in
  check "LOG-REL / D3 two store layouts, one checkpoint address" (E4_addr.Addr.equal aa aa3);
  E4_cas.close st3

(* ============================================================ 4b. the chain and the head *)

let chain_and_head () =
  print_endline "";
  print_endline "== 4b. the prev chain, the head root, the cycle refusal ==";
  let dir = fresh_dir () in
  let st, _spec, job = store_with_job dir in
  let addrs = ref [] in
  let prev = ref None in
  for i = 0 to 4 do
    let img = cell_image ~cells:(4 + i) ~cell:64 in
    match Ck.write st ~job ~position:i ~machine_image:img ~prev:!prev () with
    | Ok a ->
      addrs := a :: !addrs;
      prev := Some a
    | Error e -> failwith (Ck.write_error_word e)
  done;
  let ro = E4_cas.read_only st in
  let head = match !prev with Some a -> a | None -> assert false in
  check "CP8 chain walks prev from the head to the first"
    (match Ck.chain ro head with Ok l -> l = !addrs && List.length l = 5 | Error _ -> false);
  check "CP3 the head root names the last checkpoint"
    (Ck.head ro job = Some head);
  check "M1 the pin root of the last checkpoint is minted"
    (let cid =
       match E4_cas.get_node ro head with
       | Some n -> E4_addr.Addr.of_digest (E4_sha256.digest n.E4_node.payload)
       | None -> E4_addr.Addr.zero
     in
     match E4_cas.root ro (E4_control.normalise_name (Ck.pin_root_name ~job cid)) with
     | Some r -> E4_addr.Addr.equal r.E4_control.digest head && r.E4_control.root_kind = E4_control.Pin
     | None -> false);
  check "CP3 a publish whose prev is not the head is refused (M7 Fork)"
    (match
       Ck.write st ~job ~position:99 ~machine_image:(cell_image ~cells:3 ~cell:64)
         ~prev:(List.nth !addrs 2 |> Option.some) ()
     with
     | Error (Ck.Root_refused (E4_control.Fork _)) -> true
     | Error (Ck.Root_refused (E4_control.Stale_root _)) -> true
     | _ -> false);
  check "CP8 chain refuses a cycle instead of looping"
    (let a = addr_of 1 and b = addr_of 2 in
     let prev_of x = if E4_addr.Addr.equal x a then Some b else Some a in
     match Ck.chain_from ~prev_of a with Error (Ck.Cycle _) -> true | _ -> false);
  check "CP8 chain_from on a finite chain is the chain"
    (let a = addr_of 1 and b = addr_of 2 and c = addr_of 3 in
     let prev_of x =
       if E4_addr.Addr.equal x a then Some b else if E4_addr.Addr.equal x b then Some c else None
     in
     Ck.chain_from ~prev_of a = Ok [ a; b; c ]);
  check "chain refuses an address that is not a checkpoint"
    (match Ck.chain ro (addr_of 55) with Error (Ck.Unreadable _) -> true | _ -> false);
  check "read refuses a node that is not a checkpoint"
    (match Ck.read ro job with Error (Ck.Not_a_checkpoint E4_kind.Job) -> true | _ -> false);
  E4_cas.close st

(* ============================================================ 4c. the mutation check *)

let find_sub hay needle =
  let n = String.length needle and l = String.length hay in
  let rec go i = if i + n > l then None else if String.sub hay i n = needle then Some i else go (i + 1) in
  go 0

let mutation () =
  print_endline "";
  print_endline "== 4c. a flipped byte inside a stored chunk ==";
  let dir = fresh_dir () in
  let st, _spec, job = store_with_job dir in
  let img = cell_image ~cells:2000 ~cell:512 in
  let a =
    match Ck.write st ~job ~position:0 ~machine_image:img ~prev:None ~threshold:0 () with
    | Ok a -> a
    | Error e -> failwith (Ck.write_error_word e)
  in
  check "CP7 read verifies before the mutation"
    (match Ck.read (E4_cas.read_only st) a with Ok (_, i) -> i = img | _ -> false);
  E4_cas.close st;
  (* flip one byte of a chunk's payload, in the pack file itself *)
  let pack_dir = Filename.concat dir "pack" in
  let files = Array.to_list (Sys.readdir pack_dir) |> List.sort compare in
  let path = Filename.concat pack_dir (List.hd files) in
  let ic = open_in_bin path in
  let raw = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let needle = String.sub img 20000 24 in
  (match find_sub raw needle with
  | None -> check "the image's bytes are findable in the pack (the test's own premise)" false
  | Some off ->
    let b = Bytes.of_string raw in
    Bytes.set b off (Char.chr (Char.code (Bytes.get b off) lxor 0x01));
    let oc = open_out_bin path in
    output_string oc (Bytes.to_string b);
    close_out oc;
    let ro = E4_cas.open_ro ~dir in
    check "MUTATION a flipped byte inside a stored chunk makes read refuse"
      (match Ck.read ro a with
       | Error Ck.Missing_chunk | Error (Ck.Image_mismatch _) | Error (Ck.Length_mismatch _) -> true
       | _ -> false);
    (match Ck.read ro a with
    | Error e -> note "  refusal: %s\n" (Ck.read_error_word e)
    | Ok _ -> ());
    E4_cas.close_ro ro)

(* ============================================================ 5. the streaming closure *)

let closure () =
  print_endline "";
  print_endline "== 5. CP9 / risk R8: closure_streaming ==";
  let dir = fresh_dir () in
  let st, _spec, job = store_with_job dir in
  let img = cell_image ~cells:3000 ~cell:512 in
  let w =
    match Ck.write_counted st ~job ~position:0 ~machine_image:img ~prev:None ~threshold:0 () with
    | Ok w -> w
    | Error e -> failwith (Ck.write_error_word e)
  in
  let ro = E4_cas.read_only st in
  let root = E4_addr.Ref.make E4_kind.Checkpoint w.Ck.addr in
  let streamed = ref [] and peak = ref 0 in
  Ck.closure_streaming ro root (fun a n ->
      let l = String.length (E4_node.encode n) in
      if l > !peak then peak := l;
      streamed := a :: !streamed);
  let streamed = List.rev !streamed in
  let word = E4_cas.closure ro root in
  let key a = E4_addr.Addr.hex a in
  let s1 = List.sort compare (List.map key streamed) in
  let s2 = List.sort compare (List.map (fun (b : E4_cas.binding) -> key b.E4_cas.addr) word) in
  let nodes, bytes = Ck.closure_size ro root in
  note "  closure: %d nodes, %d node bytes; the largest node held at once is %d B (image %d B)\n"
    nodes bytes !peak (String.length img);
  check "CP9 the streaming closure visits exactly E4_cas.closure's addresses" (s1 = s2);
  check "CP9 each address once" (List.length s1 = List.length (List.sort_uniq compare s1));
  check "CP9 children first: every checked edge is delivered before its node"
    (let seen = Hashtbl.create 64 in
     let ok = ref true in
     List.iter
       (fun a ->
         (match E4_cas.get_node ro a with
         | Some n ->
           List.iter
             (fun (e : E4_addr.Ref.t) ->
               if not (Hashtbl.mem seen (key e.E4_addr.Ref.addr)) then ok := false)
             (E4_node.checked_edges n)
         | None -> ok := false);
         Hashtbl.replace seen (key a) ())
       streamed;
     !ok);
  check "CP9 the closure never holds the image: the peak node is one chunk, not the image"
    (!peak <= Ch.default.Ch.max + 512 && String.length img > 4 * !peak);
  check "CP9 closure_size counts the same nodes" (nodes = List.length streamed);
  check "the closure covers the chunks, the manifests, the checkpoint, the job and the schema"
    (nodes = w.Ck.chunks_cut + w.Ck.manifest_nodes + 3);
  E4_cas.close st

(* ============================================================ 6. ephemeral *)

let ephemeral () =
  print_endline "";
  print_endline "== 6. CP10: an ephemeral checkpoint files no node ==";
  let dir = fresh_dir () in
  let st, _spec, job = store_with_job dir in
  let before = (E4_cas.stats (E4_cas.read_only st)).E4_cas.nodes in
  let wal = E4_wal.open_ ~dir ~job ~seg_max:E4_wal.default_seg_max in
  Ck.ephemeral wal ~position:12;
  Ck.ephemeral wal ~position:34;
  E4_wal.close wal;
  let after = (E4_cas.stats (E4_cas.read_only st)).E4_cas.nodes in
  check "CP10 an ephemeral checkpoint files no CAS node" (before = after);
  let rd = E4_wal.open_reader ~dir ~job in
  let marks = ref [] in
  ignore
    (E4_wal.replay rd ~from:0 ~f:(fun _ r ->
         match r with
         | E4_wal.Checkpoint_mark { position; addr } -> marks := (position, addr) :: !marks
         | _ -> ()));
  E4_wal.close_reader rd;
  check "CP10 the marks are in the log, with no address"
    (List.rev !marks = [ (12, None); (34, None) ]);
  E4_cas.close st

(* ============================================================ 7. the machine image *)

let rec chain_prog n : E.eff =
  if n <= 0 then E.Eff_succeed (E.Term_lit E.Lit_unit)
  else
    E.Eff_bind
      (E.Eff_perform (E.Native_op_refMake, E.Term_lit (E.Lit_nat (n - 1))), chain_prog (n - 1))

let machine_image () =
  print_endline "";
  print_endline "== 7. CP11: image_of_machine / machine_of_image ==";
  let t = En.run (chain_prog 40) ~fuel:2000 in
  let img = Ck.image_of_machine t in
  let st = Ck.machine_state t in
  note "  chain 40 at fuel 2000: %s, %d trace rows, %d refs, image %d B\n" (En.outcome t)
    (En.trace_length t) (List.length (En.refs t)) (String.length img);
  check "CP11 machine_of_image (image_of_machine m) = machine_state m"
    (Ck.machine_of_image img = Some st);
  check "CP11 re-encoding the decoded state gives the same bytes"
    (match Ck.machine_of_image img with Some s -> Ck.encode_image s = img | None -> false);
  check "CP11 the decoder is exact: a trailing byte is refused"
    (Ck.machine_of_image (img ^ "\000") = None);
  check "CP11 the decoder is exact: a truncation is refused"
    (Ck.machine_of_image (String.sub img 0 (String.length img - 1)) = None);
  check "CP11 the decoder is exact: the empty string is refused" (Ck.machine_of_image "" = None);
  check "CP11 the image names the instance's carriers" (st.Ck.mi_carriers = En.carriers);
  check "CP11 the image carries the reading axis: one row per trace index"
    (List.length st.Ck.mi_trace_rows = En.trace_length t);
  check "CP11 the image carries the ref heap" (st.Ck.mi_refs = En.refs t);
  check "CP11 the image version is the pending one" (st.Ck.mi_version = Ck.image_version);
  (* Machines at different points of one run give different images.  The points are made by
     FUEL, not by a longer tape: `replay_steps` stops consuming the tape as soon as the
     command residue is non-empty (E4_engine EN4), so a machine that ran out of fuel repeats
     and a longer tape of `evaluate` decisions gives one machine over and over. *)
  let prog = En.compile (chain_prog 40) in
  let steps = List.init 6 (fun i -> En.run_program prog ~fuel:(10 + (i * 20))) in
  let images = List.map Ck.image_of_machine steps in
  check "CP11 machines at different points of one run give distinct images"
    (List.length (List.sort_uniq compare images) = List.length images);
  check "CP11 the image is a function of the machine value alone"
    (List.for_all2 (fun m i -> Ck.image_of_machine m = i) steps images);
  (* MUTATION: a changed field changes the image *)
  check "MUTATION a changed field changes the image bytes"
    (Ck.encode_image { st with Ck.mi_fuel = st.Ck.mi_fuel + 1 } <> img)

(* ============================================================ 8. the sharing table (B7) *)

let sharing () =
  print_endline "";
  print_endline "== 8. A2 §4.4 / bench B7: 64 consecutive checkpoints of chain n=2000 ==";
  let k = 64 in
  let n = 2000 in
  (* The k positions of the run.  They are made by FUEL: `replay_steps` stops consuming the
     tape once the command residue is non-empty (E4_engine EN4), so a machine that ran out of
     fuel repeats and a 64-decision tape would give one image 64 times.  Increasing fuel over
     one compiled program is the same run at 64 increasing positions, which is what A2 §4.4's
     "consecutive checkpoints" means and what makes the image GROW between them. *)
  let step = 50 in
  let prog = En.compile (chain_prog n) in
  let t_load = Unix.gettimeofday () in
  let machines = List.init k (fun i -> En.run_program prog ~fuel:((i + 1) * step)) in
  let images = List.map Ck.image_of_machine machines in
  let sizes = List.map String.length images in
  note "  %d positions of chain %d at fuel %d..%d, driven in %.2f s\n" k n step (k * step)
    (Unix.gettimeofday () -. t_load);
  check "the premise: the run has not finished at the last position, so every image differs"
    (En.outcome (List.nth machines (k - 1)) <> "finished");
  note "  image %d B -> %d B; trace %d -> %d rows; refs %d -> %d\n" (List.hd sizes)
    (List.nth sizes (k - 1))
    (En.trace_length (List.hd machines))
    (En.trace_length (List.nth machines (k - 1)))
    (List.length (En.refs (List.hd machines)))
    (List.length (En.refs (List.nth machines (k - 1))));
  check "the run really grows: every image is larger than the one before it"
    (let rec go = function [] | [ _ ] -> true | a :: (b :: _ as r) -> a < b && go r in
     go sizes);
  let run ~chunk ?(params = Ch.default) dir =
    let st, _spec, job = store_with_job dir in
    let ro () = E4_cas.read_only st in
    let base = (E4_cas.stats (ro ())).E4_cas.bytes in
    let prev = ref None in
    let rows = ref [] in
    let addrs = ref [] in
    let last = ref base in
    List.iteri
      (fun i image ->
        let threshold = if chunk then 0 else max_int in
        match
          Ck.write_counted st ~job ~position:i ~machine_image:image ~prev:!prev ~params
            ~threshold ~pin:false ()
        with
        | Error e -> failwith (Ck.write_error_word e)
        | Ok w ->
          prev := Some w.Ck.addr;
          addrs := w.Ck.addr :: !addrs;
          let now = (E4_cas.stats (ro ())).E4_cas.bytes in
          rows := (i, String.length image, w.Ck.chunks_cut, w.Ck.chunks_fresh, w.Ck.chunks_dup,
                   w.Ck.manifest_nodes, w.Ck.manifest_fresh, now - !last, now - base) :: !rows;
          last := now)
      images;
    let ordered = List.rev !addrs in
    let ok_read =
      List.for_all2
        (fun a image ->
          match Ck.read (ro ()) a with Ok (_, img) -> img = image | Error _ -> false)
        ordered images
    in
    (* the head root and the prev chain agree with the order they were written in *)
    let head_ok =
      match !addrs with
      | h :: _ ->
        Ck.head (ro ()) job = Some h
        && (match Ck.chain (ro ()) h with Ok l -> l = !addrs | Error _ -> false)
      | [] -> false
    in
    let total = (E4_cas.stats (ro ())).E4_cas.bytes - base in
    E4_cas.close st;
    (List.rev !rows, total, ok_read && head_ok)
  in
  (* WHY there is anything to share: consecutive positions of one run extend the trace and the
     ref heap and rewrite only the header fields.  That is the append shape A2 §4.4's E2 row
     names, measured here on the real thing rather than on a synthetic image. *)
  let ma = List.nth machines (k - 2) and mb = List.nth machines (k - 1) in
  let rec pref a b n = match (a, b) with x :: xs, y :: ys when x = y -> pref xs ys (n + 1) | _ -> n in
  let ta = En.trace_rows ma and tb = En.trace_rows mb in
  let ra = En.refs ma and rb = En.refs mb in
  note "  consecutive positions: trace %d -> %d rows (common prefix %d); refs %d -> %d (common prefix %d)\n"
    (List.length ta) (List.length tb) (pref ta tb 0) (List.length ra) (List.length rb)
    (pref ra rb 0);
  check "the machine image grows by APPENDING: the trace and the ref heap are stable prefixes"
    (pref ta tb 0 = List.length ta && pref ra rb 0 = List.length ra);
  (* A2 §4.4's closed form for the optimal average: c* = sqrt (42 * S / k) for an image of S
     bytes with k edited regions and 42 the bytes of a framed ref.  At S = 64 MB, k = 2 it
     gives ~32 KB, which is where the default came from; at the machine image's size it gives
     something much smaller, and this run is that prediction tested. *)
  let s_last = List.nth sizes (k - 1) in
  let cstar = int_of_float (sqrt (42.0 *. float_of_int s_last /. 2.0)) in
  note "  the closed form c* = sqrt(42 * S / k) at S = %d B, k = 2 is %d B\n" s_last cstar;
  let plans =
    [ ("avg 16 KB (the default, tuned for 64 MB)", Some Ch.default);
      ("avg 4 KB", Some { Ch.avg = 4096; min = 1024; max = 16384 });
      ("avg 1 KB (nearest the closed form)", Some { Ch.avg = 1024; min = 256; max = 4096 });
      ("OFF: the whole blob, M2 as written", None) ]
  in
  let results =
    List.map
      (fun (name, p) ->
        match p with
        | Some params -> (name, run ~chunk:true ~params (fresh_dir ()))
        | None -> (name, run ~chunk:false (fresh_dir ())))
      plans
  in
  let get name = List.assoc name results in
  let rows_star, total_star, read_star = get "avg 1 KB (nearest the closed form)" in
  let _, total_def, read_def = get "avg 16 KB (the default, tuned for 64 MB)" in
  let _, total_off, read_off = get "OFF: the whole blob, M2 as written" in
  print_endline "";
  print_endline "  chunking on at avg 1 KB / min 256 B / max 4 KB (nearest the closed form):";
  print_endline "   i   image B  chunks  fresh   dup  manif  mfresh   delta B   cumulative B";
  List.iteri
    (fun i (_, img, cuts, fresh, dup, mn, mf, delta, cum) ->
      if i < 4 || i mod 8 = 0 || i = k - 1 then
        Printf.printf "  %2d  %8d  %6d %6d %5d %6d %7d %9d %14d\n" i img cuts fresh dup mn mf delta
          cum)
    rows_star;
  let deltas rows = List.map (fun (_, _, _, _, _, _, _, d, _) -> d) rows in
  let tail l = List.filteri (fun i _ -> i > 0) l in
  let mean l = List.fold_left ( + ) 0 l / max 1 (List.length l) in
  let sum_img = List.fold_left ( + ) 0 sizes in
  print_endline "";
  Printf.printf "  %-40s %14s %14s %10s\n" "plan" "cumulative B" "mean delta B" "vs off";
  List.iter
    (fun (name, (rows, total, _)) ->
      Printf.printf "  %-40s %14d %14d %9.2fx\n" name total
        (mean (tail (deltas rows)))
        (float_of_int total_off /. float_of_int (max 1 total)))
    results;
  Printf.printf "  the %d images themselves sum to %d B (%d B .. %d B)\n" k sum_img (List.hd sizes)
    (List.nth sizes (k - 1));
  check "CP6 at the closed-form average, chunking stores far less than the whole blob"
    (total_star * 2 < total_off);
  check "CP6 the chunked store is smaller than the sum of the images it holds"
    (total_star < sum_img);
  check "CP6 chunks are shared: at the last checkpoint most chunks are Duplicate"
    (let _, _, cuts, _, dup, _, _, _, _ = List.nth rows_star (k - 1) in
     cuts > 0 && dup * 2 > cuts);
  check "B7 a checkpoint that shares half its chunks costs less than its image"
    (List.for_all (fun (_, img, cuts, _, dup, _, _, d, _) -> dup * 2 < cuts || d < img) rows_star);
  check "A2 §4.4's closed form is real: the 64 MB default saves nothing on a 100 KB image"
    (total_def * 100 > total_off * 90);
  check "every store reads every checkpoint back byte for byte"
    (read_star && read_def && read_off);
  note "  READ THIS BEFORE QUOTING THE RATIO.  The default average is tuned for a 64 MB image\n";
  note "  (A2 §4.4, owner question OQ2) and on a 100 KB machine image it cuts one to three\n";
  note "  chunks, shares nothing and costs the node overhead — the closed form says so and the\n";
  note "  row above measures it.  A checkpointing engine must therefore pick `avg` from the\n";
  note "  image size, not from a constant; that is a finding for the coordinator, not a knob\n";
  note "  this lane may turn (OQ2 fixed the default).  B7's own acceptance (<= 300 KB per\n";
  note "  checkpoint and >= 200x) is stated at 64 MB with a one-cell edit and is\n";
  note "  bench_checkpoint.ml's cell, not this one.\n"

(* ============================================================ main *)

let () =
  print_endline "== test_checkpoint (lane P6: E4_chunk, E4_checkpoint) ==";
  Printf.printf "  sandbox: %s\n%!" root_dir;
  let run name f = try f () with e -> (incr failures; Printf.printf "FAIL %s -- %s\n%!" name (Printexc.to_string e)) in
  run "chunker" chunker;
  run "manifest" manifest;
  run "node" node_bytes;
  run "round_trips" round_trips;
  run "chain" chain_and_head;
  run "mutation" mutation;
  run "closure" closure;
  run "ephemeral" ephemeral;
  run "machine image" machine_image;
  run "sharing" sharing;
  rm_rf root_dir;
  print_endline "";
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  Printf.printf "   %d checks\n" !checks;
  if !failures > 0 then exit 1
