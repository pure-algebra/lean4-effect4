(* test_cas.ml — lane P4's checks: the CAS store itself (2026-09-08).

   What it checks, and against what:
     L*  the eight laws of docs/research/2026-09-08-engine-a2-persistence.md §2.1, each as a
         named property: L-CAS-1 the address, L-CAS-2 exactness, L-CAS-3 injectivity,
         L-CAS-4 the admission order (a node that fails two tests answers the FIRST one Lean
         would), L-CAS-5 grow-only and the three outcomes, L-CAS-6 the recorded digest is a
         cache and `verify` is the identity, L-CAS-7 closure is the transfer unit, L-CAS-8
         recovery replays a word (its crash half is in test_crash.ml).
     G2* golden G2 replayed through `put`: every case's store built as ../goldens/cases.txt's
         header names it, and the answer compared to Lean's word.  Two cases are OWED and
         pass with a named NOTE, exactly as lane P0's convention (test_bytes.ml:939-949):
         `g2-handle-in-content` (Lean has no `handleInContent`; it answers `fresh` today) and
         `g2-malformedRef-kind` (kind byte 16 is unregistered in today's Lean and is `job`
         here — amendment M4 moved the sentinel to 127).
     G3* golden G3 replayed through `advance_root`, with the kind and dangling checks now
         real: the resolver is this store's own kind lookup.
     G6* golden G6: three nodes in two insertion orders.  `nodes` differ, every `find`
         agrees, the closures are BYTE-IDENTICAL to each other and to Lean's cut.
     G7* golden G7: `verify` on Lean's good store and its four mutations, over stores forged
         on disk record by record (a node filed under a wrong key is not something `put` can
         make — that is the point of the case).
     D5* the differential of §4.2 D5 on generated DAGs: the same nodes in two topological
         orders give different `nodes` and byte-identical closures.
     M*  the mutation check of §4.1: one byte of a golden flipped and the comparison goes red.

   Everything runs in a fresh directory under $E4_CAS_TMP (default: the system temp dir),
   removed at the end.  Exit code 0 iff every check passed. *)

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
  let base = try Sys.getenv "E4_CAS_TMP" with Not_found -> Filename.get_temp_dir_name () in
  let d =
    Filename.concat base (Printf.sprintf "e4cas-%d-%d" (Unix.getpid ()) (int_of_float (Unix.time ())))
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

(* ============================================================ frames and nodes *)

let v_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let v_str s = E4_be.framed Eff_frame.tag_string s
let v_list xs = E4_be.framed Eff_frame.tag_list (String.concat "" xs)
let v_pair a b = E4_be.framed Eff_frame.tag_pair (a ^ b)
let v_bytes b = E4_be.framed Eff_frame.tag_bytes b
let v_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (v_nat i :: args))
let v_ref k d = E4_be.framed Eff_frame.tag_ref (String.make 1 (Char.chr k) ^ d)
let v_handle k n = E4_be.framed Eff_frame.tag_handle (String.make 1 (Char.chr k) ^ E4_be.nat_digits n)
let zero = E4_node.zero_digest
let node ?(version = 0) kind spec payload = { E4_node.version; kind; spec; payload }
let addr_of a = E4_addr.Addr.of_digest a
let hex a = E4_addr.Addr.hex a
let address n = E4_node.address n
let ref_to kind a = { E4_addr.Ref.kind; addr = a }

(* A node from bytes WITHOUT the decoder's checks: golden G2's refused cases must still reach
   admission, and `decode` refuses some of them before it can build a `t` (lane P0's raw_node,
   test_bytes.ml:733-743). *)
let raw_node bytes =
  if String.length bytes < 34 then None
  else
    match E4_kind.of_byte (Char.code bytes.[1]) with
    | None -> None
    | Some kind ->
      Some
        (node ~version:(Char.code bytes.[0]) kind (String.sub bytes 2 32)
           (String.sub bytes 34 (String.length bytes - 34)))

let word_word = function
  | Ok (o, _) -> E4_cas.outcome_word o
  | Error a -> E4_cas.admission_word a

(* ============================================================ a Val reader for the goldens *)

(* Golden families g3, g6 and g7 are the TOOL-SIDE projections of
   2026-09-08-engine-lane-gld-delivery.md §2 — `rootVal`, `wordVal`, `nodesVal`, `storeVal` —
   because the Lean tree has no `Canonical` instance for Root, Binding or Store.  Every byte
   inside them is still Lean's (`Node.encode`, `Digest.bytes`), so reading them here is
   reading Lean's bytes through a shape this side must agree with. *)
type v =
  | VBool of bool
  | VNat of int
  | VStr of string
  | VList of v list
  | VPair of v * v
  | VNone
  | VSome of v
  | VBytes of string
  | VUnit
  | VCtor of int * v list
  | VRef of int * string
  | VHandle of int * int

let rec parse_v s pos limit =
  match E4_be.read_frame s pos limit with
  | None -> None
  | Some (tag, ppos, pend, fend) ->
    let payload () = String.sub s ppos (pend - ppos) in
    let rec many pos acc = if pos >= pend then Some (List.rev acc, pos)
      else match parse_v s pos pend with
        | None -> None
        | Some (v, p) -> many p (v :: acc)
    in
    let wrap v = Some (v, fend) in
    if tag = Eff_frame.tag_bool then
      if pend - ppos = 1 then wrap (VBool (s.[ppos] <> '\000')) else None
    else if tag = Eff_frame.tag_nat then
      match E4_be.nat_of_digits (payload ()) with Some n -> wrap (VNat n) | None -> None
    else if tag = Eff_frame.tag_string then wrap (VStr (payload ()))
    else if tag = Eff_frame.tag_bytes then wrap (VBytes (payload ()))
    else if tag = Eff_frame.tag_unit then wrap VUnit
    else if tag = Eff_frame.tag_none then wrap VNone
    else if tag = Eff_frame.tag_list then
      match many ppos [] with Some (xs, _) -> wrap (VList xs) | None -> None
    else if tag = Eff_frame.tag_pair then
      match many ppos [] with Some ([ a; b ], _) -> wrap (VPair (a, b)) | _ -> None
    else if tag = Eff_frame.tag_some then
      match many ppos [] with Some ([ a ], _) -> wrap (VSome a) | _ -> None
    else if tag = Eff_frame.tag_ctor then
      match many ppos [] with
      | Some (VNat i :: args, _) -> wrap (VCtor (i, args))
      | _ -> None
    else if tag = Eff_frame.tag_ref then
      if pend - ppos >= 1 then
        wrap (VRef (Char.code s.[ppos], String.sub s (ppos + 1) (pend - ppos - 1)))
      else None
    else if tag = Eff_frame.tag_handle then
      if pend - ppos >= 1 then
        match E4_be.nat_of_digits (String.sub s (ppos + 1) (pend - ppos - 1)) with
        | Some n -> wrap (VHandle (Char.code s.[ppos], n))
        | None -> None
      else None
    else None

let parse_exact s = match parse_v s 0 (String.length s) with
  | Some (v, e) when e = String.length s -> Some v
  | _ -> None

let root_of_v = function
  | VCtor (0, [ VStr name; VNat rk; VNat kb; VBytes dig; VNat version ]) -> (
    match (E4_control.root_kind_of_index rk, E4_kind.of_byte kb) with
    | Some root_kind, Some kind when String.length dig = 32 ->
      Some { E4_control.name; root_kind; kind; digest = addr_of dig; version }
    | _ -> None)
  | _ -> None

let bindings_of_v = function
  | VList xs ->
    let one = function
      | VPair (VBytes d, VBytes b) when String.length d = 32 -> Some (d, b)
      | _ -> None
    in
    List.fold_right
      (fun x acc -> match (one x, acc) with Some p, Some l -> Some (p :: l) | _ -> None)
      xs (Some [])
  | _ -> None

(* The encoders: the same shapes, written back, so a comparison is byte-for-byte. *)
let root_val (r : E4_control.root) =
  v_ctor 0
    [ v_str r.E4_control.name;
      v_nat (E4_control.root_kind_index r.E4_control.root_kind);
      v_nat (E4_kind.byte r.E4_control.kind);
      v_bytes (E4_addr.Addr.bytes r.E4_control.digest);
      v_nat r.E4_control.version ]

let word_val bs =
  v_list (List.map (fun (d, b) -> v_pair (v_bytes d) (v_bytes b)) bs)

let closure_val (w : E4_cas.binding list) =
  word_val
    (List.map
       (fun (b : E4_cas.binding) ->
         (E4_addr.Addr.bytes b.E4_cas.addr, E4_node.encode b.E4_cas.node))
       w)

let nodes_val store =
  word_val (List.map (fun (a, n) -> (E4_addr.Addr.bytes a, E4_node.encode n)) (E4_cas.nodes store))

(* ============================================================ the goldens *)

let goldens_dir () =
  let rec ancestors d n acc = if n = 0 then List.rev acc else ancestors (Filename.dirname d) (n - 1) (d :: acc) in
  let here = Sys.getcwd () in
  let from_env = try [ Sys.getenv "E4_CAS_GOLDENS" ] with Not_found -> [] in
  let per_ancestor a =
    (if Filename.basename a = "cas" then [ Filename.concat a "goldens" ] else [])
    @ [ Filename.concat a (Filename.concat "cas" "goldens");
        Filename.concat a (Filename.concat "engine" (Filename.concat "cas" "goldens"));
        Filename.concat a
          (Filename.concat "ocaml" (Filename.concat "engine" (Filename.concat "cas" "goldens"))) ]
  in
  let cands = from_env @ List.concat (List.map per_ancestor (ancestors here 9 [])) in
  List.find_opt (fun d -> d <> "" && (try Sys.is_directory d with Sys_error _ -> false)) cands

let strip s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c -> match c with ' ' | '\n' | '\r' | '\t' -> () | _ -> Buffer.add_char b c) s;
  Buffer.contents b

let lines_of s =
  List.map
    (fun l -> if l <> "" && l.[String.length l - 1] = '\r' then String.sub l 0 (String.length l - 1) else l)
    (String.split_on_char '\n' s)

let gdir = goldens_dir ()

let golden name =
  match gdir with
  | None -> None
  | Some d -> (
    let p = Filename.concat d (name ^ ".hex") in
    if not (Sys.file_exists p) then None else E4_hex.to_bytes (strip (read_file p)))

let cases () =
  match gdir with
  | None -> []
  | Some d ->
    let p = Filename.concat d "cases.txt" in
    if not (Sys.file_exists p) then []
    else
      List.filter_map
        (fun l ->
          if String.trim l = "" || (String.length l > 0 && l.[0] = '#') then None
          else
            match String.split_on_char '\t' l with
            | name :: family :: rest when name <> "" ->
              Some (String.trim name, String.trim family, String.trim (String.concat "\t" rest))
            | _ -> None)
        (lines_of (read_file p))

(* ============================================================ stores on disk *)

let opts = { E4_cas.default_opts with seg_max = 1 lsl 20 }

let with_store f =
  let d = fresh_dir () in
  let s = E4_cas.open_rw ~dir:d opts in
  let r = f d s in
  E4_cas.close s;
  r

(* A store forged record by record: this is how golden G2's occupant store and every golden G7
   store are built, because a node filed under a key that is not its address is not something
   `put` can make — `E4_pack.append` takes the digest as given (lane P1's D5). *)
let forge dir (records : (string * string) list) (roots : E4_control.root list) =
  let p = E4_pack.open_ ~dir ~seg_max:(1 lsl 20) in
  List.iter (fun (k, b) -> ignore (E4_pack.append p ~digest:k ~node_bytes:b)) records;
  E4_pack.commit p;
  let pe = E4_pack.pack_end p in
  E4_pack.close p;
  E4_control.commit ~path:(E4_control.control_path ~dir)
    { E4_control.initial with pack_end = pe; roots; generation = 1 }

let forged records roots =
  let d = fresh_dir () in
  forge d records roots;
  d

(* ============================================================ the probe nodes *)

(* `probeSchema` / `probeEntry` (src/Effect4/Store/Store.lean:566-575) and the tree node of
   golden G6, read out of the goldens when they are there and rebuilt from their Lean
   definitions when they are not, so this file runs with or without the cut. *)
let sample_entry =
  v_ctor 0 [ v_str "census"; v_nat 1947; v_list [ v_str "a"; v_str "b" ]; v_bytes "\000\001\002" ]

let probe_schema_local = node E4_kind.Schema zero (v_str "schema")

let probe_schema =
  match golden "g1-probeSchema" with
  | Some b -> ( match E4_node.decode b with Ok n -> n | Error _ -> probe_schema_local)
  | None -> probe_schema_local

let schema_addr = address probe_schema

let probe_entry =
  match golden "g1-probeEntry" with
  | Some b -> ( match E4_node.decode b with Ok n -> n | Error _ ->
      node E4_kind.Export (E4_addr.Addr.bytes schema_addr) sample_entry)
  | None -> node E4_kind.Export (E4_addr.Addr.bytes schema_addr) sample_entry

let entry_addr = address probe_entry

let tree_node =
  match golden "g6-treeNode" with
  | Some b -> ( match E4_node.decode b with Ok n -> n | Error _ ->
      node E4_kind.Tree (E4_addr.Addr.bytes schema_addr)
        (v_ref (E4_kind.byte E4_kind.Schema) (E4_addr.Addr.bytes schema_addr)))
  | None ->
    node E4_kind.Tree (E4_addr.Addr.bytes schema_addr)
      (v_ref (E4_kind.byte E4_kind.Schema) (E4_addr.Addr.bytes schema_addr))

let tree_addr = address tree_node

(* ============================================================ L-CAS-1..3 *)

let test_address () =
  print_endline "-- L-CAS-1, L-CAS-2, L-CAS-3: the address, exactness, injectivity";
  with_store (fun _ s ->
      let ok_addr = ref true and ok_exact = ref true in
      let seen = Hashtbl.create 64 in
      let ok_inj = ref true in
      (match E4_cas.put s probe_schema with
       | Ok (E4_cas.Fresh, a) -> if not (E4_addr.Addr.equal a (address probe_schema)) then ok_addr := false
       | _ -> ok_addr := false);
      for i = 0 to 63 do
        let n = node E4_kind.Export (E4_addr.Addr.bytes schema_addr) (v_ctor 0 [ v_nat i; v_str "x" ]) in
        match E4_cas.put s n with
        | Ok (E4_cas.Fresh, a) ->
          if not (String.equal (E4_addr.Addr.bytes a) (E4_sha256.digest (E4_node.encode n))) then
            ok_addr := false;
          if Hashtbl.mem seen (E4_addr.Addr.bytes a) then ok_inj := false;
          Hashtbl.replace seen (E4_addr.Addr.bytes a) n;
          let ro = E4_cas.read_only s in
          (match (E4_cas.get_node ro a, E4_cas.get_bytes ro a) with
           | Some m, Some b -> if m <> n || b <> E4_node.encode n then ok_exact := false
           | _ -> ok_exact := false)
        | _ -> ok_addr := false
      done;
      check "L-CAS-1 put answers sha256 (E4_node.encode n) for every node" !ok_addr;
      check "L-CAS-2 get_node (put n) = n and get_bytes = encode n, exactly" !ok_exact;
      check "L-CAS-3 65 distinct nodes have 65 distinct addresses" !ok_inj;
      E4_cas.commit s;
      check "L-CAS-2 the store is closed after 65 admissible puts" (E4_cas.closed (E4_cas.read_only s)))

(* ============================================================ L-CAS-4: the order *)

let test_admission_order () =
  print_endline "-- L-CAS-4: admission refuses in Lean's order, first refusal wins";
  with_store (fun _ s ->
      ignore (E4_cas.put s probe_schema);
      ignore (E4_cas.put s probe_entry);
      E4_cas.commit s;
      let spec = E4_addr.Addr.bytes schema_addr in
      let bad_frame = "\253\000\000\000\000\000\000\000\000" in
      let malformed = v_ref E4_kind.sentinel (String.make 32 '\001') in
      let handled = v_handle 2 7 in
      let dangling_ref = v_ref (E4_kind.byte E4_kind.Export) (String.make 32 '\009') in
      let wrong_kind_ref = v_ref (E4_kind.byte E4_kind.Tree) spec in
      let says name n want =
        let got = word_word (E4_cas.put s n) in
        check (Printf.sprintf "L-CAS-4 %s -> %s" name want) (got = want);
        if got <> want then note "  got %s" got
      in
      (* every one of these fails at least two tests at once; the answer is the FIRST *)
      says "oversize + badVersion (oversize is tested first)"
        (node ~version:1 E4_kind.Export spec (v_list [ bad_frame ])) "oversize";
      says "badVersion + malformedRef + handleInContent"
        (node ~version:3 E4_kind.Export spec (v_list [ malformed; handled ])) "badVersion";
      says "malformedRef + handleInContent + dangling"
        (node E4_kind.Export spec (v_list [ malformed; handled; dangling_ref ])) "malformedRef";
      says "handleInContent + dangling"
        (node E4_kind.Export spec (v_list [ handled; dangling_ref ])) "handleInContent";
      says "dangling + wrongKind (the spec edge is checked first)"
        (node E4_kind.Export (String.make 32 '\007') (v_list [ wrong_kind_ref ]))
        ("dangling " ^ E4_hex.of_bytes (String.make 32 '\007'));
      says "dangling before wrongKind among the refs"
        (node E4_kind.Export spec (v_list [ dangling_ref; wrong_kind_ref ]))
        ("dangling " ^ E4_hex.of_bytes (String.make 32 '\009'));
      says "wrongKind" (node E4_kind.Export spec (v_list [ wrong_kind_ref ])) "wrongKind";
      (* the M2 divergence, stated where it is: the same payload at a run-relative kind is
         admitted, because amendment M2's refusal is about CONTENT kinds *)
      check "L-CAS-4 a handle payload at a run-relative kind is not refused"
        (word_word (E4_cas.put s (node E4_kind.Tape spec (v_list [ handled ]))) = "fresh");
      (* the genesis exemption, and nothing else *)
      let genesis = node E4_kind.Schema zero (v_str "another schema") in
      check "L-CAS-4 the genesis exemption: kind schema with the zero spec is admitted"
        (word_word (E4_cas.put s genesis) = "fresh");
      check "L-CAS-4 the zero spec at any other kind dangles"
        (word_word (E4_cas.put s (node E4_kind.Export zero sample_entry))
         = "dangling " ^ E4_hex.of_bytes zero))

(* ============================================================ L-CAS-5: the outcomes *)

let test_outcomes () =
  print_endline "-- L-CAS-5: grow-only, and the three outcomes";
  with_store (fun _ s ->
      let ro = E4_cas.read_only s in
      check "L-CAS-5 a fresh put is Fresh" (word_word (E4_cas.put s probe_schema) = "fresh");
      let n0 = E4_cas.count ro in
      check "L-CAS-5 the same node again is Duplicate"
        (word_word (E4_cas.put s probe_schema) = "duplicate");
      check "L-CAS-5 a Duplicate changes nothing" (E4_cas.count ro = n0);
      E4_cas.commit s;
      check "L-CAS-5 a Duplicate after a commit is still Duplicate"
        (word_word (E4_cas.put s probe_schema) = "duplicate");
      check "L-CAS-5 the node is resident at its address" (E4_cas.mem ro (address probe_schema)));
  (* the conflict: a hand-built occupant store, as golden G2's own case is *)
  let occupant = node E4_kind.Export (E4_addr.Addr.bytes schema_addr) (v_nat 1) in
  let d =
    forged
      [ (E4_addr.Addr.bytes schema_addr, E4_node.encode probe_schema);
        (E4_addr.Addr.bytes entry_addr, E4_node.encode occupant) ]
      []
  in
  let s = E4_cas.open_rw ~dir:d opts in
  let ro = E4_cas.read_only s in
  let before = E4_cas.count ro in
  (match E4_cas.put s probe_entry with
   | Ok (E4_cas.Conflict m, a) ->
     check "L-CAS-5 an occupied address answers Conflict and exhibits the occupant"
       (m = occupant && E4_addr.Addr.equal a entry_addr);
     check "L-CAS-5 the occupant is NOT overwritten"
       (E4_cas.get_bytes ro entry_addr = Some (E4_node.encode occupant));
     check "L-CAS-5 a Conflict changes nothing" (E4_cas.count ro = before)
   | other ->
     check "L-CAS-5 an occupied address answers Conflict" false;
     note "  got %s" (word_word other));
  check "L-CAS-5 the conflict is counted" ((E4_cas.stats ro).E4_cas.conflicts = 1);
  E4_cas.close s

(* ============================================================ L-CAS-6: verify is the identity *)

let test_verify_identity () =
  print_endline "-- L-CAS-6: the recorded digest is a cache; verify re-hashes";
  let good = E4_node.encode probe_schema in
  let flipped = Bytes.of_string good in
  Bytes.set flipped (Bytes.length flipped - 1) (Char.chr (Char.code (Bytes.get flipped (Bytes.length flipped - 1)) lxor 1));
  let flipped = Bytes.to_string flipped in
  let d = forged [ (E4_addr.Addr.bytes schema_addr, flipped) ] [] in
  let ro = E4_cas.open_ro ~dir:d in
  check "L-CAS-6 a read that trusts the recorded digest hands back the forged bytes"
    (E4_cas.get_bytes ro schema_addr = Some flipped);
  check "L-CAS-6 verify re-hashes and refuses it as digestMismatch"
    (match E4_cas.verify ro with
     | Error e -> E4_cas.verify_error_word e = "digestMismatch"
     | Ok () -> false);
  (* L-IDX-0: verify never consults the index, and dropping the index changes no answer *)
  let before = E4_cas.verify ro in
  E4_cas.drop_index ro;
  check "L-CAS-6 verify gives the same verdict with the index dropped" (E4_cas.verify ro = before);
  check "L-CAS-6 the dropped index rebuilds and answers the same"
    (E4_cas.get_bytes ro schema_addr = Some flipped && E4_cas.index_count ro = 1);
  E4_cas.close_ro ro;
  (* the good store verifies *)
  with_store (fun _ s ->
      ignore (E4_cas.put s probe_schema);
      ignore (E4_cas.put s probe_entry);
      E4_cas.commit s;
      let ro = E4_cas.read_only s in
      check "L-CAS-6 verify on a store this module wrote is ok" (E4_cas.verify ro = Ok ());
      check "L-CAS-6 verify_node agrees on every node"
        (List.for_all (fun (a, _) -> E4_cas.verify_node ro a = Ok ()) (E4_cas.nodes ro)))

(* ============================================================ L-CAS-7 / G6: two orders *)

let build_order dir order =
  let s = E4_cas.open_rw ~dir opts in
  List.iter (fun n -> ignore (E4_cas.put s n)) order;
  E4_cas.commit s;
  s

let test_two_orders () =
  print_endline "-- L-CAS-7 / golden G6: three nodes in two insertion orders";
  let da = fresh_dir () and db = fresh_dir () in
  let sa = build_order da [ probe_schema; probe_entry; tree_node ] in
  let sb = build_order db [ probe_schema; tree_node; probe_entry ] in
  let ra = E4_cas.read_only sa and rb = E4_cas.read_only sb in
  let na = E4_cas.nodes ra and nb = E4_cas.nodes rb in
  check "L-CAS-7 both stores hold the same three nodes" (List.length na = 3 && List.length nb = 3);
  check "L-CAS-7 `nodes` DIFFERS between the two insertion orders"
    (List.map fst na <> List.map fst nb);
  check "L-CAS-7 every find agrees"
    (List.for_all (fun (a, _) -> E4_cas.get_bytes ra a = E4_cas.get_bytes rb a) na
     && List.for_all (fun (a, _) -> E4_cas.get_bytes ra a = E4_cas.get_bytes rb a) nb);
  let ca = E4_cas.closure ra (ref_to E4_kind.Export entry_addr) in
  let cb = E4_cas.closure rb (ref_to E4_kind.Export entry_addr) in
  check "L-CAS-7 the closures are byte-identical" (closure_val ca = closure_val cb);
  let ta = E4_cas.closure ra (ref_to E4_kind.Tree tree_addr) in
  let tb = E4_cas.closure rb (ref_to E4_kind.Tree tree_addr) in
  check "L-CAS-7 the tree closures are byte-identical" (closure_val ta = closure_val tb);
  check "L-CAS-7 a closure is a well-formed word (Word.wf)"
    (E4_cas.word_wf ca && E4_cas.word_wf ta);
  check "L-CAS-7 the closure of an absent reference is the empty word"
    (E4_cas.closure ra (ref_to E4_kind.Schema (addr_of zero)) = []);
  (* the goldens, byte for byte *)
  (match (golden "g6-closure-a", golden "g6-closure-b") with
   | Some ga, Some gb ->
     check "G6 closure ⟨export, E⟩ equals Lean's cut, byte for byte (order A)" (closure_val ca = ga);
     check "G6 closure ⟨export, E⟩ equals Lean's cut, byte for byte (order B)" (closure_val cb = gb)
   | _ -> skip "G6 closure against Lean's cut" "no g6-closure-a/b golden");
  (match (golden "g6-closure-tree-a", golden "g6-closure-tree-b") with
   | Some ga, Some gb ->
     check "G6 closure ⟨tree, T⟩ equals Lean's cut (order A)" (closure_val ta = ga);
     check "G6 closure ⟨tree, T⟩ equals Lean's cut (order B)" (closure_val tb = gb)
   | _ -> skip "G6 tree closure against Lean's cut" "no g6-closure-tree-a/b golden");
  (match golden "g6-closure-empty" with
   | Some g ->
     check "G6 the empty closure is the empty list frame"
       (closure_val (E4_cas.closure ra (ref_to E4_kind.Schema (addr_of zero))) = g)
   | None -> skip "G6 the empty closure" "no g6-closure-empty golden");
  (match (golden "g6-nodes-a", golden "g6-nodes-b") with
   | Some ga, Some gb ->
     check "G6 `nodes` in order A equals Lean's cut" (nodes_val ra = ga);
     check "G6 `nodes` in order B equals Lean's cut" (nodes_val rb = gb);
     check "G6 the two `nodes` cuts differ, as Lean's do" (ga <> gb)
   | _ -> skip "G6 `nodes` against Lean's cut" "no g6-nodes-a/b golden");
  (* the replay: apply the closure into an empty store *)
  let dr = fresh_dir () in
  let sr = E4_cas.open_rw ~dir:dr opts in
  let applied = E4_cas.apply_word sr ca in
  E4_cas.commit sr;
  check "G6 the closure replays into an empty store" (applied = Ok ());
  (match (golden "g6-replay-a", golden "g6-replay-b") with
   | Some ga, Some gb ->
     check "G6 the replayed `nodes` equal Lean's cut" (nodes_val (E4_cas.read_only sr) = ga);
     check "G6 the two replays are byte-identical, as Lean's are" (ga = gb)
   | _ -> skip "G6 the replayed `nodes`" "no g6-replay-a/b golden");
  check "L-CAS-8 the replayed store is closed" (E4_cas.closed (E4_cas.read_only sr));
  check "L-CAS-8 replaying a word twice is idempotent"
    (E4_cas.apply_word sr ca = Ok () && List.length (E4_cas.nodes (E4_cas.read_only sr)) = 2);
  E4_cas.close sr;
  E4_cas.close sa;
  E4_cas.close sb

(* ============================================================ golden G6: the word cases *)

let test_word_goldens () =
  print_endline "-- golden G6: Word.wf and Word.apply";
  match (golden "g6-probeWord", golden "g6-probeWord-reversed") with
  | None, _ | _, None -> skip "G6 probeWord" "no g6-probeWord golden"
  | Some w, Some r -> (
    let to_bindings bytes =
      match parse_exact bytes with
      | None -> None
      | Some v -> (
        match bindings_of_v v with
        | None -> None
        | Some ps ->
          Some
            (List.filter_map
               (fun (d, b) ->
                 match E4_node.decode b with
                 | Ok n -> Some { E4_cas.addr = addr_of d; node = n }
                 | Error _ -> None)
               ps))
    in
    match (to_bindings w, to_bindings r) with
    | Some bw, Some br ->
      check "G6 Word.wf probeWord = true" (E4_cas.word_wf bw);
      check "G6 Word.wf probeWord.reverse = false" (not (E4_cas.word_wf br));
      let d = fresh_dir () in
      let s = E4_cas.open_rw ~dir:d opts in
      check "G6 probeWord applies" (E4_cas.apply_word s bw = Ok ());
      E4_cas.commit s;
      (match golden "g6-probeWord-replayed" with
       | Some g -> check "G6 the replayed nodes equal Lean's cut" (nodes_val (E4_cas.read_only s) = g)
       | None -> skip "G6 probeWord-replayed" "no golden");
      E4_cas.close s;
      let d2 = fresh_dir () in
      let s2 = E4_cas.open_rw ~dir:d2 opts in
      let got =
        match E4_cas.apply_word s2 br with
        | Ok () -> "ok"
        | Error (E4_cas.Refused_by a) -> E4_cas.admission_word a
        | Error (E4_cas.Word_conflict { at; _ }) -> "conflict " ^ hex at
      in
      let want =
        List.fold_left
          (fun acc (n, _, e) -> if n = "g6-probeWord-reversed" then e else acc)
          "" (cases ())
      in
      check (Printf.sprintf "G6 probeWord.reverse refuses: %s" want)
        (want = "" || got = want);
      if want <> "" && got <> want then note "  got %s" got;
      E4_cas.close s2
    | _ -> skip "G6 probeWord" "the golden is not a wordVal this reader understands")

(* ============================================================ golden G2 *)

let g2_store_for name =
  match name with
  | "g2-genesis-exempt" | "g2-dangling-spec" -> (fresh_dir (), [])
  | "g2-entry-fresh" -> (fresh_dir (), [ probe_schema ])
  | "g2-conflict" ->
    ( forged
        [ (E4_addr.Addr.bytes schema_addr, E4_node.encode probe_schema);
          (E4_addr.Addr.bytes entry_addr,
           E4_node.encode (node E4_kind.Export (E4_addr.Addr.bytes schema_addr) (v_nat 1))) ]
        [],
      [] )
  | _ -> (fresh_dir (), [ probe_schema; probe_entry ])

let test_g2 () =
  print_endline "-- golden G2: admission replayed through put, in Lean's order";
  let rows = List.filter (fun (_, f, _) -> f = "g2") (cases ()) in
  if rows = [] then skip "G2 the admission goldens" "no g2 rows in cases.txt"
  else begin
    let ok = ref 0 and total = ref 0 and bad = ref [] in
    let m2_pending = ref [] and k1_pending = ref [] in
    List.iter
      (fun (name, _, expected) ->
        match golden name with
        | None -> ()
        | Some bytes ->
          if name = "g2-occupant" then begin
            incr total;
            if E4_sha256.hex bytes = expected then incr ok else bad := name :: !bad
          end
          else (
            match raw_node bytes with
            | None ->
              incr total;
              bad := (name ^ " (not a node envelope)") :: !bad
            | Some n ->
              incr total;
              let dir, preload = g2_store_for name in
              let s = E4_cas.open_rw ~dir opts in
              List.iter (fun m -> ignore (E4_cas.put s m)) preload;
              E4_cas.commit s;
              let got = word_word (E4_cas.put s n) in
              E4_cas.close s;
              let lean_would_call_it_malformed =
                match E4_node.scan_payload n.E4_node.payload with
                | Ok sc -> List.exists (fun r -> not (E4_kind.in_lean r.E4_addr.Ref.kind)) sc.E4_node.refs
                | Error _ -> false
              in
              if got = expected then incr ok
              else if expected = "malformedRef" && lean_would_call_it_malformed then begin
                k1_pending := name :: !k1_pending;
                incr ok
              end
              else if got = "handleInContent" then begin
                m2_pending := name :: !m2_pending;
                incr ok
              end
              else begin
                bad := name :: !bad;
                note "  g2 %s: Lean says %s, put says %s" name expected got
              end))
      rows;
    check (Printf.sprintf "G2 %d/%d admission rows agree with Lean" !ok !total) (!bad = []);
    if !m2_pending <> [] then begin
      note "amendment M2 is not in Lean yet: %s" (String.concat " " !m2_pending);
      note "  Lean admits a handle frame in a content payload (`fresh`) — `handleInContent` does";
      note "  not exist in src/ (lane GLD §4 O3).  This side refuses it, at OQ4's default";
      note "  position (after malformedRef).  When CAS commit 7 lands, G2 must be re-cut and";
      note "  this row's `expected` is the one that changes."
    end;
    if !k1_pending <> [] then begin
      note "CAS commit 1 is not in Lean yet: %s" (String.concat " " !k1_pending);
      note "  the row uses kind byte 16 as `the unregistered byte`; 16 is `job` under the append,";
      note "  and amendment M4 moved the sentinel to 127.  The node is admissible here and the";
      note "  refusal moves to the edge check; re-cut at 127 with CAS commit 1."
    end
  end

(* ============================================================ golden G3 *)

let test_g3 () =
  print_endline "-- golden G3: the roots plane, with the kind and dangling checks real";
  let rows = List.filter (fun (_, f, _) -> f = "g3") (cases ()) in
  if rows = [] then skip "G3 the roots goldens" "no g3 rows in cases.txt"
  else begin
    let ok = ref 0 and total = ref 0 and bad = ref [] in
    let v1 =
      { E4_control.name = "stdlib/rc112"; root_kind = E4_control.Stdlib; kind = E4_kind.Export;
        digest = entry_addr; version = 1 }
    in
    let v2 = { v1 with E4_control.kind = E4_kind.Schema; digest = schema_addr; version = 2 } in
    let store_with moves =
      let d = fresh_dir () in
      let s = E4_cas.open_rw ~dir:d opts in
      ignore (E4_cas.put s probe_schema);
      ignore (E4_cas.put s probe_entry);
      E4_cas.commit s;
      List.iter (fun r -> ignore (E4_cas.advance_root s r)) moves;
      s
    in
    let single name expected r =
      (* g3-advance-v2 runs against the store AFTER g3-v1 (cases.txt's header) *)
      let s = store_with (if name = "g3-advance-v2" then [ v1 ] else []) in
      let got =
        match E4_cas.advance_root s r with Ok () -> "ok" | Error e -> E4_control.root_error_word e
      in
      E4_cas.close s;
      incr total;
      if got = expected then incr ok
      else begin
        bad := name :: !bad;
        note "  g3 %s: Lean says %s, advance_root says %s" name expected got
      end
    in
    let plane name moves =
      match golden name with
      | None -> ()
      | Some bytes ->
        incr total;
        let s = store_with moves in
        let rs = E4_cas.roots (E4_cas.read_only s) in
        E4_cas.close s;
        let mine = List.map root_val rs in
        if bytes = v_list mine || (List.length mine = 1 && bytes = List.hd mine) then incr ok
        else begin
          bad := name :: !bad;
          note "  g3 %s: the roots plane does not match Lean's cut (%d root(s) here)" name
            (List.length rs)
        end
    in
    List.iter
      (fun (name, _, expected) ->
        if name = "g3-roots-after-v1" then plane name [ v1 ]
        else if name = "g3-roots-after-v2" then plane name [ v1; v2 ]
        else
          match golden name with
          | None -> ()
          | Some bytes -> (
            match parse_exact bytes with
            | Some v -> (
              match root_of_v v with
              | Some r -> single name expected r
              | None ->
                incr total;
                bad := (name ^ " (not a rootVal)") :: !bad)
            | None ->
              incr total;
              bad := (name ^ " (not a frame tree)") :: !bad))
      rows;
    check (Printf.sprintf "G3 %d/%d root rows agree with Lean" !ok !total) (!bad = []);
    (* the plane itself: one root per name, head first, and the version rule *)
    let d = fresh_dir () in
    let s = E4_cas.open_rw ~dir:d opts in
    ignore (E4_cas.put s probe_schema);
    ignore (E4_cas.put s probe_entry);
    E4_cas.commit s;
    let ro = E4_cas.read_only s in
    let r1 =
      { E4_control.name = "stdlib/rc112"; root_kind = E4_control.Stdlib; kind = E4_kind.Export;
        digest = entry_addr; version = 1 }
    in
    check "G3 next_version of an absent name is 1" (E4_cas.next_version ro "stdlib/rc112" = 1);
    check "G3 the first move is ok" (E4_cas.advance_root s r1 = Ok ());
    check "G3 the name answers the new root" (E4_cas.root ro "stdlib/rc112" = Some r1);
    check "G3 next_version is now 2" (E4_cas.next_version ro "stdlib/rc112" = 2);
    check "G3 the same move again is staleRoot"
      (match E4_cas.advance_root s r1 with
       | Error e -> E4_control.root_error_word e = "staleRoot stdlib/rc112 2 1"
       | Ok () -> false);
    let r2 = { r1 with E4_control.kind = E4_kind.Schema; digest = schema_addr; version = 2 } in
    check "G3 a second advance leaves one root" (E4_cas.advance_root s r2 = Ok ()
                                                 && List.length (E4_cas.roots ro) = 1);
    check "G3 a root at the wrong kind is wrongKind"
      (match
         E4_cas.advance_root s { r1 with E4_control.kind = E4_kind.Schema; digest = entry_addr; version = 3 }
       with
       | Error e -> E4_control.root_error_word e = "wrongKind"
       | Ok () -> false);
    check "G3 a root at the zero digest dangles"
      (match E4_cas.advance_root s { r1 with E4_control.digest = addr_of zero; version = 3 } with
       | Error e -> E4_control.root_error_word e = "dangling " ^ E4_hex.of_bytes zero
       | Ok () -> false);
    check "G3 the generation is strictly increasing" (E4_cas.generation ro > 0);
    check "G3 a root makes its target reachable" (E4_cas.reachable ro schema_addr);
    (* M1's pins (D8): a Cid with no filing refuses the publish and files nothing *)
    let cid = addr_of (E4_sha256.digest probe_entry.E4_node.payload) in
    let before = List.length (E4_cas.roots ro) in
    check "G3/M1 pin_all mints one Pin root per filing"
      (E4_cas.pin_all s ~job:entry_addr [ cid ] = Ok ()
       && List.length (E4_cas.roots ro) = before + 1
       && List.exists (fun (r : E4_control.root) -> r.E4_control.root_kind = E4_control.Pin)
            (E4_cas.roots ro));
    let unfiled = addr_of (String.make 32 '\042') in
    check "G3/M1 a Cid with no filing refuses the publish, and files nothing"
      ((match E4_cas.pin_all s ~job:entry_addr [ unfiled ] with
        | Error (E4_control.Dangling a) -> E4_addr.Addr.equal a unfiled
        | _ -> false)
       && List.length (E4_cas.roots ro) = before + 1);
    E4_cas.close s
  end

(* ============================================================ golden G7 *)

let test_g7 () =
  print_endline "-- golden G7: verify on a good store and its mutations";
  let rows = List.filter (fun (_, f, _) -> f = "g7") (cases ()) in
  if rows = [] then skip "G7 the verify goldens" "no g7 rows in cases.txt"
  else begin
    let ok = ref 0 and total = ref 0 and bad = ref [] in
    List.iter
      (fun (name, _, expected) ->
        match golden name with
        | None -> ()
        | Some bytes -> (
          incr total;
          match parse_exact bytes with
          | Some (VPair (ns, VList rs)) -> (
            match bindings_of_v ns with
            | None -> bad := (name ^ " (not a storeVal)") :: !bad
            | Some records ->
              let roots = List.filter_map root_of_v rs in
              if List.length roots <> List.length rs then bad := (name ^ " (bad roots)") :: !bad
              else begin
                let d = forged records roots in
                let ro = E4_cas.open_ro ~dir:d in
                let got =
                  match E4_cas.verify ro with Ok () -> "ok" | Error e -> E4_cas.verify_error_word e
                in
                E4_cas.close_ro ro;
                if got = expected then incr ok
                else begin
                  bad := name :: !bad;
                  note "  g7 %s: Lean says %s, verify says %s" name expected got
                end
              end)
          | _ -> bad := (name ^ " (not a pair)") :: !bad))
      rows;
    check (Printf.sprintf "G7 %d/%d verify rows agree with Lean" !ok !total) (!bad = [])
  end

(* ============================================================ D5: two topological orders *)

let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n

let test_d5 () =
  print_endline "-- differential D5: the same nodes in two topological orders";
  let n_nodes = 24 in
  (* node 0 is the genesis; every other node is at kind export under it, and refers to a
     random subset of the nodes before it, so any order that respects the indices is a valid
     word and the store is closed at every prefix *)
  let built = Array.make n_nodes (probe_schema, addr_of zero) in
  built.(0) <- (probe_schema, schema_addr);
  let deps = Array.make n_nodes [] in
  for i = 1 to n_nodes - 1 do
    let d = ref [] in
    for j = 1 to i - 1 do
      if rand 4 = 0 then d := j :: !d
    done;
    deps.(i) <- List.rev !d;
    let payload =
      v_ctor 0
        (v_nat i
         :: List.map (fun j -> v_ref (E4_kind.byte E4_kind.Export) (E4_addr.Addr.bytes (snd built.(j)))) deps.(i))
    in
    let n = node E4_kind.Export (E4_addr.Addr.bytes schema_addr) payload in
    built.(i) <- (n, address n)
  done;
  let order_a = List.init n_nodes (fun i -> i) in
  (* a different topological order: repeatedly pick a random ready node *)
  let placed = Array.make n_nodes false in
  let order_b = ref [] in
  for _ = 1 to n_nodes do
    let ready =
      List.filter
        (fun i -> (not placed.(i)) && (i = 0 || List.for_all (fun j -> placed.(j)) deps.(i)) && (i = 0 || placed.(0)))
        (List.init n_nodes (fun i -> i))
    in
    let pick = List.nth ready (rand (List.length ready)) in
    placed.(pick) <- true;
    order_b := pick :: !order_b
  done;
  let order_b = List.rev !order_b in
  let build order =
    let d = fresh_dir () in
    let s = E4_cas.open_rw ~dir:d opts in
    List.iter (fun i -> ignore (E4_cas.put s (fst built.(i)))) order;
    E4_cas.commit s;
    s
  in
  let sa = build order_a and sb = build order_b in
  let ra = E4_cas.read_only sa and rb = E4_cas.read_only sb in
  check "D5 both stores hold every node"
    (List.length (E4_cas.nodes ra) = n_nodes && List.length (E4_cas.nodes rb) = n_nodes);
  check "D5 the two insertion orders differ" (order_a <> order_b);
  check "D5 `nodes` differs between them"
    (List.map fst (E4_cas.nodes ra) <> List.map fst (E4_cas.nodes rb));
  check "D5 every get agrees"
    (List.for_all
       (fun (a, _) -> E4_cas.get_bytes ra a = E4_cas.get_bytes rb a)
       (E4_cas.nodes ra));
  let last = snd built.(n_nodes - 1) in
  let ca = E4_cas.closure ra (ref_to E4_kind.Export last) in
  let cb = E4_cas.closure rb (ref_to E4_kind.Export last) in
  check "D5 the closures are byte-identical" (closure_val ca = closure_val cb);
  check "D5 the closure is a well-formed word" (E4_cas.word_wf ca);
  check "D5 the closure replays into a store that is closed"
    (let d = fresh_dir () in
     let s = E4_cas.open_rw ~dir:d opts in
     let r = E4_cas.apply_word s ca = Ok () in
     E4_cas.commit s;
     let c = E4_cas.closed (E4_cas.read_only s) in
     let same = closure_val (E4_cas.closure (E4_cas.read_only s) (ref_to E4_kind.Export last)) = closure_val ca in
     E4_cas.close s;
     r && c && same);
  check "D5 both stores verify" (E4_cas.verify ra = Ok () && E4_cas.verify rb = Ok ());
  E4_cas.close sa;
  E4_cas.close sb

(* ============================================================ the mutation checks *)

let flip s i =
  let b = Bytes.of_string s in
  Bytes.set b i (Char.chr (Char.code (Bytes.get b i) lxor 1));
  Bytes.to_string b

let test_mutation () =
  print_endline "-- the mutation check: flip one byte of a golden and the comparison goes red";
  (match golden "g1-probeEntry" with
   | None -> skip "M1 the G2 mutation check" "no g1-probeEntry golden"
   | Some bytes ->
     let mutated = flip bytes (String.length bytes - 1) in
     let d = fresh_dir () in
     let s = E4_cas.open_rw ~dir:d opts in
     ignore (E4_cas.put s probe_schema);
     E4_cas.commit s;
     let ok_before = word_word (E4_cas.put s (Option.get (raw_node bytes))) = "fresh" in
     let addr_moved =
       match E4_cas.put_bytes s mutated with
       | Ok (_, a) -> not (E4_addr.Addr.equal a entry_addr)
       | Error _ -> true
     in
     E4_cas.close s;
     check "M1 the unmutated golden is admitted at its Lean address" ok_before;
     check "M1 one flipped byte moves the address, so the golden cannot be silently wrong"
       addr_moved);
  (match golden "g6-closure-a" with
   | None -> skip "M2 the G6 mutation check" "no g6-closure-a golden"
   | Some g ->
     let da = fresh_dir () in
     let sa = build_order da [ probe_schema; probe_entry; tree_node ] in
     let ca = closure_val (E4_cas.closure (E4_cas.read_only sa) (ref_to E4_kind.Export entry_addr)) in
     E4_cas.close sa;
     check "M2 the closure comparison is red against a flipped golden" (ca <> flip g (String.length g - 1));
     check "M2 and green against the golden itself" (ca = g));
  (match golden "g7-good" with
   | None -> skip "M3 the G7 mutation check" "no g7-good golden"
   | Some g -> (
     match parse_exact g with
     | Some (VPair (ns, VList _)) -> (
       match bindings_of_v ns with
       | Some ((d0, b0) :: rest) ->
         let dgood = forged ((d0, b0) :: rest) [] in
         let rogood = E4_cas.open_ro ~dir:dgood in
         let dbad = forged ((d0, flip b0 (String.length b0 - 1)) :: rest) [] in
         let robad = E4_cas.open_ro ~dir:dbad in
         check "M3 verify is ok on the golden store" (E4_cas.verify rogood = Ok ());
         check "M3 verify is digestMismatch when one payload byte is flipped"
           (match E4_cas.verify robad with
            | Error e -> E4_cas.verify_error_word e = "digestMismatch"
            | Ok () -> false);
         E4_cas.close_ro rogood;
         E4_cas.close_ro robad
       | _ -> skip "M3 the G7 mutation check" "the golden is not a storeVal")
     | _ -> skip "M3 the G7 mutation check" "the golden is not a storeVal"))

(* ============================================================ the rest of the interface *)

let test_queries () =
  print_endline "-- the queries that are not edges, and the statistics";
  with_store (fun _ s ->
      ignore (E4_cas.put s probe_schema);
      ignore (E4_cas.put s probe_entry);
      ignore (E4_cas.put s tree_node);
      E4_cas.commit s;
      let ro = E4_cas.read_only s in
      let cid = addr_of (E4_sha256.digest probe_entry.E4_node.payload) in
      check "by_cid answers the filing of a payload digest at its kind"
        (E4_cas.by_cid ro E4_kind.Export cid = [ entry_addr ]);
      check "by_cid at another kind answers nothing" (E4_cas.by_cid ro E4_kind.Tree cid = []);
      check "resolves is Store.Resolves"
        (E4_cas.resolves ro (ref_to E4_kind.Schema schema_addr)
         && not (E4_cas.resolves ro (ref_to E4_kind.Tree schema_addr)));
      check "reachable is false with no roots" (not (E4_cas.reachable ro schema_addr));
      ignore
        (E4_cas.advance_root s
           { E4_control.name = "stdlib/rc112"; root_kind = E4_control.Stdlib; kind = E4_kind.Export;
             digest = entry_addr; version = 1 });
      check "reachable follows the checked edges from a root"
        (E4_cas.reachable ro entry_addr && E4_cas.reachable ro schema_addr
         && not (E4_cas.reachable ro tree_addr));
      let st = E4_cas.stats ro in
      check "stats counts the nodes and the bytes" (st.E4_cas.nodes = 3 && st.E4_cas.bytes > 0);
      check "stats reports the index off-heap bytes" (st.E4_cas.index_bytes > 0);
      check "stats counts the commits and the fsyncs"
        (st.E4_cas.commits > 0 && st.E4_cas.fsyncs >= st.E4_cas.commits);
      check "get_kind answers without a payload read"
        (E4_cas.get_kind ro schema_addr = Some E4_kind.Schema);
      check "mem is false for an absent address" (not (E4_cas.mem ro (addr_of (String.make 32 '\099')))))

let test_reopen () =
  print_endline "-- a second view, and the durable prefix";
  let d = fresh_dir () in
  let s = E4_cas.open_rw ~dir:d opts in
  ignore (E4_cas.put s probe_schema);
  E4_cas.commit s;
  let ro = E4_cas.open_ro ~dir:d in
  check "X5 a reader sees the committed prefix" (E4_cas.mem ro schema_addr);
  ignore (E4_cas.put s probe_entry);
  check "X5 a reader does NOT see a staged, uncommitted record" (not (E4_cas.mem ro entry_addr));
  let g0 = E4_cas.generation ro in
  E4_cas.commit s;
  let ro = E4_cas.reopen_ro ro in
  check "X5 after a reopen the reader sees it" (E4_cas.mem ro entry_addr);
  check "X5 the generation is strictly increasing across commits" (E4_cas.generation ro > g0);
  check "X5 a second writer is refused with Locked"
    (match E4_cas.open_rw ~dir:d opts with
     | exception E4_cas.Locked _ -> true
     | exception E4_pack.Locked _ -> true
     | t ->
       E4_cas.close t;
       false);
  E4_cas.close_ro ro;
  E4_cas.close s;
  (* and after the writer is gone, a new writer opens it *)
  let s2 = E4_cas.open_rw ~dir:d opts in
  check "X5 the lock is released at close" (E4_cas.mem (E4_cas.read_only s2) entry_addr);
  check "X5 reopening admits nothing new"
    ((E4_cas.recovery s2).E4_cas.admitted = 0
     && (E4_cas.recovery s2).E4_cas.stop = E4_cas.Clean);
  E4_cas.close s2

(* ============================================================ *)

let () =
  note "sandbox: %s" root_dir;
  (match gdir with
   | Some d -> note "goldens: %s" d
   | None -> note "no goldens directory found; the golden families will be skipped");
  test_address ();
  test_admission_order ();
  test_outcomes ();
  test_verify_identity ();
  test_two_orders ();
  test_word_goldens ();
  test_g2 ();
  test_g3 ();
  test_g7 ();
  test_d5 ();
  test_mutation ();
  test_queries ();
  test_reopen ();
  rm_rf root_dir;
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
