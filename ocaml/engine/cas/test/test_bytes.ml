(* test_bytes.ml — lane P0's checks: the CAS byte layer (2026-09-08).

   What it checks, and against what:
     C*  E4_crc: the five standard CRC-32 vectors, composition over every split, the window
         form, the 32-bit range, and the be32 field.
     K*  E4_kind: the table of src/Effect4/Store/Kind.lean:60-104 and its ten #guards
         (:145-158), the reserved append 16..23, and the unregistered-byte refusal.
     A*  E4_addr: the 32-byte law, the hex delegation to E4_hex, prefix63's range, and the
         presentation round trips of amendment M6.
     N*  E4_node: the layout and the exactness refusals of src/Effect4/Store/Node.lean:439-448,
         the edge scan #guards (:449-460), the AnyRef frame shape (:462-463), the traversal
         order (L-SCAN-1), the bytes-is-a-leaf case (L-SCAN-2, which has no Lean #guard yet —
         A2 §4.1 G5 says it must exist), the malformed verdicts (L-SCAN-3), the handle scan
         (M2), the host limit (M9) and the pure admission order of Store.lean:262-276.
     G*  The goldens of ../goldens (families G1 and G5, cut from Lean by lane GLD): every
         *.hex re-encoded and re-addressed, manifest.txt's digests, cases.txt's expectations,
         and the mutation check — flip one byte and the comparison must go red.  When the
         directory is absent every G* line is a SKIP and the run still ends green.

   The value frames below are built from E4_be.framed alone — the byte rule of
   src/Effect4/Store/Val.lean:147-159 — so nothing under test builds its own input.

   Exit code 0 iff every check passed. *)

open Effect4_engine
open Effect4_engine_cas

let failures = ref 0
let skips = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let skip name why =
  Printf.printf "SKIP  %s (%s)\n" name why;
  incr skips

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* A fixed linear congruential generator: the run is reproducible. *)
let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n
let rand_bytes n = String.init n (fun _ -> Char.chr (rand 256))

(* ============================================================ the value frames

   src/Effect4/Store/Val.lean:147-159, transcribed with E4_be.framed and nothing else. *)

let v_unit = E4_be.framed Eff_frame.tag_unit ""
let v_bool b = E4_be.framed Eff_frame.tag_bool (if b then "\001" else "\000")
let v_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let v_str s = E4_be.framed Eff_frame.tag_string s
let v_bytes b = E4_be.framed Eff_frame.tag_bytes b
let v_list xs = E4_be.framed Eff_frame.tag_list (String.concat "" xs)
let v_pair a b = E4_be.framed Eff_frame.tag_pair (a ^ b)
let v_none = E4_be.framed Eff_frame.tag_none ""
let v_some a = E4_be.framed Eff_frame.tag_some a
let v_ctor i args = E4_be.framed Eff_frame.tag_ctor (v_nat i ^ String.concat "" args)
let v_ref k d = E4_be.framed Eff_frame.tag_ref (String.make 1 (Char.chr k) ^ d)
let v_handle k n =
  E4_be.framed Eff_frame.tag_handle (String.make 1 (Char.chr k) ^ E4_be.nat_digits n)

(* src/Effect4/Store/Val.lean:1150 -- sampleEntry, the input of Digest.lean's third #guard. *)
let sample_entry = v_ctor 0 [ v_str "Effect"; v_str "gen"; v_ctor 0 []; v_nat 1947 ]

let zero32 = String.make 32 '\000'
let dig i = String.make 32 (Char.chr i)

let sample_node =
  E4_node.make ~version:0 ~kind:E4_kind.Export ~spec:zero32 ~payload:sample_entry

let present_refs rs = String.concat "," (List.map E4_addr.Ref.present rs)

let decode_error_name = function
  | E4_node.Trailing -> "Trailing"
  | E4_node.Bad_version b -> Printf.sprintf "Bad_version %d" b
  | E4_node.Unregistered_kind b -> Printf.sprintf "Unregistered_kind %d" b
  | E4_node.Short_spec -> "Short_spec"
  | E4_node.Bad_frame -> "Bad_frame"
  | E4_node.Host_limit -> "Host_limit"

let refusal_name = function
  | E4_node.Oversize e -> "Oversize(" ^ decode_error_name e ^ ")"
  | E4_node.Bad_version_byte b -> Printf.sprintf "Bad_version_byte %d" b
  | E4_node.Malformed_ref -> "Malformed_ref"
  | E4_node.Handle_in_content -> "Handle_in_content"

(* ============================================================ E4_crc *)

let test_crc () =
  print_endline "-- E4_crc: CRC-32, IEEE 802.3 reflected (poly 0xEDB88320)";
  check "C0 poly is the reflected IEEE 802.3 polynomial" (E4_crc.poly = 0xEDB88320);
  check "C1 crc \"\" = 0x00000000" (E4_crc.string "" = 0x00000000);
  check "C1 crc \"123456789\" = 0xCBF43926" (E4_crc.string "123456789" = 0xCBF43926);
  check "C1 crc \"a\" = 0xE8B7BE43" (E4_crc.string "a" = 0xE8B7BE43);
  check "C1 crc \"abc\" = 0x352441C2" (E4_crc.string "abc" = 0x352441C2);
  check "C1 crc pangram = 0x414FA339"
    (E4_crc.string "The quick brown fox jumps over the lazy dog" = 0x414FA339);
  check "C2 init = crc \"\"" (E4_crc.init = E4_crc.string "");

  (* C2: composition over every split of 200 random strings. *)
  let comp_ok = ref true in
  for _ = 1 to 200 do
    let s = rand_bytes (rand 64) in
    let n = String.length s in
    for i = 0 to n do
      let a = String.sub s 0 i and b = String.sub s i (n - i) in
      if E4_crc.update (E4_crc.string a) b <> E4_crc.string s then comp_ok := false
    done
  done;
  check "C2 update (string a) b = string (a ^ b) for every split" !comp_ok;

  let char_ok = ref true in
  let s = rand_bytes 64 in
  let acc = ref E4_crc.init in
  String.iter (fun c -> acc := E4_crc.update_char !acc c) s;
  if !acc <> E4_crc.string s then char_ok := false;
  check "C2 update_char folds to the same value" !char_ok;

  (* C4: windows. *)
  let win_ok = ref true in
  for _ = 1 to 200 do
    let s = rand_bytes (32 + rand 64) in
    let pos = rand (String.length s) in
    let len = rand (String.length s - pos + 1) in
    if E4_crc.sub s pos len <> E4_crc.string (String.sub s pos len) then win_ok := false
  done;
  check "C4 sub s pos len = string (String.sub s pos len)" !win_ok;
  check "C4 an out-of-range window is Invalid_argument"
    (try ignore (E4_crc.sub "abc" 2 5); false with Invalid_argument _ -> true);
  check "C3 a crc argument outside 0..0xFFFFFFFF is Invalid_argument"
    (try ignore (E4_crc.update (-1) "x"); false with Invalid_argument _ -> true);

  (* C3: range. *)
  let range_ok = ref true in
  for _ = 1 to 500 do
    let c = E4_crc.string (rand_bytes (rand 128)) in
    if c < 0 || c > 0xFFFFFFFF then range_ok := false
  done;
  check "C3 every crc is in 0 .. 0xFFFFFFFF" !range_ok;

  (* C5: the field. *)
  check "C5 field_length = 4" (E4_crc.field_length = 4);
  check "C5 be32 0xCBF43926 = cb f4 39 26"
    (E4_crc.be32 0xCBF43926 = "\xcb\xf4\x39\x26");
  let be_ok = ref true in
  for _ = 1 to 500 do
    let n = E4_crc.string (rand_bytes (rand 32)) in
    if E4_crc.read_be32 (E4_crc.be32 n) 0 <> Some n then be_ok := false
  done;
  check "C5 read_be32 (be32 n) 0 = Some n" !be_ok;
  check "C5 read_be32 past the end is None"
    (E4_crc.read_be32 "abc" 0 = None && E4_crc.read_be32 "abcd" 1 = None
     && E4_crc.read_be32 "abcd" (-1) = None);
  check "C5 be32 refuses a value outside 32 bits"
    (try ignore (E4_crc.be32 0x1_0000_0000); false with Invalid_argument _ -> true)

(* ============================================================ E4_kind *)

let test_kind () =
  print_endline "-- E4_kind: the table of src/Effect4/Store/Kind.lean, appended per CAS commit 1";
  check "K1 all has 23 entries" (List.length E4_kind.all = 23);
  check "K1 all is in byte order 1..23"
    (List.mapi (fun i k -> E4_kind.byte k = i + 1) E4_kind.all |> List.for_all (fun x -> x));
  check "K1 of_byte (byte k) = Some k for every kind"
    (List.for_all (fun k -> E4_kind.of_byte (E4_kind.byte k) = Some k) E4_kind.all);
  check "K1 of_byte b = Some k -> byte k = b"
    (List.for_all
       (fun b -> match E4_kind.of_byte b with None -> true | Some k -> E4_kind.byte k = b)
       (List.init 300 (fun i -> i - 20)));
  check "K1 byte is injective"
    (List.length (List.sort_uniq compare (List.map E4_kind.byte E4_kind.all)) = 23);
  check "K5 name is injective and round-trips"
    (List.length (List.sort_uniq compare (List.map E4_kind.name E4_kind.all)) = 23
     && List.for_all (fun k -> E4_kind.of_name (E4_kind.name k) = Some k) E4_kind.all);

  (* Kind.lean:145-158 -- the ten #guards, verbatim. *)
  check "K1 #guard source=1 export=2 schema=4 program=5 annotation=6"
    (E4_kind.byte E4_kind.Source = 1 && E4_kind.byte E4_kind.Export = 2
     && E4_kind.byte E4_kind.Schema = 4 && E4_kind.byte E4_kind.Program = 5
     && E4_kind.byte E4_kind.Annotation = 6);
  check "K1 #guard tree=11 component=13 vector=14 fiber=15"
    (E4_kind.byte E4_kind.Tree = 11 && E4_kind.byte E4_kind.Component = 13
     && E4_kind.byte E4_kind.Vector = 14 && E4_kind.byte E4_kind.Fiber = 15);
  check "K2 #guard of_byte 0 = None (0 is the version byte)" (E4_kind.of_byte 0 = None);
  check "K1 #guard of_byte 2 = Some export" (E4_kind.of_byte 2 = Some E4_kind.Export);
  check "K5 #guard of_name \"export\" = Some export, of_name \"Export\" = None"
    (E4_kind.of_name "export" = Some E4_kind.Export && E4_kind.of_name "Export" = None);
  note "Kind.lean:155's #guard `ofByte? 16 = none` does NOT transfer: byte 16 is `job` under";
  note "CAS commit 1's append, and amendment M4 moved the unregistered-kind sentinel to 127.";

  (* K2: the refusals, at the appended table. *)
  check "K2 of_byte 127 = None (the sentinel, amendment M4)"
    (E4_kind.of_byte E4_kind.sentinel = None && E4_kind.sentinel = 127);
  check "K2 of_byte 24, 100, 128, 255, -1 = None"
    (E4_kind.of_byte 24 = None && E4_kind.of_byte 100 = None && E4_kind.of_byte 128 = None
     && E4_kind.of_byte 255 = None && E4_kind.of_byte (-1) = None);
  check "K2 is_registered agrees with of_byte on -20..299"
    (List.for_all
       (fun b -> E4_kind.is_registered b = (E4_kind.of_byte b <> None))
       (List.init 320 (fun i -> i - 20)));
  check "K2 version_byte = 0 and is never a kind"
    (E4_kind.version_byte = 0 && E4_kind.of_byte E4_kind.version_byte = None);

  (* K3, K4, K6 and the provenance line. *)
  check "K3 fiber (15) is the tombstone and the only one"
    (E4_kind.tombstoned E4_kind.Fiber
     && List.length (List.filter E4_kind.tombstoned E4_kind.all) = 1);
  check "K4 is_run_relative = {tape, log, exits, checkpoint} (amendment M2)"
    (List.filter E4_kind.is_run_relative E4_kind.all
     = [ E4_kind.Tape; E4_kind.Log; E4_kind.Exits; E4_kind.Checkpoint ]);
  check "K4 is_content is the complement of is_run_relative"
    (List.for_all (fun k -> E4_kind.is_content k <> E4_kind.is_run_relative k) E4_kind.all);
  check "K6 is_interior = {chunk}"
    (List.filter E4_kind.is_interior E4_kind.all = [ E4_kind.Chunk ]);
  check "K1 in_lean is exactly bytes 1..15 (Kind.lean has 15 rows today)"
    (List.filter E4_kind.in_lean E4_kind.all
     = List.filter (fun k -> E4_kind.byte k <= 15) E4_kind.all
     && List.length (List.filter E4_kind.in_lean E4_kind.all) = 15
     && E4_kind.lean_max_byte = 15);
  check "K1 the reserved append is job 16 .. table 23"
    (E4_kind.byte E4_kind.Job = 16 && E4_kind.byte E4_kind.Tape = 17
     && E4_kind.byte E4_kind.Log = 18 && E4_kind.byte E4_kind.Exits = 19
     && E4_kind.byte E4_kind.Receipt = 20 && E4_kind.byte E4_kind.Checkpoint = 21
     && E4_kind.byte E4_kind.Profile = 22 && E4_kind.byte E4_kind.Table = 23
     && E4_kind.name E4_kind.Table = "table")

(* ============================================================ E4_addr *)

let test_addr () =
  print_endline "-- E4_addr: Addr / Ref / Cid / Handle";
  check "AD1 Addr.length = 32" (E4_addr.Addr.length = 32);
  check "AD1 of_digest refuses anything but 32 bytes"
    ((try ignore (E4_addr.Addr.of_digest "short"); false with Invalid_argument _ -> true)
     && (try ignore (E4_addr.Addr.of_digest (String.make 33 'x')); false
         with Invalid_argument _ -> true));
  check "AD1 of_digest_opt is None off 32 and Some on 32"
    (E4_addr.Addr.of_digest_opt "short" = None
     && E4_addr.Addr.of_digest_opt (dig 7) <> None);
  check "AD1 bytes (of_digest d) = d"
    (E4_addr.Addr.bytes (E4_addr.Addr.of_digest (dig 9)) = dig 9);

  (* AD2: the hex face is E4_hex's, not a second codec. *)
  let hex_ok = ref true in
  for _ = 1 to 200 do
    let d = rand_bytes 32 in
    let a = E4_addr.Addr.of_digest d in
    let h = E4_addr.Addr.hex a in
    if h <> E4_hex.of_bytes d then hex_ok := false;
    if String.length h <> 64 then hex_ok := false;
    if String.lowercase_ascii h <> h then hex_ok := false;
    (match E4_addr.Addr.of_hex h with
     | Some a' when E4_addr.Addr.equal a a' -> ()
     | _ -> hex_ok := false);
    (match E4_addr.Addr.of_hex (String.uppercase_ascii h) with
     | Some a' when E4_addr.Addr.equal a a' -> ()
     | _ -> hex_ok := false)
  done;
  check "AD2 hex = E4_hex.of_bytes, lowercase, 64 chars, either case in" !hex_ok;
  check "AD2 of_hex refuses a short, an odd and a non-hex string"
    (E4_addr.Addr.of_hex "e3b0" = None
     && E4_addr.Addr.of_hex (String.make 63 'a') = None
     && E4_addr.Addr.of_hex (String.make 63 'a' ^ "g") = None);
  check "AD5 zero is 32 zero bytes and 64 hex zeros"
    (E4_addr.Addr.bytes E4_addr.Addr.zero = zero32
     && E4_addr.Addr.hex E4_addr.Addr.zero = String.make 64 '0');

  (* AD6: prefix63 (the leading 62 bits; deviation D1). *)
  let pfx_ok = ref true in
  for _ = 1 to 500 do
    let d = rand_bytes 32 in
    let p = E4_addr.Addr.prefix63 (E4_addr.Addr.of_digest d) in
    if p < 0 || p > max_int then pfx_ok := false;
    (* two digests with the same leading 8 bytes have the same key *)
    let d' = String.sub d 0 8 ^ rand_bytes 24 in
    if E4_addr.Addr.prefix63 (E4_addr.Addr.of_digest d') <> p then pfx_ok := false
  done;
  check "AD6 prefix63 is non-negative, fits an int, and depends only on the leading 8 bytes"
    !pfx_ok;
  check "AD6 prefix63 zero = 0 and prefix63 0xff.. is the top key"
    (E4_addr.Addr.prefix63 E4_addr.Addr.zero = 0
     && E4_addr.Addr.prefix63 (E4_addr.Addr.of_digest (String.make 32 '\255')) = max_int);
  let distinct =
    List.sort_uniq compare
      (List.map (fun i -> E4_addr.Addr.prefix63 (E4_addr.Addr.of_digest (dig i)))
         (List.init 200 (fun i -> i mod 256)))
  in
  check "AD6 prefix63 separates 200 distinct leading bytes" (List.length distinct = 200);

  (* AD4: the presentations. *)
  let pres_ok = ref true in
  List.iter
    (fun k ->
      let a = E4_addr.Addr.of_digest (rand_bytes 32) in
      let r = E4_addr.Ref.make k a in
      let s = E4_addr.Ref.present r in
      (match E4_addr.Ref.parse s with
       | Some r' when E4_addr.Ref.equal r r' -> ()
       | _ -> pres_ok := false);
      if s <> E4_kind.name k ^ ":" ^ E4_addr.Addr.hex a then pres_ok := false;
      let c = E4_addr.Cid.present k a in
      (match E4_addr.Cid.parse c with
       | Some (k', a') when E4_kind.equal k k' && E4_addr.Addr.equal a a' -> ()
       | _ -> pres_ok := false);
      if c <> E4_kind.name k ^ ":cid:" ^ E4_addr.Addr.hex a then pres_ok := false;
      (* each parser refuses the other's form *)
      if E4_addr.Ref.parse c <> None then pres_ok := false;
      if E4_addr.Cid.parse s <> None then pres_ok := false)
    E4_kind.all;
  check "AD4 Ref/Cid present-parse round trip over every kind, each refusing the other's form"
    !pres_ok;
  check "AD4 parse refuses an unregistered kind name, a short hex, and a missing colon"
    (E4_addr.Ref.parse ("nosuch:" ^ String.make 64 'a') = None
     && E4_addr.Ref.parse ("export:" ^ String.make 63 'a') = None
     && E4_addr.Ref.parse (String.make 64 'a') = None
     && E4_addr.Cid.parse ("export:cid:" ^ String.make 10 'a') = None
     && E4_addr.Cid.parse ("export:nope:" ^ String.make 64 'a') = None);

  (* AD3: a handle has an address and no inverse. *)
  let a = E4_addr.Addr.of_digest (dig 3) in
  let h1 = E4_addr.Handle.direct ~addr:a ~seg:2 ~off:4096 ~len:108 in
  let h2 = E4_addr.Handle.located a in
  check "AD3 Handle.addr is total on both constructors"
    (E4_addr.Addr.equal (E4_addr.Handle.addr h1) a
     && E4_addr.Addr.equal (E4_addr.Handle.addr h2) a);
  check "AD3 a Direct handle carries its place and a Located one does not"
    (match h1, h2 with
     | E4_addr.Handle.Direct { seg; off; len; _ }, E4_addr.Handle.Located _ ->
       seg = 2 && off = 4096 && len = 108
     | _ -> false)

(* ============================================================ E4_node: the layout *)

let test_node_layout () =
  print_endline "-- E4_node: the envelope (src/Effect4/Store/Node.lean:170-182)";
  let b = E4_node.encode sample_node in

  (* Digest.lean:315 -- the third #guard pins that sample_entry above IS Lean's sampleEntry. *)
  check "N0 sha256 (Val.encode sampleEntry) = 8fab1618… (Digest.lean:315)"
    (E4_sha256.hex sample_entry
     = "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa");

  (* Node.lean:439-441 *)
  check "N1 #guard sampleNode.encode.length = 108" (String.length b = 108);
  check "N1 #guard sampleNode.encode.take 2 = [0, 2]"
    (String.sub b 0 2 = "\000\002");
  check "N1 #guard sampleNode.encode.drop 34 = Val.encode sampleEntry"
    (String.sub b 34 (String.length b - 34) = sample_entry);
  check "N1 the spec sits at bytes 2..33" (String.sub b 2 32 = zero32);

  (* Node.lean:442-448 -- the round trip and the four refusals. *)
  check "N1 #guard decode (encode sampleNode) = some sampleNode"
    (E4_node.decode b = Ok sample_node);
  check "N2 #guard decode (encode ++ [0]) = none  -> Trailing"
    (E4_node.decode (b ^ "\000") = Error E4_node.Trailing);
  check "N2 #guard decode (1 :: drop 1) = none  -> Bad_version 1"
    (E4_node.decode ("\001" ^ String.sub b 1 (String.length b - 1))
     = Error (E4_node.Bad_version 1));
  check "N2 #guard decode (0 :: 0 :: drop 2) = none  -> Unregistered_kind 0"
    (E4_node.decode ("\000\000" ^ String.sub b 2 (String.length b - 2))
     = Error (E4_node.Unregistered_kind 0));
  check "N2 an unregistered kind byte (127, the sentinel) is Unregistered_kind 127"
    (E4_node.decode ("\000\127" ^ String.sub b 2 (String.length b - 2))
     = Error (E4_node.Unregistered_kind 127));
  check "N2 #guard decode (take 33) = none  -> Short_spec"
    (E4_node.decode (String.sub b 0 33) = Error E4_node.Short_spec);
  check "N2 #guard decode [] = none  -> Short_spec"
    (E4_node.decode "" = Error E4_node.Short_spec
     && E4_node.decode "\000" = Error E4_node.Short_spec
     && E4_node.decode "\000\002" = Error E4_node.Short_spec);
  note "Node.lean:445's #guard uses kind byte 16; under CAS commit 1 that is `job`, so this";
  note "lane uses 127 (amendment M4's sentinel) as the unregistered-byte witness.";

  (* ND1/ND2 as properties over a spread of kinds and payloads. *)
  let rt_ok = ref true and exact_ok = ref true in
  List.iter
    (fun k ->
      List.iter
        (fun p ->
          let n = E4_node.make ~version:0 ~kind:k ~spec:(dig (E4_kind.byte k)) ~payload:p in
          let bytes = E4_node.encode n in
          (match E4_node.decode bytes with
           | Ok n' ->
             if n' <> n then rt_ok := false;
             if E4_node.encode n' <> bytes then exact_ok := false
           | Error _ -> rt_ok := false))
        [ v_unit; v_none; v_bool true; v_bool false; v_nat 0; v_nat 1947;
          v_str "Effect"; v_str ""; v_bytes ""; v_bytes (rand_bytes 40);
          v_list []; v_list [ v_nat 1; v_nat 2 ]; v_pair (v_nat 1) (v_str "x");
          v_some (v_nat 3); v_ctor 0 []; sample_entry;
          v_ref 2 (dig 5); v_handle 1 0; v_handle 3 70000 ])
    E4_kind.all;
  check "ND1 decode (encode n) = Ok n over 23 kinds x 20 payloads" !rt_ok;
  check "ND2 decode b = Ok n -> encode n = b (exactness)" !exact_ok;

  (* ND9: the address is sha256 of the node bytes and of nothing else. *)
  check "ND9 address = sha256 (encode n)"
    (E4_addr.Addr.hex (E4_node.address sample_node) = E4_sha256.hex b);
  check "ND9 the address moves when any byte of the node moves"
    (let n2 = E4_node.make ~version:0 ~kind:E4_kind.Export ~spec:(dig 1)
                ~payload:sample_entry in
     not (E4_addr.Addr.equal (E4_node.address sample_node) (E4_node.address n2)));

  (* make / encode refuse a spec that is not 32 bytes. *)
  check "the envelope refuses a spec that is not 32 bytes"
    (try
       ignore (E4_node.make ~version:0 ~kind:E4_kind.Export ~spec:"short" ~payload:v_unit);
       false
     with Invalid_argument _ -> true)

(* ============================================================ E4_node: the edge scan *)

let test_node_scan () =
  print_endline "-- E4_node: the edge scan (Val.refs / Val.malformedRef, Node.lean:241-266)";

  (* Node.lean:449-453 -- sampleNode has no refs and its one edge is the spec. *)
  check "N6 #guard sampleNode.refsOf = []" (E4_node.refs sample_node = []);
  check "N6 #guard sampleNode.malformedRef = false" (not (E4_node.malformed_ref sample_node));
  check "N6 #guard sampleNode.edges = [<schema, zeroDigest>]"
    (present_refs (E4_node.edges sample_node)
     = "schema:" ^ String.make 64 '0');
  check "N6 #guard sampleNode.checkedEdges = sampleNode.edges"
    (E4_node.checked_edges sample_node = E4_node.edges sample_node);
  check "N6 #guard (Node.mk 0 schema zeroDigest sampleEntry).checkedEdges = []"
    (E4_node.checked_edges
       (E4_node.make ~version:0 ~kind:E4_kind.Schema ~spec:zero32 ~payload:sample_entry)
     = []);
  check "ND7 is_genesis is schema AND the zero spec, and nothing else"
    (E4_node.is_genesis
       (E4_node.make ~version:0 ~kind:E4_kind.Schema ~spec:zero32 ~payload:v_unit)
     && not (E4_node.is_genesis
               (E4_node.make ~version:0 ~kind:E4_kind.Schema ~spec:(dig 1) ~payload:v_unit))
     && not (E4_node.is_genesis
               (E4_node.make ~version:0 ~kind:E4_kind.Export ~spec:zero32 ~payload:v_unit)));

  (* Node.lean:454-460 -- the #guards, with byte 16 replaced by the sentinel 127 (see the
     note in test_node_layout: 16 is `job` under CAS commit 1). *)
  check "N6 #guard (Val.ref 2 (replicate 32 1)).refs = [<export, 1…>]"
    (present_refs (E4_node.scan_refs (v_ref 2 (dig 1)))
     = "export:" ^ E4_hex.of_bytes (dig 1));
  check "N6 #guard (Val.ref <unregistered> _).refs = []"
    (E4_node.scan_refs (v_ref 127 (dig 1)) = []);
  check "N6 #guard (Val.ref <unregistered> _).malformedRef = true"
    (E4_node.scan_malformed_ref (v_ref 127 (dig 1)));
  check "N6 #guard (Val.ref 2 (replicate 31 1)).malformedRef = true"
    (E4_node.scan_malformed_ref (v_ref 2 (String.make 31 '\001')));
  check "N6 a registered kind byte with a 33-byte digest is malformed and yields no ref"
    (E4_node.scan_malformed_ref (v_ref 2 (String.make 33 '\001'))
     && E4_node.scan_refs (v_ref 2 (String.make 33 '\001')) = []);
  check "N6 #guard (Val.ctor 0 [ref 4 …7, nat 3, some (ref 6 …9)]).refs = [schema 7, annotation 9]"
    (present_refs
       (E4_node.scan_refs
          (v_ctor 0 [ v_ref 4 (dig 7); v_nat 3; v_some (v_ref 6 (dig 9)) ]))
     = "schema:" ^ E4_hex.of_bytes (dig 7) ^ ",annotation:" ^ E4_hex.of_bytes (dig 9));
  check "N6 #guard (Val.ctor 0 [ref 4 …7, nat 3]).malformedRef = false"
    (not (E4_node.scan_malformed_ref (v_ctor 0 [ v_ref 4 (dig 7); v_nat 3 ])));

  (* Node.lean:462-463 -- the AnyRef frame: 42 bytes, prefix 0b 00*7 21 02. *)
  let anyref = v_ref 2 zero32 in
  check "N9 #guard (Canonical.encode (AnyRef export zeroDigest)).length = 42"
    (String.length anyref = 42);
  check "N9 #guard its first ten bytes are [0x0b,0,0,0,0,0,0,0,0x21,0x02]"
    (String.sub anyref 0 10 = "\x0b\x00\x00\x00\x00\x00\x00\x00\x21\x02");

  (* L-SCAN-1: traversal order, left to right, descending only into 4, 5, 7, 10. *)
  let tree =
    v_pair
      (v_ctor 3
         [ v_ref 1 (dig 1);
           v_list [ v_ref 2 (dig 2); v_bytes (v_ref 5 (dig 99)); v_ref 3 (dig 3) ] ])
      (v_some (v_ref 4 (dig 4)))
  in
  check "L-SCAN-1 refs are left to right across pair, ctor, list and some"
    (present_refs (E4_node.scan_refs tree)
     = String.concat ","
         [ "source:" ^ E4_hex.of_bytes (dig 1);
           "export:" ^ E4_hex.of_bytes (dig 2);
           "type:" ^ E4_hex.of_bytes (dig 3);
           "schema:" ^ E4_hex.of_bytes (dig 4) ]);

  (* L-SCAN-2: a bytes payload that IS a valid ref frame yields no ref. *)
  let bytes_that_is_a_ref = v_bytes (v_ref 2 (dig 5)) in
  check "L-SCAN-2 a `bytes` frame holding a valid ref frame yields NO ref"
    (E4_node.scan_refs bytes_that_is_a_ref = []);
  check "L-SCAN-2 and it is not malformed either (Val.refs (.bytes bs) = [])"
    (not (E4_node.scan_malformed_ref bytes_that_is_a_ref));
  check "L-SCAN-2 the same bytes UNWRAPPED do yield the ref (the wrapper is what hides it)"
    (present_refs (E4_node.scan_refs (v_ref 2 (dig 5)))
     = "export:" ^ E4_hex.of_bytes (dig 5));
  check "L-SCAN-2 a `bytes` frame holding a malformed ref frame is still not malformed"
    (not (E4_node.scan_malformed_ref (v_bytes (v_ref 127 (dig 5)))));
  check "L-SCAN-2 nested: bytes inside a list inside a pair still hides its refs"
    (E4_node.scan_refs (v_pair (v_list [ v_bytes (v_ref 2 (dig 5)) ]) v_unit) = []);

  (* ND6: the handle scan (amendment M2). *)
  let with_handle = v_list [ v_handle 1 0; v_nat 5; v_some (v_handle 3 70000) ] in
  check "ND6 handles lists the tag-12 frames in traversal order"
    (E4_node.scan_handles with_handle = [ (1, 0); (3, 70000) ]);
  check "ND6 a handle key of 0 is the kind byte and no digits (Val.lean:1136)"
    (v_handle 1 0 = E4_be.framed 12 "\001");
  check "ND6 handle_in_content is true at a content kind, false at a run-relative one"
    (E4_node.handle_in_content
       (E4_node.make ~version:0 ~kind:E4_kind.Program ~spec:(dig 1) ~payload:with_handle)
     && not (E4_node.handle_in_content
               (E4_node.make ~version:0 ~kind:E4_kind.Tape ~spec:(dig 1)
                  ~payload:with_handle)));
  check "ND6 a node with no handle frame is never handle_in_content"
    (not (E4_node.handle_in_content sample_node))

(* ============================================================ E4_node: the refusals *)

let test_node_refusals () =
  print_endline "-- E4_node: payload refusals, the host limit, and the pure admission order";

  let refuses name p expected =
    check (Printf.sprintf "ND-frame %s -> %s" name (decode_error_name expected))
      (E4_node.payload_ok p = Error expected)
  in
  refuses "an empty payload" "" E4_node.Bad_frame;
  refuses "a truncated header" (String.sub (v_nat 5) 0 5) E4_node.Bad_frame;
  refuses "a declared length past the end"
    (String.sub (v_bytes "abcdef") 0 12) E4_node.Bad_frame;
  refuses "a bool of two bytes" (E4_be.framed 1 "\000\000") E4_node.Bad_frame;
  refuses "a bool byte other than 0/1" (E4_be.framed 1 "\002") E4_node.Bad_frame;
  refuses "a nat with a leading zero digit" (E4_be.framed 2 "\000\001") E4_node.Bad_frame;
  refuses "a string that is not valid UTF-8" (E4_be.framed 3 "\255") E4_node.Bad_frame;
  refuses "a unit with a payload" (E4_be.framed 9 "x") E4_node.Bad_frame;
  refuses "a none with a payload" (E4_be.framed 6 "x") E4_node.Bad_frame;
  refuses "a pair of one frame" (E4_be.framed 5 v_unit) E4_node.Bad_frame;
  refuses "a pair of three frames"
    (E4_be.framed 5 (v_unit ^ v_unit ^ v_unit)) E4_node.Trailing;
  refuses "a some of no frame" (E4_be.framed 7 "") E4_node.Bad_frame;
  refuses "a some of two frames" (E4_be.framed 7 (v_unit ^ v_unit)) E4_node.Trailing;
  refuses "a ctor with no index frame" (E4_be.framed 10 "") E4_node.Bad_frame;
  refuses "a ctor whose index frame is not a nat"
    (E4_be.framed 10 (v_str "x")) E4_node.Bad_frame;
  refuses "a ctor index with a leading zero digit"
    (E4_be.framed 10 (E4_be.framed 2 "\000\001")) E4_node.Bad_frame;
  refuses "a ref with an empty payload" (E4_be.framed 11 "") E4_node.Bad_frame;
  refuses "a handle with an empty payload" (E4_be.framed 12 "") E4_node.Bad_frame;
  refuses "a handle whose digits have a leading zero"
    (E4_be.framed 12 "\001\000\001") E4_node.Bad_frame;
  refuses "tag 0" (E4_be.framed 0 "") E4_node.Bad_frame;
  refuses "tag 13" (E4_be.framed 13 "") E4_node.Bad_frame;
  refuses "tag 255" (E4_be.framed 255 "") E4_node.Bad_frame;
  refuses "two frames where one is owed" (v_unit ^ v_unit) E4_node.Trailing;
  refuses "one frame and a trailing byte" (v_unit ^ "\000") E4_node.Trailing;

  check "ND-frame a well-formed tree is accepted"
    (E4_node.payload_ok sample_entry = Ok ()
     && E4_node.payload_ok (v_list []) = Ok ()
     && E4_node.payload_ok (v_ctor 0 []) = Ok ()
     && E4_node.payload_ok (v_nat 0) = Ok ()
     && E4_node.payload_ok (v_bytes "") = Ok ());
  check "ND-frame a nat above the host bound is NOT refused (deviation D1: Lean's Nat is unbounded)"
    (E4_node.payload_ok (E4_be.framed 2 (String.make 20 '\001')) = Ok ());

  (* ND8 / amendment M9: a frame length at or above 2^62. *)
  let two62 = "\064\000\000\000\000\000\000\000" in
  let oversize_frame = "\002" ^ two62 in
  check "ND8 a frame whose be64 length is 2^62 is Host_limit"
    (E4_node.payload_ok oversize_frame = Error E4_node.Host_limit);
  check "ND8 the same frame nested in a list is Host_limit"
    (E4_node.payload_ok (E4_be.framed 4 oversize_frame) = Error E4_node.Host_limit);
  check "ND8 a ctor whose index frame declares 2^62 is Host_limit"
    (E4_node.payload_ok (E4_be.framed 10 oversize_frame) = Error E4_node.Host_limit);
  check "ND8 a handle key of nine digits is Host_limit"
    (E4_node.payload_ok (E4_be.framed 12 ("\001" ^ String.make 9 '\001'))
     = Error E4_node.Host_limit);

  (* D3: the total forms answer emptily on a payload that does not parse. *)
  check "D3 refs/malformed/handles are [] / false / [] on a payload that does not parse"
    (E4_node.scan_refs oversize_frame = []
     && not (E4_node.scan_malformed_ref oversize_frame)
     && E4_node.scan_handles oversize_frame = []
     && E4_node.scan_payload oversize_frame = Error E4_node.Host_limit);

  (* ND10: the pure admission order of Store.lean:262-276. *)
  let node k v p = { E4_node.version = v; kind = k; spec = dig 1; payload = p } in
  let bad_payload = oversize_frame in
  let malformed = v_ref 127 (dig 1) in
  let handled = v_handle 1 3 in
  let says name n expected =
    let got = E4_node.check_pure n in
    let ok = got = Error expected in
    check
      (Printf.sprintf "ND10 %s -> %s" name (refusal_name expected))
      ok;
    if not ok then
      note "  got %s"
        (match got with Ok () -> "Ok" | Error e -> refusal_name e)
  in
  check "ND10 a well-formed content node is admitted"
    (E4_node.check_pure sample_node = Ok ());
  says "an unparseable payload" (node E4_kind.Program 0 bad_payload)
    (E4_node.Oversize E4_node.Host_limit);
  says "an unparseable payload AND a bad version (payload wins)"
    (node E4_kind.Program 1 bad_payload) (E4_node.Oversize E4_node.Host_limit);
  says "a bad version" (node E4_kind.Program 1 v_unit) (E4_node.Bad_version_byte 1);
  says "a bad version AND a malformed ref (version wins)"
    (node E4_kind.Program 1 malformed) (E4_node.Bad_version_byte 1);
  says "a malformed ref" (node E4_kind.Program 0 malformed) E4_node.Malformed_ref;
  says "a malformed ref AND a handle in content (malformed wins)"
    (node E4_kind.Program 0 (v_list [ malformed; handled ])) E4_node.Malformed_ref;
  says "a handle at a content kind (M2)" (node E4_kind.Program 0 handled)
    E4_node.Handle_in_content;
  check "ND10 the same handle payload at a run-relative kind is admitted (M2)"
    (E4_node.check_pure (node E4_kind.Tape 0 handled) = Ok ());
  check "ND10 oversize / bad_version / handle_in_content agree with check_pure"
    (E4_node.oversize (node E4_kind.Program 0 bad_payload)
     && not (E4_node.oversize sample_node)
     && E4_node.bad_version (node E4_kind.Program 1 v_unit)
     && not (E4_node.bad_version sample_node)
     && E4_node.handle_in_content (node E4_kind.Program 0 handled))

(* ============================================================ the goldens *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let strip s =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c -> match c with ' ' | '\n' | '\r' | '\t' -> () | _ -> Buffer.add_char b c)
    s;
  Buffer.contents b

let goldens_dir () =
  let rec ancestors d n acc =
    if n = 0 then List.rev acc else ancestors (Filename.dirname d) (n - 1) (d :: acc)
  in
  let here = Sys.getcwd () in
  let from_env = try [ Sys.getenv "E4_CAS_GOLDENS" ] with Not_found -> [] in
  (* Only ever ".../cas/goldens": a bare "<ancestor>/goldens" would find ocaml/goldens, which
     is a different lane's data. *)
  let per_ancestor a =
    (if Filename.basename a = "cas" then [ Filename.concat a "goldens" ] else [])
    @ [ Filename.concat a (Filename.concat "cas" "goldens");
        Filename.concat a (Filename.concat "engine" (Filename.concat "cas" "goldens"));
        Filename.concat a
          (Filename.concat "ocaml"
             (Filename.concat "engine" (Filename.concat "cas" "goldens"))) ]
  in
  let cands = from_env @ List.concat (List.map per_ancestor (ancestors here 9 [])) in
  List.find_opt
    (fun d -> d <> "" && (try Sys.is_directory d with Sys_error _ -> false))
    cands

let lines_of s =
  List.map
    (fun l ->
      if l <> "" && l.[String.length l - 1] = '\r' then String.sub l 0 (String.length l - 1)
      else l)
    (String.split_on_char '\n' s)

let words s = List.filter (fun x -> x <> "") (String.split_on_char ' ' s)

(* One golden file: its bytes, and what the node envelope makes of them. *)
type golden = { g_name : string; g_bytes : string; g_node : E4_node.t option }

let load_goldens dir =
  let files =
    List.sort compare
      (List.filter (fun f -> Filename.check_suffix f ".hex")
         (Array.to_list (Sys.readdir dir)))
  in
  List.filter_map
    (fun f ->
      let text = read_file (Filename.concat dir f) in
      match E4_hex.to_bytes (strip text) with
      | None ->
        check (Printf.sprintf "G-hex %s is valid hexadecimal" f) false;
        None
      | Some bytes ->
        let node = match E4_node.decode bytes with Ok n -> Some n | Error _ -> None in
        Some { g_name = Filename.remove_extension f; g_bytes = bytes; g_node = node })
    files

let check_manifest dir goldens =
  let path = Filename.concat dir "manifest.txt" in
  if not (Sys.file_exists path) then
    skip "G1 manifest.txt digests" "no manifest.txt in the goldens directory"
  else begin
    let rows =
      List.filter_map
        (fun l ->
          let l = String.trim l in
          if l = "" || l.[0] = '#' then None
          else
            match words l with
            | [ name; d ] -> Some (Filename.remove_extension name, String.lowercase_ascii d)
            | _ -> None)
        (lines_of (read_file path))
    in
    if rows = [] then
      skip "G1 manifest.txt digests" "manifest.txt has no `name sha256` rows"
    else begin
      let matched = ref 0 and bad = ref [] in
      List.iter
        (fun (name, expected) ->
          match List.find_opt (fun g -> g.g_name = name) goldens with
          | None -> bad := (name ^ " (no .hex)") :: !bad
          | Some g ->
            if E4_sha256.hex g.g_bytes = expected then incr matched else bad := name :: !bad)
        rows;
      check
        (Printf.sprintf "G-man manifest.txt: %d/%d rows agree with sha256 of the golden bytes"
           !matched (List.length rows))
        (!bad = []);
      if !bad <> [] then note "  rows that disagree: %s" (String.concat " " !bad)
    end
  end

(* cases.txt is `name<TAB>family<TAB>expected` (its own header says so).  This lane owns the
   families a1 (sha256 over Val.encode), g1 (node encodings and addresses), g2's PURE rows
   (the admission tests that are functions of the node alone) and g5 (the edge scan).  The
   rest — g2's store-relative rows, g3, g4, g4entries, g6, g7 — belong to lanes P3/P4/P8; what
   P0 checks there is that their bytes are one well-formed frame tree, which is a real test of
   the walk against 45 nontrivial trees Lean cut. *)

(* A node from bytes WITHOUT the decoder's checks: g2's refused cases must still reach
   check_pure, and `decode` refuses some of them before it can build a `t`. *)
let raw_node bytes =
  if String.length bytes < 34 then None
  else
    match E4_kind.of_byte (Char.code bytes.[1]) with
    | None -> None
    | Some kind ->
      Some
        { E4_node.version = Char.code bytes.[0];
          kind;
          spec = String.sub bytes 2 32;
          payload = String.sub bytes 34 (String.length bytes - 34) }

let is_hex64 s =
  String.length s = 64
  && (match E4_hex.to_bytes s with Some _ -> true | None -> false)

(* g5's expected column: `refs=<kindbyte>:<hex>,…;malformed=<bool>` *)
let parse_g5 expected =
  let parts = String.split_on_char ';' expected in
  let field k =
    List.fold_left
      (fun acc p ->
        let kv = String.split_on_char '=' p in
        match kv with
        | [ key; v ] when String.trim key = k -> Some (String.trim v)
        | key :: rest when String.trim key = k -> Some (String.concat "=" rest)
        | _ -> acc)
      None parts
  in
  match field "refs", field "malformed" with
  | Some r, Some m ->
    let refs = if String.trim r = "" then [] else String.split_on_char ',' r in
    Some (List.map String.lowercase_ascii refs, String.lowercase_ascii m = "true")
  | _ -> None

let check_cases dir goldens =
  let path = Filename.concat dir "cases.txt" in
  if not (Sys.file_exists path) then begin
    skip "a1/G1/G2/G5 cases.txt expectations" "no cases.txt in the goldens directory";
    skip "G3/G4/G6/G7 cases.txt frame trees" "no cases.txt in the goldens directory"
  end
  else begin
    let rows =
      List.filter_map
        (fun l ->
          if String.trim l = "" || (String.length l > 0 && l.[0] = '#') then None
          else
            match String.split_on_char '\t' l with
            | name :: family :: rest when name <> "" ->
              Some
                ( Filename.remove_extension (String.trim name),
                  String.trim family,
                  String.trim (String.concat "\t" rest) )
            | _ -> None)
        (lines_of (read_file path))
    in
    if rows = [] then begin
      skip "a1/G1/G2/G5 cases.txt expectations" "cases.txt has no `name<TAB>family<TAB>…` rows";
      skip "G3/G4/G6/G7 cases.txt frame trees" "cases.txt has no rows"
    end
    else begin
      note "%d case row(s) in cases.txt" (List.length rows);
      (* per-group tallies: (ok, total, failing names) *)
      let tally = Hashtbl.create 8 in
      let record group ok name detail =
        let o, t, bad = try Hashtbl.find tally group with Not_found -> (0, 0, []) in
        Hashtbl.replace tally group
          ((if ok then o + 1 else o), t + 1, if ok then bad else name :: bad);
        if not ok then note "  %s %s: %s" group name detail
      in
      let m2_pending = ref [] in
      let k1_pending = ref [] in
      (* The goldens were cut from TODAY's Lean, whose Kind table stops at 15
         (src/Effect4/Store/Kind.lean:96-98).  This side carries CAS commit 1's append, so a
         ref frame at kind byte 16..23 is registered here and unregistered there.  These two
         projections are "what Lean's table would say", and a row that agrees under them is a
         pending re-cut, not a disagreement. *)
      let lean_refs s =
        List.filter (fun r -> E4_kind.in_lean r.E4_addr.Ref.kind) s.E4_node.refs
      in
      let lean_malformed s =
        s.E4_node.malformed
        || List.exists (fun r -> not (E4_kind.in_lean r.E4_addr.Ref.kind)) s.E4_node.refs
      in
      (* A row whose expected column is a 64-character digest: the bytes hash to it, and they
         are either a node envelope that re-encodes exactly and addresses to it, or one
         well-formed frame tree. *)
      let hexy group name bytes node sha expected =
        let shape_ok =
          match node with
          | Some n ->
            E4_node.encode n = bytes && E4_addr.Addr.hex (E4_node.address n) = expected
          | None -> E4_node.payload_ok bytes = Ok ()
        in
        record group (sha = expected && shape_ok) name
          (Printf.sprintf "sha256 %s vs %s; re-encode/address %b" sha expected shape_ok)
      in
      List.iter
        (fun (name, family, expected) ->
          match List.find_opt (fun g -> g.g_name = name) goldens with
          | None -> record family false name "no <name>.hex beside cases.txt"
          | Some g ->
            let bytes = g.g_bytes in
            let sha = E4_sha256.hex bytes in
            (match family with
             | "a1" ->
               if is_hex64 expected then
                 record "a1" (sha = expected) name
                   (Printf.sprintf "sha256 is %s, cases.txt says %s" sha expected)
               else
                 record "a1"
                   (E4_node.payload_ok bytes = Ok ())
                   name "the bytes are not one well-formed frame tree"
             | "g1" ->
               (* expected is the address = sha256 of these very bytes, whether they are a
                  node envelope or a bare Val frame (g1-anyref-frame, g1-sampleEntry-payload,
                  g1-canonical-digest-frame are frames). *)
               hexy "g1" name bytes g.g_node sha expected
             | "g2" ->
               let word = match words expected with w :: _ -> w | [] -> "" in
               if is_hex64 word then hexy "g2" name bytes g.g_node sha word
               else begin
                 match raw_node bytes with
                 | None -> record "g2" false name "the bytes are not a node envelope"
                 | Some n ->
                   let got = E4_node.check_pure n in
                   let want_ok =
                     match word with
                     | "fresh" | "duplicate" | "conflict" | "dangling" | "wrongKind" -> true
                     | _ -> false
                   in
                   let lean_says_malformed =
                     match E4_node.scan_payload n.E4_node.payload with
                     | Ok s -> lean_malformed s
                     | Error _ -> false
                   in
                   (match word, got with
                    | "badVersion", Error (E4_node.Bad_version_byte _) -> record "g2" true name ""
                    | "malformedRef", Error E4_node.Malformed_ref -> record "g2" true name ""
                    | "oversize", Error (E4_node.Oversize _) -> record "g2" true name ""
                    | "malformedRef", Ok () when lean_says_malformed ->
                      (* the ref's kind byte is 16..23: unregistered in today's Lean, a
                         registered kind here.  CAS commit 1 is what closes this. *)
                      k1_pending := name :: !k1_pending;
                      record "g2" true name ""
                    | _, Error E4_node.Handle_in_content when want_ok ->
                      (* amendment M2 is not in Lean yet: Lean admits a handle in content and
                         this side refuses it.  The divergence is exactly here, by design. *)
                      m2_pending := name :: !m2_pending;
                      record "g2" true name ""
                    | _, Ok () when want_ok -> record "g2" true name ""
                    | _ ->
                      record "g2" false name
                        (Printf.sprintf "Lean says %s, check_pure says %s" word
                           (match got with Ok () -> "Ok" | Error e -> refusal_name e)))
               end
             | "g5" ->
               (match parse_g5 expected with
                | None -> record "g5" false name ("unreadable expected column: " ^ expected)
                | Some (want_refs, want_malformed) ->
                  (match E4_node.scan_payload bytes with
                   | Error e ->
                     record "g5" false name
                       ("the bytes are not a frame tree: " ^ decode_error_name e)
                   | Ok s ->
                     let got_refs =
                       List.map
                         (fun r ->
                           string_of_int (E4_kind.byte r.E4_addr.Ref.kind) ^ ":"
                           ^ E4_addr.Addr.hex r.E4_addr.Ref.addr)
                         s.E4_node.refs
                     in
                     let ok =
                       got_refs = want_refs && s.E4_node.malformed = want_malformed
                     in
                     let lean_got =
                       List.map
                         (fun r ->
                           string_of_int (E4_kind.byte r.E4_addr.Ref.kind) ^ ":"
                           ^ E4_addr.Addr.hex r.E4_addr.Ref.addr)
                         (lean_refs s)
                     in
                     let ok_under_lean_table =
                       lean_got = want_refs && lean_malformed s = want_malformed
                     in
                     if (not ok) && ok_under_lean_table then
                       k1_pending := name :: !k1_pending;
                     record "g5" (ok || ok_under_lean_table) name
                       (Printf.sprintf "refs [%s] vs [%s]; malformed %b vs %b"
                          (String.concat "," got_refs) (String.concat "," want_refs)
                          s.E4_node.malformed want_malformed)))
             | _ ->
               (* g3, g4, g4entries, g6, g7: the tool-side projections, except the rows whose
                  expected column is a digest (g6-treeNode) — those are node encodings. *)
               let word = match words expected with w :: _ -> w | [] -> "" in
               if is_hex64 word then hexy "other" name bytes g.g_node sha word
               else
                 record "other"
                   (E4_node.payload_ok bytes = Ok ())
                   name "the bytes are not one well-formed frame tree"))
        rows;
      Hashtbl.iter
        (fun group (ok, total, _) ->
          check (Printf.sprintf "G-case family %s: %d/%d rows agree" group ok total)
            (ok = total))
        tally;
      if !m2_pending <> [] then begin
        note "amendment M2 is not in Lean yet: %s" (String.concat " " !m2_pending);
        note "  Lean admits a handle frame in a content payload (`fresh`); check_pure refuses";
        note "  it as Handle_in_content.  When CAS commit 7 lands, G2 must be re-cut."
      end;
      if !k1_pending <> [] then begin
        note "CAS commit 1 is not in Lean yet: %s" (String.concat " " !k1_pending);
        note "  these rows use kind byte 16 as `the unregistered byte`; 16 is `job` under the";
        note "  append, and amendment M4 moved the sentinel to 127.  Each row agrees under";
        note "  today's 15-row Lean table and must be re-cut at 127 with CAS commit 1."
      end
    end
  end

let check_goldens () =
  print_endline "-- the goldens of ocaml/engine/cas/goldens";
  match goldens_dir () with
  | None ->
    skip "G-man manifest.txt digests" "goldens/ not found";
    skip "a1/G1/G2/G5 cases.txt expectations" "goldens/ not found";
    skip "G3/G4/G6/G7 cases.txt frame trees" "goldens/ not found";
    skip "G-bytes every golden is a node or a frame tree" "goldens/ not found";
    skip "G-mut the golden mutation check" "goldens/ not found";
    note "searched from %s; set E4_CAS_GOLDENS to point at the directory" (Sys.getcwd ());
    note "lane GLD had not cut ocaml/engine/cas/goldens when this lane ran"
  | Some dir ->
    note "goldens directory: %s" dir;
    let goldens = load_goldens dir in
    if goldens = [] then begin
      skip "G-man manifest.txt digests" "no *.hex files in the goldens directory";
      skip "a1/G1/G2/G5 cases.txt expectations" "no *.hex files";
      skip "G3/G4/G6/G7 cases.txt frame trees" "no *.hex files";
      skip "G-bytes every golden is a node or a frame tree" "no *.hex files";
      skip "G-mut the golden mutation check" "no *.hex files"
    end
    else begin
      note "%d golden file(s)" (List.length goldens);
      (* Every golden's bytes are either a node envelope that re-encodes to itself exactly
         (ND2), or one well-formed frame tree.  g2's refused cases (a version byte of 1) are
         neither, and are named. *)
      let shaped = ref 0 and unshaped = ref [] in
      List.iter
        (fun g ->
          let ok =
            match g.g_node with
            | Some n -> E4_node.encode n = g.g_bytes
            | None -> E4_node.payload_ok g.g_bytes = Ok ()
          in
          if ok then incr shaped else unshaped := g.g_name :: !unshaped)
        goldens;
      check
        (Printf.sprintf
           "G-bytes %d/%d goldens are a node that re-encodes exactly, or one frame tree"
           !shaped (List.length goldens))
        (List.length !unshaped <= 1);
      if !unshaped <> [] then
        note "  neither: %s (expected: g2-badVersion alone)" (String.concat " " !unshaped);

      check_manifest dir goldens;
      check_cases dir goldens;

      (* The mutation check: flip one byte of a golden and the comparison must go red. *)
      match List.find_opt (fun g -> String.length g.g_bytes > 0) goldens with
      | None -> skip "G-mut the golden mutation check" "every golden file is empty"
      | Some g ->
        let expected = E4_sha256.hex g.g_bytes in
        let agrees b = E4_sha256.hex b = expected in
        let i = String.length g.g_bytes - 1 in
        let m = Bytes.of_string g.g_bytes in
        Bytes.set m i (Char.chr (Char.code (Bytes.get m i) lxor 0x01));
        let flipped = Bytes.to_string m in
        check
          (Printf.sprintf "G-mut %s: the golden agrees, and one flipped byte does not"
             g.g_name)
          (agrees g.g_bytes && not (agrees flipped))
    end


(* The mutation check that does not need a golden: it pins that the comparison this file
   performs is capable of failing at all. *)
let test_mutation_local () =
  print_endline "-- the mutation check on a locally built node";
  let b = E4_node.encode sample_node in
  let expected = E4_sha256.hex b in
  let flip i =
    let m = Bytes.of_string b in
    Bytes.set m i (Char.chr (Char.code (Bytes.get m i) lxor 0x01));
    Bytes.to_string m
  in
  let all_red = ref true in
  for i = 0 to String.length b - 1 do
    let m = flip i in
    if E4_sha256.hex m = expected then all_red := false;
    (* and the envelope notices too: either it refuses, or it decodes to a different node *)
    (match E4_node.decode m with
     | Error _ -> ()
     | Ok n -> if E4_node.encode n = b then all_red := false)
  done;
  check "G-mut every one-bit flip of the sample node changes the address and the bytes"
    !all_red;
  check "G-mut the unflipped node still agrees" (E4_sha256.hex b = expected)

let () =
  test_crc ();
  test_kind ();
  test_addr ();
  test_node_layout ();
  test_node_scan ();
  test_node_refusals ();
  test_mutation_local ();
  check_goldens ();
  if !skips > 0 then Printf.printf "== %d skipped ==\n" !skips;
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
