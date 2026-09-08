(* test_math.ml — the checks of the engine's math modules (lane M, 2026-09-08).

   What it checks, and against what:
     N*  E4_nat: the 63-bit host profile of ocaml/gen/NOTES.md §5, including a differential
         against `pow_reference` (Translate.powClamped transcribed literally) and the edge
         triple 2^62-1 / 2^62 / max_int.
     S*  E4_sha256: the FIPS 180-4 vectors ("", "abc", the 56- and 112-byte messages, one
         million 'a'), the two byte-vector #guards of src/Effect4/Store/Digest.lean:302-303,
         the third #guard (:315) over `Val.encode sampleEntry` — whose input is BUILT here
         out of E4_be frames from src/Effect4/Store/Val.lean:1150 and checked against that
         file's own three shape #guards (:1153-1155) — the streaming law, and the throughput
         of a 64 MiB buffer.
     H*  E4_hex: the #guards of Digest.lean:306-314 and the two round-trip laws as
         properties over pseudo-random input (a fixed LCG, so the run is reproducible).
     B*  E4_be: be64/framing/nat-digit laws, the refusals, and the golden bytes of
         ocaml/eff/goldens (two embedded verbatim, plus every *.bin in that directory when
         the test can find it).
   Exit code 0 iff every check passed. *)

open Effect4_engine

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* A fixed linear congruential generator: the run is reproducible. *)
let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed

let rand n = if n <= 0 then 0 else next_rand () mod n

let rand_bytes n =
  String.init n (fun _ -> Char.chr (rand 256))

(* ============================================================ E4_nat *)

let two_62_minus_1 = E4_nat.max_nat (* 4611686018427387903 on a 63-bit host *)

let test_nat () =
  print_endline "-- E4_nat: the 63-bit host profile (ocaml/gen/NOTES.md §5)";
  check "N4 bits = Sys.int_size" (E4_nat.bits = Sys.int_size);
  check "N4 max_nat = max_int and is 2^(bits-1) - 1"
    (E4_nat.max_nat = max_int && E4_nat.max_nat = (1 lsl (E4_nat.bits - 1)) - 1);
  check "N4 wire_limit = max_nat (D1: 2^62 is not an OCaml int)"
    (E4_nat.wire_limit = E4_nat.max_nat);
  check "N4 fits_wire: 0, max_nat yes; -1 no"
    (E4_nat.fits_wire 0 && E4_nat.fits_wire E4_nat.max_nat && not (E4_nat.fits_wire (-1)));
  check "N4 is_nat 0 / max_nat / -1" (E4_nat.is_nat 0 && E4_nat.is_nat max_int && not (E4_nat.is_nat (-1)));

  (* pow: the rule table of NOTES.md §5 and Translate.lean:127-137 *)
  check "N1 pow 2 10 = 1024" (E4_nat.pow 2 10 = 1024);
  check "N1 pow 2 61 = 2^61 exactly" (E4_nat.pow 2 61 = 1 lsl 61);
  check "N1 pow 2 62 = max_nat (2^62 saturates)" (E4_nat.pow 2 62 = E4_nat.max_nat);
  check "N1 pow 2 64 = max_nat (Val.wf's `< 2^64` reads as `< max_int`)"
    (E4_nat.pow 2 64 = E4_nat.max_nat);
  check "N1 pow 10 18 = 10^18 exactly" (E4_nat.pow 10 18 = 1_000_000_000_000_000_000);
  check "N1 pow 10 19 = max_nat" (E4_nat.pow 10 19 = E4_nat.max_nat);
  check "N1 pow 0 0 = 1, pow 0 5 = 0, pow 5 0 = 1"
    (E4_nat.pow 0 0 = 1 && E4_nat.pow 0 5 = 0 && E4_nat.pow 5 0 = 1);
  check "N1 pow 1 max_nat = 1 (terminates: the fixed-point exit)" (E4_nat.pow 1 max_int = 1);
  check "N1 pow 2 1000000000 = max_nat (terminates)" (E4_nat.pow 2 1_000_000_000 = E4_nat.max_nat);
  let pow_exact_ok = ref true in
  for b = 0 to 61 do
    if E4_nat.pow 2 b <> 1 lsl b then pow_exact_ok := false
  done;
  check "N1 pow 2 b = 1 lsl b for every b <= 61" !pow_exact_ok;
  let diff_ok = ref true in
  let diff_n = ref 0 in
  for a = 0 to 20 do
    for b = 0 to 70 do
      incr diff_n;
      if E4_nat.pow a b <> E4_nat.pow_reference a b then diff_ok := false
    done
  done;
  check (Printf.sprintf "N7 pow = Translate.powClamped on %d (a,b) pairs" !diff_n) !diff_ok;

  (* literals *)
  check "N1 of_lit_decimal \"1947\" = 1947" (E4_nat.of_lit_decimal "1947" = Some 1947);
  check "N1 of_lit_decimal \"0\" = 0" (E4_nat.of_lit_decimal "0" = Some 0);
  check "N1 of_lit_decimal (2^62 - 1) is exact"
    (E4_nat.of_lit_decimal "4611686018427387903" = Some E4_nat.max_nat);
  check "N1 of_lit_decimal (2^62) saturates to max_nat"
    (E4_nat.of_lit_decimal "4611686018427387904" = Some E4_nat.max_nat);
  check "N1 of_lit_decimal (2^64) saturates to max_nat"
    (E4_nat.of_lit_decimal "18446744073709551616" = Some E4_nat.max_nat);
  check "N1 of_lit_decimal refuses \"\" and \"12a\""
    (E4_nat.of_lit_decimal "" = None && E4_nat.of_lit_decimal "12a" = None);
  check "N1 of_lit is the identity in range, max_nat on a negative"
    (E4_nat.of_lit 7 = 7 && E4_nat.of_lit 0 = 0 && E4_nat.of_lit (-1) = E4_nat.max_nat);

  (* N2: Lean's division *)
  check "N2 div 7 2 = 3, div 7 0 = 0, div 0 0 = 0"
    (E4_nat.div 7 2 = 3 && E4_nat.div 7 0 = 0 && E4_nat.div 0 0 = 0);
  check "N2 rem 7 2 = 1, rem 7 0 = 7, rem 0 0 = 0"
    (E4_nat.rem 7 2 = 1 && E4_nat.rem 7 0 = 7 && E4_nat.rem 0 0 = 0);
  check "N2 div/rem never raise Division_by_zero"
    (try
       ignore (E4_nat.div max_int 0);
       ignore (E4_nat.rem max_int 0);
       true
     with _ -> false);

  (* N3: truncated subtraction *)
  check "N3 sub 5 3 = 2, sub 3 5 = 0, sub 0 max_nat = 0"
    (E4_nat.sub 5 3 = 2 && E4_nat.sub 3 5 = 0 && E4_nat.sub 0 max_int = 0);
  check "N3 pred 0 = 0, pred 1 = 0" (E4_nat.pred 0 = 0 && E4_nat.pred 1 = 0);

  (* N1: saturating add / mul / succ *)
  check "N1 add max_nat 1 = max_nat, add max_nat max_nat = max_nat"
    (E4_nat.add max_int 1 = E4_nat.max_nat && E4_nat.add max_int max_int = E4_nat.max_nat);
  check "N1 add is exact below the bound" (E4_nat.add 2 3 = 5 && E4_nat.add 0 max_int = max_int);
  check "N1 mul max_nat 2 = max_nat, mul is exact below the bound"
    (E4_nat.mul max_int 2 = E4_nat.max_nat && E4_nat.mul 6 7 = 42 && E4_nat.mul 0 max_int = 0);
  check "N1 succ max_nat = max_nat" (E4_nat.succ max_int = E4_nat.max_nat);
  check "N1 saturates max_nat 2 / 2 3 / 0 anything"
    (E4_nat.saturates max_int 2 && not (E4_nat.saturates 2 3)
     && not (E4_nat.saturates 0 max_int));

  (* N5: guarded shifts *)
  check "N5 shift_left 1 61 = 2^61, shift_left 1 62 = max_nat"
    (E4_nat.shift_left 1 61 = 1 lsl 61 && E4_nat.shift_left 1 62 = E4_nat.max_nat);
  check "N5 shift_left 3 62 = max_nat, shift_left 0 100 = 0"
    (E4_nat.shift_left 3 62 = E4_nat.max_nat && E4_nat.shift_left 0 100 = 0);
  check "N5 shift_right 1024 3 = 128" (E4_nat.shift_right 1024 3 = 128);
  check "N5 shift_right max_nat 62 = 0 and at bits/64/1000 = 0 (OCaml's lsr is undefined there)"
    (E4_nat.shift_right max_int 62 = 0
     && E4_nat.shift_right max_int E4_nat.bits = 0
     && E4_nat.shift_right max_int 64 = 0
     && E4_nat.shift_right max_int 1000 = 0);
  check "N5 land_/lor_/lxor_"
    (E4_nat.land_ 0xf0 0x3c = 0x30 && E4_nat.lor_ 0xf0 0x0c = 0xfc
     && E4_nat.lxor_ 0xff 0x0f = 0xf0);

  (* the edge triple: 2^62 - 1, 2^62, max_int *)
  check "edge 2^62-1 = max_int is carried exactly"
    (two_62_minus_1 = 4611686018427387903 && E4_nat.of_lit two_62_minus_1 = two_62_minus_1);
  check "edge 2^62 is unreachable: every route to it answers max_nat"
    (E4_nat.pow 2 62 = E4_nat.max_nat
     && E4_nat.shift_left 1 62 = E4_nat.max_nat
     && E4_nat.add two_62_minus_1 1 = E4_nat.max_nat
     && E4_nat.of_lit_decimal "4611686018427387904" = Some E4_nat.max_nat);
  check "edge max_int is a fixed point of succ/add 1/mul 1"
    (E4_nat.succ max_int = max_int && E4_nat.add max_int 1 = max_int
     && E4_nat.mul max_int 1 = max_int);

  (* N6: totality over a grid *)
  let grid = [ 0; 1; 2; 3; 7; 63; 64; 255; 1947; 1 lsl 31; 1 lsl 61; two_62_minus_1; max_int ] in
  let total_ok = ref true in
  let n_ops = ref 0 in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          incr n_ops;
          try
            ignore (E4_nat.add a b);
            ignore (E4_nat.sub a b);
            ignore (E4_nat.mul a b);
            ignore (E4_nat.div a b);
            ignore (E4_nat.rem a b);
            ignore (E4_nat.pow a b);
            ignore (E4_nat.shift_left a b);
            ignore (E4_nat.shift_right a b);
            ignore (E4_nat.land_ a b);
            ignore (E4_nat.lor_ a b);
            ignore (E4_nat.lxor_ a b);
            ignore (E4_nat.succ a);
            ignore (E4_nat.pred a);
            ignore (E4_nat.saturates a b)
          with _ -> total_ok := false)
        grid)
    grid;
  check (Printf.sprintf "N6 total: 14 operations over %d input pairs, no exception" !n_ops) !total_ok

(* ============================================================ E4_hex *)

let test_hex () =
  print_endline "-- E4_hex: Digest.lean:62-93 and its #guards (:306-314)";
  check "H1 of_bytes [255;10] = \"ff0a\"" (E4_hex.of_bytes "\xff\x0a" = "ff0a");
  check "H1 of_bytes \"\" = \"\"" (E4_hex.of_bytes "" = "");
  check "H2 to_bytes \"ff00\" = Some [255;0]" (E4_hex.to_bytes "ff00" = Some "\xff\x00");
  check "H2 to_bytes \"FF0a\" = Some [255;10] (either case)"
    (E4_hex.to_bytes "FF0a" = Some "\xff\x0a");
  check "H5 to_bytes \"g0\" = None" (E4_hex.to_bytes "g0" = None);
  check "H5 to_bytes \"0\" = None (odd length)" (E4_hex.to_bytes "0" = None);
  check "H5 to_bytes \"\" = Some \"\"" (E4_hex.to_bytes "" = Some "");
  check "H5 to_bytes refuses a non-digit anywhere"
    (E4_hex.to_bytes "00ff0z" = None && E4_hex.to_bytes "z0" = None
     && E4_hex.to_bytes "00 0f" = None);
  (* H3: to_bytes (of_bytes b) = Some b *)
  let h3_ok = ref true in
  for _ = 1 to 400 do
    let b = rand_bytes (rand 40) in
    if E4_hex.to_bytes (E4_hex.of_bytes b) <> Some b then h3_ok := false
  done;
  check "H3 to_bytes (of_bytes b) = Some b, 400 random byte strings" !h3_ok;
  (* H4: what decodes, re-printed, is the input lowercased *)
  let h4_ok = ref true in
  for _ = 1 to 400 do
    let b = rand_bytes (rand 40) in
    let h = E4_hex.of_bytes b in
    let mixed =
      String.map (fun c -> if rand 2 = 0 then Char.uppercase_ascii c else c) h
    in
    (match E4_hex.to_bytes mixed with
     | Some d -> if E4_hex.of_bytes d <> String.lowercase_ascii mixed then h4_ok := false
     | None -> h4_ok := false)
  done;
  check "H4 of_bytes (to_bytes h) = lowercase h, 400 mixed-case strings" !h4_ok;
  let empty_hex = E4_sha256.hex "" in
  check "H2 digest_of_hex of the uppercase e3b0… digest = digest \"\""
    (E4_hex.digest_of_hex (String.uppercase_ascii empty_hex) = Some (E4_sha256.digest ""));
  check "H5 digest_of_hex \"e3b0\" = None, \"\" = None"
    (E4_hex.digest_of_hex "e3b0" = None && E4_hex.digest_of_hex "" = None);
  check "H1 of_bytes output is lowercase and 2n long"
    (String.length empty_hex = 64
     && String.for_all (fun c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) empty_hex)

(* ============================================================ E4_be *)

(* The two goldens embedded verbatim (ocaml/eff/goldens/{p42,pAcquire}.bin, 2026-09-08). *)
let golden_p42_hex =
  "0a00000000000000390200000000000000000a0000000000000027020000000000000001010a00000000000000\
   14020000000000000001010200000000000000012a"

let golden_pacquire_hex =
  "0a000000000000009f020000000000000001160a000000000000004b020000000000000001060a000000000000\
   00090200000000000000000a0000000000000026020000000000000001010a00000000000000130200000000000\
   00001010200000000000000000a0000000000000038020000000000000001060a000000000000000a0200000000\
   0000000101 0a0000000000000012020000000000000000020000000000000000"

let strip_ws s = String.concat "" (String.split_on_char ' ' (String.concat "" (String.split_on_char '\n' s)))

let unhex s =
  match E4_hex.to_bytes (strip_ws s) with
  | Some b -> b
  | None -> failwith "test_math: bad embedded golden"

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let goldens_dir () =
  let candidates =
    [ (try Sys.getenv "E4_GOLDENS" with Not_found -> "");
      (* from _build/default/test, both standalone and in the ocaml workspace *)
      Filename.concat ".." (Filename.concat ".." (Filename.concat ".." (Filename.concat ".." (Filename.concat "eff" "goldens"))));
      Filename.concat ".." (Filename.concat "eff" "goldens");
      Filename.concat "ocaml" (Filename.concat "eff" "goldens") ]
  in
  List.find_opt (fun d -> d <> "" && Sys.file_exists d && Sys.is_directory d) candidates

let check_golden name bytes =
  match E4_be.exact_frame bytes with
  | None -> false
  | Some (tag, payload) ->
    let reframed = E4_be.framed tag payload in
    let ok =
      reframed = bytes
      && String.length payload = String.length bytes - E4_be.header_length
      && (match E4_be.read_frame bytes 0 (String.length bytes) with
          | Some (t, p, e, next) ->
            t = tag && p = E4_be.header_length && e = String.length bytes
            && next = String.length bytes
          | None -> false)
    in
    if not ok then Printf.printf "      golden %s: outer frame mismatch\n" name;
    ok

let test_be () =
  print_endline "-- E4_be: the framing of Canonical.lean / Wire.lean as eff_frame.ml writes it";
  check "B2 be64 0 is eight zero bytes" (E4_be.be64 0 = "\000\000\000\000\000\000\000\000");
  check "B2 be64 1 / 0x39 / 0x0102030405060708"
    (E4_be.be64 1 = "\000\000\000\000\000\000\000\001"
     && E4_be.be64 0x39 = "\000\000\000\000\000\000\000\x39"
     && E4_be.be64 0x0102030405060708 = "\001\002\003\004\005\006\007\008");
  check "B2 framed 10 \"\" is nine bytes, tag then a zero length"
    (E4_be.framed 10 "" = "\010\000\000\000\000\000\000\000\000");
  check "B2 framed tag p = tag :: be64 (length p) ++ p"
    (let p = "hello" in
     E4_be.framed 3 p = String.make 1 '\003' ^ E4_be.be64 5 ^ p);
  check "B2 frame_length n = 9 + n" (E4_be.frame_length 0 = 9 && E4_be.frame_length 65 = 74);
  (* be64 round trip *)
  let be_ok = ref true in
  for _ = 1 to 2000 do
    let n = (next_rand () lsl 31) lor next_rand () in
    let n = n land E4_nat.max_nat in
    if E4_be.read_be64 (E4_be.be64 n) 0 <> Some n then be_ok := false
  done;
  check "B2 read_be64 (be64 n) = Some n, 2000 random n in 0..max_nat" !be_ok;
  check "B5 read_be64 refuses a top byte >= 0x40 (a length at or above 2^62)"
    (E4_be.read_be64 "\x40\000\000\000\000\000\000\000" 0 = None
     && E4_be.read_be64 "\xff\xff\xff\xff\xff\xff\xff\xff" 0 = None
     && E4_be.read_be64 "\x3f\xff\xff\xff\xff\xff\xff\xff" 0 = Some E4_nat.max_nat);
  check "B4 read_be64 refuses a truncated window and a negative position"
    (E4_be.read_be64 "\000\000\000\000\000\000\000" 0 = None
     && E4_be.read_be64 (E4_be.be64 1) 1 = None
     && E4_be.read_be64 (E4_be.be64 1) (-1) = None);
  check "B4 be64 raises Invalid_argument on a negative int"
    (try ignore (E4_be.be64 (-1)); false with Invalid_argument _ -> true | _ -> false);
  (* frames *)
  check "B4 read_frame refuses a header shorter than 9 bytes"
    (E4_be.read_frame "\010\000\000\000\000" 0 5 = None && E4_be.read_frame "" 0 0 = None);
  check "B4 read_frame refuses a length that runs past the limit"
    (let f = E4_be.framed 4 "abcd" in
     E4_be.read_frame f 0 (String.length f - 1) = None);
  check "B4 exact_frame refuses trailing bytes"
    (E4_be.exact_frame (E4_be.framed 9 "" ^ "\000") = None);
  check "B4 exact_frame (framed t p) = Some (t, p)"
    (E4_be.exact_frame (E4_be.framed 12 "\001\007") = Some (12, "\001\007"));
  let frame_ok = ref true in
  for _ = 1 to 1000 do
    let tag = rand 256 in
    let p = rand_bytes (rand 60) in
    let f = E4_be.framed tag p in
    if E4_be.exact_frame f <> Some (tag, p) then frame_ok := false;
    if String.length f <> 9 + String.length p then frame_ok := false
  done;
  check "B2 exact_frame (framed tag p) = Some (tag, p), 1000 random frames" !frame_ok;
  (* nat digits *)
  check "B3 nat_digits 0 = \"\", 1 = [1], 255 = [255], 256 = [1;0], 1947 = [0x07;0x9b]"
    (E4_be.nat_digits 0 = "" && E4_be.nat_digits 1 = "\001" && E4_be.nat_digits 255 = "\xff"
     && E4_be.nat_digits 256 = "\001\000" && E4_be.nat_digits 1947 = "\x07\x9b");
  let nat_ok = ref true in
  for _ = 1 to 2000 do
    let n = ((next_rand () lsl 31) lor next_rand ()) land E4_nat.max_nat in
    if E4_be.nat_of_digits (E4_be.nat_digits n) <> Some n then nat_ok := false;
    let d = E4_be.nat_digits n in
    if String.length d > 0 && String.unsafe_get d 0 = '\000' then nat_ok := false
  done;
  check "B3 nat_of_digits (nat_digits n) = Some n and no leading zero, 2000 random n" !nat_ok;
  check "B4 nat_of_digits refuses a leading zero digit"
    (E4_be.nat_of_digits "\000\017" = None && E4_be.nat_of_digits "\000" = None);
  check "B5 nat_of_digits refuses nine digits and eight with a top byte >= 0x40"
    (E4_be.nat_of_digits (String.make 9 '\001') = None
     && E4_be.nat_of_digits ("\x40" ^ String.make 7 '\000') = None
     && E4_be.nat_of_digits ("\x3f" ^ String.make 7 '\xff') = Some E4_nat.max_nat);
  check "B6 the readers are total on 300 random strings, positions and limits"
    (let ok = ref true in
     for _ = 1 to 300 do
       let s = rand_bytes (rand 30) in
       let pos = rand 40 - 5 in
       let lim = rand 40 - 5 in
       (try
          ignore (E4_be.read_frame s pos lim);
          ignore (E4_be.read_be64 s pos);
          ignore (E4_be.nat_of_digits s);
          ignore (E4_be.exact_frame s)
        with _ -> ok := false)
     done;
     !ok);
  (* the goldens *)
  let p42 = unhex golden_p42_hex in
  let pacq = unhex golden_pacquire_hex in
  check "B1 golden p42.bin (66 bytes, embedded): outer frame reads and re-frames"
    (String.length p42 = 66 && check_golden "p42" p42);
  check "B1 golden pAcquire.bin (168 bytes, embedded): outer frame reads and re-frames"
    (String.length pacq = 168 && check_golden "pAcquire" pacq);
  check "B1 both goldens are ctor frames (tag 10, Canonical.lean's constructor tag)"
    (match (E4_be.exact_frame p42, E4_be.exact_frame pacq) with
     | Some (10, _), Some (10, _) -> true
     | _ -> false);
  (match goldens_dir () with
   | None ->
     note "ocaml/eff/goldens not found from %s — the sweep over all *.bin was not run"
       (Sys.getcwd ())
   | Some dir ->
     let files =
       List.filter (fun f -> Filename.check_suffix f ".bin") (Array.to_list (Sys.readdir dir))
     in
     let files = List.sort compare files in
     let bad = ref [] in
     List.iter
       (fun f ->
         let bytes = read_file (Filename.concat dir f) in
         if not (check_golden f bytes) then bad := f :: !bad)
       files;
     check
       (Printf.sprintf "B1 every golden in %s (%d *.bin): outer frame reads and re-frames"
          dir (List.length files))
       (!bad = [] && files <> []))

(* ============================================================ E4_sha256 *)

(* The value frames of src/Effect4/Store/Val.lean, built out of E4_be — the tags are
   Canonical.lean's (2 nat, 3 string, 10 constructor). *)
let v_nat n = E4_be.framed 2 (E4_be.nat_digits n)
let v_str s = E4_be.framed 3 s
let v_ctor i args = E4_be.framed 10 (v_nat i ^ String.concat "" args)

(* sampleEntry = .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1947]
   (src/Effect4/Store/Val.lean:1150-1151). *)
let sample_entry_bytes = v_ctor 0 [ v_str "Effect"; v_str "gen"; v_ctor 0 []; v_nat 1947 ]

let nist_56 = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

let nist_112 =
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

let test_sha256 () =
  print_endline "-- E4_sha256: FIPS 180-4, and the #guards of src/Effect4/Store/Digest.lean";
  check "S1 sha256 \"\" = e3b0c442…b855"
    (E4_sha256.hex "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
  check "S1 sha256 \"abc\" = ba7816bf…f20015ad"
    (E4_sha256.hex "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  check "S1 sha256 (56-byte NIST message) = 248d6a61…c7f89"
    (E4_sha256.hex nist_56 = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
  check "S1 sha256 (112-byte NIST message) = cf5b16a7…ee9d1"
    (E4_sha256.hex nist_112 = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1");
  check "S1 sha256 (one million 'a', streamed in 1000-byte chunks) = cdc76e5c…12cd0"
    (let c = E4_sha256.create () in
     let chunk = String.make 1000 'a' in
     for _ = 1 to 1000 do
       E4_sha256.update_string c chunk
     done;
     E4_hex.of_bytes (E4_sha256.finish c)
     = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
  check "S2 Digest.lean:303  sha256 [0xb4,0x19,0x0e] = dff2e730…975c2"
    (E4_sha256.hex "\xb4\x19\x0e"
     = "dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2");
  (* the third vector: the input is built here and pinned by Val.lean's own #guards *)
  check "S2 Val.lean:1153  (Val.encode sampleEntry).length = 74"
    (String.length sample_entry_bytes = 74);
  check "S2 Val.lean:1154  take 10 = [0x0a,0,0,0,0,0,0,0,0x41,0x02]"
    (String.sub sample_entry_bytes 0 10 = "\x0a\000\000\000\000\000\000\000\x41\x02");
  check "S2 Val.lean:1155  drop 63 = [0x02,0,0,0,0,0,0,0,0x02,0x07,0x9b]"
    (String.sub sample_entry_bytes 63 11 = "\x02\000\000\000\000\000\000\000\x02\x07\x9b");
  check "S2 Digest.lean:315  sha256 (Val.encode sampleEntry) = 8fab1618…0661fa"
    (E4_sha256.hex sample_entry_bytes
     = "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa");
  (* S3: streaming = one-shot *)
  let s3_ok = ref true in
  let msg = nist_112 ^ rand_bytes 137 in
  for i = 0 to String.length msg do
    let c = E4_sha256.create () in
    E4_sha256.update c msg 0 i;
    E4_sha256.update c msg i (String.length msg - i);
    if E4_sha256.finish c <> E4_sha256.digest msg then s3_ok := false
  done;
  check
    (Printf.sprintf "S3 every two-way split of a %d-byte message equals the one-shot digest"
       (String.length msg))
    !s3_ok;
  let s3b_ok = ref true in
  for _ = 1 to 200 do
    let m = rand_bytes (rand 400) in
    let c = E4_sha256.create () in
    let i = ref 0 in
    while !i < String.length m do
      let take = min (1 + rand 70) (String.length m - !i) in
      E4_sha256.update c m !i take;
      i := !i + take
    done;
    if E4_sha256.finish c <> E4_sha256.digest m then s3b_ok := false
  done;
  check "S3 200 random multi-chunk feeds equal the one-shot digest" !s3b_ok;
  check "S4 digest is 32 bytes, hex is 64 lowercase characters"
    (String.length (E4_sha256.digest nist_56) = 32
     && String.length (E4_sha256.hex nist_56) = 64
     && E4_sha256.digest_length = 32 && E4_sha256.block_length = 64
     && E4_sha256.hex "x" = String.lowercase_ascii (E4_sha256.hex "x"));
  check "S4 digest_sub is digest of the window"
    (E4_sha256.digest_sub ("--" ^ nist_56 ^ "--") 2 (String.length nist_56)
     = E4_sha256.digest nist_56);
  check "D1 a finished context refuses a second finish and any update"
    (let c = E4_sha256.create () in
     ignore (E4_sha256.finish c);
     let a = try ignore (E4_sha256.finish c); false with Invalid_argument _ -> true in
     let b = try E4_sha256.update_string c "x"; false with Invalid_argument _ -> true in
     a && b);
  check "S4 update refuses a window out of range"
    (let c = E4_sha256.create () in
     try E4_sha256.update c "abc" 1 5; false with Invalid_argument _ -> true)

let bench_sha256 () =
  print_endline "-- E4_sha256: throughput";
  let mib = 1024 * 1024 in
  let n = 64 * mib in
  let buf = Bytes.create n in
  for i = 0 to n - 1 do
    Bytes.unsafe_set buf i (Char.unsafe_chr (i land 0xff))
  done;
  let s = Bytes.unsafe_to_string buf in
  let t0 = Sys.time () in
  let d = E4_sha256.digest s in
  let t1 = Sys.time () in
  let secs = t1 -. t0 in
  let mbps = float_of_int n /. 1_000_000.0 /. secs in
  note "sha256 of %d MiB: %.3f s CPU = %.1f MB/s (digest %s…)" (n / mib) secs mbps
    (String.sub (E4_hex.of_bytes d) 0 16);
  check "S6 the 64 MiB digest is 32 bytes and the run completed" (String.length d = 32)

let () =
  test_nat ();
  test_hex ();
  test_be ();
  test_sha256 ();
  bench_sha256 ();
  Printf.printf "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
