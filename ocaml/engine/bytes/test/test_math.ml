(* test_math.ml — the checks of the engine's math modules (lane M, 2026-09-08).

   What it checks, and against what:
     S*  E4_sha256: the FIPS 180-4 vectors ("", "abc", the 56- and 112-byte messages, one
         million 'a'), the two byte-vector #guards of sha256 (src/Effect4/Store/Carrier/Digest.lean),
         the third `sha256` guard over `Val.encode sampleEntry` — whose input is BUILT here
         out of Eff_frame frames from sampleEntry (src/Effect4/Store/Carrier/Val.lean) and checked against that
         file's `sampleEntry` encoding guards — the streaming law, and the throughput
         of a 64 MiB buffer.
     H*  E4_hex: the #guards of Digest.ofHex? (src/Effect4/Store/Carrier/Digest.lean) and the two round-trip laws as
         properties over pseudo-random input (a fixed LCG, so the run is reproducible).
     B*  Eff_frame's whole-string face (F10, the face the engine and the store frame by,
         which E4_be forwarded until 2026-10-20): be64/framing/nat-digit laws, the refusals
         and their messages, `read_be64` against the standard library's big-endian reader,
         and the golden bytes of ocaml/eff/goldens (two embedded verbatim, plus every *.bin
         in that directory when the test can find it).
   Exit code 0 iff every check passed. *)

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures
;;

let note fmt = Printf.printf ("NOTE  " ^^ fmt ^^ "\n")

(* A fixed linear congruential generator: the run is reproducible. *)
let seed = ref 20260908

let next_rand () =
  seed := ((!seed * 1103515245) + 12345) land 0x3FFFFFFF;
  !seed
;;

let rand n = if n <= 0 then 0 else next_rand () mod n
let rand_bytes n = String.init n (fun _ -> Char.chr (rand 256))

(* ============================================================ E4_hex *)

let test_hex () =
  print_endline
    "-- E4_hex: hexOfBytes (src/Effect4/Store/Carrier/Digest.lean) and its byte and hex \
     guards";
  check "H1 of_bytes [255;10] = \"ff0a\"" (E4_hex.of_bytes "\xff\x0a" = "ff0a");
  check "H1 of_bytes \"\" = \"\"" (E4_hex.of_bytes "" = "");
  check "H2 to_bytes \"ff00\" = Some [255;0]" (E4_hex.to_bytes "ff00" = Some "\xff\x00");
  check
    "H2 to_bytes \"FF0a\" = Some [255;10] (either case)"
    (E4_hex.to_bytes "FF0a" = Some "\xff\x0a");
  check "H5 to_bytes \"g0\" = None" (E4_hex.to_bytes "g0" = None);
  check "H5 to_bytes \"0\" = None (odd length)" (E4_hex.to_bytes "0" = None);
  check "H5 to_bytes \"\" = Some \"\"" (E4_hex.to_bytes "" = Some "");
  check
    "H5 to_bytes refuses a non-digit anywhere"
    (E4_hex.to_bytes "00ff0z" = None
     && E4_hex.to_bytes "z0" = None
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
    match E4_hex.to_bytes mixed with
    | Some d -> if E4_hex.of_bytes d <> String.lowercase_ascii mixed then h4_ok := false
    | None -> h4_ok := false
  done;
  check "H4 of_bytes (to_bytes h) = lowercase h, 400 mixed-case strings" !h4_ok;
  let empty_hex = E4_sha256.hex "" in
  check
    "H2 digest_of_hex of the uppercase e3b0… digest = digest \"\""
    (E4_hex.digest_of_hex (String.uppercase_ascii empty_hex) = Some (E4_sha256.digest ""));
  check
    "H5 digest_of_hex \"e3b0\" = None, \"\" = None"
    (E4_hex.digest_of_hex "e3b0" = None && E4_hex.digest_of_hex "" = None);
  check
    "H1 of_bytes output is lowercase and 2n long"
    (String.length empty_hex = 64
     && String.for_all
          (fun c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))
          empty_hex)
;;

(* ============================================================ Eff_frame's whole-string face *)

(* The two goldens embedded verbatim (ocaml/eff/goldens/{p42,pAcquire}.bin, 2026-09-08). *)
let golden_p42_hex =
  "0a00000000000000390200000000000000000a0000000000000027020000000000000001010a0000000000000014020000000000000001010200000000000000012a"
;;

let golden_pacquire_hex =
  "0a000000000000009f020000000000000001160a000000000000004b020000000000000001060a00000000000000090200000000000000000a0000000000000026020000000000000001010a0000000000000013020000000000000001010200000000000000000a0000000000000038020000000000000001060a000000000000000a02000000000000000101 \
   0a0000000000000012020000000000000000020000000000000000"
;;

let strip_ws s =
  String.concat
    ""
    (String.split_on_char ' ' (String.concat "" (String.split_on_char '\n' s)))
;;

let unhex s =
  match E4_hex.to_bytes (strip_ws s) with
  | Some b -> b
  | None -> failwith "test_math: bad embedded golden"
;;

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s
;;

(* `$E4_GOLDENS`, or `eff/goldens` (or `ocaml/eff/goldens`) in the nearest ancestor of the
   working directory that holds one: dune runs the test from its build directory. *)
let goldens_dir () =
  let is_dir d = d <> "" && Sys.file_exists d && Sys.is_directory d in
  let rec walk dir =
    let here =
      List.find_opt
        is_dir
        [ Filename.concat dir (Filename.concat "eff" "goldens")
        ; Filename.concat dir (Filename.concat "ocaml" (Filename.concat "eff" "goldens"))
        ]
    in
    match here with
    | Some _ -> here
    | None ->
      let up = Filename.dirname dir in
      if up = dir then None else walk up
  in
  match Sys.getenv_opt "E4_GOLDENS" with
  | Some d when is_dir d -> Some d
  | _ -> walk (Sys.getcwd ())
;;

(* A natural's digits, the whole string: the window reader over all of it. A natural is
   Zarith's `Z.t` (M4); the checks compare through `Z.equal`. *)
let digits (s : string) : Z.t option = Eff_frame.nat_of_digits s 0 (String.length s)
let digits_are (s : string) (n : Z.t) : bool = Option.equal Z.equal (digits s) (Some n)

let check_golden name bytes =
  match Eff_frame.exact_frame bytes with
  | None -> false
  | Some (tag, payload) ->
    let reframed = Eff_frame.framed tag payload in
    let ok =
      reframed = bytes
      && String.length payload = String.length bytes - Eff_frame.header_length
      &&
      match Eff_frame.read_frame bytes 0 (String.length bytes) with
      | Some (t, p, e, next) ->
        t = tag
        && p = Eff_frame.header_length
        && e = String.length bytes
        && next = String.length bytes
      | None -> false
    in
    if not ok then Printf.printf "      golden %s: outer frame mismatch\n" name;
    ok
;;

let test_be () =
  print_endline
    "-- Eff_frame: the framing of Canonical.lean / Wire.lean, its whole-string face";
  check
    "B2 be64 0 is eight zero bytes"
    (Eff_frame.be64 0 = "\000\000\000\000\000\000\000\000");
  check
    "B2 be64 1 / 0x39 / 0x0102030405060708"
    (Eff_frame.be64 1 = "\000\000\000\000\000\000\000\001"
     && Eff_frame.be64 0x39 = "\000\000\000\000\000\000\000\x39"
     && Eff_frame.be64 0x0102030405060708 = "\001\002\003\004\005\006\007\008");
  check
    "B2 framed 10 \"\" is nine bytes, tag then a zero length"
    (Eff_frame.framed 10 "" = "\010\000\000\000\000\000\000\000\000");
  check
    "B2 framed tag p = tag :: be64 (length p) ++ p"
    (let p = "hello" in
     Eff_frame.framed 3 p = String.make 1 '\003' ^ Eff_frame.be64 5 ^ p);
  check
    "B2 frame_length n = 9 + n"
    (Eff_frame.frame_length 0 = 9 && Eff_frame.frame_length 65 = 74);
  (* be64 round trip *)
  let be_ok = ref true in
  for _ = 1 to 2000 do
    let n = (next_rand () lsl 31) lor next_rand () in
    let n = n land max_int in
    if Eff_frame.read_be64 (Eff_frame.be64 n) 0 <> Some n then be_ok := false
  done;
  check "B2 read_be64 (be64 n) = Some n, 2000 random n in 0..max_int" !be_ok;
  check
    "B5 read_be64 refuses a top byte >= 0x40 (a length at or above 2^62)"
    (Eff_frame.read_be64 "\x40\000\000\000\000\000\000\000" 0 = None
     && Eff_frame.read_be64 "\xff\xff\xff\xff\xff\xff\xff\xff" 0 = None
     && Eff_frame.read_be64 "\x3f\xff\xff\xff\xff\xff\xff\xff" 0 = Some max_int);
  check
    "B4 read_be64 refuses a truncated window and a negative position"
    (Eff_frame.read_be64 "\000\000\000\000\000\000\000" 0 = None
     && Eff_frame.read_be64 (Eff_frame.be64 1) 1 = None
     && Eff_frame.read_be64 (Eff_frame.be64 1) (-1) = None);
  check
    "B6 read_be64 refuses extreme positions without overflowing its bounds check"
    (List.for_all
       (fun pos -> Eff_frame.read_be64 (Eff_frame.be64 1) pos = None)
       [ min_int; -1; max_int - 8; max_int - 1; max_int ]);
  check
    "B4 read_be64 accepts an exact nonzero window"
    (Eff_frame.read_be64 ("xx" ^ Eff_frame.be64 42) 2 = Some 42);
  check
    "B4 be64 raises Invalid_argument on a negative int"
    (try
       ignore (Eff_frame.be64 (-1));
       false
     with
     | Invalid_argument _ -> true
     | _ -> false);
  (* frames *)
  check
    "B4 read_frame refuses a header shorter than 9 bytes"
    (Eff_frame.read_frame "\010\000\000\000\000" 0 5 = None
     && Eff_frame.read_frame "" 0 0 = None);
  check
    "B6 read_frame refuses invalid and extreme windows without overflowing"
    (let s = Eff_frame.framed 9 "" in
     let positions = [ min_int; -1; 0; 1; 8; 9; 10; max_int - 8; max_int - 1; max_int ] in
     let limits = [ min_int; -1; 0; 1; 8; 9; 10; max_int ] in
     List.for_all
       (fun pos ->
          List.for_all
            (fun limit ->
               let expected = if pos = 0 && limit = 9 then Some (9, 9, 9, 9) else None in
               Eff_frame.read_frame s pos limit = expected)
            limits)
       positions);
  check
    "B4 read_frame accepts an exact embedded window and leaves trailing bytes"
    (let s = "xx" ^ Eff_frame.framed 3 "abc" ^ "tail" in
     Eff_frame.read_frame s 2 14 = Some (3, 11, 14, 14)
     && Eff_frame.read_frame s 2 (String.length s) = Some (3, 11, 14, 14)
     && Eff_frame.read_frame s 2 13 = None);
  check
    "B4 read_frame refuses a length that runs past the limit"
    (let f = Eff_frame.framed 4 "abcd" in
     Eff_frame.read_frame f 0 (String.length f - 1) = None);
  check
    "B4 exact_frame refuses trailing bytes"
    (Eff_frame.exact_frame (Eff_frame.framed 9 "" ^ "\000") = None);
  check
    "B4 exact_frame (framed t p) = Some (t, p)"
    (Eff_frame.exact_frame (Eff_frame.framed 12 "\001\007") = Some (12, "\001\007"));
  let frame_ok = ref true in
  for _ = 1 to 1000 do
    let tag = rand 256 in
    let p = rand_bytes (rand 60) in
    let f = Eff_frame.framed tag p in
    if Eff_frame.exact_frame f <> Some (tag, p) then frame_ok := false;
    if String.length f <> 9 + String.length p then frame_ok := false
  done;
  check "B2 exact_frame (framed tag p) = Some (tag, p), 1000 random frames" !frame_ok;
  (* nat digits *)
  check
    "B3 nat_digits 0 = \"\", 1 = [1], 255 = [255], 256 = [1;0], 1947 = [0x07;0x9b]"
    (Eff_frame.nat_digits (Z.of_int 0) = ""
     && Eff_frame.nat_digits (Z.of_int 1) = "\001"
     && Eff_frame.nat_digits (Z.of_int 255) = "\xff"
     && Eff_frame.nat_digits (Z.of_int 256) = "\001\000"
     && Eff_frame.nat_digits (Z.of_int 1947) = "\x07\x9b");
  let nat_ok = ref true in
  for i = 1 to 2000 do
    let small = Z.of_int ((next_rand () lsl 31) lor next_rand () land max_int) in
    (* every fourth natural is past max_int: the kernel reads every natural exactly (M4) *)
    let n =
      if i mod 4 = 0 then Z.add (Z.shift_left small (2 + (i mod 80))) Z.one else small
    in
    if not (digits_are (Eff_frame.nat_digits n) n) then nat_ok := false;
    let d = Eff_frame.nat_digits n in
    if String.length d > 0 && String.unsafe_get d 0 = '\000' then nat_ok := false
  done;
  check
    "B3 nat_of_digits (nat_digits n) = Some n and no leading zero, 2000 random n, 500 \
     past max_int"
    !nat_ok;
  check
    "B4 nat_of_digits refuses a leading zero digit"
    (digits "\000\017" = None && digits "\000" = None);
  check
    "B5 nat_of_digits reads nine digits and eight with a top byte >= 0x40 exactly (M4)"
    (digits_are (String.make 9 '\001') (Z.of_bits (String.make 9 '\001'))
     && digits_are ("\x40" ^ String.make 7 '\000') (Z.shift_left Z.one 62)
     && digits_are ("\x3f" ^ String.make 7 '\xff') (Z.of_int max_int));
  check
    "B6 the readers are total on 300 random strings, positions and limits"
    (let ok = ref true in
     for _ = 1 to 300 do
       let s = rand_bytes (rand 30) in
       let pos = rand 40 - 5 in
       let lim = rand 40 - 5 in
       try
         ignore (Eff_frame.read_frame s pos lim);
         ignore (Eff_frame.read_be64 s pos);
         ignore (digits s);
         ignore (Eff_frame.exact_frame s)
       with
       | _ -> ok := false
     done;
     !ok);
  (* the goldens *)
  let p42 = unhex golden_p42_hex in
  let pacq = unhex golden_pacquire_hex in
  check
    "B1 golden p42.bin (66 bytes, embedded): outer frame reads and re-frames"
    (String.length p42 = 66 && check_golden "p42" p42);
  check
    "B1 golden pAcquire.bin (168 bytes, embedded): outer frame reads and re-frames"
    (String.length pacq = 168 && check_golden "pAcquire" pacq);
  check
    "B1 both goldens are ctor frames (tag 10, Canonical.lean's constructor tag)"
    (match Eff_frame.exact_frame p42, Eff_frame.exact_frame pacq with
     | Some (10, _), Some (10, _) -> true
     | _ -> false);
  match goldens_dir () with
  | None ->
    note
      "ocaml/eff/goldens not found from %s — the sweep over all *.bin was not run"
      (Sys.getcwd ())
  | Some dir ->
    let files =
      List.filter
        (fun f -> Filename.check_suffix f ".bin")
        (Array.to_list (Sys.readdir dir))
    in
    let files = List.sort compare files in
    let bad = ref [] in
    List.iter
      (fun f ->
         let bytes = read_file (Filename.concat dir f) in
         if not (check_golden f bytes) then bad := f :: !bad)
      files;
    check
      (Printf.sprintf
         "B1 every golden in %s (%d *.bin): outer frame reads and re-frames"
         dir
         (List.length files))
      (!bad = [] && files <> [])
;;

(* ============================================================ the kernel's reader and refusals *)

(* An answer, or the message of the Invalid_argument a call raised: two calls compare by `=`. *)
let outcome f =
  try Ok (f ()) with
  | Invalid_argument m -> Error m
;;

(* The standard library's big-endian reader as an independent reference of `read_be64`: a
   value outside 0 .. max_int is the refused top byte. *)
let native_read_be64 (s : string) (pos : int) : int option =
  if pos < 0 || pos > String.length s - 8
  then None
  else (
    let n = String.get_int64_be s pos in
    if Int64.compare n 0L < 0 || Int64.compare n (Int64.of_int max_int) > 0
    then None
    else Some (Int64.to_int n))
;;

let test_be_reference () =
  print_endline "-- Eff_frame: read_be64 against the standard library, and the refusals";
  check
    "B7 nat_digits, be64 and framed refuse with the kernel's own messages, before any \
     byte"
    (outcome (fun () -> Eff_frame.nat_digits (Z.of_int (-1)))
     = Error "Eff_frame.nat_digits: negative"
     && outcome (fun () -> Eff_frame.be64 (-1)) = Error "Eff_frame.be64: negative"
     && outcome (fun () -> Eff_frame.framed (-1) "x")
        = Error "Eff_frame.framed: tag is not a byte"
     && outcome (fun () -> Eff_frame.framed 256 "x")
        = Error "Eff_frame.framed: tag is not a byte");
  let strings =
    List.init 256 (fun k -> rand_bytes (k mod 32))
    @ List.init 100 (fun k ->
      rand_bytes (k mod 3)
      ^ Eff_frame.framed (rand 256) (rand_bytes (k mod 20))
      ^ rand_bytes (k mod 4))
    @ [ "\x40" ^ String.make 16 '\000'
      ; String.make 17 '\xff'
      ; "\x3f" ^ String.make 16 '\xff'
      ]
  in
  let native_ok = ref true in
  List.iter
    (fun s ->
       let len = String.length s in
       List.iter
         (fun pos ->
            if Eff_frame.read_be64 s pos <> native_read_be64 s pos then native_ok := false)
         [ min_int
         ; -1
         ; 0
         ; 1
         ; 2
         ; 7
         ; 8
         ; len - 8
         ; len - 1
         ; len
         ; len + 1
         ; max_int - 8
         ; max_int
         ])
    strings;
  check
    "B5 read_be64 = the standard library's big-endian reader with the 0 .. max_int \
     bound, 359 strings x 13 positions (extremes included)"
    !native_ok;
  check
    "B5 nat_of_digits past max_int: eight digits below 0x40 and at 0x40, nine, and 70 \
     000 digits each read exactly (M4)"
    (digits_are ("\x3f" ^ String.make 7 '\xff') (Z.of_int max_int)
     && digits_are ("\x40" ^ String.make 7 '\000') (Z.shift_left Z.one 62)
     && digits_are (String.make 9 '\001') (Z.of_bits (String.make 9 '\001'))
     &&
     match digits (String.make 70000 '\001') with
     | Some n -> Z.numbits n = (69999 * 8) + 1
     | None -> false);
  (* the red control: a leading zero is still refused, at any length *)
  check
    "B5 (red control) a leading zero digit is refused past max_int too"
    (Option.is_none (digits ("\000" ^ String.make 9 '\001')))
;;

(* ============================================================ E4_sha256 *)

(* The value frames of src/Effect4/Store/Carrier/Val.lean, built out of Eff_frame — the tags are
   Canonical.lean's (2 nat, 3 string, 10 constructor). *)
let v_nat n = Eff_frame.framed 2 (Eff_frame.nat_digits (Z.of_int n))
let v_str s = Eff_frame.framed 3 s
let v_ctor i args = Eff_frame.framed 10 (v_nat i ^ String.concat "" args)

(* sampleEntry = .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1947]
   (sampleEntry (src/Effect4/Store/Carrier/Val.lean)). *)
let sample_entry_bytes = v_ctor 0 [ v_str "Effect"; v_str "gen"; v_ctor 0 []; v_nat 1947 ]
let nist_56 = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

let nist_112 =
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
;;

let test_sha256 () =
  print_endline
    "-- E4_sha256: FIPS 180-4, and the #guards of src/Effect4/Store/Carrier/Digest.lean";
  check
    "S1 sha256 \"\" = e3b0c442…b855"
    (E4_sha256.hex "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
  check
    "S1 sha256 \"abc\" = ba7816bf…f20015ad"
    (E4_sha256.hex "abc"
     = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  check
    "S1 sha256 (56-byte NIST message) = 248d6a61…c7f89"
    (E4_sha256.hex nist_56
     = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
  check
    "S1 sha256 (112-byte NIST message) = cf5b16a7…ee9d1"
    (E4_sha256.hex nist_112
     = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1");
  check
    "S1 sha256 (one million 'a', streamed in 1000-byte chunks) = cdc76e5c…12cd0"
    (let c = E4_sha256.create () in
     let chunk = String.make 1000 'a' in
     for _ = 1 to 1000 do
       E4_sha256.update_string c chunk
     done;
     E4_hex.of_bytes (E4_sha256.finish c)
     = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
  check
    "S2 sha256 (src/Effect4/Store/Carrier/Digest.lean)  sha256 [0xb4,0x19,0x0e] = \
     dff2e730…975c2"
    (E4_sha256.hex "\xb4\x19\x0e"
     = "dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2");
  (* the third vector: the input is built here and pinned by Val.lean's own #guards *)
  check
    "S2 sampleEntry (src/Effect4/Store/Carrier/Val.lean)  (Val.encode \
     sampleEntry).length = 74"
    (String.length sample_entry_bytes = 74);
  check
    "S2 sampleEntry (src/Effect4/Store/Carrier/Val.lean)  take 10 = \
     [0x0a,0,0,0,0,0,0,0,0x41,0x02]"
    (String.sub sample_entry_bytes 0 10 = "\x0a\000\000\000\000\000\000\000\x41\x02");
  check
    "S2 sampleEntry (src/Effect4/Store/Carrier/Val.lean)  drop 63 = \
     [0x02,0,0,0,0,0,0,0,0x02,0x07,0x9b]"
    (String.sub sample_entry_bytes 63 11 = "\x02\000\000\000\000\000\000\000\x02\x07\x9b");
  check
    "S2 sha256 (src/Effect4/Store/Carrier/Digest.lean)  sha256 (Val.encode sampleEntry) \
     = 8fab1618…0661fa"
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
    (Printf.sprintf
       "S3 every two-way split of a %d-byte message equals the one-shot digest"
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
  check
    "S4 digest is 32 bytes, hex is 64 lowercase characters"
    (String.length (E4_sha256.digest nist_56) = 32
     && String.length (E4_sha256.hex nist_56) = 64
     && E4_sha256.digest_length = 32
     && E4_sha256.block_length = 64
     && E4_sha256.hex "x" = String.lowercase_ascii (E4_sha256.hex "x"));
  check
    "S4 digest_sub is digest of the window"
    (E4_sha256.digest_sub ("--" ^ nist_56 ^ "--") 2 (String.length nist_56)
     = E4_sha256.digest nist_56);
  check
    "D1 a finished context refuses a second finish and any update"
    (let c = E4_sha256.create () in
     ignore (E4_sha256.finish c);
     let a =
       try
         ignore (E4_sha256.finish c);
         false
       with
       | Invalid_argument _ -> true
     in
     let b =
       try
         E4_sha256.update_string c "x";
         false
       with
       | Invalid_argument _ -> true
     in
     a && b);
  check
    "S4 update refuses a window out of range"
    (let c = E4_sha256.create () in
     try
       E4_sha256.update c "abc" 1 5;
       false
     with
     | Invalid_argument _ -> true)
;;

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
  note
    "sha256 of %d MiB: %.3f s CPU = %.1f MB/s (digest %s…)"
    (n / mib)
    secs
    mbps
    (String.sub (E4_hex.of_bytes d) 0 16);
  check "S6 the 64 MiB digest is 32 bytes and the run completed" (String.length d = 32)
;;

let () =
  test_hex ();
  test_be ();
  test_be_reference ();
  test_sha256 ();
  bench_sha256 ();
  Printf.printf
    "== %s: %d failure(s) ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
;;
