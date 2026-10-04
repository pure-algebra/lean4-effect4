(* Eff_frame boundary checks, using explicit UTF-8 byte sequences and frame bytes.
   U: legal scalar boundaries, NUL, BOM and noncharacters remain accepted; malformed
      sequences are refused by both the encoder and decoder.
   P: payload callbacks run once, before the frame is appended; exceptions escape
      without appending a partial frame, and nested payloads retain their bytes.
   W: invalid windows, including extreme ints, return None; exact and embedded
      frames still stop at their declared end. These are finite host checks. *)

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let frame tag payload = Eff_frame.to_string (fun b s -> Eff_frame.emit_frame b tag s) payload

let test_utf8 () =
  let valid = [
    ""; "\000"; "\127"; "\xc2\x80"; "\xdf\xbf"; "\xe0\xa0\x80";
    "\xed\x9f\xbf"; "\xee\x80\x80"; "\xef\xbb\xbf"; "\xef\xb7\x90";
    "\xef\xbf\xbe"; "\xef\xbf\xbf"; "\xf0\x90\x80\x80";
    "\xf4\x8f\xbf\xbf"; "a\000\xef\xbb\xbf\xf0\x9f\x98\x80z"
  ] in
  List.iteri (fun i s ->
    check (Printf.sprintf "U valid UTF-8 boundary %d round-trips" i)
      (Eff_frame.utf8_valid s
       && Eff_frame.exact Eff_frame.decode_string
            (Eff_frame.to_string Eff_frame.emit_string s) = Some s)) valid;
  let invalid = [
    "\x80"; "\xbf"; "\xc0\x80"; "\xc1\xbf"; "\xc2"; "\xc2A";
    "\xe0\x9f\xbf"; "\xe0\xa0"; "\xe1\x80A"; "\xed\xa0\x80";
    "\xed\xbf\xbf"; "\xef\xbf"; "\xf0\x8f\xbf\xbf";
    "\xf0\x90\x80"; "\xf1\x80\x80A"; "\xf4\x90\x80\x80";
    "\xf5\x80\x80\x80"; "\xfe"; "\xff"; "valid\x80"
  ] in
  List.iteri (fun i s ->
    let b = Buffer.create 16 in
    Buffer.add_string b "prefix";
    let refused =
      try Eff_frame.emit_string b s; false
      with Invalid_argument message -> message = "Eff_frame.emit_string: not valid UTF-8"
    in
    check (Printf.sprintf "U malformed UTF-8 boundary %d is refused" i)
      (not (Eff_frame.utf8_valid s) && refused && Buffer.contents b = "prefix"
       && Eff_frame.exact Eff_frame.decode_string (frame 3 s) = None)) invalid

exception Payload_failure of int

let test_payload () =
  let b = Buffer.create 1 in
  Buffer.add_string b "prefix";
  let calls = ref 0 in
  Eff_frame.with_payload b 3 (fun p ->
    incr calls;
    check "P callback sees destination before frame" (Buffer.contents b = "prefix");
    Buffer.add_string b ":";
    Buffer.add_string p "abc");
  check "P callback runs once; its destination writes precede the frame"
    (!calls = 1 && Buffer.contents b = "prefix:" ^ frame 3 "abc");
  let before = Buffer.contents b in
  let escaped =
    try
      Eff_frame.with_payload b 3 (fun p ->
        incr calls; Buffer.add_string p "discarded"; raise (Payload_failure 17));
      false
    with Payload_failure n -> n = 17
  in
  check "P callback exception escapes without a partial frame"
    (escaped && !calls = 2 && Buffer.contents b = before);
  let escaped =
    try Eff_frame.with_payload b 256 (fun _ -> incr calls); false
    with Invalid_argument _ -> true
  in
  check "P invalid tag is checked after the callback without appending bytes"
    (escaped && !calls = 3 && Buffer.contents b = before);
  let retained = ref None in
  Eff_frame.with_payload b 3 (fun p -> retained := Some p; Buffer.add_string p "copy");
  Option.iter (fun p -> Buffer.clear p; Buffer.add_string p "changed") !retained;
  check "P payload bytes are copied before later callback-buffer mutation"
    (Buffer.contents b = before ^ frame 3 "copy");
  let nested = Eff_frame.to_string
      (fun out pairs -> Eff_frame.emit_list out
        (fun p pair -> Eff_frame.emit_pair p Eff_frame.emit_nat Eff_frame.emit_string pair) pairs)
      [0, ""; 256, "\000"] in
  let expected = frame 4
      (frame 5 (frame 2 "" ^ frame 3 "")
       ^ frame 5 (frame 2 "\001\000" ^ frame 3 "\000")) in
  check "P nested list/pair payloads retain exact frame bytes" (nested = expected);
  check "P empty payload retains the nine-byte frame"
    (Eff_frame.to_string (fun b () -> Eff_frame.with_payload b 9 (fun _ -> ())) ()
     = "\009\000\000\000\000\000\000\000\000");
  let large = String.make 65536 '\255' in
  check "P payload growth retains every byte"
    (Eff_frame.to_string
       (fun b p -> Eff_frame.with_payload b 8 (fun inner -> Buffer.add_string inner p)) large
     = frame 8 large)

let test_windows () =
  let s = "xx" ^ frame 3 "abc" ^ "tail" in
  check "W embedded frame accepts its exact window"
    (Eff_frame.read_frame s 2 14 = Some (3, 11, 14, 14));
  check "W trailing bytes remain outside the frame"
    (Eff_frame.read_frame s 2 (String.length s) = Some (3, 11, 14, 14));
  check "W one missing payload byte is refused" (Eff_frame.read_frame s 2 13 = None);
  check "W exact empty payload is accepted"
    (Eff_frame.read_frame (frame 9 "") 0 9 = Some (9, 9, 9, 9));
  let positions = [min_int; -1; 0; 1; 8; 9; 10; max_int - 8; max_int - 1; max_int] in
  let limits = [min_int; -1; 0; 1; 8; 9; 10; max_int] in
  let unit_frame = frame 9 "" in
  List.iter (fun pos -> List.iter (fun limit ->
    let expected = if pos = 0 && limit = 9 then Some (9, 9, 9, 9) else None in
    check (Printf.sprintf "W unit window pos=%d limit=%d" pos limit)
      (Eff_frame.read_frame unit_frame pos limit = expected)) limits) positions;
  for length = 0 to 8 do
    check (Printf.sprintf "W short header length=%d" length)
      (Eff_frame.read_frame (String.make length '\000') 0 length = None)
  done

let () =
  test_utf8 ();
  test_payload ();
  test_windows ();
  if !failures <> 0 then exit 1
