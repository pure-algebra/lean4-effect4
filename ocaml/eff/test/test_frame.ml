(* Eff_frame boundary checks, using explicit UTF-8 byte sequences and frame bytes.
   U: legal scalar boundaries, NUL, BOM and noncharacters remain accepted; malformed
      sequences are refused by both the encoder and decoder.
   P: a payload callback runs once and writes the frame's payload in place; an exception
      escapes with every open frame rolled back, an invalid tag is refused before the callback,
      and a writer kept past its encoding cannot change the bytes published (Eff_frame's F9).
   O: an encoding over its limit is refused as a value and nothing is published, even when a
      callback swallows the refusal; at its exact size it is published whole (F8).
   W: invalid windows, including extreme ints, return None; exact and embedded
      frames still stop at their declared end.
   B: the one-write writers (Eff_frame's F6) give the per-byte rule's bytes: `emit_be64` on
      3 956 ints, both ends, the negatives and every byte boundary, and `emit_nat` on the
      naturals among them and on naturals past max_int (M4), against digits computed by
      division; and a value's byte string is written whole, a code outside a byte refused.
      These are finite host checks. *)

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures
;;

let frame tag payload =
  Eff_frame.to_string (fun b s -> Eff_frame.emit_frame b tag s) payload
;;

let test_utf8 () =
  let valid =
    [ ""
    ; "\000"
    ; "\127"
    ; "\xc2\x80"
    ; "\xdf\xbf"
    ; "\xe0\xa0\x80"
    ; "\xed\x9f\xbf"
    ; "\xee\x80\x80"
    ; "\xef\xbb\xbf"
    ; "\xef\xb7\x90"
    ; "\xef\xbf\xbe"
    ; "\xef\xbf\xbf"
    ; "\xf0\x90\x80\x80"
    ; "\xf4\x8f\xbf\xbf"
    ; "a\000\xef\xbb\xbf\xf0\x9f\x98\x80z"
    ]
  in
  List.iteri
    (fun i s ->
       check
         (Printf.sprintf "U valid UTF-8 boundary %d round-trips" i)
         (Eff_frame.utf8_valid s
          && Eff_frame.exact
               Eff_frame.decode_string
               (Eff_frame.to_string Eff_frame.emit_string s)
             = Some s))
    valid;
  let invalid =
    [ "\x80"
    ; "\xbf"
    ; "\xc0\x80"
    ; "\xc1\xbf"
    ; "\xc2"
    ; "\xc2A"
    ; "\xe0\x9f\xbf"
    ; "\xe0\xa0"
    ; "\xe1\x80A"
    ; "\xed\xa0\x80"
    ; "\xed\xbf\xbf"
    ; "\xef\xbf"
    ; "\xf0\x8f\xbf\xbf"
    ; "\xf0\x90\x80"
    ; "\xf1\x80\x80A"
    ; "\xf4\x90\x80\x80"
    ; "\xf5\x80\x80\x80"
    ; "\xfe"
    ; "\xff"
    ; "valid\x80"
    ]
  in
  List.iteri
    (fun i s ->
       let refused = ref false in
       let out =
         Eff_frame.to_string
           (fun w () ->
              Eff_frame.emit_frame w 3 "prefix";
              try Eff_frame.emit_string w s with
              | Invalid_argument message ->
                refused := message = "Eff_frame.emit_string: not valid UTF-8")
           ()
       in
       check
         (Printf.sprintf "U malformed UTF-8 boundary %d is refused" i)
         ((not (Eff_frame.utf8_valid s))
          && !refused
          && out = frame 3 "prefix"
          && Eff_frame.exact Eff_frame.decode_string (frame 3 s) = None))
    invalid
;;

exception Payload_failure of int

let test_payload () =
  let calls = ref 0 in
  let prefixed f =
    Eff_frame.to_string
      (fun w () ->
         Eff_frame.emit_frame w 3 "prefix";
         f w)
      ()
  in
  let out =
    prefixed (fun w ->
      Eff_frame.with_payload w 3 (fun w ->
        incr calls;
        Eff_frame.emit_frame w 3 "abc"))
  in
  check
    "P callback runs once; its writes are the frame's payload"
    (!calls = 1 && out = frame 3 "prefix" ^ frame 3 (frame 3 "abc"));
  let escaped = ref false in
  let out =
    prefixed (fun w ->
      try
        Eff_frame.with_payload w 3 (fun w ->
          incr calls;
          Eff_frame.emit_frame w 3 "discarded";
          raise (Payload_failure 17))
      with
      | Payload_failure n -> escaped := n = 17)
  in
  check
    "P callback exception escapes without a partial frame"
    (!escaped && !calls = 2 && out = frame 3 "prefix");
  let escaped = ref false in
  let out =
    prefixed (fun w ->
      try
        Eff_frame.with_payload w 4 (fun w ->
          Eff_frame.emit_nat w (Z.of_int 1);
          Eff_frame.with_payload w 5 (fun w ->
            Eff_frame.emit_nat w (Z.of_int 2);
            raise (Payload_failure 3)))
      with
      | Payload_failure n -> escaped := n = 3)
  in
  check
    "P an exception two frames deep rolls back every open frame"
    (!escaped && out = frame 3 "prefix");
  let escaped = ref false in
  let out =
    prefixed (fun w ->
      try Eff_frame.with_payload w 256 (fun _ -> incr calls) with
      | Invalid_argument _ -> escaped := true)
  in
  check
    "P an invalid tag is refused before the callback, with no bytes appended"
    (!escaped && !calls = 2 && out = frame 3 "prefix");
  let kept = ref None in
  let out =
    Eff_frame.to_string
      (fun w () ->
         kept := Some w;
         Eff_frame.emit_frame w 3 "copy")
      ()
  in
  Option.iter (fun w -> Eff_frame.emit_frame w 3 "changed") !kept;
  check
    "P a writer kept past its encoding cannot change the bytes published"
    (out = frame 3 "copy");
  let nested =
    Eff_frame.to_string
      (fun out pairs ->
         Eff_frame.emit_list
           out
           (fun p pair ->
              Eff_frame.emit_pair p Eff_frame.emit_nat Eff_frame.emit_string pair)
           pairs)
      [ Z.zero, ""; Z.of_int 256, "\000" ]
  in
  let expected =
    frame
      4
      (frame 5 (frame 2 "" ^ frame 3 "") ^ frame 5 (frame 2 "\001\000" ^ frame 3 "\000"))
  in
  check "P nested list/pair payloads retain exact frame bytes" (nested = expected);
  check
    "P empty payload retains the nine-byte frame"
    (Eff_frame.to_string (fun b () -> Eff_frame.with_payload b 9 (fun _ -> ())) ()
     = "\009\000\000\000\000\000\000\000\000");
  let large = String.make 65536 '\255' in
  check
    "P payload growth retains every byte"
    (Eff_frame.to_string
       (fun w p -> Eff_frame.with_payload w 8 (fun w -> Eff_frame.emit_frame w 3 p))
       large
     = frame 8 (frame 3 large))
;;

let test_overflow () =
  let write w xs = Eff_frame.emit_list w Eff_frame.emit_nat xs in
  let value = List.init 40 (fun i -> Z.of_int (i * 1000)) in
  let whole = Eff_frame.to_string write value in
  let size = String.length whole in
  check
    (Printf.sprintf "O at its exact size (%d bytes) the encoding is published whole" size)
    (Eff_frame.encode ~limit:size write value = Ok whole);
  check
    "O one byte short, the encoding is refused as a value and nothing is published"
    (Eff_frame.encode ~limit:(size - 1) write value = Error { Eff_frame.limit = size - 1 });
  let swallowing w xs =
    (try write w xs with
     | _ -> ());
    Eff_frame.emit_unit w ()
  in
  check
    "O a refusal that a callback swallows is still a refusal, so no shorter encoding \
     escapes"
    (Eff_frame.encode ~limit:(size - 1) swallowing value
     = Error { Eff_frame.limit = size - 1 });
  check
    "O red control: with room, the swallowing callback's own bytes are published"
    (Eff_frame.encode ~limit:(size + 9) swallowing value
     = Ok (whole ^ frame Eff_frame.tag_unit ""));
  check
    "O a negative limit is no room at all"
    (Eff_frame.encode ~limit:(-1) write [] = Error { Eff_frame.limit = 0 })
;;

let test_windows () =
  let s = "xx" ^ frame 3 "abc" ^ "tail" in
  check
    "W embedded frame accepts its exact window"
    (Eff_frame.read_frame s 2 14 = Some (3, 11, 14, 14));
  check
    "W trailing bytes remain outside the frame"
    (Eff_frame.read_frame s 2 (String.length s) = Some (3, 11, 14, 14));
  check "W one missing payload byte is refused" (Eff_frame.read_frame s 2 13 = None);
  check
    "W exact empty payload is accepted"
    (Eff_frame.read_frame (frame 9 "") 0 9 = Some (9, 9, 9, 9));
  let positions = [ min_int; -1; 0; 1; 8; 9; 10; max_int - 8; max_int - 1; max_int ] in
  let limits = [ min_int; -1; 0; 1; 8; 9; 10; max_int ] in
  let unit_frame = frame 9 "" in
  List.iter
    (fun pos ->
       List.iter
         (fun limit ->
            let expected = if pos = 0 && limit = 9 then Some (9, 9, 9, 9) else None in
            check
              (Printf.sprintf "W unit window pos=%d limit=%d" pos limit)
              (Eff_frame.read_frame unit_frame pos limit = expected))
         limits)
    positions;
  for length = 0 to 8 do
    check
      (Printf.sprintf "W short header length=%d" length)
      (Eff_frame.read_frame (String.make length '\000') 0 length = None)
  done
;;

(* The writers as they were before F6, one byte at a time: the reference B compares against. *)
let be64_by_bytes (n : int) : string =
  String.init 8 (fun i -> Char.chr ((n lsr (8 * (7 - i))) land 0xff))
;;

(* A natural's base-256 digits by repeated division: the rule, independent of the writer. *)
let rec digits_by_division (n : Z.t) : string =
  if Z.equal n Z.zero
  then ""
  else (
    let q, r = Z.div_rem n (Z.of_int 256) in
    digits_by_division q ^ String.make 1 (Char.chr (Z.to_int r)))
;;

let nat_frame_by_bytes (n : Z.t) : string =
  let digits = digits_by_division n in
  String.make 1 (Char.chr Eff_frame.tag_nat)
  ^ be64_by_bytes (String.length digits)
  ^ digits
;;

let test_writers () =
  let s = ref 0x1234ABCD5678 in
  let next () =
    s := ((!s * 25214903917) + 11) land 0xFFFFFFFFFFFF;
    !s
  in
  let boundaries =
    List.concat_map
      (fun k ->
         let p = 1 lsl (8 * k) in
         [ p - 1; p; p + 1 ])
      [ 1; 2; 3; 4; 5; 6; 7 ]
  in
  let ints =
    [ 0
    ; 1
    ; 2
    ; 127
    ; 128
    ; 255
    ; 256
    ; max_int
    ; max_int - 1
    ; min_int
    ; min_int + 1
    ; -1
    ; -2
    ; -256
    ]
    @ boundaries
    @ List.map (fun n -> -n) boundaries
    @ List.init 3900 (fun i ->
      let r = (next () lsl 15) lxor next () in
      if i mod 3 = 0 then -r else r)
  in
  let be_ok =
    List.for_all
      (fun n -> Eff_frame.to_string Eff_frame.emit_be64 n = be64_by_bytes n)
      ints
  in
  check
    (Printf.sprintf
       "B emit_be64 is the per-byte rule on %d ints, negatives included"
       (List.length ints))
    be_ok;
  let past =
    let big = Z.succ (Z.of_int max_int) in
    [ big; Z.succ big; Z.pow (Z.of_int 2) 63; Z.pred (Z.pow (Z.of_int 2) 64) ]
    @ List.init 50 (fun i ->
      Z.add (Z.shift_left (Z.of_int (next ())) (62 + i)) (Z.of_int (next ())))
  in
  let nats = List.map Z.of_int (List.filter (fun n -> n >= 0) ints) @ past in
  let nat_ok =
    List.for_all
      (fun n -> Eff_frame.to_string Eff_frame.emit_nat n = nat_frame_by_bytes n)
      nats
  in
  check
    (Printf.sprintf
       "B emit_nat is the frame of nat_digits on %d naturals"
       (List.length nats))
    nat_ok;
  check
    "B emit_nat refuses a negative integer, as nat_digits does"
    (try
       ignore (Eff_frame.to_string Eff_frame.emit_nat (Z.of_int (-1)));
       false
     with
     | Invalid_argument m -> m = "Eff_frame.nat_digits: negative");
  let codes = List.init 10000 (fun i -> i * 7 land 0xff) in
  let expected = String.init 10000 (fun i -> Char.chr (i * 7 land 0xff)) in
  check
    "B a value's byte string of 10 000 codes is written whole"
    (Eff_val.to_bytes (Eff_types.Val.Bytes codes) = frame Eff_frame.tag_bytes expected);
  check
    "B a code outside a byte is refused"
    (try
       ignore (Eff_val.to_bytes (Eff_types.Val.Bytes [ 1; 256 ]));
       false
     with
     | Invalid_argument _ -> true)
;;

let () =
  test_utf8 ();
  test_payload ();
  test_overflow ();
  test_windows ();
  test_writers ();
  if !failures <> 0 then exit 1
;;
