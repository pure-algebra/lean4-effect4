(* test_eff — the battery of effect4_eff (hand-written).
   1. Goldens: every goldens/<name>.bin decodes exactly, re-encodes byte for byte and prints
      the JSON of goldens/<name>.json; structural corruptions of the bytes are refused. The
      `.ty` beside each golden and the verdict column of corpus.txt are Lean's own typing
      (`typeOf`, `wellTyped`), printed for the record and compared with nothing here: since
      2026-09-13 the typing has one face, `effTy`, and those files are its expected output,
      held by `make check-gen`.
   2. The wire kernel: nat digits, the bound, UTF-8, refusals.
   Exit status 1 on any failure; the counts are printed last. *)

open Eff_types

let checks = ref 0
let failures = ref 0

let check (name : string) (ok : bool) : unit =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "FAIL: %s\n%!" name
  end

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let strip (s : string) : string =
  let n = ref (String.length s) in
  while !n > 0 && (s.[!n - 1] = '\n' || s.[!n - 1] = '\r') do decr n done;
  String.sub s 0 !n

let goldens = "../goldens/"

let corpus : (string * bool) list =
  read_file (goldens ^ "corpus.txt")
  |> String.split_on_char '\n'
  |> List.filter (fun l -> l <> "")
  |> List.map (fun l ->
         match String.split_on_char '\t' l with
         | [ name; status ] -> (name, status = "well-typed")
         | _ -> failwith ("corpus.txt: bad line " ^ l))

let golden_bin name = read_file (goldens ^ name ^ ".bin")

let ellipsis (n : int) (s : string) : string =
  if String.length s <= n then s else String.sub s 0 (n - 1) ^ "\226\128\166"

(* ---- 1. goldens ---- *)

let () =
  (* no pinned count: every program corpus.txt names has its bytes, and no bytes are unnamed *)
  let bins =
    List.filter (fun f -> Filename.check_suffix f ".bin") (Array.to_list (Sys.readdir goldens))
  in
  check
    (Printf.sprintf "corpus.txt names exactly the %d byte goldens" (List.length bins))
    (corpus <> []
    && List.sort compare (List.map (fun (n, _) -> n ^ ".bin") corpus) = List.sort compare bins);
  Printf.printf "  %-16s %6s %-8s %-10s %-6s %-5s %s\n" "program" "bytes" "decode" "re-encode" "JSON" "Lean" "typeOf";
  List.iter
    (fun (name, typed) ->
      let bin = golden_bin name in
      let json = strip (read_file (goldens ^ name ^ ".json")) in
      let ty = strip (read_file (goldens ^ name ^ ".ty")) in
      match Eff_wire.decode_program_exact bin with
      | None ->
        check (name ^ ": decodes") false;
        Printf.printf "  %-16s %6d %-8s %-10s %-6s %-5s %s\n" name (String.length bin) "REFUSED" "-" "-" "-" "-"
      | Some p ->
        Printf.printf "  %-16s %6d %-8s %-10s %-6s %-5s %s\n" name (String.length bin) "ok"
          (if Eff_wire.encode_program p = bin then "identical" else "DIFFERS")
          (if Eff_json.print_eff p = json then "equal" else "DIFFERS")
          (if typed then "typed" else "ill")
          (ellipsis 44 ty);
        check (name ^ ": re-encodes byte for byte") (Eff_wire.encode_program p = bin);
        check (name ^ ": JSON equals the Lean printer's") (Eff_json.print_eff p = json);
        check (name ^ ": decode reports the whole length as rest")
          (Eff_wire.decode_program bin = Some (p, String.length bin));
        check (name ^ ": a trailing byte is refused") (Eff_wire.decode_program_exact (bin ^ "\000") = None);
        check (name ^ ": a trailing byte is not consumed by decode")
          (Eff_wire.decode_program (bin ^ "\000") = Some (p, String.length bin));
        check (name ^ ": truncation is refused")
          (Eff_wire.decode_program_exact (String.sub bin 0 (String.length bin - 1)) = None);
        let flipped = Bytes.of_string bin in
        Bytes.set flipped 0 '\004';
        check (name ^ ": a wrong tag is refused") (Eff_wire.decode_program_exact (Bytes.to_string flipped) = None);
        let longer = Bytes.of_string bin in
        Bytes.set longer 8 (Char.chr (Char.code (Bytes.get longer 8) + 1));
        check (name ^ ": a length past the end is refused")
          (Eff_wire.decode_program_exact (Bytes.to_string longer) = None))
    corpus

let () =
  let bad_index i = Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b i (fun _ -> ())) () in
  check "Eff index 27 is refused" (Eff_wire.decode_eff_exact (bad_index 27) = None);
  check "Eff index 24 with no payload is refused (provideLayer needs a layer, a flag and a body)"
    (Eff_wire.decode_eff_exact (bad_index 24) = None);
  check "Eff index 99 is refused" (Eff_wire.decode_eff_exact (bad_index 99) = None);
  check "Eff index 17 with no payload is refused (yieldNow needs a nat)"
    (Eff_wire.decode_eff_exact (bad_index 17) = None);
  let yield0 = Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b 17 (fun b -> Eff_frame.emit_nat b 0)) () in
  check "Eff index 17 with a nat is yieldNow 0" (Eff_wire.decode_eff_exact yield0 = Some (Eff_yieldNow 0));
  let extra = Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b 17 (fun b -> Eff_frame.emit_nat b 0; Eff_frame.emit_nat b 0)) () in
  check "an extra argument inside the frame is refused" (Eff_wire.decode_eff_exact extra = None)


(* ---- 4. the wire kernel ---- *)

let () =
  let open Eff_frame in
  check "nat digits: 0 is empty, 255 one byte, 256 two" (nat_digits 0 = "" && nat_digits 255 = "\255" && nat_digits 256 = "\001\000");
  check "nat digits: max_int is 8 bytes" (String.length (nat_digits max_int) = 8);
  let rt n = exact decode_nat (to_string emit_nat n) = Some n in
  check "nat round trip at 0, 1, 255, 256, 65535, 2^32, max_int" (rt 0 && rt 1 && rt 255 && rt 256 && rt 65535 && rt (1 lsl 32) && rt max_int);
  check "a negative int has no encoding" (try ignore (nat_digits (-1)); false with Invalid_argument _ -> true);
  let frame tag payload = to_string (fun b () -> emit_frame b tag payload) () in
  check "a nat with a leading zero digit is refused" (exact decode_nat (frame tag_nat "\000\001") = None);
  check "a nat of nine digits is refused" (exact decode_nat (frame tag_nat "\001\000\000\000\000\000\000\000\000") = None);
  check "a nat of eight digits above max_int is refused" (exact decode_nat (frame tag_nat "\064\000\000\000\000\000\000\000") = None);
  check "a nat of eight digits at max_int is accepted" (exact decode_nat (frame tag_nat "\063\255\255\255\255\255\255\255") = Some max_int);
  check "a bool byte other than 0/1 is refused" (exact decode_bool (frame tag_bool "\002") = None && exact decode_bool (frame tag_bool "\001\000") = None);
  check "unit with a payload is refused" (exact decode_unit (frame tag_unit "\000") = None);
  check "the empty string round-trips" (exact decode_string (to_string emit_string "") = Some "");
  check "UTF-8: multi-byte scalars are accepted" (utf8_valid "h\xc3\xa9llo \xe6\x97\xa5\xe6\x9c\xac \xf0\x9f\x98\x80");
  check "UTF-8: a stray continuation byte is refused" (not (utf8_valid "\x80") && exact decode_string (frame tag_string "\xff") = None);
  check "UTF-8: overlong and surrogate encodings are refused" (not (utf8_valid "\xc0\x80") && not (utf8_valid "\xed\xa0\x80") && not (utf8_valid "\xf4\x90\x80\x80"));
  check "UTF-8: a truncated sequence is refused" (not (utf8_valid "\xe6\x97"));
  check "emit_string refuses invalid UTF-8" (try ignore (to_string emit_string "\xff"); false with Invalid_argument _ -> true);
  check "a frame shorter than nine bytes is refused" (read_frame "\002\000" 0 2 = None && exact decode_nat "" = None);
  check "an option's some must fill its payload" (exact (decode_option decode_nat) (frame tag_some (nat_digits 1)) = None);
  check "a list decodes its elements exactly"
    (exact (decode_list decode_nat) (to_string (fun b xs -> emit_list b emit_nat xs) [ 1; 2; 3 ]) = Some [ 1; 2; 3 ]);
  check "a pair with a third element is refused"
    (exact (decode_pair decode_nat decode_nat) (frame tag_pair (to_string emit_nat 1 ^ to_string emit_nat 2 ^ to_string emit_nat 3)) = None)


let () =
  Printf.printf "test_eff: %d checks, %d failures\n%!" !checks !failures;
  if !failures > 0 then exit 1
