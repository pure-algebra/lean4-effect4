(* E4_be — the canonical framing.  The property list is in e4_be.mli.
   Every function is a transcription of ocaml/eff/eff_frame.ml (see D1 there). *)

let header_length = 9

let frame_length (n : int) : int = header_length + n

(* eff_frame.ml:81 emit_be64: shift 7 downto 0, one byte each. *)
let be64 (n : int) : string =
  if n < 0 then invalid_arg "E4_be.be64: negative";
  let b = Bytes.create 8 in
  for i = 0 to 7 do
    Bytes.unsafe_set b i (Char.unsafe_chr ((n lsr (8 * (7 - i))) land 0xff))
  done;
  Bytes.unsafe_to_string b

(* eff_frame.ml:159 read_be64, with the window check of D3.  A top byte >= 0x40 is a
   length at or above 2^62: outside E4_nat.fits_wire, refused. *)
let read_be64 (s : string) (pos : int) : int option =
  if pos < 0 || pos + 8 > String.length s then None
  else if Char.code (String.unsafe_get s pos) >= 0x40 then None
  else begin
    let n = ref 0 in
    for i = 0 to 7 do
      n := (!n lsl 8) lor Char.code (String.unsafe_get s (pos + i))
    done;
    Some !n
  end

(* eff_frame.ml:86 emit_frame. *)
let framed (tag : int) (payload : string) : string =
  if tag < 0 || tag > 255 then invalid_arg "E4_be.framed: tag is not a byte";
  let n = String.length payload in
  let b = Bytes.create (header_length + n) in
  Bytes.unsafe_set b 0 (Char.unsafe_chr tag);
  for i = 0 to 7 do
    Bytes.unsafe_set b (1 + i) (Char.unsafe_chr ((n lsr (8 * (7 - i))) land 0xff))
  done;
  Bytes.blit_string payload 0 b header_length n;
  Bytes.unsafe_to_string b

(* eff_frame.ml:170 read_frame: (tag, payload_start, payload_end, next). *)
let read_frame (s : string) (pos : int) (limit : int) : (int * int * int * int) option =
  if pos < 0 || limit > String.length s || pos + header_length > limit then None
  else
    match read_be64 s (pos + 1) with
    | None -> None
    | Some len ->
      let start = pos + header_length in
      if len > limit - start then None
      else Some (Char.code (String.unsafe_get s pos), start, start + len, start + len)

let exact_frame (s : string) : (int * string) option =
  match read_frame s 0 (String.length s) with
  | Some (tag, p, e, next) when next = String.length s -> Some (tag, String.sub s p (e - p))
  | _ -> None

(* eff_frame.ml:97 nat_digits. *)
let nat_digits (n : int) : string =
  if n < 0 then invalid_arg "E4_be.nat_digits: negative";
  let rec count m acc = if m = 0 then acc else count (m lsr 8) (acc + 1) in
  let k = count n 0 in
  let b = Bytes.create k in
  let rec fill m i =
    if i >= 0 then begin
      Bytes.unsafe_set b i (Char.unsafe_chr (m land 0xff));
      fill (m lsr 8) (i - 1)
    end
  in
  fill n (k - 1);
  Bytes.unsafe_to_string b

(* eff_frame.ml:199 decode_nat, without the frame: shortest form only, bounded by
   E4_nat.fits_wire. *)
let nat_of_digits (s : string) : int option =
  let len = String.length s in
  if len = 0 then Some 0
  else if len > 8 then None
  else if String.unsafe_get s 0 = '\000' then None
  else if len = 8 && Char.code (String.unsafe_get s 0) >= 0x40 then None
  else begin
    let n = ref 0 in
    for i = 0 to len - 1 do
      n := (!n lsl 8) lor Char.code (String.unsafe_get s i)
    done;
    Some !n
  end
