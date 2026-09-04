(* Eff_frame — the framing kernel of the canonical wire (hand-written).

   What it is: the byte rule of src/Effect4/Store/Canonical.lean, as OCaml.
     framed tag payload = tag :: be64 (length payload) ++ payload, be64 = 8 big-endian bytes.
     Unit 9 [] | Bool 1 [0|1] | Nat 2 base-256 big-endian digits, no leading zero, 0 = []
     | String 3 utf8 | List 4 (concat) | none 6 [] | some 7 x | pair 5 (a ++ b)
     | constructor i 10 (encode (i : Nat) ++ args)   (a structure is constructor 0)
   Depends on: the OCaml standard library only.

   Behaviours it holds itself to:
   F1  Every frame is self-delimiting: a decoder never reads past payload_end, and every
       decoder's result offset is the frame's end.                     by construction (read_frame)
   F2  Exactness: a wrong tag, a payload of the wrong length, a Bool byte other than 0/1, a
       Nat with a leading zero digit or above max_int, a String that is not valid UTF-8, a
       list/option/pair whose elements do not fill the payload exactly, or trailing bytes
       after the top-level frame (exact) are refusals (None), never repairs.
                                                                        by construction; tested
   F3  Round trip: decode (encode v) = Some v for every value in the Lean image, i.e. every
       int in 0 .. max_int and every valid UTF-8 string.                tested (property test)
   F4  The Lean image is the domain of encode: emit_nat raises Invalid_argument on a negative
       int, emit_string on a string that is not valid UTF-8.            by construction
   F5  Termination: an element loop advances by at least 9 bytes per element.  by construction
   Bound: Lean's Nat is unbounded; this kernel carries 0 .. 2^62 - 1 (OCaml int on 64-bit
   hosts). A Nat frame of nine or more digits, or of eight digits with a top byte >= 0x40,
   is refused as out of range. *)

let tag_bool = 1
let tag_nat = 2
let tag_string = 3
let tag_list = 4
let tag_pair = 5
let tag_none = 6
let tag_some = 7
let tag_bytes = 8
let tag_unit = 9
let tag_ctor = 10

(* ---- UTF-8 (RFC 3629: no overlongs, no surrogates, at most U+10FFFF) ---- *)

let utf8_valid (s : string) : bool =
  let n = String.length s in
  let byte i = Char.code (String.unsafe_get s i) in
  let cont i = i < n && byte i land 0xc0 = 0x80 in
  let rec go i =
    if i >= n then true
    else
      let b = byte i in
      if b < 0x80 then go (i + 1)
      else if b < 0xc2 then false
      else if b < 0xe0 then cont (i + 1) && go (i + 2)
      else if b < 0xf0 then
        cont (i + 1) && cont (i + 2)
        && (let b1 = byte (i + 1) in
            (b <> 0xe0 || b1 >= 0xa0) && (b <> 0xed || b1 < 0xa0))
        && go (i + 3)
      else if b < 0xf5 then
        cont (i + 1) && cont (i + 2) && cont (i + 3)
        && (let b1 = byte (i + 1) in
            (b <> 0xf0 || b1 >= 0x90) && (b <> 0xf4 || b1 < 0x90))
        && go (i + 4)
      else false
  in
  go 0

(* ---- encoding ---- *)

let emit_be64 (b : Buffer.t) (n : int) : unit =
  for shift = 7 downto 0 do
    Buffer.add_char b (Char.chr ((n lsr (8 * shift)) land 0xff))
  done

let emit_frame (b : Buffer.t) (tag : int) (payload : string) : unit =
  Buffer.add_char b (Char.chr tag);
  emit_be64 b (String.length payload);
  Buffer.add_string b payload

let with_payload (b : Buffer.t) (tag : int) (f : Buffer.t -> unit) : unit =
  let p = Buffer.create 32 in
  f p;
  emit_frame b tag (Buffer.contents p)

(* Base-256 digits, big-endian, no leading zero; 0 is the empty string. *)
let nat_digits (n : int) : string =
  if n < 0 then invalid_arg "Eff_frame.nat_digits: negative";
  let rec count m k = if m = 0 then k else count (m lsr 8) (k + 1) in
  let k = count n 0 in
  let s = Bytes.create k in
  let rec fill m i =
    if i >= 0 then begin
      Bytes.set s i (Char.chr (m land 0xff));
      fill (m lsr 8) (i - 1)
    end
  in
  fill n (k - 1);
  Bytes.to_string s

let emit_unit (b : Buffer.t) (() : unit) : unit = emit_frame b tag_unit ""

let emit_bool (b : Buffer.t) (v : bool) : unit =
  emit_frame b tag_bool (if v then "\001" else "\000")

let emit_nat (b : Buffer.t) (n : int) : unit = emit_frame b tag_nat (nat_digits n)

let emit_string (b : Buffer.t) (s : string) : unit =
  if not (utf8_valid s) then invalid_arg "Eff_frame.emit_string: not valid UTF-8";
  emit_frame b tag_string s

let emit_list (b : Buffer.t) (f : Buffer.t -> 'a -> unit) (xs : 'a list) : unit =
  with_payload b tag_list (fun p -> List.iter (f p) xs)

let emit_option (b : Buffer.t) (f : Buffer.t -> 'a -> unit) (o : 'a option) : unit =
  match o with
  | None -> emit_frame b tag_none ""
  | Some x -> with_payload b tag_some (fun p -> f p x)

let emit_pair (b : Buffer.t) (f : Buffer.t -> 'a -> unit) (g : Buffer.t -> 'b -> unit)
    ((x, y) : 'a * 'b) : unit =
  with_payload b tag_pair (fun p -> f p x; g p y)

let emit_ctor (b : Buffer.t) (index : int) (args : Buffer.t -> unit) : unit =
  with_payload b tag_ctor (fun p -> emit_nat p index; args p)

let to_string (f : Buffer.t -> 'a -> unit) (v : 'a) : string =
  let b = Buffer.create 64 in
  f b v;
  Buffer.contents b

(* ---- decoding: (s, pos, limit) -> (value, next) option, never reading at or past limit ---- *)

type 'a decoder = string -> int -> int -> ('a * int) option

let read_be64 (s : string) (pos : int) : int option =
  if Char.code (String.unsafe_get s pos) >= 0x40 then None
  else begin
    let n = ref 0 in
    for i = 0 to 7 do
      n := (!n lsl 8) lor Char.code (String.unsafe_get s (pos + i))
    done;
    Some !n
  end

(* (tag, payload_start, payload_end, next) *)
let read_frame (s : string) (pos : int) (limit : int) : (int * int * int * int) option =
  if pos < 0 || limit > String.length s || pos + 9 > limit then None
  else
    match read_be64 s (pos + 1) with
    | None -> None
    | Some len ->
      let start = pos + 9 in
      if len > limit - start then None
      else Some (Char.code (String.unsafe_get s pos), start, start + len, start + len)

let expect (tag : int) (s : string) (pos : int) (limit : int) : (int * int * int) option =
  match read_frame s pos limit with
  | Some (t, p, e, next) when t = tag -> Some (p, e, next)
  | _ -> None

let decode_unit : unit decoder = fun s pos limit ->
  match expect tag_unit s pos limit with
  | Some (p, e, next) when p = e -> Some ((), next)
  | _ -> None

let decode_bool : bool decoder = fun s pos limit ->
  match expect tag_bool s pos limit with
  | Some (p, e, next) when e = p + 1 ->
    (match String.unsafe_get s p with
     | '\000' -> Some (false, next)
     | '\001' -> Some (true, next)
     | _ -> None)
  | _ -> None

let decode_nat : int decoder = fun s pos limit ->
  match expect tag_nat s pos limit with
  | None -> None
  | Some (p, e, next) ->
    let len = e - p in
    if len = 0 then Some (0, next)
    else if len > 8 then None
    else if String.unsafe_get s p = '\000' then None
    else if len = 8 && Char.code (String.unsafe_get s p) >= 0x40 then None
    else begin
      let n = ref 0 in
      for i = p to e - 1 do
        n := (!n lsl 8) lor Char.code (String.unsafe_get s i)
      done;
      Some (!n, next)
    end

let decode_string : string decoder = fun s pos limit ->
  match expect tag_string s pos limit with
  | None -> None
  | Some (p, e, next) ->
    let str = String.sub s p (e - p) in
    if utf8_valid str then Some (str, next) else None

let decode_list (d : 'a decoder) : 'a list decoder = fun s pos limit ->
  match expect tag_list s pos limit with
  | None -> None
  | Some (p, e, next) ->
    let rec go p acc =
      if p = e then Some (List.rev acc, next)
      else
        match d s p e with
        | None -> None
        | Some (x, p') -> go p' (x :: acc)
    in
    go p []

let decode_option (d : 'a decoder) : 'a option decoder = fun s pos limit ->
  match read_frame s pos limit with
  | Some (t, p, e, next) when t = tag_none -> if p = e then Some (None, next) else None
  | Some (t, p, e, next) when t = tag_some ->
    (match d s p e with
     | Some (x, p') when p' = e -> Some (Some x, next)
     | _ -> None)
  | _ -> None

let decode_pair (da : 'a decoder) (db : 'b decoder) : ('a * 'b) decoder = fun s pos limit ->
  match expect tag_pair s pos limit with
  | None -> None
  | Some (p, e, next) ->
    (match da s p e with
     | None -> None
     | Some (x, p) ->
       (match db s p e with
        | Some (y, p) when p = e -> Some ((x, y), next)
        | _ -> None))

(* A constructor frame: (index, position after the index, payload_end, next). *)
let read_ctor (s : string) (pos : int) (limit : int) : (int * int * int * int) option =
  match expect tag_ctor s pos limit with
  | None -> None
  | Some (p, e, next) ->
    (match decode_nat s p e with
     | Some (i, p') -> Some (i, p', e, next)
     | None -> None)

(* The whole string is one frame: trailing bytes are a refusal. *)
let exact (d : 'a decoder) (s : string) : 'a option =
  match d s 0 (String.length s) with
  | Some (v, n) when n = String.length s -> Some v
  | _ -> None
