(* Eff_frame — the framing kernel of the canonical wire (hand-written).

   What it is: the byte rule of src/Effect4/Store/Domain/Canonical.lean, as OCaml.
     framed tag payload = tag :: be64 (length payload) ++ payload, be64 = 8 big-endian bytes.
     Unit 9 [] | Bool 1 [0|1] | Nat 2 base-256 big-endian digits, no leading zero, 0 = []
     | String 3 utf8 | List 4 (concat) | none 6 [] | some 7 x | pair 5 (a ++ b)
     | constructor i 10 (encode (i : Nat) ++ args)   (a structure is constructor 0)
     | ref 11 (kind :: digest)      | handle 12 (kind :: nat digits)
   Depends on: the OCaml standard library only.

   Tags 11 and 12 are the two frames the shared value foundation adds on top of the ten of
   Canonical.lean; the authority for their payloads is the Lean encoder itself,
   src/Effect4/Store/Carrier/Val.lean:158-159 (`.ref k d => framed Tag.ref (k :: d)` and
   `.handle k n => framed Tag.handle (k :: natBytes n)`), restated at :203-204 as `payload`.
   A ref's digest is opaque bytes of any length, including none; a handle's key is the same
   shortest-form digit string a Nat frame carries, so the key 0 is one kind byte and no
   digits (Val.lean:1136: `encode (.handle 1 0) = [12,0,0,0,0,0,0,0,1, 1]`). Neither frame
   is a program frame: the Eff wire dispatches on tags 1..10 only, so a ref or a handle
   reaching Eff_wire is refused by the tag comparison it fails.

   Behaviours it holds itself to:
   F1  Every frame is self-delimiting: a decoder never reads past payload_end, and every
       decoder's result offset is the frame's end.                     by construction (read_frame)
   F2  Exactness: a wrong tag, a payload of the wrong length, a Bool byte other than 0/1, a
       Nat with a leading zero digit or above max_int, a String that is not valid UTF-8, a
       list/option/pair whose elements do not fill the payload exactly, a ref or handle whose
       payload has no kind byte, a handle whose key digits have a leading zero or run past
       max_int, or trailing bytes after the top-level frame (exact) are refusals (None), never
       repairs.                                                         by construction; tested
   F3  Round trip: decode (encode v) = Some v for every value in the Lean image, i.e. every
       int in 0 .. max_int and every valid UTF-8 string.                tested (property test)
   F4  The Lean image is the domain of encode: emit_nat raises Invalid_argument on a negative
       int, emit_string on a string that is not valid UTF-8.            by construction
   F5  Termination: an element loop advances by at least 9 bytes per element.  by construction
   F6  The writers allocate no string per frame header: `emit_be64` is one 64-bit write, and
       `emit_nat`, `emit_ref` and `emit_handle` write their payloads in place. Their bytes are
       the per-byte rule's, for every int, the negative ones included.  by construction; tested
       (test_frame B: the old rule on 3 956 ints, both ends and every byte boundary)
   F7  One pass: an encoding is written into one growable buffer, and the encoder writes each
       of its bytes once. A nested frame reserves its eight length bytes, writes its payload in
       place and fills the length after. Doubling the buffer copies the bytes already written,
       at most once per byte amortised, and the result is one copy of the buffer. Before, each
       nested payload went into a fresh Buffer and was copied behind its header, so a byte at
       depth d was written d + 1 times.                 by construction; tested (test_eff goldens)
       Chosen over folding the sizes first by measurement (bench_frame, ocaml/engine/bench/):
       in two runs the reserve writer was faster on every value of 6 KB and more, by 1.14x to
       1.97x, and level on a 61-byte value; and the fold runs every payload callback twice
       where this runs it once.
   F8  An encoding is bounded: `encode ~limit` refuses one that needs more than `limit` bytes as
       a value (default Sys.max_string_length, the most a string holds, 2^57 - 9 on a 64-bit
       host). Nothing is published on a refusal, and a refusal that a callback swallows is
       still one: the writer remembers it. `to_string` raises Invalid_argument there instead,
       as it does on a value outside the Lean image (F4). Lengths are byte counts in
       0 .. limit, so every frame length is inside the field's 0 .. 2^62 - 1 that `read_be64`
       accepts.
                                                       by construction; tested (test_frame O)
   F9  A payload callback runs once. If it raises, the writer is rolled back to before the
       frame and the exception escapes, so no partial frame stays.      tested (test_frame P)
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
let tag_ref = 11
let tag_handle = 12
(* The signed and binary64 frames of the value append (decisions rows 121, 162): named so the
   tag table matches the store's; a program's wire carries neither, so no reader here takes one. *)
let tag_int = 13
let tag_float = 14

(* ---- UTF-8 (RFC 3629: no overlongs, no surrogates, at most U+10FFFF) ---- *)

let utf8_valid (s : string) : bool = String.is_valid_utf_8 s

(* ---- encoding: one growable buffer, each nested length reserved and filled after (F7) ---- *)

(* The bytes written so far are buf[0, len). [limit] bounds len, and [over] records that a write
   was refused past it: sticky, so a refusal a callback swallows is still a refusal (F8). *)
type writer = { mutable buf : Bytes.t; mutable len : int; limit : int; mutable over : bool }

type too_large = { limit : int }

(* Raised by [reserve] past the limit and caught by [encode]; it never escapes this module
   unless a caller's own callback lets it through [to_string], which raises its own refusal. *)
exception Over

let grow (w : writer) (need : int) : unit =
  let want = w.len + need in
  let cap = ref (max 64 (2 * Bytes.length w.buf)) in
  while !cap < want do
    cap := 2 * !cap
  done;
  let b = Bytes.create (min !cap w.limit) in
  Bytes.blit w.buf 0 b 0 w.len;
  w.buf <- b

(* Room for [need] more bytes, or the refusal: [need > limit - len] cannot overflow, since
   0 <= len <= limit. After it, buf[len, len + need) is writable. *)
let reserve (w : writer) (need : int) : unit =
  if need > w.limit - w.len then begin
    w.over <- true;
    raise Over
  end
  else if w.len + need > Bytes.length w.buf then grow w need

(* A frame header at [at]: the tag, then the 63-bit length with bit 63 clear (F6). *)
let set_header (w : writer) (at : int) (tag : char) (length : int) : unit =
  Bytes.unsafe_set w.buf at tag;
  Bytes.set_int64_be w.buf (at + 1) (Int64.logand (Int64.of_int length) Int64.max_int)

(* The eight bytes of `n lsr (8 * shift)`, shift 7 down to 0, in one write: the 63-bit int's
   pattern with bit 63 clear, which `Int64.of_int` sets for a negative int (F6). *)
let emit_be64 (w : writer) (n : int) : unit =
  reserve w 8;
  Bytes.set_int64_be w.buf w.len (Int64.logand (Int64.of_int n) Int64.max_int);
  w.len <- w.len + 8

(* The tag is checked before any byte is written; header and payload are reserved together,
   so a refusal leaves no partial frame. *)
let emit_frame (w : writer) (tag : int) (payload : string) : unit =
  let tag = Char.chr tag and k = String.length payload in
  reserve w (9 + k);
  set_header w w.len tag k;
  Bytes.unsafe_blit_string payload 0 w.buf (w.len + 9) k;
  w.len <- w.len + 9 + k

(* The header is written with its length reserved, the payload in place, the length after
   (F7). The callback runs once; if it raises, the writer is rolled back to before the frame
   and the exception escapes (F9). *)
let with_payload (w : writer) (tag : int) (f : writer -> unit) : unit =
  let tag = Char.chr tag and start = w.len in
  reserve w 9;
  Bytes.unsafe_set w.buf start tag;
  w.len <- start + 9;
  match f w with
  | () -> Bytes.set_int64_be w.buf (start + 1) (Int64.of_int (w.len - start - 9))
  | exception e ->
    w.len <- start;
    raise e

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

let emit_unit (w : writer) (() : unit) : unit = emit_frame w tag_unit ""

let emit_bool (w : writer) (v : bool) : unit =
  emit_frame w tag_bool (if v then "\001" else "\000")

let digit_count (n : int) : int =
  let rec count m k = if m = 0 then k else count (m lsr 8) (k + 1) in
  count n 0

(* The digits of [n], [k] of them, at buf[at, at + k): reserved by the caller (F6). *)
let set_digits (w : writer) (at : int) (n : int) (k : int) : unit =
  for i = 0 to k - 1 do
    Bytes.unsafe_set w.buf (at + i) (Char.unsafe_chr ((n lsr (8 * (k - 1 - i))) land 0xff))
  done

(* `emit_frame w tag_nat (nat_digits n)`, with the digits written in place (F6). *)
let emit_nat (w : writer) (n : int) : unit =
  if n < 0 then invalid_arg "Eff_frame.nat_digits: negative";
  let k = digit_count n in
  reserve w (9 + k);
  set_header w w.len (Char.unsafe_chr tag_nat) k;
  set_digits w (w.len + 9) n k;
  w.len <- w.len + 9 + k

let emit_string (w : writer) (s : string) : unit =
  if not (utf8_valid s) then invalid_arg "Eff_frame.emit_string: not valid UTF-8";
  emit_frame w tag_string s

let emit_list (w : writer) (f : writer -> 'a -> unit) (xs : 'a list) : unit =
  with_payload w tag_list (fun w -> List.iter (f w) xs)

let emit_option (w : writer) (f : writer -> 'a -> unit) (o : 'a option) : unit =
  match o with
  | None -> emit_frame w tag_none ""
  | Some x -> with_payload w tag_some (fun w -> f w x)

let emit_pair (w : writer) (f : writer -> 'a -> unit) (g : writer -> 'b -> unit)
    ((x, y) : 'a * 'b) : unit =
  with_payload w tag_pair (fun w -> f w x; g w y)

let emit_ctor (w : writer) (index : int) (args : writer -> unit) : unit =
  with_payload w tag_ctor (fun w -> emit_nat w index; args w)

(* A content reference: the kind byte, then the digest bytes (Val.lean:158). The digest is
   opaque — any byte string, the empty one included. *)
let emit_ref (w : writer) ((kind, digest) : int * string) : unit =
  if kind < 0 || kind > 255 then invalid_arg "Eff_frame.emit_ref: kind is not a byte";
  let k = String.length digest in
  reserve w (10 + k);
  set_header w w.len (Char.unsafe_chr tag_ref) (1 + k);
  Bytes.unsafe_set w.buf (w.len + 9) (Char.unsafe_chr kind);
  Bytes.unsafe_blit_string digest 0 w.buf (w.len + 10) k;
  w.len <- w.len + 10 + k

(* A live handle: the kind byte, then the key as Nat digits (Val.lean:159). The key 0 is no
   digits at all, so the payload is the kind byte alone. *)
let emit_handle (w : writer) ((kind, key) : int * int) : unit =
  if kind < 0 || kind > 255 then invalid_arg "Eff_frame.emit_handle: kind is not a byte";
  if key < 0 then invalid_arg "Eff_frame.emit_handle: negative key";
  let k = digit_count key in
  reserve w (10 + k);
  set_header w w.len (Char.unsafe_chr tag_handle) (1 + k);
  Bytes.unsafe_set w.buf (w.len + 9) (Char.unsafe_chr kind);
  set_digits w (w.len + 10) key k;
  w.len <- w.len + 10 + k

(* The default bound: an encoding is a string, so it holds at most Sys.max_string_length bytes
   (2^57 - 9 on a 64-bit host), below the length field's 0 .. 2^62 - 1 (F8). *)
let max_length = Sys.max_string_length

let encode ?(limit = max_length) (f : writer -> 'a -> unit) (v : 'a) : (string, too_large) result =
  let limit = max 0 (min limit max_length) in
  let w = { buf = Bytes.create (min 256 limit); len = 0; limit; over = false } in
  match f w v with
  | () -> if w.over then Error { limit } else Ok (Bytes.sub_string w.buf 0 w.len)
  | exception Over -> Error { limit }

let to_string (f : writer -> 'a -> unit) (v : 'a) : string =
  match encode f v with
  | Ok s -> s
  | Error { limit } -> invalid_arg (Printf.sprintf "Eff_frame.to_string: the encoding exceeds %d bytes" limit)

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
  if pos < 0 || limit < pos || limit > String.length s || limit - pos < 9 then None
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

(* A natural's shortest big-endian digits, s[p..e): no digit is 0, a leading zero is a refusal,
   and nine digits, or eight above max_int, are out of range. *)
let nat_of_digits (s : string) (p : int) (e : int) : int option =
  let len = e - p in
  if len = 0 then Some 0
  else if len > 8 then None
  else if String.unsafe_get s p = '\000' then None
  else if len = 8 && Char.code (String.unsafe_get s p) >= 0x40 then None
  else begin
    let n = ref 0 in
    for i = p to e - 1 do
      n := (!n lsl 8) lor Char.code (String.unsafe_get s i)
    done;
    Some !n
  end

let decode_nat : int decoder = fun s pos limit ->
  match expect tag_nat s pos limit with
  | None -> None
  | Some (p, e, next) -> Option.map (fun n -> (n, next)) (nat_of_digits s p e)

(* The negative integer `-(n+1)`, as its `n`: tag 13 over n's digits, the `nat` rule. *)
let decode_neg_int : int decoder = fun s pos limit ->
  match expect tag_int s pos limit with
  | None -> None
  | Some (p, e, next) -> Option.map (fun n -> (n, next)) (nat_of_digits s p e)

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

(* Proof-bearing Lean rows retain list bytes and refuse unordered foreign values.
   The caller supplies the selected element order; no sorting repairs input. *)
let rec strictly_ascending lt = function
  | [] | [_] -> true
  | a :: (b :: _ as rest) -> lt a b && strictly_ascending lt rest

let decode_checked_list d lt s pos limit =
  match decode_list d s pos limit with
  | Some (xs, next) when strictly_ascending lt xs -> Some (xs, next)
  | _ -> None

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

(* A ref frame: the kind byte and the rest of the payload as the digest. An empty payload
   carries no kind byte and is refused (Val.lean:614-617, 1169). *)
let decode_ref : (int * string) decoder = fun s pos limit ->
  match expect tag_ref s pos limit with
  | None -> None
  | Some (p, e, next) ->
    if e = p then None
    else Some ((Char.code (String.unsafe_get s p), String.sub s (p + 1) (e - p - 1)), next)

(* A handle frame: the kind byte, then the key's Nat digits. An empty payload is refused; a
   leading zero digit is refused; no digits is the key 0 (Val.lean:618-621, 1136, 1176-1177).
   The bound is decode_nat's: nine digits, or eight above max_int, are out of range. *)
let decode_handle : (int * int) decoder = fun s pos limit ->
  match expect tag_handle s pos limit with
  | None -> None
  | Some (p, e, next) ->
    if e = p then None
    else begin
      let kind = Char.code (String.unsafe_get s p) in
      let d = p + 1 in
      let len = e - d in
      if len = 0 then Some ((kind, 0), next)
      else if len > 8 then None
      else if String.unsafe_get s d = '\000' then None
      else if len = 8 && Char.code (String.unsafe_get s d) >= 0x40 then None
      else begin
        let n = ref 0 in
        for i = d to e - 1 do
          n := (!n lsl 8) lor Char.code (String.unsafe_get s i)
        done;
        Some ((kind, !n), next)
      end
    end

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
