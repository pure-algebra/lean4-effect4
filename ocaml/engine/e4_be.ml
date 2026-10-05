(* E4_be — the canonical framing.  The property list is in e4_be.mli.
   Each operation forwards to Eff_frame (ocaml/eff/eff_frame.ml), the one implementation of
   the byte rule.  What stays here is what a caller of Eff_frame establishes before it calls:
   the sign of an int, the range of a tag, and the window of `read_be64`. *)

let header_length = 9

let frame_length (n : int) : int = header_length + n

(* Eff_frame.emit_be64 writes the eight bytes of any int.  The refusal of a negative one is
   this module's. *)
let be64 (n : int) : string =
  if n < 0 then invalid_arg "E4_be.be64: negative";
  let b = Buffer.create 8 in
  Eff_frame.emit_be64 b n;
  Buffer.contents b

(* Eff_frame.read_be64 reads eight bytes at pos without a check: its one caller,
   Eff_frame.read_frame, has checked the window.  The check of D3 stays before the call. *)
let read_be64 (s : string) (pos : int) : int option =
  if pos < 0 || pos > String.length s - 8 then None else Eff_frame.read_be64 s pos

(* Eff_frame.emit_frame takes the tag through Char.chr.  The refusal of a tag that is not a
   byte is this module's, with its own message. *)
let framed (tag : int) (payload : string) : string =
  if tag < 0 || tag > 255 then invalid_arg "E4_be.framed: tag is not a byte";
  let b = Buffer.create (header_length + String.length payload) in
  Eff_frame.emit_frame b tag payload;
  Buffer.contents b

(* Eff_frame.read_frame checks its own window before it reads: (tag, payload_start,
   payload_end, next). *)
let read_frame (s : string) (pos : int) (limit : int) : (int * int * int * int) option =
  Eff_frame.read_frame s pos limit

(* One frame as an Eff_frame decoder.  Eff_frame.exact then refuses trailing bytes. *)
let frame : (int * int * int) Eff_frame.decoder = fun s pos limit ->
  match Eff_frame.read_frame s pos limit with
  | Some (tag, p, e, next) -> Some ((tag, p, e), next)
  | None -> None

let exact_frame (s : string) : (int * string) option =
  match Eff_frame.exact frame s with
  | Some (tag, p, e) -> Some (tag, String.sub s p (e - p))
  | None -> None

let nat_digits (n : int) : string =
  if n < 0 then invalid_arg "E4_be.nat_digits: negative";
  Eff_frame.nat_digits n

(* Eff_frame reads a natural's digits inside its frame only (decode_nat).  The digits are
   framed and then read: one copy of the digits and nine bytes (D4). *)
let nat_of_digits (s : string) : int option =
  let b = Buffer.create (header_length + String.length s) in
  Eff_frame.emit_frame b Eff_frame.tag_nat s;
  Eff_frame.exact Eff_frame.decode_nat (Buffer.contents b)
