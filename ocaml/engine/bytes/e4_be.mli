(* E4_be — the canonical framing.

   What it is: the engine's name for the byte rule of src/Effect4/Store/Canonical.lean and
   src/Effect4/Program/Wire.lean:

     framed tag payload = tag :: be64 (String.length payload) ++ payload,  be64 = 8 big-endian
     bytes; a natural is base-256 big-endian with no leading zero and 0 is the empty digit
     string.

   ocaml/eff/eff_frame.ml is the one implementation of that rule, and each operation here
   forwards to it (D1).  This module adds the checks that Eff_frame leaves to its caller: the
   sign of an int, the range of a tag, and the window of `read_be64`.  There is exactly one
   *encoding*: this module carries no value decoders, no Val/Eff cases and no second
   canonical form -- brief §2.2, "No second encoding is ever hashed".

   Depends on: `effect4_eff` (Eff_frame) and the OCaml standard library.

   Behaviours:
   B1  Byte agreement with Eff_frame: `be64`, `framed`, `read_frame`, `exact_frame`,
       `nat_digits` and `nat_of_digits` call Eff_frame.emit_be64, emit_frame, read_frame,
       exact, nat_digits and decode_nat.  For every golden in ocaml/eff/goldens the outer
       frame this module reads is the one Eff_frame wrote, and re-framing its tag and
       payload reproduces the golden's bytes exactly.                   by construction; tested
   B2  framed tag payload = tag :: be64 (String.length payload) ++ payload
       (Eff_frame.emit_be64, Eff_frame.emit_frame).                     by construction; tested
   B3  A natural is base-256 big-endian with no leading zero; 0 is the empty payload
       (Eff_frame.nat_digits).                                          by construction; tested
   B4  Decoding is length-directed and exact: a length that runs past the limit, a window
       shorter than a header, a negative position and trailing bytes are refusals, never
       repairs (Eff_frame.read_frame, Eff_frame.exact).                 by construction; tested
   B5  Bound: a be64 whose top byte is >= 0x40 -- a length at or above 2^62 -- is refused,
       and so is a natural of nine digits, or of eight with a top byte >= 0x40
       (E4_nat.fits_wire; Eff_frame.read_be64, Eff_frame.decode_nat).   by construction; tested
   B6  Total on the reading side: no exception escapes `read_be64`, `read_frame`,
       `nat_of_digits` or `exact_frame` for any string, position and limit.       tested
   B7  The writing side refuses what the rule does not carry, each with this module's own
       message: `be64` and `nat_digits` a negative int, `framed` a tag that is not a byte.
       Eff_frame.emit_be64 has no such check, and Eff_frame.emit_frame raises through
       Char.chr.                                                        by construction; tested

   Deviations from docs/research/2026-09-08-engine-a1-state.md §3.4 (lane M, 2026-09-08):
   D1  Corrected on 2026-10-05.  Lane M transcribed the framing layer, because the engine
       did not link `effect4_eff` then.  ocaml/engine/dune lists `effect4_eff` now, and
       this module delegates, as A1 §3.4 wrote.  The golden test (B1) is the delegation
       check.  The cost: `be64`, `framed` and `nat_of_digits` build their bytes in a Buffer,
       one copy more than the transcription made.  The cost is not measured.
   D2  `program_of_bytes`, `bytes_of_program` and `address` are NOT here: their types name
       `Eff_types.eff`.  The program seam is E4_program.
   D3  `read_be64` bounds-checks its window (Eff_frame's reads eight bytes unconditionally
       because its one caller checked first).  The check runs before the call.  On every
       in-range input the two agree.
   D4  `nat_of_digits` and `exact_frame` are added.  `nat_of_digits` frames the digits and
       reads them with Eff_frame.decode_nat, which reads digits inside their frame only.
       `exact_frame` is Eff_frame.exact over one frame. *)

val be64 : int -> string
(** Eight big-endian bytes.  Raises Invalid_argument on a negative int. *)

val read_be64 : string -> int -> int option
(** Eight bytes at pos, or None past the end / below 0 / at or above 2^62 (B5). *)

val framed : int -> string -> string
(** tag :: be64 (length payload) ++ payload.  Raises Invalid_argument unless 0 <= tag <= 255. *)

val read_frame : string -> int -> int -> (int * int * int * int) option
(** [read_frame s pos limit] is (tag, payload_pos, payload_end, frame_end), or None --
    Eff_frame.read_frame. *)

val exact_frame : string -> (int * string) option
(** The whole string is one frame: (tag, payload).  Trailing bytes are a refusal. *)

val nat_digits : int -> string
(** Base-256 big-endian, no leading zero; 0 is "".  Raises Invalid_argument if negative. *)

val nat_of_digits : string -> int option
(** The inverse of nat_digits: None on a leading zero digit, on more than eight digits, or
    on eight digits whose top byte is >= 0x40 (Eff_frame.decode_nat). *)

val frame_length : int -> int
(** The bytes a frame over a payload of this length occupies: 9 + n. *)

val header_length : int
(** 9: the tag byte and the be64 length. *)
