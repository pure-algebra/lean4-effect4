(* E4_be — the canonical framing.

   What it is: the engine's name for the byte rule of src/Effect4/Store/Canonical.lean and
   src/Effect4/Program/Wire.lean:

     framed tag payload = tag :: be64 (String.length payload) ++ payload,  be64 = 8 big-endian
     bytes; a natural is base-256 big-endian with no leading zero and 0 is the empty digit
     string.

   ocaml/eff/eff_frame.ml is the tested implementation of that rule (ocaml/eff/README.md:
   138-140, 6947 checks / 0 failures at :197) and this module agrees with it byte for byte;
   see D1 for why it is a transcription of the framing layer rather than the delegation
   docs/research/2026-09-08-engine-a1-state.md §3.4 wrote.  There is still exactly one
   *encoding*: this module carries no value decoders, no Val/Eff cases and no second
   canonical form -- brief §2.2, "No second encoding is ever hashed".

   Depends on: the OCaml standard library only.

   Behaviours:
   B1  Byte agreement with Eff_frame: for every golden in ocaml/eff/goldens the outer frame
       this module reads is the one Eff_frame wrote, and re-framing its tag and payload
       reproduces the golden's bytes exactly.  `be64`, `read_be64`, `read_frame` and
       `nat_digits` are transcriptions of eff_frame.ml:81-109 and :159-214.       tested
   B2  framed tag payload = tag :: be64 (String.length payload) ++ payload
       (Eff_frame.emit_be64 :81; emit_frame :86).                       by construction; tested
   B3  A natural is base-256 big-endian with no leading zero; 0 is the empty payload
       (Eff_frame.nat_digits :97).                                      by construction; tested
   B4  Decoding is length-directed and exact: a length that runs past the limit, a window
       shorter than a header, and a negative position are refusals, never repairs
       (Eff_frame.read_frame :170-178).                                 by construction; tested
   B5  Bound: a be64 whose top byte is >= 0x40 -- a length at or above 2^62 -- is refused,
       and so is a natural of nine digits, or of eight with a top byte >= 0x40
       (E4_nat.fits_wire; Eff_frame :160, :199-215).                    by construction; tested
   B6  Total on the reading side: no exception escapes `read_be64`, `read_frame`,
       `nat_of_digits` or `exact_frame` for any string, position and limit.       tested

   Deviations from docs/research/2026-09-08-engine-a1-state.md §3.4 (lane M, 2026-09-08):
   D1  This module does NOT delegate to Eff_frame, because ocaml/engine/dune (which lane M
       does not own) lists `unix threads.posix` only: `effect4_eff` is not a dependency of
       effect4_engine and the library does not build standalone with one.  The framing
       layer is therefore transcribed -- 60 lines, no value decoders -- and pinned to
       Eff_frame's own output by the golden test (B1).  When the coordinator adds
       `effect4_eff` to the engine's libraries, the bodies here can become one-line
       forwards and the golden test becomes the delegation check A1 §3.4 wanted.
   D2  `program_of_bytes`, `bytes_of_program` and `address` are NOT here: their types name
       `Eff_types.eff`, which is exactly the dependency D1 refuses.  They belong to the
       lane that lands the program seam; `address` is then
       `E4_sha256.hex (bytes_of_program p)` and nothing else.
   D3  `read_be64` bounds-checks its window (Eff_frame's reads eight bytes unconditionally
       because its one caller checked first).  On every in-range input the two agree.
   D4  `nat_of_digits` and `exact_frame` are added: the digit-string reader of
       Eff_frame.decode_nat :199-214 without its frame, and "the whole string is one frame"
       (Eff_frame.exact :300 restricted to the framing layer). *)

val be64 : int -> string
(** Eight big-endian bytes.  Raises Invalid_argument on a negative int. *)

val read_be64 : string -> int -> int option
(** Eight bytes at pos, or None past the end / below 0 / at or above 2^62 (B5). *)

val framed : int -> string -> string
(** tag :: be64 (length payload) ++ payload.  Raises Invalid_argument unless 0 <= tag <= 255. *)

val read_frame : string -> int -> int -> (int * int * int * int) option
(** [read_frame s pos limit] is (tag, payload_pos, payload_end, frame_end), or None --
    Eff_frame.read_frame (:170). *)

val exact_frame : string -> (int * string) option
(** The whole string is one frame: (tag, payload).  Trailing bytes are a refusal. *)

val nat_digits : int -> string
(** Base-256 big-endian, no leading zero; 0 is "".  Raises Invalid_argument if negative. *)

val nat_of_digits : string -> int option
(** The inverse of nat_digits: None on a leading zero digit, on more than eight digits, or
    on eight digits whose top byte is >= 0x40 (Eff_frame.decode_nat :199-214). *)

val frame_length : int -> int
(** The bytes a frame over a payload of this length occupies: 9 + n. *)

val header_length : int
(** 9: the tag byte and the be64 length. *)
