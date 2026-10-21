(** The framing kernel of the canonical wire: the byte rule of src/Effect4/Store/Domain/Canonical.lean.
    [framed tag payload = tag :: be64 (length payload) ++ payload]. The properties F1 to F10 are
    eff_frame.ml's header. *)

(** {1 The tags} *)

val tag_bool : int
val tag_nat : int
val tag_string : int
val tag_list : int
val tag_pair : int
val tag_none : int
val tag_some : int
val tag_bytes : int
val tag_unit : int
val tag_ctor : int
val tag_ref : int
val tag_handle : int

(** The signed frame of the value append; a program's wire carries none. *)
val tag_int : int

(** The binary64 frame of the value append; a program's wire carries none. *)
val tag_float : int

(** RFC 3629: no overlongs, no surrogates, at most U+10FFFF. *)
val utf8_valid : string -> bool

(** {1 Writing} *)

(** One encoding being written: a growable buffer that only {!encode} and {!to_string} make
    and only they publish (F7). *)
type writer

(** The eight bytes of the 63-bit pattern of any int, bit 63 clear (F6). *)
val emit_be64 : writer -> int -> unit

(** One frame of a payload in hand. @raise Invalid_argument for a tag outside a byte, before
    any byte is written. *)
val emit_frame : writer -> int -> string -> unit

(** One frame whose payload the callback writes in place; the length is filled after (F7). The
    callback runs once; if it raises, the writer is rolled back to before the frame (F9).
    @raise Invalid_argument for a tag outside a byte, before the callback runs. *)
val with_payload : writer -> int -> (writer -> unit) -> unit

(** Base-256 digits, big-endian, no leading zero; 0 is the empty string.
    @raise Invalid_argument on a negative integer. *)
val nat_digits : Z.t -> string

val emit_unit : writer -> unit -> unit
val emit_bool : writer -> bool -> unit

(** @raise Invalid_argument on a negative integer (F4). *)
val emit_nat : writer -> Z.t -> unit

(** @raise Invalid_argument on a string that is not valid UTF-8, before any byte (F4). *)
val emit_string : writer -> string -> unit

val emit_list : writer -> (writer -> 'a -> unit) -> 'a list -> unit
val emit_option : writer -> (writer -> 'a -> unit) -> 'a option -> unit

val emit_pair
  :  writer
  -> (writer -> 'a -> unit)
  -> (writer -> 'b -> unit)
  -> 'a * 'b
  -> unit

(** A constructor frame: the index, then what the callback writes. *)
val emit_ctor : writer -> Z.t -> (writer -> unit) -> unit

(** A content reference: the kind byte, then the digest (Val.lean:158).
    @raise Invalid_argument for a kind outside a byte. *)
val emit_ref : writer -> int * string -> unit

(** A live handle: the kind byte, then the key's Nat digits (Val.lean:159).
    @raise Invalid_argument for a kind outside a byte or a negative key. *)
val emit_handle : writer -> int * Z.t -> unit

(** Why {!encode} published nothing: the encoding needs more than [limit] bytes. *)
type too_large = { limit : int }

(** The bytes the writer function writes for the value, or the refusal when they need more than
    [limit] bytes (default Sys.max_string_length); nothing is published on a refusal, even one a
    callback swallowed (F8). A value outside the Lean image raises Invalid_argument (F4). *)
val encode : ?limit:int -> (writer -> 'a -> unit) -> 'a -> (string, too_large) result

(** {!encode} at the default limit, its refusal raised as Invalid_argument (F8). *)
val to_string : (writer -> 'a -> unit) -> 'a -> string

(** {1 Reading: (s, pos, limit) to (value, next), never reading at or past limit} *)

type 'a decoder = string -> int -> int -> ('a * int) option

(** Eight bytes at [pos], or [None]: a window shorter than eight bytes, a negative position, or a
    top byte of at least 0x40, so the length is outside 0 .. 2^62 - 1 (F10). *)
val read_be64 : string -> int -> int option

(** [(tag, payload_start, payload_end, next)], or [None] for a window that holds no frame. *)
val read_frame : string -> int -> int -> (int * int * int * int) option

(** A frame of this tag: [(payload_start, payload_end, next)]. *)
val expect : int -> string -> int -> int -> (int * int * int) option

val decode_unit : unit decoder
val decode_bool : bool decoder

(** A natural's shortest big-endian digits in [s.[p..e)], or [None] for a leading zero. Every
    natural is read exactly (M4). *)
val nat_of_digits : string -> int -> int -> Z.t option

val decode_nat : Z.t decoder
val decode_neg_int : Z.t decoder
val decode_string : string decoder
val decode_list : 'a decoder -> 'a list decoder
val strictly_ascending : ('a -> 'a -> bool) -> 'a list -> bool

(** A list whose elements are strictly ascending under the order given; no sort repairs input. *)
val decode_checked_list : 'a decoder -> ('a -> 'a -> bool) -> 'a list decoder

val decode_option : 'a decoder -> 'a option decoder
val decode_pair : 'a decoder -> 'b decoder -> ('a * 'b) decoder
val decode_ref : (int * string) decoder
val decode_handle : (int * Z.t) decoder

(** A constructor frame: [(index, position after the index, payload_end, next)]. *)
val read_ctor : string -> int -> int -> (Z.t * int * int * int) option

(** The whole string is one frame: trailing bytes are a refusal. *)
val exact : 'a decoder -> string -> 'a option

(** {1 The whole-string face (F10)} *)

(** 9: the tag byte and the eight length bytes. *)
val header_length : int

(** The bytes a frame over a payload of this length occupies: 9 + n. *)
val frame_length : int -> int

(** Eight big-endian bytes. @raise Invalid_argument on a negative int. *)
val be64 : int -> string

(** [tag :: be64 (length payload) ++ payload]. @raise Invalid_argument unless 0 <= tag <= 255. *)
val framed : int -> string -> string

(** The whole string is one frame: its tag and payload. Trailing bytes are a refusal. *)
val exact_frame : string -> (int * string) option
