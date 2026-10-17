(* Lcnf_string -- the route's string primitives: a Lean `String` is the OCaml string of its UTF-8
   bytes, and a `Char` is its code point.

   What it is: the forms of the rows `String.toUTF8`, `String.toByteArray`, `String.length`,
   `String.ofList` and `String.ofByteArray` of `OCaml5.Lcnf.builtins`. A string the route holds is
   valid UTF-8, since the wire refuses any other (`Eff_frame.decode_string`). The target evaluator
   (`Conform.Lcnf.Target`) answers `utf8_bytes` and `utf8_length` by rule and has none for the
   other two.

   Depends on: Lcnf_array (a byte array is an `int Lcnf_array.t`), the standard library (String,
   Char, Buffer, Uchar).

   Properties:
   S1  `utf8_bytes s` lists the bytes of `s` in order: Lean's `String.toUTF8` for a valid UTF-8
       `s`.                                                             tested (test_lcnf)
   S2  `utf8_length s` counts the bytes that start a scalar value: Lean's `String.length` for a
       valid UTF-8 `s`, and not the byte count of OCaml's `String.length`.
                                                                        tested (test_lcnf)
   S3  `of_code_points` and `of_utf8_bytes` invert `utf8_bytes`, on Unicode scalar values and on
       bytes respectively.                                              tested (test_lcnf)
   S4  No function changes a value it is given; each `Buffer` is local to one call.
                                                                        by construction *)

val utf8_bytes : string -> int Lcnf_array.t
(** The bytes of the string, each an [int] in [0, 255], in order: Lean's [ByteArray]. *)

val utf8_length : string -> int
(** The number of Unicode scalar values of a valid UTF-8 string: the bytes that do not continue a
    sequence ([c land 192 <> 128]). *)

val of_code_points : int list -> string
(** The UTF-8 string of the code points, in order. Each must be a Unicode scalar value, as every
    Lean [Char] is; [Uchar.of_int] raises [Invalid_argument] on any other. *)

val of_utf8_bytes : int Lcnf_array.t -> string
(** The string whose bytes are the vector's, in order. Each must be in [0, 255], as every Lean
    [UInt8] is; [Char.chr] raises [Invalid_argument] on any other. *)
