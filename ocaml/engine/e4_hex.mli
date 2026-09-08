(* E4_hex — the one hexadecimal codec, src/Effect4/Store/Digest.lean:62-93, :253-261.

   Depends on: the OCaml standard library only.

   Behaviours:
   H1  Lowercase out: `of_bytes` writes 0-9 then a-f (Digest.hexDigit, :63).
                                                                        by construction
   H2  Either case in: `to_bytes` reads 0-9, a-f and A-F (Digest.hexVal, :66-70).
                                                                        by construction
   H3  Round trip: `to_bytes (of_bytes b) = Some b`
       (Digest.bytesOfHexCodes_hexCodes).                               tested (property)
   H4  Exactness up to case: what decodes, re-printed, is the input lowercased
       (Digest.hexCodes_of_bytesOfHexCodes).                            tested (property)
   H5  Refusals, never repairs: an odd length, and any character outside the two ranges,
       are None (Digest.bytesOfHexCodes's [_] and fall-through arms).   tested
   H6  ASCII only: every digit is one byte, so a string's bytes are its code points
       (Digest.utf8Bytes_map_ofNat) -- this module never touches String.get_utf_8_uchar.
                                                                        by construction

   Pinned by Digest.lean's own #guards (:306-314), which are the tests:
   bytesOfHex ['f';'f';'0';'0'] = some [255,0], ['F';'F';'0';'a'] = some [255,10],
   ['g';'0'] = none, ['0'] = none, hexOfBytes [255,10] = ['f';'f';'0';'a'],
   Digest.ofHex? "E3B0…B855" = some (sha256 []), ofHex? "e3b0" = none, ofHex? "" = none.

   No deviation from docs/research/2026-09-08-engine-a1-state.md §3.3. *)

val of_bytes : string -> string
(** Lowercase, two characters per byte. *)

val to_bytes : string -> string option
(** None on an odd length or a non-digit.  Accepts either case. *)

val digest_of_hex : string -> string option
(** to_bytes, then exactly 32 bytes or None -- `Effect4.Store.Digest.ofHex?` (:257-261). *)
