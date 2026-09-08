(* E4_crc — the checksum of every framed record in the CAS, and its four-byte field.

   What it is: CRC-32 as the pack file, the control file and the WAL use it
   (docs/research/2026-09-08-engine-a2-persistence.md §1.2 `be32 rec_crc` / `be32 head_crc`,
   §1.3 `be32 checksum`, §1.4 `be32 row_crc`).  A checksum here detects a torn or flipped
   byte; it is NEVER an identity — the identity of a node is `E4_sha256` of its canonical
   bytes (brief §2.2), and the record's recorded digest is itself only a cache of that
   (L-CAS-6).  Nothing checksummed by this module is ever hashed by it.

   Which polynomial, and why: A2 names the field `CRC-32` and fixes no polynomial, so this
   lane takes the brief's default — **IEEE 802.3, reflected: 0xEDB88320**, initial register
   0xFFFFFFFF, final xor 0xFFFFFFFF, least-significant bit first.  That is zlib's `crc32`,
   Ethernet's FCS, gzip's and PNG's; it is the one every operator tool on the machine already
   computes, which is the whole argument for choosing it (`python3 -c "import zlib"`,
   `cksum` and `crc32` all agree with the vectors in C1).

   Depends on: the OCaml standard library only.

   Behaviours:
   C1  The standard vectors: crc "" = 0x00000000, crc "123456789" = 0xCBF43926,
       crc "a" = 0xE8B7BE43, crc "abc" = 0x352441C2, and crc of the 43-byte pangram
       "The quick brown fox jumps over the lazy dog" = 0x414FA339.          tested
   C2  Composition: the value carried between calls is the finished crc of the prefix, so
       `update (update init a) b = string (a ^ b)` for every split of every string, and
       `init = string ""`.  There is no separate `finish`.       by construction; tested
   C3  Range: every result is in 0 .. 0xFFFFFFFF and never negative; a `crc` argument
       outside that range is Invalid_argument, never a silent wrap.  by construction; tested
   C4  Windows: `sub s pos len` = `string (String.sub s pos len)` and `update_sub` refuses a
       window outside the string with Invalid_argument.                     tested
   C5  The field: `be32` writes the four big-endian bytes the grammars of §1.2-§1.4 name and
       `read_be32` reads them back; `read_be32` is total (None past the end, never an
       exception).                                              by construction; tested

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md (lane P0, 2026-09-08):
   D1  A2 gives no `e4_crc.mli`: it names the module in three `Depends on:` lines and fixes
       the field width, nothing else.  This interface is therefore this lane's, written to
       the brief's default polynomial; the choice is recorded above so a later lane can see
       what it must not change (a stored pack is unreadable if it moves).
   D2  `be32` / `read_be32` / `field_length` live here rather than in A1's `E4_be`.  E4_be
       carries be64 only (`e4_be.mli:55-83`) and this lane owns no file in `ocaml/engine/`;
       the only be32 in the whole CAS grammar is a checksum or a length beside one, so the
       field travels with the checksum that fills it. *)

val poly : int
(** 0xEDB88320 — the reflected IEEE 802.3 polynomial this module is built from. *)

val init : int
(** 0: the crc of the empty string, and the seed of an incremental run (C2). *)

val string : string -> int
(** The crc of a whole string. *)

val sub : string -> int -> int -> int
(** [sub s pos len] is the crc of that window (C4).  Invalid_argument if out of range. *)

val update : int -> string -> int
(** [update crc s] extends a running crc by every byte of [s] (C2). *)

val update_sub : int -> string -> int -> int -> int
(** [update_sub crc s pos len] extends a running crc by that window (C2, C4). *)

val update_char : int -> char -> int
(** One byte. *)

val be32 : int -> string
(** Four big-endian bytes.  Invalid_argument outside 0 .. 0xFFFFFFFF (C5). *)

val read_be32 : string -> int -> int option
(** Four big-endian bytes at a position, or None past the end.  Total (C5). *)

val field_length : int
(** 4: the bytes a `be32` checksum field occupies. *)
