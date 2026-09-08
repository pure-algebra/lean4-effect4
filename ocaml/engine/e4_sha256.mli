(* E4_sha256 — SHA-256 (FIPS 180-4) in pure OCaml.

   What it is: the one hash of the content address.  `Effect4.Store.sha256`
   (src/Effect4/Store/Digest.lean:57) is lean4-hash's `Hash.Sha256.sha256`; OCaml's stdlib
   ships MD5 only (Digest), so this module is the OCaml side of that address.  A digest is
   an address and no security property is claimed (Digest.lean header).

   Depends on: the OCaml standard library only (Bytes, String) and E4_hex.

   Behaviours:
   S1  FIPS 180-4 test vectors: "" , "abc", the 56-byte and 112-byte NIST messages, and
       one million 'a' -- the last as a streamed feed.                            tested
   S2  Lean agreement: the three digests src/Effect4/Store/Digest.lean #guards
       (`sha256 [] = e3b0c442…` :302, `sha256 [0xb4,0x19,0x0e] = dff2e730…` :303,
       `sha256 (Val.encode sampleEntry) = 8fab1618…` :315) are reproduced byte for byte.
       The third input is built in the test out of E4_be frames from
       `sampleEntry = .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1947]`
       (src/Effect4/Store/Val.lean:1150-1155), so the vector also pins E4_be.      tested
   S3  Streaming equals one-shot: for every split of a byte string, feeding the parts
       through `update` and `finish` equals `digest` of the whole.        tested (property)
   S4  Length: `digest` is always 32 bytes; `hex` is always 64 lowercase characters.
                                                                         by construction
   S5  Endianness and padding are the standard's: big-endian words, the 0x80 pad byte, the
       64-bit big-endian bit length.  Messages above 2^61 - 1 bytes cannot exist on this
       host (E4_nat.N4), so the length field never overflows.             by construction
   S6  No allocation per block beyond the 64-word schedule: `update` writes into a
       preallocated int array, and a run of whole blocks is compressed straight out of the
       caller's string with no copy.  The Bytes/int-array buffer is step-local and never
       enters a snapshot (brief §2.3).                                    by construction

   Deviation from docs/research/2026-09-08-engine-a1-state.md §3.2 (lane M, 2026-09-08):
   D1  `finish` raises Invalid_argument if a context is updated or finished twice, rather
       than answering an undefined digest.  The .mli said only "unusable afterwards".
                                                                                  tested *)

type ctx
(** A streaming context.  Mutable and step-local: never store one in a machine value. *)

val create : unit -> ctx

val update : ctx -> string -> int -> int -> unit
(** [update c s pos len] feeds s.[pos .. pos+len-1].
    Raises Invalid_argument on an out-of-range window or a finished context. *)

val update_string : ctx -> string -> unit

val finish : ctx -> string
(** The 32 raw digest bytes.  The context is unusable afterwards: a second call, or an
    update after it, raises Invalid_argument. *)

val digest : string -> string
(** One-shot: 32 raw bytes. *)

val digest_sub : string -> int -> int -> string
(** One-shot over a window: 32 raw bytes. *)

val hex : string -> string
(** [hex s] is [E4_hex.of_bytes (digest s)]: 64 lowercase hex characters, exactly
    `Effect4.Store.Digest.hex` of `Effect4.Store.sha256` of the same bytes. *)

val digest_length : int   (* 32 *)
val block_length : int    (* 64 *)
