(* E4_addr — the two pointer classes: the identity that reaches disk, and the repo-local
   accelerator that never does.

   What it is: `Addr` is `Store.Digest` (src/Effect4/Store/Digest.lean:35-37) — thirty-two
   bytes, the SHA-256 of a node's canonical bytes, the only thing that is ever encoded, hashed,
   named in a root, or carried across a process.  `Ref` is `Store.AnyRef`
   (src/Effect4/Store/Node.lean:71-74): an address with the kind byte its target must file
   under.  `Cid` is the payload digest, kind-free (amendment M6).  `Handle` is the repository's
   private accelerator — where a node's bytes sit in this process's pack — and it is NOT an
   address: it never reaches a byte anyone else reads.  Survey #5 / proposal 23; Irmin's
   `key` vs `hash` (indexable_intf.ml, unix/pack_key_intf.ml) is the same split.

   Depends on: E4_kind, E4_hex (ocaml/engine, lane M).  This module writes no hex codec of its
   own and no second digest.

   Behaviours:
   AD1 `Addr.t` is exactly 32 bytes; `of_digest` refuses anything else with Invalid_argument
       and `of_digest_opt` with None.  It mirrors `Store.Digest`, whose length is carried in
       the type (Digest.lean:35-37).                             by construction; tested
   AD2 `Addr.hex` and `Addr.of_hex` FORWARD to E4_hex (`of_bytes`, `digest_of_hex`); lowercase
       out, either case in, exactly `Digest.hex` / `Digest.ofHex?` (Digest.lean:252-259,
       amendment M8).                                            by construction; tested
   AD3 A `Handle` is never encoded, never compared by offset, never crosses a process boundary
       and has no inverse: `Handle.addr` is total, and there is no `Handle.of_addr`, no
       `encode`, no `decode`, no `compare`.                       by construction (the
       signature omits them)
   AD4 Presentation is `<kind>:<hex>` for a Ref and `<kind>:cid:<hex>` for a Cid (amendment M6,
       cas-design §3); `Ref.parse (Ref.present r) = Some r` and
       `Cid.parse (Cid.present k c) = Some (k, c)`, and each parser refuses the other's form,
       an unregistered kind name, a wrong-length hex string and a non-hex character.  tested
   AD5 `Addr.zero` is `zeroDigest` (Node.lean:276): thirty-two zero bytes, the spec of the
       genesis and of nothing else.                                          by construction
   AD6 `Addr.prefix63` is a pure function of the leading bytes, always in 0 .. 2^62-1, and
       equal for two addresses iff their leading 62 bits are equal.  It is an index key and
       never an identity: `E4_index.find` confirms at the record (L-IDX-1).  tested

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.5 (lane P0, 2026-09-08):
   D1  `prefix63` returns the leading **62** bits, not 63.  A2 wrote "the leading 8 bytes, top
       bit cleared", which is a value in 0 .. 2^63-1; an OCaml int on this host holds
       -2^62 .. 2^62-1 (`E4_nat.max_nat`), so no such value is representable as a
       non-negative int.  Rather than let the key go negative — A2's index stores keys in a
       `Bigarray.int`, which would carry a negative fine, but `Addr.prefix63`'s type says
       nothing about it and a signed key is a trap for the next reader — this lane keeps the
       name and narrows the width by one bit.  The consequence is one bit of collision
       probability: A2's ~1e-7 over 1 M entries becomes ~2e-7, and a collision still costs a
       read and never a wrong answer (IX1).
   D2  `Ref.equal` and `Ref.compare`, `Cid.equal`, and `Addr.of_digest_opt`'s partner
       `Addr.length` are added; nothing named in §1.5 is missing. *)

module Addr : sig
  type t

  val length : int
  (** 32. *)

  val of_digest : string -> t
  (** Invalid_argument unless the string is exactly 32 bytes (AD1). *)

  val of_digest_opt : string -> t option

  val bytes : t -> string
  (** The 32 raw bytes. *)

  val hex : t -> string
  (** = E4_hex.of_bytes (bytes t): 64 lowercase characters (AD2). *)

  val of_hex : string -> t option
  (** = E4_hex.digest_of_hex: either case, exactly 64 characters (AD2). *)

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val prefix63 : t -> int
  (** The leading 62 bits, as a non-negative int; an index key, never an identity (AD6, D1). *)

  val zero : t
  (** zeroDigest — thirty-two zero bytes (Node.lean:276) (AD5). *)
end

module Ref : sig
  type t = { kind : E4_kind.t; addr : Addr.t }
  (** Store.AnyRef (src/Effect4/Store/Node.lean:71-74). *)

  val make : E4_kind.t -> Addr.t -> t

  val present : t -> string
  (** "<kind>:<hex>" (AD4). *)

  val parse : string -> t option
  (** Refuses the Cid form (AD4). *)

  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module Cid : sig
  type t = Addr.t
  (** The payload digest; kind-free (amendment M6). *)

  val present : E4_kind.t -> t -> string
  (** "<kind>:cid:<hex>" (AD4). *)

  val parse : string -> (E4_kind.t * t) option
  (** Refuses the Ref form (AD4). *)

  val equal : t -> t -> bool
end

module Handle : sig
  type t = private
    | Direct of { addr : Addr.t; seg : int; off : int; len : int }
    | Located of Addr.t

  val direct : addr:Addr.t -> seg:int -> off:int -> len:int -> t
  val located : Addr.t -> t
  val addr : t -> Addr.t
  (** Total (AD3). *)

  (* Deliberately absent, and this is the point of the module: encode, decode, of_string,
     to_string, compare, equal, hash, of_addr. *)
end
