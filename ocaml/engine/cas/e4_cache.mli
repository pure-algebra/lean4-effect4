(* E4_cache — the bounded, address-keyed caches in front of the pack: node bytes, and a
   functor for decoded payloads.

   What it is: the memory between a reader and the pack file
   (docs/research/2026-09-08-engine-a2-persistence.md §1.10).  Both tiers are caches in the
   strict sense of L-IDX-0 — each states the identity it is derived from and the command that
   rebuilds it, and dropping the whole thing changes no answer of any query:

     bytes cache      identity: the pack (through `E4_cas.get_bytes`).   rebuild: `drop`, then
                      re-read.  The value cached under an address is `E4_node.encode` of the
                      node filed there, which is the string `sha256` of which IS the address.
     decoded cache    identity: the pack plus `V.decode`.                rebuild: `drop`, then
                      re-read and re-decode.

   Two tiers, both WEIGHT-bounded rather than count-bounded (the ecosystem survey's
   `~compute_size` observation, 2026-09-07-ocaml-ecosystem-survey.md:94: a cache of node bytes
   whose entries range from 40 bytes to a megabyte cannot be bounded by a count), and both
   CLOCK (second chance) rather than LRU: CLOCK touches one bit on a hit and allocates nothing,
   where an LRU either allocates a list node per touch or needs an intrusive array-based list
   of the same complexity for no benefit at these hit rates.  A2 §5.1 OQ6 rules that no cache
   lives inside a persistent value; nothing here is ever part of a machine state, and none of
   these types is persistent.

   The shape of one cache:

     slots        a fixed array of `slots` entries; a slot holds an address, a value, the
                  value's weight and one reference bit.  Allocated once, at `create`.
     key table    an open-addressed `Bigarray.int` table of `slot + 1` (0 = empty) at load
                  0.6, the same shape and the same load factor as `E4_index` (CA5), so the GC
                  never walks it.  Deletion is by BACKWARD SHIFT, not by a tombstone, so a
                  cache that has evicted a million entries probes exactly as fast as a fresh
                  one and the table can never fill with graves.
     free stack   the slots not in use, so admitting into a cache that is not full is O(1) and
                  never walks the clock hand.

   Depends on: E4_addr, E4_kind, E4_node, E4_cas (for the `get` that fills on a miss), bigarray.
   It reads no file of its own, writes none, and takes no lock.

   Behaviours:
   CA1 Identity.  `find c a = Some v` implies `E4_cas.get_bytes store a = Some v` for a bytes
       cache, and `V.decode (E4_node.decode (get_bytes store a)).payload = Some v` for a
       decoded one, for the store the cache was filled from.  Dropping the cache changes no
       answer of any query: `get` after `drop` answers exactly what it answered before.
                                                              by construction; tested (I1-I3)
   CA2 Bounded by WEIGHT.  `bytes c <= capacity_bytes c` after every operation, and
       `entries c <= slots c` after every operation.  An entry heavier than the whole capacity
       is never admitted — it is counted in `refusals` and served straight from the pack.
                                                              by construction; tested (B1-B4)
   CA3 Eviction is CLOCK.  Each slot carries a reference bit; `find` sets it on a hit; an
       admission that needs room advances the hand, clearing set bits and evicting the first
       slot it finds clear.  An entry enters with its bit CLEAR and earns it on its first hit,
       so an unread entry is evicted in FIFO order and a read one survives one more sweep —
       entering with the bit set would give every admission a free second chance and a hit
       would no longer be what buys survival.  A hit allocates nothing.
                                                              by construction; tested (E1, E2)
   CA4 `find` never changes membership, and `add` of a key already present replaces the value
       and leaves `entries` where it was — the weight moves by the difference of the two
       values' weights and by nothing else.                    by construction; tested (M1-M2)
   CA5 No unbounded growth anywhere.  The slot array is fixed at `create` and the key table is
       fixed with it; neither is ever grown, and no operation allocates a structure whose size
       depends on the number of operations performed.          by construction; tested (B3)
   CA6 A cache is never consulted for `verify`.  `E4_cas.verify` re-reads the pack and
       re-hashes it (e4_cas.mli CS7) and no function of this module is reachable from it: this
       module depends on `E4_cas` and not the other way round, which is the compiler's own
       statement of CA6.  The test that makes it visible poisons a cache with bytes that are
       not the node's and shows `verify` still answers `ok` and `E4_cas.get_bytes` still
       answers the pack's bytes.                               by construction; tested (V1-V3)
   CA7 Total: no function raises on any address, any value and any sequence of operations, and
       a capacity of 0 is a cache that admits nothing rather than an error.        tested (B4)
   CA8 `invariant` is the checker CA2/CA4/CA5 are tested through, and it is exported: the sum
       of the live weights is `bytes`, the number of occupied slots is `entries`, the key table
       holds exactly `entries` non-empty positions, and every occupied slot is reachable from
       the key table by its own address.                       by construction; tested (B1-B4)

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.10 (lane P7,
   2026-09-08).  Nothing named in §1.10 is missing or renamed.

   D1  §1.10 bounds a cache by bytes alone, and CA5 says "the slot array is fixed at `create`".
       Those two cannot both hold with `create ~capacity_bytes` as the only constructor: the
       number of slots a byte capacity buys depends on the size of the entries, which is not
       known at `create`.  `create ~capacity_bytes` therefore derives a slot count —
       `capacity_bytes / 1024`, clamped to [16, 1 lsl 20], the 1 KB node A2 §4.5's cells B1
       and B3 measure — and `create_sized ~slots ~capacity_bytes` names it.  The bound is
       then the CONJUNCTION `bytes <= capacity_bytes && entries <= slots`, and both halves are
       enforced by the same CLOCK eviction (CA2).  A workload of entries much smaller than
       1 KB hits the slot bound first and its capacity is `slots` entries, not
       `capacity_bytes` bytes; `stats.slot_bound_evictions` counts exactly how often that
       happened, so the tuning question is answered by a number and not by a guess.
   D2  `Decoded (V)`'s `get` in §1.10 takes an `E4_cas.ro`; `Bytes_cache` has no such function
       there, and every caller of the bytes tier needs one.  `Bytes_cache.get` is added with
       the same shape, and it is where CA1's "the identity is the pack" becomes executable.
   D3  Added beside §1.10's list: `create_sized` (D1), `mem` (a membership test that sets no
       reference bit and counts no hit — `find` may not be used for it, CA4), `bytes`,
       `entries`, `slots`, `capacity_bytes`, `reset_counters`, `invariant` (CA8), and the two
       counters `admissions` / `refusals` / `slot_bound_evictions` on `stats` (§1.10's record
       has hits, misses, evictions, bytes and entries; without the other three, CA2's "an
       entry larger than the capacity is never admitted" is not observable).
   D4  `drop` clears the contents and KEEPS the counters, because the drop-and-rebuild test of
       L-IDX-0 wants to compare the answers across a drop and the counters are the evidence
       that the second round really re-read.  `reset_counters` is separate.
   D5  §1.10's `VALUE.kind` is used: `Decoded.get` refuses a node whose kind is not `V.kind`
       (it answers None and counts a miss) rather than decoding a payload of another shape.
       §1.10 declares the field and says nothing about it. *)

(* ============================================================ the bytes tier *)

module Bytes_cache : sig
  type t

  type stats = {
    hits : int;  (** `find` / `get` calls answered from the cache *)
    misses : int;  (** `find` / `get` calls not answered from the cache *)
    evictions : int;  (** entries dropped to make room *)
    slot_bound_evictions : int;  (** of those, the ones forced by the slot bound, not by bytes (D1) *)
    admissions : int;  (** `add` calls that installed an entry *)
    refusals : int;  (** `add` calls refused because the value is heavier than the capacity (CA2) *)
    bytes : int;  (** the live weight; `<= capacity_bytes` (CA2) *)
    entries : int;  (** the live entries; `<= slots` (CA2) *)
    slots : int;
    capacity_bytes : int;
  }

  val create : capacity_bytes:int -> t
  (** §1.10's constructor; the slot count is derived (D1). *)

  val create_sized : slots:int -> capacity_bytes:int -> t
  (** Both bounds named (D1).  [slots] is at least 1. *)

  val find : t -> E4_addr.Addr.t -> string option
  (** CA1, CA3: a hit sets the slot's reference bit and allocates nothing. *)

  val mem : t -> E4_addr.Addr.t -> bool
  (** Membership without touching the reference bit and without counting a hit or a miss (D3). *)

  val add : t -> E4_addr.Addr.t -> string -> unit
  (** CA2, CA4.  A value longer than `capacity_bytes` is refused, not admitted. *)

  val get : t -> E4_cas.ro -> E4_addr.Addr.t -> string option
  (** [find], else `E4_cas.get_bytes` and admit (D2).  This is the function CA1 is about. *)

  val drop : t -> unit
  (** Throw every entry away; the counters survive (D4). *)

  val stats : t -> stats
  val reset_counters : t -> unit
  val bytes : t -> int
  val entries : t -> int
  val slots : t -> int
  val capacity_bytes : t -> int

  val invariant : t -> (unit, string) result
  (** CA8: the checker the property tests run after every operation. *)

  val hit_ratio : stats -> float
  (** hits / (hits + misses), or 0.0 when neither happened.  Bench cell B10 (A2 §4.5). *)
end

(* ============================================================ the decoded tier *)

module type VALUE = sig
  type t

  val kind : E4_kind.t
  (** The node kind whose payload this decoder reads (D5). *)

  val decode : string -> t option
  (** Over the node PAYLOAD, not the envelope. *)

  val weight : t -> int
  (** Bytes, for CA2.  It need not be exact; it must be non-negative and must not change for a
      value already in a cache. *)
end

module Decoded (V : VALUE) : sig
  type t

  val create : capacity_bytes:int -> t
  val create_sized : slots:int -> capacity_bytes:int -> t
  val find : t -> E4_addr.Addr.t -> V.t option
  val mem : t -> E4_addr.Addr.t -> bool
  val add : t -> E4_addr.Addr.t -> V.t -> unit

  val get : t -> E4_cas.ro -> E4_addr.Addr.t -> V.t option
  (** [find], else read the node, refuse it unless its kind is `V.kind` (D5), `V.decode` its
      payload, admit, answer. *)

  val drop : t -> unit
  val stats : t -> Bytes_cache.stats
  val reset_counters : t -> unit
  val bytes : t -> int
  val entries : t -> int
  val slots : t -> int
  val capacity_bytes : t -> int
  val invariant : t -> (unit, string) result
end

(* ============================================================ a ready instance *)

module Node_value : VALUE with type t = E4_node.t
(** The whole decoded node, weighed by its encoded length.  `kind` is `Program`; a caller that
    wants another kind writes three lines, which is the price §1.10 names for refusing `Obj`
    (ocaml/STANDARDS.md §4) and a heterogeneous decoded cache. *)

module Node_cache : sig
  type t

  val create : capacity_bytes:int -> t
  val create_sized : slots:int -> capacity_bytes:int -> t
  val find : t -> E4_addr.Addr.t -> E4_node.t option
  val mem : t -> E4_addr.Addr.t -> bool
  val add : t -> E4_addr.Addr.t -> E4_node.t -> unit

  val get : t -> E4_cas.ro -> E4_addr.Addr.t -> E4_node.t option
  (** Unlike `Decoded(Node_value).get`, this one accepts a node of ANY kind: the envelope
      decoder is total over kinds and there is nothing to refuse. *)

  val drop : t -> unit
  val stats : t -> Bytes_cache.stats
  val reset_counters : t -> unit
  val bytes : t -> int
  val entries : t -> int
  val slots : t -> int
  val capacity_bytes : t -> int
  val invariant : t -> (unit, string) result
end
