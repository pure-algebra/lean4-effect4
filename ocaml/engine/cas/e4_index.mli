(* E4_index — digest -> (segment, offset, kind), off the OCaml heap; plus the two derived
   indexes the repository needs.

   What it is: the accelerator that turns an address into a place in the pack
   (docs/research/2026-09-08-engine-a2-persistence.md §1.6).  It is a CACHE, and L-IDX-0 is the
   rule every cache in that document obeys — each one states (a) the identity it is derived
   from, (b) the command that rebuilds it, (c) the test that a full drop and rebuild changes no
   answer:

     node index     identity: the pack files.  rebuild: `rebuild`, a 41-byte header scan.
     by-kind index  identity: the node index (or the pack).  rebuild: `By_kind.of_index`.
     dependents     identity: the pack read through `E4_shape.table`.  rebuild: a full scan.

   Deleting `index/` is always safe: A2 §6.5 measures a full rebuild of a 1 M-node store at
   2 507 235 nodes/s for the header scan, i.e. under half a second, which is what licenses "the
   index is a cache, never identity" as an operational statement rather than a slogan.

   The table is two `Bigarray.int` arrays, 16 bytes a slot.  A2 §6.4 measured 1 M entries at
   load 0.5 -> 2 097 152 slots -> 32.0 MB off-heap, `live_words +14`, 17 698 232 lookups/s,
   against `Hashtbl` with 32-byte string keys at 77.0 MB, +10 097 160 live words and
   6 425 100 lookups/s.  The point is not only the 2.75x: it is that the GC never walks a
   Bigarray, so the index of a large store never joins the major heap.

     keys.(j) : E4_addr.Addr.prefix63 -- the digest's leading 62 bits (e4_addr.mli D1)
     vals.(j) : seg  (bits 51..61, 11 bits, 2048 segments)
              | off  (bits  8..50, 43 bits, 8 TiB per segment)
              | kind (bits  0..7)
                vals.(j) = 0 means EMPTY, and no occupied slot can be 0 because
                `Kind.byte_pos` (Kind.lean:137) proves every kind byte is at least 1.

   A prefix collision is not a correctness problem: `find` CONFIRMS by reading the record's own
   recorded digest at the offset (41 bytes, which the reader touches anyway) and keeps probing
   when the confirmation fails.  That is L-IDX-1, and it is why a 62-bit key is enough.

   The on-disk snapshot (`index/NNNNNN.idx`) is a dump of the two arrays plus the pack watermark
   it was built at:

     idxfile := "E4IDX\000" 6 ++ "00000001" 8 ++ be64 covers_seg 8 ++ be64 covers_off 8
                ++ be64 slots 8 ++ be64 count 8 ++ be32 head_crc 4     (50 bytes)
                ++ keys slots*8 ++ vals slots*8                        (little-endian words)
                ++ be32 body_crc 4

   It is byte-order- and word-size-dependent on purpose: it is a cache, never transferred, never
   hashed, and discarded and rebuilt whenever anything about it fails to match (`load_verdict`).

   Depends on: E4_pack, E4_addr, E4_kind, E4_node, E4_shape, E4_crc, E4_be, unix, bigarray
   (in-stdlib since 4.07; no findlib package and none needed).

   Behaviours:
   IX1 `find ~confirm i a = Some e` implies the record at (e.seg, e.off) has RECORDED digest `a`
       and kind `e.kind`.  A 62-bit prefix collision costs a read and never a wrong answer:
       `find` keeps probing past a slot whose key matches but whose record does not.
                                                                  by construction; tested (C1-C3)
   IX2 `rebuild` from a pack produces an index for which `find` agrees with a linear scan on
       every resident digest, and answers None for every digest not in the pack.  tested (R1-R3)
   IX3 Off-heap: the table lives in two Bigarrays and `Gc.stat().live_words` after a build is
       within 64 words of before.                                             tested (H1)
   IX4 The load factor never exceeds `max_load` (0.6); growth doubles the slot count and
       rehashes, and no entry is lost or duplicated by a growth.   by construction; tested (G1)
   IX5 Interior kinds (Chunk) may be indexed in a SEPARATE table which can be dropped
       independently (ecosystem survey #20: index only what a client names by digest).  Our
       value nodes are flat (cas-design §2), so one table covers every kind and that costs
       nothing; `By_kind` is how a caller separates them after the fact.       by construction
   IX6 The index file is a cache and is never trusted: a missing file, a bad magic, an ASCII
       version this binary does not know, a failed head or body CRC, a slot count that is not a
       power of two, a count above the slot count, a body of the wrong length, and a `covers`
       that is not the pack's durable end are ALL `load_verdict`s that discard the file and
       rebuild.  Nothing is repaired.                             by construction; tested (F1-F6)
   IX7 Grow-only, like the pack: nothing is ever removed from the table.  `add` of an
       (address, entry) pair already present in the probe chain is idempotent; two DIFFERENT
       entries whose keys collide both occupy slots and `find` returns the first in probe order
       that confirms.                                             by construction; tested (C3)
   IX8 `Deps` is NOT an edge (amendment M1): `E4_cas.reachable`, `closure` and admission never
       consult it, and there is no `propagate` (companion §7 and `exists_carrier_collision`,
       Key.lean:383-386).  It is persistent: `add` returns a new value.        by construction
   IX9 `Deps.rebuild` agrees with `Deps.of_node` applied to every node of the pack, and
       `Deps.of_node` is `E4_node.checked_edges` (the Ref edges, exactly, with no table) plus
       `E4_shape.cids_of` (the Cid fields, only through the table).  The two halves are named
       apart because the first is exact and the second is transcribed (E4_shape finding R1).
                                                                              tested (D1-D3)

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.6 (lane P2, 2026-09-08):
   D1  §1.6 assigns `seg` to bits 52..62.  Bit 62 is the sign bit of an OCaml int, so a segment
       index of 1024 or more would make `vals.(j)` negative -- storable in a `Bigarray.int`, but
       a trap for the next reader and a hazard for the `vals = 0` empty marker's argument.  The
       same 16-byte slot is kept, `seg` keeps its 11 bits at 51..61, and `off` is narrowed from
       44 to 43 bits.  Reach is unchanged in practice: 2048 segments of 8 TiB against a
       `seg_max` of 1 GiB.  `max_seg` and `max_off` are exported so a caller can check.
   D2  §1.6's `entry` has no length, and the lane brief asks for `(offset, len, kind)`.  The
       length cannot join the slot: 11 + 43 + 8 already fills the 62 bits an OCaml int gives,
       and a third array would take the index to 24 bytes a slot -- 48 bytes per node at load
       0.5, past A2 §4.5 B5's acceptance of 40.  The length is therefore READ, not stored:
       `find_full` returns it from the same 41-byte header the confirmation already reads, so it
       costs nothing extra.
   D3  §1.6's `find` and `mem` take no confirmation, yet IX1 requires one.  `find` therefore
       takes `~confirm`; `find_in` is the same over an `E4_pack.reader` (the usual caller) and
       `find_unconfirmed` is the prefix-only form, named so that nobody reaches it by accident.
   D4  §1.6's `iter` passes `E4_addr.Addr.t option` and would always pass None, since the table
       holds 62 bits of the address and not the address.  It passes the 62-bit key instead, and
       says so in its type.
   D5  §1.6's `rebuild` gets the kind from `E4_pack.scan`, which does not carry one: a scan
       reads the 41-byte header and the kind is the second byte of `node_bytes`.  `rebuild`
       therefore takes `?kind_at`, defaulting to `E4_pack.read_at` -- the O(bytes) form.  A
       caller that has a cheaper probe (lane P4 holds the mmap) passes it.  The cost is measured
       in `bench_index` and reported in the receipt, not assumed.
   D6  Added beside §1.6's list: `with_capacity` (the lane brief's `create ~capacity`),
       `cardinal` (= `count`), `add_at`, `find_full`, `mem_in`, `stats`, `bytes`,
       `heap_live_words`, `from_start`, `load_verdict` with `load_at` and `open_index`
       (§1.6 says a stale or corrupt file is discarded and rebuilt but gives no function that
       does it), `max_load`, `max_seg`, `max_off`, `slot_bytes`, and the whole `By_kind` module
       (§1.6 names the by-kind index in its header and gives it no signature).
   D7  `Deps.rebuild` and `By_kind.rebuild` return the scan verdict beside the index; §1.6's
       `Deps.rebuild` returns the index alone, which would hide a truncated pack. *)

type t

type index = t
(** An alias, so the sub-modules below can name the node index after shadowing `t`. *)

type seg = int
type off = int

type entry = { seg : seg; off : off; kind : E4_kind.t }

(* ---- the shape of a slot, as constants (D1) ---- *)

(* slot_bytes 16 (two Bigarray.int words); max_seg 2047; max_off 2^43-1; max_load 0.6 (IX4);
   min_slots 16. *)

val slot_bytes : int
val max_seg : int
val max_off : int
val max_load : float
val min_slots : int

(* ---- the file, as constants: the magic, the ASCII version matched as a string, and the
   50-byte head ---- *)

val magic : string
val version : string
val head_length : int

val from_start : seg * off
(** `(0, E4_pack.head_length)` — where the first record of a store's segment 0 lives, and the
    `~from` a full rebuild uses. *)

(* ---- building ---- *)

val create : slots:int -> t
(** [slots] is rounded UP to a power of two, at least [min_slots]. *)

val with_capacity : capacity:int -> t
(** Slots for [capacity] entries at load 0.5 — the lane brief's `create ~capacity`. *)

val add : t -> E4_addr.Addr.t -> entry -> unit
(** IX4, IX7.  Invalid_argument if `seg > max_seg` or `off > max_off` or `off < 0`. *)

val add_at : t -> E4_addr.Addr.t -> seg:seg -> off:off -> kind:E4_kind.t -> unit

(* ---- looking up ---- *)

type confirm = seg:seg -> off:off -> E4_addr.Addr.t option
(** The RECORDED digest of the record at that place, or None.  `E4_pack.read_header` is the
    41-byte implementation and `confirm_of_reader` wraps it. *)

val confirm_of_reader : E4_pack.reader -> confirm

val find : confirm:confirm -> t -> E4_addr.Addr.t -> entry option
(** IX1: probes, confirms at the record, and keeps probing past a prefix collision. *)

val find_in : E4_pack.reader -> t -> E4_addr.Addr.t -> entry option
(** [find ~confirm:(confirm_of_reader rd)]. *)

val find_full : E4_pack.reader -> t -> E4_addr.Addr.t -> (entry * int) option
(** The entry and the record's `node_len`, from the same header the confirmation reads (D2). *)

val find_unconfirmed : t -> E4_addr.Addr.t -> entry option
(** The first slot whose 62-bit key matches, with NO confirmation.  It may be a collision and it
    may be wrong; it exists for the bench and for a caller that is about to read the record for
    other reasons.  Never use it to answer `mem` (D3). *)

val mem : confirm:confirm -> t -> E4_addr.Addr.t -> bool
val mem_in : E4_pack.reader -> t -> E4_addr.Addr.t -> bool

(* [cardinal] is [count]; [bytes] is `slots * slot_bytes`, all of it off the OCaml heap. *)

val count : t -> int
val cardinal : t -> int
val slots : t -> int
val bytes : t -> int
val load_factor : t -> float

val iter : t -> (int -> entry -> unit) -> unit
(** Every occupied slot, in slot order, as `key entry` where `key` is the 62-bit prefix (D4). *)

type stats = {
  s_entries : int;
  s_slots : int;
  s_bytes : int;
  s_growths : int;  (** rehashes since `create` *)
  s_max_probe : int;  (** the longest probe an `add` walked *)
  s_confirms : int;  (** confirmations attempted by `find` *)
  s_confirm_misses : int;  (** confirmations that failed — prefix collisions paid for (IX1) *)
}

val stats : t -> stats
val reset_counters : t -> unit

val heap_live_words : unit -> int
(** `Gc.compact (); (Gc.stat ()).live_words` — what IX3 and bench cell B5 measure. *)

(* ---- rebuilding from the pack (the identity) ---- *)

type kind_at = E4_pack.reader -> seg:seg -> off:off -> E4_kind.t option

val kind_at_default : kind_at
(** Reads the record through `E4_pack.read_at` and takes `node_bytes.[1]` (D5).  O(bytes): it
    pays a CRC over the whole record for one byte.  Measured 864 661 nodes/s on a 1 M-node pack
    of 256-byte nodes, against 3 453 301 nodes/s for the header scan alone. *)

val kind_at_of_dir : dir:string -> kind_at
(** The fast probe (D5): one byte at `E4_pack.record_header_length + 1` into the record, out of
    a private read-only mapping of the segment file, using `E4_pack.seg_path` and the two
    exported constants and reimplementing no reader.  Measured 3 336 837 nodes/s on the same
    pack, i.e. within 1.7% of the header scan alone (3 393 200).  It is exactly as trusting as the non-verifying scan it runs beside (neither checks a
    CRC), and it does not see bytes appended after the closure first mapped a segment — so it is
    for a rebuild to a fixed `pack_end` and for nothing else. *)

val rebuild :
  ?kind_at:kind_at -> E4_pack.reader -> from:seg * off -> t -> E4_pack.scan_stop
(** IX2.  Adds every record from [from] in write order; grows as needed. *)

val of_pack :
  ?kind_at:kind_at ->
  ?dir:string ->
  ?capacity:int ->
  E4_pack.reader ->
  from:seg * off ->
  t * E4_pack.scan_stop
(** [dir] is the store directory; giving it selects `kind_at_of_dir` over `kind_at_default`,
    which is a 3.9x rebuild (measured, bench_index R1/R1b).  An explicit [kind_at] wins over
    both. *)

(* ---- the file: save, load, and the discard-and-rebuild rule (IX6) ---- *)

val save : path:string -> t -> covers:seg * off -> unit
(** tmp + rename + fsync of the file and of its directory. *)

type load_verdict =
  | Loaded
  | No_file
  | Bad_file of string  (** magic, version, a CRC, a length, a slot count *)
  | Stale of { covers : seg * off; pack_end : seg * off }

val load_verdict_to_string : load_verdict -> string

val load : path:string -> (t * (seg * off)) option
(** §1.6's form: the table and what it covers, or None for every refusal. *)

val load_at : path:string -> pack_end:seg * off -> (t, load_verdict) result
(** [load] plus the staleness test against the pack's durable end (IX6). *)

val open_index :
  ?kind_at:kind_at ->
  ?dir:string ->
  path:string ->
  E4_pack.reader ->
  pack_end:seg * off ->
  t * load_verdict * E4_pack.scan_stop option
(** [load_at], else create and `rebuild` from [from_start].  The verdict says which happened and
    why; the scan stop is present exactly when a rebuild ran.  [dir] as in [of_pack]. *)

(* ============================================================ the by-kind index *)

module By_kind : sig
  (** Identity: the node index, or the pack.  Rebuild: `of_index`, or `rebuild`.
      Places, not addresses: the table holds 62 bits of an address and not the address, so a
      caller that wants the digest reads the record at the place this answers (D4). *)

  type t

  val create : unit -> t
  val add : t -> E4_kind.t -> seg:seg -> off:off -> unit
  (* [find] answers in insertion order; [kinds] lists those with at least one entry, in byte
     order; [bytes] is the off-heap bytes held. *)

  val find : t -> E4_kind.t -> (seg * off) list
  val count : t -> E4_kind.t -> int
  val cardinal : t -> int
  val kinds : t -> E4_kind.t list
  val bytes : t -> int

  val of_index : index -> t
  (** From the node index alone: it already carries a kind per entry. *)

  val rebuild :
    ?kind_at:kind_at -> E4_pack.reader -> from:seg * off -> t * E4_pack.scan_stop
end

(* ============================================================ the dependents index *)

module Deps : sig
  (** Identity: the pack read through `E4_shape.table`.  Rebuild: a full scan.  It is NOT an
      edge (IX8, amendment M1) and there is no `propagate`: a row-preserving edit is not a
      meaning-preserving edit here, because `exists_carrier_collision` (Key.lean:383-386) says
      type identity never recovers code identity. *)

  type t

  (* [cardinal] counts distinct dependees; [edges] counts (dependee, dependent) pairs. *)

  val empty : t
  val cardinal : t -> int
  val edges : t -> int

  val add : t -> dep:E4_addr.Addr.t -> by:E4_addr.Ref.t -> t
  (** Persistent (IX8).  Idempotent on a pair already present, and the idempotence test is
      O(log k) in the number k of dependents that dependee already has: a `Set` of the same
      `Ref`s is held beside the list, which is kept because `find`/`iter` owe DISCOVERY
      ORDER.  It was a `List.exists` over the list, which made a build over a hub dependee
      quadratic (lane P7 finding F1, 2026-09-08-engine-lane-w-delivery.md item 1). *)

  val of_node : fields:E4_shape.t -> E4_node.t -> E4_addr.Addr.t list
  (** The dependees of one node, in order: `E4_node.checked_edges`' addresses (exact, no table)
      then `E4_shape.cids_of` (the table's Cid fields).  This is the SPECIFICATION the
      brute-force test recomputes (IX9). *)

  val add_node : t -> fields:E4_shape.t -> at:E4_addr.Addr.t -> E4_node.t -> t

  (* [find] answers in discovery order. *)

  val find : t -> E4_addr.Addr.t -> E4_addr.Ref.t list
  val mem : t -> E4_addr.Addr.t -> bool
  val iter : t -> (E4_addr.Addr.t -> E4_addr.Ref.t list -> unit) -> unit

  val rebuild :
    ?fields:E4_shape.t -> E4_pack.reader -> from:seg * off -> t * E4_pack.scan_stop
  (** A full scan: every record's node bytes are decoded, so this is O(bytes) by construction —
      it has to be, since a Cid is only a Cid through the table (E4_shape finding R1).  A record
      whose bytes do not decode contributes nothing and does not stop the scan; the scan stops
      only where `E4_pack.scan` stops. *)
end
