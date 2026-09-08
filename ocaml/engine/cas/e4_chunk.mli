(* E4_chunk — content-defined chunking of a machine image, and the two-level manifest.

   What it is: the only mechanism by which two consecutive checkpoints share bytes.  A
   run-relative payload is flat by amendment M2, so nothing is shared unless the image is
   split into `chunk` (kind 10) nodes whose digests dedup in the store's own `Duplicate`
   outcome (E4_cas CS1/L-CAS-5).  Cutting is CONTENT-DEFINED so that an insertion does not
   invalidate the tail: A2 §6.3 measured fixed-size chunking at 33 554 439 B for a 7-byte
   insertion in a 64 MB image against 91 490 B for content-defined chunking at a 16 KB
   average, so fixed-size chunking is refused (A2 §4.4, owner question OQ2).

   The rolling hash is a GEAR hash, stated so nobody has to guess:

     gear.(c) = the leading SEVEN bytes of sha256 ("e4.chunk.gear.v0:" ++ c), big-endian,
                masked to 62 bits — a fixed table of 256 constants, derived and never typed
                out, so it is reproducible from this line alone.
     h_0      = 0                     at every chunk start
     h_{i+1}  = ((h_i lsl 1) lxor gear.(byte_i)) land (2^62 - 1)
     mask     = ((1 lsl b) - 1) lsl (62 - b)   for b = log2 avg — the TOP b bits
     a cut is taken after byte i when  i - start >= min  and  h_{i+1} land mask = 0
     and is forced at  start + max  when no such i exists.

   Three facts about that recurrence carry the whole design.  (a) `lxor`, not `lor`: A2 §6.3's
   methodological note records that `(h lsl 1) lor byte` saturates to all-ones and never cuts,
   which made the first probe report content-defined chunking failing exactly as fixed-size
   chunking does.  (b) `h lsl 1` under a 62-bit mask forgets a byte after 62 steps, so h at an
   absolute position depends only on the preceding 62 bytes — which is why resetting h at each
   chunk start costs nothing and why CH6 below holds.  (c) THE MASK IS AT THE TOP OF THE WORD.
   Bit j of h depends on the last j+1 bytes, so a mask over the LOW b bits makes the cut a
   function of the last b bytes alone; this lane measured that at b = 10 on a period-90
   synthetic image, where the candidate density became 1/90 instead of 1/1024, every cut was
   min-forced, and a one-byte insertion re-phased the whole downstream lattice (1998 of 3504
   chunks rewritten).  With the mask at bits 62-b .. 61 every mask bit depends on 49..62
   preceding bytes and the same measurement gives 1.

   It is NOT a digest and is never an identity (CH5): the chunk's address is `E4_node.address`
   of its node, which is SHA-256 of Lean's canonical bytes and nothing else (brief §2.2).

   Depends on: E4_cas, E4_node, E4_addr, E4_kind, E4_be, E4_sha256 (ocaml/engine, lane M),
   Eff_frame (ocaml/eff, read-only).

   ============================================================================
   The byte grammar of a manifest node (kind 12, `manifest`).  It is ONE `Val` frame tree in
   the same framing every other payload uses (`E4_be.framed`, Eff_frame's tag alphabet), so
   `E4_node.refs` finds every child by the ordinary edge scan and nothing here is a second
   encoding:

     manifest payload := ctor 0 [ list [ ref chunk    … ] ]   a LEAF     level 0
                       | ctor 1 [ list [ ref manifest … ] ]   an INTERIOR level n+1

     ctor  := tag 10, be64 len, [ nat index ] ++ args        Eff_frame.tag_ctor
     list  := tag  4, be64 len, frames                       Eff_frame.tag_list
     ref   := tag 11, be64 33, kind byte ++ 32-byte address   Eff_frame.tag_ref

   A chunk node (kind 10, `chunk`) is `bytes` and nothing else:

     chunk payload    := tag 8, be64 len, the chunk's bytes   Eff_frame.tag_bytes

   Every node this module files carries the caller's `~spec` as its schema edge (edge 0), which
   `E4_cas` checks like any other edge: the spec must already name a resident `schema` node.
   `E4_checkpoint.ensure_schema` is what mints one today, and it is marked pending until CAS
   commit 7 blesses the run-relative shapes (risk R6).

   ============================================================================
   Behaviours:
   CH1 Cutting is a function of the bytes alone: `cut p s` depends on `p` and `s` and on
       nothing else — no clock, no store, no order of previous calls — so two images with a
       common region produce common chunks, and
       `concat (map (piece s) (cut p s)) = s` exactly.      by construction; tested (P5)
   CH2 Every chunk is at least `min` and at most `max` bytes; the LAST may be shorter, and a
       chunk is never empty.                                by construction; tested
   CH3 A chunk node is an INTERIOR node (`E4_kind.is_interior Chunk`): it is content the
       manifest names and never something a client names by digest itself.    by construction
   CH4 `reassemble store refs = Some image` iff every chunk is resident, decodes as a `bytes`
       payload and is filed at kind `chunk`; otherwise `None`.               tested (P5)
   CH5 The rolling hash is not an identity: it never leaves this module, is never stored,
       never compared against a digest and never framed.                     by construction
   CH6 ONE-BYTE EDIT LAW.  Insert or delete one byte at offset `k` of `s`, giving `s'`.
       (a) EXACT: every boundary of `cut p s` at an offset <= k is a boundary of `cut p s'`.
       A cut position is a function of the bytes strictly before it, so nothing at or before
       the edit can move.                                                    by construction
       (b) LOCAL: the cut resynchronises within a bounded neighbourhood of the edit.  h
       forgets a byte after `window` < `min` steps, so a candidate position is a function of
       its own preceding 62 bytes and the candidate lattice after the edit is the old one
       shifted by the edit; the chunk covering the edit is rewritten and the rest is
       byte-identical.  The ONE way the effect carries further is the `min`/`max` constraint:
       when the edit destroys the candidate that was the chunk's end, the chunk runs on to the
       next candidate, which the old cut may have skipped, and the lattice takes a chunk or
       two to re-coincide.  MEASURED, 200 one-byte insertions into a 1 MB record image at
       avg 1 KB / min 256 / max 4 KB: boundaries moved 1 in 197 trials, 2 in 2, 3 in 1; chunks
       rewritten at most 3 — against 999 of 1000 for fixed-size 1 KB chunking.  The law is
       therefore "local, at most three", not "at most two".        tested (prop-chunk-shift)
   CH6' The adversarial case, stated because it is real AND because the machine image is an
       instance of it.  On content with few DISTINCT byte windows — the test uses a filler of
       period 90; a rendered trace of a thousand near-identical rows is the same thing — a
       rolling hash has only that many chances to find a boundary however wide its window is,
       so most cuts become min- or max-forced (position-determined, not content-determined)
       and an edit re-phases the lattice for a while.  Measured on the period-90 image: 10
       chunks rewritten against fixed-size chunking's 988.  Measured on a real 104 KB machine
       image at `default`: one to three chunks, all max-forced.  Content-defined chunking
       DEGRADES there — it does not fail, and because the machine image grows by appending
       (test_checkpoint §8 proves the trace and the ref heap are stable prefixes) even
       max-forced cuts still dedup.  The consequence is `default`'s note below.       tested
   CH7 The two-level manifest.  A chunk-ref list longer than `single_max` is CUT INTO GROUPS BY
       CONTENT — group `i` ends after a ref whose address's `prefix63` is 0 mod `groups.avg`,
       bounded by `groups.min` and `groups.max` — so an edit that changes two chunks rewrites
       at most two group nodes and the root, instead of the whole manifest.  A2 §4.4 measures
       the manifest of a 64 MB image at 139 KB flat against ~10 KB with this lever.
                                                             by construction; benched (B7)
   CH8 Levels nest: `store_manifest` recurses until one node holds the level, so the depth is
       ceil(log_{groups.avg} n) and is 1 for every image below `single_max` chunks.  `flatten`
       reads a root manifest back to its chunk refs in level order, left to right, and is the
       inverse of the build.                                                 tested
   CH9 Streaming: `fold_chunks` never holds more than one chunk's bytes at a time, so a
       consumer that only needs a fold over the image — a size, a digest, a scan — never
       materialises it (risk R8).                            by construction; tested

   ============================================================================
   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.9 (lane P6,
   2026-09-08).  Nothing named in §1.9 is missing or renamed.
   D1  `store` and `store_manifest` take `~spec`.  §1.9's signature is
       `store : E4_cas.t -> params -> string -> Ref.t list`, which cannot file a node: every
       non-genesis node's edge 0 is its spec at kind `schema` and `E4_cas` refuses a spec that
       resolves to nothing (`Node.checkedEdges`, Node.lean:297; golden G2's `dangling-zero`).
       The spec is the caller's because the schema is the caller's — `E4_checkpoint` supplies
       the pending one.
   D2  `store_counted` is added beside `store`: the same work, answering how many chunk nodes
       were `Fresh` and how many `Duplicate`.  That count IS the structural sharing of A2 §4.4
       and the bench cell B7 needs it; recomputing it from `stats` would confuse a chunk with
       every other node the same commit filed.
   D3  `threshold` is a value, not a limit this module enforces: `cut` chunks whatever it is
       given.  Choosing `Whole` below it is `E4_checkpoint.write`'s decision, which is where
       the choice is visible to a caller that wants to force it (OQ2).
   D4  Added and each of them a reading of the same bytes: `chunks` (`cut default`, the
       brief's name), `pieces`, `piece`, `params_ok`, `groups_default`, `single_max`,
       `manifest` with `encode_manifest` / `decode_manifest`, `store_manifest`, `flatten`,
       `reassemble_manifest`, `fold_chunks`, `chunk_node`, `chunk_payload` and `window` (62 —
       the recurrence's memory, which CH6's proof cites and a test asserts against `min`). *)

(* ---------------------------------------------------------------- the parameters *)

type params = {
  avg : int;  (** the target average chunk size; a power of two — it is the cut mask plus one *)
  min : int;  (** no cut is taken before this many bytes; must be > [window] *)
  max : int;  (** a cut is forced here *)
}

val default : params
(** avg = 16384, min = 4096, max = 65536 — A2 §4.4's optimum and owner question OQ2's applied
    default.  The closed form behind it is `c* = sqrt (42 * S / k)` for an image of S bytes
    with k edited regions and 42 the bytes of a framed `ref`; at S = 64 MB and k = 2 that is
    ~32 KB, and the smaller side of the optimum is chosen because it also wins the append and
    insert mutations (A2 §4.4's table, rows E2 and E3).

    MEASURED, and a FINDING for the coordinator: `default` is a constant and the closed form
    is not.  At a 64 MB image `default` is right — bench_checkpoint's B7 cell measures 78 677
    new bytes for the second of two checkpoints against 67 109 154 with chunking off, a 853x
    reduction, inside B7's <= 300 KB and >= 200x.  At a 104 KB machine image the same closed
    form asks for ~1 480 B, and `default` cuts one to three chunks, shares nothing and costs
    the node overhead: over 64 consecutive checkpoints of the chain-of-refMake run at n = 2000
    (test_checkpoint §8) it stores 3 454 528 B against the whole blob's 3 428 148 B — 0.99x,
    i.e. slightly WORSE — where avg 4 KB gives 1.70x and avg 1 KB gives 4.46x (769 472 B, a
    mean of 12 170 B per checkpoint against a 104 KB image).  A checkpointing engine should
    therefore choose `avg` from the image size rather than take this constant; owner question
    OQ2 fixed the default and this lane does not turn it. *)

val params_ok : params -> bool
(** window < min <= avg <= max, avg a power of two and at most 2^30 (the mask must fit above
    the 62-bit word).  Every entry point raises `Invalid_argument` on params this refuses. *)

val window : int
(** 62: the number of bytes the gear recurrence remembers.  `min > window` is what makes CH6
    hold, and it is why resetting h at a chunk start is free. *)

val threshold : int
(** 1 MiB (A2 §5.1 OQ2): the image size at or above which `E4_checkpoint.write` chunks.  A
    value, not a limit — see D3. *)

(* ---------------------------------------------------------------- cutting *)

val cut : params -> string -> (int * int) list
(** The (offset, length) of every chunk, in order, covering the whole string exactly
    (CH1, CH2).  `cut p ""` is `[]`. *)

val chunks : string -> (int * int) list
(** `cut default`. *)

val piece : string -> int * int -> string
val pieces : params -> string -> string list

(* ---------------------------------------------------------------- the manifest *)

type manifest =
  | Leaf of E4_addr.Ref.t list  (** ctor 0: refs at kind `chunk`, in image order *)
  | Interior of E4_addr.Ref.t list  (** ctor 1: refs at kind `manifest`, in image order *)

type groups = { g_avg : int; g_min : int; g_max : int }
(** The content-defined cut of a REF LIST into manifest groups (CH7).  `g_avg` is a power of
    two: a ref ends a group when its address's `prefix63` is 0 modulo it. *)

val groups_default : groups
(** g_avg = 256, g_min = 64, g_max = 1024: ~10.7 KB of framed refs per group node, which is
    what turns A2 §4.4's 139 KB flat manifest into ~10 KB of rewritten manifest per edit. *)

val single_max : int
(** 1024: a chunk-ref list no longer than this is one leaf manifest and no groups are cut. *)

val group_cut : groups -> E4_addr.Ref.t list -> E4_addr.Ref.t list list
(** The groups, in order, concatenating back to the input (CH7). *)

val encode_manifest : manifest -> string
(** The payload bytes of a manifest node, in the grammar at the head of this file. *)

val decode_manifest : string -> manifest option
(** Exact: trailing bytes, a wrong ctor index, a ref at the wrong kind and a frame that is not
    a ref are all refusals. *)

(* ---------------------------------------------------------------- storing *)

val chunk_payload : string -> string
(** The payload bytes of a chunk node over these bytes: one `bytes` frame. *)

val chunk_node : spec:E4_addr.Addr.t -> string -> E4_node.t
(** The chunk node itself, at kind `chunk`, version 0. *)

val store : E4_cas.t -> spec:E4_addr.Addr.t -> params -> string -> E4_addr.Ref.t list
(** Cut the image and stage one `chunk` node per piece, in image order, answering their refs
    (D1).  Staged, not durable: the caller commits.  Raises `Store_error` if the store refuses
    a chunk node — which can only be a spec that does not resolve, since a `bytes` payload is
    admissible by construction. *)

val store_counted : E4_cas.t -> spec:E4_addr.Addr.t -> params -> string ->
  E4_addr.Ref.t list * int * int
(** `store`, also answering (fresh, duplicate) — the sharing count (D2). *)

val store_manifest :
  E4_cas.t -> spec:E4_addr.Addr.t -> ?groups:groups -> ?single_max:int ->
  E4_addr.Ref.t list -> E4_addr.Ref.t
(** Build the manifest tree over these chunk refs and stage every node of it, answering the
    ROOT manifest's ref (CH7, CH8). *)

val store_manifest_counted :
  E4_cas.t -> spec:E4_addr.Addr.t -> ?groups:groups -> ?single_max:int ->
  E4_addr.Ref.t list -> E4_addr.Ref.t * int * int * int
(** `store_manifest`, also answering (nodes, fresh, duplicate) over the manifest tree. *)

(* ---------------------------------------------------------------- reading *)

val get_chunk : E4_cas.ro -> E4_addr.Ref.t -> string option
(** The bytes of one chunk node: resident, at kind `chunk`, payload one `bytes` frame. *)

val reassemble : E4_cas.ro -> E4_addr.Ref.t list -> string option
(** CH4: the concatenation of the chunks, or None if any is missing or malformed. *)

val get_manifest : E4_cas.ro -> E4_addr.Ref.t -> manifest option

val flatten : E4_cas.ro -> E4_addr.Ref.t -> E4_addr.Ref.t list option
(** The chunk refs under a root manifest, in image order (CH8). *)

val reassemble_manifest : E4_cas.ro -> E4_addr.Ref.t -> string option
(** `flatten` then `reassemble`. *)

val fold_chunks : E4_cas.ro -> E4_addr.Ref.t -> init:'a -> f:('a -> string -> 'a) -> 'a option
(** Walk the manifest tree and fold over the chunks in image order, holding ONE chunk's bytes
    at a time (CH9, risk R8).  None if any node is missing or malformed. *)
