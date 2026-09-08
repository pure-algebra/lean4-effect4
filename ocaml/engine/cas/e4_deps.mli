(* E4_deps — the dependents index: which nodes name a given address.

   WHAT THIS MODULE IS, SAID FIRST BECAUSE IT MATTERS.  Lane P2 already built the dependents
   index, inside `E4_index.Deps` (ocaml/engine/cas/e4_index.mli:302-338), together with the
   node index it shares a pack scan with.  This module is therefore a FACE over that one and
   not a second implementation: `type t = E4_index.Deps.t`, and every operation below either
   forwards to `E4_index.Deps` verbatim or is a build path expressed in terms of it.  What it
   adds is what A2 §2.4 asks a cache to carry and what §1.6 left to lane P7:

     (a) the two BUILD paths named and shown to agree — `of_nodes` walks a store's bindings in
         write order and folds `add_node`; `rebuild` scans the pack; law DP1 is that they are
         equal, which is the "rebuild = incremental" statement of L-IDX-0 for this index;
     (b) `equal` and `to_pairs`, so DP1 is a proposition a test can decide rather than a
         sentence in a document;
     (c) the default `?fields`, so no caller has to remember that the table is
         `E4_shape.table` (finding R1: a `Cid` is only a `Cid` through the table);
     (d) `of_store`, the path from an `E4_cas.ro` — the only handle most callers hold.

   Identity: the pack, read through `E4_shape.table`.  Rebuild: a full scan (`rebuild`).  It is
   O(bytes) by construction and has to be, because a `Cid` field is byte-for-byte
   indistinguishable from any other 32-byte `bytes` frame (`E4_shape` finding R1) and only the
   per-kind table can tell them apart.

   Depends on: E4_index (the implementation), E4_shape, E4_node, E4_addr, E4_pack, E4_cas.

   Behaviours:
   DP1 REBUILD = INCREMENTAL.  For a store whose pack is intact, `of_nodes (E4_cas.nodes ro)`
       and `fst (rebuild ~from:E4_index.from_start reader)` are `equal`: same dependees, in the
       same order, each with the same dependents in the same order.  Both walk write order —
       `E4_cas.nodes` is `Store.nodes` in insertion order (e4_cas.mli) and `E4_pack.scan` is in
       write order — so the agreement is on the ORDER too and not only on the set.
                                                              by construction; tested (D1, D5)
   DP2 NOT AN EDGE (L-DEP-1, amendment M1).  Nothing in `E4_cas` consults this index:
       `reachable`, `closure` and admission are computed without it, which the compiler states
       for us — `E4_cas` does not depend on this module.  The test makes it visible by
       building a full dependents index and showing `E4_cas.reachable` and `E4_cas.closure`
       answer exactly what they answered before.                by construction; tested (D6)
   DP3 NO PROPAGATE (L-DEP-2).  There is no `propagate` and there will not be one: a
       row-preserving edit is not a meaning-preserving edit here, because
       `exists_carrier_collision` (src/Effect4/Machine/Key.lean:383-386) says type identity
       never recovers code identity.  A change under a name mints a new `Publication`; nothing
       is ever re-hashed automatically.                          by construction (the function
                                                                 does not exist)
   DP4 PERSISTENT.  `add` and `add_node` return a new value and no earlier value is observably
       changed: a `t` held across a hundred additions still answers what it answered.
                                                              by construction; tested (D3)
   DP5 THE SPECIFICATION IS `of_node`.  The dependees of one node are `E4_node.checked_edges`'
       addresses — exact, no table, and the genesis exemption included — followed by
       `E4_shape.cids_of` for that node's kind — the table's Cid fields, and only those.  The
       two halves are named apart because the first is exact and the second is transcribed.
       The brute-force test recomputes exactly this and compares.  tested (D2, D4)
   DP6 A record whose bytes do not decode contributes nothing and does not stop a scan; a scan
       stops only where `E4_pack.scan` stops, and `rebuild` returns that verdict beside the
       index so a truncated pack cannot be mistaken for a small one.       tested (D7)

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.6's `Dependents` (lane
   P7, 2026-09-08).

   D1  §1.6 gives `Dependents` a `type t` of its own.  Lane P2 landed it first, as
       `E4_index.Deps`, and building a second one would be two answers to one question.
       `type t = E4_index.Deps.t` is the whole of this deviation: the type is not abstract
       here, so a caller may use either name for the same value and no conversion exists to
       get wrong.
   D2  §1.6's `add`/`find` take `E4_addr.Cid.t` for the dependee and `E4_addr.Ref.t` for the
       dependent.  `Cid.t = Addr.t` (e4_addr.mli), and a dependee reached through
       `checked_edges` is an `Addr` and not a `Cid`, so the parameter is spelled `Addr.t` —
       the same type under the name that says what it is.  `E4_index.Deps` already spells it
       that way and this face does not disagree with the module it is a face of.
   D3  `fields` is optional here and mandatory in `E4_index.Deps`, defaulting to
       `E4_shape.table`.
   D4  Added: `of_nodes`, `of_store`, `rebuild_dir`, `to_pairs`, `equal`, `dependees`,
       `dependents_of` and `fields_default` — (a) to (d) above. *)

type t = E4_index.Deps.t
(** The lane P2 index, under this lane's name (D1). *)

val fields_default : E4_shape.t
(** `E4_shape.table` — the only table there is (finding R1). *)

(* ---------------------------------------------------------------- building *)

val empty : t

val add : t -> dep:E4_addr.Addr.t -> by:E4_addr.Ref.t -> t
(** Persistent (DP4); idempotent on a pair already present. *)

val of_node : ?fields:E4_shape.t -> E4_node.t -> E4_addr.Addr.t list
(** DP5: the dependees of one node, in order — `checked_edges` then `cids_of`. *)

val add_node : t -> ?fields:E4_shape.t -> at:E4_addr.Addr.t -> E4_node.t -> t

val of_nodes : ?fields:E4_shape.t -> (E4_addr.Addr.t * E4_node.t) list -> t
(** The INCREMENTAL build: fold `add_node` over the bindings in the order given, which for
    `E4_cas.nodes` is write order (DP1). *)

val of_store : ?fields:E4_shape.t -> E4_cas.ro -> t
(** [of_nodes (E4_cas.nodes ro)]. *)

val rebuild :
  ?fields:E4_shape.t -> from:int * int -> E4_pack.reader -> t * E4_pack.scan_stop
(** The FULL SCAN (DP1, DP6).  `E4_index.Deps.rebuild`, with the arguments ordered so the
    optional one can be erased. *)

val rebuild_dir : ?fields:E4_shape.t -> string -> t * E4_pack.scan_stop
(** [rebuild] from the start of the pack of the store directory named, opening and closing its
    own reader. *)

(* ---------------------------------------------------------------- querying *)

val find : t -> E4_addr.Addr.t -> E4_addr.Ref.t list
(** The nodes that name this address, in discovery order. *)

val mem : t -> E4_addr.Addr.t -> bool
val cardinal : t -> int
(** Distinct dependees. *)

val edges : t -> int
(** (dependee, dependent) pairs. *)

val iter : t -> (E4_addr.Addr.t -> E4_addr.Ref.t list -> unit) -> unit

val dependees : t -> E4_addr.Addr.t list
(** Every address something names, sorted by address, so two indexes can be compared without
    depending on either one's discovery order. *)

val dependents_of : t -> E4_addr.Addr.t -> E4_addr.Ref.t list
(** [find], named the long way round for a caller that reads. *)

val to_pairs : t -> (E4_addr.Addr.t * E4_addr.Ref.t list) list
(** Sorted by dependee; each dependent list in DISCOVERY order, because that order is part of
    what DP1 claims. *)

val equal : t -> t -> bool
(** [to_pairs] equal, address for address and dependent for dependent (DP1). *)

val diff : t -> t -> string option
(** None when [equal]; otherwise the first disagreement, spelled for a test's failure line. *)
