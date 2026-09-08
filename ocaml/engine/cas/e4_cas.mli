(* E4_cas — the on-disk content-addressed store: grow-only nodes keyed by the SHA-256 of their
   canonical bytes, admission in Lean's order, the three put outcomes, the roots plane, closure,
   recovery and verification.

   What it is: `src/Effect4/Store/Store.lean` and `src/Effect4/Store/Word.lean` as a durable
   object.  `put` is `Store.putNode` (Store.lean:262-276); `get_node` is `Store.find` (:87);
   `advance_root` is `Store.putRoot` (:523-530); `closure` is `Store.closure` (Word.lean:346);
   `word_wf` is `Word.wf` (:70); `apply_word` is `Word.apply` (:73); `verify` is `Store.verify`
   (Word.lean:772).  The pack holds the nodes, an index finds them, the control file holds the
   roots and the durable end.

   The store directory (A2 §1.0):

     <store>/LOCK                the writer lock — E4_pack takes it, one writer per store
     <store>/control             the roots, the durable end, the status (E4_control)
     <store>/pack/%06d.pack      the append-only node records (E4_pack)
     <store>/index/              the index snapshots (a cache; empty until lane P2 lands)

   Depends on: E4_pack, E4_control, E4_node, E4_addr, E4_kind (lanes P0/P1/P3), E4_sha256
   (ocaml/engine, lane M), unix.  It writes no second hash, no second framing writer and no
   second byte grammar (brief §2.2).

   ============================================================================
   Behaviours (the laws of docs/research/2026-09-08-engine-a2-persistence.md §2.1):

   CS1 / L-CAS-5  Grow-only, three outcomes.  `Fresh` appends; `Duplicate` changes nothing;
       `Conflict occupant` changes nothing and exhibits the occupant, which is never
       overwritten (`putNode_sub` Store.lean:350, `put_duplicate` :482, `put_conflict`).
       No function of this module removes or replaces a node.       by construction; tested
   CS2 / L-CAS-4  Admission refuses in exactly Lean's order, first refusal wins:
         1  `Oversize`         the payload is not one well-formed frame tree (Lean: ¬ WF)
         1' `Host_limit`       a frame length >= 2^62 (amendment M9; OCaml only)
         2  `Bad_version`      a version byte other than 0
         3  `Malformed_ref`    a tag-11 frame with an unregistered kind byte or a digest that
                               is not 32 bytes
         3' `Handle_in_content` a content kind whose payload carries a tag-12 frame
                               (amendment M2; A2 owner question OQ4's default position —
                               `admission_stages` below is where it moves, in one line)
         4  `Dangling`         a checked edge names no node          [checked_edges order,
         5  `Wrong_kind`       a checked edge names another kind      spec edge first]
       The genesis (kind `schema` with the zero spec) is exempt from the spec edge and nothing
       else is (`Node.checkedEdges`, Node.lean:297).      tested: golden G2, prop L-CAS-4
   CS3  The address is `sha256 (E4_node.encode n)` and nothing else is ever hashed
       (`Store.address`, Node.lean:354; L-CAS-1).                    by construction; tested
   CS4  Single writer, checked: `open_rw` takes the pack's exclusive lock on <store>/LOCK and
       raises `Locked` when another writer holds it.  Readers take no lock.       tested (X5)
   CS5  Durability is per COMMIT, not per put: `put` stages, `commit` performs ONE write(2)
       and ONE fsync(2) per touched pack segment and then one tmp+rename+fsync of the control
       file — the group commit and the watermark advance are one durable step.
                                                                     by construction; benched
   CS6 / L-CAS-8  Recovery: on open, the records past the control file's `pack_end` are
       re-scanned and re-admitted in write order; the scan stops at the first record that
       fails CRC, digest or admission.  A torn or corrupt record is truncated away by the pack
       (E4_pack PK3/PK7); an ADMISSION failure is not (see D6).  Licensed by `Word.wf` /
       `wf_closed`: a children-first word replays from a closed store into a closed store.
                                                                     tested (X1, X2, X7)
   CS7 / L-CAS-6  `verify` is `Store.verify`: it re-reads every record from the pack and
       re-hashes it, re-decodes it, re-resolves every checked edge at its kind and resolves
       every root.  It NEVER consults the index and never trusts a record's recorded digest —
       both are caches of it.                              by construction; tested (G7, X3)
   CS8  The store never collects (Store.lean:19, cas-design §8).  `reachable` and `by_cid` are
       queries, never edges (amendment M1: `Reachable` does not walk `Cid` fields), and
       `pin_all` mints the pin roots a publish owes.                          tested (G3)
   CS9 / L-CAS-7  `closure` is the transfer unit: it is a well-formed word, children first,
       and two stores holding the same nodes in different insertion orders have DIFFERENT
       `nodes` and byte-identical closures.                          tested: golden G6, D5

   ============================================================================
   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.8 (lane P4,
   2026-09-08).  Nothing named in §1.8 is missing or renamed.

   D1  The digest index is INTERNAL.  Lane P2's `e4_index.mli` had not landed when this lane
       built, so `E4_cas` carries a private `Index` module with A2 §1.6's shape
       (`create ~slots` / `find` / `add` / `mem` / `count` / `slots`, first-wins on a repeated
       key, `rebuild` by a pack scan) over a `Hashtbl` keyed by the 32 raw digest bytes.  It
       is a cache in the strict sense — `drop_index` throws it away and the next query
       rebuilds it from the pack, changing no answer (L-IDX-0, crash family X3).  Swapping in
       `E4_index` is a change to that one module and to nothing else: `find`'s entry is
       `{ seg; off; kind }`, except that the kind is filled lazily here (a header scan cannot
       see the kind byte, and paying a full record read per entry at rebuild would cost the
       B4 number for a field most entries are never asked for).
   D2  `Oversize` carries no payload, as §1.8 writes it; `E4_node.check_pure`'s
       `Oversize of decode_error` is split here into `Oversize` and `Host_limit` (CS2 rows 1
       and 1'), which is what §1.8's two rows ask for.
   D3  `apply_word` answers its own error type.  Lean's `Word.apply` refuses a conflicting
       binding with `Admission.conflict address occupant` (Word.lean:73-81), and §1.8's
       `admission` has no such constructor — `put` can never return one.  `word_error` is
       therefore `Refused_by of admission | Word_conflict of { at; occupant }`.
   D4  Added, and each of them is a read of state this module already holds: `read_only` (the
       writer's own read view — §1.8 types `put` on `t` and `get_node` on `ro` and gives no
       bridge), `dir`, `generation`, `nodes` (`Store.nodes`, in insertion order, which is what
       makes L-CAS-7 testable), `addresses`, `closed` (`Closed`, Store.lean:241, as a
       decision), `recovery`, `drop_index`, `index_count`, and the four printers
       `outcome_word` / `admission_word` / `verify_error_word` / `recovery_stop_word`, whose
       vocabulary is Lean's so a golden's `expected` column compares as a string.
   D5  `by_cid` is computed WITHOUT `E4_shape` (lane P2's file): a `Cid` is the payload digest
       (amendment M6), so `by_cid k c` is the addresses of the resident nodes of kind `k`
       whose payload hashes to `c`.  It needs no per-kind field table — the field table is
       needed for the DEPENDENTS index (§1.7), which is lane P7's and is not here.
       AMENDED by lane W (P6 finding F6): it WAS a full scan that re-hashed every resident
       payload on every call, so `pin_all` at publish was O(store bytes) PER CALL.  §2.4 says
       `byCid` is "a cache with a rebuild"; the cache now exists (`cidmap` in e4_cas.ml).
       Each node's payload is hashed once per view, on the first `by_cid` that sees it, and a
       call then costs a hash-table lookup plus the matches.  It is a CACHE and not an edge
       (CS8 is untouched): it changes no answer, `verify` never consults it, and it is
       rebuilt from the pack whenever the watermark moves backwards.  `drop_index` drops the
       node index only; the by-Cid table has no public drop because nothing observes it.
   D6  An ADMISSION failure in the recovered tail does not truncate the pack.
       `E4_pack.truncate_to` refuses any offset below the writer's own `pack_end`
       (e4_pack.ml:766-768), which after `open_at` is the end of the last record that passed
       CRC and digest — so a record that is physically intact but whose children are missing
       cannot be cut away through lane P1's interface.  Rather than truncate another lane's
       file behind its back, or silently drop the tail and let a later commit make those bytes
       "trusted", this lane STOPS: the store opens with everything below the failure,
       `recovery` names the offset and the refusal, and `put` / `commit` / `advance_root`
       raise `Store_error` until an operator acts.  It is unreachable under this module's own
       writes (a commit stages children first and a crash can only lose a suffix), and the
       alternative is losing records a later restart would have to invent.
   D7  `advance_root` commits the pack before it moves a root, so a root never names a node
       that is not yet durable, and then writes the control file once: the two halves of CS5
       stay one durable step.
   D8  `pin_all` names its roots `runs/<job hex>/pin/<cid hex>` (with `/2`, `/3`, … when one
       `Cid` has several filings).  Amendment M1 fixes the mechanism — "publishing a job mints
       `pin` roots for the filings its `Cid`s name, over the node address `byCid` finds; if
       `byCid` finds no filing, refuse the publish (`dangling`), never file a new node" — and
       names the roots after the job's parts (`runs/<job>/program`, `/tape`, `/profile`),
       which a bare `Cid` list cannot distinguish.  `pin` mints one root under a name the
       caller chooses and is what a publisher should use; `pin_all` is §1.8's signature kept
       working.  `RootKind.pin` is not in Lean (`Store.lean:47-53`) and lane GLD reports M1 as
       owed (2026-09-08-engine-lane-gld-delivery.md §4 O4), so no golden pins the names.
   D9  `verify_node` re-hashes and re-decodes its one node and resolves its edges through the
       ordinary lookup; only whole-store `verify` refuses to consult the index (CS7).  A
       one-node verification that rebuilt the whole table would not be a query anybody could
       afford on the read path. *)

(* ---------------------------------------------------------------- the store *)

type t
(** A writer: the pack's lock, the staging buffer, the index and the control payload. *)

type ro
(** A read view: no lock.  `read_only` derives one from a writer (it sees that writer's staged
    records); `open_ro` opens one on a store another process is writing (it sees exactly what
    the last control commit made durable). *)

type outcome =
  | Fresh  (** appended *)
  | Duplicate  (** the resident IS this node; nothing changed *)
  | Conflict of E4_node.t  (** another node is resident at this address; nothing changed *)

type admission =
  | Oversize  (** the payload is not one well-formed frame tree (Lean: ¬ payload.WF) *)
  | Host_limit of string  (** a frame length >= 2^62 — amendment M9, not a Lean refusal *)
  | Bad_version of int  (** the version byte that was not 0 *)
  | Malformed_ref
  | Handle_in_content  (** amendment M2; its position in the order is A2 OQ4 *)
  | Dangling of E4_addr.Addr.t
  | Wrong_kind of { at : E4_addr.Addr.t; expected : E4_kind.t; actual : E4_kind.t }

type verify_error =
  | Digest_mismatch of E4_addr.Addr.t
  | Undecodable of E4_addr.Addr.t
  | Verify_malformed_ref of E4_addr.Addr.t
  | Verify_dangling of { node : E4_addr.Addr.t; missing : E4_addr.Addr.t }
  | Verify_wrong_kind of {
      node : E4_addr.Addr.t;
      ref_ : E4_addr.Addr.t;
      expected : E4_kind.t;
      actual : E4_kind.t;
    }
  | Root_unresolved of string
(** `Word.VerifyError` (src/Effect4/Store/Word.lean:724-737), constructor for constructor. *)

exception Locked of string
(** Another writer holds <dir>/LOCK (CS4).  Carries the directory. *)

exception Store_error of string
(** The store cannot be opened or cannot be grown: a control file this binary does not
    understand, a pack whose head does not check, or an unadmitted tail (D6). *)

(* ---------------------------------------------------------------- the words *)

val outcome_word : outcome -> string
(** "fresh" | "duplicate" | "conflict" — `Store.Outcome`'s spelling, so golden G2's `expected`
    column compares as a string. *)

val admission_word : admission -> string
(** "oversize" | "hostLimit <why>" | "badVersion" | "malformedRef" | "handleInContent" |
    "dangling <hex>" | "wrongKind" — `Store.Admission`'s spelling (Store.lean:153-169), with
    the two refusals Lean does not have named as the amendments name them. *)

val verify_error_word : verify_error -> string
(** "digestMismatch" | "undecodable" | "malformedRef" | "dangling <missing hex>" |
    "wrongKind" | "rootUnresolved <name>" — golden G7's vocabulary. *)

(* ---------------------------------------------------------------- opening *)

type open_opts = {
  seg_max : int;  (** pack segment rotation, bytes *)
  index_slots : int;  (** the index's initial capacity *)
  verify_on_open : bool;  (** run `verify` after recovery and raise `Store_error` on a fault *)
}

val default_opts : open_opts
(** seg_max = 1 GiB (`E4_pack.default_seg_max`), index_slots = 1 lsl 12, no verify.  §1.8's
    default is 1 lsl 20; that is 32 MB of table for a store of any size, and `E4_index` grows
    itself at load 0.6 (IX4), so the large number is only a tax on small stores.  A caller
    that knows how many nodes it will hold passes `index_slots` and lands at the load factor
    A2 §6.4 measured — bench cell B5's bytes-per-node is a function of exactly that. *)

type recovery_stop =
  | Clean  (** the tail ended where the pack ended *)
  | Torn of E4_pack.scan_stop  (** the pack refused a record: CRC, digest, tag, length *)
  | Refused of {
      seg : int;
      off : int;
      addr : E4_addr.Addr.t;
      why : admission;
    }  (** a physically intact record the store refuses to admit (D6) *)

type recovery = {
  from : int * int;  (** the control file's `pack_end` — where re-admission started *)
  admitted : int;  (** records admitted `Fresh` *)
  duplicates : int;  (** records already resident at their address *)
  ends_at : int * int;  (** the end of the last admitted record: the new watermark *)
  stop : recovery_stop;
  pack : E4_pack.recovery;  (** what the pack's own scan found (E4_pack PK7) *)
}

val recovery_stop_word : recovery_stop -> string
val recovery : t -> recovery

val open_rw : dir:string -> open_opts -> t
(** Create or open the store at [dir], take the writer lock, recover the tail (CS6) and commit
    the watermark.  Raises `Locked` when another writer holds the lock, and `Store_error` when
    the control file or a pack head cannot be read. *)

val open_ro : dir:string -> ro
(** A read view over what the control file says is durable.  Takes no lock, admits nothing and
    never writes.  `Store_error` when the control file cannot be read. *)

val read_only : t -> ro
(** The writer's own read view (D4): it sees the records staged since the last commit. *)

val close : t -> unit
val close_ro : ro -> unit

val reopen_ro : ro -> ro
(** Re-read the control file and index whatever another writer has committed since (X5). *)

val dir : t -> string

(* ---------------------------------------------------------------- nodes *)

val put : t -> E4_node.t -> (outcome * E4_addr.Addr.t, admission) result
(** CS1, CS2, CS3.  Stages the record; not durable until [commit]. *)

val put_bytes : t -> string -> (outcome * E4_addr.Addr.t, admission) result
(** [put] of `E4_node.decode`'s answer.  Bytes that do not decode are refused in the order a
    node's own admission would refuse them: a version byte other than 0 is `Bad_version`, a
    frame at or above 2^62 is `Host_limit`, anything else is `Oversize`. *)

val commit : t -> unit
(** CS5: one write(2) and one fsync(2) per touched pack segment, then the control file's
    watermark by tmp+rename+fsync — one durable step.  A no-op when nothing is staged and the
    watermark has not moved. *)

val get_node : ro -> E4_addr.Addr.t -> E4_node.t option
(** `Store.find` (Store.lean:87). *)

val get_bytes : ro -> E4_addr.Addr.t -> string option
val get_kind : ro -> E4_addr.Addr.t -> E4_kind.t option
val mem : ro -> E4_addr.Addr.t -> bool

val resolves : ro -> E4_addr.Ref.t -> bool
(** `Store.Resolves` (:182): a node is filed at that digest, at that kind. *)

val nodes : ro -> (E4_addr.Addr.t * E4_node.t) list
(** `Store.nodes` (:73-75): the bindings in INSERTION order, which is the pack's write order.
    Order-dependent by construction — that is what L-CAS-7 is about. *)

val addresses : ro -> E4_addr.Addr.t list
val count : ro -> int

(* ---------------------------------------------------------------- roots *)

val root : ro -> string -> E4_control.root option
val roots : ro -> E4_control.root list
val next_version : ro -> string -> int
val generation : ro -> int

val advance_root :
  t -> ?prev:E4_addr.Addr.t -> E4_control.root -> (unit, E4_control.root_error) result
(** `Store.putRoot` (:523-530) with the version, dangling and kind checks all real: the
    resolver is this store's own kind lookup.  Commits the pack first (D7) and the control
    file after, so a root never names a node that is not durable. *)

val pin : t -> name:string -> E4_kind.t -> E4_addr.Cid.t -> (unit, E4_control.root_error) result
(** Amendment M1's `pin name target`: a `Pin` root over the address `by_cid` finds for that
    `Cid` at that kind.  `Dangling` when the `Cid` has no filing — a pin never files a node. *)

val pin_all :
  t -> job:E4_addr.Addr.t -> E4_addr.Cid.t list -> (unit, E4_control.root_error) result
(** §1.8's signature (D8): one `Pin` root per filing, named `runs/<job hex>/pin/<cid hex>`.
    Refuses the whole publish with `Dangling` when any `Cid` has no filing, and files nothing
    in that case. *)

(* ---------------------------------------------------------------- words, closure, verify *)

type binding = { addr : E4_addr.Addr.t; node : E4_node.t }
(** `Word.Binding` (src/Effect4/Store/Word.lean:44-48). *)

val word_wf : binding list -> bool
(** `Word.wf` (:70): children first, digests exact, no digest twice. *)

val closure : ro -> E4_addr.Ref.t -> binding list
(** `Store.closure` (:346): the reachable subgraph of a reference, children first, each digest
    once, with `Word.emit`'s guard, at fuel `count`.  Order-independent (L-CAS-7). *)

type word_error =
  | Refused_by of admission
  | Word_conflict of { at : E4_addr.Addr.t; occupant : E4_node.t }
      (** `Admission.conflict` (Store.lean:166-168), which `put` can never answer (D3) *)

val apply_word : t -> binding list -> (unit, word_error) result
(** `Word.apply` (:73-81): a fold of `put`; a `Duplicate` is fine, a `Conflict` refuses. *)

val verify : ro -> (unit, verify_error) result
(** `Store.verify` (Word.lean:772).  CS7: its own scan of the pack, every record re-hashed and
    re-decoded, every checked edge re-resolved at its kind, every root resolved.  The index is
    not consulted and the recorded digest is not trusted. *)

val verify_node : ro -> E4_addr.Addr.t -> (unit, verify_error) result
(** `Store.verifyNode` (Word.lean:749-755) for one address (D9). *)

val closed : ro -> bool
(** `Closed` (Store.lean:241): every resident node's checked edges resolve at their kinds. *)

(* ---------------------------------------------------------------- queries that are not edges *)

val by_cid : ro -> E4_kind.t -> E4_addr.Cid.t -> E4_addr.Addr.t list
(** Amendment M6: the filings of a payload digest AT A KIND, in insertion order (D5).
    O(matches) plus one payload hash for each node written since the previous call. *)

val by_cid_any : ro -> E4_addr.Cid.t -> (E4_kind.t * E4_addr.Addr.t) list

val reachable : ro -> E4_addr.Addr.t -> bool
(** `Store.Reachable`: some root's checked-edge closure contains this address.  It never walks
    a `Cid` field (amendment M1). *)

(* ---------------------------------------------------------------- the caches, statistics *)

val drop_index : ro -> unit
(** L-IDX-0: throw the digest index away.  The next query rebuilds it from the pack and every
    answer is the same (crash family X3). *)

val index_count : ro -> int

type stats = {
  nodes : int;
  bytes : int;
  index_slots : int;
  index_bytes : int;
  commits : int;
  fsyncs : int;
  conflicts : int;
}

val stats : ro -> stats
(** The writer's counters are visible through `read_only`; a view from `open_ro` reports zero
    for `commits`, `fsyncs` and `conflicts` because it performs none. *)
