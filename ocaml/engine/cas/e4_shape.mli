(* E4_shape — which fields of a kind's frozen payload are Cids, which are Refs, which are
   Digest stamps, and which are plain data.

   What it is: the per-kind, per-`ValPath` field table of
   docs/research/2026-09-08-engine-a2-persistence.md §1.7, transcribed from the payload shapes
   the tree already fixes and pinned by a golden when the coordinator cuts G8.  It exists
   because of a finding, not a preference:

     FINDING R1.  `Canonical Digest` frames a digest as `Val.bytes d.bytes`
     (instCanonicalDigest (src/Effect4/Store/Domain/Canonical.lean)), i.e. `08 ++ be64 32 ++ <32 bytes>`, and the CAS
     design gives `Cid α` the same shape (2026-09-07-cas-design.md §1, §3).  So a `Cid` field is
     byte-for-byte indistinguishable from any other 32-byte `bytes` frame — a `Digest` stamp, a
     `spanDigest` on a `Pin`, an `engine` manifest digest, a hash literal inside a program.  A
     blind byte scan therefore cannot build the dependents index and cannot decide which 32-byte
     blobs are edges of the `Cid` graph.  The resolution is M17's rule one level up — every
     ordinal in canonical bytes is a position in a table that is itself content — applied to the
     frozen payload shapes: the table is transcribed, never inferred from bytes.

     FINDING R1'.  A second finding of this lane, and the reason the table has a `status`
     column.  **The kind byte is not injective on carriers** — `Kind (src/Effect4/Store/Carrier/Kind.lean)`
     says so in its own header, and the tree bears it out: `source` (1) carries
     `StdLib.Source` (SourceC.instContent (git:9b887fdc8^:src/Effect4/StdLib/Derived.lean)), `Store.Pin` (PinGen.PinC.instContent (src/Effect4/Store/Domain/PinDerived.lean)) and
     `Char.Implementation` (Implementation (git:9b887fdc8^:src/Effect4/Char/Conformance/Receipt.lean)); `annotation` (6) carries
     `Annotation τ` (instContentAnnotation (src/Effect4/Store/Domain/Traits.lean)), `Char.{Evidence,Claim,Target,Characterized}`
     (EvidenceC.instContent, ClaimC.instContent, TargetC.instContent, CharacterizedC.instContent (git:9b887fdc8^:src/Effect4/Char/Derived.lean)) and `Char.Receipt` (Receipt (git:9b887fdc8^:src/Effect4/Char/Conformance/Receipt.lean));
     `vector` (14) carries `Char.{GSet,Fact,Vector}` (CharGSetC.instContent, CharFactC.instContent, CharVectorC.instContent (git:9b887fdc8^:src/Effect4/Char/Canonical.lean)).  Those
     carriers have different arities and different field orders, so for such a kind NO ValPath
     is decidable from the kind byte alone.  A2 §1.7's "the frozen payload shape per kind" is
     therefore true only where a kind has exactly one carrier.  This table says which, in the
     open: a `Shared` row has no fields, and `cids_of` answers `[]` there rather than guessing.
     Nothing is lost for `refs`: a `Ref` is a tag-11 frame and `E4_node.refs` finds it exactly,
     without any table (SH1).

   Depends on: E4_kind, E4_addr, E4_be (ocaml/engine, lane M), and Eff_frame for the frame
   tags, which it never restates.  It reads payload bytes through `E4_be.read_frame` and never
   builds a value tree.

   Behaviours:
   SH1 A Ref field is a tag-11 frame and is found by `E4_node.refs` with no table at all; a Cid
       field is a tag-8 frame of length 32 and is found ONLY through this table.  `refs_of` is
       the table's answer and is a SUBSET of `E4_node.scan_refs`; the exact answer for refs is
       always `E4_node`'s.                                        by construction; tested
   SH2 The table covers every registered kind: `rows table` has one row per `E4_kind.all`, in
       byte order, and a kind with no Cid fields has the empty `cids_of`.        tested
   SH3 `cids_of_checked` / `refs_of_checked` refuse a payload that does not match the row's
       shape — a wrong tag, a `bytes` frame that is not 32 long, a ref frame whose kind byte is
       not the one the row fixes, a path that does not resolve — and never return a partial
       read.  The lenient `cids_of` / `refs_of` drop exactly what the checked form refuses.
                                                                                 tested
   SH4 No row is ever inferred from bytes.  Every row carries its provenance in
       `row.carriers` (the Lean declarations that file under that byte) and its `status`:
         Frozen      exactly one carrier files here; the row is that carrier's shape
         Shared cs   several carriers share the byte (finding R1'); no field is decidable
         Unused      the byte is registered and no carrier files under it today
         Tombstoned  `fiber` (15)
         Pending     bytes 16..23, the CAS append (DI-25): Lean's `Kind` table holds them, but
                     no Lean carrier files under them yet, so the shape is
                     2026-09-07-cas-design.md §4's and A2 §1.9's, and the checkpoint's is the
                     payload `E4_checkpoint` writes (its byte table)
       `status` is about carriers, never about the table: every byte 1..23 is Lean's.
                                                                           by construction
   SH5 The path language is `Arg i` (the i-th child of a ctor/pair/some/list frame) and `Each`
       (every child of a list frame), and a path resolves to a LIST of frames.  `Each` is why
       `Tree`'s bindings can be a row at all.                      by construction; tested
   SH6 The walk descends only into tags 4 (list), 5 (pair), 7 (some) and 10 (ctor), exactly as
       `E4_node`'s does, and never into tag 8: a `bytes` payload that happens to contain frames
       has no children (`Val.refs (.bytes bs) = []`, Val.refs (src/Effect4/Store/Domain/Node.lean)).            tested

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.7 (lane P2, 2026-09-08):
   D1  §1.7's paths are `int list`.  A `ValPath` into a LIST field cannot be written that way:
       `Store.Tree`'s bindings are `List (String × AnyRef)` (PinGen.TreeC.instContent (src/Effect4/Store/Domain/PinDerived.lean)), so the
       refs sit at "every element, second component".  The path element is therefore
       `Arg of int | Each`, and `int list` is the special case `List.map (fun i -> Arg i)`
       (`args`, below).
   D2  §1.7's `field` has three constructors.  This one has four: `Ref_field` carries the kind
       the shape fixes for the target (the brief's `Ref of kind`) and `Data_field` is added so a
       row can say "this ValPath is deliberately not an address" — the `Data` of the brief's
       `Cid | Ref of kind | Stamp | Data`.  `class_at` is the four-way view, plus `Cls_unknown`
       for a path under a `Shared`, `Unused`, `Tombstoned` or `Pending`-with-no-row kind.
   D3  Added beside §1.7's list: `rows`, `row`, `status`, `stamps_of`, the three `_checked`
       forms with `mismatch`, `resolve` (the path walk, exposed because the tests and lane P7
       both need it), `class_at`, `path_to_string`, `field_path`, and the constants `args` /
       `cid_length`.
   D4  §1.7's SH3 says a shape mismatch is "a decode refusal".  A refusal of WHAT is not stated
       and cannot be `E4_node.decode`'s: a node whose payload is a well-formed frame tree of the
       wrong shape is admitted by `Store.putNode` (Store.putNode (src/Effect4/Store/Domain/Store.lean) tests `Val.WF`, the
       version, the refs and the edges — never a per-kind shape), so refusing it here would make
       this host narrower than Lean, which brief §2.1 forbids.  The refusal is therefore of the
       QUERY: `cids_of_checked` answers `Error`, `E4_node.decode` and admission are untouched. *)

type step =
  | Arg of int (** the i-th child, 0-based *)
  | Each (** every child — a list frame's elements *)

(** A `ValPath`: argument indices in the encoded tree (amendment M5). *)
type path = step list

(** `[i; j]` as `[Arg i; Arg j]` — A2 §1.7's `int list` paths (D1). *)
val args : int list -> path

(** "0.2" / "0.*.1"; for messages and the receipt, never an identity. *)
val path_to_string : path -> string

type field =
  | Cid_field of path
  (** a tag-8 `bytes` frame of exactly 32 bytes that IS an address (finding R1) *)
  | Ref_field of path * E4_kind.t option
  (** a tag-11 `ref` frame; the kind is the one the shape fixes, or None when the shape
          says `AnyRef` *)
  | Stamp of path
  (** a tag-8 `bytes` frame of exactly 32 bytes that names NOTHING in the store: an
          `engine` manifest digest, a `spanDigest`, a `stores` digest *)
  | Data_field of path (** deliberately not an address (D2) *)

val field_path : field -> path

type cls =
  | Cls_cid
  | Cls_ref of E4_kind.t option
  | Cls_stamp
  | Cls_data
  | Cls_unknown
  (** the row does not classify this path: a `Shared`, `Unused` or `Tombstoned` kind, or a
          path the row does not mention *)

type status =
  | Frozen (** one carrier; the row is its shape *)
  | Shared of string list (** finding R1': several carriers share the byte *)
  | Unused (** registered, no carrier today *)
  | Tombstoned (** fiber (15) *)
  | Pending
  (** 16..23: no Lean carrier yet; the shape is cas-design §4's / A2 §1.9's, or, for a
          checkpoint, the payload `E4_checkpoint` writes *)

type row =
  { kind : E4_kind.t
  ; status : status
  ; carriers : string list
    (** the Lean declarations that file under this byte, for provenance *)
  ; fields : field list (** empty unless [status] is [Frozen] or [Pending] *)
  ; note : string (** why the row is what it is; printed by the receipt, never parsed *)
  }

type t

(** The transcribed table (SH2, SH4). *)
val table : t

(** One row per `E4_kind.all`, in byte order. *)
val rows : t -> row list

val row : t -> E4_kind.t -> row
val status_of : t -> E4_kind.t -> status
val fields_of : t -> E4_kind.t -> field list
val class_at : t -> E4_kind.t -> path -> cls

(** 32: the length a Cid, a Ref digest and a Stamp all share (finding R1). *)
val cid_length : int

(* ---- resolving a path over payload bytes ---- *)

(** Every frame the path reaches, as `(tag, payload_start, payload_end)`, in tree order.  `[]`
    when the path does not resolve or the payload is not a well-formed frame tree (SH5, SH6). *)
val resolve : payload:string -> path -> (int * int * int) list

(* ---- the queries the repository needs ---- *)

(** What `pin_all` and `by_cid` need (A2 §1.8).  `[]` for every kind whose row has no
    `Cid_field`, which today is every kind except `job` (SH2). *)
val cids_of : t -> E4_kind.t -> payload:string -> E4_addr.Cid.t list

(** The TABLE's refs — a subset of `E4_node.scan_refs`, which is the exact answer (SH1). *)
val refs_of : t -> E4_kind.t -> payload:string -> E4_addr.Ref.t list

(** The 32-byte digests that name nothing.  They are listed so that a caller can see they were
    considered and rejected, never so that they can be followed. *)
val stamps_of : t -> E4_kind.t -> payload:string -> string list

type mismatch =
  { m_kind : E4_kind.t
  ; m_at : path
  ; m_reason : string (** "no such path" | "tag 5, want 8" | "bytes 17, want 32" | ... *)
  }

val mismatch_to_string : mismatch -> string

val cids_of_checked
  :  t
  -> E4_kind.t
  -> payload:string
  -> (E4_addr.Cid.t list, mismatch) result

val refs_of_checked
  :  t
  -> E4_kind.t
  -> payload:string
  -> (E4_addr.Ref.t list, mismatch) result

(** SH3, D4: a refusal of the QUERY, never of admission. *)
val stamps_of_checked : t -> E4_kind.t -> payload:string -> (string list, mismatch) result
