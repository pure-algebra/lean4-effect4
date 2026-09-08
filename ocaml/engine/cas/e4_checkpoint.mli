(* E4_checkpoint — a machine state as content: the run-relative node a parked machine becomes,
   the chunked image behind it, the `prev` chain, and the reader that gets it back.

   What it is: amendment M2 makes a checkpoint a RUN-RELATIVE kind (byte 21).  Its payload
   carries the job it is a checkpoint OF, the position on that job's tape, the previous
   checkpoint of the same job, a digest stamp over the image, and the image itself — whole
   below `E4_chunk.threshold` and as a manifest of `chunk` nodes above it, which is the only
   way two consecutive checkpoints share bytes (A2 §4.4; E4_chunk).

   THE LAW THIS MODULE EXISTS FOR (A2 §1.4, L-LOG-3, LAW LOG-REL):

     A checkpoint's address is a function of (job, position) and of the machine content, and
     of NOTHING the host chose.  No field names a segment file, a byte offset, a wall clock, a
     domain id, a process id or the insertion order of any host structure.  Two hosts
     replaying one tape to one position produce byte-identical checkpoints; two different
     positions are two different addresses; two different jobs differ in the job field alone.

   Everything below is arranged so that law is readable off the bytes: `write` derives every
   byte of the payload from its arguments, `E4_chunk.cut` is a function of the image alone,
   and the schema edge is a fixed node this module mints.

   ============================================================================
   PENDING: CAS COMMIT 7 (risk R6, A2 §5.2).  The run-relative payload shapes —
   `checkpoint`/`job`/`tape`/`log` — DO NOT EXIST IN LEAN YET.  So the checkpoint's bytes here
   are an ENGINE-SIDE canonical image: the machine's persistent carriers rendered through the
   SAME frame grammar `E4_be` and `Eff_frame` use, in the fixed order documented below, under
   a schema node this module mints and marks pending.  THE RULE, written here so it is not
   lost: when CAS commit 7 lands, `image_of_machine`'s encoder is REPLACED by the Lean-blessed
   image, `schema_payload`'s marker becomes the blessed schema's address, and golden G8 pins
   both.  Nothing outside this file changes, because nothing outside this file reads the
   image's bytes.  Until then `image_version` is 0 and `pending` is true.

   ============================================================================
   THE BYTE TABLE — a checkpoint node's payload (kind 21, `checkpoint`).  One `Val` frame tree
   in the framing of src/Effect4/Store/Canonical.lean, written through `E4_be.framed` and
   nothing else; the tag alphabet is `Eff_frame`'s (bool 1, nat 2, string 3, list 4, pair 5,
   none 6, some 7, bytes 8, unit 9, ctor 10, ref 11, handle 12).

     checkpoint payload := ctor 0
       [ ref  job          ]  tag 11: kind byte 16 (`job`)   ++ 32-byte address   — a CHECKED EDGE
       [ nat  position     ]  tag  2
       [ opt  tape_prefix  ]  tag 6, or tag 7 [ ref kind 17 ] — a CHECKED EDGE when present
       [ opt  prev         ]  tag 6, or tag 7 [ ref kind 21 ] — a CHECKED EDGE when present
       [ bytes engine      ]  tag  8, 32 bytes: sha256 of the image.  A STAMP, never an edge
       [ nat  image_length ]  tag  2
       [ image             ]  ctor 0 [ bytes image        ]   whole
                            | ctor 1 [ list [ ref chunk ] ]   chunked, one level
                            | ctor 2 [ ref manifest       ]   chunked, through a manifest tree

     ctor  := tag 10, be64 len, [ nat index ] ++ args      nat := tag 2, be64 len, digits
     ref   := tag 11, be64 33,  kind byte ++ 32 bytes      opt := tag 6 | tag 7, be64 len, frame

   Three consequences worth naming.  (1) `job`, `tape_prefix` and `prev` are `ref` frames, so
   `E4_node.refs` finds them and `E4_cas` checks them: a checkpoint whose job, tape prefix or
   predecessor is not stored is refused `Dangling` BY THE STORE, not by a check here (CP2,
   L-CP-1).  (2) `engine` is a `bytes` frame, which `Val.refs` treats as a leaf
   (Node.lean:250), so it is a stamp and never an edge — and a byte scan cannot tell it from a
   `Cid`, which is why `E4_shape` exists (A2 §1.7, risk R1).  (3) The image is the LAST field,
   so every field before it sits at a fixed offset given the three optional refs.

   THE BYTE TABLE — the machine image (`image_of_machine`), pending as above.  `Fast.t`'s
   persistent carriers are reachable only through the free rows of `E4_engine.ENGINE`, and
   this is those rows in a fixed, documented order.  Every string field is a `bytes` frame,
   not a `string` frame, because a `string` frame carries Eff_frame's UTF-8 rule and a
   rendered carrier row is not promised to be UTF-8:

     image := ctor 0
       [ nat   image_version ]  0 while pending
       [ bytes carriers      ]  ENGINE.carriers — which instance produced it
       [ nat   fuel          ]
       [ bytes outcome       ]
       [ bytes answer        ]  the four-letter alphabet with its frontier, rendered
       [ nat   fiber_count   ]
       [ nat   trace_length  ]
       [ opt   root_exit     ]  none | some (bytes)
       [ list  exits         ]  pair (nat fiber, bytes exit), in ENGINE order
       [ list  fiber_rows    ]  pair (nat fiber, bytes row),  in ENGINE order
       [ list  trace_rows    ]  bytes, in trace-index order — the reading axis
       [ list  refs          ]  bytes, ascending by cell key
       [ bytes store_row     ]

   ============================================================================
   Depends on: E4_cas, E4_chunk, E4_node, E4_addr, E4_kind, E4_control, E4_wal, E4_be,
   E4_sha256, E4_engine (ocaml/engine), Eff_frame (ocaml/eff, read-only).

   Behaviours:
   CP1 / LAW LOG-REL  A checkpoint's bytes are a function of (job, position, tape prefix,
       prev, image) and of nothing else.  Two stores with different segment layouts, different
       index states and different insertion orders give one address; two positions give two
       addresses; two jobs differ in the 32 bytes of the job field and in nothing else.
                                                             by construction; tested (LOG-REL)
   CP2 / L-CP-1  `write` refuses unless the job — and the tape prefix and the predecessor when
       given — are already stored at their kinds.  The refusal is the store's own `Dangling`
       or `Wrong_kind`, not a check here.                                    tested
   CP3  The `prev` chain is checked at PUBLISH: the head root `runs/<job hex>/checkpoint` is a
       `Registry` root, so `E4_control.advance_root ~prev` refuses a move whose `prev` is not
       the resident head with `Fork` (amendment M7), and a racing publisher gets `Stale_root`
       and retries.                                                          tested
   CP4  Handles inside the image are allocation indices of a replay of `job` from a fresh
       load (M2), and nothing else in the image is host-relative: every field of the image is
       a free row of `E4_engine.ENGINE`, which is a pure function of a machine VALUE holding
       no mutable structure (brief §2.3).                                    by construction
   CP5  With chunking on the image is recoverable byte for byte:
       `read (write .. image) = image`, and `E4_chunk.reassemble` of the manifest's chunks is
       the image.                                                            tested (P5)
   CP6  Consecutive checkpoints of one job share every chunk they have in common, by digest:
       the store's `Duplicate` outcome IS the sharing (E4_cas CS1).  Measured over 64
       consecutive checkpoints of the chain-of-refMake run at n = 2000: the machine image
       grows by APPENDING (the trace and the ref heap of position i are prefixes of position
       i+1's, checked), and at the closed-form average the last checkpoint cuts 34 chunks of
       which 30 are `Duplicate`, the store holding 769 472 B against the whole blob's
       3 428 148 B.  READ `E4_chunk.default`'s note before quoting a ratio: the win is a
       function of `avg` against the image SIZE, and the 64 MB default buys nothing at all on
       a 100 KB image.                                             benched (B7); tested
   CP7  `read` VERIFIES.  It re-reads every chunk, re-concatenates and re-hashes, and refuses
       unless the length and the sha256 match the payload's `image_length` and `engine`.  A
       flipped byte in a chunk record is caught by the pack's CRC first and by this hash if
       anyone repairs the CRC — the checkpoint is never handed back half-right.  tested
   CP8  `chain` walks `prev` from a head to the first checkpoint, refuses a cycle instead of
       looping, and is bounded by the store's node count.  A cycle is unreachable through
       `write` — it would need a sha256 fixed point — so `chain_from` exposes the walk over an
       arbitrary `prev_of` and that is what the cycle test forges.           tested
   CP9 / risk R8  `closure_streaming` never materialises the image: it walks the checked edges
       of a chunk-bearing root children-first, holding one node's bytes and a stack of
       addresses, and visits exactly the addresses `E4_cas.closure` visits.  tested
   CP10 An EPHEMERAL checkpoint is not a node (L-CP-2, cas-design §8): `ephemeral` writes a
       `Checkpoint_mark` row with no address into the job's WAL and files nothing.  tested
   CP11 `image_of_machine` and `machine_of_image` round-trip exactly: `machine_of_image
       (image_of_machine m) = Some (machine_state m)`, and re-encoding that state gives the
       same bytes.  `machine_of_image` is exact — a trailing byte, a wrong ctor index, a
       missing field and a wrong tag are refusals, never partial reads.      tested

   ============================================================================
   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.9 and from the lane
   prompt (lane P6, 2026-09-08):
   D1  The prompt writes `read`, `chain` and `closure_streaming` on `E4_cas.t`.  They are on
       `E4_cas.ro` here, because that is the type `E4_cas`'s read functions take and
       `E4_cas.read_only : t -> ro` is its own bridge (E4_cas D4).  A writer calls
       `read (E4_cas.read_only s) a`; `ro` is strictly the more general choice.
   D2  `write` answers `(Addr.t, write_error) result`, not `Addr.t`: filing a checkpoint can
       be refused by admission (an unstored job) or by the roots plane (a `Fork` on the head),
       and neither is an exception this lane may invent.  `write_exn` is the prompt's exact
       shape and raises `Write_refused`.
   D3  §1.9's `image` is `Whole of string | Chunked of Ref.t list`.  A third case,
       `Manifested of Ref.t`, carries A2 §4.4's lever 3 (the two-level manifest), without
       which the manifest of a large image is itself rewritten whole on every checkpoint —
       139 KB against ~10 KB at 64 MB.  `Chunked` is still written when one leaf holds the
       level and the caller asks for it (`~manifest:false`).
   D4  §1.9's `tape_prefix : Ref Tape` is `tape_prefix : Ref.t option`.  CAS commit 7 has not
       landed, there is no `tape` node for a run to name, and a required-but-unfilled ref
       would make every checkpoint refuse.  The FIELD is in the grammar so the shape does not
       move when commit 7 lands; the option is what is pending.
   D5  §1.9's `engine : Digest` is documented there as "the manifest digest".  Here it is
       `sha256 image` — the stamp CP7 verifies against.  With the manifest form the manifest's
       own address is already a checked edge, so a second copy of it would be a stamp that
       proves nothing; the image's digest is what a reader cannot otherwise check.
   D6  Pins at publish (amendment M1, L-CAS-11) go through `advance_root` with
       `root_kind = Pin` over the address `write` JUST produced, not through
       `E4_cas.pin_all`.  M1's mechanism is "a pin root over the node address `by_cid` finds
       for the Cid" and that address is exactly this one, so the root minted is the same root;
       what is skipped is the lookup.  A FINDING for the coordinator: lane P4's `by_cid` is a
       full scan that re-hashes every resident payload (e4_cas.ml:590-598, its D5), so
       `pin_all` at every checkpoint is O(store bytes) per publish and is unusable on a store
       holding thousands of chunk nodes.  `~pin_via_cid:true` takes the literal M1 path and
       the test checks the two mint the same root.
   D7  This module mints its own schema node (`ensure_schema`) and uses its address as the
       spec of every node it files.  Edge 0 of a non-genesis node is checked
       (`Node.checkedEdges`, Node.lean:297), so a checkpoint needs a resident schema; Lean's
       genesis is a 90 KB node this lane will not transcribe, and the blessed run-relative
       schema is CAS commit 7's.  The node minted is a genesis in the exact sense the store
       means — kind `schema`, the zero spec — so it is admitted with no edge of its own, and
       its payload names the pending version so the address changes when the shape does.
   D8  Added beside §1.9's list, each of them a reading of the same bytes: `payload_of` /
       `t_of_payload` (= `encode` / `decode`), `read_parts` (the prompt's four-field answer),
       `chain_from`, `closure_fold`, `image_bytes`, `machine_state`, `Of_engine`,
       `schema_node` / `schema_address` / `ensure_schema`, `head_root_name`, `pin_root_name`,
       `image_version`, `pending`, and the printers `write_error_word` / `read_error_word`. *)

open Effect4_engine
(* E4_engine — `Fast.t` is the machine value the image is taken of (A1 §5, EN5). *)

(* ---------------------------------------------------------------- the node *)

type image =
  | Whole of string  (** ctor 0: the image inline, below `E4_chunk.threshold` *)
  | Chunked of E4_addr.Ref.t list  (** ctor 1: chunk refs, in image order *)
  | Manifested of E4_addr.Ref.t  (** ctor 2: the root of a manifest tree (D3) *)

type t = {
  job : E4_addr.Ref.t;  (** kind `job` *)
  position : int;
  tape_prefix : E4_addr.Ref.t option;  (** kind `tape`; pending, D4 *)
  prev : E4_addr.Ref.t option;  (** kind `checkpoint` *)
  engine : E4_addr.Addr.t;  (** sha256 of the image; a stamp, never an edge (D5) *)
  image_length : int;
  image : image;
}

val encode : t -> string
(** The payload bytes, in the byte table at the head of this file. *)

val decode : string -> t option
(** Exact: a trailing byte, a wrong ctor index, a ref at the wrong kind, a missing field and
    an `engine` that is not 32 bytes are all refusals. *)

val payload_of : t -> string
val t_of_payload : string -> t option

val node : spec:E4_addr.Addr.t -> t -> E4_node.t
(** The checkpoint node itself: version 0, kind `checkpoint`, this spec, `encode t`. *)

(* ---------------------------------------------------------------- the pending schema (D7) *)

val image_version : int
(** 0 — the engine-side image's version while CAS commit 7 is owed. *)

val pending : bool
(** true until the run-relative shapes are Lean's.  Read it in a report, not in a branch. *)

val schema_payload : string
val schema_node : E4_node.t
(** kind `schema`, the zero spec — a genesis in the store's sense, so it is admitted with no
    edge of its own.  Its payload names the pending version. *)

val schema_address : E4_addr.Addr.t
val ensure_schema : E4_cas.t -> E4_addr.Addr.t
(** File the schema node if it is not resident and answer its address.  Staged, not durable. *)

(* ---------------------------------------------------------------- the roots *)

val head_root_name : E4_addr.Addr.t -> string
(** `runs/<job hex>/checkpoint` — a `Registry` root, so the `prev` check of amendment M7
    applies to it (CP3). *)

val pin_root_name : job:E4_addr.Addr.t -> E4_addr.Cid.t -> string
(** `runs/<job hex>/pin/<cid hex>` — lane P4's `pin_all` name (E4_cas D8), so the pin this
    module mints is the root `pin_all` would have minted (D6). *)

(* ---------------------------------------------------------------- writing *)

type write_error =
  | Refused of E4_cas.admission  (** the store refused the checkpoint node *)
  | Chunk_refused of string  (** the store refused a chunk or manifest node *)
  | Root_refused of E4_control.root_error  (** the head root or a pin *)

val write_error_word : write_error -> string

exception Write_refused of string

val write :
  E4_cas.t ->
  job:E4_addr.Addr.t ->
  position:int ->
  machine_image:string ->
  prev:E4_addr.Addr.t option ->
  ?params:E4_chunk.params ->
  ?threshold:int ->
  ?manifest:bool ->
  ?tape_prefix:E4_addr.Addr.t ->
  ?pin:bool ->
  ?pin_via_cid:bool ->
  ?head:bool ->
  unit ->
  (E4_addr.Addr.t, write_error) result
(** Chunk the image above [threshold] (default `E4_chunk.threshold`), stage every chunk and
    manifest node and the checkpoint node, GROUP-COMMIT them in one `E4_cas.commit`, mint the
    pin root (M1, D6) and advance the head root `runs/<job hex>/checkpoint` with the `prev`
    check (CP3).  [prev] is the previous checkpoint's address, or None for the first.
    [manifest] (default true) chooses the two-level form; [pin] and [head] (both default true)
    turn off the roots for a caller that is only measuring bytes. *)

val write_exn :
  E4_cas.t ->
  job:E4_addr.Addr.t ->
  position:int ->
  machine_image:string ->
  prev:E4_addr.Addr.t option ->
  E4_addr.Addr.t
(** The prompt's shape (D2).  @raise Write_refused *)

type written = {
  addr : E4_addr.Addr.t;
  chunks_cut : int;
  chunks_fresh : int;
  chunks_dup : int;
  manifest_nodes : int;
  manifest_fresh : int;
  manifest_dup : int;
  payload_bytes : int;
  image_bytes_written : int;  (** the image's own length, chunked or not *)
}

val write_counted :
  E4_cas.t ->
  job:E4_addr.Addr.t ->
  position:int ->
  machine_image:string ->
  prev:E4_addr.Addr.t option ->
  ?params:E4_chunk.params ->
  ?threshold:int ->
  ?manifest:bool ->
  ?tape_prefix:E4_addr.Addr.t ->
  ?pin:bool ->
  ?pin_via_cid:bool ->
  ?head:bool ->
  unit ->
  (written, write_error) result
(** `write` with the sharing counts A2 §4.4 and bench cell B7 are about. *)

(* ---------------------------------------------------------------- reading *)

type read_error =
  | Absent of E4_addr.Addr.t
  | Not_a_checkpoint of E4_kind.t
  | Bad_payload
  | Missing_chunk
  | Image_mismatch of { expected : E4_addr.Addr.t; actual : E4_addr.Addr.t }
  | Length_mismatch of { expected : int; actual : int }

val read_error_word : read_error -> string

val image_bytes : E4_cas.ro -> t -> string option
(** The image behind a decoded checkpoint: inline, from its chunks, or through its manifest.
    It does NOT verify — `read` is what verifies (CP7). *)

val read : E4_cas.ro -> E4_addr.Addr.t -> (t * string, read_error) result
(** The checkpoint and its image, VERIFIED (CP7): the image is reassembled, its length is
    checked against `image_length` and its sha256 against `engine`. *)

val read_parts :
  E4_cas.ro ->
  E4_addr.Addr.t ->
  (E4_addr.Addr.t * int * E4_addr.Addr.t option * string, read_error) result
(** The prompt's four-field answer: (job, position, prev, image). *)

val head : E4_cas.ro -> E4_addr.Addr.t -> E4_addr.Addr.t option
(** The head of `runs/<job hex>/checkpoint`, if the root is there. *)

(* ---------------------------------------------------------------- the chain *)

type chain_error = Cycle of E4_addr.Addr.t | Unreadable of E4_addr.Addr.t * read_error

val chain : E4_cas.ro -> E4_addr.Addr.t -> (E4_addr.Addr.t list, chain_error) result
(** The `prev` walk from this checkpoint back to the first, head first (CP8). *)

val chain_from :
  prev_of:(E4_addr.Addr.t -> E4_addr.Addr.t option) ->
  E4_addr.Addr.t ->
  (E4_addr.Addr.t list, chain_error) result
(** The same walk over an arbitrary predecessor function, so a cycle can be exhibited and
    refused in a test (CP8). *)

(* ---------------------------------------------------------------- the closure (R8) *)

val closure_streaming :
  E4_cas.ro -> E4_addr.Ref.t -> (E4_addr.Addr.t -> E4_node.t -> unit) -> unit
(** The checked-edge closure of a chunk-bearing root, children first, each address once,
    delivered one node at a time and never accumulated (CP9). *)

val closure_fold :
  E4_cas.ro -> E4_addr.Ref.t -> init:'a -> f:('a -> E4_addr.Addr.t -> E4_node.t -> 'a) -> 'a

val closure_size : E4_cas.ro -> E4_addr.Ref.t -> int * int
(** (nodes, node bytes) over the same walk, without holding a byte of it. *)

(* ---------------------------------------------------------------- ephemeral (CP10) *)

val ephemeral : E4_wal.t -> position:int -> unit
(** A `Checkpoint_mark` row with no address: a log row, never a CAS node (L-CP-2). *)

(* ---------------------------------------------------------------- the machine image *)

type machine_image = {
  mi_version : int;
  mi_carriers : string;
  mi_fuel : int;
  mi_outcome : string;
  mi_answer : string;
  mi_fiber_count : int;
  mi_trace_length : int;
  mi_root_exit : string option;
  mi_exits : (int * string) list;
  mi_fiber_rows : (int * string) list;
  mi_trace_rows : string list;
  mi_refs : string list;
  mi_store_row : string;
}
(** The free rows of `E4_engine.ENGINE` in the fixed order the byte table above gives. *)

val encode_image : machine_image -> string
val machine_of_image : string -> machine_image option
(** Exact (CP11). *)

module Of_engine (En : E4_engine.ENGINE) : sig
  val state : En.t -> machine_image
  val image : En.t -> string
end

val machine_state : E4_engine.Fast.t -> machine_image
val image_of_machine : E4_engine.Fast.t -> string
(** The pending canonical image of a `Fast` machine (CP11, and the PENDING note above). *)
