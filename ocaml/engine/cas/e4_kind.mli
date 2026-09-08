(* E4_kind — the kind byte of a node, transcribed from src/Effect4/Store/Kind.lean.

   What it is: the second byte of every node
   (`Node.encode = version :: kind.byte :: spec ++ payload`, src/Effect4/Store/Node.lean:170-171),
   as an OCaml sum.  Bytes are identity: appended, never renumbered, never reused after
   retirement.  This module TRANSCRIBES Lean's table; it never mints a byte.

   Two provenances, and the line between them is load-bearing:
     * bytes 1..15 are Lean's today — `Kind.byte` (src/Effect4/Store/Kind.lean:60-75),
       `Kind.name` (:78-93), `Kind.all` (:96-98), `Kind.ofByte?` (:101), `Kind.ofName?` (:104),
       and the ten `#guard`s at :145-158.  `in_lean` is true exactly for these.
     * bytes 16..23 are RESERVED AND NOT IN LEAN YET: job 16, tape 17, log 18, exits 19,
       receipt 20, checkpoint 21, profile 22 are CAS commit 1's append
       (docs/research/2026-09-08-cas-amendments.md §2 row 1; 2026-09-07-cas-design.md §4), and
       table 23 is amendment M17's ordinal ledger / KeyTable node under the coordinator's
       applied default for A2 owner question OQ3 (2026-09-08-engine-a2-persistence.md:1409).
       `in_lean` is false for all eight.  A golden cut from today's Lean can only pin 1..15;
       a node filed at 16..23 by this estate before CAS commit 1 lands would be a byte Lean
       refuses, so nothing mints one until then.

   Depends on: the OCaml standard library only.

   Behaviours:
   K1  `byte` is exactly Kind.byte for 1..15 and the CAS append for 16..23; `of_byte (byte k)
       = Some k` and `of_byte b = Some k -> byte k = b`; `all` is in byte order and has 23
       entries; `byte` and `name` are injective.                            tested
   K2  0 is the version byte and never a kind; 127 is the sentinel, reserved forever, never a
       kind (amendment M4).  `of_byte 0 = None`, `of_byte 127 = None`, and every byte outside
       1..23 — negative, 24..126, 128..255 — is None: an unregistered byte is a REFUSAL, never
       a repair and never a fresh kind.                          by construction; tested
   K3  `Fiber` (15) is a tombstone: `tombstoned Fiber = true`, it is never minted by this
       estate, and its byte is never reused.                                by construction
   K4  Run-relative kinds are exactly Tape, Log, Exits, Checkpoint (amendment M2); every other
       kind is a content kind, and a content kind refuses a payload carrying a handle frame
       (tag 12) — the test itself is `E4_node.handle_in_content`.  tested (kind half here)
   K5  `name` is Kind.name's spelling (lowercase ASCII) and `of_name` is case-SENSITIVE:
       `of_name "Export" = None` (Kind.lean:158).                           tested
   K6  `is_interior` is Chunk alone: an interior node is never a root index entry
       (2026-09-07-ocaml-ecosystem-survey.md #20).                          by construction

   No deviation from docs/research/2026-09-08-engine-a2-persistence.md §1.1 beyond the
   `Properties:`/`Behaviours:` rename that §1 asks for on landing, and three added
   predicates — `in_lean`, `is_registered`, `lean_max_byte` — which carry the provenance line
   above so a caller can gate on it instead of hard-coding 15. *)

type t =
  (* 1..15 — src/Effect4/Store/Kind.lean:60-75, in that order *)
  | Source | Export | Type | Schema | Program | Annotation | Entry | Query | Result
  | Chunk | Tree | Manifest | Component | Vector | Fiber
  (* 16..22 — cas-design §4; 23 — amendment M17.  Reserved, not in Lean yet. *)
  | Job | Tape | Log | Exits | Receipt | Checkpoint | Profile | Table

val all : t list
(** In byte order; 23 entries. *)

val byte : t -> int
(** 1..23. *)

val of_byte : int -> t option
(** None for every unregistered byte, 0 and 127 included (K2). *)

val name : t -> string
(** "source" … "table" — the printer of Kind.lean:78-93. *)

val of_name : string -> t option
(** Case-sensitive (K5). *)

val sentinel : int
(** 127: never a kind, reserved forever; the unregistered-kind test byte (amendment M4). *)

val version_byte : int
(** 0: the first byte of every node, and never a kind. *)

val lean_max_byte : int
(** 15: the highest byte Lean's Kind.lean carries today. *)

val is_registered : int -> bool
(** `of_byte b <> None`. *)

val in_lean : t -> bool
(** True for bytes 1..15; false for the reserved append 16..23 (see the header). *)

val tombstoned : t -> bool
(** Fiber (15) alone. *)

val is_run_relative : t -> bool
(** Tape | Log | Exits | Checkpoint — amendment M2. *)

val is_content : t -> bool
(** The complement of [is_run_relative]. *)

val is_interior : t -> bool
(** Chunk alone (K6). *)

val equal : t -> t -> bool
val compare : t -> t -> int
