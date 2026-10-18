(* E4_kind — the kind byte of a node, transcribed from `Effect4.Store.Kind`
   (src/Effect4/Store/Carrier/Kind.lean).

   What it is: the second byte of every node (`Node.encode`, src/Effect4/Store/Domain/Node.lean:
   version :: kind.byte :: spec ++ payload), as an OCaml sum.  Bytes are identity: appended,
   never renumbered, never reused after retirement.  This module TRANSCRIBES Lean's table; it
   never mints a byte.

   One table: bytes 1..23 are Lean's `Kind.byte`, `Kind.name`, `Kind.all`, `Kind.ofByte?` and
   `Kind.ofName?`.  Bytes 16..23 (job 16, tape 17, log 18, exits 19, receipt 20, checkpoint 21,
   profile 22, table 23) are the CAS append that DI-25 rules (docs/DESIGN-ISSUES.md), and the
   sentinel 127 is Lean's `Kind.sentinel`, reserved forever and never a kind.  Every kind has a
   Lean-cut golden node, `g1-kind-<name>` in ../goldens.

   Depends on: the OCaml standard library only.

   Behaviours:
   K1  `byte` is exactly Lean's `Kind.byte` for 1..23; `of_byte (byte k) = Some k` and
       `of_byte b = Some k -> byte k = b`; `all` is in byte order and has 23 entries; `byte` and
       `name` are injective.        tested (test_bytes K1, and one Lean-cut node per kind)
   K2  0 is the version byte and never a kind; 127 is the sentinel, reserved forever, never a
       kind (amendment M4).  `of_byte 0 = None`, `of_byte 127 = None`, and every byte outside
       1..23 — negative, 24..126, 128..255 — is None: an unregistered byte is a REFUSAL, never
       a repair and never a fresh kind (Lean's `Kind.byte_ne_sentinel`).  by construction; tested
   K3  `Fiber` (15) is a tombstone: `tombstoned Fiber = true`, it is never minted by this
       estate, and its byte is never reused.                                by construction
   K4  Run-relative kinds are exactly Tape, Log, Exits, Checkpoint (amendment M2); every other
       kind is a content kind, and a content kind refuses a payload carrying a handle frame
       (tag 12) — the test itself is `E4_node.handle_in_content`.  tested (kind half here)
   K5  `name` is Kind.name's spelling (lowercase ASCII) and `of_name` is case-SENSITIVE:
       `of_name "Export" = None`, as Lean's guard says.                     tested
   K6  `is_interior` is Chunk alone: an interior node is never a root index entry
       (2026-09-07-ocaml-ecosystem-survey.md #20).                          by construction

   No deviation from docs/research/2026-09-08-engine-a2-persistence.md §1.1 beyond the
   `Properties:`/`Behaviours:` rename that §1 asks for on landing, and one added predicate,
   `is_registered`. *)

type t =
  (* 1..23 — Lean's `Kind`, in byte order; 16..23 are the CAS append (DI-25) *)
  | Source | Export | Type | Schema | Program | Annotation | Entry | Query | Result
  | Chunk | Tree | Manifest | Component | Vector | Fiber
  | Job | Tape | Log | Exits | Receipt | Checkpoint | Profile | Table

val all : t list
(** In byte order; 23 entries. *)

val byte : t -> int
(** 1..23. *)

val of_byte : int -> t option
(** None for every unregistered byte, 0 and 127 included (K2). *)

val name : t -> string
(** "source" … "table" — Lean's `Kind.name`. *)

val of_name : string -> t option
(** Case-sensitive (K5). *)

val sentinel : int
(** 127: never a kind, reserved forever; the unregistered-kind test byte (Lean's
    `Kind.sentinel`, DI-25). *)

val version_byte : int
(** 0: the first byte of every node, and never a kind. *)

val is_registered : int -> bool
(** `of_byte b <> None`. *)

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
