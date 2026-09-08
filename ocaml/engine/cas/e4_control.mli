(* E4_control — the control file: the store's roots, its durable end, and its status.

   What it is: the ONLY mutable bytes in the CAS.  Written by tmp+rename under the writer
   lock; read by anyone.  It carries the roots plane (src/Effect4/Store/Store.lean:510-556)
   verbatim, the pack's durable end (`pack_end`), the index's coverage, a monotone
   `generation` and a reserved-tag `status` field.  The shape is irmin-pack's discipline as
   docs/research/2026-09-07-ocaml-ecosystem-survey.md row #4 transcribes it (`:243-278`,
   `version.ml` + `unix/control_file.ml`), and proposal 22: fixed-width ASCII version FIRST,
   the checksum computed over the payload with its own field ZEROED, `status` LAST so that
   everything before it sits at a fixed offset, reserved status tags a future writer may use
   and an old reader may tag-decode and preserve, and tmp-write + atomic rename.

   For 0.1 the roots plane lives ONLY here (A2 owner question OQ7), and it moves by
   compare-and-set on an optimistic version exactly as `Store.putRoot`
   (src/Effect4/Store/Store.lean:523-530).

   Depends on: E4_kind, E4_addr, E4_crc, E4_be (be64, from effect4_engine), unix.
   It writes no second framing writer and no hash of any kind: a CRC-32 here detects a torn
   or flipped byte and is never an identity (brief §2.2).

   ============================================================================
   The byte grammar (docs/research/2026-09-08-engine-a2-persistence.md §1.3, verbatim)

     control    := magic version payload
     magic      := "E4CAS\000"                        6   exact bytes
     version    := "00000001"                         8   ASCII, EXACT string match; never
                                                          parsed as a number
     payload    := be64 pack_end_seg                  8   payload offset  0
                   be64 pack_end_off                  8                   8
                   be64 index_end_seg                 8                  16
                   be64 index_end_off                 8                  24
                   be64 generation                    8                  32  monotone
                   be32 checksum                      4                  40  CRC-32 over the
                                                          whole payload with THIS field = 0
                   be32 scheme_version                4                  44  a store with
                                                          another scheme is refused
                   be32 ledger_generation             4                  48  M16/M17
                   be32 root_count                    4                  52
                   root * root_count                                     56
                   status                                                    MUST BE LAST
     root       := be16 name_len                      2   1 <= name_len <= 512
                   name                        name_len   lowercase ASCII only (amendment M8)
                   root_kind                          1   0 stdlib 1 journal 2 daemon
                                                          3 schema 4 char 5 registry 6 pin
                                                          (cas-design §6; Lean has 0..4 only,
                                                          Store.lean:47-53)
                   kind                               1   E4_kind.byte of the target's kind
                   digest                            32
                   be64 version                       8   Store.Root.version, the optimistic
                                                          version
     status     := status_tag                         1
                   status_body               to end-of-file
     status_tag := 0 Fresh | 1 Gced | 2 Imported | 3..15 reserved (never reuse)

   `status_body` is "the rest of the file" — that is what makes `status` last worth anything:
   a newer writer may give a reserved tag a body, and an older reader tag-decodes it, holds
   the bytes, and writes them back unchanged (CF3, the format-revision property).  Under
   version "00000001" the tags 0..2 carry an EMPTY body; a body at those tags, or a tag above
   15, is a refusal rather than a repair.

   The fixed part is therefore 6 + 8 + 56 = 70 bytes, plus 44 + name_len per root, plus 1 for
   the status tag.

   One consequence the survey argues at `:273-278` and this file makes operational: the ASCII
   version distinguishes a STALE BINARY (the version does not match) from CORRUPTION (the
   version matches and the checksum fails).  They are two different operator actions, so they
   are two different constructors of [open_error].

   ============================================================================
   Behaviours:
   CF1 Version first, in fixed-width ASCII, compared as a string.  An unknown version is
       `Stale_binary`, never a parse — and never `Corrupt`.            by construction; tested
   CF2 The checksum is CRC-32 over the payload with the checksum field zeroed, and it is
       verified BEFORE any field is parsed.  A payload that reaches the checksum and fails it
       is `Corrupt`, distinct from CF1.  Consequently every single-byte mutation of a
       well-formed file is a refusal: in the magic `Bad_magic`, in the version `Stale_binary`,
       anywhere after it `Corrupt`.                                                    tested
   CF3 `status` is the last field; every field before it is at a fixed offset given
       `root_count`.  Reserved tags 3..15 decode to `Reserved (tag, body)` with the body being
       the rest of the file, and are written back verbatim by a reader that does not
       understand them.                                              by construction; tested
   CF4 `commit` writes <path>.tmp, fsyncs it, renames onto <path>, then fsyncs the directory.
       A crash leaves either the old file or the new one, never a mixture; a torn or
       never-renamed tmp is not read by anyone, and `cleanup` removes it.  by construction;
                                                                                       tested
   CF5 `advance_root` is compare-and-set on the optimistic version exactly as `Store.putRoot`
       (Store.lean:523-530), in Lean's order: version, then resolution, then kind.  The move's
       version must equal `next_version name` (the resident's plus one, or 1 when absent),
       else `Stale_root`; the target must resolve, else `Dangling`; it must resolve at the
       root's kind, else `Wrong_kind`.  For a `Registry` root the new publication's `prev`
       must equal the root's current digest (`Addr.zero` when there is none), else `Fork`
       (amendment M7).                                                    tested: golden G3
   CF6 Root names are stored lowercase and looked up lowercase (amendment M8): `advance_root`
       lowercases, `root` and `next_version` lowercase what they are asked.
                                                                       by construction; tested
   CF7 `generation` is strictly increasing across changes: every function that returns a
       changed payload — `advance_root`, `set_pack_end`, `set_index_end`, `set_status`,
       `set_ledger_generation`, `bump` — increments it, and `commit` writes what it is given.
       A reader that re-reads and sees the same generation saw the same roots.
                                                                       by construction; tested
   CF8 Roots are head-first, as `Store.putRoot` conses (`:527`): the moved root is the head and
       the resident of that name is filtered out, so a name appears at most once and
       `roots` has the same order the Lean plane does.                     tested: golden G3
   CF9 Every be64 field is refused at or above 2^62 (amendment M9, the host limit): it is
       reported as a refusal, never misread.  `E4_be.read_be64` is the one that refuses, and
       it is the only side where the bound can bind: an OCaml int on this host holds
       -2^62 .. 2^62-1 (`E4_nat.max_nat`), so a writer cannot even hold such a field and
       `encode` refuses only a negative one.                            by construction; tested

   ============================================================================
   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.3 (lane P3,
   2026-09-08).  Nothing named in §1.3 is missing or renamed; the list is what §1.3 left open.

   D1  §1.3 declares an abstract `type t` and then types every function with `payload`, so `t`
       is unused there.  Here `type t = payload`: both names work and mean the same record,
       which is what the build lanes' prompt ("`roots`, `pack_end`/`set_pack_end`") assumes.
   D2  §1.3's CF5 says the M7 `prev` failure is `Stale_root`, but `root_error` carries a
       `Fork` constructor whose fields are exactly that failure's (`name`, `head`, `prev`).
       This lane answers `Fork`: the constructor exists for it, and §2.1 L-CAS-10 states the
       law as "the move is refused" without naming a constructor.  `Fork` is unreachable for
       any root kind other than `Registry`, and no Lean golden pins it — `RootKind`
       (Store.lean:47-53) has no `registry` and no `pin`, and lane GLD reports M7 and M1 as
       owed (2026-09-08-engine-lane-gld-delivery.md §4 O4).
   D3  `Corrupt of string` carries the reason.  §1.3 documents it as "the checksum failed",
       which is CF2's case, but a truncated or structurally impossible payload is corruption
       too and `open_error` has no other constructor for it; adding one would be a second
       operator action that does not exist.  The string is the reason, never the bytes.
   D4  Added, all of them derived and none of them new state: `t`, `initial`, `encode`,
       `decode`, `write` (= `commit`), `put_root` (= `advance_root`), the accessors `roots`,
       `pack_end`, `index_end`, `generation`, `scheme_version`, `ledger_generation`, `status`,
       the setters `set_pack_end`, `set_index_end`, `set_status`, `set_ledger_generation`,
       `bump`, the name normaliser `normalise_name`, the printers `root_kind_name`,
       `root_kind_index`, `root_kind_of_index`, `open_error_word`, `root_error_word`, and the
       constants `magic`, `version_string`, `filename`, `tmp_filename`, `max_name_length`,
       `fixed_payload_length`, `control_path`, `tmp_path`.  `encode`/`decode` are the grammar
       above with no I/O, which is what a crash test needs to build a file by hand.
   D5  `be16` (the root's name length) is written here.  E4_be carries be64 only and E4_crc
       be32 only; two bytes appear exactly once in the whole CAS grammar, in this file, so
       the reader and writer for them travel with it.
   D6  `encode` raises `Invalid_argument` on a payload it cannot represent — a name that is
       empty, longer than `max_name_length`, or not lowercase printable ASCII; a negative
       be64 field (CF9 says why the upper half cannot bind here); a be32 field outside
       0 .. 0xFFFFFFFF; a status tag outside 0..15;
       a non-empty body at a tag 0..2; a `Reserved` tag below 3.  A refusal to WRITE a
       nonsense file is a programming error, not an operator's; `advance_root` normalises so
       the normal path never reaches it.
   D7  The directory fsync of CF4 is best-effort: on a platform where a directory cannot be
       opened for fsync the `Unix_error` is swallowed and the rename still stands.  Every
       filesystem this engine targets (ext4 under WSL, A2 §6.1) supports it. *)

(* ---------------------------------------------------------------- the plane *)

type root_kind = Stdlib | Journal | Daemon | Schema | Char | Registry | Pin
(** `Store.RootKind` (src/Effect4/Store/Store.lean:47-53) for 0..4, extended by
    2026-09-07-cas-design.md §6 with `Registry` (5) and `Pin` (6), which Lean does not have. *)

type root = {
  name : string;  (** lowercase; CF6 *)
  root_kind : root_kind;
  kind : E4_kind.t;
  digest : E4_addr.Addr.t;
  version : int;
}
(** `Store.Root` (Store.lean:64-70), field for field. *)

type status = Fresh | Gced | Imported | Reserved of int * string
(** `Reserved (tag, body)`: 3 <= tag <= 15, and the body is whatever a future writer put
    after the tag.  Both are preserved verbatim on the next commit (CF3). *)

type payload = {
  pack_end : int * int;  (** seg, off — the pack's durable end (the watermark) *)
  index_end : int * int;  (** seg, off — what the index snapshot covers *)
  generation : int;  (** monotone; CF7 *)
  scheme_version : int;  (** scheme0.version; a store with another is refused *)
  ledger_generation : int;  (** the ordinal ledger's generation (M16/M17) *)
  roots : root list;  (** head-first, as Store.putRoot conses (CF8) *)
  status : status;  (** MUST BE LAST in the bytes *)
}

type t = payload
(** D1: one record, two names. *)

val initial : t
(** Everything zero, no roots, `Fresh`.  The payload a fresh store's first commit writes. *)

(* ---------------------------------------------------------------- constants *)

val magic : string
(** "E4CAS\000" — six bytes. *)

val version_string : string
(** "00000001" — eight ASCII bytes, compared as a string and never parsed (CF1). *)

val filename : string
(** "control". *)

val tmp_filename : string
(** "control.tmp". *)

val max_name_length : int
(** 512. *)

val fixed_payload_length : int
(** 56: the payload bytes before the first root. *)

val control_path : dir:string -> string
(** <dir>/control. *)

val tmp_path : path:string -> string
(** <path>.tmp — the file `commit` writes before it renames (CF4). *)

(* ---------------------------------------------------------------- the bytes *)

type open_error =
  | Missing  (** no file at that path *)
  | Stale_binary of string  (** the ASCII version we could not match; CF1 *)
  | Corrupt of string  (** the checksum failed, or the payload could not hold; CF2, D3 *)
  | Bad_magic

val encode : payload -> string
(** The grammar above, checksum filled in.  Raises `Invalid_argument` on an unrepresentable
    payload (D6). *)

val decode : string -> (payload, open_error) result
(** The grammar above: magic, then version, then the checksum over the whole payload with its
    own field zeroed, then the fields (CF1, CF2). *)

val read : path:string -> (payload, open_error) result
(** `decode` of the file's bytes; `Missing` when there is no such file. *)

val commit : path:string -> payload -> unit
(** CF4: write <path>.tmp, fsync it, rename it onto <path>, fsync the directory.  The writer
    lock is the caller's (`<store>/LOCK`, A2 §1.0). *)

val write : path:string -> payload -> unit
(** = [commit]. *)

val cleanup : dir:string -> unit
(** Remove a stale <dir>/control.tmp — a tmp that was written but never renamed, torn or
    whole.  Called at open; it never touches `control` (CF4, crash family X4(a)). *)

(* ---------------------------------------------------------------- the plane, read *)

val root : payload -> string -> root option
(** `Store.root?` (Store.lean:513), lowercasing the name asked for (CF6). *)

val next_version : payload -> string -> int
(** `Store.nextVersion` (Store.lean:516-519): the resident's version plus one, or 1 when the
    name is absent.  Lowercases the name asked for (CF6). *)

val roots : t -> root list
(** The plane, head-first (CF8). *)

val pack_end : t -> int * int
val index_end : t -> int * int
val generation : t -> int
val scheme_version : t -> int
val ledger_generation : t -> int
val status : t -> status

(* ---------------------------------------------------------------- the plane, moved *)

type root_error =
  | Stale_root of { name : string; expected : int; actual : int }
      (** the move's version was not `next_version name` *)
  | Dangling of E4_addr.Addr.t  (** the target resolved to nothing *)
  | Wrong_kind of { at : E4_addr.Addr.t; expected : E4_kind.t; actual : E4_kind.t }
  | Fork of { name : string; head : E4_addr.Addr.t; prev : E4_addr.Addr.t }
      (** a `Registry` root whose new publication's `prev` is not the resident digest (M7, D2) *)

val advance_root :
  payload ->
  resolve:(E4_addr.Addr.t -> E4_kind.t option) ->
  ?prev:E4_addr.Addr.t ->
  root ->
  (payload, root_error) result
(** CF5, CF6, CF7, CF8.  [resolve] is the store's kind lookup — the node at that address and
    the kind it is filed under, or None — which is lane P4's; this module never touches a
    node.  [prev] is required for a `Registry` root and ignored for every other kind; absent
    means `Addr.zero`, which is what a first publication carries. *)

val put_root :
  payload ->
  resolve:(E4_addr.Addr.t -> E4_kind.t option) ->
  ?prev:E4_addr.Addr.t ->
  root ->
  (payload, root_error) result
(** = [advance_root]. *)

(* ---------------------------------------------------------------- the watermark *)

val set_pack_end : t -> int * int -> t
(** The `pack_end` watermark: the durable end of the pack after the last commit.  Bumps
    `generation` (CF7). *)

val set_index_end : t -> int * int -> t
val set_status : t -> status -> t
val set_ledger_generation : t -> int -> t

val bump : t -> t
(** `generation` + 1 and nothing else (CF7). *)

(* ---------------------------------------------------------------- names and words *)

val normalise_name : string -> string
(** Lowercase (CF6).  ASCII only, so this is `String.lowercase_ascii`. *)

val valid_name : string -> bool
(** 1 .. `max_name_length` bytes, printable ASCII, no uppercase (amendment M8). *)

val root_kind_index : root_kind -> int
(** 0..6 — the byte the grammar writes, and `rootKindIndex` in the goldens' `rootVal`
    projection (2026-09-08-engine-lane-gld-delivery.md §2). *)

val root_kind_of_index : int -> root_kind option
val root_kind_name : root_kind -> string
val status_tag : status -> int

val open_error_word : open_error -> string
(** A one-line operator word: "missing", "badMagic", "staleBinary <version>",
    "corrupt <reason>". *)

val root_error_word : root_error -> string
(** The Lean `Admission` vocabulary, verbatim, so a golden's `expected` column can be compared
    as a string: "staleRoot <name> <expected> <actual>", "wrongKind", "dangling <hex>", and
    "fork <name> <head hex> <prev hex>" for the M7 refusal Lean does not have (D2).  The `ok`
    word is the caller's — it is not an error. *)
