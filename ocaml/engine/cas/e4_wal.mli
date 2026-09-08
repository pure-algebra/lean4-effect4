(* E4_wal — the write-ahead log of one job: decision rows and event rows, in segments.

   What it is: where a job's tape and its event stream are durable before they are content
   (docs/research/2026-09-08-engine-a2-persistence.md §1.4, proposal 18 / survey #12).  A row
   is `be32 len :: be32 crc :: body`; a segment is a file under `<store>/log/<job-hex>/`
   named by the index of its first row; replay is from a checkpoint position plus the tail.
   This is the DURABLE SPINE.  A3's `E4_log` (ocaml/engine/query/e4_log.mli) is the in-memory
   projection over the same rows, and `replay` here is what feeds it at load; nothing else
   writes `E4_log`.

   A row body is an OPAQUE canonical byte string plus a row-kind byte.  This module never
   parses a decision, so it does not depend on today's decision alphabet (`evaluate`,
   `flush`, `fire:<o>`, `evaluate:<f>`, `answer:<f>:<t>:<n>` — src/Effect4/Api.lean,
   ocaml/link/e4_bridge.ml:75-80): the bytes a caller stages are the bytes replay returns,
   and they are the canonical bytes Lean would hash (brief §2.2).  `Event of string` stands
   until the `LogEvent` carrier exists (A2 risk R7 / knock-on C4); the framing above is
   defined without it, so the carrier's arrival changes no byte of this file's grammar.

   Depends on: E4_crc (the row and header checksums and the be32 field), E4_addr (the job's
   address), E4_be (be64 — A1's framing; never a second writer), unix.

   The grammar (A2 §1.4, transcribed):

     segment    := seg_head row*
     seg_head   := "E4LOG\000"        6
                   "00000001"         8   ASCII version, matched as a string, never parsed
                   job_lo             8   the LAST eight bytes of the job's address (D3)
                   be64 first_index   8   the index of this segment's first data row
                   be32 head_crc      4   CRC-32 over the 30 bytes before it
     row        := be32 row_len       4   the length of row_body; <= row_max (1 MiB)
                   be32 row_crc       4   CRC-32 over row_body
                   row_body    row_len
     row_body   := row_tag            1   1 Decision | 2 Event | 3 Checkpoint_mark | 4 Seal
                   be64 index         8   the row's (job, index) position
                   body        row_len - 9
     body       := (Decision, Event)         the opaque canonical bytes
                 | (Checkpoint_mark)         be64 position :: 0x00 | 0x01 ++ digest(32)
                 | (Seal)                    be64 next_first_index

   LAW LOG-REL (A2 §1.4, law L-LOG-3, brief §2.4 INV-TAPE-1).  Every position is
   `(job, index)`-relative and never a global sequence: indices count the DATA rows of one
   job from 0, and nothing a host chose — a segment file, a byte offset, a clock, a domain,
   a pid, a rotation point — is a function of them or is named by a row body.  Two hosts
   replaying one tape agree on every position and on every row byte.

   Behaviours:
   LG1 Rows are self-delimiting and checksummed; a torn or corrupt row ends the log and every
       row after it is discarded even if well formed — a gap is never repaired, and the
       verdict names the exact index.                                          tested
   LG2 Indices are contiguous from a segment's `first_index` with no gaps.  A missing middle
       segment, a renumbered row and a lost seal are reported `Gap {expected; found}` and
       stop replay; nothing is silently skipped.                               tested
   LG3 Group commit: `stage`/`append` buffer, `commit`/`sync` performs one write(2) and one
       fsync(2).  Rows in one commit are all durable or all absent, and `durable_upto` is the
       one number that says which.                       by construction; tested
   LG4 LAW LOG-REL: no row body names a segment, an offset, a clock, a domain or a pid — the
       row constructors have no such field — and the index a row is given is a function of
       the job's row sequence alone.  Two jobs staged the same rows have the same indices and
       byte-identical rows on disk; their segment headers differ only in `job_lo` (D3).
                                                          by construction; tested
   LG5 Rotation at `seg_max` bytes writes a `Seal` row carrying the next segment's
       `first_index` and consumes no index (D2).  An unsealed segment is the one that was
       open at a crash: reopening it truncates a torn tail to the last good row and appends
       from there.                                                             tested
   LG6 `replay ~from` opens the segment whose `[first_index, next first_index)` contains
       `from` by a binary search over the directory listing — O(log segments), never a full
       scan of the earlier ones.                          by construction; tested
   LG7 Single writer: one `t` per job directory, held by an in-process claim and by
       `lockf(F_TLOCK)` on `<job-dir>/LOCK`.  A second `open_` raises `Locked`.  A reader
       takes no lock and needs none: a row is only ever appended, never rewritten.  tested
   LG8 The row body is opaque and exact: `replay` returns the bytes `stage` was given, byte
       for byte, for every string including the empty one and one full of NULs.  tested
   LG9 A row body of more than `row_max` bytes is refused at `stage` with `Row_too_large` and
       never reaches the disk; a stored row whose length field exceeds it is `Oversize`,
       never misread.                                     by construction; tested

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.4 (lane P5, 2026-09-08):
   D1  `seq` is the (job, index) position of A2 §1.4's law, so this file uses the name
       `index` in its functions (`last_index`, `checkpoint_mark`, the build brief's words)
       and keeps `seq` as the type name of §1.4.  They are one thing.
   D2  A `Seal` consumes NO index, and `replay` does not deliver it to `f`.  §1.4 gives every
       row a `be64 seq` "strictly increasing, no gaps"; if a seal took an index, the index of
       every later row would be a function of `seg_max` — the rotation point — which LAW
       LOG-REL forbids and differential D3 (one tape, two segment layouts) would fail.  The
       seal's index field therefore carries `next_first_index` (equal to the index of the
       next data row), replay checks it against the running position, and a lost seal between
       two segments whose indices still meet is recovered rather than refused.  `stage` of a
       `Seal` raises `Invalid_argument`: rotation owns it.
   D3  `job_lo` is eight RAW bytes (the address's last eight), not a be64 number.  A be64 at
       or above 2^62 is a refusal on this host (E4_be.read_be64, M9), and one address in four
       has its top bit set, so a numeric reading would refuse one job in four.  The field is
       a self-identification guard: a segment under the wrong job's directory is `Wrong_job`.
   D4  `stop` gains `Bad_row`, `Oversize`, `Bad_header` and `Wrong_job` beside §1.4's four.
       They are damage §1.4's four cannot name — an unknown row tag, a length field past
       `row_max`, a segment head that fails its own CRC, and a segment belonging to another
       job — and folding them into `Bad_crc` would report the wrong operator action.
   D5  Added beside §1.4's functions: `open_job`/`open_reader_job` (the build brief's
       `job:string` hex form), `append`/`sync` (aliases of `stage`/`commit`), `rotate`,
       `checkpoint_mark`, `last_index`, `durable_upto`, `replay_seq`, `job_dir`,
       `segment_name`, `stop_to_string`, and the grammar's constants.  Nothing named in §1.4
       is missing or renamed.
   D6  `replay_seq` takes `~verdict:(stop ref)`, set when the sequence ends.  A `Seq.t` has
       nowhere else to put a verdict, and dropping the verdict would make LG1 unobservable
       through that door.
   D7  `close` commits what is staged before releasing the lock.  The alternative — dropping
       staged rows at close — makes the last commit's durability depend on whether anyone
       called `commit`, which is a footgun in a log. *)

(* ---------------------------------------------------------------- the grammar *)

val magic : string
(** "E4LOG\000" — the six bytes every segment starts with. *)

val version : string
(** "00000001" — eight ASCII bytes, compared as a string and never parsed (L-CF-1's rule,
    applied to the log). *)

val head_length : int
(** 34: the segment head, checksum included. *)

val row_header_length : int
(** 8: `be32 row_len :: be32 row_crc`. *)

val body_header_length : int
(** 9: the row tag and the be64 index inside `row_body`. *)

val row_max : int
(** 1 MiB: the largest `row_body` (LG9). *)

val default_seg_max : int
(** 64 MiB: the rotation threshold `open_` is given when a caller has no reason to choose. *)

val min_seg_max : int
(** The smallest legal `seg_max`: a head plus one empty row.  `seg_max` is a THRESHOLD tested
    after a commit, never a cap: a row is never split and never refused for the room left, so
    a segment may exceed `seg_max` by the size of the commit that crossed it. *)

val segment_name : int -> string
(** The file name of the segment whose first data row has this index: sixteen lowercase hex
    digits and ".seg", so the lexicographic order of the names is the order of the indices. *)

val job_dir : dir:string -> job:E4_addr.Addr.t -> string
(** `<dir>/log/<job-hex>` (A2 §1.0; per-job, owner question OQ5). *)

(* ---------------------------------------------------------------- rows *)

type seq = int
(** A (job, index) position: the count of data rows before this one in this job.  Never a
    global sequence number (LAW LOG-REL). *)

type row =
  | Decision of string
      (** The canonical decision bytes — the same bytes Lean would hash (brief §2.2).
          Opaque here. *)
  | Event of string
      (** The canonical event bytes; `string` until the LogEvent carrier lands (risk R7). *)
  | Checkpoint_mark of { position : seq; addr : E4_addr.Addr.t option }
      (** A checkpoint covers the positions `< position`; replay from that checkpoint is
          `replay ~from:position`.  `addr` is the checkpoint node's address once it is
          published, `None` while it is not. *)
  | Seal of { next_first_seq : seq }
      (** Written by rotation, consumed by replay, never staged and never delivered (D2). *)

exception Locked of string
(** A second writer on one job directory (LG7); the string is the directory. *)

exception Row_too_large of int
(** A staged body of more than `row_max` bytes (LG9); the int is its length. *)

(* ---------------------------------------------------------------- the writer *)

type t

val open_ : dir:string -> job:E4_addr.Addr.t -> seg_max:int -> t
(** Creates `<dir>/log/<job-hex>/` if it is absent, takes the writer's claim (LG7) and opens
    the job's last segment for append, truncating a torn tail to its last good row (LG5).
    Raises `Locked` if another `t` holds the directory, `Invalid_argument` if
    `seg_max < min_seg_max`, and `Failure (stop_to_string s)` when the last segment's damage
    is structural — `Bad_header`, `Wrong_job` or `Gap` — because truncating those would hide
    them.  A torn tail (`Short`, `Bad_crc`, `Bad_row`, `Oversize`) is recovered, not raised. *)

val open_job : dir:string -> job:string -> seg_max:int -> t
(** `open_` with the job as 64 hexadecimal characters (either case).  Raises
    `Invalid_argument` on anything that is not a 32-byte digest in hex. *)

val close : t -> unit
(** Commits what is staged (D7), closes the segment and releases the claim.  Idempotent. *)

val job : t -> E4_addr.Addr.t
val dir_of : t -> string
(** The job directory `open_` created or found. *)

val stage : t -> row -> seq
(** Buffers one row and returns the index it will have (LG3).  Not durable until `commit`.
    Raises `Row_too_large`, and `Invalid_argument` on a `Seal` (D2). *)

val append : t -> row -> seq
(** `stage`, under the build brief's name. *)

val commit : t -> unit
(** One write(2) of the staged buffer, then one fsync(2); then rotation if the segment has
    reached `seg_max` (LG5).  Idempotent when nothing is staged. *)

val sync : t -> unit
(** `commit`, under the build brief's name. *)

val rotate : t -> unit
(** Commit, seal the current segment and open the next one, whatever the segment's size.
    What `commit` does for itself at the threshold. *)

val checkpoint_mark : t -> seq -> unit
(** Record — durably — that a checkpoint covers the positions `< position`, so that replay
    from that checkpoint is `replay ~from:position`.  Stages a `Checkpoint_mark` with no
    address yet and commits it. *)

val next_seq : t -> seq
(** The index the next staged row will be given: one past the last, staged rows included. *)

val last_index : t -> seq option
(** The index of the last row, staged rows included; `None` for a job with no rows. *)

val durable_upto : t -> seq
(** Every index strictly below this is on the disk and fsynced; nothing at or above it is
    (LG3). *)

val staged_bytes : t -> int
(** The bytes buffered and not yet written. *)

val truncate_to : t -> seq -> unit
(** Discard the staged buffer and every stored row at or above this index, then continue
    from it.  Writer only.  Raises `Invalid_argument` for an index above `next_seq` or below
    the current segment's first index — this module deletes no segment. *)

(* ---------------------------------------------------------------- the reader *)

type reader
(** Holds no file handle: a segment is opened, read and closed inside one `replay`, so a
    reader is safe across a rotation and needs no lock (LG7). *)

val open_reader : dir:string -> job:E4_addr.Addr.t -> reader
val open_reader_job : dir:string -> job:string -> reader
val close_reader : reader -> unit

type stop =
  | Eof
      (** The clean end: every stored row was delivered. *)
  | Short of seq
      (** A row at this index was cut off by the end of its segment (a torn write). *)
  | Bad_crc of seq
      (** The row at this index failed its CRC. *)
  | Bad_row of seq
      (** The row at this index passed its CRC and is not a row: an unknown tag, or a body
          too short to carry one. *)
  | Oversize of { at : seq; len : int }
      (** The row at this index declares more than `row_max` bytes (LG9, M9's shape). *)
  | Gap of { expected : seq; found : seq }
      (** The next row's index is not the one that must follow: a missing middle segment, a
          renumbered row, or a seal that does not meet its successor (LG2). *)
  | Bad_header of { path : string }
      (** A segment head that fails its magic, its version string or its own CRC. *)
  | Wrong_job of { path : string }
      (** A segment whose `job_lo` is another job's: a file moved between directories. *)

val stop_to_string : stop -> string
(** One line naming the damage and where it is; what an operator is shown. *)

val replay : reader -> from:seq -> f:(seq -> row -> unit) -> stop
(** Calls [f] for every DATA row from [from] in index order and returns why it stopped
    (LG1, LG2, LG6).  Every row's CRC is verified, including the rows below [from], which are
    walked but not delivered.  `Seal` rows are consumed, not delivered (D2). *)

val replay_seq : reader -> from:seq -> verdict:stop ref -> (seq * row) Seq.t
(** The same walk as a sequence; [verdict] is set when the sequence ends, to `Eof` or to the
    damage that stopped it (D6).  The sequence is re-startable and reads the segments again
    each time it is forced from the front. *)

val tape : reader -> from:seq -> upto:seq -> string list
(** Just the `Decision` bodies at the indices in `[from, upto)`, in order: the tape prefix a
    checkpoint's `tapePrefix` names. *)

val segments : reader -> (seq * string) list
(** (first index, path) for every `*.seg` in the job's directory, ascending.  A reading of
    the directory, not of the files. *)

val end_index : reader -> seq * stop
(** Walk to the end and answer the index one past the last good row, with the verdict.  The
    cheap "where does this job stand" question, and what a writer's `open_` uses. *)
