(* E4_pack — the append-only node records of one store, and the group-commit writer.

   What it is: the bytes a node lives in.  One segment is a file; a store is a list of
   segments, rotated at `seg_max` bytes.  The writer is single (a lock on <store>/LOCK);
   readers are many and need no lock because a record is only ever appended and never
   rewritten (docs/research/2026-09-08-engine-a2-persistence.md §1.0, §1.2).

     packfile   := pack_head record*
     pack_head  := "E4PACK\000"                7   ASCII magic
                   "00000001"                  8   ASCII version, exact match, never a number
                   be64 seg_index              8   this segment's index, 0-based
                   be32 head_crc               4   CRC-32 over the 23 bytes before it
     record     := 'R'                         1   0x52; a record always starts here
                   be64 node_len               8   length of node_bytes; < 2^62 (M9)
                   digest                     32   sha256 node_bytes — the address
                   node_bytes          node_len   = Node.encode n (Node.lean:170-171)
                   be32 rec_crc                4   CRC-32 over the 41 header bytes ++ node_bytes

   Overhead is 45 bytes per node, the head is 27.  `be64` is written and read through
   `E4_be` (which is `Digits.be64`, `Eff_frame.emit_be64`); this module adds no second
   framing writer and no second hash (brief §2.2).

   Why the digest is in the record: without it a rebuild must re-hash every byte of the
   store; with it a rebuild reads 41 bytes and seeks (A2 §6.5, 2.5 M nodes/s).  The recorded
   digest is a CACHE of the identity, never the identity: `read` re-hashes and compares
   (L-CAS-6), and no function here answers from the recorded digest alone except the two
   whose names say so (`read_at`, `read_header`, and `scan` without `~verify`).

   Depends on: E4_addr, E4_crc (lane P0), E4_be and E4_sha256 (ocaml/engine, lane M), unix.

   Behaviours:
   PK1 A record's bytes are `'R' :: be64 len :: digest :: node_bytes :: be32 crc`, and
       `read_at` at a record offset returns exactly those node_bytes or None.
                                                        by construction; tested (R1, R2)
   PK2 Append is atomic per commit, not per node: `stage`/`append` buffer, `commit`/`sync`
       perform ONE write(2) per touched segment and ONE fsync(2) per touched segment.  A
       crash during a commit leaves a prefix of the buffer on disk; a scan stops at the
       first record that fails PK1.  `append` never fsyncs; `pack_end` = `durable_upto`
       advances only at a `sync`.                        by construction; tested (G1..G4, X1)
   PK3 Grow-only: no byte already committed is ever rewritten.  The only truncation is of a
       torn tail at open, and only above the last record that passed PK1; `truncate_to`
       refuses to go below `pack_end`.                   by construction; tested (T1, T2)
   PK4 `scan` visits records in write order and is O(records), not O(bytes): it reads the
       41-byte header and seeks past node_bytes.  `~verify:true` (and `read`) is the
       O(bytes) form and is what recovery and verification use.
                                                        by construction; tested (S1, S2)
   PK5 A node_len >= 2^62 is refused as `Host_limit`, never misread (amendment M9; the Lean
       byte language strictly contains this one).        by construction; tested (X5)
   PK6 Single writer: `open_` takes an exclusive lock on <dir>/LOCK — an in-process registry
       AND `Unix.lockf`, so a second `open_` in this process and a second process are both
       refused with `Locked`.  Readers take no lock.               tested (W1, W2)
   PK7 Recovery: `open_` scans from `?from` (default: the head of the last segment) with
       `~verify`, admits every record that passes the CRC and whose bytes re-hash to the
       recorded digest, in write order, and stops at the FIRST failure.  `pack_end` is the
       end of the last admitted record and `recovery` names why the scan stopped.  The
       admission of those records into a store is lane P4's; this module yields them.
                                                        by construction; tested (X1..X4)
   PK8 Rotation: a record that would push a non-empty segment past `seg_max` starts a new
       segment, whose 27-byte head is part of the same staged batch.  A record larger than
       `seg_max - 27` gets a segment to itself and exceeds `seg_max`; the alternative is
       refusing a node the store admits.                 by construction; tested (Z1, Z2)

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.2 (lane P1, 2026-09-08):
   D1  §1.2's `scan` both "reads the 41-byte header and seeks past node_bytes" (PK4) and can
       answer `Bad_digest` (its `scan_stop`) — the two cannot both hold, because a digest
       verdict costs the payload.  Resolved by a `~verify` flag: `scan` without it is the
       header scan (its verdicts are `Eof`, `Short`, `Bad_tag`, `Bad_head`, `Host_limit`),
       `scan ~verify:true` additionally checks the CRC and re-hashes (`Bad_crc`,
       `Bad_digest`).  Recovery uses the verifying form (§2.1 L-CAS-8, crash family X2);
       an index rebuild uses the fast one (§4.5 B4).
   D2  `scan_stop` gains `Bad_tag` and `Bad_head`.  §1.2 has no verdict for "the byte at
       this offset is not 'R'" or "this segment's 27-byte head does not check", and calling
       either `Short` would be a lie — X2's requirement is that the failure "is reported at
       the exact offset, never a silent skip".
   D3  Added beside §1.2's list, all named by the lane's brief: `append` (`stage` with a raw
       32-byte digest), `flush`/`sync` (the write and the fsync halves of `commit`, so a
       caller can coalesce without promising durability), `written_upto`/`durable_upto`/
       `staged_end` (the three watermarks `pack_end` is the last of), `read` (the verifying
       read of PK4/L-CAS-6, with a `refusal` that names which check failed), `scan_seq` (the
       `Seq.t` of `(offset, record)` in write order ending in exactly one `Stopped verdict`),
       `open_at` (the optional-argument form of `open_`: `?from`, `?verify`, `?truncate`),
       `recovery`, `segments`, `seg_path`, and the two printers.
   D4  `open_` is `open_at ~dir ~seg_max ()` with `?from` defaulting to the head of the LAST
       segment: earlier segments were sealed by a rotation that fsynced them and only the
       last can be torn.  Lane P4 passes the control file's `pack_end_off` as `?from` and
       pays for the tail alone.
   D5  `stage` does NOT check that `addr` is `sha256 node_bytes`: that hash is the caller's
       (it is what `E4_cas.put` computed to address the node at all) and re-hashing here
       would double the cost of every put.  `read` and `scan ~verify:true` re-hash, which is
       where L-CAS-6 is enforced and where X2(b) bites. *)

type t
(** A writer: one store directory, the lock, the staging buffer and the three watermarks. *)

type reader
(** A reader: no lock, one mmap per segment, re-mapped when the writer grows a file. *)

type seg = int
type off = int  (* byte offset inside a segment *)

exception Locked of string
(** `open_` while another writer holds <dir>/LOCK (PK6).  Carries the directory. *)

exception Bad_pack of string
(** A segment head that is not this format at all: bad magic, an ASCII version this binary
    does not know, a head CRC that fails, or a seg_index that is not the file's own. *)

(* ---- the grammar, as constants ---- *)

val magic : string              (* "E4PACK\000" — 7 bytes *)
val version : string            (* "00000001" — 8 ASCII bytes, matched as a string *)
val head_length : int           (* 27 = 7 + 8 + 8 + 4 *)
val record_tag : char           (* 'R' *)
val record_header_length : int  (* 41 = 1 + 8 + 32 *)
val record_overhead : int       (* 45 = 41 + 4 *)
val default_seg_max : int       (* 1 GiB (A2 §1.0) *)

val seg_path : dir:string -> seg -> string
(** <dir>/pack/%06d.pack *)

(* ---- opening ---- *)

val open_ : dir:string -> seg_max:int -> t
(** Takes the writer lock, creates <dir>, <dir>/pack and segment 0 if absent, and recovers
    the tail of the last segment (PK6, PK7).  `open_at ~dir ~seg_max ()`. *)

val open_at :
  ?from:seg * off -> ?verify:bool -> ?truncate:bool -> dir:string -> seg_max:int -> unit -> t
(** [from] is where the durable end was believed to be — lane P4 passes the control file's
    `pack_end` (default: the head of the last segment, D4).  [verify] (default true) makes
    recovery check the CRC and re-hash every record from [from].  [truncate] (default true)
    discards the torn tail: the failing record's offset becomes the file's length and every
    later segment is unlinked (PK3, crash family X1).  With [truncate:false] the bytes stay
    on disk and the next commit overwrites them. *)

val open_reader : dir:string -> reader
(** No lock.  Sees segments the writer creates later. *)

val close : t -> unit
val close_reader : reader -> unit

(* ---- writing: stage many, commit once (PK2) ---- *)

val stage : t -> addr:E4_addr.Addr.t -> node_bytes:string -> seg * off
(** Buffers one record and returns where it WILL live.  Not durable until [commit].
    The caller owes `addr = sha256 node_bytes` (D5). *)

val append : t -> digest:string -> node_bytes:string -> seg * off
(** [stage] with the 32 raw digest bytes.  Invalid_argument unless the digest is 32 bytes. *)

val staged_bytes : t -> int
(** Bytes buffered and not yet written — segment heads a rotation staged included. *)

val staged_count : t -> int
(** Records buffered and not yet written. *)

val flush : t -> unit
(** ONE write(2) per touched segment, no fsync.  Advances [written_upto], not [pack_end]. *)

val sync : t -> unit
(** [flush] then ONE fsync(2) per segment written since the last sync, plus one directory
    fsync if a segment file was created.  Advances [pack_end].  A no-op when nothing has
    been staged or written since the last sync. *)

val commit : t -> unit
(** §1.2's name for [sync]. *)

val pack_end : t -> seg * off
(** The durable end after the last commit (PK2). *)

val durable_upto : t -> seg * off
(** = [pack_end]: the watermark below which every byte survived an fsync. *)

val written_upto : t -> seg * off
(** Written with write(2), not necessarily fsynced.  [pack_end] <= this. *)

val staged_end : t -> seg * off
(** Where the next record will land.  [written_upto] <= this. *)

val seg_max : t -> int
val dir : t -> string

val truncate_to : t -> seg:seg -> off:off -> unit
(** Discard a torn tail: truncate that segment and unlink every later one.  Writer only;
    Invalid_argument below [pack_end] (PK3) or with bytes staged. *)

(* ---- what recovery found ---- *)

type scan_stop =
  | Eof                                           (** the clean end of the last segment *)
  | Short of { seg : seg; off : off }             (** a record that does not fit the file *)
  | Bad_crc of { seg : seg; off : off }           (** rec_crc disagrees (verifying only) *)
  | Bad_digest of { seg : seg; off : off }        (** sha256 node_bytes <> the recorded
                                                      digest (verifying only) — L-CAS-6 *)
  | Host_limit of { seg : seg; off : off }        (** node_len >= 2^62 (M9, PK5) *)
  | Bad_tag of { seg : seg; off : off; byte : int }  (** the byte here is not 'R' (D2) *)
  | Bad_head of { seg : seg }                        (** the segment head does not check (D2) *)

val scan_stop_to_string : scan_stop -> string

type recovery = {
  from : seg * off;         (** where the recovery scan started *)
  stop : scan_stop;         (** why it stopped — the verdict of the first bad record *)
  records : int;            (** records admitted, in write order *)
  ends_at : seg * off;      (** the end of the last admitted record = pack_end at open *)
  truncated : bool;         (** the torn tail was discarded *)
  verified : bool;          (** the scan re-hashed (default) *)
}

val recovery : t -> recovery
(** What `open_` found.  The re-admission of those records into a store is lane P4's. *)

(* ---- reading ---- *)

type record = {
  r_addr : E4_addr.Addr.t;      (** the digest the record carries *)
  r_len : int;                  (** node_len *)
  r_bytes : string option;      (** the node bytes: always Some from [read], Some from
                                    [scan_seq ~verify:true], None from the header scan *)
}

type refusal =
  | No_segment of seg
  | Past_end of { seg : seg; off : off; size : int }
  | Not_a_record of { seg : seg; off : off; byte : int }
  | Truncated of { seg : seg; off : off }
  | Over_host_limit of { seg : seg; off : off }
  | Crc_mismatch of { seg : seg; off : off; crc_recorded : int; crc_computed : int }
  | Digest_mismatch of { seg : seg; off : off; dig_recorded : string; dig_computed : string }

val refusal_to_string : refusal -> string

val read : reader -> seg:seg -> off:off -> (record, refusal) result
(** The verifying read (L-CAS-6): the tag, the length, the CRC, and then `sha256 node_bytes`
    against the recorded digest.  It never trusts the recorded digest, so a payload byte
    flipped with the CRC repaired is `Digest_mismatch` and a digest byte flipped with the CRC
    repaired is `Digest_mismatch` too. *)

val read_at : reader -> seg:seg -> off:off -> (E4_addr.Addr.t * string) option
(** The record's RECORDED digest and its node_bytes.  Checks 'R', the CRC and the length.
    Does NOT re-hash: that is [read] (and `E4_cas.verify`). *)

val read_header : reader -> seg:seg -> off:off -> (E4_addr.Addr.t * int) option
(** digest and node_len only — 41 bytes; the rebuild path (PK4). *)

val blit_at : reader -> seg:seg -> off:off -> Bytes.t -> int -> int
(** Copy node_bytes into a caller buffer at a position; returns the length, or -1 when there
    is no readable record there.  Invalid_argument if the buffer is too small. *)

(* ---- scanning and recovery ---- *)

val scan :
  ?verify:bool ->
  reader ->
  from:seg * off ->
  f:(E4_addr.Addr.t -> seg -> off -> int -> unit) ->
  scan_stop
(** Calls [f addr seg off node_len] for every well-formed record from [from], in write
    order, and returns why it stopped.  Without [verify] the payload is not read (PK4);
    with it the CRC and the digest are checked and the stop may be `Bad_crc`/`Bad_digest`
    (D1). *)

type scanned =
  | Scanned of (seg * off) * record
  | Stopped of scan_stop

val scan_seq : ?verify:bool -> reader -> from:seg * off -> scanned Seq.t
(** The same walk as a sequence: the records in write order, then exactly one `Stopped`
    verdict as the final element.  The sequence is finite and is not restartable-cheap —
    each traversal re-reads. *)

val segments : reader -> seg list
(** The segment indices present, ascending.  Re-read from the directory at every call. *)
