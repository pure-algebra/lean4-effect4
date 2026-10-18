(* E4_lock -- the single-writer lock on a directory, shared by the pack (E4_pack PK6) and the
   WAL (E4_wal LG7).

   What it is: one holder per directory, as <dir>/LOCK.  Unix.lockf is a POSIX fcntl lock: it
   refuses another process, but not a second descriptor of this one, so an in-process table
   refuses that.  E4_cas takes the lock before it reads or writes anything of the store, and
   hands it to E4_pack.open_at (K2 of ocaml/engine/test/stm/stm_disk.ml).
   Depends on: the stdlib (Mutex, Hashtbl), unix.

   Behaviours:
   L1 One holder per directory in this process: a second [acquire] is refused while the first
      is held.                                       tested (stm_disk K1, test_pack W1, test_wal W6)
   L2 One holder across processes: [acquire] takes Unix.lockf F_TLOCK on <dir>/LOCK.
                                                                     tested (test_pack W3)
   L3 Atomic: one mutex covers the table's check, the lockf and the insert, and every release,
      so two domains never both hold one directory (K1).            tested (stm_disk K1)
   L4 A release runs once: a second [release] does nothing, so it never closes a descriptor
      number that now names another file.                                    by construction
   L5 The key is the directory's real path, so two spellings of one directory share one
      holder.                                                                 by construction *)

type t

(** Takes the lock on <dir>/LOCK, creating the file if absent; <dir> must exist.  [Error key]
    when another holder has it, in this process or another, with [key] the directory's real
    path.  Raises Unix.Unix_error when the file cannot be opened. *)
val acquire : dir:string -> (t, string) result

(** Drops the lock and its descriptor.  Idempotent (L4). *)
val release : t -> unit
