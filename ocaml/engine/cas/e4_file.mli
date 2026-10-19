(* E4_file — the store's durable file steps on a local file system (decisions row 417 (3)).

   What it is: the two steps a durable write of the store is made of.  [sync_dir] makes the
   names in a directory survive a crash: the pack calls it when a segment appears or goes.
   [replace] puts a file's new bytes in place whole: the control file (E4_control) and the index
   snapshot (E4_index) are replaced through it.  The store supports a local file system; a
   network file system has no failure contract here (row 417 (3)).
   Depends on: the stdlib, unix.

   Behaviours:
   F1 A failed step raises Unix.Unix_error, and nothing here swallows one: a failed file or
      directory sync is a failed commit, which E4_disk answers as an I/O fault, and it closes
      the uncertain writer.                                  by construction; tested (test_disk)
   F2 [replace] writes [path ^ ".tmp"], created with [perm], through [write], syncs it, closes
      it, renames it over [path] and syncs [path]'s directory.  Once it returns, a crash leaves
      the new bytes; before, a crash leaves the old file and perhaps the tmp, which the next
      [replace] removes, as E4_control.cleanup does at open.
                                         by construction; tested (test_control X4, test_index F12)
   F3 A descriptor these steps open is closed on every path; when a step fails, its failure is
      the one raised.                                                        by construction *)

(** Syncs the directory [path] (F1). *)
val sync_dir : string -> unit

(** [replace ~path ~perm write] puts the bytes [write] writes to the descriptor at [path] (F2).
    [write] must not close the descriptor. *)
val replace : path:string -> perm:int -> (Unix.file_descr -> unit) -> unit
