(* E4_check -- the harness of the engine's and the disk store's tests: each check's named PASS
   or FAIL line, the counts, the summary line and the exit code, and the scratch directories a
   test makes and removes.

   What it is: the hygiene lane's H5 (docs/research/2026-10-18-slices/README.md §10.2). Each
   test file once defined its own failure counter, its own check and its own summary line, and
   the store's tests each read their own variable for a scratch directory (E4_CAS_TMP,
   E4_PACK_TMP, E4_INDEX_TMP, E4_CHECKPOINT_TMP, E4_CACHE_TMP, E4_DISK_TMP). This module is the
   one copy. A scratch directory lies under the system's temporary directory, which TMPDIR
   names, as for every other OCaml program.
   Depends on: the OCaml standard library, unix (the permissions [remove_tree] restores).

   Behaviours:
   C1 [check name ok] prints one line, the verdict, the gap and the name, and flushes it at
      once; it counts the check, and a false [ok] as a failure. The verdict is PASS or FAIL.
                                                                    tested (test_check)
   C2 [finish ()] prints the summary line and exits. With no failure it prints
      [== ALL PASS: 0 failure(s) in N checks ==] and exits 0; otherwise
      [== FAILED: K failure(s) in N checks ==] and exits 1.       tested (test_check, red control)
   C3 [temp_dir prefix] makes a fresh directory under [under], or under the system's temporary
      directory, whose name starts with [prefix]; two calls never answer one path.
                                                                    tested (test_check)
   C4 [remove_tree path] removes [path] and everything under it, entries without write or read
      permission included. No exception escapes it: an absent [path] is no error, and an entry
      the host refuses to remove stays.                             tested (test_check)
   Bound: the counts belong to one process. A forked child counts its own checks, and the
   flush of C1 keeps the parent's printed lines out of the child's buffer. *)

(** The space between the verdict and the check's name: [One] for the engine's tests, [Two]
    for the disk store's and the dispatcher's, whose logs have always printed two. *)
type gap =
  | One
  | Two

(** [check name ok] prints [PASS name] or [FAIL name] (C1). [gap] defaults to [One]. *)
val check : ?gap:gap -> string -> bool -> unit

(** The checks counted so far, and the failures among them. *)
val checks : unit -> int

val failures : unit -> int

(** Prints the summary line and exits, 0 when no check failed and 1 otherwise (C2). *)
val finish : unit -> 'a

(** [temp_dir prefix] makes a fresh directory (C3). It raises [Sys_error] when the host cannot
    make one: that is a fault of the host, not an answer of the test. *)
val temp_dir : ?under:string -> string -> string

(** [remove_tree path] removes [path] and everything under it (C4). *)
val remove_tree : string -> unit
