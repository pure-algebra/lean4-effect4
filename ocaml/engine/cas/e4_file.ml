(* E4_file — see e4_file.mli for what this is and the behaviours it holds itself to. *)

(* F3: [use fd step] runs [step fd] and closes [fd].  When the step fails, the descriptor still
   goes, and the step's failure is the one raised; when the step succeeds, a failed close is
   the answer. *)
let use fd step =
  match step fd with
  | () -> Unix.close fd
  | exception failure ->
    (try Unix.close fd with
     | Unix.Unix_error _ -> ());
    raise failure
;;

let sync_dir path = use (Unix.openfile path [ Unix.O_RDONLY ] 0) Unix.fsync

let replace ~path ~perm write =
  let tmp = path ^ ".tmp" in
  (* a tmp a stopped replace left behind, read-only perhaps, is not ours to keep *)
  (try Unix.unlink tmp with
   | Unix.Unix_error (Unix.ENOENT, _, _) -> ());
  use
    (Unix.openfile tmp [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] perm)
    (fun fd ->
       write fd;
       Unix.fsync fd);
  Unix.rename tmp path;
  sync_dir (Filename.dirname path)
;;
