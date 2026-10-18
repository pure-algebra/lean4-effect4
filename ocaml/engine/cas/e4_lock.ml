(* E4_lock -- see e4_lock.mli for what this is and the behaviours it holds itself to. *)

type t = { fd : Unix.file_descr; key : string; mutable live : bool }

let held : (string, unit) Hashtbl.t = Hashtbl.create 8
let mutex = Mutex.create ()

let acquire ~dir =
  let key = try Unix.realpath dir with Unix.Unix_error _ | Sys_error _ -> dir in
  Mutex.protect mutex (fun () ->
      if Hashtbl.mem held key then Error key
      else
        let fd = Unix.openfile (Filename.concat dir "LOCK") [ Unix.O_RDWR; Unix.O_CREAT ] 0o600 in
        match Unix.lockf fd Unix.F_TLOCK 0 with
        | () ->
          Hashtbl.replace held key ();
          Ok { fd; key; live = true }
        | exception Unix.Unix_error _ ->
          (try Unix.close fd with Unix.Unix_error _ -> ());
          Error key)

let release t =
  Mutex.protect mutex (fun () ->
      if t.live then begin
        t.live <- false;
        (try Unix.lockf t.fd Unix.F_ULOCK 0 with Unix.Unix_error _ -> ());
        (try Unix.close t.fd with Unix.Unix_error _ -> ());
        Hashtbl.remove held t.key
      end)
