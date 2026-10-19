(* Direct POSIX lock and fork semantics. Extra open/close is a control, not production code. *)
open Effect4_engine_cas
let raw_child_can_lock path =
  let pid=Unix.fork() in
  if pid=0 then (
    let fd=Unix.openfile path [Unix.O_RDWR] 0 in
    let held=try Unix.lockf fd Unix.F_TLOCK 0;true with Unix.Unix_error _->false in
    Unix.close fd;Unix._exit(if held then 0 else 1))
  else match snd(Unix.waitpid [] pid) with Unix.WEXITED 0->true|_->false
let () =
  let dir=Sys.argv.(1) in Unix.mkdir dir 0o700;
  let path=Filename.concat dir "LOCK" in
  let claim=match E4_lock.acquire ~dir with Ok x->x|Error _->failwith "claim" in
  Printf.printf "another process while claimed: can_lock=%b\n%!" (raw_child_can_lock path);
  let extra=Unix.openfile path [Unix.O_RDONLY] 0 in Unix.close extra;
  Printf.printf "after extra LOCK fd closes: can_lock=%b\n%!" (raw_child_can_lock path);
  E4_lock.release claim;
  let claim=match E4_lock.acquire ~dir with Ok x->x|Error _->failwith "reclaim" in
  let r,w=Unix.pipe() in
  let pid=Unix.fork() in
  if pid=0 then (
    Unix.close w;let buf=Bytes.create 1 in ignore(Unix.read r buf 0 1);Unix.close r;
    let raw=Unix.openfile path [Unix.O_RDWR] 0 in
    let works=try Unix.lockf raw Unix.F_TLOCK 0;true with Unix.Unix_error _->false in
    Unix.close raw;
    Printf.printf "after parent release, child raw=%b inherited_registry=%s\n%!" works
      (match E4_lock.acquire ~dir with Ok c->E4_lock.release c;"accepted"|Error _->"refused");
    Unix._exit 0)
  else (
    Unix.close r;E4_lock.release claim;ignore(Unix.write_substring w "x" 0 1);Unix.close w;ignore(Unix.waitpid [] pid))
