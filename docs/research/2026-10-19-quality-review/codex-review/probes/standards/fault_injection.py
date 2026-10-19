#!/usr/bin/env python3
"""Build exact pinned sources inside modules whose Unix calls inject named I/O failures.
No production file changes. This tests error branches; it does not simulate hardware power loss.
"""
from pathlib import Path
import hashlib,subprocess,json,time
ROOT=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
OUT=Path(__file__).resolve().parent
header='''open Effect4_engine_cas
module Real_unix = Unix
let reject_directory_sync = ref false
let reject_write = ref false
let injected_dir_errors = ref 0
module Fault_unix = struct
  include Unix
  let fsync fd =
    if !reject_directory_sync && (Unix.fstat fd).Unix.st_kind = Unix.S_DIR then
      (incr injected_dir_errors; raise (Unix.Unix_error (Unix.EIO, "fsync", "injected directory")))
    else Unix.fsync fd
  let write_substring fd bytes start length =
    if !reject_write then raise (Unix.Unix_error (Unix.EIO, "write", "injected"))
    else Unix.write_substring fd bytes start length
end
'''
parts=[header];manifest={}
for name, file in [('Control','e4_control.ml'),('Wal','e4_wal.ml')]:
 path=ROOT/'ocaml/engine/cas'/file
 data=path.read_bytes();manifest[str(path)]=hashlib.sha256(data).hexdigest()
 parts.append('module '+name+' = struct\nmodule Unix = Fault_unix\n'+data.decode()+'\nend\n')
parts.append('''let () =
  let root = Sys.argv.(1) in
  Unix.mkdir root 0o700;
  let path = Filename.concat root "control" in
  reject_directory_sync := true;
  Control.commit ~path Control.initial;
  Printf.printf "control commit: returned success after %d injected directory EIO; readable=%b\\n%!"
    !injected_dir_errors (match Control.read ~path with Ok _ -> true | Error _ -> false);
  reject_directory_sync := false;
  let dir = Filename.concat root "wal" in
  let job = E4_addr.Addr.of_digest (String.make 32 'w') in
  let w = Wal.open_ ~dir ~job ~seg_max:Wal.default_seg_max in
  ignore (Wal.stage w (Wal.Decision "one"));
  ignore (Wal.stage w (Wal.Decision "two"));
  reject_write := true;
  (try Wal.commit w with e -> Printf.printf "WAL commit failure: %s\\n%!" (Printexc.to_string e));
  Printf.printf "WAL after failed write: staged=%d next=%d durable=%d\\n%!"
    (Wal.staged_bytes w) (Wal.next_seq w) (Wal.durable_upto w);
  reject_write := false;
  ignore (Wal.stage w (Wal.Decision "three")); Wal.commit w;
  let rd = Wal.open_reader ~dir ~job in
  let n = ref 0 in
  let stop = Wal.replay rd ~from:0 ~f:(fun _ _ -> incr n) in
  Printf.printf "WAL later successful commit: durable=%d replayed=%d stop=%s\\n%!"
    (Wal.durable_upto w) !n (Wal.stop_to_string stop);
  Wal.close w
''')
(OUT/'injected_sources.ml').write_text(''.join(parts))
(OUT/'injected-source-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
scratch=OUT/('injected-run-'+str(time.time_ns()))
result=subprocess.run(['python3',str(OUT.parent/'run_ml.py'),str(OUT/'injected_sources.ml'),str(scratch)],text=True,capture_output=True)
(OUT/'injected.log').write_text(result.stdout+result.stderr)
print(result.stdout);print(result.stderr);raise SystemExit(result.returncode)
