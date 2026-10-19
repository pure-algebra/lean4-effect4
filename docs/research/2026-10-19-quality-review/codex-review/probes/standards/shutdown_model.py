#!/usr/bin/env python3
from pathlib import Path
import sys,subprocess,hashlib
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
sys.path.insert(0,str(OUT.parent));from run_ml import compile_probe
source=(ROOT/'ocaml/engine/e4_sched.ml').read_text()
header='''open Effect4_engine
let pause=Atomic.make false
let reached=Atomic.make false
let released=Atomic.make false
module Paused_mailbox = struct
  include E4_mailbox
  let push_with t make =
    if Atomic.get pause then (
      Atomic.set reached true;
      while not(Atomic.get released) do Domain.cpu_relax() done);
    E4_mailbox.push_with t make
end
module Sched = struct
module E4_mailbox = Paused_mailbox
'''
p=OUT/'shutdown_model.ml';p.write_text(header+source+'\nend\n'+(OUT/'shutdown_model_tail.ml').read_text())
(OUT/'scheduler-source-sha256.txt').write_text(hashlib.sha256(source.encode()).hexdigest()+'\n')
exe=compile_probe(p,'zarith,yojson,unix,threads,qcheck-core,qcheck-core.runner,qcheck-stm.stm,qcheck-stm.domain')
r=subprocess.run([str(exe)],capture_output=True,text=True,timeout=20)
(OUT/'shutdown-model.log').write_text(r.stdout+r.stderr+f'\nexit={r.returncode}\n')
print(r.stdout);print(r.stderr);print('exit=',r.returncode)
