#!/usr/bin/env python3
"""Exercise installed Jane Street patterns in a private dune workspace.
Properties: inputs, expansions and library hashes are retained; failures propagate.
No dependency installation and no main-checkout build.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
OPAM=Path('/Users/pooks/.opam/effect4')

def execute(args,cwd,log,expect=0):
    log.write('$ '+' '.join(map(str,args))+'\n')
    log.flush()
    result=subprocess.run(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write(result.stdout)
    log.write(f'EXIT {result.returncode}\n')
    log.flush()
    if expect==0:
        result.check_returncode()
    else:
        assert result.returncode!=0
    return result.stdout

def main():
    with (HERE/'run.log').open('w') as log, tempfile.TemporaryDirectory(prefix='effect4-jane-') as temporary:
        work=Path(temporary)
        head=execute(['git','rev-parse','HEAD'],ROOT,log).strip()
        execute(['git','status','--short'],ROOT,log)
        for args in [['ocamlc','-version'],['dune','--version']]:
            execute(['opam','exec','--switch=effect4','--',*args],work,log)
        execute(['opam','list','--switch=effect4','--installed','--columns=name,version','--short'],work,log)
        shutil.copy2(HERE/'ecosystem_probe.ml',work/'ecosystem_probe.ml')
        carrier_bytes=(ROOT/'ocaml/eff/eff_types.ml').read_bytes()
        (work/'eff_types.ml').write_bytes(carrier_bytes)
        (HERE/'input-eff-types.ml').write_bytes(carrier_bytes)
        (work/'dune-project').write_text('(lang dune 3.11)\n')
        (work/'dune').write_text('''(executable
 (name ecosystem_probe)
 (libraries core core.univ_map typerep bin_prot sexplib)
 (preprocess (pps ppx_jane ppx_typerep_conv))
 (flags (:standard -w -a)))
''')
        execute(['opam','exec','--switch=effect4','--','dune','exec','--root',str(work),'./ecosystem_probe.exe'],work,log)
        args=['opam','exec','--switch=effect4','--','dune','describe','pp','--root',str(work),'ecosystem_probe.ml']
        result=subprocess.run(args,cwd=work,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        log.write('$ '+' '.join(args)+f'\nEXIT {result.returncode}; stdout retained in expanded.ml\n'+result.stderr)
        result.check_returncode()
        (HERE/'expanded.ml').write_text(result.stdout)
        negative='''open Base
module Asc = struct
 type t=int
 include Comparator.Make(struct type nonrec t=t let compare=Int.compare let sexp_of_t=Int.sexp_of_t end)
end
module Desc = struct
 type t=int
 include Comparator.Make(struct type nonrec t=t let compare a b=Int.compare b a let sexp_of_t=Int.sexp_of_t end)
end
let mixed = Set.union (Set.empty (module Asc)) (Set.empty (module Desc))
'''
        (work/'negative.ml').write_text(negative)
        diagnostic=execute(['opam','exec','--switch=effect4','--','ocamlfind','ocamlc','-package','base','-c','negative.ml'],work,log,expect=1)
        assert 'comparator_witness' in diagnostic and 'Desc' in diagnostic and 'Asc' in diagnostic
        assert "The type `t' is required but not provided" not in diagnostic
        log.write('PASS comparator_witness_prevents_mixing_orders\n')
        paths=[OPAM/'lib/base/type_equal.mli',OPAM/'lib/base/type_equal.ml',OPAM/'lib/base/comparator.mli',
            OPAM/'lib/core/univ_map/univ_map_intf.ml',OPAM/'lib/typerep/std_internal.mli',
            OPAM/'lib/typerep/variant_and_record_intf.ml',OPAM/'lib/typerep/type_generic.mli',
            OPAM/'lib/bin_prot/shape/bin_shape.mli',OPAM/'lib/sexplib0/sexp_grammar.ml',
            OPAM/'doc/ppx_typerep_conv/README.md',OPAM/'doc/ppx_bin_prot/README.md',
            OPAM/'lib/base/base.cmxa',OPAM/'lib/core/core.cmxa',OPAM/'lib/typerep/typerep_lib.cmxa',
            OPAM/'lib/bin_prot/bin_prot.cmxa',OPAM/'lib/ppx_typerep_conv/ppx_typerep_conv.cmxa',
            OPAM/'lib/ppx_bin_prot/ppx_bin_prot.cmxa']
        hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        local={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'ecosystem_probe.ml',HERE/'expanded.ml',work/'_build/default/ecosystem_probe.exe']}
        (HERE/'provenance.json').write_text(json.dumps({'head':head,'carrier_source':{'path':'ocaml/eff/eff_types.ml','sha256':hashlib.sha256(carrier_bytes).hexdigest()},'installed_files':hashes,'artifacts':local},indent=2)+'\n')
        log.write('PASS ecosystem_driver_finished\n')
    print(HERE/'run.log')

if __name__=='__main__':main()
