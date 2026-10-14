#!/bin/bash
set -euo pipefail
export PATH=/tmp/proc6-landing/bin:$PATH
lake build Effect4.Laws.Program.FragmentBlock Effect4.Laws.Program.Agreement.BlockPlain Effect4.Laws 2>&1 | tee /tmp/proc6-landing/c-integrated-build.log
lake env lean -DwarningAsError=true /tmp/proc6-landing/c-integrated-audit.lean 2>&1 | tee /tmp/proc6-landing/c-integrated-audit.log
make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics 2>&1 | tee /tmp/proc6-landing/c-integrated-semantics.log
