#!/bin/bash
set -euo pipefail
export PATH=/tmp/proc6-landing/bin:$PATH
lake build Effect4.Laws Test.Program.BlockMeaning Test.Dogfood.Scenario.Todo.Cached 2>&1 | tee /tmp/proc6-landing/b-dependents.log
lake env lean -DwarningAsError=true /tmp/proc6-landing/b-audit.lean 2>&1 | tee /tmp/proc6-landing/b-audit.log
make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics 2>&1 | tee /tmp/proc6-landing/b-semantics.log
