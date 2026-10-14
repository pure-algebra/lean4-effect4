#!/bin/bash
set -euo pipefail
export PATH="/tmp/proc6-landing/bin:$PATH"
lake build Test.Dogfood.Scenario.Todo.Cached 2>&1 | tee /tmp/proc6-landing/g-build.log
lake env lean -DwarningAsError=true harness/truth/session/Keyed.lean 2>&1 | tee /tmp/proc6-landing/g-keyed-check.log
lake env lean -DwarningAsError=true apps/todo/Check.lean 2>&1 | tee /tmp/proc6-landing/g-checker-check.log
lake env lean -DwarningAsError=true /tmp/proc6-landing/g-final-audit.lean 2>&1 | tee /tmp/proc6-landing/g-final-audit.log
make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules check-host-protocol 2>&1 | tee /tmp/proc6-landing/g-host-protocol.log
make -o ts/eff/node_modules -o harness/truth/node_modules -o apps/todo/node_modules gen-semantics 2>&1 | tee /tmp/proc6-landing/final-semantics.log
