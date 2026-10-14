#!/bin/bash
set -euo pipefail
lake build Effect4 Effect4.Laws Test.Dogfood.Proofs.HostRouting Test.Program.AgreementContract | tee /tmp/proc6-landing/f-integrated-build.log
lake env lean -DwarningAsError=true /tmp/proc6-landing/f-integrated-audit.lean | tee /tmp/proc6-landing/f-integrated-audit.log
