#!/bin/bash
# Scratch (seat CLEANUP, S3): the narrow build of the touched modules' direct dependents, one lake
# at a time (run under the shared slot), each step timed.
set -u
cd /Users/pooks/Dev/lean4-effect4-cleanup
step() { echo "+ $*"; /usr/bin/time -p "$@"; echo "exit=$?"; }
step lake build OCaml5 Conform Test.Audit.ClockLowering Test.Audit.LetReturn \
  Drivers.Corpus Drivers.ForeignCorpus Drivers.ProgramStructureCheck Drivers.Styles Drivers.TsGen
step lake env lean -DwarningAsError=true -M6144 Test/fixtures/ty-rule/CensusMirrorsOCaml5.lean
step lake env lean -DwarningAsError=true -M6144 Test/fixtures/ty-rule/CensusMirrorsConformLcnfMl.lean
