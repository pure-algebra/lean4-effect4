#!/bin/bash
# Scratch (seat CLEANUP, S3): the two ty-rule mirror fixtures that import the touched modules,
# after the census instruments they read are built.
set -u
cd /Users/pooks/Dev/lean4-effect4-cleanup
step() { echo "+ $*"; /usr/bin/time -p "$@"; echo "exit=$?"; }
step lake build Effect4.Laws.Auto.Traversals Effect4.Laws.Auto.Exhaustive
step lake env lean -DwarningAsError=true -M6144 Test/fixtures/ty-rule/CensusMirrorsOCaml5.lean
step lake env lean -DwarningAsError=true -M6144 Test/fixtures/ty-rule/CensusMirrorsConformLcnfMl.lean
