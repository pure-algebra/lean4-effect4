#!/bin/bash
# Verifier of seat ALGEBRA (formal pass, 2026-10-01): rerun the seat's seven probes and the
# verifier's four probes, one at a time, through the one-compiler lock, and compare the seat's
# logs byte for byte. Usage: bash verify-rerun.sh
set -u
LOCK=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
V=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass/algebra
mkdir -p "$V/verify-logs"
for p in P1Coproduct P2KripkeTyping P3TapeAction P4ComodelIteration P5ScopeMarkers P6ProtocolLaws P7ProvideRows; do
  bash "$LOCK" lake env lean -M6144 -DwarningAsError=true "$V/probes/$p.lean" > "$V/verify-logs/rerun-$p.log" 2>&1
  code=$?
  if diff -q "$V/verify-logs/rerun-$p.log" "$V/logs/$p.log" > /dev/null; then same=identical; else same=DIFFERS; fi
  echo "$p exit=$code log=$same"
done
for p in verify-StepLoop verify-WrapWalk verify-BindGuard verify-ProvideMerge; do
  bash "$LOCK" lake env lean -M6144 -DwarningAsError=true "$V/$p.lean" > "$V/verify-logs/$p.log" 2>&1
  code=$?
  bad=$(grep -c -E 'sorryAx|Classical.choice|error' "$V/verify-logs/$p.log")
  echo "$p exit=$code lines=$(wc -l < "$V/verify-logs/$p.log") suspicious=$bad"
done
