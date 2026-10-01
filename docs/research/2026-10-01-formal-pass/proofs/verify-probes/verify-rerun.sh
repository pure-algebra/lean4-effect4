#!/bin/bash
# Verifier re-run of seat PROOFS' probes, one at a time through the one-compiler lock.
# Usage: bash verify-rerun.sh <probe.lean> <logname>
LOCK=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
LOGDIR=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass/proofs/verify-logs
probe="$1"; name="$2"
log="$LOGDIR/verify-rerun-$name.log"
{
  echo "# probe: $probe"
  echo "# sha256: $(shasum -a 256 "$probe" | cut -d' ' -f1)"
  echo "# head: $(git -C /Users/pooks/Dev/lean4-effect4 rev-parse --short HEAD)"
  echo "# started: $(date '+%Y-%m-%d %H:%M:%S')"
} > "$log"
start=$(date +%s)
/usr/bin/time -l bash "$LOCK" lake env lean -M6144 -DwarningAsError=true "$probe" >> "$log" 2> "$log.time"
rc=$?
end=$(date +%s)
{
  echo "# exit: $rc"
  echo "# wall seconds (including lock wait): $((end-start))"
  grep -E "real|maximum resident" "$log.time" | sed 's/^/# /'
} >> "$log"
rm -f "$log.time"
echo "$name exit=$rc"
