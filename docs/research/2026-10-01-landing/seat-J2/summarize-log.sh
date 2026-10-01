#!/usr/bin/env bash
# Seat J (copied verbatim by seat J2): a build or generator log reduced to what the receipt cites: the commands run (`+ ` lines),
# every error and warning line, the two gate lines, every module built (not replayed), and the
# tail. The full log stays in the seat's scratch directory; this summary is what is committed.
set -euo pipefail
log="$1"
echo "# summary of $(basename "$log") ($(wc -l < "$log" | tr -d ' ') lines)"
echo "## commands"; grep -E '^\+ |^python3 |^lake |^make ' "$log" | cut -c1-400 || true
echo "## errors and warnings"; grep -n -E '^error|: error|✖|^warning|: warning' "$log" | cut -c1-400 || echo "(none)"
echo "## gates"; grep -E 'library-root gate|module and axiom gate|exact implementation boundary' "$log" | cut -c1-400 || echo "(none)"
echo "## built (not replayed)"; grep -E '^(✔|ℹ|⚠) \[[0-9]+/[0-9]+\] Built' "$log" | cut -c1-200 || echo "(none)"
echo "## tail"; tail -3 "$log"
