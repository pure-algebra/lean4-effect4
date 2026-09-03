#!/usr/bin/env bash
# Content-hash stamps for the gates. Source it after lib/portable.sh:
#
#   . "$(dirname "${BASH_SOURCE[0]}")/lib/portable.sh"
#   . "$(dirname "${BASH_SOURCE[0]}")/lib/stamp.sh"
#
# Rule 9 of docs/research/2026-09-03-refactor-plan.md: a gate does not re-run
# when nothing it depends on has changed. A gate names its inputs -- its own
# script, its fixtures, the sources it reads, and the Lake trace files of the
# compiled closure it inspects -- and derives a KEY from their contents. A
# stamp is a file `.lake/stamps/<gate>/<key>` whose one line is the summary the
# gate printed when it last passed with exactly those inputs. A HIT means that
# file exists: the same bytes went in, so the same verdict comes out, and the
# gate prints the stamped summary and exits 0. A MISS runs the gate; the stamp
# is written only after a full pass, so a failing run never leaves one behind.
#
# Why Lake traces: `.lake/build/lib/lean/<Module>.trace` is Lake's own content
# hash of a module's source together with the traces of everything it imports,
# so the trace of an umbrella module stands for every olean and every source
# beneath it. Hashing the trace is milliseconds; hashing the oleans is not.
#
# Why `.lake/stamps`: it is already gitignored, it is deleted by exactly the
# command that deletes the build (`lake clean`), and a fresh clone has no
# stamps and no build, which is the right pair.
#
# Override: EFFECT4_FORCE=1 (or a `--force` flag the caller maps onto it) makes
# `stamp_hit` report a miss, so the gate re-runs and re-stamps.

stamp_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/.lake/stamps"

# stamp_key <path>...   the key for these inputs: a digest over each file's
# digest and path, in sorted path order, so a rename is a change. A directory
# argument stands for every regular file under it. A missing path is a change
# too: it contributes its name and the word `absent`, never an error, because
# a gate may legitimately depend on a file that does not exist yet.
stamp_key() {
  local path
  {
    for path in "$@"; do
      if [ -d "$path" ]; then
        find "$path" -type f | LC_ALL=C sort
      else
        printf '%s\n' "$path"
      fi
    done
  } | LC_ALL=C sort -u | while IFS= read -r path; do
    if [ -f "$path" ]; then
      printf '%s  %s\n' "$(sha256 "$path")" "$path"
    else
      printf 'absent  %s\n' "$path"
    fi
  done | sha256
}

# stamp_hit <gate> <key>   true when a stamp exists for this key and no force
# override is set.
stamp_hit() {
  [ "${EFFECT4_FORCE:-0}" != "1" ] && [ -f "$stamp_root/$1/$2" ]
}

# stamp_summary <gate> <key>   the summary line stored with the stamp.
stamp_summary() {
  cat "$stamp_root/$1/$2"
}

# stamp_write <gate> <key> <summary>   record a pass. Older stamps for the same
# gate are removed: only the current inputs are ever a hit, and the directory
# does not accumulate one file per edit.
stamp_write() {
  mkdir -p "$stamp_root/$1"
  rm -f "$stamp_root/$1"/*
  printf '%s\n' "$3" >"$stamp_root/$1/$2"
}

# stamp_report <gate> <key>   the standard hit line, for a gate to print
# before exiting 0.
stamp_report() {
  printf 'PASS %s: unchanged since %s; %s; skipped (EFFECT4_FORCE=1 re-runs)\n' \
    "$1" "$(date -r "$stamp_root/$1/$2" '+%Y-%m-%d %H:%M')" "$(stamp_summary "$1" "$2")"
}
