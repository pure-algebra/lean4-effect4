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
#
# ## Generators are not stamped; their callers key on their inputs
#
# A `generate-*.sh` has no verdict to cache: it exists to print bytes, and a
# checker that skipped its generator would have nothing to compare. So the
# stamp always sits on the CHECKING side. A checker that calls a generator
# names, in its own key, the generator script and everything the generator
# reads -- the Lean file it runs, that file's import traces, the pinned host
# bytes, the manifest -- so a change anywhere under the generator still misses.
# Rule 9 of docs/research/2026-09-03-refactor-plan.md is about a gate not
# re-running, and that is the gate, not its subroutine.
#
# The same asymmetry applies to the `--update`, `--dry-run` and `--print-row`
# modes: those write or compare against something other than the committed
# projection, so they are never stamped and never consult a stamp.

stamp_repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
stamp_root="$stamp_repo_root/.lake/stamps"
stamp_build_lib="$stamp_repo_root/.lake/build/lib/lean"

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

# ---------------------------------------------------------------------------
# Input helpers. Each prints one path per line, for a caller to collect into
# the argument list of `stamp_key`.
# ---------------------------------------------------------------------------

# stamp_lean_traces <lean-source>...   the Lake trace of every `Effect4` or
# `Effect4Test` module these sources import.
#
# A harness driver such as `harness/trace/Generate.lean` is elaborated by
# `lake env lean --run`, so it is never a compiled module and has no trace of
# its own; what it reads is its own bytes -- which the caller lists directly --
# and the oleans of its imports. A module's trace is Lake's hash of that
# module's source together with the traces of everything IT imports, so the
# direct imports stand for the whole closure and nothing below them needs
# naming. A trace that does not exist yet is `absent` to `stamp_key`, which is
# a change, not an error: the first build after it appears is a miss.
#
# Only `Effect4*` modules are named. `Lean` and `Init` belong to the toolchain,
# which the caller pins by listing `lean-toolchain`.
stamp_lean_traces() {
  local source module
  for source in "$@"; do
    [ -f "$source" ] || continue
    while IFS= read -r module; do
      case "$module" in
        Effect4|Effect4.*|Effect4Test|Effect4Test.*)
          printf '%s\n' "$stamp_build_lib/${module//.//}.trace" ;;
      esac
    done < <(sed -n 's/^import[[:space:]][[:space:]]*\([A-Za-z0-9_.]*\).*$/\1/p' "$source")
  done
}

# stamp_fact <name> <value>   a pseudo-input for something that is not a file:
# a tool version, a seed, the directory an environment variable selected.
#
# It is spelled as a path that cannot exist, so `stamp_key` folds it in as
# `absent  !<name>=<value>`; the path itself is part of the digest, so a
# different value is a different key. This is how a gate keys the node version
# it ran under, or the compiler it found, without hashing a 23 MB binary.
stamp_fact() {
  printf '!%s=%s\n' "$1" "$2"
}

# stamp_host_inputs   the identity of the pinned Effect installation a host
# gate runs against.
#
# Three package manifests, named by their absolute path, so that pointing
# EFFECT4_EFFECT_NODE_MODULES at a different installation is a different key
# even when the versions agree; `harness/trace/host-pin.json`, which carries
# the SHA-256 of the whole 2,341-file Effect tree and the upstream commit, so a
# re-pin is a change; and the node version, which the receipts record and the
# run loop's yield behaviour depends on.
#
# It does not hash the tree itself. That pin file IS the tree's digest, and
# re-deriving it costs longer than every gate in the sweep put together.
stamp_host_inputs() {
  local node_modules
  node_modules="${EFFECT4_EFFECT_NODE_MODULES:-$HOME/Dev/foldlab/library/effects/node_modules}"
  node_modules="$(cd "$node_modules" 2>/dev/null && pwd || printf '%s' "$node_modules")"
  printf '%s\n' \
    "$node_modules/effect/package.json" \
    "$node_modules/typescript/package.json" \
    "$node_modules/@effect/tsgo/package.json" \
    "$stamp_repo_root/harness/trace/host-pin.json"
  stamp_fact node "$(node --version 2>/dev/null || echo absent)"
}

# stamp_tools_inputs <file>...   the effect4-tools runner files a host gate
# invokes, under whatever EFFECT4_TOOLS names. The runners assert the host pin
# and drive tsc, the language service and node, so their bytes are as much an
# input as the fixtures they check.
stamp_tools_inputs() {
  local tools file
  tools="${EFFECT4_TOOLS:-$stamp_repo_root/../effect4-tools}"
  for file in "$@"; do
    printf '%s\n' "$tools/packages/harness/$file"
  done
}
