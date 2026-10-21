#!/bin/sh
# Generate the object's codec with the tree's own generator, and compare (or, with --write, splice)
# the copy that probe-object.lean holds.
#
#   docs/research/2026-10-21-program-domain-design/codec/gen.sh           # compare
#   docs/research/2026-10-21-program-domain-design/codec/gen.sh --write   # splice
#
# Steps: compile codec/ObjectDef.lean as the module Probe.ObjectDef into a scratch directory; run
# `effect4gen Main` on SigApp, Object and Certificate with the imports of the proposed group (the
# carriers and the program group's file, nothing that reaches the printer); compile the output with
# every warning an error; then compare the carriers and the generated body with the two marked
# sections of probe-object.lean. It also measures the codec of the two read refusals.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
WORK=${TMPDIR:-/tmp}/effect4-object-codec
rm -rf "$WORK"
mkdir -p "$WORK/src/Probe" "$WORK/olean/Probe"
cp "$HERE/ObjectDef.lean" "$WORK/src/Probe/ObjectDef.lean"
cd "$ROOT"
export LEAN_NUM_THREADS=3
lake env lean -DwarningAsError=true -R "$WORK/src" -o "$WORK/olean/Probe/ObjectDef.olean" \
  "$WORK/src/Probe/ObjectDef.lean"
lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH .lake/build/bin/effect4gen Main --group Object \
  --qualified-names --imports Probe.ObjectDef,Effect4.Store.Domain.Derived.Program \
  --kind Effect4.Program.Object=program --out $WORK/ObjectDerived.lean \
  Effect4.Program.SigApp Effect4.Program.Object Effect4.Program.Certificate"
lake env sh -c "LEAN_PATH=$WORK/olean:\$LEAN_PATH lean -DwarningAsError=true $WORK/ObjectDerived.lean"
echo "generated: $(wc -l < "$WORK/ObjectDerived.lean") lines, compiled clean"
# The read refusals of `Object.read` have no codec today (open point 7): measure what the generator
# emits for them, with the store's own imports, and compile it.
lake env sh -c ".lake/build/bin/effect4gen Main --group ReadRefusals --qualified-names \
  --imports Effect4.Store.Domain.Read,Effect4.Store.Domain.Derived.Value \
  --out $WORK/ReadRefusalsDerived.lean Effect4.Store.Node.ReadRefusal Effect4.Store.ReadRefusal"
lake env lean -DwarningAsError=true "$WORK/ReadRefusalsDerived.lean"
echo "read refusals: $(wc -l < "$WORK/ReadRefusalsDerived.lean") lines, compiled clean"
python3 -I - "$HERE/ObjectDef.lean" "$WORK/ObjectDerived.lean" "$HERE/../probe-object.lean" "${1:-}" <<'PY'
import sys
carriers_path, derived_path, probe_path, mode = sys.argv[1:5]

def body_after(lines, start):
    for i, line in enumerate(lines):
        if line.startswith(start):
            return lines[i:]
    sys.exit(f"no line starting {start!r}")

carriers = body_after(open(carriers_path).read().splitlines(), "set_option autoImplicit false")
derived = body_after(open(derived_path).read().splitlines(), "set_option autoImplicit false")
probe = open(probe_path).read().splitlines()

def splice(lines, name, body):
    begin, end = f"-- BEGIN {name}", f"-- END {name}"
    i, j = lines.index(begin), lines.index(end)
    return lines[: i + 1] + body + lines[j:], lines[i + 1 : j]

probe2, old_carriers = splice(probe, "carriers", carriers)
probe3, old_derived = splice(probe2, "generated", derived)
if mode == "--write":
    open(probe_path, "w").write("\n".join(probe3) + "\n")
    print("spliced into probe-object.lean")
elif old_carriers == carriers and old_derived == derived:
    print("reproduced: probe-object.lean holds the carriers and the generator's output, byte for byte")
else:
    sys.exit("probe-object.lean differs from a fresh run; rerun with --write")
PY
