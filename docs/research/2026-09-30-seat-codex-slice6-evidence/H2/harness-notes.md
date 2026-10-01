# H2 fresh-namespace measurement harnesses

`Baseline.lean` concatenates the E cutover candidates. `PartOne.lean` concatenates their
mechanical H2 counterparts. Both import the installed production `Typed.Assembly` first and
use the same fresh namespace `Research.Slice6.H2`; compile them independently, never import
one from the other. Production Typed is open for support declarations, while the copied
Admission/Residual/Stack/Assembly declarations are local. A local `World` abbreviation pins
the typed world and avoids ambiguity with Machine.World.

The only harness transformations are removal of the source imports, replacement of the
outer namespace commands, and omission of post-namespace proofgraph commands. The copied
statements and proof bodies are otherwise byte-for-byte unchanged. This includes the
existing obligation declarations; no M5–M7 law was added or discharged. PartOne still has
all predicted failures; no repair or `sorry` was inserted.

Compile Baseline first under the same options intended for PartOne. Correct any harness
resolution errors identically in both before interpreting the H2 diagnostic set. Only a
successful baseline makes the comparison meaningful. Lean may recover from a failing proof
internally and emit additional dependent errors; those are not automatically new required
body edits. No compiler command has been run by the preparing seat.

The `.map.json` files contain source hashes, every copied line, module intervals and declaration
intervals. The `.theorems.csv` files list the 67 theorem regions for quick review. The two
harnesses use the same namespace but share no source import or generated object with each
other. Run `python3 map_errors.py Baseline <baseline-log>` or `python3 map_errors.py PartOne
<part-one-log>` from this directory to attribute Lean diagnostics. Its reported region count
is not a repair-cost verdict; inspect the body and whether the error is a cascade.

Static checks verified every copied line against its input and all recorded hashes; the
log-mapper script passed Python syntax parsing. No Lean build, active-source mutation, or
Git operation was performed.
