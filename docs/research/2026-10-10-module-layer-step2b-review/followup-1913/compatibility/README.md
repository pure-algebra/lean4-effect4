# Compatibility repair follow-up

ML2-C2-01 is repaired in the checked working tree.
The implementation base is `1c98dd94831c060e591cd7e5bef19d6528c5d22a`.
The exact source and fixture hashes are in [inputs.json](inputs.json).

## Claim and placement

The placement remains the gate obligation in [the original review](../../../2026-10-10-module-layer-landing-review/README.md).
It serves R2 through clause C2 of the cross-revision compatibility check.
The observation is C2's verdict on well-formed manifests with unique entries.
It is neither a codec theorem nor a statement about machine execution.
The consumer remains `run`, through `c2`, in `scripts/lib/conservativity.py`.

## Checked repair

`c2` excludes `TAG_MANIFEST` from the named field-change exemption.
The argument-shape manifests retain that exemption.
Changing `defs=30` to `defs=99` is now refused during the field addition and afterward.
The authorized field addition still passes.
Removing its policy permission still causes refusal.
JSON tag changes and named constructor movement, renaming, and removal still cause refusal.
The existing R4 refusal and G6 acceptance remain intact.

An independent Sol 6.1 review runs 24 focused C2 controls.
Each control produces its expected outcome.
The existing mutation battery produces its expected overall verdict for all 29 controls.
R17 exercises the new text-tag refusal through C2 alone; C1, C3, and C4 pass.
No producer, Lean build, or behavior gate runs in this review.

```sh
PYTHONDONTWRITEBYTECODE=1 TMPDIR=/private/tmp python3 scripts/lib/conservativity.py --self-test
PYTHONDONTWRITEBYTECODE=1 python3 /private/tmp/ml2-c2-followup-audit/probe.py
```

The first command runs from the implementation worktree and uses temporary extracts.
The second script changes its candidates only in memory.
Both commands exit with status zero.
The retained script still writes its outputs to the scratch path.
The outputs and input hashes are stored beside this note.
The two repaired input files retain their hashes through the checks.

## Evidence limits

Two earlier limitations remain outside this repair.
`manifest_lines` uses the last occurrence of a family.
A malformed duplicate-family manifest can therefore hide an earlier bad line.
The same control passes before and after this repair.
It lies outside the original finding's unique-entry premise.

The mutation battery checks overall verdicts, then reports each requested clause label.
It does not assert that the named clause supplies the refusal.
R8 reports C4, although C2 rejects its duplicate record entry and C4 passes.
Therefore the 29 outcomes do not establish 29 clause-specific detectors.
R17's retained output identifies the correct refusing clause.

## Next action

Keep the repair and R17 in the implementation landing.
Do not describe these finite controls as a whole-candidate compatibility result.
If the mutation battery is strengthened later, assert the refusing clause before reporting its success label.
Treat duplicate-family refusal as separate parser hardening.
