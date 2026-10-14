# Exact emitted connector directions

The default tangent check now uses exact emitted decimal coordinates.
The coordinator must also compare connector key sets when checking a replacement renderer.

## Base and head

The base is `3dff3c8ffeb8e82b732af0eefc2c6e8bedcda1cb`.
The implementation head is `c867150d6cd6b65a2dd51d7a132cc68f5a959e76`.
The branch is `codex/connector-check`.
The worktree is `C:/Users/kokok/Dev/effect4-peg-board`.

Only `tools/view/check_connectors.py` changes production tool code.
This receipt and three measured JSON files retain the evidence.
The generated SVG directories remain unchanged and uncommitted.

## Exact observation

`cubic_contours` reads each original decimal token as a Python `Fraction`.
`endpoint_handle` reads the first nonzero endpoint control difference.
`check_contour` requires a nonzero tangent at each end of every side segment.
At each internal side junction, the default check requires a zero determinant and a strictly positive dot product.
It uses no angle epsilon to decide agreement.
The position check compares squared rational distances against its existing `1e-6` tolerance.

Floating-point angles remain diagnostic output.
A positive `--angle-degrees` selects an explicitly approximate comparison.
The retained kink probe also remains a finite floating-point observation.
The two transverse cap junctions remain outside the side-junction check.

## Counterexample to the former numerical check

The control uses incoming milli handles `(1000000,1000001)` and outgoing milli handles `(1000001,1000002)`.
Their exact determinant is `-1`.
Their approximate angle is below the former `1e-7` degree allowance.
The default check now refuses this nonparallel pair.
Separate controls refuse a constant side and oppositely directed tangents.

## Connector occurrence comparison

`--baseline` accepts a directory or file of SVG inputs.
The comparison requires unique selected SVG filenames.
It reports missing and unexpected frames.
For matching frames, it independently reports missing and unexpected connector keys.
Contour findings remain present even when the key comparison fails.
The comparison uses the same finite filled-forward-key profile as the contour check.
It asserts no relation for unselected keys.

## Commands and measured results

The input directories belong to the main integration worktree.
The commands only read those directories.

| Command | Result | Evidence |
| --- | --- | --- |
| `python tools/view/check_connectors.py --self-test --json docs/research/2026-10-13-connector-check-evidence/ExactSelfTests.json` | Exit 0; 18 controls pass | `ExactSelfTests.json` |
| `python tools/view/check_connectors.py <continuous-after> --baseline <continuous-before> --json docs/research/2026-10-13-connector-check-evidence/ExactAfter.json` | Exit 0; 16 frames, 103 connectors, 998 side junctions, no findings | `ExactAfter.json` |
| `python tools/view/check_connectors.py --kink-fixture <continuous-before>/009.svg --json docs/research/2026-10-13-connector-check-evidence/ExactKink.json` | Exit 0; the retained defect's cubic signature agrees | `ExactKink.json` |
| `git diff --check` | Pass | Command output |

`<continuous-after>` is `C:/Users/kokok/.codex/worktrees/pegs-port/lean4-effect4/tools/view/out/continuous-after`.
`<continuous-before>` is its sibling directory `continuous-before`.
All sixteen selected filenames and all connector key sets agree.
Each JSON frame records the SHA256 of the input bytes.

## Scope and remaining work

This tool supplies finite R14 rendering controls under the concept `initial-algebras-folds`.
No Lean declaration, proof obligation, or axiom exemption changes.
No Lake build or axiom audit applies to this Python-only change.
No external runtime behaviour gate is reached.

The exact decision concerns rational directions in the emitted cubic profile.
It establishes neither global absence of intersections nor correct docking, width, curvature, clearance, or machine meaning.
The key comparison detects missing selected occurrences, not an arbitrary program observation relation.
The existing syntax checker still bounds admitted coordinates to finite host numbers.
Positive angle tolerances and the kink solver retain their stated floating-point boundary.
