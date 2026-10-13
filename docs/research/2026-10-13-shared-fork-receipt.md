# Shared fork origin

The owner requests one origin peg for both fork arms.
This change gives the fork glyph one contour with a shared root.

Base: `889bd326f65aefd8faa02a37427fc5e1b2b47011`.
Branch: `codex/pegs-port`.
Changed declaration: `PegGlyphs.draw`, `tools/Tools/View/Tube/PegGlyphs.lean`.
The `.arrow` arm now uses one `Skeleton.fork` instead of two separate line bodies.
Its root peg stands at grid point `(1,4)`.
The two terminal pegs stand at `(7,2)` and `(7,6)`.
One concave peg shapes the space between the arms.
The vocabulary and program pages consume this same glyph.

No theorem statement or machine observation changes.
The shared contour follows the owner's visual ruling. It establishes no fluid-transfer property.

## Verification

All Lake commands use `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build view-pages Test.Audit.GlyphControls` | Exit 0; 937 jobs |
| `lake env lean docs/research/2026-10-13-codex-pegs-evidence/StrictAudit.lean` | Exit 0 |
| `lake exe view-pages tools/view/out/pegs-fork` | Exit 0 |
| `git diff --check` | Exit 0 |

The existing finite controls accept the new glyph's tangents, path chaining, casing, rounding, and cell bounds.
The browser preview shows both arms starting at the same rounded origin.
The audit reports:

```text
#axiom_audit: 309 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
#axiom_audit: 129 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The narrow build retains the known manifest warning until the coordinator aligns `lakefile.toml`.
The earlier preview remains under `tools/view/out/pegs-final`.
The revised preview is `tools/view/out/pegs-fork/program-pegs.html`.
