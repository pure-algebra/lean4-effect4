# lean4-markdown as prior art for the typed human-surface emitter

Status: project research input, 2026-08-26

Claim posture: bounded design comparison only. Route (b) — own the module,
credit the pattern — was ruled by the operator in-session on 2026-08-26; no
code is copied and no dependency is added. Convergence to the upstream
dependency, if the ecosystem ever warrants it, is an ordinary refactor with
`Effects/Conformance/Markdown.lean` as the seam.

## Source identity

| Field | Value |
| --- | --- |
| Repository | [`predictable-machines/lean4-markdown`](https://github.com/predictable-machines/lean4-markdown) |
| Revision at study | `main` HEAD `ee1aa6b9c872e11315db7596bdd3713bf12fcf24` (shallow study clone, 2026-08-26) |
| Version | `0.1.3`; toolchain `leanprover/lean4:v4.32.0`; zero dependencies |
| License | MIT, declared in the README; the repository carries no LICENSE file |
| Shape | one 214-line module: block/inline AST, pure renderers, `Markdown.Represent` typeclass, table helpers |

## Patterns adopted (re-expressed, not copied)

1. **The `Represent` typeclass** — `α → List MarkdownTag` is exactly the
   conformance workflow's projection pattern. Re-expressed as `ToMarkdown`
   with `blocks : α → List Block`; ledger rows, briefing sections, and
   manifest family headers each become instances, and every human surface is
   `render ∘ blocks` over typed values.
2. **Arity-checked tables** — headers as `Vector String n`, rows as
   `Vector Cell n`, so a row with a missing column does not elaborate. The
   kits-as-fields philosophy applied to the human surface.

## The gap that decided route (b)

The upstream renderer performs no escaping: `.text s` emits `s` raw, so a
plain-meaning sentence containing `|` silently breaks table geometry, and
backticks or asterisks mangle prose. The conformance ledger is a gate
surface — byte-compared and transition-checked — and must render well-formed
output for every admitted input. The owned module therefore escapes inline
text by a declared deterministic policy as the *default* path, with the
policy documented beside the code; escape-soundness is a candidate for a
small law under the workflow's own reflection form later.

## Does not transfer

- The unescaped rendering path (the gap above).
- `li : String` list items and the `br` constructor — the owned module keeps
  bullets as inline lists and omits what the surfaces do not need.
- The v4.32.0 toolchain and the `@ version-tag` installation guidance — no
  dependency exists to pin.
