# Retained TypeScript target proof graph

Status: ported syntax and renderer; target cutover open, 2026-08-31

The graph-bearing owner is `TS-PG-RETAINED-RENDER`. The passive `Style` record
uses the attached `TS-LEAF-STYLE` receipt and has no ceremonial graph of its
own.

```text
TS-SOURCE-PIN --> TS-SYNTAX --> TS-RENDER
                                  |   \
                                  |    --> TS-BYTE-COUNTEREXAMPLES
                                  v
                         TS-TYPED-LOWERING (open)
                                  |
                                  v
                   TS-TSC + EFFECT + LSP HARNESS (open)
```

## Edge ledger

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-closed` | one pinned Foldlab source digest, Effect4 namespace, and the exact type rows in the owning contract and `PORT-MANIFEST.md` |
| construction | `required-closed` | exact constructor and projection signatures plus the default `Expr` receipt in `ExprContract.lean` |
| semantics | `not-applicable` | this packet claims target syntax and bytes, not an Effect4 denotation |
| laws | `required-closed` | the retained recursive printer equations elaborate and the representative reductions are kernel checked |
| representation | `required-closed` | syntax and rendering are separate modules; `Style` is the attached passive leaf; rendering accepts only the retained syntax values |
| counterexamples | `required-open` | escaping and fixed-layout attacks are closed; the checked-target exclusion of `Decl.raw` waits for lowering |
| bridges | `required-open` | no checked Effect4-to-TypeScript lowering or source-target simulation exists yet |
| targets | `required-open` | direct TypeScript, pinned Effect v4, and language-service harnesses are not part of this port |
| trust | `required-closed` | the source and battery build under the repository trust gate; this packet exports no proof theorem |
| coverage | `required-open` | the retained Foldlab file is covered, but the Effect v4 target profile and overload ledger are later work |

The port is usable as a target-syntax library now. It is not approved as the
full generated Effect TypeScript cutover while any required edge remains open.
