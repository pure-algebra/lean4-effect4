# Retained baseline at `66ee4657` (DI-47)

Captured 2026-09-09 by the coordinator, **before** any slice appended to an alphabet
(`Err.text` and `Defect.error` in S2, `Eff.catchIf` in S3a, `Ty.lit` in S4b). This directory is
the independent authority the `⊑` compatibility gate (settlement v2, DI-47; slice S5b) compares
the reflected descriptions against. No generator writes here. It changes only by a deliberate,
named promotion command, never by regeneration; a diff in this directory is a review event.

| file | what it is | how it was produced |
| --- | --- | --- |
| `families.json` | every family of the four descriptions (scout C's inventory list) plus `Machine.Err`, `Machine.Defect`, `Store.Kind`, `Machine.HandleKind`: constructors in declaration order, structure fields in order, the mutual block | `lake env lean` on the coordinator's `Inventory.lean` (reflection of the compiled environment at this commit; the source is quoted in `docs/research/2026-09-09-coordinator-log.md`) |
| `eff_manifest.txt` | the OCaml generator's family/constructor manifest at this commit | copy of `ocaml/eff/eff_manifest.txt` |
| `wire-manifest.txt` | the wire tool's family/constructor manifest at this commit | copy of `ocaml/goldens/eff/manifest.txt` |
| `golden-digests.sha256` | SHA-256 of the eight wire goldens (`ocaml/goldens/eff/*.hex`), the 42 `.bin`/`.json`/`.ty` goldens and the corpus and coverage lists under `ocaml/eff/goldens/` | `shasum -a 256` from `ocaml/` |

What the gate must refuse against this baseline (v2 DI-47, scout C §4): a constructor
reordered or removed; a structure field reordered, removed or re-framed; a tag or ordinal
reused; an old golden whose bytes change; a decoder that stops accepting an old value exactly;
an operation that stays readable but loses its permission to execute without saying so. An
append at the end of a family is the one change the gate admits without a promotion.

This file carries no `cut-from:` stamp on purpose: it is not a generated artefact
(`docs/GENERATED.md`), it is a frozen fixture.
