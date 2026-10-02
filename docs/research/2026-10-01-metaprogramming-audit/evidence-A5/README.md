# A5 bounded printing experiments

Base `8c9be258`, implementation head `9190c779`, Lean 4.33.1. No production producer,
delaborator or fixture was changed. See per-command JSON for exact invocations and bounds.

## Source text

PrintingOptions copies the existing srcOf helper (the same implementation in Rows,
LayerView, View, Fold and Authoring). With the type of nativeReservedServiceTypes,
changing pp.notation yields:

- Default: `List (Effect4.ServiceKey × Effect4.Program.Ty)`
- Notation disabled: `List (Prod Effect4.ServiceKey Effect4.Program.Ty)`

Restoring the options restores the original bytes. This proves only this finite helper
example is context-sensitive. The actual generator drivers create fresh Core contexts with
default options: no supported CLI invocation was found that imports interactive options.
Compiler/default/environment changes are input changes. No generator or regeneration ran.
The first probe invocation lacked the Lean command elaborator import; final invocation passed.

## Local goal display

DisplayBaseline is the unchanged Test/Program/TypedProgBindRed.lean; it passed.
DisplayPrototype adds a local literal-only Val.nat unexpander and notation; its unchanged
expectations correctly reject the changed first diagnostic. Exactly **one of two** existing
message fixtures in this battery changes, in two displayed occurrences:

`Typed.Fits w (Val.nat 0) ...` → `Typed.Fits w value%[0] ...`.

DisplayControls updates that one expected message and tests the notation's elaboration
(by rfl), a numeral's display, explicit/notation-disabled printing, unapplied constructor,
symbolic argument fallback, and restoration outside the namespace. All pass. The battery's
six printed theorem axiom lists remain `[propext, Quot.sound]`. Probe drafts had two harness
errors (reserved variable name and ambiguous ppExpr); fixed before the passing run.

The selected one-battery count is not a global fixture-impact count. The proposed shipping
change is **none**: Val.nat is already compact, and replacing it with a new spelling provides
little demonstrated benefit. If richer display is wanted later, start in an opt-in tooling
scope with its own notation; do not print Eff as the existing eff authoring macro, which has
a different result type. A global display change still requires a full measured fixture
inventory and the coordinator's ruling. No target print/read law is implied by this example.

Source/artifact closure verification: 1,092 hashes over 405 modules, no mismatches. The fresh
module and earlier-slice command receipts cover rebuilt artifacts. This is narrow testing,
not a whole-repository build or gate.
