# Source configuration consolidation

The finalizer goal needs full source annotations at every stored code location.
The existing configuration has the right locations, but fixes their annotation to the direct fragment.

Placement: scope-lifetime-finalization R11 and store-typing R4.
Consumers: `FinalizerRun.once_placed_outside_census` and the existing source configuration claims.

Parameterize the existing configuration by a code predicate, a captured-scope predicate, and its race permission.
Keep terminal reply and countdown permissions separate.
Move its existing metadata transports to this parameterized predicate.
Keep the source configuration names as instances.
Reuse its command and decision transports with explicit native evaluation premises.
Use the full finalizer annotation to supply those premises.

This change adds no stored representation or machine behavior.
Local configuration closure establishes neither history funding nor release custody.
The finalizer endpoint still needs their composition.
