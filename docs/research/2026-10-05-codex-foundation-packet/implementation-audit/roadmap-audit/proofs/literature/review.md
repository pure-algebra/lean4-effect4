# Roadmap citation check

The citation needs one narrow correction: Proposition 3.9 concerns composition, not prefix lifting.

## Lynch–Vaandrager

Primary source: [*Forward and Backward Simulations I: Untimed Systems*](https://ir.cwi.nl/pub/1393), Information and Computation 121(2), 1995, pages 214–233.
Printed page 219 of the retained [final PDF](https://ir.cwi.nl/pub/1393/1393D.pdf) was visually checked.

- **Section 3.2, Lemma 3.8, page 219:** let f simulate A forward into B. If A has a finite move from s′ to s with external trace β, and u′ is related to s′, then B has a finite move from u′ to some u related to s, with trace β.
- **Proposition 3.9, page 219:** forward simulation is reflexive and transitive. Its composition proof uses Lemma 3.8.
- **Proposition 3.12, page 219:** a forward simulation from a forest yields a refinement. The forest premise concerns executions, not syntax-tree shape.

Section 2.1, page 217, defines a move through a finite execution fragment and its external trace.
This does not directly establish the project's exact prefix, machine or session equality.

Suggested roadmap wording: “Use the finite-fragment lifting pattern of §3.2, Lemma 3.8. Proposition 3.9 supplies composition.”

## Gambino–Hyland

The owner's TYPES 2003 book gives *Wellfounded Trees and Dependent Polynomial Functors*, pages 210–225.
[Theorem 12](https://link.springer.com/chapter/10.1007/978-3-540-24849-1_14), page 220, provides dependent-polynomial initial algebras in a locally cartesian closed category with W-types.
Lemma 13, pages 220–221, characterizes the indexed-tree construction used in that proof.

These supply conceptual support for well-founded indexed induction.
They do not prove that the project's reference relation has a decreasing finite rank.
That proof must define its address domain, edge relation and measure, then show every admitted reference edge decreases the measure.
Use “proof technique” or “conceptual connection,” not “directly supplied theorem.”

## Scope

This is a citation audit only.
No repository file changed, and no Lean, compiler, build, generator or runtime probe ran.
The web metadata resolved; the fresh PDF fetch timed out.
The retained primary PDF supplies the checked statements.
