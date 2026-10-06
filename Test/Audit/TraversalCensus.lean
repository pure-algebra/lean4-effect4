import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive
import Test.Audit.ExhaustiveFixture
import Test.Audit.TraversalFixture

/-!
# The traversal census — how every definition reads each free object

Builds print the census (`lake build Test.Audit.TraversalCensus`); the census of the tree is not
asserted. The `structural` and `wf` rows of each census are the exemption list of the principle
"every traversal is a fold"; the count is the distance from it (`one-level` rows are listed and
not counted). Read against `docs/core/system-map.md` §§5–6 and `docs/core/traversal-census.md`.

The instrument's own red controls are asserted (2026-10-01; the organization verifier's three
blind spots, `docs/research/2026-10-01-formal-pass/organization/verify.md` §3 M1): the census
of the planted shapes in `Test/Audit/TraversalFixture.lean`, one row per shape, and the class of
four definitions of the tree it used to misread — `Ty.sub` is `wf` (its fixpoint sits in a
`_unary` helper over `WellFounded.Nat.fix`; it was printed `opaque`), `Codegen.Types.ofNormalized`
is a `[private]` structural row (private definitions were no rows), `Ty.isFactor` is `one-level`
(its `match` compiles through a sparse `casesOn` named after `Ty.infer`; it was printed `opaque`),
and `Ty.closed` stays `structural`.

A fold row names its algebra by the name it was written with (2026-10-01, seat G's owed item 4):
`Codegen.Schema.representation` and `Codegen.Schema.check` fold through the private
`printAlgebra`, which the census printed as
`_private.Effect4.Codegen.Schema.0.Effect4.Codegen.Schema.printAlgebra`. The two rows are pinned
by substring (`whitespace := lax`, so no line number and no tab is part of the pin) against the
tree's `Representation` census.

Beside it, the exhaustiveness inventory: which matches on a type have no catch-all, and so
are the definitions a new constructor refuses. It is printed, not asserted, for the same
reason the census is — `docs/core/decisions.md` row 34 keeps the census an instrument, and the
gate over compiled default arms is the case-site policy (`make check-cases`). Read it before
appending a constructor: `lake env lean Test/Audit/TraversalCensus.lean`.

The one assertion here is the inventory's own red control, over
`Test/Audit/ExhaustiveFixture.lean`: a match that names every constructor, with no wildcard,
must be reported
`catchAll false`, the same match closed by `| _ =>` must be reported `catchAll true`, a
match on `Term` must not be reported at all, and a private definition must be reported under the
name it was written with, marked `[private]`.

One control is for the commands' syntax. The clause `under Some.Prefix` of `#traversal_census`,
`#traversal_class` and `#exhaustive_gate` makes `under` a keyword in that place only. A
hypothesis named `under` elaborates below, beside a command that uses the clause.
-/

/--
info: #traversal_census Effect4.Program.Ty (family [Effect4.Program.Ty]) under Test.Audit.TraversalFixture: 9 definitions take a family value (1 private) — fold 0, generated 0, structural 3 (of which 0 with a fold beside them, 0 instance implementations), wf 2 (of which 0 with a fold beside them), one-level 2 (of which 0 with a fold beside them), delegates 1, opaque 1; declared folds: []
  delegates	Test.Audit.TraversalFixture:86	Test.Audit.TraversalFixture.viaDepth	(Ty)	→ [Test.Audit.TraversalFixture.depth]
  one-level	Test.Audit.TraversalFixture:59	Test.Audit.TraversalFixture.notUnion	(Ty)
  one-level	Test.Audit.TraversalFixture:64	Test.Audit.TraversalFixture.isOption	(Ty)
  opaque	Test.Audit.TraversalFixture:88	Test.Audit.TraversalFixture.pairUp	(Ty)
  structural	Test.Audit.TraversalFixture:54	Test.Audit.TraversalFixture.privateDepth [private]	(Ty)
  structural	Test.Audit.TraversalFixture:72	Test.Audit.TraversalFixture.depth	(Ty)
  structural	Test.Audit.TraversalFixture:78	Test.Audit.TraversalFixture.fuelDepth	(Ty)
  wf	Test.Audit.TraversalFixture:36	Test.Audit.TraversalFixture.wfPair	(Ty)
  wf	Test.Audit.TraversalFixture:45	Test.Audit.TraversalFixture.fuelWalk	(Ty)
#traversal_census done: 9 rows; 1 modules under Test.Audit.TraversalFixture scanned
-/
#guard_msgs in
#traversal_census Effect4.Program.Ty under Test.Audit.TraversalFixture

-- The word `under` is a keyword of the three commands and of no other place (`&" under "`,
-- 2026-10-06). This file's environment holds the three syntaxes, and a hypothesis may have the
-- name. With the token reserved, this line did not parse: `unexpected token 'under'`.
example (under : True) : True := under

/--
info: #traversal_class Effect4.Program.Ty under Effect4:
wf	Effect4.Program.Ty.sub
structural	Effect4.Codegen.Types.ofNormalized [private]
one-level	Effect4.Program.Ty.isFactor
structural	Effect4.Program.Ty.closed
-/
#guard_msgs in
#traversal_class Effect4.Program.Ty for Effect4.Program.Ty.sub Effect4.Codegen.Types.ofNormalized
  Effect4.Program.Ty.isFactor Effect4.Program.Ty.closed

/--
Effect4.Codegen.Schema.representation (Representation) Effect4.Codegen.Schema.printAlgebra
-/
#guard_msgs (whitespace := lax, substring := true) in
#traversal_census Effect4.Representation

/--
Effect4.Codegen.Schema.check (Check) Effect4.Codegen.Schema.printAlgebra
-/
#guard_msgs (whitespace := lax, substring := true) in
#traversal_census Effect4.Representation

#traversal_census Effect4.Program.Eff
#traversal_census Effect4.Program.Ty
#traversal_census Effect4.Program.Term
#traversal_census Effect4.Representation
#traversal_census Effect4.Store.Val

/--
info: #exhaustive_gate Effect4.Program.Ty (family [Effect4.Program.Ty]) under Test.Audit.ExhaustiveFixture: 3 match(es) read it, 1 with no catch-all — appending a constructor refuses exactly those
  Test.Audit.ExhaustiveFixture.catchAllAbsent	Test.Audit.ExhaustiveFixture	Test.Audit.ExhaustiveFixture.catchAllAbsent.match_1	discr 0	alts 28	catchAll false
  Test.Audit.ExhaustiveFixture.catchAllPresent	Test.Audit.ExhaustiveFixture	Test.Audit.ExhaustiveFixture.catchAllPresent.match_1	discr 0	alts 4	catchAll true
  Test.Audit.ExhaustiveFixture.privateCatchAll [private]	Test.Audit.ExhaustiveFixture	Test.Audit.ExhaustiveFixture.privateCatchAll.match_1	discr 0	alts 2	catchAll true
#exhaustive_gate done: 3 rows; 1 modules under Test.Audit.ExhaustiveFixture scanned
-/
#guard_msgs in
#exhaustive_gate Effect4.Program.Ty under Test.Audit.ExhaustiveFixture

#exhaustive_gate Effect4.Program.Ty
#exhaustive_gate Effect4.Program.Term
#exhaustive_gate Effect4.Store.Val
