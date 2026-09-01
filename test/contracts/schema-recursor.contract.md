# Schema representation recursor contract packet

Status: **Pass-B FROZEN; implementation REQUIRED-BLOCKED**. The production
fence is the `SC-REP-03-RECURSOR` addition to
`Effect4/Schema/Representation.lean`. The breaker-owned Lean battery is
`Effect4Test/Schema/RepresentationFoldContract.lean`; the retained executable
attack is
`Effect4Test/Counterexamples/Schema/RecursiveElimination.lean`. A builder must
make both files green without editing this packet, the battery, or the attack.

This packet closes only the general nondependent-elimination share of
`SC-REP-03`. It does not define Schema denotation, document reference meaning,
wire encoding, host revival, an effectful interpreter, or a normalization.

## Existing-type disposition and minimality

The fold eliminates the existing mutually recursive `Representation` and
`Check` carriers. It reuses all four existing parameterized child records:

- `CheckRepresentationAnnotationOf` for optional lists of nested schemas;
- `ElementOf` for tuple element types;
- `PropertySignatureOf` for object property types; and
- `IndexSignatureOf` for index parameter and result types.

No `RepresentationF`, `CheckF`, `RecursiveRepresentation`, `SchemaTree`,
`KeywordKind`, or second payload carrier is permitted. A one-layer base
functor would duplicate the complete constructor alphabet solely to expose a
fold, while the existing parameterized child records already expose every
nested occurrence that needs substitution.

The only new carrier is the algebra of handlers. It has two result sorts,
`rho` for a representation and `kappa` for a check. Collapsing those sorts into
one would force every consumer to inject and project a sum or accept impossible
results. Splitting them mirrors the existing mutual family without duplicating
either source carrier.

The fold is pure and nondependent. This is the weakest sufficient composition
for analysis, rendering, counting, and later denotational algebras. Monadic or
effectful elimination is not part of this edge; a consumer can choose an
effectful result type without changing the traversal API.

## Public declarations

The builder owes exactly one algebra and two folds. Their result sorts use the
same `Type` universe as the existing workshop signature; this packet does not
silently widen that already-tested public surface:

```lean
structure Effect4.Representation.FoldAlgebra
    (rho kappa : Type) where
  declaration : RepresentationAnnotation -> Annotations ->
    List rho -> List kappa -> rho
  reference : ReferenceKey -> rho
  suspend : Annotations -> List kappa -> rho -> rho
  null : Annotations -> List kappa -> rho
  undefined : Annotations -> List kappa -> rho
  void : Annotations -> List kappa -> rho
  never : Annotations -> List kappa -> rho
  unknown : Annotations -> List kappa -> rho
  any : Annotations -> List kappa -> rho
  string : Annotations -> List kappa -> rho
  number : Annotations -> List kappa -> rho
  boolean : Annotations -> List kappa -> rho
  bigint : Annotations -> List kappa -> rho
  symbol : Annotations -> List kappa -> rho
  literal : Annotations -> List kappa -> LiteralValue -> rho
  uniqueSymbol : Annotations -> List kappa -> GlobalSymbolKey -> rho
  objectKeyword : Annotations -> List kappa -> rho
  enum : Annotations -> List kappa -> List EnumEntry -> rho
  templateLiteral : Annotations -> List kappa -> List rho -> rho
  arrays : Annotations -> List kappa -> List (ElementOf rho) ->
    List rho -> rho
  objects : Annotations -> List kappa -> List (PropertySignatureOf rho) ->
    List (IndexSignatureOf rho) -> rho
  union : Annotations -> List kappa -> List rho -> UnionMode -> rho
  filter : CheckRepresentationAnnotationOf rho -> Annotations -> Bool -> kappa
  filterGroup : Option (CheckRepresentationAnnotationOf rho) ->
    Annotations -> List kappa -> kappa

Effect4.Representation.fold :
  Representation.FoldAlgebra rho kappa -> Representation -> rho

Effect4.Check.fold :
  Representation.FoldAlgebra rho kappa -> Check -> kappa

Effect4.Representation.FoldAlgebra.rebuild :
  Representation.FoldAlgebra Representation Check

Effect4.Representation.fold_rebuild :
  forall representation,
    Representation.fold Representation.FoldAlgebra.rebuild representation = representation

Effect4.Check.fold_rebuild :
  forall check, Check.fold Representation.FoldAlgebra.rebuild check = check
```

There are no public list, option, annotation, element, property, or index fold
helpers. Those are implementation details. The public equations below are
stated with ordinary `List.map`, `Option.map`, and the existing record
constructors, so a consumer never depends on a recursion-compilation artifact.

## Exhaustive recursive-route census

Every occurrence in this table must be replaced by its corresponding fold
result before the enclosing algebra handler is invoked.

| Route | Source field | Algebra field receives |
| --- | --- | --- |
| R1 | `Declaration.typeParameters` | `List rho` in source order |
| R2 | every non-`Reference` node's `checks` | `List kappa` in source order |
| R3 | `Suspend.thunk` | `rho` |
| R4 | `TemplateLiteral.parts` | `List rho` in source order |
| R5 | `Arrays.elements[*].type` | `List (ElementOf rho)`, other fields unchanged |
| R6 | `Arrays.rest` | `List rho` in source order |
| R7 | `Objects.propertySignatures[*].type` | `List (PropertySignatureOf rho)`, other fields unchanged |
| R8 | `Objects.indexSignatures[*].parameter` | mapped `IndexSignatureOf rho.parameter` |
| R9 | `Objects.indexSignatures[*].type` | mapped `IndexSignatureOf rho.type` |
| R10 | `Union.types` | `List rho` in source order |
| R11 | `Filter.representation.schemas` | `CheckRepresentationAnnotationOf rho` |
| R12 | `FilterGroup.representation[*].schemas` | `Option (CheckRepresentationAnnotationOf rho)` |
| R13 | `FilterGroup.checks` | `List kappa` in source order |

`Reference` is the sole recursive leaf. `Suspend.checks` is still traversed on
the raw carrier even though field admission later requires it to be empty. A
general fold may not silently assume admitted input.

## Computation laws

The public equation theorems are named and marked `[simp]`:
`Representation.fold_<constructor>` and `Check.fold_<constructor>`, with all
twenty-four constructor names represented. The fixed battery states their
complete Lean types. Writing `F = Representation.fold algebra` and
`G = Check.fold algebra`, their content is:

```text
F (declaration rep ann tps checks)
  = algebra.declaration rep ann (map F tps) (map G checks)
F (reference key) = algebra.reference key
F (suspend ann checks thunk)
  = algebra.suspend ann (map G checks) (F thunk)

F (null ann checks)          = algebra.null ann (map G checks)
F (undefined ann checks)     = algebra.undefined ann (map G checks)
F (void ann checks)          = algebra.void ann (map G checks)
F (never ann checks)         = algebra.never ann (map G checks)
F (unknown ann checks)       = algebra.unknown ann (map G checks)
F (any ann checks)           = algebra.any ann (map G checks)
F (string ann checks)        = algebra.string ann (map G checks)
F (number ann checks)        = algebra.number ann (map G checks)
F (boolean ann checks)       = algebra.boolean ann (map G checks)
F (bigint ann checks)        = algebra.bigint ann (map G checks)
F (symbol ann checks)        = algebra.symbol ann (map G checks)
F (objectKeyword ann checks) = algebra.objectKeyword ann (map G checks)

F (literal ann checks value)
  = algebra.literal ann (map G checks) value
F (uniqueSymbol ann checks key)
  = algebra.uniqueSymbol ann (map G checks) key
F (enum ann checks entries)
  = algebra.enum ann (map G checks) entries
F (templateLiteral ann checks parts)
  = algebra.templateLiteral ann (map G checks) (map F parts)
F (arrays ann checks elements rest)
  = algebra.arrays ann (map G checks)
      (map (ElementOf.map-type F) elements) (map F rest)
F (objects ann checks properties indexes)
  = algebra.objects ann (map G checks)
      (map (PropertySignatureOf.map-type F) properties)
      (map (IndexSignatureOf.map-both F) indexes)
F (union ann checks types mode)
  = algebra.union ann (map G checks) (map F types) mode

G (filter rep ann aborted)
  = algebra.filter (map rep.schemas F) ann aborted
G (filterGroup rep ann checks)
  = algebra.filterGroup (map (map rep.schemas F) rep) ann (map G checks)
```

The `map-type`, `map-both`, and annotation-map spellings above are explanatory
notation only. The Lean battery expands them as record literals so no public
mapping declaration is implied. Nonrecursive fields are copied exactly.

These are computation laws, not denotational laws. They say which already
folded children each handler sees; they assign no meaning to the handler's
result.

The rebuild algebra applies the original 22 representation and two check
constructors to the recursively rebuilt fields. `Representation.fold_rebuild`
and `Check.fold_rebuild` are the mutual identity laws. They establish that the
fold retains enough structure to reconstruct either source family; they do not
replace the route equations, because passing an original nested record instead
of its recursively substituted form can make a rebuild test pass while still
breaking arbitrary algebras.

## Counterexample `E4-SCHEMA-CE-043`

The false design claim is:

> Traversing direct `Representation` children and `FilterGroup.checks` is a
> complete general recursion over `Representation` and `Check`.

The smallest witness is a `String` root with one `Filter`; the filter's
required representation annotation contains one schema. A shallow trace is
`[String, Filter]`. The contracted trace is `[String, Filter, Number]`. The
durable file also contains a twelve-label witness that jointly exercises type
parameters, checks, array elements and rest, object properties and both index
positions, both annotation-schema routes, and a check group. Every route has a
different label, so omission, duplication, and reordering each change the
expected trace.

This counterexample is distinct from, and attached to, `E4-SCHEMA-CE-033`.
That earlier row discovered all three Check recursion paths: required
`Filter.representation.schemas`, optional
`FilterGroup.representation.schemas`, and `FilterGroup.checks`; it proves the
field-admission judgment must follow them. `E4-SCHEMA-CE-043` reuses those
three paths and extends the attack across every recursive container route of
the reusable public eliminator.

## Proof-graph allocation

This packet attaches to the existing required edge:

```text
SCHEMA-PG-PAYLOAD / SC-REP-03-RECURSOR
  identity      -> one FoldAlgebra over existing carriers
  construction  -> exact two-sorted handler signatures
  laws          -> twenty-four public computation equations
  reconstruction -> rebuild algebra and both mutual identity theorems
  recursion     -> R1 through R13, finite structural decrease
  counterexample -> E4-SCHEMA-CE-043 retained
  trust         -> axiom receipts for all equation theorems
  coverage      -> fixed battery plus generated structural-assurance join
```

A proof graph is required here because this is a nontrivial mutual recursive
eliminator and directly closes a cutover-bearing payload edge. Private helper
recursions receive no separate graph.

## Rejected designs

1. **Generated mutual recursor signature.** Rejected: Lean's nested mutual
   recursor exposes container motives that are compiler/elaborator detail. The
   earlier payload packet already ruled that signature out as a public API.
2. **A second one-layer syntax carrier.** Rejected: it duplicates all 24 node
   forms and creates another representation that later bridges must relate.
3. **One keyword handler indexed by `RepresentationTag`.** Rejected: it either
   accepts impossible non-keyword tags or requires the forbidden duplicate
   `KeywordKind` alphabet.
4. **One result sort for both families.** Rejected: it erases the existing
   typed distinction and forces impossible cases into every consumer.
5. **Direct-child traversal.** Rejected by `E4-SCHEMA-CE-043`: parameterized
   child records and check annotations contain real recursive occurrences.
6. **An effectful or monadic fold.** Rejected for this edge: effects are a
   consumer choice, not part of raw structural elimination.
7. **`FoldHom`, a dependent algebra, or a fusion framework.** Rejected from
   this first edge: none is needed to state exhaustive elimination,
   computation, or reconstruction. A later optimization can contract a fusion
   theorem without enlarging the foundational carrier now.

## Decrease, frame, and trust

The source values are finite trees. The satisfiability probe establishes that
the whole mutual block elaborates with explicit arguments and
`termination_by structural` for the representation, check, list, record, and
option inputs. That structural form is required. A `sizeOf`/well-founded
replacement is rejected because it needlessly weakens the already-achieved
trust result. Private helper functions are permitted; `partial`, `unsafe`,
`sorry`, custom axioms, and a `Quot.sound`-bearing termination proof are not.

The frame is the input value and algebra only. There is no state, scheduler,
resource, host callback, or reference-table lookup.

`#print axioms` on the satisfiability probe reports an empty list for
`Representation.FoldAlgebra`, `Representation.fold`, and `Check.fold`. Every
exported computation theorem must likewise be axiom-free. The builder adds the
axiom report and generated-assurance rows; those closure artifacts are not
breaker-owned and are not frozen by this packet.

## RED and acceptance commands

The current production fence has no fold declarations. The breaker command is:

```text
lake env lean -DmaxErrors=10000 --json \
  Effect4Test/Schema/RepresentationFoldContract.lean
lake env lean -DmaxErrors=10000 --json \
  Effect4Test/Counterexamples/Schema/RecursiveElimination.lean
```

At freeze both commands must exit nonzero because the public algebra, folds,
and equation theorems are absent. The high error cap is mandatory so the
battery reaches the final constructor law.

Freeze receipt:

- battery SHA-256
  `4de2a571131c843e83a036fcb518b45b2f1272caf3ec1467e601bc7e4510396b`;
- attack SHA-256
  `6625927071bd376f3088f2086c50f03d6440c3921e1fac94f7968d54e20197d9`;
- battery exit 1 with 84 of 84 errors in
  `lean.unknownIdentifier._namedError`, reaching the final
  `Check.fold_filterGroup` law;
- attack exit 1 with 3 of 3 errors in
  `lean.unknownIdentifier._namedError`, reaching the complete twelve-label
  trace; and
- exact missing public family: `Representation.FoldAlgebra`,
  `Representation.fold`, `Check.fold`,
  `Representation.FoldAlgebra.rebuild`, both `fold_rebuild` theorems, and the
  22 plus 2 named constructor equations.

After implementation both commands must exit zero, followed by the owning
Schema axiom report, generated structural-assurance gate and its reaction
test, and the default Lake build. A green local battery closes no document,
wire, denotation, or host-equivalence edge.
