# 2026-10-15 Does a `Modeled` codec lower to OCaml? A probe for P1

Status: a finite probe, not authority.
Base: `9fb977c4e` on `refactor/phase1-phase3`.
Role: the measurement that the interop plan's P1 asks for first (`docs/research/2026-10-15-interop-plan/README.md` §5.4).

## The one thing to know first

The derived instance's codec does not lower cleanly, because it runs the carrier fold at run time.
A first-order codec, written as a deriver would write it, lowers to a native OCaml record. It
compiles, and it round-trips. So the deriver should write first-order functions, and the fold
stays their specification.

## Question

P1 types the to-do's host over a Lean structure that derives `Modeled`. Can the LCNF route lower
that structure's codec into OCaml that a provider can use?

## What was run

| Probe | Files | Evidence | Result |
| --- | --- | --- | --- |
| The derived codec of `Todo` and `Status` (`Modeled.image`), as LCNF roots | `probe/ModeledLower.lean` | tested | closure of 109 declarations; refused on two primitives with no row |
| A first-order codec, as a deriver would write it | the same file | tested | closure of 3 declarations; `Ml.checkModule` passes |
| The first-order writer against the fold's writer | `todoToVal_eq` | proved by `rfl` | the two writers are equal by definition |
| The first-order reader against the fold's bytes | the file's `#eval` lines | tested | both readers decode both writers' bytes |
| The lowered codec under `ocamlopt` 5.1.1 | `probe/probe_gen.ml`, `probe/test_probe.ml` | tested | a round trip, a refused malformed frame and the sum's tagged frame, `rc=0` |

The commands, from the repository root:

```bash
lake env lean --root=<src> -o <olean>/Probe/ModeledLower.olean <src>/Probe/ModeledLower.lean
```

```bash
lake env bash -c 'LEAN_PATH=<olean>:$LEAN_PATH lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean --recipe probe/recipe.json'
```

```bash
opam exec --switch=effect4 -- ocamlfind ocamlopt -package zarith -linkpkg eff_types.ml probe_gen.ml test_probe.ml -o test_probe
```

The recipe lists the first-order roots. The fold run listed `encodeTodo`, `decodeTodo`,
`encodeStatus`, `decodeStatus` and `encodeTodos` in their place.

## Findings

### The derived codec runs the carrier fold

`Modeled.image` is `Image.equiv` over `Model.image ty`, and `Model.image` is a fold over `Ty`. At
run time the code evaluates that fold at the instance's type. The closure therefore holds the
carrier algebra, `TyAlgebra`, `Model.Leaves`, `Columns` and `Sigma`. The route cannot spell
`Sigma.snd : β fst` or the identity context's fields, since their types depend on a value.

The run stops earlier, at two primitives with no row: `Int.decLt` and `Int.natAbs`. The fold
builds the `int` arm's image although `Todo` has no integer. No lowered machine code uses an
`Int` primitive: both closure manifests name none.

### A first-order codec lowers to native OCaml

`todoToVal` and `todoOfVal` match on the record frame directly. Their closure is three
declarations. The route declares `type todo = { id : int; title : string; done_ : bool }` and
`type status = Status_pending | Status_closed of string`. A provider in OCaml is then ordinary
code over `todo`.

### The fold stays the specification

The first-order writer equals the fold's writer by `rfl`. A deriver can emit that proof. The
reader's agreement is a theorem over the exact embedding: retraction and exactness pin a reader
to its writer. The recursive deriver needs first-order functions anyway, since the fold cannot
tie a recursive knot (`docs/research/2026-10-15-recursive-types/README.md` §4.2).

### The generator writes its manifest beside the committed ones

`LcnfGen` wrote `ocaml/gen/closure-probe_gen.tsv` although `--out` named a scratch directory.
The manifest's directory does not follow the artifact.

## Proposals

1. `deriving Modeled` writes `toVal` and `ofVal` by structural recursion over the declaration.
   The instance proves them equal to the fold's image. The LCNF route lowers them.
2. The primitive table gains `Int`'s rows inside the profile bound, with the first `Int` field.
3. The closure manifest goes beside the artifact, or where a recipe field names it.

## What this does not establish

- The probe covers one structure of three fields and one sum of two constructors.
- The reader's agreement with the fold is tested on four values, not proved.
- No `Int`, `Option`, `List` or nested field is lowered first-order here.
- No provider is run through `E4_host`. That is P1's step 6.
