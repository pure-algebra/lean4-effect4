/-! ## Acceptance guards for the generated Schema Fold

Appended verbatim by `--append tools/Effect4Gen/guards/schemafold.lean` into
`src/Effect4/Schema/Fold.lean`.

These guards exercise:
1. One tree that reaches every composite position of the family: a `List Check` under a
   representation, a `List Representation`, the three record lists of `arrays` and
   `objects`, and both routes into a check's `representation.schemas` — the second
   recursion edge that `E4-SCHEMA-CE-033` names.
2. The identity algebra rebuilds that tree (`cata_id_representation` computed, not proved).
3. `foldMap_representation` counts the representation and the check nodes of it, the check
   route through a filter's annotation included.
4. The red control: one algebra that drops the `arrays` elements rebuilds a *different*
   tree, and the count drops by exactly the one node it dropped. A guard that passed for
   both algebras would be pinning nothing.
5. The generated constructor equations are exactly a `RepresentationHom` of the fold: the
   24 equations are handed to the structure's 24 fields, so a mismatch between the two
   emitted shapes is a type error here rather than a surprise in a consumer.
-/

namespace SchemaFoldAcceptance

open Effect4

def ann0 : Annotations := none
def ann1 : Annotations := some [⟨"title", Json.str "t"⟩]

/-- Every composite position of the family in one value. -/
def sample : Representation :=
  .arrays ann1
    [.filter ⟨"f", Json.null, some [.never ann0 [], .string ann0 []]⟩ ann0 false]
    [⟨true, .number ann0 [], ann1⟩]
    [.objects ann0 []
        [⟨.string "p", .boolean ann0 [], false, true, ann1⟩]
        [⟨.string ann0 [], .bigint ann0 []⟩],
      .union ann0
        [.filterGroup (some ⟨"g", Json.null, none⟩) ann0
          [.filter ⟨"h", Json.null, some [.void ann0 []]⟩ ann0 true]]
        [.reference ⟨"ref"⟩, .templateLiteral ann0 [] [.symbol ann0 []]]
        .anyOf]

/-! (2) The identity algebra rebuilds the tree. -/
#guard cata_representation RepresentationAlgebra.id sample == sample

def representationNodes (representation : Representation) : Nat :=
  foldMap_representation 0 (· + ·) representation (f_representation := fun _ => 1)

def checkNodes (representation : Representation) : Nat :=
  foldMap_representation 0 (· + ·) representation (f_check := fun _ => 1)

/-! (3) Thirteen representation nodes: the three the two filters' `schemas` hold are
reached, so the fold walks the second recursion edge. Three check nodes: the tuple's
filter, the union's group, and the filter inside it. -/
#guard representationNodes sample == 13
#guard checkNodes sample == 3

/-- (4) The red control: the identity algebra with one child dropped. -/
def dropElements : RepresentationAlgebra RepresentationSelfCarrier :=
  { RepresentationAlgebra.id with
    representation_arrays := fun annotations checks _ rest =>
      .arrays annotations checks [] rest }

#guard !(cata_representation dropElements sample == sample)
#guard representationNodes (cata_representation dropElements sample) == 12

/-- (5) The generated constructor equations are a `RepresentationHom` of the fold. -/
def cataHom {R : RepresentationFam → Type} (alg : RepresentationAlgebra R) :
    RepresentationHom alg where
  f_representation := cata_representation alg
  f_check := cata_check alg
  h_representation_declaration := cata_representation_declaration alg
  h_representation_reference := cata_representation_reference alg
  h_representation_suspend := cata_representation_suspend alg
  h_representation_null := cata_representation_null alg
  h_representation_undefined := cata_representation_undefined alg
  h_representation_void := cata_representation_void alg
  h_representation_never := cata_representation_never alg
  h_representation_unknown := cata_representation_unknown alg
  h_representation_any := cata_representation_any alg
  h_representation_string := cata_representation_string alg
  h_representation_number := cata_representation_number alg
  h_representation_boolean := cata_representation_boolean alg
  h_representation_bigint := cata_representation_bigint alg
  h_representation_symbol := cata_representation_symbol alg
  h_representation_literal := cata_representation_literal alg
  h_representation_uniqueSymbol := cata_representation_uniqueSymbol alg
  h_representation_objectKeyword := cata_representation_objectKeyword alg
  h_representation_enum := cata_representation_enum alg
  h_representation_templateLiteral := cata_representation_templateLiteral alg
  h_representation_arrays := cata_representation_arrays alg
  h_representation_objects := cata_representation_objects alg
  h_representation_union := cata_representation_union alg
  h_check_filter := cata_check_filter alg
  h_check_filterGroup := cata_check_filterGroup alg

end SchemaFoldAcceptance
