/-
Executable witness for `E4-SCHEMA-CE-043`.

A traversal that follows only direct `Representation` children and
`FilterGroup.checks` misses schemas nested in check annotations as well as
types inside the parameterized element/property/index records. The exact trace
algebra makes omission, duplication, and reordering observable without
assigning Schema denotation.
-/

import Effect4.Schema.Representation

namespace Test.Counterexamples.Schema.RecursiveElimination

open Effect4

private def node (label : String) (children : List (List String)) : List String :=
  label :: children.flatten

private def schemaTraces
    (schemas : Option (List (List String))) : List (List String) :=
  schemas.getD []

private def optionalAnnotationTraces
    (annotation : Option (CheckRepresentationAnnotationOf (List String))) :
    List (List String) :=
  annotation.elim [] (fun value => schemaTraces value.schemas)

/--
Preorder labels for every representation and check node reached by the fold.
Child list order is retained, and the two fields of an index are observed in
parameter-then-type order.
-/
def routeTraceAlgebra :
    Representation.FoldAlgebra (List String) (List String) where
  declaration := fun _ _ types checks => node "Declaration" (types ++ checks)
  reference := fun _ => node "Reference" []
  suspend := fun _ checks thunk => node "Suspend" (checks ++ [thunk])
  null := fun _ checks => node "Null" checks
  undefined := fun _ checks => node "Undefined" checks
  void := fun _ checks => node "Void" checks
  never := fun _ checks => node "Never" checks
  unknown := fun _ checks => node "Unknown" checks
  any := fun _ checks => node "Any" checks
  string := fun _ checks => node "String" checks
  number := fun _ checks => node "Number" checks
  boolean := fun _ checks => node "Boolean" checks
  bigint := fun _ checks => node "BigInt" checks
  symbol := fun _ checks => node "Symbol" checks
  literal := fun _ checks _ => node "Literal" checks
  uniqueSymbol := fun _ checks _ => node "UniqueSymbol" checks
  objectKeyword := fun _ checks => node "ObjectKeyword" checks
  enum := fun _ checks _ => node "Enum" checks
  templateLiteral := fun _ checks parts => node "TemplateLiteral" (checks ++ parts)
  arrays := fun _ checks elements rest =>
    node "Arrays" (checks ++ elements.map ElementOf.type ++ rest)
  objects := fun _ checks properties indexes =>
    node "Objects"
      (checks ++ properties.map PropertySignatureOf.type ++
        indexes.flatMap fun index => [index.parameter, index.type])
  union := fun _ checks types _ => node "Union" (checks ++ types)
  filter := fun representation _ _ =>
    node "Filter" (schemaTraces representation.schemas)
  filterGroup := fun representation _ checks =>
    node "FilterGroup" (optionalAnnotationTraces representation ++ checks)

/--
The smallest hidden-recursion witness: root, filter, and one schema under the
filter's required representation annotation.
-/
def nestedFilterSchema : Representation :=
  .string none
    [.filter
      { id := "effect/test/hidden-schema"
        payload := .null
        schemas := some [.number none []] }
      none false]

/-- A direct-child-only traversal observes only the root and the filter. -/
def shallowRootAndCheckTrace : Representation -> List String
  | .string _ checks =>
      "String" :: checks.map (fun check => CheckTag.tagName check.tag)
  | _ => []

#guard shallowRootAndCheckTrace nestedFilterSchema == ["String", "Filter"]

/- The general fold must also observe the schema nested in the filter. -/
theorem nestedFilterSchema_trace :
    Representation.fold routeTraceAlgebra nestedFilterSchema =
      ["String", "Filter", "Number"] := by
  decide

/--
One finite witness exercising every nontrivial recursive container route:
declaration type parameters and checks; array elements and rest; property and
both index positions; required and optional annotation schemas; and nested
check groups.
-/
def allRecursiveRoutes : Representation :=
  .declaration
    { id := "effect/test/all-recursive-routes", payload := .null }
    none
    [ .arrays none []
        [{ isOptional := false, type := .null none [], annotations := none }]
        [.undefined none []]
    , .objects none []
        [{ name := .string "property"
           type := .void none []
           isOptional := false
           isMutable := false
           annotations := none }]
        [{ parameter := .never none [], type := .unknown none [] }]
    ]
    [ .filterGroup
        (some
          { id := "effect/test/group-schema"
            payload := .null
            schemas := some [.any none []] })
        none
        [.filter
          { id := "effect/test/filter-schema"
            payload := .null
            schemas := some [.string none []] }
          none false]
    ]

/--
Every recursive route has a distinct label. Any omission, duplication, or
route-order change alters this exact trace.
-/
theorem allRecursiveRoutes_trace :
    Representation.fold routeTraceAlgebra allRecursiveRoutes =
      [ "Declaration"
      , "Arrays", "Null", "Undefined"
      , "Objects", "Void", "Never", "Unknown"
      , "FilterGroup", "Any", "Filter", "String" ] := by
  decide

end Test.Counterexamples.Schema.RecursiveElimination
