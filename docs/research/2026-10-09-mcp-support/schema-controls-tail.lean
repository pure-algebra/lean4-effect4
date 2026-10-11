
namespace McpSchemaControls
open Effect4 Effect4.Store ProbeMcp

def zeroHex : String := String.ofList (List.replicate 64 '0')
def refDoc : ShapeDoc := ⟨.anyRef, []⟩
def refJson (kind : String) : Json := .obj [("kind", .str kind), ("address", .str zeroHex)]
def duplicateDoc : ShapeDoc :=
  ⟨.sum "S" [("Same", 0, [("x", .nat)]), ("Same", 1, [("x", .nat)])], []⟩
def distinctDoc : ShapeDoc :=
  ⟨.sum "S" [("First", 0, [("x", .nat)]), ("Second", 1, [("x", .nat)])], []⟩
def sumValue : Val := .ctor 1 [.nat 0]
def rowDoc : ShapeDoc := Canonical.shape (Effect4.Row Nat)
def rowJson (ns : List Nat) : Json := .arr (ns.map Effect4.Arch.Json.ofNat)

def checks : List (String × Bool × Bool) :=
  [("known-reference-schema", validDoc refDoc (refJson "schema"), true),
   ("known-reference-reader", (refDoc.read (refJson "schema")).isSome, true),
   ("unknown-reference-schema", validDoc refDoc (refJson "notAKind"), true),
   ("unknown-reference-reader", (refDoc.read (refJson "notAKind")).isSome, false),
   ("distinct-cases-tags-valid", distinctDoc.wellTagged, true),
   ("distinct-cases-value-fits", distinctDoc.accepts sumValue, true),
   ("distinct-cases-print-validates", validDoc distinctDoc (distinctDoc.print sumValue), true),
   ("distinct-cases-read-restores-value", distinctDoc.read (distinctDoc.print sumValue) == some sumValue, true),
   ("duplicate-case-names-tags-valid", duplicateDoc.wellTagged, true),
   ("duplicate-case-names-value-fits", duplicateDoc.accepts sumValue, true),
   ("duplicate-case-names-print-validates", validDoc duplicateDoc (duplicateDoc.print sumValue), false),
   ("duplicate-case-names-read-restores-value", duplicateDoc.read (duplicateDoc.print sumValue) == some sumValue, false),
   ("ascending-row-schema", validDoc rowDoc (rowJson [1, 2]), true),
   ("ascending-row-carrier-reader", (Canonical.ofJsonAnyOrder (α := Effect4.Row Nat) (rowJson [1, 2])).isSome, true),
   ("descending-row-schema", validDoc rowDoc (rowJson [2, 1]), true),
   ("descending-row-shape-reader", (rowDoc.read (rowJson [2, 1])).isSome, true),
   ("descending-row-carrier-reader", (Canonical.ofJsonAnyOrder (α := Effect4.Row Nat) (rowJson [2, 1])).isSome, false),
   ("single-named-binding-schema", validDoc ⟨.named "A", [("A", .bool)]⟩ (.bool true), true),
   ("single-named-binding-reader", ((⟨.named "A", [("A", .bool)]⟩ : ShapeDoc).read (.bool true)).isSome, true),
   ("named-alias-schema", validDoc ⟨.named "A", [("A", .named "B"), ("B", .bool)]⟩ (.bool true), true),
   ("named-alias-reader", ((⟨.named "A", [("A", .named "B"), ("B", .bool)]⟩ : ShapeDoc).read (.bool true)).isSome, false)]

end McpSchemaControls

def main : IO Unit := do
  let rows := McpSchemaControls.checks.map fun (name, actual, expected) =>
    Effect4.Json.obj [("name", .str name), ("actual", .bool actual), ("expected", .bool expected),
      ("pass", .bool (actual == expected))]
  IO.println (ProbeMcp.render (.arr rows))
  unless McpSchemaControls.checks.all (fun (_, actual, expected) => actual == expected) do
    throw (IO.userError "MCP schema control failed")
