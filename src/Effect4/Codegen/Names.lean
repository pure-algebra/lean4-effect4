import TypeScript.Identifier

/-!
# Legal target names, once

The names the surface mints or accepts are decided here and nowhere else. The lexical
check of the original source and the Effect v4 profile used to carry this predicate
separately, so a repair to one left the other accepting what it rejected (review log,
B21). Nothing here claims a host exports the name or that the name has a type; it is
the spelling rule alone.
-/

namespace Effect4.Codegen.Names

/-- Ambient value names a generated or admitted binding must not shadow. -/
def reservedExtra : List String := ["arguments", "eval", "undefined", "NaN", "Infinity"]

/-- A legal binding name: a target identifier that is no reserved word and no ambient value. -/
def binderName (name : String) : Bool :=
  TypeScript.targetIdentifier name && !reservedExtra.contains name

end Effect4.Codegen.Names
