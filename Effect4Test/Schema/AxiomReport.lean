import Effect4.Schema.Representation

/-!
Fresh kernel dependency report for all six Schema representation alphabets.
-/

#print axioms Effect4.RepresentationTag.census_length
#print axioms Effect4.RepresentationTag.census_nodup
#print axioms Effect4.RepresentationTag.mem_census
#print axioms Effect4.RepresentationTag.ofTagName_tagName
#print axioms Effect4.RepresentationTag.tagName_injective
#print axioms Effect4.RepresentationTag.tagName_ofTagName

#print axioms Effect4.UnionMode.census_length
#print axioms Effect4.UnionMode.census_nodup
#print axioms Effect4.UnionMode.mem_census
#print axioms Effect4.UnionMode.ofModeName_modeName
#print axioms Effect4.UnionMode.modeName_injective
#print axioms Effect4.UnionMode.modeName_ofModeName

#print axioms Effect4.CheckTag.census_length
#print axioms Effect4.CheckTag.census_nodup
#print axioms Effect4.CheckTag.mem_census
#print axioms Effect4.CheckTag.ofTagName_tagName
#print axioms Effect4.CheckTag.tagName_injective
#print axioms Effect4.CheckTag.tagName_ofTagName

#print axioms Effect4.LiteralKind.census_length
#print axioms Effect4.LiteralKind.census_nodup
#print axioms Effect4.LiteralKind.mem_census

#print axioms Effect4.EnumValueKind.census_length
#print axioms Effect4.EnumValueKind.census_nodup
#print axioms Effect4.EnumValueKind.mem_census
#print axioms Effect4.EnumValueKind.toLiteralKind_injective
#print axioms Effect4.EnumValueKind.toLiteralKind_ne_bigint
#print axioms Effect4.EnumValueKind.toLiteralKind_ne_boolean

#print axioms Effect4.PropertyKeyKind.census_length
#print axioms Effect4.PropertyKeyKind.census_nodup
#print axioms Effect4.PropertyKeyKind.mem_census
