import Effect4.Schema.Bridge
import Effect4.Schema.Authoring

/-! Verifier of seat PROGRAMS (2026-10-01): stage (c), names carried as annotations (PROG-D16;
note §3.1, whose requirement `ofSchema (schemaWith names t) = some t` "holds by `ofSchema_schema`'s
reading of annotations today"). `ofSchema` ignores a node's annotations but refuses an annotated
tuple element (`Schema/Bridge.lean:73-78`, the pattern `⟨false, a, none⟩` at :127). So where the
names go decides whether the requirement holds: on the tuple node, yes; on its elements, the
natural place for a field name, no. Scratch, not in the tree. -/

set_option autoImplicit false

namespace Verify.StageC
open Effect4 Effect4.Program

def named (n : String) : Annotations := some [{ key := "title", payload := .str n }]

-- green: today's pair reads back
#guard Schema.Bridge.ofSchema (Schema.tuple [Schema.element (Schema.Bridge.schema .nat),
  Schema.element (Schema.Bridge.schema .string)]) = some (.prod .nat .string)
-- names on the tuple node: ignored, reads back
#guard Schema.Bridge.ofSchema (.arrays (named "User") [] [Schema.element (Schema.Bridge.schema .nat),
  Schema.element (Schema.Bridge.schema .string)] []) = some (.prod .nat .string)
-- RED: names on the elements: refused
#guard Schema.Bridge.ofSchema (Schema.tuple [Schema.element (Schema.Bridge.schema .nat) false (named "id"),
  Schema.element (Schema.Bridge.schema .string) false (named "name")]) = none

end Verify.StageC
