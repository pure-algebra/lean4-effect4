import Effect4.Laws.Codegen.PrintReadable
import Effect4.Program.Native

/-! Structural target controls for row 195's record decision.
Raw reconstruction keeps its existing readability domain without a typing premise.
Source parsing and target execution are checked separately by finite TypeScript controls. -/

namespace Effect4.Test.RecordTagCodegen
open Effect4.Program Effect4.Codegen

-- Even an untyped raw scrutinee retains the exact stored decision and branch binders.
def raw : NativeEff := .select (.lit (.nat 7)) (.recordTag "Found")
  (.succeed (.var 0)) (.succeed (.var 0))

def pair : NativeEff := .select (.lit (.nat 7)) (.tag "Found")
  (.succeed (.var 0)) (.succeed (.var 0))

#guard roundTrip (nativeSignature []) (fun _ _ => none) 0 raw = .ok raw
#guard roundTrip (nativeSignature []) (fun _ _ => none) 0 pair = .ok pair
#guard match print (nativeSignature []) 0 raw with
  | .ok (.call (.ident "caseTagR") _) => true
  | _ => false
#guard match print (nativeSignature []) 0 pair with
  | .ok (.call (.ident "caseTag") _) => true
  | _ => false
#guard !exportNameSafe "caseTagR"

end Effect4.Test.RecordTagCodegen

#print axioms Effect4.Program.readLeaf_exact
#print axioms Effect4.Program.readLeaf_print
#print axioms Effect4.Program.read_print
#print axioms Effect4.Program.read_exact
#print axioms Effect4.Program.print_of_readable
