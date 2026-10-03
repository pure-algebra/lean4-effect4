import Effect4Gen.Dispatch
import Effect4Gen.Rows
import Effect4Gen.Forms
import Effect4Gen.PreludeAtoms

/-! Catalogue generators inspect compiled Effect4 values.
Build this executable only after regenerating the files its imports consume. -/

namespace Effect4Gen.CatalogueExe

def generators : Effect4Gen.Dispatch.Generators :=
  [("Rows", Effect4Gen.Rows.cli), ("Forms", Effect4Gen.Forms.cli),
   ("PreludeAtoms", Effect4Gen.PreludeAtoms.cli)]

end Effect4Gen.CatalogueExe

def main := Effect4Gen.Dispatch.main Effect4Gen.CatalogueExe.generators
