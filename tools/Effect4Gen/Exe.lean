import Effect4Gen.Dispatch
import Effect4Gen.Fold
import Effect4Gen.Main
import Effect4Gen.Authoring
import Effect4Gen.View
import Effect4Gen.LayerView
import Effect4Gen.Atoms
import Effect4Gen.Fragments

/-! The early generator builds before Effect4's generated folds.
Its tools inspect declarations loaded by each run's `--imports` argument.
Catalogue tools live in `Effect4Gen.CatalogueExe`. -/

namespace Effect4Gen.Exe

def generators : Effect4Gen.Dispatch.Generators :=
  [("Fold", Effect4Gen.Fold.cli), ("Main", Effect4Gen.Main.cli),
   ("Authoring", Effect4Gen.Authoring.cli), ("View", Effect4Gen.View.cli),
   ("LayerView", Effect4Gen.LayerView.cli), ("Atoms", Effect4Gen.Atoms.cli),
   ("Fragments", Effect4Gen.Fragments.cli)]

end Effect4Gen.Exe

def main := Effect4Gen.Dispatch.main Effect4Gen.Exe.generators
