/-! ## Acceptance guards for the generated layer view

Appended verbatim by `--append tools/Effect4Gen/guards/layerview.lean` into
`src/Effect4/Program/LayerView.lean`.

1. One generic layer function, made an algebra by `EffAlgebra.ofLayer`, is run over a tree by the
   generated fold: a node count written once for every constructor of every family.
2. Every constructor name of every family has its argument sorts, and no family lists a name twice.
3. `build` refuses a name that is no constructor, and refuses arguments of the wrong sorts.
-/

namespace LayerViewAcceptance

open Effect4 Effect4.Program

/-- Count the nodes: one for this layer plus what the children counted. -/
def countLayer : (fam : EffFam) → String → List (ArgF Nat (fun _ => Nat)) → Nat :=
  fun _ _ args => 1 + (args.map fun
    | .child _ r => r
    | _ => 0).sum

def sample : Eff Nat :=
  .bind (.succeed (.lit (.nat 1)))
    (.catchIf (.lit (.bool true)) (.perform 3 (.var 0)) (.suspend (.succeed (.var 0))))

-- bind, succeed, catchIf, perform, suspend, succeed
#guard cata_eff (EffAlgebra.ofLayer countLayer) sample == 6

-- a spine counts its cells: raceAll over two entrants is withFiber, raceAll, cons, e, cons, e, nil
#guard cata_eff (EffAlgebra.ofLayer countLayer)
  (.withFiber (.raceAll (.cons (.succeed (.var 0)) (.cons (.succeed (.var 1)) .nil)))) == 7

def families : List EffFam := [.eff, .stmt, .stmts, .effs, .action, .layer, .layers]

#guard families.all fun f => (ctorNames f).all fun c => (argSorts f c).isSome
#guard families.all fun f => (ctorNames f).eraseDups.length == (ctorNames f).length
#guard (argSorts .eff "whileLoop").isNone

#guard (build (Op := Nat) .eff "whileLoop" []).isNone
#guard (build (Op := Nat) .eff "bind" [.term (.var 0)]).isNone
#guard build (Op := Nat) .eff "suspend" [.child .eff (.succeed (.var 0))]
  == some (Eff.suspend (.succeed (.var 0)))

end LayerViewAcceptance
