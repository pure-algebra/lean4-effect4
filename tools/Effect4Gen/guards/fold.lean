/-! ## Acceptance guards for the generated Program Fold

Appended verbatim by `--append tools/Effect4Gen/guards/fold.lean` into
`src/Effect4/Program/Fold.lean`.

These guards exercise:
1. `EffMonoAlgebra` and `foldMono` as embedding into the 7-family program IR fold.
2. Standard structural queries: `operations`, `serviceKeys`, and `subtermCount`.
3. Execution on sample ASTs.
4. Definitional equality between `Eff.weaken` and `cata_frontier_eff (weakenAlg ...)`.
-/

namespace FoldAcceptance

open Effect4 Effect4.Program

universe u

structure EffMonoAlgebra (Op : Type) (M : Type u) where
  empty : M
  combine : M → M → M
  onEff : Eff Op → M := fun _ => empty
  onStmt : Stmt Op → M := fun _ => empty
  onAction : ActionTerm Op → M := fun _ => empty
  onLayer : LayerTerm Op → M := fun _ => empty

def foldMono {Op : Type} {M : Type u} (mono : EffMonoAlgebra Op M) (eff : Eff Op) : M :=
  foldMap_eff mono.empty mono.combine eff mono.onEff mono.onStmt (fun _ => mono.empty)
    (fun _ => mono.empty) mono.onAction mono.onLayer (fun _ => mono.empty)

def operations {Op : Type} [DecidableEq Op] (eff : Eff Op) : List Op :=
  foldMap_eff [] (fun a b => (a ++ b).eraseDups) eff (f_eff := fun
    | .perform op _ => [op]
    | .callback op _ => [op]
    | _ => [])

def serviceKeys {Op : Type} (eff : Eff Op) : List ServiceKey :=
  foldMap_eff [] (fun a b => (a ++ b).eraseDups) eff
    (f_eff := fun
      | .service k => [k]
      | .provideService k _ _ => [k]
      | _ => [])
    (f_layer := fun
      | .succeed k _ => [k]
      | .effect k _ => [k]
      | _ => [])

def subtermCount {Op : Type} (eff : Eff Op) : Nat :=
  foldMap_eff 0 (· + ·) eff (f_eff := fun _ => 1) (f_stmt := fun _ => 1)
    (f_action := fun _ => 1) (f_layer := fun _ => 1)

def sampleKey : ServiceKey := ⟨⟨0⟩, ⟨0⟩⟩

def sampleProgram : Eff Nat :=
  .provideLayer (.effect sampleKey (.succeed (.var 0))) false
    (.bind (.perform 1 (.var 0)) (.succeed (.var 1)))

#guard operations sampleProgram == [1]
#guard serviceKeys sampleProgram == [sampleKey]
#guard subtermCount sampleProgram > 0

def pWeaken : Eff Nat :=
  .provideLayer (.effect sampleKey (.succeed (.var 0))) false (.succeed (.var 0))

#guard Eff.weaken 0 pWeaken ==
  (.provideLayer (.effect sampleKey (.succeed (.var 0))) false (.succeed (.var 1)) : Eff Nat)
#guard (Eff.weaken 0 pWeaken == cata_frontier_eff (weakenAlg 0) pWeaken)

end FoldAcceptance
