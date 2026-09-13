/-! ## Acceptance guards for the generated Program Fold

Appended verbatim by `--append tools/Effect4Gen/guards/fold.lean` into
`src/Effect4/Program/Fold.lean`.

These guards exercise:
1. `EffMonoAlgebra` and `foldMono` as embedding into the 7-family program IR fold.
2. Standard structural queries: `operations`, `serviceKeys`, and `subtermCount`.
3. Execution on sample ASTs.
4. Definitional equality between `Eff.weaken` and `cata_frontier_eff (weakenAlg ...)`.
5. `foldM_eff` in `StateM Nat`: the node count it accumulates in the state equals
   the `subtermCount` the pure `foldMap_eff` computes.
6. `foldM_eff` in `Except String`: a slot that refuses one named operation makes the
   whole fold an `.error`, and leaves a program without that operation an `.ok`.
7. `foldM_eff` in `ReaderT (List Nat) Id`: the environment reaches every slot, so an
   environment-indexed traversal is expressible.
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

/-! ### The monadic fold

`EffTraversal` is the Kleisli counterpart of `EffMonoAlgebra` above: a constant carrier
`A`, a way to combine the children's values, and one action per family run at each node.
A `foldM` slot receives its children already folded and cannot see the node, so the two
hooks the guards below discriminate on -- `succeed` and `perform` -- are named fields
rather than a match on the node. `EffTraversal.alg` is the whole 65-slot algebra; the
three guards differ only in the monad and in which hooks they set. -/

structure EffTraversal (Op : Type) (M : Type → Type) (A : Type) [Monad M] where
  empty : A
  combine : A → A → A
  /-- Run at every node of a named family (`Eff`, `Stmt`, `ActionTerm`, `LayerTerm`). -/
  atNode : M A := pure empty
  atEff : M A := atNode
  atStmt : M A := atNode
  atAction : M A := atNode
  atLayer : M A := atNode
  /-- Run at the three list families (`Stmts`, `Effs`, `LayerTerms`), which `subtermCount`
  does not count either. -/
  atList : M A := pure empty
  atSucceed : Term → M A := fun _ => atEff
  atPerform : Op → Term → M A := fun _ _ => atEff

/-- The node action runs first, then the children's values fold into its result. -/
def EffTraversal.acc {Op : Type} {M : Type → Type} {A : Type} [Monad M]
    (s : EffTraversal Op M A) (c : M A) (xs : List A) : M A := do
  let v ← c
  pure (xs.foldl s.combine v)

def EffTraversal.alg {Op : Type} {M : Type → Type} {A : Type} [Monad M]
    (s : EffTraversal Op M A) : EffMAlgebra Op M (fun _ => A) where
  eff_succeed a0 := s.acc (s.atSucceed a0) []
  eff_fail _ := s.acc s.atEff []
  eff_failCause _ := s.acc s.atEff []
  eff_yieldError _ := s.acc s.atEff []
  eff_sync _ := s.acc s.atEff []
  eff_suspend x0 := s.acc s.atEff [x0]
  eff_perform a0 a1 := s.acc (s.atPerform a0 a1) []
  eff_bind x0 x1 := s.acc s.atEff [x0, x1]
  eff_gen x0 := s.acc s.atEff [x0]
  eff_catchCause x0 x1 := s.acc s.atEff [x0, x1]
  eff_matchCause x0 x1 x2 := s.acc s.atEff [x0, x1, x2]
  eff_onExit x0 x1 := s.acc s.atEff [x0, x1]
  eff_exit x0 := s.acc s.atEff [x0]
  eff_uninterruptible x0 := s.acc s.atEff [x0]
  eff_interruptible x0 := s.acc s.atEff [x0]
  eff_branch _ x1 x2 := s.acc s.atEff [x1, x2]
  eff_whileLoop _ _ _ x3 := s.acc s.atEff [x3]
  eff_yieldNow _ := s.acc s.atEff []
  eff_callback _ _ := s.acc s.atEff []
  eff_awaitFiber _ _ := s.acc s.atEff []
  eff_withFiber x0 := s.acc s.atEff [x0]
  eff_scoped x0 := s.acc s.atEff [x0]
  eff_acquireRelease x0 x1 := s.acc s.atEff [x0, x1]
  eff_provideLayer x0 _ x2 := s.acc s.atEff [x0, x2]
  eff_service _ := s.acc s.atEff []
  eff_provideService _ _ x2 := s.acc s.atEff [x2]
  eff_catchIf _ x1 x2 := s.acc s.atEff [x1, x2]
  stmt_bindYield x0 := s.acc s.atStmt [x0]
  stmt_yieldDiscard x0 := s.acc s.atStmt [x0]
  stmt_ret _ := s.acc s.atStmt []
  stmt_ifElse _ x1 x2 := s.acc s.atStmt [x1, x2]
  stmt_whileTrue x0 := s.acc s.atStmt [x0]
  stmt_breakLoop := s.acc s.atStmt []
  stmts_nil := s.acc s.atList []
  stmts_cons x0 x1 := s.acc s.atList [x0, x1]
  effs_nil := s.acc s.atList []
  effs_cons x0 x1 := s.acc s.atList [x0, x1]
  action_fork x0 _ := s.acc s.atAction [x0]
  action_forkIn x0 _ _ := s.acc s.atAction [x0]
  action_forkScoped x0 _ := s.acc s.atAction [x0]
  action_runIn _ _ := s.acc s.atAction []
  action_interrupt _ := s.acc s.atAction []
  action_interruptScoped _ := s.acc s.atAction []
  action_interruptAll _ _ := s.acc s.atAction []
  action_awaitAll _ := s.acc s.atAction []
  action_awaitAllFailFast _ := s.acc s.atAction []
  action_snapshotChildren := s.acc s.atAction []
  action_awaitNewChildren _ := s.acc s.atAction []
  action_raceAll x0 := s.acc s.atAction [x0]
  action_setContext _ := s.acc s.atAction []
  action_getContext := s.acc s.atAction []
  action_getId := s.acc s.atAction []
  action_closeScope _ _ := s.acc s.atAction []
  layer_succeed _ _ := s.acc s.atLayer []
  layer_effect _ x1 := s.acc s.atLayer [x1]
  layer_effectDiscard x0 := s.acc s.atLayer [x0]
  layer_provide x0 x1 := s.acc s.atLayer [x0, x1]
  layer_provideMerge x0 x1 := s.acc s.atLayer [x0, x1]
  layer_merge x0 x1 := s.acc s.atLayer [x0, x1]
  layer_fresh x0 := s.acc s.atLayer [x0]
  layer_orDie x0 := s.acc s.atLayer [x0]
  layer_ref _ := s.acc s.atLayer []
  layer_mergeAll x0 := s.acc s.atLayer [x0]
  layers_nil := s.acc s.atList []
  layers_cons x0 x1 := s.acc s.atList [x0, x1]

/-- A program that reaches all seven families: `Stmts`, `Effs` and `LayerTerms` nodes are
the ones `subtermCount` does not count, so a fold that counted them would part company
with it here and not on `sampleProgram`. -/
def listProgram : Eff Nat :=
  .provideLayer
    (.mergeAll (.cons (.effect sampleKey (.succeed (.var 0))) .nil)) false
    (.bind (.gen (.cons (.bindYield (.perform 3 (.var 0))) (.cons (.ret (.var 1)) .nil)))
      (.withFiber (.raceAll (.cons (.succeed (.var 0)) (.cons (.succeed (.var 1)) .nil)))))

/-- (5) `StateM Nat`: one increment per named-family node, the count read off the state. -/
def countTraversal : EffTraversal Nat (StateM Nat) Unit where
  empty := ()
  combine _ _ := ()
  atNode := modify (· + 1)

def countNodes (eff : Eff Nat) : Nat :=
  ((foldM_eff countTraversal.alg eff).run 0).2

#guard countNodes sampleProgram == subtermCount sampleProgram
    && countNodes listProgram == subtermCount listProgram

/-- (6) `Except String`: the `perform` slot refuses operation `1`. -/
def refuseOne : EffTraversal Nat (Except String) Unit where
  empty := ()
  combine _ _ := ()
  atPerform op _ := if op == 1 then .error "perform of op 1 is refused" else pure ()

/-- The same shape as `sampleProgram`, performing an operation `refuseOne` admits. -/
def otherProgram : Eff Nat :=
  .provideLayer (.effect sampleKey (.succeed (.var 0))) false
    (.bind (.perform 2 (.var 0)) (.succeed (.var 1)))

#guard (foldM_eff refuseOne.alg sampleProgram).toOption.isNone
    && (foldM_eff refuseOne.alg otherProgram).toOption.isSome

/-- (7) `ReaderT (List Nat) Id`: each `succeed` slot records the environment's depth. -/
def depthTraversal : EffTraversal Nat (ReaderT (List Nat) Id) (List Nat) where
  empty := []
  combine := (· ++ ·)
  atSucceed _ := do return [(← read).length]

def depthEnv : List Nat := [7, 8, 9]

-- `sampleProgram` has two `Eff.succeed` nodes, so two readings of the same environment.
#guard Id.run ((foldM_eff depthTraversal.alg sampleProgram).run depthEnv)
    == [depthEnv.length, depthEnv.length]

end FoldAcceptance
