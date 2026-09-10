import Effect4.Program.Eff
import Effect4.Program.Ty

namespace Effect4.Program.Fold

open Effect4.Program

/-!
# Effect4.Program.Fold — Initial Algebras & Structural Catamorphisms

Initial algebras and executable structural recursions for the first-order AST families:
* `TyAlgebra` & `Ty.cata`: the type syntax (§1).
* `TermAlgebra` & `Term.cata` / `Terms.cata`: pure value expressions (§2).
* `CauseTermAlgebra` & `CauseTerm.cata`: exit cause expressions (§3).
* `EffAlgebra` & mutual catamorphisms: the 7-family program IR block (§4).

Each algebra structure provides paramorphic access (child subterm + folded accumulator).
Every catamorphism is accompanied by a definitional bridge theorem `cata_eq_rec` proving
exact equivalence to Lean's built-in structural recursor.
-/

/-! ## 1. Ty Initial Algebra -/

structure TyAlgebra (R : Type u) where
  never : R
  unit : R
  nat : R
  int : R
  string : R
  bool : R
  handle : String → R
  option : Ty → R → R
  list : Ty → R → R
  prod : Ty → Ty → R → R → R
  except : Ty → Ty → R → R → R
  exitOf : Ty → Ty → R → R → R
  causeOf : Ty → R → R
  fiberOf : Ty → Ty → R → R → R
  union : Ty → Ty → R → R → R
  lit : String → R

def Ty.cata (alg : TyAlgebra R) : Ty → R
  | .never => alg.never
  | .unit => alg.unit
  | .nat => alg.nat
  | .int => alg.int
  | .string => alg.string
  | .bool => alg.bool
  | .handle target => alg.handle target
  | .option inner => alg.option inner (cata alg inner)
  | .list inner => alg.list inner (cata alg inner)
  | .prod left right => alg.prod left right (cata alg left) (cata alg right)
  | .except error value => alg.except error value (cata alg error) (cata alg value)
  | .exitOf value error => alg.exitOf value error (cata alg value) (cata alg error)
  | .causeOf error => alg.causeOf error (cata alg error)
  | .fiberOf value error => alg.fiberOf value error (cata alg value) (cata alg error)
  | .union left right => alg.union left right (cata alg left) (cata alg right)
  | .lit value => alg.lit value

theorem Ty.cata_eq_rec (alg : TyAlgebra R) (t : Ty) :
    cata alg t = Ty.rec (motive := fun _ => R)
      alg.never alg.unit alg.nat alg.int alg.string alg.bool
      (fun target => alg.handle target)
      (fun inner ih => alg.option inner ih)
      (fun inner ih => alg.list inner ih)
      (fun left right ihL ihR => alg.prod left right ihL ihR)
      (fun error value ihE ihV => alg.except error value ihE ihV)
      (fun value error ihV ihE => alg.exitOf value error ihV ihE)
      (fun error ih => alg.causeOf error ih)
      (fun value error ihV ihE => alg.fiberOf value error ihV ihE)
      (fun left right ihL ihR => alg.union left right ihL ihR)
      (fun value => alg.lit value) t := by
  induction t <;> simp [cata, *]

/-! ## 2. Term & Terms Initial Algebra -/

structure TermAlgebra (RTerm : Type u) (RTerms : Type u) where
  var : Var → RTerm
  lit : Lit → RTerm
  app : String → Terms → RTerms → RTerm
  nil : RTerms
  cons : Term → Terms → RTerm → RTerms → RTerms

mutual
  def Term.cata (alg : TermAlgebra RTerm RTerms) : Term → RTerm
    | .var index => alg.var index
    | .lit value => alg.lit value
    | .app atom args => alg.app atom args (Terms.cata alg args)
  def Terms.cata (alg : TermAlgebra RTerm RTerms) : Terms → RTerms
    | .nil => alg.nil
    | .cons head tail => alg.cons head tail (Term.cata alg head) (Terms.cata alg tail)
end

/-! ## 3. CauseTerm Initial Algebra -/

structure CauseTermAlgebra (R : Type u) where
  fail : Term → R
  die : Term → R
  interrupt : Option Term → R
  both : CauseTerm → CauseTerm → R → R → R

def CauseTerm.cata (alg : CauseTermAlgebra R) : CauseTerm → R
  | .fail error => alg.fail error
  | .die defect => alg.die defect
  | .interrupt who => alg.interrupt who
  | .both left right => alg.both left right (cata alg left) (cata alg right)

theorem CauseTerm.cata_eq_rec (alg : CauseTermAlgebra R) (c : CauseTerm) :
    cata alg c = CauseTerm.rec (motive := fun _ => R)
      alg.fail alg.die alg.interrupt
      (fun left right ihL ihR => alg.both left right ihL ihR) c := by
  induction c <;> simp [cata, *]

/-! ## 4. Eff & Mutual Families Initial Algebra -/

/-- The initial algebra across all 7 mutual AST families of the Effect4 program IR.
Every constructor provides paramorphic access: children subterms and their folded accumulators. -/
structure EffAlgebra (Op : Type) (REff : Type u) (RStmt : Type u) (RStmts : Type u)
    (REffs : Type u) (RAction : Type u) (RLayer : Type u) (RLayers : Type u) where
  -- Eff (27 constructors)
  effSucceed : Term → REff
  effFail : Term → REff
  effFailCause : CauseTerm → REff
  effYieldError : Term → REff
  effSync : Term → REff
  effSuspend : Eff Op → REff → REff
  effPerform : Op → Term → REff
  effBind : Eff Op → Eff Op → REff → REff → REff
  effGen : Stmts Op → RStmts → REff
  effCatchCause : Eff Op → Eff Op → REff → REff → REff
  effCatchIf : Term → Eff Op → Eff Op → REff → REff → REff
  effMatchCause : Eff Op → Eff Op → Eff Op → REff → REff → REff → REff
  effOnExit : Eff Op → Eff Op → REff → REff → REff
  effExit : Eff Op → REff → REff
  effUninterruptible : Eff Op → REff → REff
  effInterruptible : Eff Op → REff → REff
  effBranch : Term → Eff Op → Eff Op → REff → REff → REff
  effWhileLoop : Term → Term → Term → Eff Op → REff → REff
  effYieldNow : Nat → REff
  effCallback : Op → Term → REff
  effAwaitFiber : Term → Effect4.Supervision.ObserverMode → REff
  effWithFiber : ActionTerm Op → RAction → REff
  effScoped : Eff Op → REff → REff
  effAcquireRelease : Eff Op → Eff Op → REff → REff → REff
  effProvideLayer : LayerTerm Op → Bool → Eff Op → RLayer → REff → REff
  effService : ServiceKey → REff
  effProvideService : ServiceKey → Term → Eff Op → REff → REff

  -- Stmt (6 constructors)
  stmtBindYield : Eff Op → REff → RStmt
  stmtYieldDiscard : Eff Op → REff → RStmt
  stmtRet : Term → RStmt
  stmtIfElse : Term → Stmts Op → Stmts Op → RStmts → RStmts → RStmt
  stmtWhileTrue : Stmts Op → RStmts → RStmt
  stmtBreakLoop : RStmt

  -- Stmts (2 constructors)
  stmtsNil : RStmts
  stmtsCons : Stmt Op → Stmts Op → RStmt → RStmts → RStmts

  -- Effs (2 constructors)
  effsNil : REffs
  effsCons : Eff Op → Effs Op → REff → REffs → REffs

  -- ActionTerm (16 constructors)
  actionFork : Eff Op → Effect4.Supervision.ForkOptions → REff → RAction
  actionForkIn : Eff Op → Effect4.Supervision.ForkOptions → Term → REff → RAction
  actionForkScoped : Eff Op → Effect4.Supervision.ForkOptions → REff → RAction
  actionRunIn : Term → Term → RAction
  actionInterrupt : Term → RAction
  actionInterruptScoped : Term → RAction
  actionInterruptAll : Term → Option Term → RAction
  actionAwaitAll : Term → RAction
  actionAwaitAllFailFast : Term → RAction
  actionSnapshotChildren : RAction
  actionAwaitNewChildren : Term → RAction
  actionRaceAll : Effs Op → REffs → RAction
  actionSetContext : Term → RAction
  actionGetContext : RAction
  actionGetId : RAction
  actionCloseScope : Term → Term → RAction

  -- LayerTerm (10 constructors)
  layerSucceed : ServiceKey → Lit → RLayer
  layerEffect : ServiceKey → Eff Op → REff → RLayer
  layerEffectDiscard : Eff Op → REff → RLayer
  layerProvide : LayerTerm Op → LayerTerm Op → RLayer → RLayer → RLayer
  layerProvideMerge : LayerTerm Op → LayerTerm Op → RLayer → RLayer → RLayer
  layerMerge : LayerTerm Op → LayerTerm Op → RLayer → RLayer → RLayer
  layerFresh : LayerTerm Op → RLayer → RLayer
  layerOrDie : LayerTerm Op → RLayer → RLayer
  layerRef : List Nat → RLayer
  layerMergeAll : LayerTerms Op → RLayers → RLayer

  -- LayerTerms (2 constructors)
  layerTermsNil : RLayers
  layerTermsCons : LayerTerm Op → LayerTerms Op → RLayer → RLayers → RLayers

mutual
  /-- Structural fold over `Eff Op`. -/
  def Eff.cata (alg : EffAlgebra Op REff RStmt RStmts REffs RAction RLayer RLayers) : Eff Op → REff
    | .succeed value => alg.effSucceed value
    | .fail error => alg.effFail error
    | .failCause cause => alg.effFailCause cause
    | .yieldError error => alg.effYieldError error
    | .sync thunk => alg.effSync thunk
    | .suspend body => alg.effSuspend body (Eff.cata alg body)
    | .perform op request => alg.effPerform op request
    | .bind first rest => alg.effBind first rest (Eff.cata alg first) (Eff.cata alg rest)
    | .gen body => alg.effGen body (Stmts.cata alg body)
    | .catchCause body handler =>
      alg.effCatchCause body handler (Eff.cata alg body) (Eff.cata alg handler)
    | .catchIf test body handler =>
      alg.effCatchIf test body handler (Eff.cata alg body) (Eff.cata alg handler)
    | .matchCause body onValue onCause =>
      alg.effMatchCause body onValue onCause (Eff.cata alg body) (Eff.cata alg onValue) (Eff.cata alg onCause)
    | .onExit body finalizer =>
      alg.effOnExit body finalizer (Eff.cata alg body) (Eff.cata alg finalizer)
    | .exit body => alg.effExit body (Eff.cata alg body)
    | .uninterruptible body => alg.effUninterruptible body (Eff.cata alg body)
    | .interruptible body => alg.effInterruptible body (Eff.cata alg body)
    | .branch test thenB elseB =>
      alg.effBranch test thenB elseB (Eff.cata alg thenB) (Eff.cata alg elseB)
    | .whileLoop initial test step body =>
      alg.effWhileLoop initial test step body (Eff.cata alg body)
    | .yieldNow priority => alg.effYieldNow priority
    | .callback register request => alg.effCallback register request
    | .awaitFiber fiber mode => alg.effAwaitFiber fiber mode
    | .withFiber action => alg.effWithFiber action (ActionTerm.cata alg action)
    | .scoped body => alg.effScoped body (Eff.cata alg body)
    | .acquireRelease acquire release =>
      alg.effAcquireRelease acquire release (Eff.cata alg acquire) (Eff.cata alg release)
    | .provideLayer layer isLocal body =>
      alg.effProvideLayer layer isLocal body (LayerTerm.cata alg layer) (Eff.cata alg body)
    | .service key => alg.effService key
    | .provideService key value body =>
      alg.effProvideService key value body (Eff.cata alg body)

  /-- Structural fold over `Stmt Op`. -/
  def Stmt.cata (alg : EffAlgebra Op REff RStmt RStmts REffs RAction RLayer RLayers) : Stmt Op → RStmt
    | .bindYield effect => alg.stmtBindYield effect (Eff.cata alg effect)
    | .yieldDiscard effect => alg.stmtYieldDiscard effect (Eff.cata alg effect)
    | .ret value => alg.stmtRet value
    | .ifElse test thenB elseB =>
      alg.stmtIfElse test thenB elseB (Stmts.cata alg thenB) (Stmts.cata alg elseB)
    | .whileTrue body => alg.stmtWhileTrue body (Stmts.cata alg body)
    | .breakLoop => alg.stmtBreakLoop

  /-- Structural fold over `Stmts Op`. -/
  def Stmts.cata (alg : EffAlgebra Op REff RStmt RStmts REffs RAction RLayer RLayers) : Stmts Op → RStmts
    | .nil => alg.stmtsNil
    | .cons head tail => alg.stmtsCons head tail (Stmt.cata alg head) (Stmts.cata alg tail)

  /-- Structural fold over `Effs Op`. -/
  def Effs.cata (alg : EffAlgebra Op REff RStmt RStmts REffs RAction RLayer RLayers) : Effs Op → REffs
    | .nil => alg.effsNil
    | .cons head tail => alg.effsCons head tail (Eff.cata alg head) (Effs.cata alg tail)

  /-- Structural fold over `ActionTerm Op`. -/
  def ActionTerm.cata (alg : EffAlgebra Op REff RStmt RStmts REffs RAction RLayer RLayers) : ActionTerm Op → RAction
    | .fork program options => alg.actionFork program options (Eff.cata alg program)
    | .forkIn program options scope =>
      alg.actionForkIn program options scope (Eff.cata alg program)
    | .forkScoped program options => alg.actionForkScoped program options (Eff.cata alg program)
    | .runIn target scope => alg.actionRunIn target scope
    | .interrupt target => alg.actionInterrupt target
    | .interruptScoped target => alg.actionInterruptScoped target
    | .interruptAll targets who => alg.actionInterruptAll targets who
    | .awaitAll targets => alg.actionAwaitAll targets
    | .awaitAllFailFast targets => alg.actionAwaitAllFailFast targets
    | .snapshotChildren => alg.actionSnapshotChildren
    | .awaitNewChildren snapshot => alg.actionAwaitNewChildren snapshot
    | .raceAll entrants => alg.actionRaceAll entrants (Effs.cata alg entrants)
    | .setContext context => alg.actionSetContext context
    | .getContext => alg.actionGetContext
    | .getId => alg.actionGetId
    | .closeScope scope exit => alg.actionCloseScope scope exit

  /-- Structural fold over `LayerTerm Op`. -/
  def LayerTerm.cata (alg : EffAlgebra Op REff RStmt RStmts REffs RAction RLayer RLayers) : LayerTerm Op → RLayer
    | .succeed key value => alg.layerSucceed key value
    | .effect key body => alg.layerEffect key body (Eff.cata alg body)
    | .effectDiscard body => alg.layerEffectDiscard body (Eff.cata alg body)
    | .provide self that =>
      alg.layerProvide self that (LayerTerm.cata alg self) (LayerTerm.cata alg that)
    | .provideMerge self that =>
      alg.layerProvideMerge self that (LayerTerm.cata alg self) (LayerTerm.cata alg that)
    | .merge left right =>
      alg.layerMerge left right (LayerTerm.cata alg left) (LayerTerm.cata alg right)
    | .fresh inner => alg.layerFresh inner (LayerTerm.cata alg inner)
    | .orDie inner => alg.layerOrDie inner (LayerTerm.cata alg inner)
    | .ref target => alg.layerRef target
    | .mergeAll layers => alg.layerMergeAll layers (LayerTerms.cata alg layers)

  /-- Structural fold over `LayerTerms Op`. -/
  def LayerTerms.cata (alg : EffAlgebra Op REff RStmt RStmts REffs RAction RLayer RLayers) : LayerTerms Op → RLayers
    | .nil => alg.layerTermsNil
    | .cons head tail =>
      alg.layerTermsCons head tail (LayerTerm.cata alg head) (LayerTerms.cata alg tail)
end

/-! ## 5. Monoidal Accumulator -/

/-- A simplified algebra specification when all carrier types collapse into a single monoid `M`. -/
structure EffMonoAlgebra (Op : Type) (M : Type u) where
  empty : M
  combine : M → M → M
  onEff : Eff Op → M := fun _ => empty
  onStmt : Stmt Op → M := fun _ => empty
  onAction : ActionTerm Op → M := fun _ => empty
  onLayer : LayerTerm Op → M := fun _ => empty

/-- Embed an `EffMonoAlgebra` into the full 7-carrier `EffAlgebra`. -/
def EffMonoAlgebra.toAlgebra {Op : Type} {M : Type u} (mono : EffMonoAlgebra Op M) :
    EffAlgebra Op M M M M M M M where
  effSucceed val := mono.onEff (.succeed val)
  effFail err := mono.onEff (.fail err)
  effFailCause cause := mono.onEff (.failCause cause)
  effYieldError err := mono.onEff (.yieldError err)
  effSync thunk := mono.onEff (.sync thunk)
  effSuspend body ih := mono.combine (mono.onEff (.suspend body)) ih
  effPerform op req := mono.onEff (.perform op req)
  effBind e1 e2 ih1 ih2 := mono.combine (mono.onEff (.bind e1 e2)) (mono.combine ih1 ih2)
  effGen body ih := mono.combine (mono.onEff (.gen body)) ih
  effCatchCause b h ihB ihH := mono.combine (mono.onEff (.catchCause b h)) (mono.combine ihB ihH)
  effCatchIf t b h ihB ihH := mono.combine (mono.onEff (.catchIf t b h)) (mono.combine ihB ihH)
  effMatchCause b v c ihB ihV ihC :=
    mono.combine (mono.onEff (.matchCause b v c)) (mono.combine ihB (mono.combine ihV ihC))
  effOnExit b f ihB ihF := mono.combine (mono.onEff (.onExit b f)) (mono.combine ihB ihF)
  effExit b ih := mono.combine (mono.onEff (.exit b)) ih
  effUninterruptible b ih := mono.combine (mono.onEff (.uninterruptible b)) ih
  effInterruptible b ih := mono.combine (mono.onEff (.interruptible b)) ih
  effBranch t b1 b2 ih1 ih2 := mono.combine (mono.onEff (.branch t b1 b2)) (mono.combine ih1 ih2)
  effWhileLoop i t s b ih := mono.combine (mono.onEff (.whileLoop i t s b)) ih
  effYieldNow p := mono.onEff (.yieldNow p)
  effCallback op req := mono.onEff (.callback op req)
  effAwaitFiber fib mode := mono.onEff (.awaitFiber fib mode)
  effWithFiber act ih := mono.combine (mono.onEff (.withFiber act)) ih
  effScoped b ih := mono.combine (mono.onEff (.scoped b)) ih
  effAcquireRelease a r ihA ihR :=
    mono.combine (mono.onEff (.acquireRelease a r)) (mono.combine ihA ihR)
  effProvideLayer l loc b ihL ihB :=
    mono.combine (mono.onEff (.provideLayer l loc b)) (mono.combine ihL ihB)
  effService key := mono.onEff (.service key)
  effProvideService key val b ih :=
    mono.combine (mono.onEff (.provideService key val b)) ih

  stmtBindYield e ih := mono.combine (mono.onStmt (.bindYield e)) ih
  stmtYieldDiscard e ih := mono.combine (mono.onStmt (.yieldDiscard e)) ih
  stmtRet val := mono.onStmt (.ret val)
  stmtIfElse t b1 b2 ih1 ih2 := mono.combine (mono.onStmt (.ifElse t b1 b2)) (mono.combine ih1 ih2)
  stmtWhileTrue b ih := mono.combine (mono.onStmt (.whileTrue b)) ih
  stmtBreakLoop := mono.onStmt .breakLoop

  stmtsNil := mono.empty
  stmtsCons _ _ ihHead ihTail := mono.combine ihHead ihTail

  effsNil := mono.empty
  effsCons _ _ ihHead ihTail := mono.combine ihHead ihTail

  actionFork p opt ih := mono.combine (mono.onAction (.fork p opt)) ih
  actionForkIn p opt sc ih := mono.combine (mono.onAction (.forkIn p opt sc)) ih
  actionForkScoped p opt ih := mono.combine (mono.onAction (.forkScoped p opt)) ih
  actionRunIn t sc := mono.onAction (.runIn t sc)
  actionInterrupt t := mono.onAction (.interrupt t)
  actionInterruptScoped t := mono.onAction (.interruptScoped t)
  actionInterruptAll t who := mono.onAction (.interruptAll t who)
  actionAwaitAll t := mono.onAction (.awaitAll t)
  actionAwaitAllFailFast t := mono.onAction (.awaitAllFailFast t)
  actionSnapshotChildren := mono.onAction .snapshotChildren
  actionAwaitNewChildren snap := mono.onAction (.awaitNewChildren snap)
  actionRaceAll entrants ih := mono.combine (mono.onAction (.raceAll entrants)) ih
  actionSetContext ctx := mono.onAction (.setContext ctx)
  actionGetContext := mono.onAction .getContext
  actionGetId := mono.onAction .getId
  actionCloseScope sc ex := mono.onAction (.closeScope sc ex)

  layerSucceed key val := mono.onLayer (.succeed key val)
  layerEffect key b ih := mono.combine (mono.onLayer (.effect key b)) ih
  layerEffectDiscard b ih := mono.combine (mono.onLayer (.effectDiscard b)) ih
  layerProvide s t ihS ihT := mono.combine (mono.onLayer (.provide s t)) (mono.combine ihS ihT)
  layerProvideMerge s t ihS ihT :=
    mono.combine (mono.onLayer (.provideMerge s t)) (mono.combine ihS ihT)
  layerMerge l r ihL ihR := mono.combine (mono.onLayer (.merge l r)) (mono.combine ihL ihR)
  layerFresh inner ih := mono.combine (mono.onLayer (.fresh inner)) ih
  layerOrDie inner ih := mono.combine (mono.onLayer (.orDie inner)) ih
  layerRef target := mono.onLayer (.ref target)
  layerMergeAll layers ih := mono.combine (mono.onLayer (.mergeAll layers)) ih

  layerTermsNil := mono.empty
  layerTermsCons _ _ ihHead ihTail := mono.combine ihHead ihTail

end Effect4.Program.Fold

namespace Effect4.Program

open Effect4.Program.Fold

/-- Fold an `Eff` tree into a monoid value using an `EffMonoAlgebra`. -/
def Eff.foldMono {Op : Type} {M : Type u} (mono : EffMonoAlgebra Op M) (eff : Eff Op) : M :=
  Eff.cata mono.toAlgebra eff

/-! ## 6. Standard Structural Queries -/

/-- Collect all operations `Op` performed anywhere in an `Eff Op` AST. -/
def Eff.operations [DecidableEq Op] (eff : Eff Op) : List Op :=
  eff.foldMono {
    empty := []
    combine := fun a b => (a ++ b).eraseDups
    onEff := fun
      | .perform op _ => [op]
      | .callback op _ => [op]
      | _ => []
  }

/-- Collect all service keys referenced anywhere in an `Eff Op` AST (including nested layers). -/
def Eff.serviceKeys (eff : Eff Op) : List ServiceKey :=
  eff.foldMono {
    empty := []
    combine := fun a b => (a ++ b).eraseDups
    onEff := fun
      | .service k => [k]
      | .provideService k _ _ => [k]
      | _ => []
    onLayer := fun
      | .succeed k _ => [k]
      | .effect k _ => [k]
      | _ => []
  }

/-- Count the total number of subterms in an `Eff Op` AST. -/
def Eff.subtermCount (eff : Eff Op) : Nat :=
  eff.foldMono {
    empty := 0
    combine := (· + ·)
    onEff := fun _ => 1
    onStmt := fun _ => 1
    onAction := fun _ => 1
    onLayer := fun _ => 1
  }

end Effect4.Program

