import Effect4.Program.Typing.Agreement
import Effect4.Laws.Program.Folds.Checker

/-! The checker projections as folds; moved without changing declarations or proofs. -/

namespace Effect4.Program

namespace Checker

/-! ## The checker's projections as the fold -/

/-- `effTy` is the success of the fold of `check.alg` at the root. -/
theorem _root_.Effect4.Program.effTy.eq_cata (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    Program.effTy sig env e = (cata_eff (check.alg sig) e env []).toOption :=
  congrArg Except.toOption (check.eq_cata sig env [] e)

theorem _root_.Effect4.Program.layerTy.eq_cata (sig : Signature Op) (l : LayerTerm Op) :
    Program.layerTy sig l = (cata_layer (check.alg sig) l []).toOption :=
  congrArg Except.toOption (checkLayer.eq_cata sig [] l)

theorem _root_.Effect4.Program.layersTy.eq_cata (sig : Signature Op) (ls : LayerTerms Op) :
    Program.layersTy sig ls = (cata_layers (check.alg sig) ls []).toOption.bind LayerTy.mergeNonempty :=
  congrArg (fun x : Except TypeRefusal (List LayerTy) => x.toOption.bind LayerTy.mergeNonempty)
    (checkLayers.eq_cata sig [] ls)

theorem _root_.Effect4.Program.stmtsTy.eq_cata (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (b : Stmts Op) :
    Program.stmtsTy sig env inLoop b = (cata_stmts (check.alg sig) b env inLoop none []).toOption :=
  congrArg Except.toOption (checkStmts.eq_cata sig env inLoop none [] b)

theorem _root_.Effect4.Program.effsTy.eq_cata (sig : Signature Op) (env : TyEnv) (es : Effs Op) :
    Program.effsTy sig env es = (cata_effs (check.alg sig) es env []).toOption :=
  congrArg Except.toOption (checkEffs.eq_cata sig env [] es)

theorem _root_.Effect4.Program.actionTy.eq_cata (sig : Signature Op) (env : TyEnv)
    (a : ActionTerm Op) :
    Program.actionTy sig env a = (cata_action (check.alg sig) a env []).toOption :=
  congrArg Except.toOption (checkAction.eq_cata sig env [] a)

end Checker

end Effect4.Program
