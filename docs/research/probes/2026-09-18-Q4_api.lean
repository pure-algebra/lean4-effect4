import Lean
import Batteries.Util.ProofWanted
open Lean Meta Elab Command
#check @Lean.Meta.matchMatcherApp?
#check @Lean.Meta.MatcherApp
#check @Lean.Meta.transform
#check @Lean.Meta.forEachExpr
#check @Lean.Elab.Command.elabCommand
#check @Lean.Elab.Command.runTermElabM
#check @Lean.Expr.instantiateForall
#check @Lean.Meta.forallMetaTelescope
#check @Lean.Meta.forallTelescopeReducing
#check @Lean.Meta.isDefEq
#check @Lean.Meta.mkAppM
#check @Lean.Meta.getMatcherInfo?
#check @Lean.Meta.Match.MatcherInfo
#check @Lean.Elab.Deriving.mkHeader
#check @Lean.registerSimplePersistentEnvExtension
#check @Lean.Elab.Term.elabTermEnsuringType
#check @Lean.Meta.getProjectionFnInfo?
#check @Lean.getStructureFieldsFlattened
#check @Lean.Meta.mkProjection
#check @Lean.Elab.Command.elabCommandTopLevel
#check @Lean.Meta.getStructureInfo?
theorem_wanted probe_wanted (n : Nat) : n + 0 = n
#print axioms probe_wanted
