import Lean

/-!
The population of authored declarations: the constants an author wrote, as against the
auxiliaries that the elaborator and the compiler generate. The auxiliaries are equation lemmas,
matchers, recursors, `noConfusion`, injectivity and `sizeOf` lemmas, functional induction
principles and nested-proof auxiliaries. The semantics report, the semantics census and the
architecture map count one population through `isAuxiliary`.

Lean's own predicates decide wherever one exists: `Name.isInternalDetail`, `isReservedName` (the
names Lean realizes on demand, such as `eq_def`, `eq_1`, `induct` and `fun_cases`),
`isAuxRecursor`, `isNoConfusion`, `isRecCore` and `Meta.isMatcherCore`. The companions that Lean
names by spelling alone are matched in the last name component only, and only when the prefix is
the constructor or inductive they are generated from. The string filters this replaces matched
`eq_`, `proof_` and `match_` in any component, so they dropped authored theorems such as
`eq_cata` (`docs/research/2026-10-04-reference-scout/proof-graph.md`, recommendation 1).
-/
namespace ProofGraph
open Lean

/-- A companion Lean names by spelling: `inj`, `injEq` and `sizeOf_spec` of a constructor;
`noConfusionType`, `ctorIdx`, `ctorElim`, `below`, `ibelow`, `brecOn` and `binductionOn` of an
inductive (an inductive predicate's `brecOn` carries no auxiliary-recursor tag); a derived
`instSizeOf…` instance. -/
def isGeneratedCompanion (env : Environment) : Name → Bool
  | .str p s =>
    s.startsWith "instSizeOf" ||
      match env.find? p with
      | some (.ctorInfo _) => s == "inj" || s == "injEq" || s == "sizeOf_spec"
      | some (.inductInfo info) =>
        s == "noConfusionType" || s == "ctorIdx" ||
          (s == "ctorElim" && info.numCtors > 1) ||
          ((s == "below" || s == "brecOn") && info.isRec) ||
          s == "ibelow" || s == "binductionOn"
      | _ => false
  | _ => false

/-- Whether `n` itself, not counting its prefixes, is a generated auxiliary. -/
def isAuxiliaryHere (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || n.hasMacroScopes || isReservedName env n || isAuxRecursor env n ||
    isNoConfusion env n || isRecCore env n || Meta.isMatcherCore env n ||
    isGeneratedCompanion env n

/-- Whether `n` is an auxiliary the elaborator or the compiler generated, rather than a
declaration an author wrote. A constant under an auxiliary is one too: a matcher's `congr_eq_1`,
a `brecOn`'s `go` and `eq`. -/
def isAuxiliary (env : Environment) : Name → Bool
  | .anonymous => false
  | n@(.str p _) => isAuxiliaryHere env n || isAuxiliary env p
  | .num _ _ => true

end ProofGraph
