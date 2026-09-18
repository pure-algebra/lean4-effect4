import Effect4.Program.Typing.Rules

/-!
# Program.Typing.Terms — the type of a term in argument position, as a fold

`termTy`/`termsTy` (`Typing.lean`) are not a fold as written: `termsTy` splits on the head's
constructor to apply the literal rule (`litArgTy const value`) and recurses on the *rebuilt*
head otherwise. `Typing.lean`'s `argTy` names the head rule; here it is the fold itself — a
term's type under the enclosing atom's const-generic flag, the flag an accumulator
(`sig.constAtom atom` for an application's arguments). `termTy` is `argTy` at `false`
(`litArgTy_false`) and `termsTy` is `argsTy`, rule for rule: `Typing/Agreement.lean` says so.
The second file beside `Typing.lean`'s term block; `fold_of` reads its algebra
(`Program/Folds/TermTy.lean`).
-/

namespace Effect4.Program.Checker

variable {Op : Type}

mutual
  /-- The type of a term in argument position: a variable from the environment, the literal
  rule under the flag, an application by its atom at its arguments' types under the atom's
  own flag. -/
  def argTy (sig : Signature Op) (env : TyEnv) (const : Bool) : Term → Option Ty
    | .var index => env[index]?
    | .lit value => some (litArgTy const value)
    | .app atom args => do
      let tys ← argsTy sig env (sig.constAtom atom) args
      sig.atomOf atom tys
  /-- The argument types of an application, argument by argument. -/
  def argsTy (sig : Signature Op) (env : TyEnv) (const : Bool) : Terms → Option (List Ty)
    | .nil => some []
    | .cons head tail => do
      let t ← argTy sig env const head
      let rest ← argsTy sig env const tail
      some (t :: rest)
end

end Effect4.Program.Checker
