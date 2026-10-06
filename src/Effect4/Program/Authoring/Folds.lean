module

public import Effect4.Program.Authoring

/-! A list fold in the existing scope reader, for decisions row 228.
The list and the initial value resolve at the term's own scope.
The body resolves under the accumulator's name and then the element's name.
The builder states no typing: the checker types the fold. -/

@[expose] public section

namespace Effect4.Program.Authoring

/-- `fold acc item accTy list init body`: the body sees the accumulator as `acc` and the element
as `item`, and the nearest binder of a name wins, as at every other binder. `accTy` states the
accumulator's type where it is wider than the initial value's: an accumulator that starts as
the empty list (DI-91). -/
def fold (acc item : String) (accTy : Option Ty) (list init body : TermSrc) : TermSrc :=
  fun env path => do
    let listTerm ← list env path
    let initTerm ← init env path
    let bodyTerm ← body (env.push [acc, item]) path
    .ok (.fold accTy listTerm initTerm bodyTerm)

/-- `foldWith list init body`: `fold` with its two binders as Lean functions over names minted
for this scope, read through `minted`. No name an author writes is a minted name, so a term of
the caller keeps its reading inside the body (`var_push_minted_pair`,
`Laws/Program/Authoring/Folds.lean`). A builder that places a caller's term in a fold's body
uses this form: with `fold`'s fixed names the caller's variable of the same name would read the
folded element. It emits the same `Term.fold`. `accTy` is `fold`'s. -/
def foldWith (list init : TermSrc) (body : TermSrc → TermSrc → TermSrc)
    (accTy : Option Ty := none) : TermSrc :=
  fun env path =>
    fold (env.mint "acc") (env.mint "item") accTy list init
      (body (minted (env.mint "acc")) (minted (env.mint "item"))) env path

end Effect4.Program.Authoring
