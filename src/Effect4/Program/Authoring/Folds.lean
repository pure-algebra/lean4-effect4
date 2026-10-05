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

end Effect4.Program.Authoring
