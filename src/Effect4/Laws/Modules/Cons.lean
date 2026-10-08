import Effect4.Laws.Modules.Checking

/-!
# The shared typing rule of list construction

Placement: `store-typing`, helper of `step-language-typed`, requirement R4.
The matcher and atom helpers serve `types_cons`; Step's cons case consumes that rule.
Reach: every scope and native atom signature, at an element type in normal form.
These rules establish neither membership, a run, nor target execution.
-/
set_option autoImplicit false

namespace Effect4.Modules
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- The cons matcher binds its one variable to the common normal element type.
A helper of `step-language-typed`, consumed by `nativeAtomTy_cons`. -/
theorem matchArgsB_cons (X : Ty) (normal : X.normalize = X) :
    Bounds.matchArgsB [.var 0, .list (.var 0)] [X, .list X] =
      some [(0, Ty.join X X), (0, Ty.join X X)] := by
  open Bounds Ty in
  dsimp only [matchArgsB]
  rw [candsList_cons, cands_var, candsList_cons, cands, cands_var, candsList_nil,
    List.append_nil, List.cons_append, List.nil_append]
  have solved : solve [] [(0, .co, X), (0, .co, X)] =
      [(0, Ty.join X X), (0, Ty.join X X)] := rfl
  rw [solved, if_pos (show [Ty.var 0, Ty.list (.var 0)].length = [X, Ty.list X].length from rfl)]
  have joined : Ty.join X X = X := by rw [Ty.join_self, normal]
  have item : Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.var 0) = X := by
    dsimp only [Ty.instantiate, List.lookup]
    rw [joined]
    rfl
  have list : Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.list (.var 0)) = .list X := by
    dsimp only [Ty.instantiate, List.lookup]
    rw [joined]
    rfl
  have fits : (([Ty.var 0, Ty.list (.var 0)].zip [X, Ty.list X]).all fun pr =>
      Ty.sub pr.2.normalize (Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] pr.1).normalize) = true := by
    change (Ty.sub X.normalize (Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.var 0)).normalize &&
      (Ty.sub (.list X : Ty).normalize (Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.list (.var 0))).normalize && true)) = true
    rw [item, list, Ty.sub_refl, Ty.sub_refl]
    rfl
  rw [fits]
  rfl

/-- The native cons atom answers the common normal element type.
A helper of `step-language-typed`, consumed by `types_cons`. -/
theorem nativeAtomTy_cons (T : Ty) (normal : T.normalize = T) :
    nativeAtomTy "cons" [T, .list T] = some (.list T) := by
  change (Bounds.matchArgsB [.var 0, .list (.var 0)] [T, .list T]).map
    (fun σ => Ty.instantiate σ (.list (.var 0))) = some (.list T)
  rw [matchArgsB_cons T normal]
  dsimp only [Option.map, Ty.instantiate, List.lookup, BEq.beq, Nat.beq]
  have joined : Ty.join T T = T := by rw [Ty.join_self, normal]
  rw [joined]
  rfl

/-- A cons at the common normal element type, under either literal flag.
A helper of `step-language-typed`, consumed by Step's cons typing case. -/
theorem types_cons {Op : Type} {sig : Signature Op} (atoms : sig.atomOf = nativeAtomTy)
    {T : Ty} (normal : T.normalize = T) {x xs : TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (hx : TypesEach sig x env path types T)
    (hxs : TypesEach sig xs env path types (.list T)) :
    TypesEach sig (app "cons" [x, xs]) env path types (.list T) :=
  fun _ => types_app (.cons (hx _) (.cons (hxs _) .nil))
    (atomOf_native atoms (nativeAtomTy_cons T normal))

end Effect4.Modules
