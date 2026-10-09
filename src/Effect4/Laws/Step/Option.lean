import Effect4.Laws.Step.Checking
import Effect4.Laws.Step.Reading
import Effect4.Schema.Modeled

/-!
# Consuming an option at one declared type

Placement: helpers of step-language-sound and step-language-typed, requirements R10 and R4.
The consumer is Step.getOrElse, then the shared headOr builder and Pool's headStamp pass.
Reading observes the payload or the supplied default. Both child terms must read.
Typing requires the common result type in normal form and the native atom signature.
The statement establishes no laziness, membership, or host execution.
-/

set_option autoImplicit false
namespace Effect4.Modules
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model

/-- The option matcher binds its variable to the common normal payload and default type. -/
theorem matchArgsB_getOrElse (X : Ty) (normal : X.normalize = X) :
    Bounds.matchArgsB [.option (.var 0), .var 0] [.option X, X] =
      some [(0, Ty.join X X), (0, Ty.join X X)] := by
  open Bounds Ty in
  dsimp only [matchArgsB]
  rw [candsList_cons, cands, cands_var, candsList_cons, cands_var, candsList_nil,
    List.append_nil, List.cons_append, List.nil_append]
  have solved : solve [] [(0, .co, X), (0, .co, X)] =
      [(0, Ty.join X X), (0, Ty.join X X)] := rfl
  rw [solved, if_pos (show [Ty.option (.var 0), Ty.var 0].length = [Ty.option X, X].length from rfl)]
  have joined : Ty.join X X = X := by rw [Ty.join_self, normal]
  have item : Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.var 0) = X := by
    dsimp only [Ty.instantiate, List.lookup]
    rw [joined]
    rfl
  have optional : Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.option (.var 0)) = .option X := by
    dsimp only [Ty.instantiate, List.lookup]
    rw [joined]
    rfl
  have fits : (([Ty.option (.var 0), Ty.var 0].zip [Ty.option X, X]).all fun pr =>
      Ty.sub pr.2.normalize (Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] pr.1).normalize) = true := by
    change (Ty.sub (.option X : Ty).normalize
      (Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.option (.var 0))).normalize &&
      (Ty.sub X.normalize (Ty.instantiate [(0, Ty.join X X), (0, Ty.join X X)] (.var 0)).normalize && true)) = true
    rw [optional, item, Ty.sub_refl, Ty.sub_refl]
    rfl
  rw [fits]
  rfl

/-- The native option consumer returns the common normal result type. -/
theorem nativeAtomTy_getOrElse (T : Ty) (normal : T.normalize = T) :
    nativeAtomTy "getOrElse" [.option T, T] = some T := by
  change (Bounds.matchArgsB [.option (.var 0), .var 0] [.option T, T]).map
    (fun σ => Ty.instantiate σ (.var 0)) = some T
  rw [matchArgsB_getOrElse T normal]
  dsimp only [Option.map, Ty.instantiate, List.lookup, BEq.beq, Nat.beq]
  have joined : Ty.join T T = T := by rw [Ty.join_self, normal]
  rw [joined]
  rfl

/-- The option consumer has its common declared type under either literal flag. -/
theorem types_getOrElse {Op : Type} {sig : Signature Op} (atoms : sig.atomOf = nativeAtomTy)
    {T : Ty} (normal : T.normalize = T) {x fallback : TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (hx : TypesEach sig x env path types (.option T))
    (hd : TypesEach sig fallback env path types T) :
    TypesEach sig (app "getOrElse" [x, fallback]) env path types T :=
  fun _ => types_app (.cons (hx _) (.cons (hd _) .nil))
    (atomOf_native atoms (nativeAtomTy_getOrElse T normal))

/-- An option consumer reads the payload, or its already evaluated default. -/
theorem reads_getOrElse (L : Leaves) (T : Ty) (x : Option (CarrierAt L T)) (fallback : CarrierAt L T)
    {sx sd : TermSrc} {env : Env} {path : List Nat} {vals : List Store.Val}
    (hx : Reads sx env path vals ((imageAt L (.option T)).toVal x))
    (hd : Reads sd env path vals ((imageAt L T).toVal fallback)) :
    Reads (app "getOrElse" [sx, sd]) env path vals ((imageAt L T).toVal (x.getD fallback)) := by
  cases x with
  | none => exact reads_app (.cons hx (.cons hd .nil)) rfl
  | some v => exact reads_app (.cons hx (.cons hd .nil)) rfl

end Effect4.Modules
