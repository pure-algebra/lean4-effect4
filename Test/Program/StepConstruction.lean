import Effect4.Laws.Modules.Construction
import Effect4.Program.Native

/-! Readers and finite refusal controls for the shared construction rules.
Placement: `step-language-sound` (R10) and `step-language-typed` (R4).
These checks establish neither a module run nor a host result. -/
set_option autoImplicit false
namespace Test.Program.StepConstruction
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Store Effect4.Schema
open Effect4.Schema.Model Effect4.Modules

def fields : List (String × Bool × Ty) := [("active", false, .bool), ("count", false, .nat)]
def present : List (String × TermSrc) := [("active", bool true), ("count", nat 7)]

-- Reader at a populated record and every identity interpretation and scope.
example (L : Leaves) (env : Env) (path : List Nat) (vals : List Val) :
    Reads (record fields present) env path vals
      ((imageAt L (.record fields)).toVal (true, ((7 : Nat), ()))) :=
  reads_record_image L fields (true, ((7 : Nat), ())) (by decide) rfl
    (.cons (reads_bool true env path vals) (.cons (reads_nat 7 env path vals) .nil))

-- Reader of exact field typing, under either literal flag.
example {Op : Type} (sig : Signature Op) {env : Env} {path : List Nat} {types : List Ty} :
    TypesEach sig (record fields present) env path types (.record fields) :=
  types_record_declared sig fields (by decide) rfl rfl rfl
    (.cons (types_bool true true) (.cons (types_nat 7 true) .nil))

example {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {env : Env} {path : List Nat} {types : List Ty} :
    TypesEach sig (ascribe (.list .nat) nilT) env path types (.list .nat) :=
  types_nil_ascribe sig atoms .nat rfl rfl (by
    unfold Ty.subN
    change Ty.sub (.list .never) (.list .nat) = true
    rw [Ty.sub_args_list]
    change (Ty.sub .never .nat && true) = true
    rw [Ty.OrderProof.sub_never, Bool.and_true])

example {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {env : Env} {path : List Nat} {types : List Ty} :
    TypesEach sig (ascribe (.option .bool) noneT) env path types (.option .bool) :=
  types_none_ascribe sig atoms .bool rfl rfl (by
    unfold Ty.subN
    change Ty.sub (.option .never) (.option .bool) = true
    rw [Ty.sub_args_option]
    change (Ty.sub .never .bool && true) = true
    rw [Ty.OrderProof.sub_never, Bool.and_true])

-- Normality does not discharge formation of a type variable outside a template.
#guard (.list (.var 0) : Ty).normalize == .list (.var 0)
#guard (Formation.check (Formation.sites false [] (.record (ascribeFields (.list (.var 0)))))).isSome
-- Repeated names refuse the record check even when every supplied type matches.
#guard Program.Record.check [("x", false, .nat), ("x", false, .nat)] ["x", "x"] [.nat, .nat] == none
-- A wrong supplied field type refuses; construction is no cast.
#guard Program.Record.check fields ["active", "count"] [.nat, .nat] == none
-- An unsorted input is canonicalized, so the image connector needs ascending names.
#guard Machine.Record.build ["z", "a"] [.nat 1, .nat 2] !=
  some (Machine.Record.frame [("z", .nat 1), ("a", .nat 2)])
end Test.Program.StepConstruction
