import Effect4.Modules.Step
import Effect4.Laws.Modules.Reading
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Program.TyNormal

/-! Generic tuple helpers serve step-language-sound (translation-simulation, R10)
and step-language-typed (store-typing, R4). Their consumers are the Step tuple arms.
They retain the native flat tuple observation and the existing normalization premises.
They establish no checked Modeled admission, allocation, progress, or host behavior. -/

set_option autoImplicit false
namespace Effect4.Modules
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Store

theorem ItemResults.all_cons {R : Ty → Type} (f : {t : Ty} → R t → Prop)
    {t : Ty} (ts : List Ty) (x : R t) (xs : ItemResults R ts) :
    ItemResults.All (R := R) f (t :: ts) (x, xs) ↔ f x ∧ ItemResults.All f ts xs := by
  cases ts with
  | nil => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | cons _ _ => exact Iff.rfl

/-- Flatten typed values in their declared order. -/
def tupleValues (L : Leaves) : (ts : List Ty) → Inputs L ts → List Val
  | [], _ => []
  | t :: ts, xs => (imageAt L t).toVal xs.1 :: tupleValues L ts xs.2

theorem tupleColumns_image (L : Leaves) : ∀ (ts : List Ty) (xs : Inputs L ts),
    (imageAt L (.tuple ts)).toVal (tupleColumns L ts xs) = Val.tuple (tupleValues L ts xs)
  | [], _ => rfl
  | _ :: ts, xs => by
    have ih := tupleColumns_image L ts xs.2
    exact congrArg (fun tail => Val.tuple ((imageAt L _).toVal xs.1 :: tail)) (Val.list.inj ih)

theorem packTuple_image (L : Leaves) (ts : List Ty) (xs : Inputs L ts) :
    (imageAt L (tupleShape ts)).toVal (packTuple L ts xs) = Val.tuple (tupleValues L ts xs) := by
  match ts with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => exact tupleColumns_image L _ xs

theorem tupleChecks_mono {a b : Ty → Bool} (h : ∀ t, a t = true → b t = true)
    (ts : List Ty) : tupleChecks a ts = true → tupleChecks b ts = true := by
  match ts with
  | [_, _] => exact h _
  | [] => exact fun _ => rfl
  | [_] =>
    intro checked
    simp only [tupleChecks, List.all_cons, List.all_nil, Bool.and_true] at checked ⊢
    exact h _ checked
  | _ :: _ :: _ :: _ =>
    intro checked
    apply List.all_eq_true.mpr
    intro t member
    exact h t (List.all_eq_true.mp checked t member)

theorem tupleNormals_iff (ts : List Ty) :
    tupleFacts.tupleNormals ts ↔ ∀ t ∈ ts, t.normalize = t := by
  induction ts with
  | nil => exact ⟨(fun _ _ h => nomatch h), fun _ => trivial⟩
  | cons t ts ih =>
    cases ts with
    | nil =>
      simp only [tupleFacts.tupleNormals, List.mem_singleton]
      exact ⟨fun h u eq => eq ▸ h, fun h => h t rfl⟩
    | cons u us =>
      change (t.normalize = t ∧ tupleFacts.tupleNormals (u :: us)) ↔ _
      rw [ih]
      simp only [List.mem_cons]
      constructor
      · intro h v member
        cases member with
        | inl eq => exact eq ▸ h.1
        | inr tail => exact h.2 v tail
      · intro h
        exact ⟨h t (Or.inl rfl), fun v member => h v (Or.inr member)⟩

theorem tupleFacts_normal (ts : List Ty) (h : tupleFacts ts) :
    Ty.normalize (.tuple ts) = tupleShape ts := by
  match ts with
  | [_, _] => exact Ty.normalize_pair_canonical h.1 h.2.1 h.2.2.1 h.2.2.2
  | [] => rfl
  | [a] => exact Ty.normalize_tuple_canonical (fun t member => (List.mem_singleton.mp member) ▸ h) (by simp only [List.length_cons, List.length_nil]; omega)
  | a :: b :: c :: ts =>
    apply Ty.normalize_tuple_canonical _ (by simp only [List.length_cons]; omega)
    intro t member
    cases member with
    | head => exact h.1
    | tail _ member => exact (tupleNormals_iff _).mp h.2 t member

theorem tupleFacts_of_check (ts : List Ty) (h : tupleChecks Ty.certNormal ts = true) : tupleFacts ts := by
  match ts with
  | [_, _] => exact certNormal_prod_facts h
  | [] => trivial
  | [_] =>
    apply Ty.normalize_of_certNormal
    exact List.all_eq_true.mp h _ (by exact List.Mem.head _)
  | a :: b :: c :: ts =>
    refine ⟨Ty.normalize_of_certNormal _ (List.all_eq_true.mp h a (List.Mem.head _)), ?_⟩
    apply (tupleNormals_iff _).mpr
    intro t member
    exact Ty.normalize_of_certNormal _ (List.all_eq_true.mp h t (List.Mem.tail _ member))

theorem reads_tuple_image (L : Leaves) (ts : List Ty) (xs : Inputs L ts)
    {sources : List TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (h : ReadsAll sources env path vals (tupleValues L ts xs)) :
    Reads (Authoring.tuple sources) env path vals
      ((imageAt L (tupleShape ts)).toVal (packTuple L ts xs)) := by
  rw [packTuple_image]
  exact reads_app h rfl

theorem types_tuple_shape {Op : Type} {sig : Signature Op} (atoms : sig.atomOf = nativeAtomTy)
    {ts : List Ty} {sources : List TermSrc} {env : Env} {path : List Nat} {types : List Ty}
    (h : ∀ const, TypesAll sig sources env path types const ts) (facts : tupleFacts ts) :
    TypesEach sig (Authoring.tuple sources) env path types (tupleShape ts) :=
  fun _ => (types_app (h _) (atomOf_native atoms (nativeAtomTy_tuple ts))).to (tupleFacts_normal ts facts)
end Effect4.Modules
