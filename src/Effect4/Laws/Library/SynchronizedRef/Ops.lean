import Effect4.Library.SynchronizedRef.Ops
import Effect4.Laws.Library.Semaphore.Ops
import Effect4.Laws.Library.Ref.Callback
import Effect4.Laws.Step.Construction

/-! Compatibility readers of existing R4 claims: waiting-wrapper-typed,
step-language-typed, and fold-typed-atomic-update.
The plan records all five placement fields before these proofs.
These laws check make, get, and a pure Step callback under the native signature.
They establish no lock ownership, progress, schedule agreement, allocation, membership, or host behavior. -/

set_option autoImplicit false
namespace Effect4.SynchronizedRef
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The handle's declaration is canonical when its backing type is canonical.
Helper of make_answers, get_answers, and modify_answers. -/
theorem handle_normal {A : Ty} (normal : A.normalize = A) :
    (handleTy A).normalize = handleTy A := by
  change Ty.normalize (.record _) = _
  rw [Ty.normalize_record]
  change Ty.record [("backing", false, (Ty.refOf A).normalize),
    ("semaphore", false, (Ty.refOf Semaphore.cellTy).normalize)] = _
  rw [normalize_refOf_canonical normal, normalize_refOf_canonical Semaphore.Model.cellTy_normal]
  rfl

/-- The handle's field types are formed when its backing type is formed.
Helper of make_answers. -/
theorem handle_nodes {A : Ty} (formed : NodesFormed A) : NodesFormed (handleTy A) := by
  intro t member
  change t ∈ handleTy A :: (Formation.nodes (.refOf A) ++
    (Formation.nodes (.refOf Semaphore.cellTy) ++ [])) at member
  rcases List.mem_cons.mp member with rfl | member
  · change (["backing", "semaphore"] : List String).Nodup
    decide
  · rcases List.mem_append.mp member with member | member
    · exact nodesFormed_refOf formed t member
    · rw [List.append_nil] at member
      exact nodesFormed_refOf Semaphore.cell_nodes t member

/-- Read the backing field at the backing Ref type.
Helper of get_answers and modify_answers. -/
theorem backing_type {A : Ty} (normal : A.normalize = A) :
    Record.fieldType false (handleTy A) "backing" = some (.refOf A) :=
  Record.fieldType_normal (handle_normal normal) rfl

/-- Read the semaphore field at the existing Semaphore handle type.
Helper of modify_answers. -/
theorem semaphore_type {A : Ty} (normal : A.normalize = A) :
    Record.fieldType false (handleTy A) "semaphore" = some (.refOf Semaphore.cellTy) :=
  Record.fieldType_normal (handle_normal normal) rfl

/-- Construction checks its declared backing type and the existing Semaphore constructor.
Compatibility reader of waiting-wrapper-typed and native Ref typing under R4. -/
@[semantics "store-typing" (requirement := R4)]
theorem make_answers {table : RowTable} {A : Ty} {initial : TermSrc} {s : TypedScope}
    (normal : A.normalize = A) (formed : NodesFormed A)
    (typed : ∀ path, Types (nativeSignature table) initial s.env path s.types false A) :
    Answers (nativeSignature table) (make A initial) s (handleTy A) := by
  unfold make
  refine answers_bindWith (answers_refMake normal formed typed) fun backing hbacking => ?_
  refine answers_bindWith (Semaphore.make_types 1 (by decide) _) fun semaphore hsemaphore => ?_
  refine answers_succeed fun path => ?_
  exact types_record_declared (nativeSignature table) (handleFields A) (by
      exact .cons (fun entry member => by
        rw [List.mem_singleton.mp member]
        change Field.ltKey (Field.bytesKey "backing") (Field.bytesKey "semaphore") = true
        decide) (.cons (fun _ member => nomatch member) .nil))
    (handle_normal normal) ((Formation.check_eq_none_iff _).mpr (formed_sites (handle_nodes formed) _))
    rfl (.cons (hbacking.push.here path true) (.cons (hsemaphore.here path true) .nil))

/-- Reading checks only the backing field and the existing Ref read.
Compatibility reader of native Ref typing under R4. -/
@[semantics "store-typing" (requirement := R4)]
theorem get_answers {table : RowTable} {A : Ty} {self : TermSrc} {s : TypedScope}
    (normal : A.normalize = A) (formed : NodesFormed A)
    (typed : Typed (nativeSignature table) self s (handleTy A)) :
    Answers (nativeSignature table) (get self) s A :=
  answers_refGet normal formed (fun path _ => types_field (typed path false) (backing_type normal))

/-- A pure modify checks at the original caller scope, including all captured sources.
Compatibility reader of waiting-wrapper-typed, step-language-typed, and fold-typed-atomic-update.
The one-cell meaning remains the existing Ref.modify_callback_agrees claim. -/
@[semantics "store-typing" (requirement := R4)]
theorem modify_answers {table : RowTable} {A B : Ty} {Γ : List Ty} {self : TermSrc}
    (body : Step (A :: Γ) (.prod B A))
    (captures : {t : Ty} → Input Γ t → TermSrc) {s : TypedScope}
    (normalA : A.normalize = A) (formedA : NodesFormed A)
    (normalB : B.normalize = B) (formedB : NodesFormed B)
    (typed : Typed (nativeSignature table) self s (handleTy A))
    (inputs : ∀ {t : Ty} (x : Input Γ t), Typed (nativeSignature table) (captures x) s t)
    (facts : body.Facts) :
    Answers (nativeSignature table) (modify self body captures) s B := by
  intro path
  have held := Step.freeze_kept (typed path)
  have captured : ∀ {t : Ty} (x : Input Γ t),
      Kept (nativeSignature table) (Step.freeze (captures x) s.env path) s t :=
    fun x => Step.freeze_kept (inputs x path)
  have wrapped := Semaphore.withPermits_types (b := EffTy.pure B)
    (held.field (semaphore_type normalA)) (kept_nat 1 s)
    (fun t reach => (Effect4.Ref.modify_callback_answers body
      (fun x => Step.freeze (captures x) s.env path) normalA formedA normalB formedB
      ((held.field (backing_type normalA)) t reach)
      (fun x => captured x t reach) facts).has)
  exact wrapped.answers path

end Effect4.SynchronizedRef
