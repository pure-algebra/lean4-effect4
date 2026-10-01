/-! Seat TREE exploration E2 (2026-10-01): does a hand single-motive eliminator, registered
with `@[induction_eliminator]`, give back `induction t with | ctor … ih => …` on a nested `Ty`
(option C) and on a mutual `Ty`/`Fields` (option B)? Core Lean only. -/

namespace E2.C

inductive Ty
  | never | unit | nat
  | option (inner : Ty)
  | prod (left right : Ty)
  | record (fields : List (String × Ty))

/-- The membership-form eliminator, as `Store.Val.ind` is (`Store/Carrier/Val.lean:270`). -/
@[induction_eliminator]
theorem Ty.ind {motive : Ty → Prop}
    (never : motive .never) (unit : motive .unit) (nat : motive .nat)
    (option : ∀ inner, motive inner → motive (.option inner))
    (prod : ∀ left right, motive left → motive right → motive (.prod left right))
    (record : ∀ fields, (∀ p ∈ fields, motive p.2) → motive (.record fields)) :
    ∀ t, motive t := fun t =>
  Ty.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs, motive p.2)
    (motive_3 := fun p => motive p.2)
    never unit nat option prod record
    (fun _ h => nomatch h)
    (fun _ _ ihHead ihTail => fun p hp => by
      cases hp with
      | head => exact ihHead
      | tail _ h => exact ihTail p h)
    (fun _ _ ih => ih)
    t

def depth : Ty → Nat
  | .never | .unit | .nat => 0
  | .option t => depth t + 1
  | .prod a b => max (depth a) (depth b) + 1
  | .record fs => depthFields fs + 1
termination_by structural t => t
where depthFields : List (String × Ty) → Nat
  | [] => 0
  | (_, t) :: rest => max (depth t) (depthFields rest)
termination_by structural fs => fs

theorem depthFields_ge {fs : List (String × Ty)} {p : String × Ty} (h : p ∈ fs) :
    depth p.2 ≤ depth.depthFields fs := by
  induction fs with
  | nil => nomatch h
  | cons q rest ih =>
    obtain ⟨n, t⟩ := q
    rcases List.mem_cons.mp h with rfl | h
    · simp only [depth.depthFields]; omega
    · have := ih h; simp only [depth.depthFields]; omega

/-- The tactic, the arm names and the hypotheses of today's proofs, one arm more. -/
theorem depth_lt_of_record (t : Ty) : ∀ p, t = .record [p] → depth p.2 < depth t := by
  induction t with
  | never => intro p h; nomatch h
  | unit => intro p h; nomatch h
  | nat => intro p h; nomatch h
  | option inner ih => intro p h; nomatch h
  | prod left right ihl ihr => intro p h; nomatch h
  | record fields ih =>
    intro p h
    injection h with h
    subst h
    have := depthFields_ge (fs := [p]) (List.mem_singleton_self p)
    simp only [depth]
    omega

#print axioms depth_lt_of_record

end E2.C

namespace E2.B

mutual
inductive Ty
  | never | unit | nat
  | option (inner : Ty)
  | prod (left right : Ty)
  | record (fields : Fields)
inductive Fields
  | nil
  | cons (name : String) (type : Ty) (rest : Fields)
end

def Fields.types : Fields → List Ty
  | .nil => []
  | .cons _ t rest => t :: rest.types

@[induction_eliminator]
theorem Ty.ind {motive : Ty → Prop}
    (never : motive .never) (unit : motive .unit) (nat : motive .nat)
    (option : ∀ inner, motive inner → motive (.option inner))
    (prod : ∀ left right, motive left → motive right → motive (.prod left right))
    (record : ∀ fields, (∀ t ∈ fields.types, motive t) → motive (.record fields)) :
    ∀ t, motive t := fun t =>
  Ty.rec (motive_1 := motive) (motive_2 := fun fs => ∀ t ∈ fs.types, motive t)
    never unit nat option prod record
    (fun _ h => nomatch h)
    (fun _ _ _ ihHead ihTail => fun t ht => by
      cases ht with
      | head => exact ihHead
      | tail _ h => exact ihTail t h)
    t

theorem record_ne (t : Ty) : ∀ fs, t = .record fs → ∀ u ∈ fs.types, u ≠ t := by
  induction t with
  | never => intro fs h; nomatch h
  | unit => intro fs h; nomatch h
  | nat => intro fs h; nomatch h
  | option inner ih => intro fs h; nomatch h
  | prod left right ihl ihr => intro fs h; nomatch h
  | record fields _ =>
    intro fs h u hu heq
    injection h with h
    subst h
    have size_lt : ∀ (gs : Fields) (v : Ty), v ∈ gs.types → sizeOf v < sizeOf gs := by
      intro gs
      induction gs using Fields.rec (motive_1 := fun _ => True) with
      | nil => intro v hv; nomatch hv
      | cons n t rest _ ihr =>
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simp only [Fields.cons.sizeOf_spec]; omega
        · have := ihr v hv; simp only [Fields.cons.sizeOf_spec]; omega
      | _ => trivial
    have hlt := size_lt fields u hu
    have hrec : sizeOf (Ty.record fields) = 1 + sizeOf fields := Ty.record.sizeOf_spec fields
    rw [heq] at hlt
    omega

#print axioms record_ne

end E2.B
