import Effect4.Program.Decision
import Effect4.Laws.Program.Residual

/-!
# Laws.Program.Decision — a typed scrutinee always decides

The `select` packet (`docs/research/2026-09-16-select-and-iterate-ready-packet.md` §1.1):
`Decision.decide_typed`, the one safety theorem of the value-decided fork. A scrutinee of
type `t` on which `Decision.arms` answers always decides, and the value the chosen arm binds
has that arm's type. `.bool` by the shape of a Boolean, `.option` by
`Val.hasTy_option_inv_at`, `.tag` by `Ty.payload_hasTy` (the hit) and `Ty.diffTag_sound`
(the miss). `NativeAtom.tagHit_eq` bridges the runtime test to the reader; `tagHit` keeps
its own equations, which the `catchIf` lemmas depend on.

This is the whole "no `badShape` on an admitted program" story for the construct, and the
only place the three decisions are proved about separately.
-/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- `tagHit` is the Boolean image of `tagPayload?`. -/
theorem NativeAtom.tagHit_eq (tag : String) (v : Val) :
    NativeAtom.tagHit tag v = (Val.tagPayload? tag v).isSome := by
  cases v <;> try rfl
  rename_i xs
  match xs with
  | [] => rfl
  | [x] => cases x <;> rfl
  | x :: _ :: _ :: _ => cases x <;> rfl
  | [x, y] =>
    cases x <;> try rfl
    rename_i t
    simp only [NativeAtom.tagHit, Val.tagPayload?]
    cases t == tag <;> simp

/-- On a tagged column, a hit's payload has the payload type: the two-cell list can inhabit
only a member tagged with the hit's tag, and that member's payload type is one of the
payloads whose canonical union `payloadTy` is. -/
theorem Ty.payload_hasTy (tag : String) (c : Ty) (v p : Val) (P : Ty) (allocated : List String)
    (hc : Ty.taggedColumn c = true) (hv : Val.hasTy v c allocated = true)
    (hp : Val.tagPayload? tag v = some p) (hP : Ty.payloadTy tag c = some P) :
    Val.hasTy p P allocated = true := by
  -- the value is the two-cell list `[str tag, p]`
  obtain rfl : v = Val.list [Val.str tag, p] := by
    unfold Val.tagPayload? at hp
    split at hp
    · rename_i t x
      split at hp
      · rename_i h
        simp only [Option.some.injEq] at hp
        subst hp
        simp only [beq_iff_eq] at h
        subst h
        rfl
      · exact nomatch hp
    · exact nomatch hp
  -- some member of the column admits it
  rw [← hasTy_members] at hv
  simp only [List.any_eq_true] at hv
  obtain ⟨m, hm, hvm⟩ := hv
  simp only [Ty.taggedColumn, List.all_eq_true] at hc
  have hcm := hc m hm
  -- that member is a pair tagged `tag`, and its payload type admits `p`
  obtain ⟨q, hmq, hq⟩ : ∃ q, m = .prod (.lit tag) q ∧ Val.hasTy p q allocated = true := by
    rcases m with _ | _ | _ | _ | _ | _ | tgt | inner | inner | ⟨a, b⟩ | ⟨e, w⟩ | ⟨w, e⟩ | e
      | ⟨w, e⟩ | ⟨l, r⟩ | s
    all_goals try (exact absurd hcm Bool.false_ne_true)
    all_goals try (simp only [Val.hasTy, Bool.false_eq_true] at hvm; done)
    rcases a with _ | _ | _ | _ | _ | _ | tgt | inner | inner | ⟨a1, a2⟩ | ⟨e, w⟩ | ⟨w, e⟩ | e
      | ⟨w, e⟩ | ⟨l, r⟩ | t
    all_goals try (exact absurd hcm Bool.false_ne_true)
    simp only [Val.hasTy, Bool.and_eq_true, beq_iff_eq] at hvm
    obtain ⟨rfl, hq⟩ := hvm
    exact ⟨b, rfl, hq⟩
  -- so `q` is one of the payloads
  have hq_mem : q ∈ c.members.filterMap (Ty.payloadOf tag) := by
    rw [List.mem_filterMap]
    refine ⟨m, hm, ?_⟩
    rw [hmq]
    simp only [Ty.payloadOf]
    exact if_pos trivial
  have hne : c.members.filterMap (Ty.payloadOf tag) ≠ [] := fun h => by
    rw [h] at hq_mem
    exact List.not_mem_nil hq_mem
  have hP' : Ty.payloadTy tag c =
      some (Ty.normalize (Ty.ofMembers (c.members.filterMap (Ty.payloadOf tag)))) := by
    unfold Ty.payloadTy
    cases hfm : c.members.filterMap (Ty.payloadOf tag) with
    | nil => exact absurd hfm hne
    | cons x xs => rfl
  rw [hP'] at hP
  simp only [Option.some.injEq] at hP
  subst hP
  rw [hasTy_normalize, hasTy_ofMembers]
  simp only [List.any_eq_true]
  exact ⟨q, hq_mem, hq⟩

/-- The value an arm binds inhabits the arm's environment extension: nothing against nothing,
one value against one type. -/
def Decision.BoundTyped (allocated : List String) : Option Val → List Ty → Prop
  | none, [] => True
  | some x, [ty] => Val.hasTy x ty allocated = true
  | _, _ => False

/-- A typed scrutinee always decides, and the bound value has the arm's type. -/
theorem Decision.decide_typed (d : Decision) {t : Ty} {e0 e1 : List Ty} {v : Val}
    {allocated : List String}
    (harms : d.arms t = some (e0, e1)) (hv : Val.hasTy v t allocated = true) :
    ∃ first bound, d.decide v = some (first, bound) ∧
      Decision.BoundTyped allocated bound (if first then e0 else e1) := by
  cases d with
  | bool =>
    simp only [Decision.arms] at harms
    split at harms
    · rename_i ht
      subst ht
      try simp only [Option.some.injEq, Prod.mk.injEq] at harms
      obtain ⟨h0, h1⟩ := harms
      subst h0; subst h1
      simp only [Val.hasTy] at hv
      split at hv
      · rename_i b
        exact ⟨b, none, rfl, by cases b <;> trivial⟩
      · exact nomatch hv
    · exact nomatch harms
  | option =>
    simp only [Decision.arms] at harms
    split at harms
    · rename_i a hnorm
      try simp only [Option.some.injEq, Prod.mk.injEq] at harms
      obtain ⟨h0, h1⟩ := harms
      subst h0; subst h1
      rw [← hasTy_normalize, hnorm] at hv
      rcases Val.hasTy_option_inv_at hv with rfl | ⟨x, rfl, hx⟩
      · exact ⟨true, none, rfl, trivial⟩
      · exact ⟨false, some x, rfl, hx⟩
    · exact nomatch harms
  | tag name =>
    simp only [Decision.arms] at harms
    split at harms
    · rename_i hcol
      cases hP : Ty.payloadTy name t.normalize with
      | none =>
        rw [hP] at harms
        exact nomatch harms
      | some P =>
        rw [hP] at harms
        simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at harms
        obtain ⟨h0, h1⟩ := harms
        subst h0; subst h1
        have hv' : Val.hasTy v t.normalize allocated = true := by
          rw [hasTy_normalize]
          exact hv
        cases hp : Val.tagPayload? name v with
        | some p =>
          refine ⟨true, some p, by simp only [Decision.decide, hp], ?_⟩
          show Val.hasTy p P allocated = true
          exact Ty.payload_hasTy name t.normalize v p P allocated hcol hv' hp hP
        | none =>
          refine ⟨false, some v, by simp only [Decision.decide, hp], ?_⟩
          show Val.hasTy v (Ty.diffTag name t.normalize) allocated = true
          apply Ty.diffTag_sound name t.normalize v allocated hv'
          rw [NativeAtom.eval_tagIs, NativeAtom.tagHit_eq, hp]
          rfl
    · exact nomatch harms

end Effect4.Program
