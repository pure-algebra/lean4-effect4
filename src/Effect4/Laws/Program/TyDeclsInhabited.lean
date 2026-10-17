import Effect4.Laws.Program.TyDecls
import Effect4.Laws.Program.Typed.Membership

/-!
# Inhabitance under a declaration table: sound and complete against membership

The completeness of inhabitance under a table (`inhabited_iff_memberIn`), with the soundness
step it shares. They sit above `Typed/Membership.lean`: a context's witness is built in a world
(`context_services_fresh`), and the step at a leaf reads `inhabited_of_hasTy`. The table's
membership, its decision and its order are `Laws/Program/TyDecls.lean`, below the world, so the
typed world reads them.

Placement of the claims (`AGENTS.md`, five points): as `Laws/Program/TyDecls.lean`'s, the claim
`recursive-types-inhabited`.
-/

namespace Effect4.Program
open Effect4 Effect4.Machine

namespace TyDecls

/-- At a type that names no declared name at its head, a step whose questions are inhabited is
inhabited. -/
theorem inhabitedWith_of_step {decls : TyDecls} {known : List String} {v : Val} {t : Ty}
    {allocated : List String} {ps : List (Val × Ty)} (hu : decls.unfold? t = none)
    (hps : Val.obligations v t allocated = some ps)
    (hall : ∀ p ∈ ps, cata_ty (decls.inhabitedWith known) p.2 = true) :
    cata_ty (decls.inhabitedWith known) t = true := by
  have hleaf : ∀ {u : Ty}, cata_ty (decls.inhabitedWith known) u = Effect4.Program.inhabited u →
      Val.obligations v u allocated = (if Val.hasTy v u allocated then some [] else none) →
      Val.obligations v u allocated = some ps → cata_ty (decls.inhabitedWith known) u = true := by
    intro u hcata hcatch hsome
    rw [hcatch] at hsome
    cases hh : Val.hasTy v u allocated with
    | true => rw [hcata]; exact Typed.inhabited_of_hasTy u v allocated hh
    | false =>
      rw [hh] at hsome
      cases hsome
  cases t
  case never => cases hps
  case union => cases hps
  case handle name => exact hleaf rfl rfl hps
  case app name args =>
    unfold unfold? at hu
    simp only [Ty.refName?, Option.bind_some] at hu
    refine hleaf ?_ rfl hps
    show (if (decls.body? name).isSome then _ else _) = _
    cases hb : decls.body? name with
    | some b =>
      rw [hb] at hu
      cases hu
    | none => rfl
  case option | list | exitOf | causeOf | map => rfl
  case prod a b =>
    simp only [Val.obligations] at hps
    split at hps
    · cases hps
      show (cata_ty (decls.inhabitedWith known) a && cata_ty (decls.inhabitedWith known) b) = true
      rw [hall _ (List.mem_cons_self), hall _ (List.mem_cons_of_mem _ List.mem_cons_self)]
      rfl
    · cases hps
  case except error value =>
    simp only [Val.obligations] at hps
    split at hps
    · cases hps
      show (cata_ty (decls.inhabitedWith known) error || cata_ty (decls.inhabitedWith known) value) = true
      rw [hall _ List.mem_cons_self, Bool.true_or]
    · cases hps
      show (cata_ty (decls.inhabitedWith known) error || cata_ty (decls.inhabitedWith known) value) = true
      rw [hall _ List.mem_cons_self, Bool.or_true]
    · cases hps
  case record fs =>
    simp only [Val.obligations] at hps
    obtain ⟨parts, _, hnamed⟩ := Option.bind_eq_some_iff.mp hps
    rw [cata_ty_record]
    have hpm : prodMapSnd (prodMapSnd (cata_ty (decls.inhabitedWith known))) =
        fun q : String × Bool × Ty => (q.1, prodMapSnd (cata_ty (decls.inhabitedWith known)) q.2) :=
      rfl
    rw [hpm]
    show (Ty.canon (fs.map fun q => (q.1, prodMapSnd (cata_ty (decls.inhabitedWith known)) q.2))).all
      (fun p => p.2.1 || p.2.2) = true
    unfold Ty.canon
    rw [Field.canonBy_map, List.all_map, List.all_eq_true]
    intro c hc
    show (c.2.1 || cata_ty (decls.inhabitedWith known) c.2.2) = true
    cases ho : c.2.1 with
    | true => rfl
    | false =>
      obtain ⟨x, hx⟩ := namedPairs_required _ _ _ hnamed c hc ho
      rw [Bool.false_or]
      exact hall _ hx
  case tuple ts =>
    simp only [Val.obligations] at hps
    split at hps
    · rename_i xs
      rw [cata_ty_tuple]
      show (ts.map (cata_ty (decls.inhabitedWith known))).all id = true
      rw [List.all_eq_true]
      intro b hb
      obtain ⟨u, hu', rfl⟩ := List.mem_map.mp hb
      obtain ⟨x, hx⟩ := itemPairs_all _ _ hps u hu'
      exact hall _ hx
    · cases hps
  all_goals exact hleaf rfl rfl hps

end TyDecls

/-- **Inhabitance is sound against membership under the table**: a type with a member is
inhabited, so refusing a column that `TyDecls.inhabited` calls empty never refuses one with a
member. -/
theorem inhabited_of_memberIn {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    (h : MemberIn decls allocated v t) : decls.inhabited t = true := by
  induction h with
  | left _ ih => rw [TyDecls.inhabited_union, ih, Bool.true_or]
  | right _ ih => rw [TyDecls.inhabited_union, ih, Bool.or_true]
  | @unfold v t name body hu _ ih =>
    have hb := TyDecls.body?_of_unfold? hu
    have hname := List.contains_iff_mem.mpr (TyDecls.mem_inhabitedNames hb ih)
    have href : t.refName? = some name := by
      unfold TyDecls.unfold? at hu
      cases hr : t.refName? with
      | none =>
        rw [hr] at hu
        cases hu
      | some m =>
        rw [hr, Option.bind_some] at hu
        obtain ⟨b', _, he⟩ := Option.map_eq_some_iff.mp hu
        cases he
        rfl
    cases t
    case app n args =>
      cases href
      show (if (decls.body? name).isSome then _ else _) = true
      rw [hb, Option.isSome_some, if_pos rfl]
      exact hname
    all_goals cases href
  | step hu hps _ ih => exact TyDecls.inhabitedWith_of_step hu hps ih

/-- **A round's algebra is complete when its known names are witnessed**: a type that the round
calls inhabited has a member at an extension of any allocation table. Placement: concept
`store-typing`, R3, a step of the claim `recursive-types-inhabited`. Route: induct on `t`, as
`fits_of_inhabited_fresh` does. A union or an `except` takes a side that is inhabited; a product,
a tuple and a record's required fields build their parts in turn, each at the table the previous
part left, and carry the earlier parts forward (`memberIn_mono`). An external handle takes the
fresh index `allocated.length`. A declared name takes its witness from `hk`; an option, a list, a
map, an exit and a cause have a member with no question. Consumer: `witnessed_inhabitedNames`. -/
@[semantics "store-typing" (requirement := R3)]
theorem exists_memberIn_fresh {decls : TyDecls} {known : List String}
    (hk : decls.Witnessed known) (t : Ty) (h : cata_ty (decls.inhabitedWith known) t = true)
    (allocated : List String) :
    ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
      MemberIn decls allocated' v t := by
  induction t generalizing allocated with
  | never => cases h
  | var _ => cases h
  | unit => exact ⟨.unit, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | nat => exact ⟨.nat 0, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | int => exact ⟨.nat 0, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | number => exact ⟨.nat 0, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | string => exact ⟨.str "", allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | bool => exact ⟨.bool true, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | lit s =>
    exact ⟨.str s, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl (beq_iff_eq.mpr rfl)⟩
  | null => exact ⟨.none, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | undefined => exact ⟨.unit, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | bytes => exact ⟨.bytes [], allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | unknown => exact ⟨.unit, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | fiberOf _ _ _ _ =>
    exact ⟨Val.fiber ⟨0⟩, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | refOf _ _ => exact ⟨Val.cell ⟨0⟩, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | deferredOf _ _ _ _ =>
    exact ⟨Val.promise ⟨0⟩, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | contextOf keys =>
    obtain ⟨services, _, hkeys⟩ := Typed.context_services_fresh
      (Typed.initialWorld (EffTy.pure .unit) fun _ => some .unit)
      (fun _ => ⟨.unit, .unit, rfl, trivial, Typed.live_of_handles_nil rfl⟩) keys.elems
    refine ⟨Val.context (Ctx.withServices services), allocated, fun _ _ h => h,
      memberIn_of_hasTy rfl rfl ?_⟩
    have hctx : Val.context? (Val.context (Ctx.withServices services)) =
        some (Ctx.withServices services) := ctxImage.ofVal_toVal _
    show (match Val.context? (Val.context (Ctx.withServices services)) with
      | some ctx => keys.elems.all fun key => (ctx.services.getV key).isSome
      | none => false) = true
    rw [hctx, List.all_eq_true]
    intro key hkey
    obtain ⟨_, value, _, hg, _⟩ := hkeys key hkey
    show (services.getV key).isSome = true
    rw [hg]
    rfl
  | option _ _ => exact ⟨.none, allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | list _ _ => exact ⟨.list [], allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | map _ _ _ _ =>
    exact ⟨.list [], allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | exitOf _ _ _ _ =>
    exact ⟨Val.exitErr ⟨[]⟩, allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | causeOf _ _ =>
    exact ⟨Val.exitErr ⟨[]⟩, allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | handle target =>
    obtain ⟨v, al', e, hv⟩ := exists_hasTy_handle_fresh (Typed.not_retired_of_inhabited h) allocated
    exact ⟨v, al', e, memberIn_of_hasTy rfl rfl hv⟩
  | app name args _ =>
    cases hb : decls.body? name with
    | some body =>
      have hc : known.contains name = true := by
        have h' : (if (decls.body? name).isSome then known.contains name
            else inhabitedAlg.ty_app name (args.map (cata_ty (decls.inhabitedWith known)))) =
            true := h
        rw [hb, Option.isSome_some, if_pos rfl] at h'
        exact h'
      have hu : decls.unfold? (.app name args) = some (name, body) := by
        show (decls.body? name).map (name, ·) = _
        rw [hb]
        rfl
      exact exists_memberIn_ref hk hu hc allocated
    | none =>
      -- an undeclared reference is never inhabited (decisions row 406 (1))
      have h' : (if (decls.body? name).isSome then known.contains name
          else inhabitedAlg.ty_app name (args.map (cata_ty (decls.inhabitedWith known)))) =
          true := h
      rw [hb, Option.isSome_none] at h'
      exact Bool.noConfusion h'
  | prod a b iha ihb =>
    have h' : (cata_ty (decls.inhabitedWith known) a && cata_ty (decls.inhabitedWith known) b) =
      true := h
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h'
    obtain ⟨va, al1, e1, ma⟩ := iha ha allocated
    obtain ⟨vb, al2, e2, mb⟩ := ihb hb al1
    refine ⟨.list [va, vb], al2, fun i s hi => e2 i s (e1 i s hi), .step rfl rfl ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact memberIn_mono e2 ma
    · rcases List.mem_singleton.mp hp with rfl
      exact mb
  | except e a ihe iha =>
    have h' : (cata_ty (decls.inhabitedWith known) e || cata_ty (decls.inhabitedWith known) a) =
      true := h
    rcases Bool.or_eq_true_iff.mp h' with he | ha
    · obtain ⟨v, al', ext, hv⟩ := ihe he allocated
      refine ⟨.ctor 0 [v], al', ext, .step rfl rfl ?_⟩
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      exact hv
    · obtain ⟨v, al', ext, hv⟩ := iha ha allocated
      refine ⟨.ctor 1 [v], al', ext, .step rfl rfl ?_⟩
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      exact hv
  | union l r ihl ihr =>
    have h' : (cata_ty (decls.inhabitedWith known) l || cata_ty (decls.inhabitedWith known) r) =
      true := h
    rcases Bool.or_eq_true_iff.mp h' with hl | hr
    · obtain ⟨v, al', ext, hv⟩ := ihl hl allocated
      exact ⟨v, al', ext, .left hv⟩
    · obtain ⟨v, al', ext, hv⟩ := ihr hr allocated
      exact ⟨v, al', ext, .right hv⟩
  | tuple ts ih =>
    rw [cata_ty_tuple] at h
    have h' : (ts.map (cata_ty (decls.inhabitedWith known))).all id = true := h
    rw [List.all_map, List.all_eq_true] at h'
    obtain ⟨xs, ps, al', ext, hps, hall⟩ :=
      itemPairs_fresh ts (fun u hu al => ih u hu (h' u hu) al) allocated
    exact ⟨.list xs, al', ext, .step rfl hps hall⟩
  | record fs ih =>
    rw [TyDecls.inhabitedWith_record, List.all_eq_true] at h
    obtain ⟨ns, xs, ps, al', ext, _, hps, hall⟩ :=
      namedPairs_fresh (Ty.canon fs) (Field.canonBy_names_nodup _)
        (fun q hq hreq al => ih q (Ty.mem_canon hq)
          (by
            have hq' := h q hq
            rw [hreq, Bool.false_or] at hq'
            exact hq') al)
        allocated
    exact ⟨.ctor 0 [.list ns, .list xs], al', ext, .step rfl hps hall⟩

/-- **The iteration keeps its invariant**: every name it adds has a witnessed declaration. -/
theorem witnessed_inhabitedNames (decls : TyDecls) : decls.Witnessed decls.inhabitedNames := by
  refine decls.saturate_inv decls.inhabitedHolds
    (R := fun name => ∀ body, decls.body? name = some body → ∀ allocated : List String,
      ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
        MemberIn decls allocated' v body)
    ?_ [] (fun _ hn => absurd hn List.not_mem_nil)
  intro known hk name hh body hb
  unfold TyDecls.inhabitedHolds at hh
  rw [hb] at hh
  exact exists_memberIn_fresh hk body hh

/-- **Inhabitance is complete against membership under the table**: an inhabited type has a
member at some allocation table. Placement: concept `store-typing`, R3, a step of the claim
`recursive-types-inhabited`, from `exists_memberIn_fresh` and the round invariant. Consumer: `inhabited_iff_memberIn`. It establishes nothing of a world
(`Fits`). -/
@[semantics "store-typing" (requirement := R3)]
theorem exists_memberIn_of_inhabited {decls : TyDecls} {t : Ty}
    (h : decls.inhabited t = true) :
    ∃ (v : Val) (allocated : List String), MemberIn decls allocated v t :=
  have ⟨v, allocated, _, hv⟩ := exists_memberIn_fresh (witnessed_inhabitedNames decls) t h []
  ⟨v, allocated, hv⟩

/-- **Inhabitance agrees with membership under the table** (claim `recursive-types-inhabited`):
the least fixed point over the table says `true` exactly where some value is a member. The
soundness half is proved (`inhabited_of_memberIn`); the completeness half is
`exists_memberIn_of_inhabited`. -/
@[semantics "store-typing" (requirement := R3)]
theorem inhabited_iff_memberIn {decls : TyDecls} {t : Ty} :
    decls.inhabited t = true ↔ ∃ (v : Val) (allocated : List String), MemberIn decls allocated v t :=
  ⟨exists_memberIn_of_inhabited, fun ⟨_, _, h⟩ => inhabited_of_memberIn h⟩

end Effect4.Program
