import Effect4.Laws.Codegen.Services

/-! Probe: the profiled service check is a conjunction. The target's check holds exactly when
the domain's formation holds and the target's naming conditions hold. Codex proved one
direction (`serviceFaultIn_anyName`); the conjunction is the statement that says what the
profile parameterisation means. -/

set_option autoImplicit false
namespace Probe
open Effect4 Effect4.Program

/-- TypeScript's naming conditions on a block's services, beside role formation. -/
def tsNames (defs : List DefDecl) : Prop :=
  tsProfile.defNameFault defs = none ∧
  repeatOf ((servicesOf defs).flatMap fun sv => tsProfile.serviceConsts sv.name) = none ∧
  ∀ sv ∈ servicesOf defs,
    sv.methods.any (fun x => !plainMethodName x.1) = false ∧
    tsProfile.collides defs sv.name = false

theorem any_not_anyName (methods : List (String × Nat × Nat)) :
    methods.any (fun x => !anyName.method x.1) = false := by
  rw [List.any_eq_false]
  intro x _ hx
  simp only [anyName, Bool.not_true, Bool.false_eq_true] at hx

/-- One service: the target's check is formation and the two naming conditions. -/
theorem serviceFaultOfIn_tsProfile_iff (defs : List DefDecl) (sv : Service) :
    serviceFaultOfIn tsProfile defs sv = none ↔
      serviceFaultOfIn anyName defs sv = none ∧
        sv.methods.any (fun x => !plainMethodName x.1) = false ∧
        tsProfile.collides defs sv.name = false := by
  unfold serviceFaultOfIn
  cases hinit : defs[sv.init]? with
  | none => simp
  | some init =>
    dsimp only
    cases hreq : (init.request ≠ .unit || !init.params.isEmpty) with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [any_not_anyName]
      show _ ↔ (if (!(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty || false) = true then _
        else if false = true then _ else _) = none ∧ _
      simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      cases hshape : (!(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty) with
      | true => simp
      | false =>
        simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        rw [show tsProfile.method = plainMethodName from rfl]
        cases hplain : sv.methods.any (fun x => !plainMethodName x.1) with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hcoll : tsProfile.collides defs sv.name with
          | true => simp
          | false => simp

/-- A block: the target's check is formation and the naming conditions, whatever the order
the printer reports its refusals in. -/
theorem serviceFaultIn_tsProfile_iff (defs : List DefDecl) :
    serviceFaultIn tsProfile defs = none ↔ serviceFaultIn anyName defs = none ∧ tsNames defs := by
  unfold serviceFaultIn tsNames
  cases hdef : tsProfile.defNameFault defs with
  | some n => simp
  | none =>
    dsimp only
    show _ ↔ (match (none : Option String) with
      | some n => some (PrintRefusal.serviceName n)
      | none => match repeatOf ((servicesOf defs).flatMap fun sv => anyName.serviceConsts sv.name) with
        | some n => some (.serviceName n)
        | none => match strayOf ((servicesOf defs).map (·.name)) defs with
          | some why => some why
          | none => (servicesOf defs).findSome? (serviceFaultOfIn anyName defs)) = none ∧ _
    dsimp only
    cases hts : repeatOf ((servicesOf defs).flatMap fun sv => tsProfile.serviceConsts sv.name) with
    | some n => simp
    | none =>
      dsimp only
      have hdom : repeatOf ((servicesOf defs).flatMap fun sv => anyName.serviceConsts sv.name) =
          none :=
        (repeatOf_eq_none_iff _).mpr ((names_sublist _).nodup ((repeatOf_eq_none_iff _).mp hts))
      rw [hdom]
      dsimp only
      cases hstray : strayOf ((servicesOf defs).map (·.name)) defs with
      | some why => simp
      | none =>
        dsimp only
        simp only [List.findSome?_eq_none_iff, true_and]
        constructor
        · intro h
          refine ⟨fun sv hsv => ((serviceFaultOfIn_tsProfile_iff defs sv).mp (h sv hsv)).1,
            fun sv hsv => ((serviceFaultOfIn_tsProfile_iff defs sv).mp (h sv hsv)).2⟩
        · rintro ⟨hform, hnames⟩ sv hsv
          exact (serviceFaultOfIn_tsProfile_iff defs sv).mpr ⟨hform sv hsv, hnames sv hsv⟩

end Probe
