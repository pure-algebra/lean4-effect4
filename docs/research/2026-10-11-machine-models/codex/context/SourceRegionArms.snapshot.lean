import Effect4.Laws.Program.Typed.Denotation.Terms
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects
variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}
def BoundFits (w : World) : Option Val → List Ty → Prop
  | none, [] => True
  | some x, [ty] => Fits w x ty
  | _, _ => False

/-- **A typed scrutinee decides** (proved): the membership form of `Decision.decide_typed`
(`Laws/Program/Decision.lean`). A tag hit's payload fits the payload type (`fits_tagPayload`); a
miss is a member of the residual (`Ty.diffTag`), since a tagged member it fit would make it a hit
(`Ty.hasTy_of_not_tagged`). -/
theorem decide_fits {w : World} {d : Decision} {t : Ty} {e0 e1 : List Ty} {v : Val}
    (harms : d.arms t = some (e0, e1)) (hv : Fits w v t) :
    ∃ first bound, d.decide v = some (first, bound) ∧
      BoundFits w bound (if first then e0 else e1) := by
  cases d with
  | bool =>
    simp only [Decision.arms] at harms
    split at harms
    · rename_i ht
      simp only [Option.some.injEq, Prod.mk.injEq] at harms
      obtain ⟨rfl, rfl⟩ := harms
      obtain ⟨b, rfl⟩ := fits_bool_inv (fits_subN w (b := .bool) ht v hv)
      exact ⟨b, none, rfl, by cases b <;> trivial⟩
    · exact nomatch harms
  | option =>
    simp only [Decision.arms] at harms
    obtain ⟨a, hopt, heq⟩ := Option.map_eq_some_iff.mp harms
    cases heq
    have hv' := fits_subN w (optionTy_upper hopt) v hv
    rcases fits_option_inv hv' with rfl | ⟨x, rfl, hx⟩
    · exact ⟨true, none, rfl, trivial⟩
    · exact ⟨false, some x, rfl, hx⟩
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
        obtain ⟨rfl, rfl⟩ := harms
        have hvc : Fits w v t.normalize := (fits_normalize w t v).mpr hv
        cases hp : Val.tagPayload? name v with
        | some payload =>
          exact ⟨true, some payload, by simp only [Decision.decide, hp],
            fits_tagPayload hcol hvc hp hP⟩
        | none =>
          refine ⟨false, some v, by simp only [Decision.decide, hp], ?_⟩
          show Fits w v (Ty.diffTag name t.normalize)
          obtain ⟨m, hm, hvm⟩ := (fits_members w v _).mpr hvc
          unfold Ty.diffTag
          rw [fits_ofMembers]
          refine ⟨m, List.mem_filter.mpr ⟨hm, ?_⟩, hvm⟩
          cases htag : Ty.isTagged name m
          · rfl
          · have hsome := Ty.tagPayload_of_tagged name m v _ htag (fits_hasTy w m v hvm)
            rw [hp] at hsome
            exact nomatch hsome
    · exact nomatch harms

  | recordTag name =>
    obtain ⟨⟨hit, miss⟩, hparts, heq⟩ := Option.map_eq_some_iff.mp harms
    cases heq
    refine ⟨Record.tagHit name v, some v, rfl, ?_⟩
    simp only [Record.tagArms] at hparts
    split at hparts
    · next hcolumn =>
      cases hparts
      have hn := (fits_normalize w t v).mpr hv
      obtain ⟨branch, hmember, hbranch⟩ := (fits_members w v t.normalize).mpr hn
      have htag := Record.tagHit_eq_isTag name
        (List.all_eq_true.mp hcolumn branch hmember) (fits_hasTy w branch v hbranch)
      cases hb : Record.tagHit name v with
      | false =>
        change Fits w v (Ty.ofMembers _)
        apply (fits_ofMembers w v _).mpr
        exact ⟨branch, List.mem_filter.mpr ⟨hmember, by rw [← htag, hb]; rfl⟩, hbranch⟩
      | true =>
        change Fits w v (Ty.ofMembers _)
        apply (fits_ofMembers w v _).mpr
        exact ⟨branch, List.mem_filter.mpr ⟨hmember, htag ▸ hb⟩, hbranch⟩
    · exact nomatch hparts

theorem childBind_path (q : Point) (i : Nat) (b : Option Val) :
    (q.childBind i b).path = q.path ++ [i] := by
  cases b <;> rfl

theorem childBind_env (q : Point) (i : Nat) (b : Option Val) :
    (q.childBind i b).env = q.env ++ b.toList := by
  cases b with
  | none => exact (List.append_nil _).symm
  | some v => rfl

theorem childBind_completed (q : Point) (i : Nat) (b : Option Val) :
    (q.childBind i b).completed = q.completed := by
  cases b <;> rfl

theorem childBind_params (q : Point) (i : Nat) (b : Option Val) :
    (q.childBind i b).params = q.params := by
  cases b <;> rfl

/-- The environment a decision's chosen arm runs in is typed at the arm's extension. -/
theorem envTyped_bound {w : World} {env : List Ty} {vals : List Val} {extra : List Ty}
    {b : Option Val} (h : EnvTyped w env vals) (hb : BoundFits w b extra) :
    EnvTyped w (env ++ extra) (vals ++ b.toList) := by
  cases b with
  | none =>
    cases extra with
    | nil =>
      simp only [List.append_nil, Option.toList]
      exact h
    | cons _ _ => exact (hb : False).elim
  | some x =>
    cases extra with
    | nil => exact (hb : False).elim
    | cons t rest =>
      cases rest with
      | nil => exact envTyped_append h hb
      | cons _ _ => exact (hb : False).elim

theorem denoteAction_of (root : NativeEff) (p : Point) {a : NAction}
    (hact : actionAt root p = some a) : denoteAction root p = denoteFiberAction root p a := by
  unfold denoteAction
  rw [hact]

theorem suspend_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.suspend b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0]))
    (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.suspend b) p) := by
  obtain ⟨env, hcheck, henv, _, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_suspend] at hcheck
  have hcb := Checker.inv_suspend _ _ _ _ _ hcheck
  rw [denoteR_suspend _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_suspendR_typed root (Row.subset_refl _) (fun w' o =>
    ambient_constructR_typed root (Row.subset_refl _) (fun w'' o' completed hc => ?_))
  have o'' := leHost_trans _ _ _ o o'
  exact hb w'' (serviceTy_leHost o'' htie) ({ p with completed }.child 0) ty
    (child_fuel_eq (p := { p with completed }) hfuel 0) rfl
    (pointTyped_child (q := { p with completed }.child 0) hat rfl rfl hcb (envTyped_mono o'' henv) hc (stackTyped_mono o'' hstack)) available coverage

/-- **`select`**: the counted step, the scrutinee decides (`decide_fits`), and the chosen arm runs
at its point with the value it binds, widened to the join of the arms. -/
theorem select_arm {available : Env.Requirement} {s : Term} {d : Decision} {a0 a1 : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.select s d a0 a1)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (h0 : ChildDenotes root f a0 (p.path ++ [0])) (h1 : ChildDenotes root f a1 (p.path ++ [1]))
    (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.select s d a0 a1) p) := by
  obtain ⟨env, hcheck, henv, _, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_select] at hcheck
  obtain ⟨sty, ⟨e0, e1⟩, t0, t1, hsty, harms, hc0, hc1, rfl⟩ :=
    Checker.inv_select _ _ _ _ _ _ _ _ hcheck
  have required0 : Row.Subset t0.requires available :=
    Row.subset_trans (Row.subset_union_left _ _) coverage
  have required1 : Row.Subset t1.requires available :=
    Row.subset_trans (Row.subset_union_right _ _) coverage
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hsty
  rw [denoteR_select _ _ _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_suspendR_typed root (Row.subset_refl _) (fun w' o =>
    ambient_constructR_typed root (Row.subset_refl _) (fun w'' o' completed hc => ?_))
  have o'' := leHost_trans _ _ _ o o'
  have htie'' := serviceTy_leHost o'' htie
  obtain ⟨first, bound, hdec, hbound⟩ := decide_fits harms (fits_mono o'' hfit)
  show AmbientProg root w'' available
    ((⟨t0.answer.join t1.answer, t0.error.join t1.error, Row.union t0.requires t1.requires⟩ : EffTy),
      available, available) (match (evalTerm p.env s).bind d.decide with
    | some (true, bound) => denoteR root.program a0 ({ p with completed }.childBind 0 bound)
    | some (false, bound) => denoteR root.program a1 ({ p with completed }.childBind 1 bound)
    | none => .pure badShapeExit)
  rw [hv, Option.bind_some, hdec]
  cases first with
  | true =>
    refine ambientProg_widen root (before := (t0, available, available))
      (Ty.subN_join_left _ _) (Ty.subN_join_left _ _) (Row.subset_refl _) (Row.subset_refl _) ?_
    refine h0 w'' htie'' ({ p with completed }.childBind 0 bound) t0 (by rw [Point.childBind_fuel]; rw [hfuel]; rfl)
      (childBind_path { p with completed } 0 bound) ?_ available required0
    refine pointTyped_child (q := { p with completed }.childBind 0 bound) hat rfl
      (childBind_path { p with completed } 0 bound) hc0 ?_
      (by rw [childBind_completed]; exact hc)
      (by rw [childBind_params]; exact stackTyped_mono o'' hstack)
    rw [childBind_env]
    exact envTyped_bound (envTyped_mono o'' henv) hbound
  | false =>
    refine ambientProg_widen root (before := (t1, available, available))
      (Ty.subN_join_right _ _) (Ty.subN_join_right _ _) (Row.subset_refl _) (Row.subset_refl _) ?_
    refine h1 w'' htie'' ({ p with completed }.childBind 1 bound) t1 (by rw [Point.childBind_fuel]; rw [hfuel]; rfl)
      (childBind_path { p with completed } 1 bound) ?_ available required1
    refine pointTyped_child (q := { p with completed }.childBind 1 bound) hat rfl
      (childBind_path { p with completed } 1 bound) hc1 ?_
      (by rw [childBind_completed]; exact hc)
      (by rw [childBind_params]; exact stackTyped_mono o'' hstack)
    rw [childBind_env]
    exact envTyped_bound (envTyped_mono o'' henv) hbound

theorem scoped_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.scoped b)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.scoped b) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_scoped] at hcheck
  obtain ⟨tb, hcb, rfl⟩ := Checker.inv_scoped _ _ _ _ _ hcheck
  rw [denoteR_scoped _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  exact ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) tb ⟨pointTyped_child hat rfl rfl hcb henv hview hstack, by
      rw [← (root.scopeSig_extends p.path).bodyRequires]
      exact coverage⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ (Row.subset_refl _)) (Row.subset_refl _)

/-- **`gen`**: the counted step, then the generator entry at the point itself, whose row the
point's typing and its generator node meet. -/
theorem gen_arm {available : Env.Requirement} {body : Stmts NativeOp} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.gen body)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.gen body) p) := by
  rw [denoteR_gen _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  unfold suspendR
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun later ordered _ _ => ?_) (Row.subset_refl _)
  exact .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty ⟨⟨pointTyped_mono ordered hpt, body, hat⟩, coverage⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ (Row.subset_refl _)) (Row.subset_refl _)

/-- **`iterate`**: the counted step, the initial cursor (`evalTerm_progress_env`), then the loop
entry at the point itself, its cursor at the loop's checked cursor type (`LoopPointTyped`,
decisions row 190 (b)): the initial term's type is below it (`Checker.inv_iterate`). -/
theorem iterate_arm {available : Env.Requirement} {cursorTy : Option Ty} {initial test step result : Term} {body : NativeEff}
    (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.iterate cursorTy initial test step result body)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.iterate cursorTy initial test step result body) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  have checked := hcheck
  rw [Eff.expandIn_iterate] at hcheck
  obtain ⟨c0, _, _, _, _, hc0, _, _, _, _, _, hsub0, _, _⟩ := Checker.inv_iterate _ _ _ _ _ _ _ _ _ _ hcheck
  obtain ⟨cursor, hcursor, hfit⟩ := evalTerm_progress_env henv hc0
  have pre : LoopPointTyped root w p ty cursor := ⟨cursorTy, initial, test, step, result, body, env,
    c0, hat, checked, henv, hview, ((root.scopeSig_extends p.path).termTy env initial).symm.trans hc0,
    fits_subN w (a := c0) (b := cursorTy.getD c0) hsub0 cursor hfit, hstack⟩
  rw [denoteR_iterate _ _ _ _ _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f), hcursor]
  unfold suspendR
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun later ordered _ _ => ?_) (Row.subset_refl _)
  exact .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty ⟨loopPointTyped_mono ordered pre, coverage⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ (Row.subset_refl _)) (Row.subset_refl _)

/-- **`uninterruptible`**: the mask row over the body at the child, at the body's type. -/
theorem uninterruptible_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.uninterruptible b)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.uninterruptible b) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_uninterruptible] at hcheck
  have hcb := Checker.inv_uninterruptible _ _ _ _ _ hcheck
  have hact : actionAt root.program p =
      some (WithFiberAction.setInterruptible (resolve root.program (p.child 0)) false) := by
    unfold actionAt
    rw [hat]
  rw [denoteR_uninterruptible _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f),
    denoteAction_of _ _ hact]
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty
    ⟨BodyTyped.at_ _ _ (pointTyped_child hat rfl rfl hcb henv hview hstack), coverage, ?_, ?_⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ (Row.subset_refl _)) (Row.subset_refl _)
  · intro point ctx same
    cases same
  · intro point previous same
    cases same

/-- **`interruptible`**: as `uninterruptible`, with the flag set. -/
theorem interruptible_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.interruptible b)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.interruptible b) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_interruptible] at hcheck
  have hcb := Checker.inv_interruptible _ _ _ _ _ hcheck
  have hact : actionAt root.program p =
      some (WithFiberAction.setInterruptible (resolve root.program (p.child 0)) true) := by
    unfold actionAt
    rw [hat]
  rw [denoteR_interruptible _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f),
    denoteAction_of _ _ hact]
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty
    ⟨BodyTyped.at_ _ _ (pointTyped_child hat rfl rfl hcb henv hview hstack), coverage, ?_, ?_⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ (Row.subset_refl _)) (Row.subset_refl _)
  · intro point ctx same
    cases same
  · intro point previous same
    cases same

theorem fits_exitErr_causeOf {w : World} {e : Ty} {c : CauseV} (h : FitsCause w e c) :
    Fits w (Val.exitErr c) (.causeOf e) := by
  show (match Val.cause? (Val.exitErr c) with
    | some c' => CauseFits (fun x => Fits w x e) c'
    | none => False)
  rw [Val.cause?_exitErr]
  exact h

theorem catchCause_arm {available : Env.Requirement} {b h : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.catchCause b h)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hh : ChildDenotes root f h (p.path ++ [1]))
    (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.catchCause b h) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_catchCause] at hcheck
  obtain ⟨tb, th, hcb, hch, rfl⟩ := Checker.inv_catchCause _ _ _ _ _ _ hcheck
  have bodyCovered := Row.subset_trans (Row.subset_union_left tb.requires th.requires) coverage
  have handlerCovered := Row.subset_trans (Row.subset_union_right tb.requires th.requires) coverage
  rw [denoteR_catchCause _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_guardBind root
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview hstack) available bodyCovered)
    (fun later ordered exit present payload => ?_) (fun later ordered exit payload absent => ?_)
    (Row.subset_refl _)
  · cases exit with
    | success value => exact Bool.noConfusion present
    | failure cause =>
      refine ambient_constructR_typed root (Row.subset_refl _) (fun after grew completed completedTyped => ?_)
      have future := leHost_trans _ _ _ ordered grew
      have causeFit : FitsCause after tb.error cause :=
        fitsExit_failure_cause (strongExit_mono _ _ _ _ grew payload.1).1
      refine ambientProg_widen root (before := (th, available, available))
        (after := ((⟨tb.answer.join th.answer, th.error, Row.union tb.requires th.requires⟩ : EffTy),
          available, available))
        (Ty.subN_join_right _ _) (Ty.subN_refl _) (Row.subset_refl _) (Row.subset_refl _) ?_
      exact hh after (serviceTy_leHost future htie) ({ p with completed }.childWith 1 (Val.exitErr cause)) th
        (childWith_fuel_eq (p := { p with completed }) hfuel 1 (Val.exitErr cause)) rfl
        (pointTyped_child (q := { p with completed }.childWith 1 (Val.exitErr cause)) hat rfl rfl hch
          (envTyped_append (envTyped_mono future henv) (fits_exitErr_causeOf causeFit))
          completedTyped (stackTyped_mono future hstack)) available handlerCovered
  · cases exit with
    | failure cause => exact Bool.noConfusion absent
    | success value =>
      exact ⟨exitOk_success_of_answerN (Ty.subN_join_left _ _) payload.1, payload.2⟩


end Effect4.Program.Typed
