import Effect4.Laws.Program.Typed.Denotation.Arguments

/-!
M5's remaining source arms consume the shared term and bind declarations.
The context migration retains the closed-row load claims of decisions row 117.
The ambient entry protocol carries the actual available service row, decisions row 349.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects


/-! ## The definition block (decisions row 328)

A block stands at the root of the program. Its bodies are child `0`, a spine whose head is child
`0` and rest child `1`, so the body of definition `k` stands at `defBodyPath`'s path; the main
program is child `1`. The checker's verdict on the whole program, a module check
(`typeOfProgram`), types each body and the main program at the source's signature, which is the
tables' signature extended by the block (`ProgramSource.signature`). -/

/-- The body of definition `k` at its path in the bodies' spine. A step of
`bodiesTyped_of_typeOf`. -/
theorem Node.at_effs_body : ∀ (bodies : Effs NativeOp) (k : Nat),
    Node.at_ (.effs bodies) (List.replicate k 1 ++ [0]) = (bodies.toList[k]?).map Node.eff
  | .nil, 0 => rfl
  | .nil, _ + 1 => rfl
  | .cons _ _, 0 => rfl
  | .cons _ t, k + 1 => Node.at_effs_body t k

/-- The source's signature for a program with a block: the tables' signature extended by it. -/
theorem ProgramSource.signature_defs {root : ProgramSource} {decls : List DefDecl}
    {bodies : Effs NativeOp} {main : NativeEff} {layers : LayerTerms NativeOp}
    (hprog : root.program = .defs decls bodies main layers) :
    root.signature = root.sig.signature.withDefs decls := by
  show root.sig.signature.withDefs root.program.defsOf = _
  rw [hprog]
  rfl

/-- The module judgment of a checked block, at the source's signature: the checker's verdict on
the whole program is the module check of its expansion (`typeOfProgram`), and the expansion keeps
the block (`Eff.expandIn_defs`). A step of `bodiesTyped_of_typeOf` and `mainChecked_of_typeOf`. -/
theorem moduleHasTy_of_typeOf {root : ProgramSource} {rootTy : EffTy} {decls : List DefDecl}
    {bodies : Effs NativeOp} {main : NativeEff} {layers : LayerTerms NativeOp}
    (hprog : root.program = .defs decls bodies main layers)
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy) :
    ∃ bodies' : Effs NativeOp,
      (∀ k : Nat, bodies'.toList[k]? = (bodies.toList[k]?).map (Eff.expandIn root.program)) ∧
      BodiesHasTy root.signature decls bodies' ∧
      Conform.Effect4.Typing.HasTy root.signature [] (Eff.expandIn root.program main) rootTy ∧
      LayersTyped root.signature (LayerTerms.expandIn root.program layers) := by
  have wf : root.program.layerRefsWF = true := by
    have c := checked
    unfold Program.typeOfProgram at c
    split at c
    · assumption
    · cases c
  obtain ⟨bodies', hexp, hget⟩ := Eff.expandIn_defs root.program decls bodies main layers
  have hexpand : root.program.expandRefs =
      .defs decls bodies' (Eff.expandIn root.program main) (LayerTerms.expandIn root.program layers) := by
    rw [← Eff.expandIn_self, ← hexp, ← hprog]
  rw [typeOfProgram_eq_if_refsWF, if_pos wf, hexpand] at checked
  have hm := checkModule_sound _ _ _ (Effect4.Laws.Auto.toOption_eq_some.mp checked)
  rw [ProgramSource.signature_defs hprog]
  cases hm with
  | defs hb hmain hl => exact ⟨bodies', hget, hb, hmain, hl⟩
  | plain hd => cases hd

/-- **The block's bodies are typed**, from the checker's verdict on the whole program (decisions
row 328): `BodiesTyped`, M5's premise for the invocation's arm, discharged at the load as the
references' formation is. A program with no block has no declaration. -/
theorem bodiesTyped_of_typeOf {root : ProgramSource} {rootTy : EffTy}
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy) :
    BodiesTyped root := by
  intro k d hd
  have hcases : (∃ decls bodies main layers, root.program = .defs decls bodies main layers) ∨
      root.program.defsOf = [] := by
    cases root.program with
    | defs decls bodies main layers => exact .inl ⟨decls, bodies, main, layers, rfl⟩
    | _ => exact .inr rfl
  rcases hcases with ⟨decls, bodies, main, layers, hprog⟩ | hnil
  · rw [hprog] at hd
    obtain ⟨bodies', hget, hb, -, -⟩ := moduleHasTy_of_typeOf hprog checked
    obtain ⟨body', tb, hbody', htyped, hformed, hadmits⟩ := hb.get hd
    rw [hget k] at hbody'
    obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hbody'
    have hlt : k < bodies.toList.length := (List.getElem?_eq_some_iff.mp hbody).1
    refine ⟨0 :: List.replicate k 1 ++ [0], body, tb, ?_, ?_,
      Conform.Effect4.Typing.check_complete _ _ _ _ htyped _, hformed, hadmits⟩
    · rw [hprog]
      exact if_pos hlt
    · rw [hprog]
      show Node.at_ (.effs bodies) (List.replicate k 1 ++ [0]) = _
      rw [Node.at_effs_body, hbody]
      rfl
  · rw [hnil, List.getElem?_nil] at hd
    cases hd

/-- A whole layer of a typed spine is typed, read through the expansion: the head at `[0]`, and
the rest's layers below `1`. A step of `moduleLayersTyped_of_typeOf`. -/
theorem layersTyped_at {sig : Signature NativeOp} {P : NativeEff} :
    ∀ (t : List Nat) (ls : LayerTerms NativeOp) (l : LayerTerm NativeOp),
      Path.spineHead t = true → Node.at_ (.layers ls) t = some (.layer l) →
      LayersTyped sig (LayerTerms.expandIn P ls) →
        ∃ lt, Conform.Effect4.Typing.LayerHasTy sig (LayerTerm.expandIn P l) lt
  | [0], .cons _ _, _, _, hat, hT => by
    cases hat
    rw [LayerTerms.expandIn_cons] at hT
    cases hT with
    | cons hh _ => exact ⟨_, hh⟩
  | [0], .nil, _, _, hat, _ => by cases hat
  | 1 :: r, .cons _ tl, l, hs, hat, hT => by
    rw [LayerTerms.expandIn_cons] at hT
    cases hT with
    | cons _ ht => exact layersTyped_at r tl l hs hat ht
  | 1 :: _, .nil, _, _, hat, _ => by cases hat
  | [], _, _, hs, _, _ => by cases hs
  | 0 :: _ :: _, _, _, hs, _, _ => by cases hs
  | (_ + 2) :: _, _, _, hs, _, _ => by cases hs

/-- **The module's layers are typed**, from the checker's verdict on the whole program (decisions
row 341, step 2): `ModuleLayersTyped`, M5's premise for a reference into the module, discharged at
the load as the bodies are. A path in the module's layers stands in a block. -/
theorem moduleLayersTyped_of_typeOf {root : ProgramSource} {rootTy : EffTy}
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy) :
    ModuleLayersTyped root := by
  intro target l hin hhead hl
  have hblock : ∃ decls bodies main layers, root.program = .defs decls bodies main layers := by
    unfold Eff.inModule at hin
    split at hin
    · rename_i decls bodies main layers hprog
      exact ⟨decls, bodies, main, layers, hprog⟩
    · cases hin
  obtain ⟨decls, bodies, main, layers, hprog⟩ := hblock
  obtain ⟨-, -, -, -, hlayers⟩ := moduleHasTy_of_typeOf hprog checked
  have hh := Eff.inModule_head hin
  cases target with
  | nil => cases hh
  | cons x t =>
    cases hh
    have hat : Node.at_ (.layers layers) t = some (.layer l) := by
      have h0 := Node.at_of_layerAt hl
      rw [hprog] at h0
      exact h0
    obtain ⟨lt, hty⟩ := layersTyped_at t layers l hhead hat hlayers
    exact ⟨lt, Conform.Effect4.Typing.checkLayer_complete _ _ _ hty _⟩

/-- **The main program of a checked block is checked** at the source's signature, at the
whole program's type, at its path. The load's start (`rootCode_typed`) reads it: a block has no
step of its own, and the run goes on at its main program (`denoteR_defs`). -/
theorem mainChecked_of_typeOf {root : ProgramSource} {rootTy : EffTy} {decls : List DefDecl}
    {bodies : Effs NativeOp} {main : NativeEff} {layers : LayerTerms NativeOp}
    (hprog : root.program = .defs decls bodies main layers)
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy) :
    Checker.check root.signature [] [1] (Eff.expandIn root.program main) = .ok rootTy := by
  obtain ⟨-, -, -, hmain, -⟩ := moduleHasTy_of_typeOf hprog checked
  exact Conform.Effect4.Typing.check_complete _ _ _ _ hmain _

/-! ## Arms: `bind`, `select` and the scoped shapes

An arm reads the induction through its children only: a child's denotation is typed at every
world `J` ranges over and every point at the child's path with the arm's remaining fuel
(`ChildDenotes`). The continuations a guard runs are typed at later worlds, so a child is used at
the world its point is built at, with the point's environment and view moved there. -/



/-! ### The value-decided fork (`select`) -/

/-- What a decision's chosen arm binds, at the arm's environment extension: nothing against
nothing, one value fitting one type (`Decision.BoundTyped`'s membership form). -/
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

section ScopedArms2

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`suspend`**: the counted step, then the body constructed with the view at its invocation. -/
theorem suspend_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.suspend b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0]))
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
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
    (ambientStackTyped_child (q := { p with completed }.child 0) hat rfl rfl
      (ambientStackTyped_mono o'' savedParams))

/-- **`select`**: the counted step, the scrutinee decides (`decide_fits`), and the chosen arm runs
at its point with the value it binds, widened to the join of the arms. -/
theorem select_arm {available : Env.Requirement} {s : Term} {d : Decision} {a0 a1 : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.select s d a0 a1)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (h0 : ChildDenotes root f a0 (p.path ++ [0])) (h1 : ChildDenotes root f a1 (p.path ++ [1]))
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
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
      (ambientStackTyped_child (q := { p with completed }.childBind 0 bound) hat
        (childBind_path _ _ _) (childBind_params _ _ _) (ambientStackTyped_mono o'' savedParams))
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
      (ambientStackTyped_child (q := { p with completed }.childBind 1 bound) hat
        (childBind_path _ _ _) (childBind_params _ _ _) (ambientStackTyped_mono o'' savedParams))
    refine pointTyped_child (q := { p with completed }.childBind 1 bound) hat rfl
      (childBind_path { p with completed } 1 bound) hc1 ?_
      (by rw [childBind_completed]; exact hc)
      (by rw [childBind_params]; exact stackTyped_mono o'' hstack)
    rw [childBind_env]
    exact envTyped_bound (envTyped_mono o'' henv) hbound

end ScopedArms2

/-! ### Handlers, regions, masks and loops -/

/-- A caught cause, bound as a value, fits the handler's `Cause<E>` when its failures fit `E`. -/
theorem fits_exitErr_causeOf {w : World} {e : Ty} {c : CauseV} (h : FitsCause w e c) :
    Fits w (Val.exitErr c) (.causeOf e) := by
  show (match Val.cause? (Val.exitErr c) with
    | some c' => CauseFits (fun x => Fits w x e) c'
    | none => False)
  rw [Val.cause?_exitErr]
  exact h

/-- The context read, typed at the context type. -/
theorem getContext_typed (root : ProgramSource) (w : World) :
    TypedProg root w (EffTy.pure Ty.context) (fiberValR .getContext rfl) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.handle Ty.contextTarget) rfl
    (fun w' _ ans post => .pure (strongExit_success w' _ ans post))

/-- The denotation at a node the fiber action table resolves: `denoteAction` at that action. -/
theorem denoteAction_of (root : NativeEff) (p : Point) {a : NAction}
    (hact : actionAt root p = some a) : denoteAction root p = denoteFiberAction root p a := by
  unfold denoteAction
  rw [hact]

section ScopedArms3

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`catchCause`**: the `onFailure` shape (`catchGuard_typed`): the handler at every failure the
body admits, the caught cause bound at `Cause<E>`, widened to the join of the answers. -/
theorem catchCause_arm {available : Env.Requirement} {b h : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.catchCause b h)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hh : ChildDenotes root f h (p.path ++ [1]))
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.catchCause b h) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_catchCause] at hcheck
  obtain ⟨tb, th, hcb, hch, rfl⟩ := Checker.inv_catchCause _ _ _ _ _ _ hcheck
  have bodyCovered := Row.subset_trans (Row.subset_union_left tb.requires th.requires) coverage
  have handlerCovered := Row.subset_trans (Row.subset_union_right tb.requires th.requires) coverage
  rw [denoteR_catchCause _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_guardBind root
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview hstack) available bodyCovered
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl savedParams))
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
          (ambientStackTyped_child hat rfl rfl (ambientStackTyped_mono future savedParams))
  · cases exit with
    | failure cause => exact Bool.noConfusion absent
    | success value =>
      exact ⟨exitOk_success_of_answerN (Ty.subN_join_left _ _) payload.1, payload.2⟩

/-- **`matchCause`**: the `all` shape (`allGuard_typed`): the value arm on a success, the cause
arm on a failure, each widened to the join. -/
theorem matchCause_arm {available : Env.Requirement} {b v c : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.matchCause b v c)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (coverage : Row.Subset ty.requires available)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hv : ChildDenotes root f v (p.path ++ [1]))
    (hc : ChildDenotes root f c (p.path ++ [2]))
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.matchCause b v c) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_matchCause] at hcheck
  obtain ⟨tb, tv, tc, hcb, hcv, hcc, rfl⟩ := Checker.inv_matchCause _ _ _ _ _ _ _ hcheck
  have frontCovered := Row.subset_trans (Row.subset_union_left (Row.union tb.requires tv.requires) tc.requires) coverage
  have bodyCovered := Row.subset_trans (Row.subset_union_left tb.requires tv.requires) frontCovered
  have valueCovered := Row.subset_trans (Row.subset_union_right tb.requires tv.requires) frontCovered
  have causeCovered := Row.subset_trans (Row.subset_union_right (Row.union tb.requires tv.requires) tc.requires) coverage
  rw [denoteR_matchCause _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_guardBind root
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview hstack) available bodyCovered
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl savedParams))
    (fun later ordered exit _ payload => ?_)
    (fun _ _ exit _ absent => by cases exit <;> exact Bool.noConfusion absent) (Row.subset_refl _)
  cases exit with
  | success value =>
    refine ambient_constructR_typed root (Row.subset_refl _) (fun after grew completed completedTyped => ?_)
    have future := leHost_trans _ _ _ ordered grew
    refine ambientProg_widen root (before := (tv, available, available))
      (after := ((⟨tv.answer.join tc.answer, tv.error.join tc.error,
        Row.union (Row.union tb.requires tv.requires) tc.requires⟩ : EffTy), available, available))
      (Ty.subN_join_left _ _) (Ty.subN_join_left _ _) (Row.subset_refl _) (Row.subset_refl _) ?_
    exact hv after (serviceTy_leHost future htie) ({ p with completed }.childWith 1 value) tv
      (childWith_fuel_eq (p := { p with completed }) hfuel 1 value) rfl
      (pointTyped_child (q := { p with completed }.childWith 1 value) hat rfl rfl hcv
        (envTyped_append (envTyped_mono future henv) (fits_mono grew ((fitsExit_success_iff later tb value).mp payload.1.1)))
        completedTyped (stackTyped_mono future hstack)) available valueCovered
      (ambientStackTyped_child hat rfl rfl (ambientStackTyped_mono future savedParams))
  | failure cause =>
    refine ambient_constructR_typed root (Row.subset_refl _) (fun after grew completed completedTyped => ?_)
    have future := leHost_trans _ _ _ ordered grew
    refine ambientProg_widen root (before := (tc, available, available))
      (after := ((⟨tv.answer.join tc.answer, tv.error.join tc.error,
        Row.union (Row.union tb.requires tv.requires) tc.requires⟩ : EffTy), available, available))
      (Ty.subN_join_right _ _) (Ty.subN_join_right _ _) (Row.subset_refl _) (Row.subset_refl _) ?_
    exact hc after (serviceTy_leHost future htie) ({ p with completed }.childWith 2 (Val.exitErr cause)) tc
      (childWith_fuel_eq (p := { p with completed }) hfuel 2 (Val.exitErr cause)) rfl
      (pointTyped_child (q := { p with completed }.childWith 2 (Val.exitErr cause)) hat rfl rfl hcc
        (envTyped_append (envTyped_mono future henv)
          (fits_exitErr_causeOf (fitsExit_failure_cause (strongExit_mono _ _ _ _ grew payload.1).1)))
        completedTyped (stackTyped_mono future hstack)) available causeCovered
      (ambientStackTyped_child hat rfl rfl (ambientStackTyped_mono future savedParams))

/-- **`onExit`**: the region (`onExit_typed`): the body at its type, the finalizer on every exit
the body admits, the exit bound as `Exit<A, E>`. -/
theorem onExit_arm {available : Env.Requirement} {b fin : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.onExit b fin)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (coverage : Row.Subset ty.requires available)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hf : ChildDenotes root f fin (p.path ++ [1]))
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.onExit b fin) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_onExit] at hcheck
  obtain ⟨tb, tf, hcb, hcf, rfl⟩ := Checker.inv_onExit _ _ _ _ _ _ hcheck
  have bodyCovered := Row.subset_trans (Row.subset_union_left tb.requires tf.requires) coverage
  have finalizerCovered := Row.subset_trans (Row.subset_union_right tb.requires tf.requires) coverage
  rw [denoteR_onExit _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_onExit_typed root (bodyType := tb) (cleanupType := tf)
    (Ty.subN_refl _) (Ty.subN_join_left _ _) (Ty.subN_join_right _ _)
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview hstack) available bodyCovered
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl savedParams))
    (fun later ordered exit payload => ?_)
  refine ambient_constructR_typed root (Row.subset_refl _) (fun after grew completed completedTyped => ?_)
  have future := leHost_trans _ _ _ ordered grew
  exact hf after (serviceTy_leHost future htie) ({ p with completed }.childWith 1 (reifyExitVal exit)) tf
    (childWith_fuel_eq (p := { p with completed }) hfuel 1 (reifyExitVal exit)) rfl
    (pointTyped_child (q := { p with completed }.childWith 1 (reifyExitVal exit)) hat rfl rfl hcf
      (envTyped_append (envTyped_mono future henv) (fitsExit_mono grew payload.1))
      completedTyped (stackTyped_mono future hstack)) available finalizerCovered
    (ambientStackTyped_child hat rfl rfl (ambientStackTyped_mono future savedParams))

/-- **`scoped`**: the scoped region's row, its body the child at the body's type; the exit it
answers is typed at the body's columns, which the region's type keeps. -/
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
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **`gen`**: the counted step, then the generator entry at the point itself, whose row the
point's typing and its generator node meet. -/
theorem gen_arm {available : Env.Requirement} {body : Stmts NativeOp} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.gen body)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.gen body) p) := by
  rw [denoteR_gen _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  unfold suspendR
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun later ordered _ _ => ?_) ⟨Row.subset_refl _, Row.subset_refl _⟩
  exact .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty ⟨⟨pointTyped_mono ordered hpt, body, hat⟩, coverage⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩

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
    (fun _ _ _ h => nomatch h) () trivial (fun later ordered _ _ => ?_) ⟨Row.subset_refl _, Row.subset_refl _⟩
  exact .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty ⟨loopPointTyped_mono ordered pre, coverage⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **`uninterruptible`**: the mask row over the body at the child, at the body's type. -/
theorem uninterruptible_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.uninterruptible b)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
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
    ⟨BodyTyped.at_ _ _ (pointTyped_child hat rfl rfl hcb henv hview hstack), coverage, ?_, ?_,
      (⟨(fun _ impossible => by cases impossible),
        (fun _ _ _ impossible => by cases impossible),
        ⟨(fun point role => by
          rcases role with identity | ⟨ctx, impossible | impossible⟩
          · cases identity
            exact ambientStackTyped_child hat rfl rfl savedParams
          · cases impossible
          · cases impossible), fun _ _ _ impossible => by cases impossible⟩⟩ : BodyCoverage root w available (.at_ (p.child 0)) ty)⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩
  · intro point ctx same
    cases same
  · intro flag point previous impossible
    cases impossible

/-- **`interruptible`**: as `uninterruptible`, with the flag set. -/
theorem interruptible_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.interruptible b)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
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
    ⟨BodyTyped.at_ _ _ (pointTyped_child hat rfl rfl hcb henv hview hstack), coverage, ?_, ?_,
      (⟨(fun _ impossible => by cases impossible),
        (fun _ _ _ impossible => by cases impossible),
        ⟨(fun point role => by
          rcases role with identity | ⟨ctx, impossible | impossible⟩
          · cases identity
            exact ambientStackTyped_child hat rfl rfl savedParams
          · cases impossible
          · cases impossible), fun _ _ _ impossible => by cases impossible⟩⟩ : BodyCoverage root w available (.at_ (p.child 0)) ty)⟩
    (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩
  · intro point ctx same
    cases same
  · intro flag point previous impossible
    cases impossible

/-- **`acquireRelease`**: the context read (`seqGuard_typed`), then the masked acquire at the
point itself (`Body.acquireIn`), whose row is the node's own type; the body names the node and
the context read, whose services fit (`fits_context_inv`). -/
theorem acquireRelease_arm {available : Env.Requirement} {a r : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.acquireRelease a r)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.acquireRelease a r) p) := by
  rw [denoteR_acquireRelease _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_guardBind root (ambient_captureContext_typed root w available)
    (fun later ordered exit arm payload => ?_) (fun later ordered exit payload absent => ?_)
    (Row.subset_refl _)
  · cases exit with
    | failure cause => exact Bool.noConfusion arm
    | success value =>
      obtain ⟨ctx, decoded, members⟩ := fits_context_inv payload.1.1
      have same : value = Val.context ctx := Val.context?_exact decoded
      subst value
      have captured := ambient_captured_context payload
      have bound : Row.Subset available ctx.services.keysRow :=
        (Provision.satisfies_iff_subset_keysRow _ available).mp captured.2
      simp only [seqR, ambientInput, Val.context?_context]
      refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) ty
        ⟨BodyTyped.acquireIn _ _ _ (pointTyped_mono ordered hpt) ⟨a, r, hat⟩ members,
          Row.subset_trans coverage bound, ?_, ?_,
          (⟨(fun _ impossible => by cases impossible),
            (fun _ _ _ impossible => by cases impossible),
            ⟨(fun point role => by
              rcases role with impossible | ⟨context, identity | impossible⟩
              · cases impossible
              · cases identity
                exact ambientStackTyped_widen bound (ambientStackTyped_mono ordered savedParams)
              · cases impossible), fun _ _ _ impossible => by cases impossible⟩⟩ :
            BodyCoverage root later ctx.services.keysRow (.acquireIn p ctx) ty)⟩
        (fun _ _ returned post => .pure ⟨post, by cases returned <;> exact bound⟩ ⟨bound, Row.subset_refl _⟩) ⟨bound, Row.subset_refl _⟩
      · intro point context identity
        cases identity
        exact (Provision.satisfies_iff_subset_keysRow _ _).mpr (Row.subset_refl _)
      · intro flag point previous impossible
        cases impossible
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload.1, Row.subset_refl _⟩

end ScopedArms3

/-! ### The conditional handler (`catchIf`) -/

/-- **A cause with no selected failure has no typed failure** (proved): the first `Fail` of a
cause whose failures are represented is selected, so a cause none is selected from carries only
defects and interruptions and fits every error column (the membership form of
`causeAdmits_of_firstErrorValue_none`, `Laws/Program/Residual.lean`). -/
theorem fitsCause_of_firstErrorValue_none {w : World} {e e' : Ty} {cause : CauseV}
    (hc : FitsCause w e cause) (hnone : firstErrorValue? cause = none) :
    FitsCause w e' cause := by
  intro r hr
  cases r with
  | fail err ann =>
    exfalso
    cases hfirst : firstFailure? cause with
    | none =>
      have hno := List.findSome?_eq_none_iff.mp hfirst (.fail err ann) hr
      exact nomatch hno
    | some error =>
      obtain ⟨reason, hmem, hreason⟩ := List.exists_of_findSome?_eq_some hfirst
      have hfit := hc reason hmem
      cases reason with
      | die _ _ => exact nomatch hreason
      | interrupt _ _ => exact nomatch hreason
      | fail actual annotations =>
        have heq : actual = error := Option.some.inj hreason
        subst heq
        obtain ⟨v, hv, _⟩ := hfit
        have hsel : firstErrorValue? cause = some v := by
          show (firstFailure? cause).bind valOfErr = some v
          rw [hfirst, Option.bind_some, hv]
        rw [hnone] at hsel
        exact nomatch hsel
  | die _ _ => trivial
  | interrupt _ _ => trivial

/-- A caught value is the cause's first failure's value. -/
theorem firstErrorValue?_of_caught {env : List Val} {test : Term} {cause : CauseV}
    {value : Val} (h : caughtErrorValue? env test cause = some value) :
    firstErrorValue? cause = some value := by
  unfold caughtErrorValue? at h
  cases hfirst : firstErrorValue? cause with
  | none =>
    rw [hfirst] at h
    exact nomatch h
  | some first =>
    rw [hfirst] at h
    change (if evalTerm (env ++ [first]) test = some (.bool true) then some first else none) =
      some value at h
    split at h
    · cases h
      rfl
    · exact nomatch h

/-- **A missed conditional handler's rethrow fits the error bound** (proved): the membership
form of `catchIf_miss_error_admits` (`Laws/Program/Residual.lean`). A literal `true` test catches
every selected failure; a tag test whose residual is empty catches every one (`Ty.diffTag_sound`);
otherwise the bound keeps the body's column. -/
theorem catchIf_miss_fits {w : World} {env : List Val} {test : Term} {be he : Ty}
    {cause : CauseV} (hc : FitsCause w be cause)
    (hmiss : caughtErrorValue? env test cause = none) :
    FitsCause w (catchIfError test env.length be he) cause := by
  unfold catchIfError
  split
  · rename_i htrue
    subst htrue
    cases hvalue : firstErrorValue? cause with
    | none => exact fitsCause_of_firstErrorValue_none hc hvalue
    | some value =>
      unfold caughtErrorValue? at hmiss
      rw [hvalue] at hmiss
      change (if evalTerm (env ++ [value]) (.lit (.bool true)) = some (.bool true) then some value
        else none) = none at hmiss
      rw [if_pos (show evalTerm (env ++ [value]) (.lit (.bool true)) = some (.bool true) from rfl)]
        at hmiss
      exact nomatch hmiss
  · split
    · rename_i tag htag
      split
      · rename_i hnever
        cases hvalue : firstErrorValue? cause with
        | none => exact fitsCause_of_firstErrorValue_none hc hvalue
        | some value =>
          have hv := fits_firstErrorValue hc hvalue
          rw [tagTest?_sound test env.length tag htag] at hmiss
          unfold caughtErrorValue? at hmiss
          rw [hvalue] at hmiss
          change (if evalTerm (env ++ [value]) (tagTest tag env.length) = some (.bool true)
            then some value else none) = none at hmiss
          rw [evalTerm_tagTest] at hmiss
          have hfalse : NativeAtom.tagHit tag value = false := by
            cases h : NativeAtom.tagHit tag value
            · rfl
            · rw [h, if_pos rfl] at hmiss
              exact nomatch hmiss
          have hbad := Ty.diffTag_sound tag be.normalize value _
            (by rw [hasTy_normalize]; exact fits_hasTy w be value hv)
            (by rw [NativeAtom.eval_tagIs, hfalse])
          rw [hnever] at hbad
          exact nomatch hbad
      · exact causeFits_map (fun x hx => fits_join_left w be he x hx) hc
    · exact causeFits_map (fun x hx => fits_join_left w be he x hx) hc

/-- The handler's error column is below the conditional handler's bound. -/
theorem subN_catchIfError (test : Term) (caught : Nat) (be he : Ty) :
    Ty.subN he (catchIfError test caught be he) = true := by
  unfold catchIfError
  split
  · exact Ty.subN_refl _
  · split
    · split
      · exact Ty.subN_refl _
      · exact Ty.subN_join_right _ _
    · exact Ty.subN_join_right _ _

section CatchIfArm

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`catchIf`**: the `onFailure` shape: on a failure the body admits, the first failure's value
is caught when the test holds (the handler runs with it bound at the body's error column),
otherwise the cause is rethrown, which the conditional bound admits (`catchIf_miss_fits`). -/
theorem catchIf_arm {available : Env.Requirement} {test : Term} {b h : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.catchIf test b h)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0])) (hh : ChildDenotes root f h (p.path ++ [1]))
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.catchIf test b h) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_catchIf] at hcheck
  obtain ⟨tb, th, testTy, hcb, _, _, hch, _, rfl⟩ := Checker.inv_catchIf _ _ _ _ _ _ _ hcheck
  have bodyCovered := Row.subset_trans (Row.subset_union_left tb.requires th.requires) coverage
  have handlerCovered := Row.subset_trans (Row.subset_union_right tb.requires th.requires) coverage
  rw [denoteR_catchIf _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_guardBind root
    (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl
      (pointTyped_child hat rfl rfl hcb henv hview hstack) available bodyCovered
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl savedParams))
    (fun later ordered exit present payload => ?_) (fun later ordered exit payload absent => ?_)
    (Row.subset_refl _)
  · cases exit with
    | success value => exact Bool.noConfusion present
    | failure cause =>
      refine ambient_constructR_typed root (Row.subset_refl _)
        (fun after grew completed completedTyped => ?_)
      have future := leHost_trans _ _ _ ordered grew
      have causeTyped := strongExit_mono _ _ _ _ grew payload.1
      have causeFit := fitsExit_failure_cause causeTyped.1
      change AmbientProg root after available _ (match caughtErrorValue? p.env test cause with
        | some value => denoteR root.program h ({ p with completed }.childWith 1 value)
        | none => .pure (.failure cause))
      cases caught : caughtErrorValue? p.env test cause with
      | some value =>
        have valueFits := fits_firstErrorValue causeFit (firstErrorValue?_of_caught caught)
        refine ambientProg_widen root (before := (th, available, available))
          (Ty.subN_join_right _ _) (subN_catchIfError test env.length tb.error th.error)
          (Row.subset_refl _) (Row.subset_refl _) ?_
        exact hh after (serviceTy_leHost future htie) _ th (childWith_fuel_eq (p := { p with completed }) hfuel 1 value) rfl
          (pointTyped_child (q := { p with completed }.childWith 1 value) hat rfl rfl hch
            (envTyped_append (envTyped_mono future henv) valueFits) completedTyped
            (stackTyped_mono future hstack)) available handlerCovered
          (ambientStackTyped_child hat rfl rfl (ambientStackTyped_mono future savedParams))
      | none =>
        have lengthEq : env.length = p.env.length := henv.1
        have miss := catchIf_miss_fits (he := th.error) causeFit caught
        rw [← lengthEq] at miss
        exact .pure ⟨⟨(fitsExit_failure_iff _ _ _).mpr ⟨miss, causeTyped.2⟩, causeTyped.2⟩,
          Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  · cases exit with
    | failure cause => exact Bool.noConfusion absent
    | success value =>
      exact ⟨exitOk_success_of_answerN (Ty.subN_join_left _ _) payload.1, payload.2⟩

end CatchIfArm

/-! ## Arms: the fiber rows

`awaitFiber` and the sixteen fiber actions (`withFiber`). An action's node is resolved by
`actionAt` (`Program/Compile.lean`), which reads the action's terms at the point; every branch it
refuses is excluded by term progress at the checker's types, since the refusal's pre is `False`
(`fiberPre`). A fiber handle's type is read through the upper form of the fiber rule
(`fiberTy_upper`, `src/Effect4/Laws/Program/Eliminators.lean`): a value at the handle's type
moves up to the fiber type of the rule's answer (`fits_subN`). A value at a fiber type is read
through `fiber_of_fits`, and a list of fibers as `actionAt` decodes one (`fibers_of_fits`). The
rows whose entries compare in raw `Ty.sub` (`awaitAll`, `awaitAllFailFast`, `raceAll`; decisions
row 137) are met at a raw union of the declared columns, which lies below the checker's columns
in its order (`unionFold_subN`). -/

/-! ### Fiber handles, views and raw unions -/

/-- A member of a fiber handle type is a fiber handle declared below its columns (the `fiberOf`
arm of `Fits`). -/
theorem fiber_of_fits {w : World} {x : Val} {a e : Ty} (h : Fits w x (.fiberOf a e)) :
    ∃ index, x = Value.fiber index ∧ FiberDeclared w ⟨index⟩ a e := by
  simp only [Fits] at h
  split at h
  · rename_i index
    exact ⟨index, rfl, h⟩
  · exact h.elim

/-- A completed exit the view answers to a join (`Point.awaitExit`): the view's entry for the
target. -/
theorem awaitExit_join {p : Point} {id : FiberId} {exit : ExitV}
    (h : p.awaitExit id .joinEffect = some exit) :
    ∃ entry ∈ p.completed, entry.1 = id ∧ exit = entry.2 := by
  unfold Point.awaitExit at h
  obtain ⟨entry, hfind, hmap⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hfind
  simp only [decide_eq_true_eq] at hp
  exact ⟨entry, List.mem_of_find?_eq_some hfind, hp, hmap.symm⟩

/-- A completed exit the view answers to an await by value: the view's entry for the target,
reified. -/
theorem awaitExit_value {p : Point} {id : FiberId} {exit : ExitV}
    (h : p.awaitExit id .awaitValue = some exit) :
    ∃ entry ∈ p.completed, entry.1 = id ∧ exit = .success (reifyExitVal entry.2) := by
  unfold Point.awaitExit at h
  obtain ⟨entry, hfind, hmap⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hfind
  simp only [decide_eq_true_eq] at hp
  exact ⟨entry, List.mem_of_find?_eq_some hfind, hp, hmap.symm⟩

/-- The view's entry for a fiber whose handle fits `(a, e)` fits `(a, e)`: the entry is typed at
the fiber's declared type (`PointTyped`'s view, row 175), which is below the handle's columns. -/
theorem view_exitOk {w : World} {completed : List (FiberId × ExitV)} {index : Nat} {a e : Ty}
    {entry : FiberId × ExitV}
    (hview : ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2)
    (hmem : entry ∈ completed) (hid : entry.1 = ⟨index⟩) (hdecl : FiberDeclared w ⟨index⟩ a e)
    (req : Env.Requirement) : ExitOk w ⟨a, e, req⟩ entry.2 := by
  obtain ⟨fty, hΓ, hex⟩ := hview entry hmem
  obtain ⟨fty', hΓ', ha, he⟩ := hdecl
  rw [hid, hΓ'] at hΓ
  cases hΓ
  exact exitOk_widen ha he hex

/-- The checker's order on exit types is the order on their columns. -/
theorem subN_exitOf {a e a' e' : Ty} (ha : Ty.subN a a' = true) (he : Ty.subN e e' = true) :
    Ty.subN (.exitOf a e) (.exitOf a' e') = true := by
  unfold Ty.subN at ha he
  show Ty.sub (.exitOf a.normalize e.normalize) (.exitOf a'.normalize e'.normalize) = true
  rw [Ty.sub_args_exitOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, ha, he]

/-- The checker's order on list types is the order on their element types: the list
constructor keeps the order. A step of the claim `denote-typed`. Its consumer is each fiber arm
that reads a list of handles: the fiber rule's upper form is at the element type
(`interruptAll_arm`, `awaitAll_arm`, `awaitAllFailFast_arm`). -/
theorem subN_list {a b : Ty} (below : Ty.subN a b = true) :
    Ty.subN (.list a) (.list b) = true := by
  unfold Ty.subN at below
  show Ty.sub (.list a.normalize) (.list b.normalize) = true
  rw [Ty.sub_args_list]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, below]

/-- The checker's order on lists of exits is the order on the exits' columns. -/
theorem subN_listExitOf {a e a' e' : Ty} (ha : Ty.subN a a' = true) (he : Ty.subN e e' = true) :
    Ty.subN (.list (.exitOf a e)) (.list (.exitOf a' e')) = true := by
  have hx := subN_exitOf ha he
  unfold Ty.subN at hx
  show Ty.sub (.list (Ty.exitOf a e).normalize) (.list (Ty.exitOf a' e').normalize) = true
  rw [Ty.sub_args_list]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, hx]

/-- Raw `sub` places each operand below a union of it: a union's members are its operands'
(`Ty.members`), and raw `sub` reads members (`Ty.OrderProof.sub_iff_members`). -/
theorem sub_union_self_left (a b : Ty) : Ty.sub a (.union a b) = true :=
  (Ty.OrderProof.sub_iff_members Ty.sub_trans a _).mpr fun x hx =>
    ⟨x, List.mem_append_left _ hx, Ty.sub_refl x⟩

theorem sub_union_self_right (a b : Ty) : Ty.sub b (.union a b) = true :=
  (Ty.OrderProof.sub_iff_members Ty.sub_trans b _).mpr fun x hx =>
    ⟨x, List.mem_append_right _ hx, Ty.sub_refl x⟩

/-- A raw union is below every bound of its operands in the checker's order
(`Ty.OrderProof.sub_normalize_union_le`). -/
theorem subN_union_le {a b c : Ty} (hac : Ty.subN a c = true) (hbc : Ty.subN b c = true) :
    Ty.subN (.union a b) c = true :=
  Ty.OrderProof.sub_normalize_union_le Ty.sub_trans a b c.normalize hac hbc

/-- Every column of a list is raw-below the raw union of the list's columns. -/
theorem sub_unionFold {α : Type} (f : α → Ty) :
    ∀ (xs : List α) (x : α), x ∈ xs →
      Ty.sub (f x) (xs.foldr (fun y acc => Ty.union (f y) acc) .never) = true
  | [], _, hx => nomatch hx
  | y :: ys, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sub_union_self_left _ _
    · exact Ty.sub_trans _ _ _ (sub_unionFold f ys x hx) (sub_union_self_right _ _)

/-- The raw union of a list's columns is below every bound of the columns in the checker's
order. -/
theorem unionFold_subN {α : Type} (f : α → Ty) (c : Ty) :
    ∀ (xs : List α), (∀ x ∈ xs, Ty.subN (f x) c = true) →
      Ty.subN (xs.foldr (fun y acc => Ty.union (f y) acc) .never) c = true
  | [], _ => Bounds.subN_never c
  | y :: ys, h => subN_union_le (h y List.mem_cons_self)
      (unionFold_subN f c ys fun x hx => h x (List.mem_cons_of_mem y hx))

/-- **The await-all certificate** (proved): for targets whose handles fit `(a, e)`, the raw unions
of their declared columns meet the rows' raw entries (`fiberPre`'s `awaitAll` and
`awaitAllFailFast` arms) and lie below `(a, e)` in the checker's order. -/
theorem awaitAllCert {w : World} {ids : List FiberId} {a e : Ty}
    (hdecl : ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e)) :
    ∃ A E, (∀ t ∈ ids, ∃ fty, w.Γ t = some fty ∧ fty.answer.sub A = true ∧
        fty.error.sub E = true) ∧ Ty.subN A a = true ∧ Ty.subN E e = true := by
  have hcol : ∀ t ∈ ids, ∃ fty, w.Γ t = some fty ∧ Ty.subN fty.answer a = true ∧
      Ty.subN fty.error e = true := fun t ht => hdecl t ht
  refine ⟨ids.foldr (fun y acc => Ty.union (((w.Γ y).map EffTy.answer).getD .never) acc) .never,
    ids.foldr (fun y acc => Ty.union (((w.Γ y).map EffTy.error).getD .never) acc) .never,
    fun t ht => ?_, unionFold_subN _ _ ids fun t ht => ?_, unionFold_subN _ _ ids fun t ht => ?_⟩
  · obtain ⟨fty, hΓ, -, -⟩ := hcol t ht
    have ha := sub_unionFold (fun y => ((w.Γ y).map EffTy.answer).getD .never) ids t ht
    have he := sub_unionFold (fun y => ((w.Γ y).map EffTy.error).getD .never) ids t ht
    simp only [hΓ, Option.map_some, Option.getD_some] at ha he
    exact ⟨fty, hΓ, ha, he⟩
  · obtain ⟨fty, hΓ, ha, -⟩ := hcol t ht
    simp only [hΓ, Option.map_some, Option.getD_some]
    exact ha
  · obtain ⟨fty, hΓ, -, he⟩ := hcol t ht
    simp only [hΓ, Option.map_some, Option.getD_some]
    exact he

/-- A list of fiber handles read element by element: each handle answers its fiber. -/
theorem mapM_fibers {w : World} {a e : Ty} {g : Val → Option FiberId}
    (hg : ∀ index, g (Value.fiber index) = some ⟨index⟩) :
    ∀ (xs : List Val), (∀ x ∈ xs, Fits w x (.fiberOf a e)) →
      ∃ ids, xs.mapM g = some ids ∧ ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e)
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | x :: xs, h => by
    obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits (h x List.mem_cons_self)
    obtain ⟨ids, hids, hfits⟩ := mapM_fibers hg xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨⟨index⟩ :: ids, ?_, fun id hid => ?_⟩
    · simp only [List.mapM_cons, hg, hids]
      rfl
    · rcases List.mem_cons.mp hid with rfl | hid
      · exact hdecl
      · exact hfits id hid

/-- A list of fiber handles read element by element, at the reader's answer. -/
theorem mapM_fibers_eq {w : World} {a e : Ty} {g : Val → Option FiberId} {xs : List Val}
    {res : Option (List FiberId)} (heq : xs.mapM g = res)
    (hg : ∀ index, g (Value.fiber index) = some ⟨index⟩)
    (hall : ∀ x ∈ xs, Fits w x (.fiberOf a e)) :
    ∃ ids, res = some ids ∧ ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e) := by
  obtain ⟨ids, hids, hfits⟩ := mapM_fibers hg xs hall
  exact ⟨ids, heq.symm.trans hids, hfits⟩

/-- **A value at a list of fiber handles** (proved): a list whose elements fit, or a snapshot whose
handles the handle image reads back, each declared (the two shapes `Fits`' list arm reads,
`fits_list_iff`). `actionAt` decodes a list of fibers by these two shapes (its `handles`,
`Program/Compile.lean`). -/
theorem fibers_of_fits {w : World} {v : Val} {a e : Ty} (h : Fits w v (.list (.fiberOf a e))) :
    (∃ xs, v = .list xs ∧ ∀ x ∈ xs, Fits w x (.fiberOf a e)) ∨
      ∃ hs ids, v = Value.fiberSnapshot hs ∧
        (Store.Image.list Value.fiberHandle).ofVal hs = some ids ∧
          ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e) := by
  obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp h
  rcases Val.asList?_exact hxs with rfl | rfl
  · exact .inl ⟨xs, rfl, hall⟩
  · obtain ⟨ids, hsnap, hmap⟩ := Option.map_eq_some_iff.mp hxs
    refine .inr ⟨.list xs, ids, rfl, hsnap, fun id hid => hall _ ?_⟩
    rw [← hmap]
    exact List.mem_map_of_mem hid

/-- A row answering `unit` continued by its answer is typed at `pure unit`. -/
theorem unitAnswer_typed (root : ProgramSource) {w : World} {ans : Val} (h : ans = Val.unit) :
    TypedProg root w (EffTy.pure .unit) (.pure (.success ans)) := by
  subst h
  exact .pure (strongExit_success w _ _ trivial)

/-- The ambient scope's read, typed at the scope type (`fiberPost`'s `ambientScope` arm). -/
theorem ambientScope_typed (root : ProgramSource) (w : World) :
    TypedProg root w (EffTy.pure Ty.scope) (fiberValR .ambientScope rfl) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial
    (fun w' _ ans post => .pure (strongExit_success w' _ ans post))

/-- A value at an exit type decodes as an exit (`exitOfVal`, the exit image read back). -/
theorem exitOfVal_of_fits {w : World} {v : Val} {a e : Ty} (h : Fits w v (.exitOf a e)) :
    ∃ ex, exitOfVal v = some ex := by
  simp only [Fits] at h
  split at h
  · rename_i x
    exact ⟨_, exitOfVal_exitOk x⟩
  · rename_i written
    split at h
    · rename_i c hc
      refine ⟨.failure c, ?_⟩
      rw [causeImage.ofVal_exact hc]
      exact exitOfVal_exitErr c
    · exact h.elim
  · exact h.elim

/-- The checked entrants of a race: each entrant's point is typed at its own checked type, raw
below the raw unions of the entrants' columns, which lie below the race's checked columns in
the checker's order. Private: the spine's rounds (`effsRounds`) are no definition of the tree. -/
private theorem raceEntrants_typed {root : ProgramSource} {w : World} {env : List Ty}
    {base : List Nat} :
    ∀ (es : Effs NativeOp) (q : Point) (T : EffTy),
      (∀ x, q.path <+: x → scopeParams root.program x = scopeParams root.program base) →
      Node.at_ (.eff root.program) q.path = some (.effs es) →
      Checker.checkEffs (root.scopeSig base) env q.path []
          (effsRounds (Node.eff root.program)
            (List.range ((root.program.refSites []).length + 1)) es) = .ok T →
      EnvTyped w env q.env →
      (∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2) →
      StackTyped root w (scopeParams root.program base) q.params →
      ∃ A E, (∀ r ∈ entrantPoints es q, ∃ ty, PointTyped root w r ty ∧
          ty.answer.sub A = true ∧ ty.error.sub E = true ∧ Row.Subset ty.requires T.requires) ∧
        Ty.subN A T.answer = true ∧ Ty.subN E T.error = true
  | .nil, _, T, _, _, hc, _, _, _ => by
    rw [effsRounds_nil] at hc
    have hT := Checker.inv_effs_nil _ _ _ _ _ hc
    subst hT
    exact ⟨.never, .never, fun r hr => absurd hr List.not_mem_nil, Bounds.subN_never _, Bounds.subN_never _⟩
  | .cons h t, q, T, hscope, hat, hc, henv, hview, hstack => by
    rw [effsRounds_cons] at hc
    obtain ⟨H, R, hch, hct, rfl⟩ := Checker.inv_effs_cons _ _ _ _ _ _ hc
    obtain ⟨A, E, hrest, hA, hE⟩ :=
      raceEntrants_typed t (q.child 1) R (fun x hx => hscope x ((List.prefix_append _ _).trans hx))
        (node_at_child hat rfl) hct henv hview hstack
    refine ⟨.union H.answer A, .union H.error E, fun r hr => ?_,
      subN_union_le (Ty.subN_join_left _ _) (Ty.subN_trans hA (Ty.subN_join_right _ _)),
      subN_union_le (Ty.subN_join_left _ _) (Ty.subN_trans hE (Ty.subN_join_right _ _))⟩
    simp only [entrantPoints, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨H, pointTyped_scope (hscope _ (List.prefix_append _ _)) (node_at_child hat rfl) hch
        henv hview hstack, sub_union_self_left _ _, sub_union_self_left _ _, Row.subset_union_left _ _⟩
    · obtain ⟨ty, hpt, ha, he, required⟩ := hrest r hr
      exact ⟨ty, hpt, Ty.sub_trans _ _ _ ha (sub_union_self_right _ _),
        Ty.sub_trans _ _ _ he (sub_union_self_right _ _),
        Row.subset_trans required (Row.subset_union_right _ _)⟩

section FiberArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy}

/-- **`awaitFiber`**: the target is a fiber handle (`fiberTy_upper`, term progress); a completed
target answers from the view, which is typed at its declared type (row 175); a running one is the
await row, whose post answers at the declared type, below the handle's columns
(`await_fits`; by value, `subN_exitOf`). -/
theorem awaitFiber_arm {available : Env.Requirement} {t : Term} {mode : Supervision.ObserverMode} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.awaitFiber t mode)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.awaitFiber t mode) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  rw [denoteR_awaitFiber _ _ _ hfuel]
  cases mode with
  | joinEffect =>
    obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_join _ _ _ _ _ hcheck
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
    replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
    obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
    rw [hv]
    change AmbientProg root w available _ (match p.awaitExit ⟨index⟩ .joinEffect with
      | some exit => .pure exit
      | none => .vis (.inr (.await ⟨index⟩ .joinEffect)) Effects.Program.pure)
    cases hawait : p.awaitExit ⟨index⟩ .joinEffect with
    | some exit =>
      obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_join hawait
      exact .pure ⟨view_exitOk hview hmem hid hdecl _, by cases entry.2 <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
    | none =>
      refine ambient_fiber_leaf_of_typed root available _ _
        (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
        (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
        ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
        (fun answer => ⟨answer, rfl⟩)
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () ?_ (fun w' o ans post => ?_)
      · obtain ⟨fty, hΓ, -, -⟩ := hdecl
        show (w.Γ ⟨index⟩).isSome = true
        rw [hΓ]
        rfl
      · obtain ⟨fty', hΓ', hex⟩ := post
        exact .pure ⟨await_fits hfit o hΓ' hex.1 _, hex.2⟩
  | awaitValue =>
    obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_await _ _ _ _ _ hcheck
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
    replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
    obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
    rw [hv]
    change AmbientProg root w available _ (match p.awaitExit ⟨index⟩ .awaitValue with
      | some exit => .pure exit
      | none => .vis (.inr (.await ⟨index⟩ .awaitValue)) fun v => .pure (.success v))
    cases hawait : p.awaitExit ⟨index⟩ .awaitValue with
    | some exit =>
      obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_value hawait
      exact .pure ⟨strongExit_success w _ _ (view_exitOk hview hmem hid hdecl .empty).1, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
    | none =>
      obtain ⟨fty, hΓ, ha, he⟩ := hdecl
      refine ambient_fiber_leaf_of_typed root available _ _
        (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
        (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
        ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
        (fun answer => ⟨.success answer, rfl⟩)
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () ?_ (fun w' o ans post => ?_)
      · show (w.Γ ⟨index⟩).isSome = true
        rw [hΓ]
        rfl
      · obtain ⟨fty', hΓ', hans⟩ := post
        rw [o.1.2.1 _ _ hΓ] at hΓ'
        cases hΓ'
        exact .pure (strongExit_success w' _ _ (fits_subN w' (subN_exitOf ha he) ans hans))

/-- **`fork`**: the body's point is typed at its checked type (the row's pre is the body's
typing); the post's fiber is declared at that type, so its handle fits the fiber type. -/
theorem fork_arm {available : Env.Requirement} {b : NativeEff} {options : Supervision.ForkOptions}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.fork b options))))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_fork] at hcheck
  obtain ⟨q, hcq, rfl⟩ :=
    Checker.inv_action_fork _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  have hact : actionAt root.program p = some (WithFiberAction.fork
      (resolve root.program ((p.child 0).child 0)) options (p.child 0).path) := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  have hbody : PointTyped root w ((p.child 0).child 0) q :=
    pointTyped_scope (scopeParams_prefix hat (fun _ _ _ _ h => nomatch h)
      ((List.prefix_append _ _).trans (List.prefix_append _ _)))
      (node_at_child (node_at_child hat rfl) rfl) hcq henv hview hstack
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) q ⟨BodyTyped.at_ _ _ hbody, coverage,
      (fun _ _ impossible => by cases impossible),
      (fun _ _ _ impossible => by cases impossible),
      ⟨(fun _ impossible => by cases impossible),
        (fun _ _ _ impossible => by cases impossible),
        ⟨(fun point role => by
          rcases role with identity | ⟨ctx, impossible | impossible⟩
          · cases identity
            exact (ambientPointTyped_scope (q := (p.child 0).child 0)
              (scopeParams_prefix hat (fun _ _ _ _ h => nomatch h)
                ((List.prefix_append _ _).trans (List.prefix_append _ _)))
              (node_at_child (node_at_child hat rfl) rfl) hcq henv hview savedParams).2
          · cases impossible
          · cases impossible), fun _ _ _ impossible => by cases impossible⟩⟩⟩
    (fun w' _ ans post => ?_) ⟨Row.subset_refl _, Row.subset_refl _⟩
  obtain ⟨id, rfl, hΓ⟩ := post
  exact .pure ⟨strongExit_success w' _ _ ⟨q, hΓ, Ty.subN_refl _, Ty.subN_refl _⟩,
    Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **`forkIn`**: as `fork`, the scope term a present scope's handle (`fits_scope_inv`). -/
theorem forkIn_arm {available : Env.Requirement} {b : NativeEff} {options : Supervision.ForkOptions} {scope : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.forkIn b options scope))))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_forkIn] at hcheck
  obtain ⟨q, scopeTy, hcq, hscope, hsub_scope, rfl⟩ :=
    Checker.inv_action_forkIn _ _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hscope
  obtain ⟨sc, rfl, hlive⟩ := fits_scope_inv (fits_subN w (b := .scope) hsub_scope v hfit)
  have hact : actionAt root.program p = some (WithFiberAction.forkIn
      (resolve root.program ((p.child 0).child 0)) options sc (p.child 0).path) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv]
    rfl
  rw [denoteAction_of _ _ hact]
  have hbody : PointTyped root w ((p.child 0).child 0) q :=
    pointTyped_scope (scopeParams_prefix hat (fun _ _ _ _ h => nomatch h)
      ((List.prefix_append _ _).trans (List.prefix_append _ _)))
      (node_at_child (node_at_child hat rfl) rfl) hcq henv hview hstack
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) q ⟨⟨hbody, hlive⟩, coverage⟩ (fun w' _ ans post => ?_) ⟨Row.subset_refl _, Row.subset_refl _⟩
  obtain ⟨id, rfl, hΓ⟩ := post
  exact .pure ⟨strongExit_success w' _ _ ⟨q, hΓ, Ty.subN_refl _, Ty.subN_refl _⟩,
    Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **`forkScoped`**: the ambient scope's read (`seqGuard_typed`), then `forkIn` on the handle it
answers, a present scope's (`fits_scope_inv`). -/
theorem forkScoped_arm {available : Env.Requirement} {b : NativeEff} {options : Supervision.ForkOptions}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.forkScoped b options))))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_forkScoped] at hcheck
  obtain ⟨q, hcq, rfl⟩ :=
    Checker.inv_action_forkScoped _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  have hact : actionAt root.program p = some WithFiberAction.ambientScope := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  have hbody : PointTyped root w ((p.child 0).child 0) q :=
    pointTyped_scope (scopeParams_prefix hat (fun _ _ _ _ h => nomatch h)
      ((List.prefix_append _ _).trans (List.prefix_append _ _)))
      (node_at_child (node_at_child hat rfl) rfl) hcq henv hview hstack
  simp only [denoteFiberAction]
  rw [hat]
  simp only []
  have scopeRead : AmbientProg root w available (EffTy.pure Ty.scope, available, available)
      (fiberValR .ambientScope rfl) :=
    ambient_fiber_leaf_of_typed root available .ambientScope _
      (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
      (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
      (ambientScope_typed root w) (fun _ pre => pre) (fun _ _ _ _ post => post)
      (fun _ => rfl) (fun value => ⟨.success value, rfl⟩)
  refine ambient_guardBind root scopeRead (fun later ordered exit arm payload => ?_)
    (fun later ordered exit payload absent => ?_) (Row.subset_refl _)
  · cases exit with
    | failure cause => exact Bool.noConfusion arm
    | success value =>
      obtain ⟨scope, rfl, live⟩ := fits_scope_inv payload.1.1
      simp only [seqR, ambientInput]
      refine .fiber (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
        (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
        q ⟨⟨pointTyped_mono ordered hbody, live⟩,
          Row.subset_trans (Row.subset_union_left _ _) coverage⟩
        (fun after _ answer post => ?_) ⟨Row.subset_refl _, Row.subset_refl _⟩
      obtain ⟨id, rfl, declared⟩ := post
      exact .pure ⟨strongExit_success after _ _ ⟨q, declared, Ty.subN_refl _, Ty.subN_refl _⟩,
        Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Ty.subN_refl _) payload.1, Row.subset_refl _⟩

/-- **`runIn`**: a declared fiber and a present scope (the row's pre), answering `unit`. -/
theorem runIn_arm {available : Env.Requirement} {target scope : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.runIn target scope))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨handle, pair, scopeTy, hty, hfib, hscope, hsub_scope, rfl⟩ :=
    Checker.inv_action_runIn _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
  obtain ⟨index, rfl, fty, hΓ, -, -⟩ := fiber_of_fits hfit
  obtain ⟨u, hu, hufit⟩ := evalTerm_progress_env henv hscope
  obtain ⟨sc, rfl, hlive⟩ := fits_scope_inv (fits_subN w (b := .scope) hsub_scope u hufit)
  have hact : actionAt root.program p = some (WithFiberAction.runIn ⟨index⟩ sc) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, hu]
    rfl
  rw [denoteAction_of _ _ hact]
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () ⟨?_, hlive⟩ (fun w' _ ans post => unitAnswer_typed root post)
  show (w.Γ ⟨index⟩).isSome = true
  rw [hΓ]
  rfl

/-- **`interrupt`**: the target a fiber handle; the row answers `unit`. -/
theorem interrupt_arm {available : Env.Requirement} {target : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.interrupt target))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨handle, pair, hty, hfib, rfl⟩ :=
    Checker.inv_action_interrupt _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
  obtain ⟨index, rfl, fty, hdecl, -⟩ := fiber_of_fits hfit
  have hact : actionAt root.program p = some (WithFiberAction.interrupt ⟨index⟩) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv]
    rfl
  rw [denoteAction_of _ _ hact]
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () (show (w.Γ ⟨index⟩).isSome = true by rw [hdecl]; rfl)
    (fun w' _ ans post => unitAnswer_typed root post)

/-- **`interruptScoped`**: as `interrupt`. -/
theorem interruptScoped_arm {available : Env.Requirement} {target : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.interruptScoped target))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨handle, pair, hty, hfib, rfl⟩ :=
    Checker.inv_action_interruptScoped _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
  replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
  obtain ⟨index, rfl, fty, hdecl, -⟩ := fiber_of_fits hfit
  have hact : actionAt root.program p = some (WithFiberAction.interruptScoped ⟨index⟩) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv]
    rfl
  rw [denoteAction_of _ _ hact]
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () (show (w.Γ ⟨index⟩).isSome = true by rw [hdecl]; rfl)
    (fun w' _ ans post => unitAnswer_typed root post)

/-- Fiber handles that fit are declared. -/
theorem fibersDeclared_of_fits {ids : List FiberId} {a e : Ty}
    (hdecl : ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf a e)) :
    ∀ t ∈ ids, (w.Γ t).isSome = true := by
  intro t ht
  obtain ⟨fty, hΓ, -, -⟩ : ∃ fty, w.Γ t = some fty ∧ Ty.subN fty.answer a = true ∧
      Ty.subN fty.error e = true := hdecl t ht
  rw [hΓ]
  rfl

/-- **`interruptAll`**: the targets a list of declared fiber handles (`fibers_of_fits`, the row's
pre), the interruptor a number; the row answers `unit`. -/
theorem interruptAll_arm {available : Env.Requirement} {targets : Term} {who : Option Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.interruptAll targets who))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hc := Checker.inv_withFiber _ _ _ _ _ hcheck
  cases who with
  | none =>
    obtain ⟨ts, inner, pair, hts, hlist, hfib, rfl⟩ := Checker.inv_action_interruptAll_self _ _ _ _ _ hc
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
    replace hfit := fits_subN w (listOf_upper hlist) v hfit
    replace hfit := fits_subN w (subN_list (fiberTy_upper hfib)) v hfit
    obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
        some (WithFiberAction.interruptAll ids none) ∧
          ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
      unfold actionAt
      rw [hat]
      simp only []
      rw [hv, Option.bind_some]
      rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
      · simp only [Val.tuple?, Option.bind_some]
        split
        · next ids heq =>
          obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          cases hids'
          exact ⟨ids, rfl, hfits⟩
        · next heq =>
          obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          exact nomatch hids
      · simp only [hofv]
        exact ⟨ids, rfl, hall⟩
    rw [denoteAction_of _ _ hact]
    refine ambient_fiber_leaf_of_typed root available _ _
      (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
      (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
      ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
      (fun answer => ⟨.success answer, rfl⟩)
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () (fibersDeclared_of_fits hdecl)
      (fun w' _ ans post => unitAnswer_typed root post)
  | some who =>
    obtain ⟨ts, inner, pair, whoTy, hts, hlist, hfib, hwho, hsub_who, rfl⟩ := Checker.inv_action_interruptAll_by _ _ _ _ _ _ hc
    obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
    replace hfit := fits_subN w (listOf_upper hlist) v hfit
    replace hfit := fits_subN w (subN_list (fiberTy_upper hfib)) v hfit
    obtain ⟨n, hn, hnfit⟩ := evalTerm_progress_env henv hwho
    obtain ⟨m, rfl⟩ := fits_nat_inv (fits_subN w (b := .nat) hsub_who n hnfit)
    obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
        some (WithFiberAction.interruptAll ids (some ⟨m⟩)) ∧
          ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
      unfold actionAt
      rw [hat]
      simp only []
      rw [hv, Option.bind_some, hn]
      rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
      · simp only [Val.tuple?, Option.bind_some]
        split
        · next ids heq =>
          obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          cases hids'
          exact ⟨ids, rfl, hfits⟩
        · next heq =>
          obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
          exact nomatch hids
      · simp only [hofv]
        exact ⟨ids, rfl, hall⟩
    rw [denoteAction_of _ _ hact]
    refine ambient_fiber_leaf_of_typed root available _ _
      (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
      (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
      ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
      (fun answer => ⟨.success answer, rfl⟩)
    exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () (fibersDeclared_of_fits hdecl)
      (fun w' _ ans post => unitAnswer_typed root post)

/-- **`awaitAll`**: the targets a list of declared fibers (`fibers_of_fits`); the row is met at the
raw unions of their declared columns (`awaitAllCert`), whose answer is below the checked list of
exits. -/
theorem awaitAll_arm {available : Env.Requirement} {targets : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.awaitAll targets))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨ts, inner, pair, hts, hlist, hfib, rfl⟩ :=
    Checker.inv_action_awaitAll _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
  replace hfit := fits_subN w (listOf_upper hlist) v hfit
  replace hfit := fits_subN w (subN_list (fiberTy_upper hfib)) v hfit
  obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
      some (WithFiberAction.awaitAll ids) ∧
        ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, Option.bind_some]
    rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
    · simp only [Val.tuple?, Option.bind_some]
      split
      · next ids heq =>
        obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        cases hids'
        exact ⟨ids, rfl, hfits⟩
      · next heq =>
        obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        exact nomatch hids
    · simp only [hofv]
      exact ⟨ids, rfl, hall⟩
  rw [denoteAction_of _ _ hact]
  obtain ⟨A, E, hpre, hA, hE⟩ := awaitAllCert hdecl
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.list (.exitOf A E)) (.inl ⟨A, E, rfl, hpre⟩)
    (fun w' _ ans post =>
      .pure (strongExit_success w' _ ans (fits_subN w' (subN_listExitOf hA hE) ans post)))

/-- **`awaitAllFailFast`**: as `awaitAll`. -/
theorem awaitAllFailFast_arm {available : Env.Requirement} {targets : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.awaitAllFailFast targets))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨ts, inner, pair, hts, hlist, hfib, rfl⟩ :=
    Checker.inv_action_awaitAllFailFast _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hts
  replace hfit := fits_subN w (listOf_upper hlist) v hfit
  replace hfit := fits_subN w (subN_list (fiberTy_upper hfib)) v hfit
  obtain ⟨ids, hact, hdecl⟩ : ∃ ids, actionAt root.program p =
      some (WithFiberAction.awaitAllFailFast ids) ∧
        ∀ id ∈ ids, Fits w (Val.fiber id) (.fiberOf pair.1 pair.2) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, Option.bind_some]
    rcases fibers_of_fits hfit with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, hall⟩
    · simp only [Val.tuple?, Option.bind_some]
      split
      · next ids heq =>
        obtain ⟨ids', hids', hfits⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        cases hids'
        exact ⟨ids, rfl, hfits⟩
      · next heq =>
        obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        exact nomatch hids
    · simp only [hofv]
      exact ⟨ids, rfl, hall⟩
  rw [denoteAction_of _ _ hact]
  obtain ⟨A, E, hpre, hA, hE⟩ := awaitAllCert hdecl
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.list (.exitOf A E)) (.inl ⟨A, E, rfl, hpre⟩)
    (fun w' _ ans post =>
      .pure (strongExit_success w' _ ans (fits_subN w' (subN_listExitOf hA hE) ans post)))

/-- **`snapshotChildren`**: the row answers at its certificate, the checked type. -/
theorem snapshotChildren_arm {available : Env.Requirement}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber .snapshotChildren)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, -, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty := Checker.inv_action_snapshotChildren _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  subst hty
  have hact : actionAt root.program p = some WithFiberAction.snapshotChildren := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.list (.fiberOf .unknown .unknown)) rfl
    (fun w' _ ans post => .pure (strongExit_success w' _ ans post))

/-- **`awaitNewChildren`**: the snapshot a list of fiber handles (below the snapshot type in raw
`sub`, `fits_sub`); the row answers `unit`. -/
theorem awaitNewChildren_arm {available : Env.Requirement} {snapshot : Term}
    (hat : Node.at_ (.eff root.program) p.path =
      some (.eff (.withFiber (.awaitNewChildren snapshot))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨s, hs, hsub, rfl⟩ :=
    Checker.inv_action_awaitNewChildren _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hs
  have hfit' : Fits w v (.list (.fiberOf .unknown .unknown)) :=
    fits_sub w hsub v ((fits_normalize w s v).mpr hfit)
  obtain ⟨ids, hact⟩ : ∃ ids, actionAt root.program p =
      some (WithFiberAction.awaitNewChildren ids) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hv, Option.bind_some]
    rcases fibers_of_fits hfit' with ⟨xs, rfl, hall⟩ | ⟨hs, ids, rfl, hofv, -⟩
    · simp only [Val.tuple?, Option.bind_some]
      split
      · next ids _ => exact ⟨ids, rfl⟩
      · next heq =>
        obtain ⟨ids, hids, -⟩ := mapM_fibers_eq heq (by intro _; rfl) hall
        exact nomatch hids
    · simp only [hofv]
      exact ⟨ids, rfl⟩
  rw [denoteAction_of _ _ hact]
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => unitAnswer_typed root post)

/-- **`raceAll`**: every entrant's point is typed (the row's pre, `raceEntrants_typed`), at the raw
unions of the entrants' columns; the race's exit fits them, so the checked join. -/
theorem raceAll_arm {available : Env.Requirement} {es : Effs NativeOp}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.raceAll es))))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_raceAll] at hcheck
  have hc := Checker.inv_action_raceAll _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨A, E, hpre, hA, hE⟩ := raceEntrants_typed es ((p.child 0).child 0) ty
    (fun x hx => scopeParams_prefix hat (fun _ _ _ _ h => nomatch h)
      (((List.prefix_append _ _).trans (List.prefix_append _ _)).trans hx))
    (node_at_child (node_at_child hat rfl) rfl) hc henv hview hstack
  obtain ⟨ents, hact⟩ : ∃ ents, actionAt root.program p =
      some (WithFiberAction.raceAll ents (some ((p.child 0).child 0).path)) := by
    unfold actionAt
    rw [hat]
    exact ⟨_, rfl⟩
  rw [denoteAction_of _ _ hact]
  have hrace : racePoints root.program p = entrantPoints es ((p.child 0).child 0) := by
    unfold racePoints
    rw [hat]
  change AmbientProg root w available (ty, available, available) (.vis (.inr (.raceAll (racePoints root.program p)
    (some ((p.child 0).child 0).path))) Effects.Program.pure)
  rw [hrace]
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ⟨A, E, ty.requires⟩ ?_
    (fun w' _ ans post => .pure ⟨exitOk_widen hA hE post,
      by cases ans <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩
  intro point member
  obtain ⟨pointTy, admitted, answer, error, required⟩ := hpre point member
  exact ⟨pointTy, admitted, answer, error, Row.subset_trans required coverage⟩

/-- First-exit entrant typing serves `withFiber_arm` at the same checked joined columns. -/
theorem raceAllFirst_arm {available : Env.Requirement} {es : Effs NativeOp}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.raceAllFirst es))))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_raceAllFirst] at hcheck
  have hc := Checker.inv_action_raceAllFirst _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨A, E, hpre, hA, hE⟩ := raceEntrants_typed es ((p.child 0).child 0) ty
    (fun x hx => scopeParams_prefix hat (fun _ _ _ _ h => nomatch h)
      (((List.prefix_append _ _).trans (List.prefix_append _ _)).trans hx))
    (node_at_child (node_at_child hat rfl) rfl) hc henv hview hstack
  obtain ⟨ents, hact⟩ : ∃ ents, actionAt root.program p =
      some (WithFiberAction.raceAllFirst ents (some ((p.child 0).child 0).path)) := by
    unfold actionAt
    rw [hat]
    exact ⟨_, rfl⟩
  rw [denoteAction_of _ _ hact]
  have hrace : racePoints root.program p = entrantPoints es ((p.child 0).child 0) := by
    unfold racePoints
    rw [hat]
  change AmbientProg root w available (ty, available, available) (.vis (.inr (.raceAllFirst (racePoints root.program p)
    (some ((p.child 0).child 0).path))) Effects.Program.pure)
  rw [hrace]
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ⟨A, E, ty.requires⟩ ?_
    (fun w' _ ans post => .pure ⟨exitOk_widen hA hE post,
      by cases ans <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩
  intro point member
  obtain ⟨pointTy, admitted, answer, error, required⟩ := hpre point member
  exact ⟨pointTy, admitted, answer, error, Row.subset_trans required coverage⟩

/-- **`getId`**: the fiber's id, a number. -/
theorem getId_arm {available : Env.Requirement}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber .getId)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, -, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty := Checker.inv_action_getId _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  subst hty
  have hact : actionAt root.program p = some WithFiberAction.getId := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => ?_)
  obtain ⟨id, rfl⟩ := post
  exact .pure (strongExit_success w' _ _ trivial)

/-- **`getInterruptible`** (decisions row 245): the mask at a constant body. Its answer is one of
the two saved images (`fiberPost`'s row), a member of the saved state's type in every world
(`fits_savedMask`). -/
theorem getInterruptible_arm {available : Env.Requirement}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber .getInterruptible)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, -, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  have hty :=
    Checker.inv_action_getInterruptible _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  subst hty
  have hact : actionAt root.program p = some WithFiberAction.getInterruptible := by
    unfold actionAt
    rw [hat]
  rw [denoteAction_of _ _ hact]
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨.success answer, rfl⟩)
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => ?_)
  obtain ⟨flag, rfl⟩ := post
  exact .pure (strongExit_success w' _ _ (fits_savedMask w' flag))

/-- **`closeScope`**: a present scope and an exit value that decodes (`exitOfVal_of_fits`) and fits
`Exit<unknown, unknown>` (the row's pre, F-CLOSE); the close answers an exit at `pure unit`. -/
theorem closeScope_arm {available : Env.Requirement} {scope exit : Term}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.closeScope scope exit))))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨scopeTy, exitTy, pair, hs, hsub_scope, hex, hexit, rfl⟩ :=
    Checker.inv_action_closeScope _ _ _ _ _ _ (Checker.inv_withFiber _ _ _ _ _ hcheck)
  obtain ⟨u, hu, hufit⟩ := evalTerm_progress_env henv hs
  obtain ⟨sc, rfl, hlive⟩ := fits_scope_inv (fits_subN w (b := .scope) hsub_scope u hufit)
  obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hex
  replace hvfit := fits_subN w (exitOf_upper hexit) v hvfit
  obtain ⟨ex, hexv⟩ := exitOfVal_of_fits hvfit
  have hact : actionAt root.program p = some (WithFiberAction.closeScope sc ex) := by
    unfold actionAt
    rw [hat]
    simp only []
    rw [hu, hv, Option.bind_some, hexv]
    rfl
  rw [denoteAction_of _ _ hact]
  -- the closing exit fits `Exit<unknown, unknown>` (F-CLOSE): the value is the exit's image, at
  -- its checked exit type, widened
  have himage : v = reifyExitVal ex := by
    rw [reifyExitVal_eq_exitImage]
    exact exitImage.ofVal_exact hexv
  have hfits : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex := by
    show Fits w (reifyExitVal ex) (.exitOf .unknown .unknown)
    rw [← himage]
    refine fits_subN w (subN_exitOf ?_ ?_) v hvfit
    · exact Ty.sub_unknown _
    · exact Ty.sub_unknown _
  refine ambient_fiber_leaf_of_typed root available _ _
    (fun _ impossible => nomatch impossible) (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) (fun _ _ _ impossible => nomatch impossible)
    ?_ (fun _ pre => pre) (fun _ _ _ _ post => post) (fun _ => rfl)
    (fun answer => ⟨answer, rfl⟩)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () ⟨hlive, hfits⟩ (fun _ _ _ post => .pure post)

/-- **`withFiber`**: the seventeen actions, each by its arm. -/
theorem withFiber_arm {available : Env.Requirement} {a : ActionTerm NativeOp} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber a)))
    (hpt : PointTyped root w p ty) (services : w.serviceTy = root.sig.serviceTy)
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.withFiber a) p) := by
  rw [denoteR_withFiber _ _ _ hfuel]
  cases a with
  | fork b options => exact fork_arm hat hpt coverage savedParams
  | forkIn b options scope => exact forkIn_arm hat hpt coverage
  | forkScoped b options => exact forkScoped_arm hat hpt coverage
  | runIn target scope => exact runIn_arm hat hpt
  | interrupt target => exact interrupt_arm hat hpt
  | interruptScoped target => exact interruptScoped_arm hat hpt
  | interruptAll targets who => exact interruptAll_arm hat hpt
  | awaitAll targets => exact awaitAll_arm hat hpt
  | awaitAllFailFast targets => exact awaitAllFailFast_arm hat hpt
  | snapshotChildren => exact snapshotChildren_arm hat hpt
  | awaitNewChildren snapshot => exact awaitNewChildren_arm hat hpt
  | raceAll es => exact raceAll_arm hat hpt coverage
  | raceAllFirst es => exact raceAllFirst_arm hat hpt coverage
  | context keys =>
    obtain ⟨env, checked, -, -, -⟩ := hpt.at_node hat
    rw [Eff.expandIn_of_round _ _ rfl] at checked
    have typed := checked_context_denotation root w p env keys available ty hat checked services coverage
    rw [denoteR_withFiber _ _ _ hfuel] at typed
    exact typed
  | getId => exact getId_arm hat hpt
  | closeScope scope exit => exact closeScope_arm hat hpt
  | getInterruptible => exact getInterruptible_arm hat hpt

end FiberArms

/-! ## Arms: the store rows, the services and `exit`

A `perform` at a built-in row is the row's store operation (`syncRow_typed`), its asynchronous
registration (`deferredAwait`, `sleep`) or, at a host row, the host registration whose certificate
is the node's checked type: the checker types the node at the row's instance at the request
(`rowTy`), and `bitEntry` (`Typed/Residual.lean`) reads that instance (decisions row 183). `service` reads the context's binding at the key's declared carrier (`ServicesFit`, the
world's table tied to the source's); `provideService` sets a context whose new binding fits that
carrier (`fits_flatFits`, a lawful signature's carriers being flat) and restores the previous
one. `exit` reifies its body's exit, an inline exit typed by `inlineYield_typed`. -/

/-! ### Built-in rows -/

/-! The two handle inversions `fits_refOf_inv` and `fits_deferredOf_inv` live in
`Typed/Membership.lean` since the list fold (decisions rows 228 and 229): the identity atom's
membership case reads them, and membership does not import the denotation. Names and statements
are unchanged. -/

/-- A cell's declaration survives compatible world extension (`leHost` extends the reference
table). -/
theorem refDeclared_mono {w w' : World} (ord : w.leHost w') {key : RefKey} {t : Ty}
    (h : RefDeclared w key t) : RefDeclared w' key t := by
  obtain ⟨t', hlookup, hequiv⟩ := h
  exact ⟨t', ord.1.2.2.2.1 _ _ hlookup, hequiv⟩

/-- A deferred's declaration survives compatible world extension. -/
theorem promiseDeclared_mono {w w' : World} (ord : w.leHost w') {key : DeferredKey} {a e : Ty}
    (h : PromiseDeclared w key a e) : PromiseDeclared w' key a e := by
  obtain ⟨a', e', hlookup, ha, he⟩ := h
  exact ⟨a', e', ord.1.2.2.1 _ _ hlookup, ha, he⟩

/-- **Reference read** (the TYPES 2003 card's first step): a reply fitting the cell's declared
type at the reply's world fits every type the cell is declared equivalent to; the lookup's
equality identifies the reply's declaration, and normalized subtyping transports the reply. A step
of `denote-typed`; its consumers are `syncRow_typed`'s reading arms. -/
theorem refRead {w : World} {key : RefKey} {A ty : Ty} {ans : Val}
    (hdecl : RefDeclared w key A) (hlookup : w.Ρ key = some ty) (hfit : Fits w ans ty) :
    Fits w ans A := by
  obtain ⟨t', hlookup', hequiv⟩ := hdecl
  rw [hlookup] at hlookup'
  cases hlookup'
  exact fits_subN w hequiv.1 ans hfit

/-! #### A term row's store pre, from its binder term's typing

A read-modify-write row carries a binder term (decisions row 43), and the store's pre asks that
the term map the cell's declared type into the row's result type at every later world
(`TermMaps`, `storePre`). The checker types the term at the instance's element type and matches
its type against the shape's result template (`bindTerm`), so the pre follows from the term's
typing: `termMaps_of_typed` gives the term relation at the instance, the guard and the cell's
declaration move it to the declared type (`TermMaps.widen`'s two directions, read at values), and
the request's binding of the element type is the one the columns keep (`bindTerm_keeps`). -/

/-- **A term row's checked use discharges its store pre.** The use binds the term at the shape's
templates from the request's bindings `σ` (`bindTerm`), and the cell is declared at a type
equivalent to the request's element type. Then the term maps the declared type into the shape's
result at the declared type and the answer type `B` the term bound, at every later world; and
every member of the declared type is a member of the element type the columns are instantiated
at. When the request bound no element type its instance is `never`, the cell's type has no
member, and both hold vacuously: such a node is dead. A step of `denote-typed`; its consumer is
`syncRow_typed` at the eight term rows. It says nothing of a term the checker refuses. -/
theorem bindTerm_termMaps {sig : Signature NativeOp} (hatom : sig.atomOf = nativeAtomTy)
    {w : World} {tys : TyEnv} {env : List Val} (henv : EnvTyped w tys env) {f : Term}
    (s : FnShape) {σ σ' : Ty.Subst}
    (hbind : bindTerm σ (some ⟨s.param, s.result, fun A => termTy sig (tys ++ [A]) f⟩) = .ok σ')
    {ty : Ty} (hequiv : Equiv ty (Ty.instantiate σ (.var 0))) :
    TermMaps w f env ty (Ty.instantiate [(0, ty), (1, Ty.instantiate σ' (.var 1))] s.result) ∧
      ∀ w' a, Fits w' a ty → Fits w' a (Ty.instantiate σ' (.var 0)) := by
  obtain ⟨r, hr, hm⟩ := bindTerm_some_ok hbind
  have hguard := (Bounds.matchB_sound hm).1
  have hparam : (Ty.instantiate σ s.param.normalize).normalize =
      (Ty.instantiate σ (.var 0)).normalize := rfl
  have hmaps : TermMaps w f env (Ty.instantiate σ (.var 0)).normalize r :=
    termMaps_of_typed hatom henv (hparam ▸ hr)
  cases hσ : σ.lookup 0 with
  | none =>
    -- the request bound no element type: the cell's type is below `never`, which has no member
    have hvar : Ty.instantiate σ (.var 0) = .never := by
      simp only [Ty.instantiate, hσ, Option.getD_none]
    have hnever : ∀ w' a, ¬ Fits w' a ty := fun w' a ha => by
      have h := fits_subN w' hequiv.1 a ha
      rw [hvar] at h
      exact h
    exact ⟨fun w' _ a ha => (hnever w' a ha).elim, fun w' a ha => (hnever w' a ha).elim⟩
  | some u =>
    have hσ' : σ'.lookup 0 = some u := bindTerm_keeps hbind 0 u hσ
    have hu : Ty.instantiate σ (.var 0) = u := by
      simp only [Ty.instantiate, hσ, Option.getD_some]
    have hu' : Ty.instantiate σ' (.var 0) = u := by
      simp only [Ty.instantiate, hσ', Option.getD_some]
    rw [hu] at hequiv hmaps
    refine ⟨?_, fun w' a ha => by rw [hu']; exact fits_subN w' hequiv.1 a ha⟩
    intro w' ord a ha
    obtain ⟨x, hx, hfit⟩ :=
      hmaps w' ord a ((fits_normalize w' u a).mpr (fits_subN w' hequiv.1 a ha))
    refine ⟨x, hx, ?_⟩
    -- the guard: the term's value fits the result template's instance at the term's bindings
    have hinst : Fits w' x (Ty.instantiate σ' s.result.normalize) :=
      (fits_normalize w' _ x).mp (fits_sub w' hguard x ((fits_normalize w' r x).mpr hfit))
    -- shape by shape: the instance reads `u` where the store reads the cell's declared type
    cases s with
    | update =>
      have hx' : Fits w' x (Ty.instantiate σ' (.var 0)) := hinst
      rw [hu'] at hx'
      exact fits_subN w' hequiv.2 x hx'
    | updateSome =>
      have hx' : Fits w' x (.option (Ty.instantiate σ' (.var 0))) := hinst
      rw [hu'] at hx'
      rcases fits_option_inv hx' with rfl | ⟨y, rfl, hy⟩
      · exact trivial
      · exact fits_subN w' hequiv.2 y hy
    | modify =>
      have hn : FnShape.modify.result.normalize = .prod (.var 1) (.var 0) := by decide +kernel
      rw [hn] at hinst
      have hx' : Fits w' x (.prod (Ty.instantiate σ' (.var 1)) (Ty.instantiate σ' (.var 0))) :=
        hinst
      rw [hu'] at hx'
      obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w' x _ _).mp hx'
      exact (fits_prod_iff w' _ _ _).mpr ⟨p, q, rfl, hp, fits_subN w' hequiv.2 q hq⟩
    | modifySome =>
      have hn : FnShape.modifySome.result.normalize = .prod (.var 1) (.option (.var 0)) := by
        decide +kernel
      rw [hn] at hinst
      have hx' : Fits w' x (.prod (Ty.instantiate σ' (.var 1))
          (.option (Ty.instantiate σ' (.var 0)))) := hinst
      rw [hu'] at hx'
      obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w' x _ _).mp hx'
      refine (fits_prod_iff w' _ _ _).mpr ⟨p, q, rfl, hp, ?_⟩
      rcases fits_option_inv hq with rfl | ⟨y, rfl, hy⟩
      · exact trivial
      · exact fits_subN w' hequiv.2 y hy

/-- **A checked row use places the request's values under the instance** (the inversion of the
row rule, `checkRow`): the request's bindings `σ` put every member of the request's type under
the row's request at them (the guard, `Bounds.matchB_sound`); the operation's binder term
extends them to `σ'` (`bindTerm`), which only widens (`bindTerm_widens`); the node's columns are
the instance's normal forms at `σ'`, with its formation. A step of `denote-typed` (M5); its
consumers are `syncRow_typed`, `deferredAwait_arm`, `sleep_arm` and `inlineYield_typed`. -/
theorem rowTy_fits {row : Effect4.Program.Row} {reqTy : Ty} {use : Option TermUse} {t : EffTy}
    (h : rowTy row reqTy use = some t) {w : World} {v : Val} (hv : Fits w v reqTy) :
    ∃ σ σ', Fits w v (row.request.normalize.instantiate σ) ∧ bindTerm σ use = .ok σ' ∧
      Ty.Widens σ σ' ∧
      t = ⟨(row.answer.instantiate σ').normalize, (row.error.instantiate σ').normalize,
        Env.Requirement.ofList row.requires⟩ ∧
      Formation.Formed (Formation.instantiatedSites row σ') := by
  rw [rowTy_eq_some_iff] at h
  unfold checkRow at h
  split at h
  · cases h
  · rename_i σ hmatch
    split at h
    · cases h
    · rename_i σ' hbind
      split at h
      · cases h
      · rename_i hformed
        cases h
        refine ⟨σ, σ', ?_, hbind, bindTerm_widens hbind, rfl,
          (Formation.check_eq_none_iff _).mp hformed⟩
        have hsub := (Bounds.matchB_sound hmatch).1
        rw [(Ty.normal_normalize reqTy).fixed] at hsub
        exact (fits_normalize w _ v).mp (fits_sub w hsub v
          ((fits_normalize w reqTy v).mpr hv))

/-- `rowTy_fits` at an operation that carries no binder term: the request's bindings stand. A
step of `denote-typed`; its consumers are `syncRow_typed`'s rows without a term,
`deferredAwait_arm`, `sleep_arm` and `inlineYield_typed`. -/
theorem rowTy_fits_none {row : Effect4.Program.Row} {reqTy : Ty} {t : EffTy}
    (h : rowTy row reqTy none = some t) {w : World} {v : Val} (hv : Fits w v reqTy) :
    ∃ σ, Fits w v (row.request.normalize.instantiate σ) ∧
      t = ⟨(row.answer.instantiate σ).normalize, (row.error.instantiate σ).normalize,
        Env.Requirement.ofList row.requires⟩ ∧
      Formation.Formed (Formation.instantiatedSites row σ) := by
  obtain ⟨σ, σ', hinst, hbind, -, rfl, hformed⟩ := rowTy_fits h hv
  cases hbind
  exact ⟨σ, hinst, rfl, hformed⟩

/-- Every node of a formed site list's type is head-formed at the list's template flag. A step of
`denote-typed`; its consumer is `syncRow_typed`'s `deferredFail` arm, which reads the formation
rule on a deferred's error column at the checked instance (decisions rows 42 and 120). -/
theorem Formation.headFormed_of_nodes {template : Bool} {path : List String} {ty t : Ty}
    (h : Formation.Formed (Formation.sites template path ty)) (ht : t ∈ Formation.nodes ty) :
    Formation.HeadFormed template t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hmem : ((Formation.nodes ty)[i], i) ∈ (Formation.nodes ty).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  exact h _ (List.mem_map_of_mem hmem)

/-- A member of a term row's request, at the request's bindings, is a cell declared at a type
equivalent to the element type the bindings give. A step of `syncRow_typed` at the term rows. -/
theorem fits_termRequest_inv {w : World} {v : Val} {σ : Ty.Subst}
    (h : Fits w v (Ty.instantiate σ (Ty.refOf (.var 0)).normalize.normalize)) :
    ∃ k ty, v = Val.cell k ∧ w.Ρ k = some ty ∧ Equiv ty (Ty.instantiate σ (.var 0)) := by
  have hn : (Ty.refOf (.var 0)).normalize.normalize = .refOf (.var 0) := by decide +kernel
  rw [hn] at h
  obtain ⟨k, rfl, ty, hlookup, hequiv⟩ := fits_refOf_inv h
  exact ⟨k, ty, rfl, hlookup, hequiv⟩

/-- A member of the instance of a row parameter is a member of the node's checked column at that
parameter: the column is the parameter's instance, normalized. A step of `syncRow_typed` at the
term rows that answer the cell's value or `Ref.modify`'s `B`. -/
theorem fits_paramColumn {w : World} {ans : Val} {σ : Ty.Subst} (i : Nat)
    (h : Fits w ans (Ty.instantiate σ (.var i))) :
    Fits w ans (Ty.instantiate σ (Ty.var i).normalize).normalize :=
  (fits_normalize w _ ans).mpr h

/-- **The store rows, per instantiation** (the state plan's T3a and T3b): a request fitting the
checked type of a `sync` row's use decodes to the row's store operation (`NativeOp.syncOpOf`) at
the point's environment, whose pre it meets at a certificate the instance fixes, and whose post
answers at the node's checked columns at every later world. A `Ref` row runs at the cell's
declared type through `refRead`; a read-modify-write row discharges its term's pre from the
term's typing, over an environment that fits the node's (`bindTerm_termMaps`), and `Ref.modify`
certifies at the answer type `B` its term bound, which may differ from the cell's; a
`Deferred.make` declares its promise at its own type arguments' instance; a completion fits the
promise's declared columns, and a failure's value is in the error alphabet by the formation rule on
a deferred's error column. A step of the claims `denote-typed` and `straight-meaning-typed`; its
consumers are `syncPerform_arm`, `inlineYield_typed` and `progress`. It covers native `sync` rows
at every instance and term the checker admits, at every world; it says nothing of a host row
(R6), and one store step is atomic in the model only. -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem syncRow_typed (root : ProgramSource) {w : World} {req : Env.Requirement}
    (op : NativeOp) (hk : NativeOp.kind op = .sync) {env : List Val} {tys : TyEnv}
    (henv : EnvTyped w tys env) {reqTy : Ty} {t : EffTy}
    (hrow : rowTy (NativeOp.row op).normalizeTypes reqTy (root.signature.termUse tys op) = some t)
    (v : Val) (hfit : Fits w v reqTy) :
    ∃ o, NativeOp.syncOpOf op env v = some o ∧
      TypedProg root w ⟨t.answer, t.error, req⟩ (.vis (.inl o) fun ans => .pure (.success ans)) := by
  cases hb : op.binder? with
  | some st =>
    -- the eight term rows: the request is a declared cell, and the term's typing is its pre
    obtain ⟨σ, σ', hinst, hbind, -, rfl, -⟩ := rowTy_fits hrow hfit
    cases op with
    | refUpdateWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, -⟩ := bindTerm_termMaps (sig := root.signature) rfl henv .update hbind hequiv
      refine ⟨SyncOp.refUpdate k f env, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.refUpdate k f env) (cert := ()) ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      subst post
      exact TypedProg.pure (strongExit_success w' _ Val.unit trivial)
    | refGetAndUpdateWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, hcell⟩ :=
        bindTerm_termMaps (sig := root.signature) rfl henv .update hbind hequiv
      refine ⟨SyncOp.refGetAndUpdate k f env, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.refGetAndUpdate k f env) (cert := ())
        ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      obtain ⟨ty, hlookup', hfit'⟩ := post
      rw [ord.1.2.2.2.1 _ _ hlookup] at hlookup'
      cases hlookup'
      exact TypedProg.pure (strongExit_success w' _ ans (fits_paramColumn 0 (hcell w' ans hfit')))
    | refUpdateAndGetWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, hcell⟩ :=
        bindTerm_termMaps (sig := root.signature) rfl henv .update hbind hequiv
      refine ⟨SyncOp.refUpdateAndGet k f env, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.refUpdateAndGet k f env) (cert := ())
        ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      obtain ⟨ty, hlookup', hfit'⟩ := post
      rw [ord.1.2.2.2.1 _ _ hlookup] at hlookup'
      cases hlookup'
      exact TypedProg.pure (strongExit_success w' _ ans (fits_paramColumn 0 (hcell w' ans hfit')))
    | refUpdateSomeWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, -⟩ :=
        bindTerm_termMaps (sig := root.signature) rfl henv .updateSome hbind hequiv
      refine ⟨SyncOp.refUpdateSome k f env, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.refUpdateSome k f env) (cert := ())
        ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      subst post
      exact TypedProg.pure (strongExit_success w' _ Val.unit trivial)
    | refGetAndUpdateSomeWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, hcell⟩ :=
        bindTerm_termMaps (sig := root.signature) rfl henv .updateSome hbind hequiv
      refine ⟨SyncOp.refGetAndUpdateSome k f env, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.refGetAndUpdateSome k f env) (cert := ())
        ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      obtain ⟨ty, hlookup', hfit'⟩ := post
      rw [ord.1.2.2.2.1 _ _ hlookup] at hlookup'
      cases hlookup'
      exact TypedProg.pure (strongExit_success w' _ ans (fits_paramColumn 0 (hcell w' ans hfit')))
    | refUpdateSomeAndGetWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, hcell⟩ :=
        bindTerm_termMaps (sig := root.signature) rfl henv .updateSome hbind hequiv
      refine ⟨SyncOp.refUpdateSomeAndGet k f env, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.refUpdateSomeAndGet k f env) (cert := ())
        ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      obtain ⟨ty, hlookup', hfit'⟩ := post
      rw [ord.1.2.2.2.1 _ _ hlookup] at hlookup'
      cases hlookup'
      exact TypedProg.pure (strongExit_success w' _ ans (fits_paramColumn 0 (hcell w' ans hfit')))
    | refModifyWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, -⟩ := bindTerm_termMaps (sig := root.signature) rfl henv .modify hbind hequiv
      refine ⟨SyncOp.refModify k f env, rfl, ?_⟩
      -- the certificate is the answer type `B` the term bound: it may differ from the cell's
      refine TypedProg.store (op := SyncOp.refModify k f env)
        (cert := Ty.instantiate σ' (.var 1)) ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      exact TypedProg.pure (strongExit_success w' _ ans (fits_paramColumn 1 post))
    | refModifySomeWith f =>
      obtain ⟨k, t', rfl, hlookup, hequiv⟩ := fits_termRequest_inv hinst
      obtain ⟨hmaps, -⟩ :=
        bindTerm_termMaps (sig := root.signature) rfl henv .modifySome hbind hequiv
      refine ⟨SyncOp.refModifySome k f env, rfl, ?_⟩
      -- the certificate is the answer type `B` the term bound: it may differ from the cell's
      refine TypedProg.store (op := SyncOp.refModifySome k f env)
        (cert := Ty.instantiate σ' (.var 1)) ⟨t', hlookup, hmaps⟩ ?_
      intro w' ord ans post
      exact TypedProg.pure (strongExit_success w' _ ans (fits_paramColumn 1 post))
    | refMake | refGet | refSet | refGetAndSet | refSetAndGet | deferredIsDone | deferredPoll
    | deferredSucceed | deferredFail | deferredAwait | scopeMake _ | sleep | clockNow | external _
    | deferredMakeOf _ _ | call _ | param _ => cases hb
  | none =>
  -- the rows without a term: the request's bindings stand
  have huse : root.signature.termUse tys op = none := by
    show (op.binder?.map _).map _ = none
    rw [hb]
    rfl
  rw [huse] at hrow
  obtain ⟨σ, hinst, rfl, hformed⟩ := rowTy_fits_none hrow hfit
  cases op with
  | refUpdateWith f | refGetAndUpdateWith f | refUpdateAndGetWith f | refUpdateSomeWith f
  | refGetAndUpdateSomeWith f | refUpdateSomeAndGetWith f | refModifyWith f
  | refModifySomeWith f => cases hb
  | refMake =>
    refine ⟨SyncOp.refMake v, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refMake v) (cert := Ty.instantiate σ (.var 0)) hinst ?_
    intro w' ord ans post
    obtain ⟨key, rfl, hlookup⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.cell key) ((fits_normalize w' _ _).mpr ?_)
    exact (⟨_, hlookup, Ty.subN_refl _, Ty.subN_refl _⟩ : RefDeclared w' key _)
  | refGet =>
    obtain ⟨k, rfl, hdecl⟩ := fits_refOf_inv hinst
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refGet k, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.refGet k) (cert := ()) ⟨t', hlookup⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ((fits_normalize w' _ _).mpr ?_)
    exact refRead (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refSet =>
    have hn : (NativeOp.row .refSet).request.normalize.normalize =
        .prod (.refOf (.var 0)) (.var 0) := by decide +kernel
    change Fits w v (Ty.instantiate σ (NativeOp.row .refSet).request.normalize.normalize) at hinst
    rw [hn] at hinst
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v _ _).mp hinst
    obtain ⟨k, rfl, hdecl⟩ := fits_refOf_inv hp
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refSet k q, rfl, ?_⟩
    have hq' : Fits w q t' := fits_subN w hequiv.2 q hq
    refine TypedProg.store (op := SyncOp.refSet k q) (cert := ()) ⟨t', hlookup, hq'⟩ ?_
    intro w' ord ans post
    subst post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.cell k) ((fits_normalize w' _ _).mpr ?_)
    exact refDeclared_mono ord ⟨t', hlookup, hequiv⟩
  | refGetAndSet =>
    have hn : (NativeOp.row .refGetAndSet).request.normalize.normalize =
        .prod (.refOf (.var 0)) (.var 0) := by decide +kernel
    change Fits w v (Ty.instantiate σ (NativeOp.row .refGetAndSet).request.normalize.normalize)
      at hinst
    rw [hn] at hinst
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v _ _).mp hinst
    obtain ⟨k, rfl, hdecl⟩ := fits_refOf_inv hp
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refGetAndSet k q, rfl, ?_⟩
    have hq' : Fits w q t' := fits_subN w hequiv.2 q hq
    refine TypedProg.store (op := SyncOp.refGetAndSet k q) (cert := ()) ⟨t', hlookup, hq'⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ((fits_normalize w' _ _).mpr ?_)
    exact refRead (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | refSetAndGet =>
    have hn : (NativeOp.row .refSetAndGet).request.normalize.normalize =
        .prod (.refOf (.var 0)) (.var 0) := by decide +kernel
    change Fits w v (Ty.instantiate σ (NativeOp.row .refSetAndGet).request.normalize.normalize)
      at hinst
    rw [hn] at hinst
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v _ _).mp hinst
    obtain ⟨k, rfl, hdecl⟩ := fits_refOf_inv hp
    obtain ⟨t', hlookup, hequiv⟩ := hdecl
    refine ⟨SyncOp.refSetAndGet k q, rfl, ?_⟩
    have hq' : Fits w q t' := fits_subN w hequiv.2 q hq
    refine TypedProg.store (op := SyncOp.refSetAndGet k q) (cert := ()) ⟨t', hlookup, hq'⟩ ?_
    intro w' ord ans post
    obtain ⟨ty, hlookup', hfit'⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ ans ((fits_normalize w' _ _).mpr ?_)
    exact refRead (refDeclared_mono ord ⟨t', hlookup, hequiv⟩) hlookup' hfit'
  | deferredMakeOf value error =>
    have hv : v = Val.unit := fits_unit_inv hinst
    subst hv
    refine ⟨SyncOp.deferredMake, rfl, ?_⟩
    -- the promise is declared at the instance of the operation's own type arguments
    refine TypedProg.store (op := SyncOp.deferredMake)
      (cert := (Ty.instantiate σ value.normalize, Ty.instantiate σ error.normalize)) trivial ?_
    intro w' ord ans post
    obtain ⟨key, rfl, hlookup⟩ := post
    refine TypedProg.pure ?_
    refine strongExit_success w' _ (Val.promise key) ((fits_normalize w' _ _).mpr ?_)
    exact (⟨_, _, hlookup, ⟨Ty.subN_refl _, Ty.subN_refl _⟩, ⟨Ty.subN_refl _, Ty.subN_refl _⟩⟩ :
      PromiseDeclared w' key _ _)
  | deferredIsDone =>
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredOf_inv hinst
    obtain ⟨a', e', hlookup, _, _⟩ := hdecl
    refine ⟨SyncOp.deferredIsDone k, rfl, ?_⟩
    have hisSome : (w.«Π» k).isSome = true := by rw [hlookup]; rfl
    refine TypedProg.store (op := SyncOp.deferredIsDone k) (cert := ()) hisSome ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    exact strongExit_success w' _ (Val.bool b) trivial
  | deferredPoll =>
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredOf_inv hinst
    obtain ⟨a', e', hlookup, _, _⟩ := hdecl
    refine ⟨SyncOp.deferredPoll k, rfl, ?_⟩
    have hisSome : (w.«Π» k).isSome = true := by rw [hlookup]; rfl
    refine TypedProg.store (op := SyncOp.deferredPoll k) (cert := ()) hisSome ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    exact strongExit_success w' _ (Val.bool b) trivial
  | deferredSucceed =>
    have hn : (NativeOp.row .deferredSucceed).request.normalize.normalize =
        .prod (.deferredOf (.var 0) (.var 1)) (.var 0) := by decide +kernel
    change Fits w v (Ty.instantiate σ (NativeOp.row .deferredSucceed).request.normalize.normalize)
      at hinst
    rw [hn] at hinst
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v _ _).mp hinst
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredOf_inv hp
    obtain ⟨a', e', hlookup, ha, _⟩ := hdecl
    refine ⟨SyncOp.deferredCompleteWith k (.ofExit (.success q)), rfl, ?_⟩
    have hexit : ExitOk w ⟨a', e', Env.Requirement.empty⟩ (.success q) :=
      strongExit_success w _ q (fits_subN w ha.2 q hq)
    refine TypedProg.store (op := SyncOp.deferredCompleteWith k (.ofExit (.success q)))
      (cert := ()) ⟨a', e', hlookup, hexit⟩ ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    exact strongExit_success w' _ (Val.bool b) trivial
  | deferredFail =>
    have hreq : (NativeOp.row .deferredFail).request.normalize =
        .prod (.deferredOf (.var 0) (.var 1)) (.var 1) := by decide +kernel
    -- the formation rule on a deferred's error column, at the checked instance (D4 of the
    -- T3a design): the value a failure carries is in the error alphabet
    have hadm : admittedErrTy (Ty.instantiate σ (.var 1)) = true := by
      have hsites : Formation.Formed (Formation.sites false ["row", "request"]
          (Ty.instantiate σ (.prod (.deferredOf (.var 0) (.var 1)) (.var 1)))) := by
        intro site hs
        apply hformed
        show site ∈ Formation.sites false ["row", "request"]
            (Ty.instantiate σ (NativeOp.row .deferredFail).request.normalize) ++ _ ++ _
        rw [hreq]
        exact List.mem_append_left _ (List.mem_append_left _ hs)
      have hnode : Formation.HeadFormed false
          (.deferredOf (Ty.instantiate σ (.var 0)) (Ty.instantiate σ (.var 1))) :=
        Formation.headFormed_of_nodes hsites
          (List.mem_append_right _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))))
      rcases hnode with h | ⟨h, _⟩
      · exact h
      · cases h
    change Fits w v (Ty.instantiate σ (NativeOp.row .deferredFail).request.normalize.normalize)
      at hinst
    rw [Ty.normalize_idem, hreq] at hinst
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v _ _).mp hinst
    obtain ⟨k, rfl, hdecl⟩ := fits_deferredOf_inv hp
    obtain ⟨a', e', hlookup, _, he⟩ := hdecl
    refine ⟨SyncOp.deferredCompleteWith k (.ofExit (.failure (.fail (errOf q)))), rfl, ?_⟩
    have hexit : ExitOk w ⟨a', e', Env.Requirement.empty⟩ (.failure (.fail (errOf q))) := by
      refine ⟨(fitsExit_failure_iff _ _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
      all_goals
        simp only [Cause.fail, List.mem_singleton] at hr
        subst hr
      · exact ⟨q, valOfErr_errOf_fits hadm hq, fits_subN w he.2 q hq⟩
      · trivial
      · trivial
    refine TypedProg.store
      (op := SyncOp.deferredCompleteWith k (.ofExit (.failure (.fail (errOf q)))))
      (cert := ()) ⟨a', e', hlookup, hexit⟩ ?_
    intro w' ord ans post
    obtain ⟨b, rfl⟩ := post
    refine TypedProg.pure ?_
    exact strongExit_success w' _ (Val.bool b) trivial
  | scopeMake strategy =>
    cases strategy with
    | sequential =>
      have hv : v = Val.unit := fits_unit_inv hinst
      subst hv
      refine ⟨SyncOp.scopeMake .sequential, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.scopeMake .sequential) (cert := ()) trivial ?_
      intro w' ord ans post
      exact TypedProg.pure (strongExit_success w' _ ans ((fits_normalize w' _ _).mpr post))
    | parallel =>
      have hv : v = Val.unit := fits_unit_inv hinst
      subst hv
      refine ⟨SyncOp.scopeMake .parallel, rfl, ?_⟩
      refine TypedProg.store (op := SyncOp.scopeMake .parallel) (cert := ()) trivial ?_
      intro w' ord ans post
      exact TypedProg.pure (strongExit_success w' _ ans ((fits_normalize w' _ _).mpr post))
  | clockNow =>
    have hv : v = Val.unit := fits_unit_inv hinst
    subst hv
    refine ⟨SyncOp.clockNow, rfl, ?_⟩
    refine TypedProg.store (op := SyncOp.clockNow) (cert := ()) trivial ?_
    intro w' ord ans post
    obtain ⟨n, rfl⟩ := post
    refine TypedProg.pure ?_
    exact strongExit_success w' _ (Val.nat n) trivial
  | deferredAwait => cases hk
  | sleep => cases hk
  | external _ => cases hk
  | call _ => cases hk
  | param _ => cases hk

/-- A built-in operation reads its own row; only a host operation reads the table. -/
theorem nativeRowOf_builtin (table : RowTable) {op : NativeOp}
    (hk : NativeOp.kind op ≠ .program) : nativeRowOf table op = op.row := by
  cases op with
  | external i => exact absurd rfl hk
  | _ => rfl

/-- A store row is not a host row. -/
theorem kind_ne_program_of_sync {op : NativeOp} (h : NativeOp.kind op = .sync) :
    NativeOp.kind op ≠ .program := by
  rw [h]
  decide

/-- The checker's order places a type below its double normal form. -/
theorem subN_normalize₂ {a b : Ty} (h : Ty.subN a b = true) :
    Ty.subN a b.normalize.normalize = true := by
  rw [Ty.subN_normalize_right, Ty.subN_normalize_right]
  exact h

/-- The checker's order places a type below its normal form: a step of `deferredAwait_arm`,
which widens a promise's declared columns to the node's instance. -/
theorem subN_normalize₁ {a b : Ty} (h : Ty.subN a b = true) : Ty.subN a b.normalize = true := by
  rw [Ty.subN_normalize_right]
  exact h

section PerformArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy}

/-- **A checked built-in `perform`**: its request evaluates to a value fitting the request's
checked type, and the node's type is the row's check at that type (`rowTy`), which each arm reads
through `rowTy_fits`. A step of `denote-typed`; its consumers are `syncPerform_arm`,
`deferredAwait_arm`, `sleep_arm` and `inlineYield_typed`. -/
theorem builtinPerform_inv {op : NativeOp} {r : Term} {q : Point} {t : EffTy}
    (hk : NativeOp.kind op ≠ .program)
    (hat : Node.at_ (.eff root.program) q.path = some (.eff (.perform op r)))
    (hpt : PointTyped root w q t) :
    ∃ tys v reqTy, EnvTyped w tys q.env ∧ evalTerm q.env r = some v ∧ Fits w v reqTy ∧
      rowTy (NativeOp.row op).normalizeTypes reqTy (root.signature.termUse tys op) = some t := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨reqTy, -, hreq, hrow⟩ := Checker.inv_perform _ _ _ _ _ _ hcheck
  obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hreq
  -- a built-in row is no invocation, so the block's signature reads the tables' row there
  have hnone : root.sig.signature.callOf op = none := by
    cases op with
    | call _ => exact (hk rfl).elim
    | _ => rfl
  have hrowOf : root.signature.rowOf op = (NativeOp.row op).normalizeTypes := by
    show (root.sig.signature.withDefs root.program.defsOf).rowOf op = _
    rw [root.sig.signature.withDefs_rowOf_of_none _ hnone]
    show (nativeRowOf root.table op).normalizeTypes = _
    rw [nativeRowOf_builtin root.table hk]
  -- nor a parameter's run, so every scope reads the source's row there
  have hpnone : root.signature.paramOf op = none := by
    cases op with
    | param _ => exact (hk rfl).elim
    | _ => rfl
  rw [(root.scopeSig_of_none q.path hpnone).2, (root.scopeSig_extends q.path).termUse,
    hrowOf] at hrow
  exact ⟨env, v, reqTy, henv, hv, hvfit, hrow⟩

/-- Native source sync rows never register a foreign capture.
Consumer: the ambient source sync arm; acquireIn registers through its explicit capture producer. -/
theorem syncOpOf_not_foreign_scopeAdd (op : NativeOp) (env : List Val) (value : Val)
    (scope : Nat) (capture : Capture) :
    NativeOp.syncOpOf op env value ≠ some (.scopeAdd scope (.foreign capture)) := by
  fun_cases NativeOp.syncOpOf op env value <;> exact nofun

/-- **A `perform` at a `sync` built-in row**: the store operation at the node's checked instance
(`syncRow_typed`). The consumer of the reference-read card. -/
theorem syncPerform_arm {available : Env.Requirement} {op : NativeOp} {r : Term} (hk : NativeOp.kind op = .sync)
    (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform op r)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.perform op r) p) := by
  obtain ⟨tys, v, reqTy, henv, hv, hfit, hrow⟩ :=
    builtinPerform_inv (by rw [hk]; exact nofun) hat hpt
  obtain ⟨o, ho, htyped⟩ := syncRow_typed root (req := ty.requires) op hk henv hrow v hfit
  rw [denoteR_perform_sync _ _ _ hfuel ((NativeOp.row_kind op).trans hk), hv, Option.bind_some, ho]
  exact ambient_storeR_of_typed root available (fun scope capture identity =>
    syncOpOf_not_foreign_scopeAdd op p.env v scope capture (identity ▸ ho)) htyped

/-- **`Deferred.await`**: the registration on the request's deferred, met at the deferred's
declared columns (`asyncPre`), which are equivalent to the instance's in the checker's order. -/
theorem deferredAwait_arm {available : Env.Requirement} {r : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform .deferredAwait r)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.perform .deferredAwait r) p) := by
  obtain ⟨_, v, reqTy, -, hv, hfit, hrow⟩ := builtinPerform_inv (by decide) hat hpt
  obtain ⟨σ, hinst, rfl, -⟩ := rowTy_fits_none hrow hfit
  obtain ⟨k, rfl, a', e', hPi, ⟨ha, -⟩, ⟨he, -⟩⟩ := fits_deferredOf_inv hinst
  rw [denoteR_perform _ _ _ hfuel]
  change AmbientProg root w available _ (denoteAsync r p)
  unfold denoteAsync
  rw [hv]
  exact ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ⟨a', e', Env.Requirement.empty⟩
    ⟨a', e', hPi, Ty.sub_refl _, Ty.sub_refl _⟩
    (fun w' _ ans post => .pure ⟨exitOk_widen (subN_normalize₁ ha) (subN_normalize₁ he) post,
      by cases ans <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **`Effect.sleep`**: no time is the counted yield, answering `unit`; a positive time the
timer's registration, met at `(unit, never)`. -/
theorem sleep_arm {available : Env.Requirement} {r : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform .sleep r)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.perform .sleep r) p) := by
  obtain ⟨_, v, reqTy, -, hv, hfit, hrow⟩ := builtinPerform_inv (by decide) hat hpt
  obtain ⟨σ, hinst, rfl, -⟩ := rowTy_fits_none hrow hfit
  obtain ⟨n, rfl⟩ := fits_nat_inv hinst
  rw [denoteR_perform _ _ _ hfuel]
  change AmbientProg root w available _ (denoteSleep r p)
  unfold denoteSleep
  rw [hv, Option.bind_some]
  cases n with
  | zero =>
    change AmbientProg root w available _ (.vis (.inr (.yieldNow 0)) fun v => .pure (.success v))
    refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => ?_) ⟨Row.subset_refl _, Row.subset_refl _⟩
    have hans : ans = Val.unit := post
    subst hans
    exact .pure ⟨strongExit_success w' _ _ trivial, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  | succ n =>
    change AmbientProg root w available _ (.vis (.inr (.async (.store (.registerSleep (ClockMillis.ofNat (n + 1))))
      (Val.nat (n + 1)))) Effects.Program.pure)
    exact ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (EffTy.pure .unit) (Ty.sub_refl _)
      (fun w' _ ans post => .pure ⟨exitOk_widen (Ty.subN_refl _) (Ty.subN_refl _) post,
        by cases ans <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **A host row** (`perform (.external i)`): the host registration, its certificate the node's
checked type, the row's instance at the request (`bitEntry` at that instance by reflexivity,
decisions row 183). A host answer admitted at the certificate is admitted at the node's type, with
no bridge through the template. A step of `denote-typed`; its consumer is `perform_arm`. -/
theorem external_arm {available : Env.Requirement} {i : Nat} {request : Term} (hfuel : p.fuel ≠ 0)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform (.external i) request)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.perform (.external i) request) p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨requestTy, hdom, hreq, hrow⟩ :=
    Checker.inv_perform _ env p.path (NativeOp.external i) request ty hcheck
  rw [(root.scopeSig_of_none p.path (op := .external i) rfl).1] at hdom
  rw [(root.scopeSig_of_none p.path (op := .external i) rfl).2,
    (root.scopeSig_extends p.path).termUse] at hrow
  obtain ⟨v, hv, -⟩ := evalTerm_progress_env henv hreq
  rw [denoteR_perform _ _ _ hfuel]
  show AmbientProg root w available (ty, available, available) (denoteForeign (.external i) request p)
  unfold denoteForeign
  rw [hv]
  have hbit : bitEntry root (.external i) ty :=
    ⟨hdom, requestTy, ty, hrow, Ty.sub_refl _, Ty.sub_refl _⟩
  refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) ty hbit ?_ ⟨Row.subset_refl _, Row.subset_refl _⟩
  intro w' ord ans post
  exact .pure ⟨post, by cases ans <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- **No point of an admitted program is a definition block**: the checker refuses a block below
the whole module's root (`TypeReason.definitionBlock`), so no point's check answers there. -/
theorem defs_not_typed {decls : List DefDecl} {bodies : Effs NativeOp} {main : NativeEff}
    {q : Point} {t : EffTy}
    {layers : LayerTerms NativeOp}
    (hat : Node.at_ (.eff root.program) q.path = some (.eff (.defs decls bodies main layers)))
    (hpt : PointTyped root w q t) : False := by
  obtain ⟨env, hcheck, -, -, -⟩ := hpt.at_node hat
  obtain ⟨bodies', main', layers', heq⟩ :=
    Eff.expandIn_defs_head (root := root.program) decls bodies main layers
  rw [heq] at hcheck
  exact nomatch hcheck

/-- **An invocation** (decisions row 328, goal G3; the arm of `denote-typed`): the counted step,
then the definition's body at its path, its one variable the request's value. The checker types
the invocation by the definition's declared row (`invoke_hasTy`), which the declaration's
formation keeps closed: the request's value fits the declared request and the node's type is the
declared columns (`rowTy_closed_some`). The body is typed at its point by the block's typing
(`BodiesTyped`), one unit of fuel lighter (`Point.redirect`), and its type widens to the declared
columns (`DefDecl.admits`). Its consumer is `perform_arm`. -/
theorem call_arm {available : Env.Requirement} {k : Nat} {r : Term} {f : Nat} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform (.call k) r)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hbodies : BodiesTyped root)
    (hden : ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f c path)
    (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.perform (.call k) r) p) := by
  obtain ⟨env, hcheck, henv, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨reqTy, hdom, hreq, hrow⟩ := Checker.inv_perform _ _ _ _ _ _ hcheck
  -- an invocation runs no parameter, so every scope reads the source's row there
  rw [(root.scopeSig_of_none p.path (op := .call k) rfl).1] at hdom
  rw [(root.scopeSig_of_none p.path (op := .call k) rfl).2,
    (root.scopeSig_extends p.path).termUse] at hrow
  -- the block declares definition `k`, which takes no program, and the invocation reads its row
  obtain ⟨d, hd, hparams⟩ := root.sig.signature.withDefs_dom_call_some _ rfl hdom
  have hrowOf : root.signature.rowOf (.call k) = d.row.normalizeTypes :=
    root.sig.signature.withDefs_rowOf_call _ rfl hd
  rw [hrowOf] at hrow
  obtain ⟨path, body, tb, hpath, hbody, hbcheck, hformed, hadmits⟩ := hbodies k d hd
  -- a body with no parameter has no parameter in scope: it is checked at the source's own
  -- signature, and any stack is typed there
  have hscope : scopeParams root.program path = [] := (scopeParams_body hpath hd).trans hparams
  have hbcheck' : Checker.check (root.scopeSig path) [d.request.normalize] path
      (Eff.expandIn root.program body) = .ok tb := by
    unfold ProgramSource.scopeSig
    rw [hscope, ← hparams]
    exact hbcheck
  simp only [DefDecl.formed, Bool.and_eq_true] at hformed
  obtain ⟨⟨⟨⟨hreqc, hansc⟩, herrc⟩, -⟩, -⟩ := hformed
  obtain ⟨hsub, rfl⟩ := rowTy_closed_some (row := d.row.normalizeTypes)
    (Ty.closed_normalize _ hreqc) (Ty.closed_normalize _ hansc) (Ty.closed_normalize _ herrc) hrow
  simp only [DefDecl.admits, Bool.and_eq_true] at hadmits
  obtain ⟨⟨hans, herr⟩, required⟩ := hadmits
  have bodyCovered : Row.Subset tb.requires available :=
    Row.subset_trans (of_decide_eq_true required) coverage
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hreq
  rw [denoteR_perform _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_suspendR_typed root (Row.subset_refl _) (fun w' o =>
    ambient_constructR_typed root (Row.subset_refl _) (fun w'' o' completed hc => ?_))
  have o'' := leHost_trans _ _ _ o o'
  simp only [hv, hpath, hbody]
  -- the body at its point, typed at its own type, widened to the declared columns
  refine ambientProg_widen root (before := (tb, available, available))
    (after := ((⟨d.row.normalizeTypes.answer.normalize, d.row.normalizeTypes.error.normalize,
      Env.Requirement.ofList d.row.normalizeTypes.requires⟩ : EffTy), available, available)) ?_ ?_
    (Row.subset_refl _) (Row.subset_refl _) (hden body path hbody w''
    (serviceTy_leHost o'' htie) { p.redirect path with completed, env := [v], call := p.path :: p.call } tb (by simp only [Point.redirect, hfuel]; rfl) rfl
    ⟨body, [d.request.normalize], hbody, hbcheck', ?_, hc, ?_⟩ available bodyCovered ?_)
  · show Ty.sub tb.answer.normalize d.answer.normalize.normalize.normalize = true
    rw [Ty.normalize_idem, Ty.normalize_idem]
    exact hans
  · show Ty.sub tb.error.normalize d.error.normalize.normalize.normalize = true
    rw [Ty.normalize_idem, Ty.normalize_idem]
    exact herr
  · have hreqFit : Fits w'' v d.request.normalize :=
      fits_subN w'' (show Ty.sub reqTy.normalize d.request.normalize.normalize = true from hsub)
        v (fits_mono o'' hfit)
    exact envTyped_append (envTyped_nil w'') hreqFit
  · show StackTyped root w'' (scopeParams root.program path) p.params
    rw [hscope]
    exact stackTyped_nil root w'' _
  · show AmbientStackTyped root w'' available (scopeParams root.program path) p.params
    rw [hscope]
    exact ambientStackTyped_nil root w'' available _

/-- **A hop to a checked node** (slice CX2, `docs/research/2026-10-10-cx-lexical-scope.md` §5):
a point whose node the checker types at its scope's signature, with typed values, view and stack,
denotes a typed program at that type, widened to any bound above it. The shared tail of the arms
that move the run to another node of the root: `invoke_arm` to a body, `param_arm` to a site. -/
theorem hop_typed {root : ProgramSource} {f : Nat} {available : Env.Requirement}
    (hden : ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f c path)
    {w : World} (htie : w.serviceTy = root.sig.serviceTy) {q : Point} {node : NativeEff}
    {env : List Ty} {t T : EffTy} (hfuel : q.fuel = f)
    (hat : Node.at_ (.eff root.program) q.path = some (.eff node))
    (hcheck : Checker.check (root.scopeSig q.path) env q.path (Eff.expandIn root.program node) =
      .ok t)
    (henv : EnvTyped w env q.env)
    (hview : ∀ r ∈ q.completed, ∃ fty, w.Γ r.1 = some fty ∧ ExitOk w fty r.2)
    (hstack : AmbientStackTyped root w available (scopeParams root.program q.path) q.params)
    (hans : Ty.subN t.answer T.answer = true) (herr : Ty.subN t.error T.error = true)
    (covered : Row.Subset t.requires available) :
    AmbientProg root w available (T, available, available) (denoteR root.program node q) :=
  ambientProg_widen root (before := (t, available, available))
    (after := (T, available, available)) hans herr (Row.subset_refl _) (Row.subset_refl _)
    (hden node q.path hat w htie q t hfuel rfl
      ⟨node, env, hat, hcheck, henv, hview, ambientStackTyped_erases hstack⟩
      available covered hstack)

/-- **A parameter's run in a scope's domain reads its parameter's row** (`Signature.withParams_param`
at the source's signature, which keeps every run outside its domain). A step of `param_arm`. -/
theorem ProgramSource.scopeSig_param (src : ProgramSource) (path : List Nat) {i : Nat}
    (hd : (src.scopeSig path).dom (.param i) = true) :
    ∃ q, (scopeParams src.program path)[i]? = some q ∧
      (src.scopeSig path).rowOf (.param i) = q.row.normalizeTypes :=
  Signature.withParams_param src.signature (scopeParams src.program path) (op := NativeOp.param i)
    (i := i) rfl (src.signature_paramsOutside _ i rfl) hd

/-- **A parameter in scope is formed**: the scope is some declaration's parameters
(`scopeParams_decl`), and a typed block's declarations are formed (`BodiesTyped`), each
parameter with them (`DefDecl.formed`). A step of `param_arm`. -/
theorem paramFormed_of_scope {root : ProgramSource} (hbodies : BodiesTyped root) {path : List Nat}
    {i : Nat} {q : ParamDecl} (hq : (scopeParams root.program path)[i]? = some q) :
    q.formed = true := by
  rcases scopeParams_decl root.program path with h0 | ⟨k, d, hd, hps⟩
  · rw [h0, List.getElem?_nil] at hq
    cases hq
  · obtain ⟨-, -, -, -, -, -, hformed, -⟩ := hbodies k d hd
    rw [hps] at hq
    simp only [DefDecl.formed, Bool.and_eq_true] at hformed
    exact List.all_eq_true.mp hformed.2 q (List.mem_of_getElem? hq)

/-- **A parameter's run** (decisions row 340; the arm of `denote-typed`): the counted step, then
the site that the innermost invocation passed for parameter `i`, its values extended by the
request's value, at the stack below that invocation (`denoteR`'s `param` arm). The point's
scope holds parameter `i` (`ProgramSource.scopeSig_param`), formed with its declaration
(`paramFormed_of_scope`), so the request fits the parameter's request and the node's type is the
parameter's columns (`rowTy_closed_some`). The stack's top frame holds a site typed at the
parameter (`StackTyped`), so the site's program is typed at its own point, with the caller's
values and the stack below, and widens to the parameter's columns (`hop_typed`). Placed in
slice CX1 (`docs/research/2026-10-10-cx-lexical-scope.md` §9), proved in CX2. Its consumer is
`perform_arm`. -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem param_arm {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {i : Nat}
    {r : Term} {f : Nat} {available : Env.Requirement} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform (.param i) r)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hbodies : BodiesTyped root)
    (hden : ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f c path)
    (saved : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.perform (.param i) r) p) := by
  obtain ⟨env, hcheck, henv, -, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨reqTy, hdom, hreq, hrow⟩ := Checker.inv_perform _ _ _ _ _ _ hcheck
  -- the scope holds parameter `i`, whose declaration's row the run reads
  obtain ⟨q, hq, hrowOf⟩ := root.scopeSig_param p.path hdom
  rw [hrowOf, (root.scopeSig_extends p.path).termUse] at hrow
  have hformed := paramFormed_of_scope hbodies hq
  simp only [ParamDecl.formed, Bool.and_eq_true] at hformed
  obtain ⟨⟨⟨hreqc, hansc⟩, herrc⟩, -⟩ := hformed
  obtain ⟨hsub, rfl⟩ := rowTy_closed_some (row := q.row.normalizeTypes)
    (Ty.closed_normalize _ hreqc) (Ty.closed_normalize _ hansc) (Ty.closed_normalize _ herrc) hrow
  -- the stack's top frame holds the site of parameter `i`
  obtain ⟨top, rest, hparams⟩ : ∃ top rest, p.params = top :: rest := by
    cases hp : p.params with
    | nil =>
      rw [hp] at hstack
      have hnil : scopeParams root.program p.path = [] := hstack
      rw [hnil, List.getElem?_nil] at hq
      cases hq
    | cons top rest => exact ⟨top, rest, rfl⟩
  rw [hparams] at saved
  obtain ⟨site, arg, envs, t, hsite, hnode, hacheck, hadm, henvs, hrest⟩ := saved i q hq
  obtain ⟨hadm, required⟩ := hadm
  simp only [ParamDecl.admits, Bool.and_eq_true] at hadm
  obtain ⟨hans, herr⟩ := hadm
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hreq
  rw [denoteR_perform _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_suspendR_typed root (Row.subset_refl _) (fun w' o =>
    ambient_constructR_typed root (Row.subset_refl _) (fun w'' o' completed hc => ?_))
  have o'' := leHost_trans _ _ _ o o'
  simp only [hv, hparams, hsite, hnode]
  -- the site's program at its own point, at the caller's values and the stack below the call
  refine hop_typed hden (serviceTy_leHost o'' htie) (t := t)
    (by simp only [Point.redirect, hfuel]; rfl) hnode hacheck ?_ hc (ambientStackTyped_mono o'' hrest) ?_ ?_ required
  · have hreqFit : Fits w'' v q.request.normalize :=
      fits_subN w'' (show Ty.sub reqTy.normalize q.request.normalize.normalize = true from hsub)
        v (fits_mono o'' hfit)
    exact envTyped_append (envTyped_mono o'' henvs) hreqFit
  · show Ty.sub t.answer.normalize q.answer.normalize.normalize.normalize = true
    rw [Ty.normalize_idem, Ty.normalize_idem]
    exact hans
  · show Ty.sub t.error.normalize q.error.normalize.normalize.normalize = true
    rw [Ty.normalize_idem, Ty.normalize_idem]
    exact herr

/-- **`perform`**: a host row, the two asynchronous built-in rows, a store row, an invocation
(`call_arm`), which reads the block's typing and the induction at the body's point, or a
parameter's run (`param_arm`). -/
theorem perform_arm {available : Env.Requirement} {op : NativeOp} {r : Term} {f : Nat} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.perform op r)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hbodies : BodiesTyped root)
    (hden : ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f c path)
    (coverage : Row.Subset ty.requires available)
    (saved : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.perform op r) p) := by
  have hpos : p.fuel ≠ 0 := by rw [hfuel]; exact Nat.succ_ne_zero f
  cases op with
  | external i => exact external_arm hpos hat hpt
  | call k => exact call_arm hfuel hat hpt htie hbodies hden coverage
  | param i => exact param_arm hfuel hat hpt htie hbodies hden saved
  | deferredAwait => exact deferredAwait_arm hpos hat hpt
  | sleep => exact sleep_arm hpos hat hpt
  | _ => exact syncPerform_arm rfl hpos hat hpt

/-- **The frame an invocation pushes is typed at its definition's parameters** (K4, slice CX2;
`docs/research/2026-10-10-cx-lexical-scope.md` §9): each program the invocation passes stands at
its site below the invocation, so at the invocation's scope; the checker types it there over the
caller's environment extended by its parameter's request, at a type the parameter admits
(`Checker.inv_effs_slot`); the caller's values fit the caller's environment; and the stack below
is typed at the caller's scope. The conclusion is `StackTyped`'s clause for the pushed frame.
Private: the spine's rounds (`effsRounds`) are no definition of the tree. A step of
`invoke_arm`. -/
private theorem argSites_typed {root : ProgramSource} {w : World} {env : List Ty}
    {vals : List Val} {base : List Nat} {stack : List (List ArgSite)}
    (henv : EnvTyped w env vals) (hstack : StackTyped root w (scopeParams root.program base) stack) :
    ∀ (qs : List ParamDecl) (args : Effs NativeOp) (spine : List Nat) (T : EffTy),
      (∀ x, spine <+: x → scopeParams root.program x = scopeParams root.program base) →
      Node.at_ (.eff root.program) spine = some (.effs args) →
      qs.length = (effsRounds (Node.eff root.program)
        (List.range ((root.program.refSites []).length + 1)) args).toList.length →
      Checker.checkEffs (root.scopeSig base) env spine qs
          (effsRounds (Node.eff root.program)
            (List.range ((root.program.refSites []).length + 1)) args) = .ok T →
      ∀ (j : Nat) (q : ParamDecl), qs[j]? = some q →
        ∃ (site : ArgSite) (arg : NativeEff) (env' : List Ty) (t : EffTy),
          (argSitesAt spine vals args)[j]? = some site ∧
          Node.at_ (.eff root.program) site.path = some (.eff arg) ∧
          Checker.check (root.scopeSig site.path) (env' ++ [q.request.normalize]) site.path
            (Eff.expandIn root.program arg) = .ok t ∧
          q.admits t = true ∧ EnvTyped w env' site.env ∧
          StackTyped root w (scopeParams root.program site.path) stack
 := by
  intro parameters arguments path result scope node count checked
  exact argument_certificates (fun parameter type => parameter.admits type = true)
    henv hstack parameters arguments path result scope node count checked
    (fun _ _ admitted _ => admitted)

/-- **An invocation with programs** (decisions row 340; the arm of `denote-typed`): the counted
step, then the definition's body at its path, its one variable the request's value, and the
sites of the call's programs pushed on the point's stack (`denoteR_invoke`). The checker types
the invocation by the definition's declared row (`Checker.inv_invoke`), which the declaration's
formation keeps closed, so the request fits the declared request and the node's type is the
declared columns (`rowTy_closed_some`). The body has the definition's parameters in scope
(`scopeParams_body`), so the block's typing types it at its point (`BodiesTyped`); the frame
pushed is typed at those parameters (`argSites_typed`); and the body widens to the declared
columns (`hop_typed`, `DefDecl.admits`). Placed as goal G3's successor in slice HO-1, proved in
CX2 (`docs/research/2026-10-10-cx-lexical-scope.md` §9). Its consumer is `denote-typed`'s
dispatch (`childDenotes_upto`). -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem invoke_arm {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {k : Nat}
    {r : Term} {args : Effs NativeOp} {f : Nat} {available : Env.Requirement} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.invoke k r args)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hbodies : BodiesTyped root)
    (hden : ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f c path)
    (coverage : Row.Subset ty.requires available)
    (saved : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.invoke k r args) p) := by
  obtain ⟨env, hcheck, henv, -, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_invoke] at hcheck
  obtain ⟨d, reqTy, t0, ts, hdef, -, hlen, hreq, hrow, hargs, rfl⟩ :=
    Checker.inv_invoke _ _ _ _ _ _ _ hcheck
  -- the invoked definition is the block's (`Signature.withDefs`)
  rw [root.scopeSig_defOf] at hdef
  have hd : root.program.defsOf[k]? = some d := by
    have h' : (root.program.defsOf[k]?).or (root.sig.signature.defOf k) = some d := hdef
    rw [show root.sig.signature.defOf k = none from rfl, Option.or_none] at h'
    exact h'
  obtain ⟨path, body, tb, hpath, hbody, hbcheck, hformed, hadmits⟩ := hbodies k d hd
  -- the body has the definition's parameters in scope
  have hscope : scopeParams root.program path = d.params := scopeParams_body hpath hd
  have hbcheck' : Checker.check (root.scopeSig path) [d.request.normalize] path
      (Eff.expandIn root.program body) = .ok tb := by
    unfold ProgramSource.scopeSig
    rw [hscope]
    exact hbcheck
  simp only [DefDecl.formed, Bool.and_eq_true] at hformed
  obtain ⟨⟨⟨⟨hreqc, hansc⟩, herrc⟩, -⟩, -⟩ := hformed
  obtain ⟨hsub, rfl⟩ := rowTy_closed_some (row := d.row.normalizeTypes)
    (Ty.closed_normalize _ hreqc) (Ty.closed_normalize _ hansc) (Ty.closed_normalize _ herrc) hrow
  simp only [DefDecl.admits, Bool.and_eq_true] at hadmits
  obtain ⟨⟨hans, herr⟩, bodyRequired⟩ := hadmits
  obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hreq
  -- the frame the invocation pushes, typed at the definition's parameters
  have hframe : AmbientStackTyped root w available d.params (argSitesAt (p.path ++ [0]) p.env args :: p.params) :=
    ambient_argument_birth henv saved d.params args (p.path ++ [0]) ts
      (fun x hx => scopeParams_prefix hat (fun _ _ _ _ h => nomatch h)
        ((List.prefix_append _ _).trans hx))
      (node_at_child hat rfl) hlen hargs
      (Row.subset_trans (Row.subset_union_right _ _) coverage)
  rw [denoteR_invoke _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  refine ambient_suspendR_typed root (Row.subset_refl _) (fun w' o =>
    ambient_constructR_typed root (Row.subset_refl _) (fun w'' o' completed hc => ?_))
  have o'' := leHost_trans _ _ _ o o'
  simp only [hv, hpath, hbody]
  -- the body at its point, typed at its own type, widened to the declared columns
  refine hop_typed hden (serviceTy_leHost o'' htie) (t := tb)
    (by simp only [Point.redirect, hfuel]; rfl) hbody hbcheck' ?_ hc ?_ ?_ ?_
    (Row.subset_trans (of_decide_eq_true bodyRequired)
      (Row.subset_trans (Row.subset_union_left _ _) coverage))
  · have hreqFit : Fits w'' v d.request.normalize :=
      fits_subN w'' (show Ty.sub reqTy.normalize d.request.normalize.normalize = true from hsub)
        v (fits_mono o'' hfit)
    exact envTyped_append (envTyped_nil w'') hreqFit
  · show AmbientStackTyped root w'' available (scopeParams root.program path)
      (argSitesAt (p.path ++ [0]) p.env args :: p.params)
    rw [hscope]
    exact ambientStackTyped_mono o'' hframe
  · show Ty.sub tb.answer.normalize d.answer.normalize.normalize.normalize = true
    rw [Ty.normalize_idem, Ty.normalize_idem]
    exact hans
  · show Ty.sub tb.error.normalize d.error.normalize.normalize.normalize = true
    rw [Ty.normalize_idem, Ty.normalize_idem]
    exact herr

end PerformArms

/-! ### Services -/

/-- **A lawful source's service carriers are flat**: the reserved `Scope` key's carrier, a
declaration's (`serviceChecks`' flatness check, `LawfulSig.services`), or a built-in code's. -/
theorem serviceTy_flat (root : ProgramSource) (key : ServiceKey) (sty : Ty)
    (hsty : root.signature.serviceTy key = some sty) :
    flatCarrier sty = true := by
  have hsig : root.signature.serviceTy = root.sig.serviceTy := rfl
  rw [hsig] at hsty
  unfold SigApp.serviceTy at hsty
  split at hsty
  · rename_i entry hentry
    have hmem := List.mem_of_find?_eq_some hentry
    simp only [nativeReservedServiceTypes, List.mem_singleton] at hmem
    injection hmem with _ henty
    subst henty
    injection hsty with hsty'
    subst hsty'
    decide
  · split at hsty
    · exact nomatch hsty
    · split at hsty
      · rename_i ty hcode
        unfold SigApp.codeTy at hcode
        cases hfind : root.sig.services.find? (fun entry => entry.1.service == key.service) with
        | none =>
          rw [hfind] at hcode
          exact nomatch hcode
        | some entry =>
          rw [hfind] at hcode
          simp only [Option.map_some] at hcode
          injection hcode with hcode'
          subst hcode'
          injection hsty with hsty'
          subst hsty'
          have hmem := List.mem_of_find?_eq_some hfind
          have hsvc := root.lawful.services entry hmem
          have hc1 : (flatCarrier entry.2, ServiceReason.nonFlatCarrier) ∈ serviceChecks entry := by
            simp only [serviceChecks, List.mem_cons]
            exact Or.inr (Or.inl trivial)
          exact hsvc _ hc1
      · unfold SigApp.builtinCodeTy at hsty
        cases hfind : nativeServiceTypes.find? (fun entry => entry.1 == key.service.value) with
        | none =>
          rw [hfind] at hsty
          exact nomatch hsty
        | some entry =>
          rw [hfind] at hsty
          simp only [Option.map_some] at hsty
          injection hsty with hsty'
          subst hsty'
          have hmem := List.mem_of_find?_eq_some hfind
          have hall : ∀ e ∈ nativeServiceTypes, flatCarrier e.2 = true := by decide
          exact hall entry hmem

/-- A context's services fit at every later world. -/
theorem servicesFit_mono {w w' : World} (ord : w.leHost w') {ctx : Env.Ctx}
    (h : ServicesFit w ctx) : ServicesFit w' ctx :=
  servicesFit_map ord.1.2.1 ord.1.2.2.1 ord.1.2.2.2.1 ord.2 ord.1.1.2
    (serviceTy_of_le ord.1) h

/-- The context set, at a context whose services fit, answers `unit`. -/
theorem setContext_typed (root : ProgramSource) {w : World} {ctx : Ctx}
    (h : ServicesFit w ctx.services) :
    TypedProg root w (EffTy.pure .unit) (fiberValR (.setContext ctx) rfl) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () h (fun _ _ _ post => unitAnswer_typed root post)

section ServiceArms

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`service`**: the context read, then the binding at the key, which fits the key's carrier
(`ServicesFit`, the world's table being the source's), or the missing-service defect, which the
part-one exclusion admits; the defect is not a successful service value. -/
theorem service_arm {available : Env.Requirement} {key : ServiceKey} (hfuel : p.fuel ≠ 0)
    (htie : w.serviceTy = root.sig.serviceTy)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.service key)))
    (hpt : PointTyped root w p ty) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.service key) p) := by
  obtain ⟨env, hcheck, -, -, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_of_round _ _ rfl] at hcheck
  obtain ⟨sty, hsty, rfl⟩ := Checker.inv_service _ env p.path key ty hcheck
  rw [root.scopeSig_serviceTy] at hsty
  rw [denoteR_service _ _ hfuel]
  refine ambient_guardBind root (ambient_captureContext_typed root w available)
    (fun later ordered exit arm payload => ?_) (fun later ordered exit payload absent => ?_)
    (Row.subset_refl _)
  · cases exit with
    | failure cause => exact Bool.noConfusion arm
    | success value =>
      obtain ⟨ctx, decoded, members⟩ := fits_context_inv payload.1.1
      have same : value = Val.context ctx := Val.context?_exact decoded
      subst value
      have captured := ambient_captured_context payload
      have bound : Row.Subset available ctx.services.keysRow :=
        (Provision.satisfies_iff_subset_keysRow _ available).mp captured.2
      simp only [seqR, ambientInput, Val.context?_context]
      unfold serviceLookupR
      rw [Val.context?_context]
      dsimp only
      cases found : ctx.services.getV key with
      | some val =>
        have declared : later.serviceTy key = some sty := by
          rw [serviceTy_leHost ordered htie]
          exact hsty
        exact .pure ⟨strongExit_success later _ val
          (flatFits_fits (members.1 key val sty found declared)), bound⟩ ⟨bound, Row.subset_refl _⟩
      | none =>
        refine .pure ⟨⟨?_, ?_⟩, bound⟩ ⟨bound, Row.subset_refl _⟩
        · rw [fitsExit_failure_iff]
          refine ⟨fun r hr => ?_, ?_⟩
          · simp only [Cause.die, List.mem_singleton] at hr
            subst hr
            trivial
          · intro r hr
            simp only [Cause.die, List.mem_singleton] at hr
            subst hr
            decide
        · intro r hr
          simp only [Cause.die, List.mem_singleton] at hr
          subst hr
          decide
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload.1, Row.subset_refl _⟩

/-- **`provideService`**: the value term at the key's carrier, then the context update: the
context read; when the update keeps the context's identity the body runs as is, else the set
context binding the value (its services fit: `fits_flatFits`, the carrier flat by
`serviceTy_flat`) and the body at the child under the finalizer restoring the previous context
(`onExit_typed`). -/
theorem provideService_arm {available : Env.Requirement} {key : ServiceKey} {value : Term} {b : NativeEff}
    (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.provideService key value b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (coverage : Row.Subset ty.requires available)
    (saved : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideService key value b) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_provideService] at hcheck
  obtain ⟨sty, vty, tb, hsty, hvty, hsub, hcb, rfl⟩ :=
    Checker.inv_provideService _ _ _ _ _ _ _ hcheck
  obtain ⟨v, evaluated, _⟩ := evalTerm_progress_env henv hvty
  have protocol := checked_provideService_arm root w p env key value (Eff.expandIn root.program b)
    available _ v hcheck henv evaluated htie (fun carrier declared => serviceTy_flat root key carrier declared)
    coverage (by rw [hfuel]; exact Nat.succ_ne_zero f) (fun bodyTy checked =>
      pointTyped_child hat rfl rfl checked henv hview hstack)
    (ambientStackTyped_child (q := p.child 0) hat rfl rfl saved)
  rw [denoteR_provideService _ _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f), evaluated] at protocol ⊢
  exact protocol

end ServiceArms

/-! ### `exit` -/

/-- **An immediate exit is admitted** (the `exit` arm's inline branch): at a checked point, an
exit `inlineYield` reads off the source is admitted at the point's type. The wrong-shape branches
never fire at a typed point: every request, value and target the checker types evaluates and
decodes (term progress, `syncRow_typed`, the handle inversions); a completed target answers from
the view (row 175); `exit` of an immediate exit is that exit's success, by induction on fuel. -/
theorem inlineYield_typed {root : ProgramSource} {w : World} (f : Nat) :
    ∀ (p : Point) {e : NativeEff} {ty : EffTy} {ex : ExitV}, p.fuel = f →
      Node.at_ (.eff root.program) p.path = some (.eff e) → PointTyped root w p ty →
      inlineYield e p = some ex → ExitOk w ty ex := by
  induction f with
  | zero =>
    intro p e ty ex hfuel _ _ hinline
    unfold inlineYield at hinline
    rw [if_pos hfuel] at hinline
    exact nomatch hinline
  | succ f ih =>
    intro p e ty ex hfuel hat hpt hinline
    have hpos : p.fuel ≠ 0 := by rw [hfuel]; exact Nat.succ_ne_zero f
    unfold inlineYield at hinline
    rw [if_neg hpos] at hinline
    cases e with
    | succeed t =>
      obtain ⟨env, hcheck, henv, _, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      obtain ⟨t', hty, rfl⟩ := Checker.inv_succeed _ _ _ _ _ hcheck
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
      simp only [hv, Option.some.injEq] at hinline
      subst hinline
      exact strongExit_success w _ v hfit
    | fail t =>
      obtain ⟨env, hcheck, henv, _, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      obtain ⟨e, hty, hadm, rfl⟩ := Checker.inv_fail _ _ _ _ _ hcheck
      obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
      simp only [hv, Option.some.injEq] at hinline
      subst hinline
      refine ⟨(fitsExit_failure_iff _ _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
      all_goals
        simp only [Cause.fail, List.mem_singleton] at hr
        subst hr
      · exact ⟨v, valOfErr_errOf_fits hadm hfit, hfit⟩
      · trivial
      · trivial
    | failCause c =>
      obtain ⟨env, hcheck, henv, _, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      obtain ⟨e, hty, rfl⟩ := Checker.inv_failCause _ _ _ _ _ hcheck
      obtain ⟨cause, hc, hfits, hshape⟩ := causeOf_progress henv c e hty
      simp only [hc, Option.some.injEq] at hinline
      subst hinline
      exact ⟨(fitsExit_failure_iff _ _ _).mpr ⟨hfits, hshape⟩, hshape⟩
    | perform op r =>
      cases op with
      | external i =>
        obtain ⟨env, hcheck, henv, _, hstack⟩ := hpt.at_node hat
        rw [Eff.expandIn_of_round _ _ rfl] at hcheck
        obtain ⟨reqTy, -, hreq, -⟩ := Checker.inv_perform _ _ _ _ _ _ hcheck
        obtain ⟨v, hv, -⟩ := evalTerm_progress_env henv hreq
        simp only [inlineAsyncYield, hv] at hinline
        exact nomatch hinline
      -- an invocation has no immediate exit: its row is a program's (`NativeOp.kind`)
      | call k => exact nomatch hinline
      | param i => exact nomatch hinline
      | sleep =>
        obtain ⟨_, v, reqTy, -, hv, hfit, hrow⟩ := builtinPerform_inv (by decide) hat hpt
        obtain ⟨σ, hinst, -, -⟩ := rowTy_fits_none hrow hfit
        obtain ⟨n, rfl⟩ := fits_nat_inv hinst
        simp only [NativeOp.row_kind, NativeOp.kind, inlineAsyncYield, hv, Option.bind_some,
          NativeOp.sleepMillisOf] at hinline
        exact nomatch hinline
      | deferredAwait =>
        obtain ⟨_, v, reqTy, -, hv, hfit, hrow⟩ := builtinPerform_inv (by decide) hat hpt
        obtain ⟨σ, hinst, -, -⟩ := rowTy_fits_none hrow hfit
        obtain ⟨k, rfl, -⟩ := fits_deferredOf_inv hinst
        simp only [NativeOp.row_kind, NativeOp.kind, inlineAsyncYield, hv, Option.bind_some,
          NativeOp.awaitCellOf] at hinline
        exact nomatch hinline
      | _ =>
        obtain ⟨_, v, reqTy, henv, hv, hfit, hrow⟩ :=
          builtinPerform_inv (kind_ne_program_of_sync rfl) hat hpt
        obtain ⟨o, ho, -⟩ := syncRow_typed root (req := Env.Requirement.empty) _ rfl henv
          hrow v hfit
        simp only [NativeOp.row_kind, NativeOp.kind, hv, Option.bind_some, ho] at hinline
        exact nomatch hinline
    | awaitFiber target mode =>
      obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_of_round _ _ rfl] at hcheck
      cases mode with
      | joinEffect =>
        obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_join _ _ _ _ _ hcheck
        obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
        replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
        obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
        simp only [hv] at hinline
        obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_join hinline
        exact view_exitOk hview hmem hid hdecl _
      | awaitValue =>
        obtain ⟨handle, pair, hty, hfib, rfl⟩ := Checker.inv_awaitFiber_await _ _ _ _ _ hcheck
        obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
        replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
        obtain ⟨index, rfl, hdecl⟩ := fiber_of_fits hfit
        simp only [hv] at hinline
        obtain ⟨entry, hmem, hid, rfl⟩ := awaitExit_value hinline
        exact strongExit_success w _ _ (view_exitOk hview hmem hid hdecl .empty).1
    | exit b =>
      obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_exit] at hcheck
      obtain ⟨tb, hcb, rfl⟩ := Checker.inv_exit _ _ _ _ _ hcheck
      dsimp only at hinline
      cases hsub : inlineYield b (p.child 0) with
      | none =>
        rw [hsub] at hinline
        exact nomatch hinline
      | some ex' =>
        rw [hsub, Option.map_some, Option.some.injEq] at hinline
        subst hinline
        have hex' := ih (p.child 0) (child_fuel_eq hfuel 0) (node_at_child hat rfl)
          (pointTyped_child hat rfl rfl hcb henv hview hstack) hsub
        exact strongExit_success w _ (reifyExitVal ex') hex'.1
    | provideContext context body =>
      obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_provideContext] at hcheck
      obtain ⟨contextTy, keys, bodyTy, termCheck, normalized, bodyCheck, rfl⟩ :=
        Checker.inv_provideContext _ _ _ _ _ _ hcheck
      obtain ⟨value, evaluated, members⟩ := evalTerm_progress_env henv termCheck
      have given : Fits w value (.contextOf keys) := by
        rw [← normalized]
        exact (fits_normalize _ _ _).mpr members
      obtain ⟨ctx, decoded, _, _, _⟩ := fits_contextOf_inv given
      simp only [evaluated, Option.bind_some, decoded] at hinline
      exact exitOk_widen (mid := bodyTy) (Ty.subN_refl _) (Ty.subN_refl _)
        (ih (p.child 0) (child_fuel_eq hfuel 0) (node_at_child hat rfl)
          (pointTyped_child hat rfl rfl bodyCheck henv hview hstack) hinline)
    | provideService key value b =>
      obtain ⟨env, hcheck, henv, -, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_provideService] at hcheck
      obtain ⟨sty, vty, tb, -, hvty, -, -, -⟩ := Checker.inv_provideService _ _ _ _ _ _ _ hcheck
      obtain ⟨v, hv, -⟩ := evalTerm_progress_env henv hvty
      simp only [hv] at hinline
      exact nomatch hinline
    -- a restore site: its saved term's value is a saved image; at a false bit the body's own
    -- immediate exit at child 0, at the node's type; at a true bit a `WithFiber`, no exit
    | restore saved b =>
      obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
      rw [Eff.expandIn_restore] at hcheck
      obtain ⟨savedTy, hsaved, hsub_saved, hcb⟩ := Checker.inv_restore _ _ _ _ _ _ hcheck
      obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hsaved
      obtain ⟨flag, rfl⟩ := fits_maskRestore_inv (fits_subN w (b := .maskRestore) hsub_saved v hvfit)
      simp only [hv, Option.bind_some, Val.savedMask?_savedMask] at hinline
      cases flag with
      | true => exact nomatch hinline
      | false =>
        exact ih (p.child 0) (child_fuel_eq hfuel 0) (node_at_child hat rfl)
          (pointTyped_child hat rfl rfl hcb henv hview hstack) hinline
    | defs decls bodies main _ => exact (defs_not_typed hat hpt).elim
    | _ => exact nomatch hinline

/- The actual source provider keeps its checked child and immediate-exit evidence.
The protected Region arm consumes the actual supplied map and ambient entry row.
Consumer: the existing M5 source induction. -/
section ContextSourceArm
variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}
theorem provideContext_arm {available : Env.Requirement} {context : Term} {body : NativeEff}
    (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.provideContext context body)))
    (hpt : PointTyped root w p ty) (coverage : Row.Subset ty.requires available)
    (saved : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideContext context body) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_provideContext] at hcheck
  obtain ⟨contextTy, keys, bodyTy, termCheck, normalized, bodyCheck, rfl⟩ :=
    Checker.inv_provideContext _ _ _ _ _ _ hcheck
  obtain ⟨value, evaluated, members⟩ := evalTerm_progress_env henv termCheck
  have given : Fits w value (.contextOf keys) := by
    rw [← normalized]
    exact (fits_normalize _ _ _).mpr members
  obtain ⟨supplied, decoded, _, _, _⟩ := fits_contextOf_inv given
  have same : value = Val.context supplied := Val.context?_exact decoded
  subst value
  have child : PointTyped root w (p.child 0) bodyTy :=
    pointTyped_child hat rfl rfl bodyCheck henv hview hstack
  rw [denoteR_provideContext _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f), evaluated]
  simp only [Option.bind_some, Val.context?_context]
  cases immediate : inlineYield body (p.child 0) with
  | some exit =>
    refine .pure ⟨?_, ?_⟩ ⟨Row.subset_refl available, Row.subset_refl _⟩
    · exact exitOk_widen (mid := bodyTy) (Ty.subN_refl _) (Ty.subN_refl _)
        (inlineYield_typed f (p.child 0) (child_fuel_eq hfuel 0)
          (node_at_child hat rfl) child immediate)
    · cases exit <;> exact Row.subset_refl available
  | none =>
    exact ambient_updateContext_provide root available available bodyTy.requires keys supplied
      given coverage (Row.subset_refl _)
      ⟨bodyTy.answer, bodyTy.error, Row.diff bodyTy.requires keys⟩
      (.program (p.child 0)) child
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl saved) (.provide supplied.services) (fun _ => rfl)
end ContextSourceArm

section ExitArm

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {f : Nat}

/-- **`exit`**: the body's exit reified as a successful exit value at `Exit<A, E>`; an immediate
exit by `inlineYield_typed`, otherwise the body at the child under the both-arm boundary
(`allGuard_typed`). -/
theorem exit_arm {available : Env.Requirement} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.exit b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0]))
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.exit b) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_exit] at hcheck
  obtain ⟨tb, hcb, rfl⟩ := Checker.inv_exit _ _ _ _ _ hcheck
  have hchild : PointTyped root w (p.child 0) tb := pointTyped_child hat rfl rfl hcb henv hview hstack
  rw [denoteR_exit _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f)]
  cases hsub : inlineYield b (p.child 0) with
  | some ex' =>
    exact .pure ⟨strongExit_success w _ _ (inlineYield_typed f (p.child 0) (child_fuel_eq hfuel 0)
      (node_at_child hat rfl) hchild hsub).1, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  | none =>
    refine ambient_guardBind root
      (hb w htie (p.child 0) tb (child_fuel_eq hfuel 0) rfl hchild available coverage
        (ambientStackTyped_child (q := p.child 0) hat rfl rfl savedParams))
      (fun later _ exit _ payload => ?_) (fun _ _ exit _ impossible => ?_) (Row.subset_refl _)
    · have selected : ambientInput (tb, available, available) exit = available := by
        cases exit <;> rfl
      rw [selected]
      exact .pure ⟨strongExit_success later _ (reifyExitVal exit) payload.1.1,
        Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
    · cases exit <;> exact Bool.noConfusion impossible

/-- **`restore`** (decisions rows 244 and 245; the body's address in the claim
`scoped-body-substitution-boundary`). The saved term's value is a saved image
(`evalTerm_progress_env`, `fits_maskRestore_inv`), so the node never refuses. Both saved choices
read the one checked body at child 0, in the node's environment and at the node's type
(`Checker.inv_restore`, `pointTyped_child`): a true bit is the mask row over that body, as
`interruptible_arm`; a false bit is the body's own denotation, with no row of the node's. -/
theorem restore_arm {available : Env.Requirement} {saved : Term} {b : NativeEff} (hfuel : p.fuel = f + 1)
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.restore saved b)))
    (hpt : PointTyped root w p ty) (htie : w.serviceTy = root.sig.serviceTy)
    (hb : ChildDenotes root f b (p.path ++ [0]))
    (coverage : Row.Subset ty.requires available)
    (savedParams : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available (ty, available, available) (denoteR root.program (.restore saved b) p) := by
  obtain ⟨env, hcheck, henv, hview, hstack⟩ := hpt.at_node hat
  rw [Eff.expandIn_restore] at hcheck
  obtain ⟨savedTy, hsaved, hsub_saved, hcb⟩ := Checker.inv_restore _ _ _ _ _ _ hcheck
  obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hsaved
  obtain ⟨flag, rfl⟩ := fits_maskRestore_inv (fits_subN w (b := .maskRestore) hsub_saved v hvfit)
  have hchild : PointTyped root w (p.child 0) ty := pointTyped_child hat rfl rfl hcb henv hview hstack
  rw [denoteR_restore _ _ _ (by rw [hfuel]; exact Nat.succ_ne_zero f), hv, Option.bind_some,
    Val.savedMask?_savedMask]
  cases flag with
  | true =>
    have hact : actionAt root.program p =
        some (WithFiberAction.setInterruptible (resolve root.program (p.child 0)) true) := by
      unfold actionAt
      rw [hat]
    show AmbientProg root w available (ty, available, available) (denoteAction root.program p)
    rw [denoteAction_of _ _ hact]
    refine ProgramArrow.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) ty
      ⟨BodyTyped.at_ _ _ hchild, coverage, (fun _ _ impossible => by cases impossible),
        (fun _ _ _ impossible => by cases impossible),
        ⟨(fun _ impossible => by cases impossible), (fun _ _ _ impossible => by cases impossible),
          ⟨(fun point role => by
            rcases role with identity | ⟨ctx, impossible | impossible⟩
            · cases identity
              exact ambientStackTyped_child hat rfl rfl savedParams
            · cases impossible
            · cases impossible), fun _ _ _ impossible => by cases impossible⟩⟩⟩
      (fun _ _ exit post => .pure ⟨post, by cases exit <;> exact Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩) ⟨Row.subset_refl _, Row.subset_refl _⟩
  | false =>
    exact hb w htie (p.child 0) ty (child_fuel_eq hfuel 0) rfl hchild available coverage
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl savedParams)

end ExitArm

/-! ## The assembly: the arms by induction on fuel

At no fuel every point is the frontier (`denoteR_zero_typed`); at positive fuel each constructor's
arm applies, every child's hypothesis (`ChildDenotes`) being the induction's at the child's node
and the lower fuel. The layer family (`provideLayer`, decisions row 176 (b)) is proved in
`Typed/LayerArm.lean`: its arm enters here as the hypothesis `ProvideLayerArm`, which that module
discharges (`provideLayerArm`). -/

/-- **The layer family's arm, as a hypothesis** (decisions row 176 (b): built layers answer the
fiber-context image; proved at every source by `provideLayerArm`, `Typed/LayerArm.lean`, which the
import direction places after this module): at a well-formed program, given that
every node at every fuel up to `f` denotes typed programs at its typed points, a typed
`provideLayer` point with fuel `f + 1` denotes a typed program. -/
def ProvideLayerArm (root : ProgramSource) : Prop :=
  root.program.layerRefsWF = true → ModuleLayersTyped root → ∀ (f : Nat),
    (∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path) →
    ∀ (w : World), w.serviceTy = root.sig.serviceTy → ∀ (p : Point) (ty : EffTy)
      (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff), p.fuel = f + 1 →
      Node.at_ (.eff root.program) p.path = some (.eff (.provideLayer l i b)) →
      PointTyped root w p ty → ∀ available, Row.Subset ty.requires available →
        AmbientStackTyped root w available (scopeParams root.program p.path) p.params →
        AmbientProg root w available (ty, available, available) (denoteR root.program (.provideLayer l i b) p)

/-- **The arms assembled** (by induction on fuel, given the layer family's arm): every node of a
well-formed program, at every fuel up to `f`, denotes typed programs at its typed points. -/
theorem childDenotes_upto (root : ProgramSource) (hlayer : ProvideLayerArm root)
    (hwf : root.program.layerRefsWF = true) (hmod : ModuleLayersTyped root)
    (hbodies : BodiesTyped root) :
    ∀ (f : Nat), ∀ f' ≤ f, ∀ (c : NativeEff) (path : List Nat),
      Node.at_ (.eff root.program) path = some (.eff c) → ChildDenotes root f' c path := by
  intro f
  induction f with
  | zero =>
    intro f' hf' c path _ w _ q ty hq _ _ available _ _
    exact denoteR_zero_typed c (by omega)
  | succ f ih =>
    intro f' hf' c path hc w htie q ty hq hqpath hqt available coverage savedParams
    rcases Nat.lt_or_eq_of_le hf' with hlt | heq
    · exact ih f' (Nat.lt_succ_iff.mp hlt) c path hc w htie q ty hq hqpath hqt available coverage savedParams
    · subst heq
      have hat : Node.at_ (.eff root.program) q.path = some (.eff c) := hqpath ▸ hc
      have hpos : q.fuel ≠ 0 := by rw [hq]; exact Nat.succ_ne_zero f
      have hch : ∀ (c' : NativeEff) (i : Nat), (Node.eff c).child i = some (.eff c') →
          ChildDenotes root f c' (q.path ++ [i]) :=
        fun c' i hci => ih f (Nat.le_refl f) c' (q.path ++ [i]) (node_at_child hat hci)
      cases c with
      | succeed t => exact succeed_arm hpos hat hqt
      | fail t => exact fail_arm hpos hat hqt
      | failCause c => exact failCause_arm hpos hat hqt
      | sync t => exact sync_arm hpos hat hqt
      | suspend b => exact suspend_arm hq hat hqt htie (hch b 0 rfl) coverage savedParams
      | perform op r =>
        exact perform_arm hq hat hqt htie hbodies (fun c' path' hc' => ih f (Nat.le_refl f) c' path' hc') coverage savedParams
      | bind a b => exact bind_arm hq hat hqt htie (hch a 0 rfl) (hch b 1 rfl) coverage savedParams
      | gen body => exact gen_arm hq hat hqt coverage
      | catchCause b h => exact catchCause_arm hq hat hqt htie (hch b 0 rfl) (hch h 1 rfl) coverage savedParams
      | matchCause b v c => exact matchCause_arm hq hat hqt htie coverage (hch b 0 rfl) (hch v 1 rfl) (hch c 2 rfl) savedParams
      | onExit b fin => exact onExit_arm hq hat hqt htie coverage (hch b 0 rfl) (hch fin 1 rfl) savedParams
      | exit b => exact exit_arm hq hat hqt htie (hch b 0 rfl) coverage savedParams
      | uninterruptible b => exact uninterruptible_arm hq hat hqt coverage savedParams
      | interruptible b => exact interruptible_arm hq hat hqt coverage savedParams
      | yieldNow priority => exact yieldNow_arm hpos hat hqt
      | awaitFiber t mode => exact awaitFiber_arm hpos hat hqt
      | withFiber a => exact withFiber_arm hpos hat hqt htie coverage savedParams
      | «scoped» b => exact scoped_arm hq hat hqt coverage
      | acquireRelease a r => exact acquireRelease_arm hq hat hqt coverage savedParams
      | provideContext context body => exact provideContext_arm hq hat hqt coverage savedParams
      | provideLayer l i b => exact hlayer hwf hmod f ih w htie q ty l i b hq hat hqt available coverage savedParams
      | service key => exact service_arm hpos htie hat hqt
      | provideService key value b => exact provideService_arm hq hat hqt htie coverage savedParams
      | catchIf test b h => exact catchIf_arm hq hat hqt htie (hch b 0 rfl) (hch h 1 rfl) coverage savedParams
      | select s d a0 a1 => exact select_arm hq hat hqt htie (hch a0 0 rfl) (hch a1 1 rfl) coverage savedParams
      | iterate cursorTy initial test step result body => exact iterate_arm hq hat hqt coverage
      | restore saved b => exact restore_arm hq hat hqt htie (hch b 0 rfl) coverage savedParams
      | defs decls bodies main _ => exact (defs_not_typed hat hqt).elim
      | invoke k r args =>
        exact invoke_arm hq hat hqt htie hbodies (fun c' path' hc' => ih f (Nat.le_refl f) c' path' hc') coverage savedParams

/-- **No node of the program is a `provideLayer`**: the fragment on which the layer family's arm
cannot be reached. -/
def LayerFree (root : NativeEff) : Prop :=
  ∀ (path : List Nat) (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff),
    Node.at_ (.eff root) path ≠ some (.eff (.provideLayer l i b))

/-- On the layer-free fragment the layer family's arm holds: no point reaches it. -/
theorem provideLayerArm_of_layerFree {root : ProgramSource} (h : LayerFree root.program) :
    ProvideLayerArm root :=
  fun _ _ _ _ _ _ p _ l i b _ hat _ _ _ _ => absurd hat (h p.path l i b)

/-- The actual acquired result and checker issue the captured release callback policy.
Concept: residual-program-typing, R4 and R9; helper of the closed M5 source claim.
Consumer: the ambient acquireIn registration, preserving actual captured-map coverage.
No service declaration substitutes for coverage of that map. -/
theorem capturedReleasePolicy (root : ProgramSource) (world : World) (point : Point)
    (acquire release : NativeEff) (env : List Ty) (type acquiredType : EffTy)
    (available : Env.Requirement) (ctx : Ctx) (acquired : Val)
    (node : Node.at_ (.eff root.program) point.path = some (.eff (.acquireRelease acquire release)))
    (checked : Checker.check (root.scopeSig point.path) env point.path
      (Eff.expandIn root.program (.acquireRelease acquire release)) = .ok type)
    (acquireChecked : Checker.check (root.scopeSig point.path) env (point.path ++ [0])
      (Eff.expandIn root.program acquire) = .ok acquiredType)
    (values : EnvTyped world env point.env) (answer : Fits world acquired acquiredType.answer)
    (requires : Row.Subset type.requires available) (covered : ctx.services.Satisfies available)
    (arguments : AmbientStackTyped root world available
      (scopeParams root.program point.path) point.params) :
    AmbientCapturePolicy root world (point.capture acquired ctx) := by
  rw [Eff.expandIn_acquireRelease] at checked
  obtain ⟨a, r, acquiredCheck, releaseCheck, never, typeEq⟩ :=
    Checker.inv_acquireRelease _ _ _ _ _ _ checked
  rw [acquireChecked] at acquiredCheck
  cases acquiredCheck
  subst type
  have captureBound : Row.Subset available ctx.services.keysRow :=
    (Provision.satisfies_iff_subset_keysRow _ _).mp covered
  have releaseBound := Row.subset_trans
    (Row.subset_union_right acquiredType.requires r.requires)
    (Row.subset_union_left (Row.union acquiredType.requires r.requires)
      (Env.Requirement.single (root.scopeSig point.path).scopeKey))
  intro future ordered completed completedTyped exitValue exitFit
  refine ⟨r, ?_, never, Row.subset_trans releaseBound (Row.subset_trans requires captureBound)⟩
  refine ⟨pointTyped_child node rfl rfl releaseCheck ?_ completedTyped
    (stackTyped_mono ordered (ambientStackTyped_erases arguments)), ?_⟩
  · have acquiredValues := envTyped_append (envTyped_mono ordered values) (fits_mono ordered answer)
    have exitValues := envTyped_append acquiredValues exitFit
    simpa only [Point.ofCapture, Point.capture, Point.childWith, Point.child, List.append_assoc, List.singleton_append] using exitValues
  · exact ambientStackTyped_child (parent := point) node rfl rfl
      (ambientStackTyped_widen captureBound (ambientStackTyped_mono ordered arguments))

end Effect4.Program.Typed
