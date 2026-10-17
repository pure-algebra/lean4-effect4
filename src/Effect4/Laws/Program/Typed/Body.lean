import Effect4.Laws.Program.Typed.LayerArm

/-!
# Laws.Program.Typed.Body — an admitted body's program is typed

Concept 2 of `docs/core/semantics.md` (`residual-program-typing`), serving concept 4's
`step-deliver-preserves` and `step-loop-preserves`: a helper of `deliver_preserves`, consumed by
the `mask` clause and the fork clauses (`Typed/Commands/Evaluate.lean`, `Clauses/Spawn.lean`),
which install `bodyR interp body` as a fiber's current code when `ambientFiberPre` admits `body`
(`BodyTyped` with `BodyCoverage`, `Typed/Residual.lean`).

`bodyTyped_ambient`: at a source whose layer references are well formed (`J.sourceWF`, decisions
row 170) and a world whose service table is the source's (`J.services`), an admitted body's program
at any completed view is typed by the ambient judgment at the row the fiber's context covers
(decisions row 349), at the body's position (`bodyPosition`). One arm per `Body` constructor:

- `at_`: M5 at the point (`denotesTyped`, through `denoteAt_ambient`);
- `raceCleanup`: the race's cancel answers `unit`;
- `acquireIn`: `acquireRelease`'s masked half (`acquireInR`; `internal/effect.ts:3978-3986`): the
  `Scope` read, the acquire at the point's child 0 (M5), the release's registration (its capture is
  covered by the captured context, `CaptureTyped`), and the closed branch's release now
  (`foreignFin_ambient`, under the captured context merged over the current one, which keeps
  the row);
- `release`: the release at its point under the restore of the previous context, at the keys both
  contexts hold (`ambient_release_body`, `Typed/MaskEntry.lean`);
- `layerBuild`: the layer family's build (`layerBuild_typed`);
- `region`: the installed region's program (`region_ambient`): a point's program, a layer's build,
  the build with the memo map added, a leaf's construction;
- `contextEntry`: the provider's protected entry (`contextEntry_ambient`): the context read, the
  update installed and its region run under the restore of the previous context, or the region
  run as is when the update keeps the context.

`Body.fin` is admitted at no type (`BodyTyped`, `Typed/Admission.lean`). Not established: anything
about a machine; the clauses that consume this are `Evaluate`'s and `Spawn`'s.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-- **A checked point's code is typed** at every row covering its requirement row and typing its
parameters: M5 at the point, through the interpreter's body hook. -/
theorem denoteAt_ambient (root : ProgramSource) {w : World} (hwf : SourceWF root)
    (htie : Tied root w) {available : Env.Requirement} {p : Point}
    {ty : EffTy} (h : PointTyped root w p ty) (requires : Row.Subset ty.requires available)
    (stack : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available ((ty, available, available) : AmbientPosition)
      (denoteAt root.program p) := by
  obtain ⟨e, env, hat, hcheck, henv, hview⟩ := h
  have unfolded : denoteAt root.program p = denoteR root.program e p := by
    simp only [denoteAt, hat]
  rw [unfolded]
  exact denotesTyped root hwf w htie p e ty hat ⟨e, env, hat, hcheck, henv, hview⟩ available
    requires stack

/-! ## Foreign releases -/

/-- **A typed capture's release is covered by its captured context** (`AmbientCapturePolicy`):
the release point typed at the checker's release type, its parameters and its requirement row
within the captured context's keys (`CaptureTyped`). -/
theorem captureTyped_policy {root : ProgramSource} {w : World} {c : Capture}
    (h : CaptureTyped root w c) : AmbientCapturePolicy root w c := by
  intro later ordered completed completedTyped exitValue exitFit
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, -, hstack, hrow⟩ :=
    captureTyped_mono ordered h
  rw [Eff.expandIn_acquireRelease] at hcheck
  obtain ⟨a', r, hacq', hrel, hnever, ht⟩ := Checker.inv_acquireRelease _ _ _ _ _ t hcheck
  rw [hacq] at hacq'
  cases hacq'
  subst ht
  refine ⟨r, ⟨pointTyped_child hnode rfl rfl hrel ?_ completedTyped
    (ambientStackTyped_erases hstack), ?_⟩, hnever, ?_⟩
  · show EnvTyped later (env ++ [a.answer, .exitOf .unknown .unknown]) (c.env ++ [exitValue])
    have := envTyped_append henv exitFit
    simpa only [List.append_assoc, List.singleton_append] using this
  · exact ambientStackTyped_child (parent := Point.ofCapture c completed) hnode rfl rfl hstack
  · exact Row.subset_trans (Row.subset_trans (Row.subset_union_right _ _)
      (Row.subset_union_left _ _)) hrow

/-- The finalizer type's position at a row. -/
abbrev finPosition (available : Env.Requirement) : AmbientPosition :=
  ((⟨.unknown, .never, Env.Requirement.empty⟩ : EffTy), available, available)

/-- **A foreign release, run now** (`denoteFin`'s foreign arm; `internal/effect.ts:3983`,
`:2180-2199`), at any row the fiber's context covers: the counted release marker, the current
context read, the captured one merged over it (`releaseContext`), which keeps the row, the
construction query, and the masked release at its point under the restore of the read context. -/
theorem foreignFin_ambient (root : ProgramSource) {w : World} {c : Capture}
    (h : CaptureTyped root w c) {available : Env.Requirement} {ex : ExitV}
    (hex : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex) :
    AmbientProg root w available (finPosition available) (denoteFin (.foreign c) ex) := by
  refine ambient_fiberAdmin rfl (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial (fun w1 o1 _ _ => ?_)
  refine ambient_guardBind root (ambient_captureContext_typed root w1 available)
    (fun w2 o2 exit arm payload => ?_) (fun _ _ exit payload absent => ?_) (Row.subset_refl _)
  · cases exit with
    | failure cause => exact Bool.noConfusion arm
    | success value =>
      obtain ⟨previous, decoded, _⟩ := fits_context_inv payload.1.1
      have same : value = Val.context previous := Val.context?_exact decoded
      subst value
      obtain ⟨previousServices, previousCovers⟩ := ambient_captured_context payload
      have bound : Row.Subset available previous.services.keysRow :=
        (Provision.satisfies_iff_subset_keysRow _ available).mp previousCovers
      have o12 := leHost_trans _ _ _ o1 o2
      obtain ⟨_, _, _, _, _, _, _, _, _, capturedServices, -, -⟩ := captureTyped_mono o12 h
      let next : Ctx := releaseContext previous c.ctx
      have nextServices : ServicesFit w2 next.services :=
        servicesFit_merge previousServices capturedServices
      have window : Row.Subset available next.services.keysRow :=
        (Provision.satisfies_iff_subset_keysRow _ available).mp
          (Provision.satisfies_merge_left previous.services c.ctx.services available previousCovers)
      have captured : Row.Subset c.ctx.services.keysRow next.services.keysRow :=
        (Provision.satisfies_iff_subset_keysRow _ _).mp
          (Provision.satisfies_merge_right previous.services c.ctx.services _
            ((Provision.satisfies_iff_subset_keysRow _ _).mpr (Row.subset_refl _)))
      simp only [seqR, ambientInput, Val.context?_context]
      refine ambient_guardBind root
        (mid := ((EffTy.pure .unit, next.services.keysRow, available) : AmbientPosition))
        (ambient_setContext_guarantees root w2 previous.services.keysRow available next
          nextServices bound window)
        (fun w3 o3 exit' arm' _ => ?_) (fun _ _ exit' payload' absent' => ?_) bound
      · cases exit' with
        | failure cause => exact Bool.noConfusion arm'
        | success done =>
          simp only [seqR]
          refine ambient_constructR_typed root window (fun w4 o4 completed hview => ?_)
          have o24 := leHost_trans _ _ _ o3 o4
          obtain ⟨rty, ⟨hpt, hstack⟩, hnever, hreq⟩ :=
            captureTyped_policy (captureTyped_mono (leHost_trans _ _ _ o12 o24) h) w4 (leHost_refl _)
              completed hview
              (reifyExitVal ex)
              (reifyExitVal_fits w4 _ ex (fitsExit_mono (leHost_trans _ _ _ o12 o24) hex))
          refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
            (fun _ _ _ h => nomatch h) rty
            ⟨BodyTyped.release _ previous rty hpt (servicesFit_mono o24 previousServices),
              Row.subset_trans hreq captured,
              (fun _ _ impossible => by cases impossible),
              (fun _ _ _ same => by cases same; rfl),
              (fun _ impossible => by cases impossible),
              (fun _ _ _ impossible => by cases impossible),
              (fun point role => by
                rcases role with impossible | ⟨ctx, impossible | identity⟩
                · cases impossible
                · cases impossible
                · cases identity
                  exact ambientStackTyped_widen captured hstack),
              (fun _ _ _ impossible => by cases impossible)⟩
            (fun _ _ ans post => .pure ⟨exitOk_finalizer hnever post,
                by cases ans <;> exact subset_rowMeet bound window⟩
              ⟨subset_rowMeet bound window, Row.subset_refl _⟩) ⟨window, Row.subset_refl _⟩
      · cases exit' with
        | success done => exact Bool.noConfusion absent'
        | failure cause =>
          exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload'.1, Row.subset_refl _⟩
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload.1, Row.subset_refl _⟩

/-- **A registered finalizer runs at a covered row**: a foreign release under its captured
context merged over the current one (`foreignFin_ambient`), every other finalizer as
administrative code (`denoteFin_admin`). -/
theorem finalizer_ambient (root : ProgramSource) {w : World} {fin : FinName}
    (h : FinalizerAdmitted root w fin) {available : Env.Requirement} {ex : ExitV}
    (hex : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex) :
    AmbientProg root w available (finPosition available) (denoteFin fin ex) := by
  cases fin with
  | foreign c => exact foreignFin_ambient root h hex
  | _ =>
    exact ambientProg_of_admin root
      (finalizerTyped_of_admitted root w _ h w (leHost_refl w) ex hex)
      (denoteFin_admin _ (by intro c same; cases same) ex) available

/-! ## The bodies -/

/-- **`acquireRelease`'s masked half** at a row its captured context covers: the `Scope` read, the
acquire at the point's child 0 (the node's own columns, `Checker.inv_acquireRelease`), the
release's registration as a capture the registration admits (`CaptureTyped`: the node, the
checker's verdicts, the environment extended by the acquired value, the context's services, its
parameters and requirement row within the context's keys), and the acquired value as the answer,
after the release when the scope was already closed. -/
theorem acquireIn_ambient (root : ProgramSource) {w : World} (hwf : SourceWF root)
    (htie : Tied root w) {available : Env.Requirement} {p : Point}
    {ctx : Ctx} {ty : EffTy} (h : PointTyped root w p ty) {acquire release : NativeEff}
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.acquireRelease acquire release)))
    (hsvc : ServicesFit w ctx.services) (covered : ctx.services.Satisfies available)
    (requires : Row.Subset ty.requires available)
    (stack : AmbientStackTyped root w available (scopeParams root.program p.path) p.params) :
    AmbientProg root w available ((ty, available, available) : AmbientPosition)
      (acquireInR (denoteAt root.program (p.child 0)) p ctx) := by
  have bound : Row.Subset available ctx.services.keysRow :=
    (Provision.satisfies_iff_subset_keysRow _ available).mp covered
  obtain ⟨e, env, hat', hcheck, henv, hview, hstack⟩ := h
  rw [hat] at hat'
  cases hat'
  have hcheck' := hcheck
  rw [Eff.expandIn_acquireRelease] at hcheck'
  obtain ⟨a, r, hacq, _, _, rfl⟩ := Checker.inv_acquireRelease _ _ _ _ _ _ hcheck'
  have aRequires : Row.Subset a.requires available :=
    Row.subset_trans (Row.subset_trans (Row.subset_union_left _ _) (Row.subset_union_left _ _))
      requires
  have hacquire : AmbientProg root w available ((a, available, available) : AmbientPosition)
      (denoteAt root.program (p.child 0)) :=
    denoteAt_ambient root hwf htie (pointTyped_child hat rfl rfl hacq henv hview hstack) aRequires
      (ambientStackTyped_child (q := p.child 0) hat rfl rfl stack)
  unfold acquireInR
  -- the `Scope` read
  refine ambient_seqGuard (mid := EffTy.pure Ty.scope)
    (ambient_fiberAdmin rfl (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () trivial (fun w1 _ ans post =>
        .pure ⟨strongExit_success w1 _ _ post, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩))
    (Bounds.subN_never _) (fun w1 o1 v hv => ?_)
  obtain ⟨s, rfl, hlive⟩ := fits_scope_inv hv
  simp only [seqR, Val.scope?_scopeHandle]
  -- the acquire, at the node's own columns
  refine ambient_seqGuard (ambientProg_mono root o1 hacquire) (Ty.subN_refl _)
    (fun w2 o2 aval hfit => ?_)
  simp only [seqR]
  have o12 := leHost_trans _ _ _ o1 o2
  -- the capture the registration admits
  have hcap : CaptureTyped root w2 (p.capture aval ctx) :=
    ⟨acquire, release, env, _, a, hat, hcheck, hacq, envTyped_append (envTyped_mono o12 henv) hfit,
      servicesFit_mono o12 hsvc,
      ambientStackTyped_widen bound (ambientStackTyped_mono o12 stack),
      Row.subset_trans requires bound⟩
  -- the registration: `unit` when the scope is open, its closing exit when it is closed
  refine ambient_seqGuard
    (mid := ⟨.union .unit (.exitOf .unknown .unknown), .never, Env.Requirement.empty⟩)
    (ambient_foreign_registration_typed root available s (p.capture aval ctx)
      (scopeLive_mono o2.1 hlive) hcap (captureTyped_policy hcap))
    (Bounds.subN_never _) (fun w3 o3 u hu => ?_)
  simp only [seqR]
  have hval : Fits w3 aval a.answer := fits_mono o3 hfit
  rcases hu with hunit | hexit
  · rw [fits_unit_inv hunit, if_pos rfl]
    exact .pure ⟨strongExit_success w3 _ aval hval, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  · obtain ⟨ex, hex⟩ := exitOfVal_of_fits hexit
    have hne : u ≠ Val.unit := by
      intro hu
      rw [hu] at hex
      exact nomatch hex
    rw [if_neg hne, hex]
    -- the closed branch: the release now, under the captured context merged over the current
    -- one, then the acquired value
    exact ambient_seqGuard (mid := ⟨.unknown, .never, Env.Requirement.empty⟩)
      (foreignFin_ambient root (captureTyped_mono o3 hcap) (fitsExit_of_exitOfVal hexit hex))
      (Bounds.subN_never _) (fun w4 o4 _ _ =>
        .pure ⟨strongExit_success w4 _ aval (fits_mono o4 hval), Row.subset_refl _⟩
          ⟨Row.subset_refl _, Row.subset_refl _⟩)

/-- The keeping update installs nothing: `provide` of the empty map. -/
theorem apply_of_keepsIdentity {update : Env.ContextUpdate} {previous : Env.Ctx}
    (keeps : updateKeepsIdentity update previous = true) : update.apply previous = previous := by
  cases update with
  | provide that =>
    have empty : that.entries = [] := (of_decide_eq_true keeps).2
    show Env.Context.mergeEntries previous that.entries = previous
    rw [empty]
    rfl
  | _ => exact Bool.noConfusion keeps

/-- **The installed region's program** (`regionBodyR`, the generated Region fold) at a row its
context covers: a point's program (M5), a layer's build (`layerBuild_typed`), the build with the
memo map added (`addCurrentMemoMap_exit`), a leaf's construction with its answer bound
(`bindService_exit`). -/
theorem region_ambient (root : ProgramSource) {w : World} (hwf : SourceWF root)
    (htie : Tied root w) (completed : List (FiberId × ExitV))
    {available : Env.Requirement} {region : Region} {intrinsic ty : EffTy}
    (typed : RegionTyped root w region intrinsic)
    (answer : Ty.subN intrinsic.answer ty.answer = true)
    (error : Ty.subN intrinsic.error ty.error = true)
    (requires : Row.Subset intrinsic.requires available)
    (stack : RegionStackTyped root w available region) :
    AmbientProg root w available ((ty, available, available) : AmbientPosition)
      (bodyR (interpRAt root.program completed) (.region region)) := by
  refine ambientProg_widen root (before := (intrinsic, available, available))
    (after := (ty, available, available)) answer error (Row.subset_refl _)
    (Row.subset_refl _) ?_
  show AmbientProg root w available _ (regionBodyR (denoteAt root.program)
    (layerBuildR root.program) region)
  cases region with
  | program point =>
    exact denoteAt_ambient root hwf htie typed requires stack
  | build point memo scope =>
    obtain ⟨lt, rfl, hpt, hlive, hmemo⟩ := typed
    obtain ⟨l, hat, hrest⟩ := hpt
    show AmbientProg root w available _ (layerBuildR root.program point memo scope)
    simp only [layerBuildR, hat]
    exact layerBuild_typed hwf.refs hwf.layers l point w lt memo scope available htie hat
      ⟨l, hat, hrest⟩ hlive hmemo requires stack
  | buildAdding point memo scope =>
    obtain ⟨lt, rfl, hpt, hlive, hmemo⟩ := typed
    obtain ⟨l, hat, hrest⟩ := hpt
    show AmbientProg root w available _
      ((guardR .onSuccess (layerBuildR root.program point memo scope)).bind (seqR fun value =>
        addCurrentMemoMapR memo value))
    simp only [layerBuildR, hat]
    refine ambient_seqGuard (layerBuild_typed hwf.refs hwf.layers l point w lt memo scope available
      htie hat ⟨l, hat, hrest⟩ hlive hmemo requires stack) (Ty.subN_refl _) (fun w1 o1 v hv => ?_)
    simp only [seqR]
    obtain ⟨v', hv', fits'⟩ := addCurrentMemoMap_exit (Tied.mono o1 htie)
      (memoLive_mono o1.1 hmemo) hv
    rw [hv']
    exact .pure ⟨strongExit_success w1 _ _ fits', Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩
  | construct point key =>
    obtain ⟨bodyTy, hpt, rfl, carriers⟩ := typed
    show AmbientProg root w available _
      ((guardR .onSuccess (denoteAt root.program point)).bind (seqR fun value =>
        bindServiceR key value))
    refine ambient_seqGuard (denoteAt_ambient root hwf htie hpt requires stack) (Ty.subN_refl _)
      (fun w1 o1 v hv => ?_)
    simp only [seqR]
    obtain ⟨ctx, hbind, hfits⟩ := bindService_exit (key := key) (v := v)
      (fun k hk => by
        obtain ⟨carrier, declared, sub, flat⟩ := carriers k hk
        exact ⟨carrier, le_serviceTy o1.1 ▸ declared, fits_flatFits flat (fits_subN w1 sub v hv)⟩)
      (fits_live w1 _ v hv)
    rw [hbind]
    exact .pure ⟨strongExit_success w1 _ _ hfits, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩

/-- A region's mask returns at the row it entered at. -/
theorem ambientFiberInput_region (available : Env.Requirement) (flag : Bool) (region : Region)
    (answer : ExitV) :
    ambientFiberInput available (.mask flag (.region region)) answer = available := by
  cases flag <;> rfl

/-- The installed region's mask at a row its context covers: the region body admitted
(`BodyTyped.region`), its requirement row and parameters within the row (`BodyCoverage`), its
answer the region's, the row unchanged. -/
theorem restoreRegion_ambient (root : ProgramSource) {w : World} {available : Env.Requirement}
    {region : Region} {intrinsic ty : EffTy} (flag : Bool) {guaranteed : Env.Requirement}
    (typed : RegionTyped root w region intrinsic)
    (answer : Ty.subN intrinsic.answer ty.answer = true)
    (error : Ty.subN intrinsic.error ty.error = true)
    (requires : Row.Subset intrinsic.requires available)
    (stack : RegionStackTyped root w available region)
    (entry : Row.Subset guaranteed available) :
    AmbientProg root w available ((ty, guaranteed, guaranteed) : AmbientPosition)
      (restoreRegionR region flag) := by
  let cut : EffTy := ⟨ty.answer, ty.error, available⟩
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cut
    ⟨.region region intrinsic cut typed answer error, Row.subset_refl _,
      (fun _ _ impossible => by cases impossible),
      (fun _ _ _ impossible => by cases impossible),
      (fun region' same => by
        cases same
        exact ⟨intrinsic, typed, answer, error, requires, stack⟩),
      (fun _ _ _ impossible => by cases impossible),
      (fun point role => by
        rcases role with impossible | ⟨ctx, impossible | impossible⟩ <;> cases impossible),
      (fun _ _ _ impossible => by cases impossible)⟩
    (fun _ _ ans post => by
      rw [ambientFiberInput_region]
      exact .pure ⟨post, by cases ans <;> exact entry⟩ ⟨entry, Row.subset_refl _⟩) ⟨entry, Row.subset_refl _⟩

/-- **The provider's protected entry** (`contextEntryR`, `internal/effect.ts:2087-2096`) at a row
the fiber's context covers: the context read, which covers the row; the update installed and the
region run at the installed row under the restore of the read context (`ambient_onExit_restore`);
or, when the update keeps the context, the region run as is. -/
theorem contextEntry_ambient (root : ProgramSource) {w : World} {available : Env.Requirement}
    {update : Env.ContextUpdate} {region : Region} {flag : Bool} {intrinsic ty : EffTy}
    (typed : RegionTyped root w region intrinsic)
    (answer : Ty.subN intrinsic.answer ty.answer = true)
    (error : Ty.subN intrinsic.error ty.error = true)
    (updateTyped : ContextUpdateTyped w update)
    (covers : ∀ previous : Env.Ctx, previous.Satisfies available →
      (update.apply previous).Satisfies intrinsic.requires ∧
        (update.apply previous).Satisfies available ∧
        RegionStackTyped root w (update.apply previous).keysRow region) :
    AmbientProg root w available ((ty, available, available) : AmbientPosition)
      (contextEntryR update region flag) := by
  unfold contextEntryR
  refine ambient_guardBind root (ambient_captureContext_typed root w available)
    (fun w1 o1 exit arm payload => ?_) (fun _ _ exit payload absent => ?_) (Row.subset_refl _)
  · cases exit with
    | failure cause => exact Bool.noConfusion arm
    | success value =>
      obtain ⟨previous, decoded, _⟩ := fits_context_inv payload.1.1
      have same : value = Val.context previous := Val.context?_exact decoded
      subst value
      obtain ⟨previousServices, previousCovers⟩ := ambient_captured_context payload
      have bound : Row.Subset available previous.services.keysRow :=
        (Provision.satisfies_iff_subset_keysRow _ available).mp previousCovers
      have installed := covers previous.services previousCovers
      have region1 := regionTyped_mono o1 typed
      simp only [seqR, ambientInput, Val.context?_context]
      split
      · rename_i keeps
        rw [apply_of_keepsIdentity keeps] at installed
        exact restoreRegion_ambient root flag region1 answer error
          ((Provision.satisfies_iff_subset_keysRow _ _).mp installed.1)
          (regionStackTyped_mono o1 installed.2.2) bound
      · let next : Ctx := Ctx.withServices (update.apply previous.services)
        have nextServices : ServicesFit w1 next.services :=
          updateTyped w1 o1 previous.services previousServices
        have nextBound : Row.Subset available next.services.keysRow :=
          (Provision.satisfies_iff_subset_keysRow _ available).mp installed.2.1
        refine ambient_guardBind root
          (mid := ((EffTy.pure .unit, next.services.keysRow, available) : AmbientPosition))
          (ambient_setContext_guarantees root w1 previous.services.keysRow available next
            nextServices bound nextBound)
          (fun w2 o2 exit' arm' _ => ?_) (fun _ _ exit' payload' absent' => ?_) bound
        · cases exit' with
          | failure cause => exact Bool.noConfusion arm'
          | success done =>
            simp only [seqR]
            exact ambient_onExit_restore root previous (servicesFit_mono o2 previousServices) bound
              (restoreRegion_ambient root flag (regionTyped_mono o2 region1) answer error
                ((Provision.satisfies_iff_subset_keysRow _ _).mp installed.1)
                (regionStackTyped_mono (leHost_trans _ _ _ o1 o2) installed.2.2) nextBound)
        · cases exit' with
          | success done => exact Bool.noConfusion absent'
          | failure cause =>
            exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload'.1, Row.subset_refl _⟩
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload.1, Row.subset_refl _⟩

/-- Where an admitted body's program leaves the fiber: a capture's release at the keys both the
previous context it restores and the entered one hold, every other body at the row it entered
at. -/
def bodyPosition (available : Env.Requirement) (body : Body) (cert : EffTy) : AmbientPosition :=
  match body with
  | .release _ previous =>
    (cert, rowMeet previous.services.keysRow available, rowMeet previous.services.keysRow available)
  | _ => (cert, available, available)

/-- **The body bridge** (decisions row 349): an admitted body's program, at any completed view,
entered at a row the fiber's context covers, is typed by the ambient judgment at the body's
position. -/
theorem bodyTyped_ambient (root : ProgramSource) {w : World} (hwf : SourceWF root)
    (htie : Tied root w) (completed : List (FiberId × ExitV)) {b : Body}
    {cert : EffTy} {available : Env.Requirement}
    (typed : BodyTyped root w b cert) (requires : Row.Subset cert.requires available)
    (acquired : ∀ point ctx, b = .acquireIn point ctx → ctx.services.Satisfies available)
    (coverage : BodyCoverage root w available b cert) :
    AmbientProg root w available (bodyPosition available b cert)
      (bodyR (interpRAt root.program completed) b) := by
  obtain ⟨regionCov, entryCov, pointCov, layerCov⟩ := coverage
  cases typed with
  | at_ p ty h =>
    exact denoteAt_ambient root hwf htie h requires (pointCov p (.inl rfl))
  | raceCleanup race =>
    exact ambient_fiberAdmin rfl (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => by
        subst post
        exact .pure ⟨strongExit_success w' _ _ trivial, Row.subset_refl _⟩ ⟨Row.subset_refl _, Row.subset_refl _⟩)
  | acquireIn p ctx ty h node hsvc =>
    obtain ⟨acquire, release, hat⟩ := node
    exact acquireIn_ambient root hwf htie h hat hsvc (acquired p ctx rfl) requires
      (pointCov p (.inr ⟨ctx, .inl rfl⟩))
  | release p previous _ h hsvc =>
    exact ambient_release_body root available p previous hsvc cert
      (denoteAt_ambient root hwf htie h requires (pointCov p (.inr ⟨previous, .inr rfl⟩)))
  | layerBuild p m scope lt h hlive hmemo =>
    obtain ⟨l, hat, hrest⟩ := h
    show AmbientProg root w available _ (layerBuildR root.program p m scope)
    simp only [layerBuildR, hat]
    exact layerBuild_typed hwf.refs hwf.layers l p w lt m scope available htie hat ⟨l, hat, hrest⟩
      hlive hmemo requires (layerCov p m scope rfl)
  | region body bodyTy ty typed answer error =>
    obtain ⟨intrinsic, typed', answer', error', inside, stack⟩ := regionCov body rfl
    exact region_ambient root hwf htie completed typed' answer' error' inside stack
  | contextEntry update body flag' bodyTy ty typed answer error updateTyped =>
    obtain ⟨intrinsic, typed', answer', error', covers⟩ := entryCov update body flag' rfl
    exact contextEntry_ambient root typed' answer' error' updateTyped covers

end Effect4.Program.Typed
