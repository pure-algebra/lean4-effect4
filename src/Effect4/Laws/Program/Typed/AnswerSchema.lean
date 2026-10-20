import Effect4.Laws.Program.Typed.Edits
import Effect4.Laws.Schema.Codec

/-!
# Laws.Program.Typed.AnswerSchema — a host answer decoded by its Schema, admitted at its token

Concept 5 (exact codecs) meeting Concept 1's membership (`Fits`), consumed by the host-answer edit of
the decision lane (`edit_answer`, `edit_answer`, the `DecisionKeeps` premise of
`decision_preserves`). The Schema JSON codec (`Schema.decode`) filters by the shape check
`Val.hasTy` (`hasTy_of_decode`); membership is stronger. On the shape-decided fragment
(`shapeDecides`, the classifier table's column) the two agree at every world
(`fits_of_hasTy_shapeDecides`). An exit is not in that fragment: its codec is total over every
representable exit, internal defects included, and its membership also asks a shape-free cause
(decisions row 152), so a decoded exit is typed exactly when that decidable check holds
(`exitOk_of_decode`). With the token's declaration that is the host answer's admission
(`answerOk_of_decode`), which the proved answer edit consumes (`decodedAnswer_keeps`).

Not established: the session-level correlation of the reply to its parked row and token (host
boundary, `docs/core/host-boundary.md`), world-reading answer types (handles, fibers, cells,
`unknown`), nested exits, or agreement with the target library's decoder.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-- A successful decode passes the shape check at the decoded type, under any key names. -/
theorem hasTy_of_decode {names : KeyNames} {t : Ty} {j : Json} {v : Val}
    (h : Schema.decode names t j = some v) : Val.hasTy v t = true := by
  have normal : Schema.decode names (CTy.ofRaw t).toRaw j = some v := by
    show Schema.decode names t.normalize j = some v
    rw [Schema.decode_policy, Ty.normalize_idem]
    exact h
  rw [← hasTy_normalize]
  exact Schema.hasTy_decode normal

/-- **A decoded value at a shape-decided type fits it**, at every world. -/
theorem fits_of_decode (w : World) {names : KeyNames} {t : Ty} {j : Json} {v : Val}
    (decided : shapeDecides t = true) (h : Schema.decode names t j = some v) : Fits w v t :=
  fits_of_hasTy_shapeDecides w t decided v [] (hasTy_of_decode h)

/-- An exit the shape check admits at shape-decided columns, with a shape-free cause, is typed. -/
theorem exitOk_of_hasTy (w : World) {ty : EffTy} {ex : ExitV} {allocated : List String}
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (hv : Val.hasTy (reifyExitVal ex) (.exitOf ty.answer ty.error) allocated = true)
    (shape : NoShapeDefect ty ex) : ExitOk w ty ex := by
  refine ⟨?_, shape⟩
  cases ex with
  | success v =>
    have hx : Val.hasTy v ty.answer allocated = true := hv
    exact (fitsExit_success_iff w ty v).mpr (fits_of_hasTy_shapeDecides w _ answer v allocated hx)
  | failure c =>
    have hc : Val.hasTy (Val.exitErr c) (.exitOf ty.answer ty.error) allocated = true := hv
    rw [hasTy_exitErr] at hc
    refine (fitsExit_failure_iff w ty c).mpr ⟨fun r hr => ?_, shape⟩
    have hr' := List.all_eq_true.mp hc r hr
    cases r with
    | fail err ann =>
      simp only [reasonAdmits] at hr'
      split at hr'
      · rename_i x hx
        exact ⟨x, hx, fits_of_hasTy_shapeDecides w _ error x allocated hr'⟩
      · exact Bool.noConfusion hr'
    | die _ _ => trivial
    | interrupt _ _ => trivial

/-- **A decoded exit is typed when its cause is shape-free**: the codec represents every exit, the
membership check on top is `NoShapeDefect`. -/
theorem exitOk_of_decode (w : World) {names : KeyNames} {ty : EffTy} {j : Json} {ex : ExitV}
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (decoded : Schema.decode names (.exitOf ty.answer ty.error) j = some (reifyExitVal ex))
    (shape : NoShapeDefect ty ex) : ExitOk w ty ex :=
  exitOk_of_hasTy w answer error (hasTy_of_decode decoded) shape

/-- **The decoded answer is admitted at its token** (`AnswerOk`): the token's declaration, a decode
at its exit type, a shape-free cause. The session's correlation of the reply to that token is the
host boundary's, not this theorem's. -/
theorem answerOk_of_decode {w : World} {m : RState} {target : FiberId} {token : Nat} {ty : EffTy}
    {names : KeyNames} {j : Json} {ex : ExitV} (declared : w.Θ target token = some ty)
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (decoded : Schema.decode names (.exitOf ty.answer ty.error) j = some (reifyExitVal ex))
    (shape : NoShapeDefect ty ex) :
    AnswerOk w m (.answerAsync target token (.ofExit ex)) :=
  fun _ => ⟨ty, declared, exitOk_of_decode w answer error decoded shape⟩

/-- **The answer edit keeps the typed configuration** for a decoded, shape-free answer at a
declared token (`edit_answer` with `answerOk_of_decode`). -/
theorem decodedAnswer_keeps (root : ProgramSource) (rootTy : EffTy) {w : World} {m : RState}
    {target : FiberId} {token : Nat} {ty : EffTy} {names : KeyNames} {j : Json} {ex : ExitV}
    (typed : MachineTyped root rootTy w m) (stuck : m.stuck = none)
    (declared : w.Θ target token = some ty)
    (answer : shapeDecides ty.answer = true) (error : shapeDecides ty.error = true)
    (decoded : Schema.decode names (.exitOf ty.answer ty.error) j = some (reifyExitVal ex))
    (shape : NoShapeDefect ty ex) :
    ∃ w', w.leHost w' ∧
      (letI := termEvaluatorFor root.program
       Machine.Lift.Guarded (MachineTyped root rootTy) (ConfigTyped root rootTy)
         (SnapshotTyped root) [] w'
         (driveStep (interpR root.program)
           { m with state := (prepareAsyncAnswer (interpR root.program) m target token
             (.ofExit ex)).1 }
           (.resume target token
             (prepareAsyncAnswer (interpR root.program) m target token (.ofExit ex)).2)
           [Cmd.drainDue]).1
         (driveStep (interpR root.program)
           { m with state := (prepareAsyncAnswer (interpR root.program) m target token
             (.ofExit ex)).1 }
           (.resume target token
             (prepareAsyncAnswer (interpR root.program) m target token (.ofExit ex)).2)
           [Cmd.drainDue]).2) :=
  edit_answer root rootTy w m target token (.ofExit ex) typed stuck
    (answerOk_of_decode declared answer error decoded shape)

/-! ## Membership under a table on the shape-decided fragment

A shape-decided type (`shapeDecides`, the classifier table's column) names no reference: the
reference's row is not shape-decided. So a member of such a type under any declaration table
passes the shape check, and the shape check is membership there at every world
(`fits_of_hasTy_shapeDecides`). A host answer the session admits under the application's table
is then a member of a shape-decided column at every world (`HostSession.PreparedSuccess`). -/

/-- A record frame's questions are at its fields' types. -/
theorem namedPairs_types : ∀ (cs : List (String × Bool × Ty)) (ns xs : List Val)
    {ps : List (Val × Ty)}, namedPairs cs ns xs = some ps → ∀ p ∈ ps, ∃ c ∈ cs, c.2.2 = p.2 := by
  intro cs ns xs
  fun_induction namedPairs cs ns xs with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 _ _ _ ih =>
    intro ps h p hp
    obtain ⟨c, hc, he⟩ := ih h p hp
    exact ⟨c, List.mem_cons_of_mem _ hc, he⟩
  | case3 =>
    intro ps h
    cases h
  | case4 o t cs n ns x xs ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hq
    · exact ⟨(n, o, t), List.mem_cons_self, rfl⟩
    · obtain ⟨c, hc, he⟩ := ih hqs p hq
      exact ⟨c, List.mem_cons_of_mem _ hc, he⟩
  | case5 _ _ _ _ _ _ _ _ ih =>
    intro ps h p hp
    obtain ⟨c, hc, he⟩ := ih h p hp
    exact ⟨c, List.mem_cons_of_mem _ hc, he⟩
  | case6 =>
    intro ps h
    cases h
  | case7 =>
    intro ps h
    cases h

/-- A tuple's questions are at its items' types. -/
theorem itemPairs_types : ∀ (ts : List Ty) (xs : List Val) {ps : List (Val × Ty)},
    itemPairs ts xs = some ps → ∀ p ∈ ps, p.2 ∈ ts := by
  intro ts xs
  fun_induction itemPairs ts xs with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 t ts x xs ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hqs p hq)
  | case3 =>
    intro ps h
    cases h

/-- A map's questions are at its key type or its value type. -/
theorem entryPairs_types (key value : Ty) : ∀ (es : List Val) {ps : List (Val × Ty)},
    entryPairs key value es = some ps → ∀ p ∈ ps, p.2 = key ∨ p.2 = value := by
  intro es
  fun_induction entryPairs key value es with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 a x es ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl rfl
    rcases List.mem_cons.mp hp with rfl | hq
    · exact Or.inr rfl
    · exact ih hqs p hq
  | case3 =>
    intro ps h
    cases h

/-- A cause's questions are at its error type. -/
theorem causeObligations_types (error : Ty) : ∀ (rs : List (Reason Err Defect FiberId Ann))
    {ps : List (Val × Ty)}, causeObligations error rs = some ps → ∀ p ∈ ps, p.2 = error := by
  intro rs
  fun_induction causeObligations error rs with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 e ann rs x hx ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hq
    · rfl
    · exact ih hqs p hq
  | case3 =>
    intro ps h
    cases h
  | case4 r rs _ ih => exact ih

/-- **The questions of a shape-decided type are at shape-decided types.** -/
theorem obligations_shapeDecides {v : Val} {t : Ty} {allocated : List String}
    {ps : List (Val × Ty)} (hs : shapeDecides t = true)
    (h : Val.obligations v t allocated = some ps) : ∀ p ∈ ps, shapeDecides p.2 = true := by
  intro p hp
  cases t with
  | option a =>
    have ha : shapeDecides a = true := hs
    simp only [Val.obligations] at h
    split at h
    · cases h; cases hp
    · cases h
      rcases List.mem_singleton.mp hp with rfl
      exact ha
    · cases h
  | list a =>
    have ha : shapeDecides a = true := hs
    simp only [Val.obligations] at h
    split at h
    · obtain ⟨ids, _, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨id, _, rfl⟩ := List.mem_map.mp hp
      exact ha
    · cases h
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      exact ha
    · cases h
  | prod a b =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp (show (shapeDecides a && shapeDecides b) = true from hs)
    simp only [Val.obligations] at h
    split at h
    · cases h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ha
      · rcases List.mem_singleton.mp hp with rfl
        exact hb
    · cases h
  | except e a =>
    obtain ⟨he, ha⟩ := Bool.and_eq_true_iff.mp (show (shapeDecides e && shapeDecides a) = true from hs)
    simp only [Val.obligations] at h
    split at h
    · cases h
      rcases List.mem_singleton.mp hp with rfl
      exact he
    · cases h
      rcases List.mem_singleton.mp hp with rfl
      exact ha
    · cases h
  | causeOf e =>
    have he : shapeDecides e = true := hs
    simp only [Val.obligations] at h
    obtain ⟨c, _, hc⟩ := Option.bind_eq_some_iff.mp h
    rw [causeObligations_types e c.reasons hc p hp]
    exact he
  | record fs =>
    have hs' : ∀ q ∈ fs, shapeDecides q.2.2 = true := by
      unfold shapeDecides at hs
      rw [allHeads_record ClassRow.shapeDecides rfl] at hs
      exact fun q hq => List.all_eq_true.mp hs q hq
    simp only [Val.obligations] at h
    obtain ⟨parts, _, hparts⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, hc, he⟩ := namedPairs_types _ _ _ hparts p hp
    rw [← he]
    exact hs' c (Ty.mem_canon hc)
  | map k a =>
    obtain ⟨hk, ha⟩ := Bool.and_eq_true_iff.mp (show (shapeDecides k && shapeDecides a) = true from hs)
    simp only [Val.obligations] at h
    split at h
    · split at h
      · rcases entryPairs_types k a _ h p hp with he | he <;> rw [he]
        · exact hk
        · exact ha
      · cases h
    · cases h
  | tuple ts =>
    have hs' : ∀ u ∈ ts, shapeDecides u = true := by
      unfold shapeDecides at hs
      rw [allHeads_tuple ClassRow.shapeDecides rfl] at hs
      exact fun u hu => List.all_eq_true.mp hs u hu
    simp only [Val.obligations] at h
    split at h
    · exact hs' _ (itemPairs_types _ _ h p hp)
    · cases h
  | union l r => cases h
  | exitOf _ _ | handle _ | fiberOf _ _ | refOf _ | deferredOf _ _ | unknown | app _ _
  | contextOf _ => exact Bool.noConfusion hs
  | _ =>
    simp only [Val.obligations] at h
    split at h
    · cases h; cases hp
    · cases h

/-- **On the shape-decided fragment, membership under any table is the shape check**: a member of
a shape-decided type under a declaration table passes `Val.hasTy`. The reference's row is not
shape-decided, so no step unfolds a name, and each question of a step is at a shape-decided
type (`obligations_shapeDecides`). Placement: concept `store-typing`, R3; consumer the session's
admitted successes (`HostSession.preflight_success_prepared_fits`). -/
theorem hasTy_of_memberIn_shapeDecides {decls : TyDecls} {allocated : List String} {v : Val}
    {t : Ty} (h : MemberIn decls allocated v t) (hs : shapeDecides t = true) :
    Val.hasTy v t allocated = true := by
  induction h with
  | @left v l r _ ih =>
    obtain ⟨hl, _⟩ := Bool.and_eq_true_iff.mp (show (shapeDecides l && shapeDecides r) = true from hs)
    simp only [Val.hasTy, ih hl, Bool.true_or]
  | @right v l r _ ih =>
    obtain ⟨_, hr⟩ := Bool.and_eq_true_iff.mp (show (shapeDecides l && shapeDecides r) = true from hs)
    simp only [Val.hasTy, ih hr, Bool.or_true]
  | unfold hu _ _ =>
    obtain ⟨n, args, rfl⟩ := TyDecls.ref_of_unfold? hu
    exact Bool.noConfusion hs
  | @step v t ps _ hobl _ ih =>
    rw [hasTy_eq_obligationsAll (Val.isMember_of_obligations hobl)]
    unfold obligationsAll
    rw [hobl]
    exact List.all_eq_true.mpr fun p hp => ih p hp (obligations_shapeDecides hs hobl p hp)

end Effect4.Program.Typed
