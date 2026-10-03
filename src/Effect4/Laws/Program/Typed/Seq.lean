import Effect4.Laws.Program.Typed.Residual
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typed.Seq — the sequencing lemma `denoteR`'s bind needs

Formal pass, algebra note A4 and its verification (ALG-04: `algebra/verify-BindGuard.lean`,
ported to the merged tree's typed exits in
`docs/research/2026-10-01-landing/ports-at-dceae006/HeadBindGuard.lean`). The generic protocol
judgment is closed under sequencing (`Typed.bind`, `Laws/Effects/Protocol.lean`); the concrete
`TypedProg` is not. A closing marker carries an exit at the current type, so a continuation
cannot retype it (`typedProg_not_bind_closed`), and a guard's skipped exit bypasses the
continuation, so even a first program whose only closing marker sits inside a guard body does
not bind (`bind_not_typed`); both are red controls in `Test/Program/TypedProgBindRed.lean`. The
context `bind k` is neutral; the failure comes from the program's non-local exits, the principle
that non-local control flow breaks the bind rule (Timany and Birkedal, as de Vilhena 2022 §2.4
cites them; read in `docs/research/2026-09-05-effects-papers-review.md` G8). Hazel's restriction
of `Bind` to neutral contexts is only a loose analogy (verifier ALG-04).

M5's sequencing tool is therefore one compatibility lemma per guard shape. Every guard
`denoteR` builds is `(guardR kind a).bind K` (`DenoteR.lean`), so one lemma carries them all:

* `close_typed`: closing a typed program with `unguard` keeps its type (the marker's payload is
  at the current type, and the machine never resumes a closed marker); one induction, every arm
  a constructor;
* `guardBind_typed`: the body at an intermediate type, the continuation on every exit the arm
  takes, every skipped exit at the result: the guarded sequence is typed (the body by
  `close_typed`);
* its shapes: `seqGuard_typed` (`onSuccess`: `bind` and the joins' sequencing; `seq_typed` is its
  instance at `seqR`), `catchGuard_typed` (`onFailure`: `catchCause`, `catchIf`, `orDie`, a
  finalizer's cleanup), `allGuard_typed` (`all`, `onExit`: `exit`, `matchCause`, a finalizer's
  boundary); `finalizer_typed` and `onExit_typed` for `finalizerR` and `onExitR`;
* `typedProg_widen`: a typed program is typed at every type above it in the checker's order.

Exits are read through `ExitOk` (H2 part one), at every typed exit position. Decisions row 148:
these are the compatibility lemmas M5's denotation lemma rests on
(`Typed/Denotation.lean`).
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **Closing keeps the type.** Closing a typed program with `unguard` is typed at the same
type: every leaf becomes a closing marker carrying the leaf's exit. -/
@[semantics "residual-program-typing"]
theorem close_typed (root : ProgramSource) {w : World} {T : EffTy} {a : RProgram}
    (h : TypedProg root w T a) (g : ExitV → RProgram) :
    TypedProg root w T (a.bind (fun ex => .vis (.inr (.unguard ex)) g)) := by
  induction h with
  | pure exit => exact .unguard exit
  | store cert pre _ ih => exact .store cert pre (fun w' o ans post => ih w' o ans post)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert pre
      (fun w' o ans post => ih w' o ans post)
  | guard mid _ _ skip ihBody ihRun =>
    exact .guard mid ihBody (fun w' o ex post => ihRun w' o ex post) skip
  | unguard payload => exact .unguard payload
  | finishFinalizer payload => exact .finishFinalizer payload
  | scopedGuard mid prev sc _ callback live services widen ihBody =>
    exact .scopedGuard mid prev sc ihBody
      (fun ex => Contracts.scopeExitCallback?_bind (callback ex) _) live services widen

/-- A failed exit's judgment moves along the checker's order on error columns: only `Fail`
reasons read the column, and the shape exclusion reads no type. -/
theorem exitOk_failure_of_errorN {w : World} {mid ty : EffTy} {c : CauseV}
    (herr : Ty.subN mid.error ty.error = true) (h : ExitOk w mid (.failure c)) :
    ExitOk w ty (.failure c) := by
  refine ⟨?_, h.2⟩
  have hf := h.1
  rw [fitsExit_failure_iff] at hf ⊢
  exact ⟨causeFits_map (fun x hx => fits_subN w herr x hx) hf.1, hf.2⟩

/-- A successful exit's judgment moves along the checker's order on answer columns. -/
theorem exitOk_success_of_answerN {w : World} {mid ty : EffTy} {v : Val}
    (hans : Ty.subN mid.answer ty.answer = true) (h : ExitOk w mid (.success v)) :
    ExitOk w ty (.success v) :=
  strongExit_success w ty v (fits_subN w hans v h.1)

/-- An exit's judgment moves along the checker's order on both columns. -/
theorem exitOk_widen {w : World} {mid ty : EffTy} {ex : ExitV}
    (hans : Ty.subN mid.answer ty.answer = true) (herr : Ty.subN mid.error ty.error = true)
    (h : ExitOk w mid ex) : ExitOk w ty ex :=
  ⟨fitsExit_subN hans herr h.1, h.2⟩

/-- **The guard compatibility lemma** (the general form of `seq_typed`, decisions row 148): a
first program typed at `mid`, a continuation typed at `ty` at every later world on every exit the
guard's arm takes and `mid` admits, and every exit the arm does not take admitted at `ty`: the
guarded sequence is typed at `ty`. Every guard `denoteR` builds has this shape
(`guardR kind a`, bound to a continuation); the body closes by `close_typed`. -/
theorem guardBind_typed (root : ProgramSource) {w : World} {mid ty : EffTy} {kind : GuardKind}
    {a : RProgram} {K : ExitV → RProgram} (ha : TypedProg root w mid a)
    (hrun : ∀ w', w.leHost w' → ∀ ex, kind.hasExitArm ex = true → ExitOk w' mid ex →
      TypedProg root w' ty (K ex))
    (hskip : ∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
      ExitOk w' ty ex) :
    TypedProg root w ty ((guardR kind a).bind K) := by
  show TypedProg root w ty (.vis (.inr (.guard_ kind)) _)
  refine TypedProg.guard mid ?_ (fun w' o ex hpost => hrun w' o ex hpost.1 hpost.2) hskip
  show TypedProg root w mid
    ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind K)
  rw [Effects.Program.bind_assoc]
  exact close_typed root ha K

/-- **The `scoped` arm's code** (decisions row 188 (a)): `evaluateFiberR`'s `.scoped` arm
(`EvaluateR.lean`) installs the `onExit false` guard over the body, bound to the scope's exit
callback. It is typed at `ty` when the body is typed at `mid`, the scope is present, the context
the callback restores fits, and every exit `mid` admits fits `ty`. The callback is typed only at
this run position (`TypedProg.scopedGuard`); as code it is not (`E4-TYPED-CE-034`). Consumer: the
`scoped` arm of `M6Ledger.step_loop` and `M6Ledger.step_deliver`. -/
theorem scopedGuardBind_typed (root : ProgramSource) {w : World} {mid ty : EffTy} {a : RProgram}
    {prev : Ctx} {sc : Nat} {j : ExitV → RProgram} (ha : TypedProg root w mid a)
    (live : ScopeLive w sc) (services : ServicesFit w prev.services)
    (widen : ∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → ExitOk w' ty ex) :
    TypedProg root w ty
      ((guardR (.onExit false) a).bind fun ex => .vis (.inr (.scopeExit prev sc ex)) j) := by
  show TypedProg root w ty (.vis (.inr (.guard_ (.onExit false))) _)
  refine TypedProg.scopedGuard mid prev sc ?_ (fun _ => rfl) live services widen
  show TypedProg root w mid
    ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind _)
  rw [Effects.Program.bind_assoc]
  exact close_typed root ha fun ex => .vis (.inr (.scopeExit prev sc ex)) j

/-- **The `onSuccess` shape** (`bind`, the joins' sequencing): the continuation at every success
`mid` admits; a failure skips it and must fit `ty`'s error column, below which `mid`'s is. -/
theorem seqGuard_typed (root : ProgramSource) {w : World} {mid ty : EffTy} {a : RProgram}
    {K : ExitV → RProgram} (ha : TypedProg root w mid a)
    (herr : Ty.subN mid.error ty.error = true)
    (hrun : ∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (K (.success v))) :
    TypedProg root w ty ((guardR .onSuccess a).bind K) := by
  refine guardBind_typed root ha (fun w' o ex harm hex => ?_) (fun w' _ ex hex hmiss => ?_)
  · cases ex with
    | success v => exact hrun w' o v hex.1
    | failure c => exact Bool.noConfusion harm
  · cases ex with
    | success v => exact Bool.noConfusion hmiss
    | failure c => exact exitOk_failure_of_errorN herr hex

/-- **The `onFailure` shape** (`catchCause`, `catchIf`, `orDie`, a finalizer's cleanup): the
continuation at every failure `mid` admits; a success skips it and must fit `ty`'s answer
column, below which `mid`'s is. -/
theorem catchGuard_typed (root : ProgramSource) {w : World} {mid ty : EffTy} {a : RProgram}
    {K : ExitV → RProgram} (ha : TypedProg root w mid a)
    (hans : Ty.subN mid.answer ty.answer = true)
    (hrun : ∀ w', w.leHost w' → ∀ c, ExitOk w' mid (.failure c) →
      TypedProg root w' ty (K (.failure c))) :
    TypedProg root w ty ((guardR .onFailure a).bind K) := by
  refine guardBind_typed root ha (fun w' o ex harm hex => ?_) (fun w' _ ex hex hmiss => ?_)
  · cases ex with
    | success v => exact Bool.noConfusion harm
    | failure c => exact hrun w' o c hex
  · cases ex with
    | success v => exact exitOk_success_of_answerN hans hex
    | failure c => exact Bool.noConfusion hmiss

/-- **The `all` and `onExit` shapes** (`exit`, `matchCause`, a finalizer's boundary): a guard
whose arm takes every exit runs the continuation on every exit `mid` admits; nothing skips. -/
theorem allGuard_typed (root : ProgramSource) {w : World} {mid ty : EffTy} {kind : GuardKind}
    (hall : ∀ ex, kind.hasExitArm ex = true) {a : RProgram} {K : ExitV → RProgram}
    (ha : TypedProg root w mid a)
    (hrun : ∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → TypedProg root w' ty (K ex)) :
    TypedProg root w ty ((guardR kind a).bind K) :=
  guardBind_typed root ha (fun w' o ex _ hex => hrun w' o ex hex)
    (fun _ _ ex _ hmiss => absurd (hall ex) (by rw [hmiss]; exact Bool.false_ne_true))

/-- **The `seqR` compatibility lemma.** A first program typed at `mid`, a value continuation
typed at `ty` at every later world on every value that fits `mid`'s answer column, and equal
error columns: the sequence `denoteR` builds is typed at `ty`. A failure of the first program
skips the continuation and must fit `ty`'s error column, which the equal columns give. The
instance of `seqGuard_typed` at `seqR`. -/
@[semantics "residual-program-typing"]
theorem seq_typed (root : ProgramSource) {w : World} {mid ty : EffTy} {a : RProgram}
    {k : Val → RProgram} (ha : TypedProg root w mid a)
    (hk : ∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (k v))
    (herr : mid.error = ty.error) :
    TypedProg root w ty ((guardR .onSuccess a).bind (seqR k)) :=
  seqGuard_typed root ha (herr ▸ Ty.subN_refl _) hk

/-- **Widening along the checker's order** (proved): a program typed at `T` is typed at every
type above it in both columns. Every exit the program carries moves up
(`exitOk_widen`); a guard's body keeps its intermediate type. -/
theorem typedProg_widen (root : ProgramSource) {w : World} {T T' : EffTy} {p : RProgram}
    (hans : Ty.subN T.answer T'.answer = true) (herr : Ty.subN T.error T'.error = true)
    (h : TypedProg root w T p) : TypedProg root w T' p := by
  induction h with
  | pure exit => exact .pure (exitOk_widen hans herr exit)
  | store cert pre _ ih => exact .store cert pre (fun w' o ans post => ih w' o ans post hans herr)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert pre
      (fun w' o ans post => ih w' o ans post hans herr)
  | guard mid body _ skip _ ihRun =>
    exact .guard mid body (fun w' o ex post => ihRun w' o ex post hans herr)
      (fun w' o ex hfit harm => exitOk_widen hans herr (skip w' o ex hfit harm))
  | unguard payload => exact .unguard (exitOk_widen hans herr payload)
  | finishFinalizer payload => exact .finishFinalizer (exitOk_widen hans herr payload)
  | scopedGuard mid prev sc body callback live services widen _ =>
    exact .scopedGuard mid prev sc body callback live services
      (fun w' o ex hex => exitOk_widen hans herr (widen w' o ex hex))

/-- The exit a failed finalizer leaves after a failed body: both causes combined
(`Exit.restoreAfterFinalizer`, rc.112's `combineFinalizerCause`), typed at a column both fit. -/
theorem exitOk_restore {w : World} {ty : EffTy} {cause c : CauseV}
    (hbody : ExitOk w ty (.failure cause)) (hfin : ExitOk w ty (.failure c)) :
    ExitOk w ty (Exit.restoreAfterFinalizer (.failure cause) (.failure c)) := by
  show ExitOk w ty (.failure (Cause.combine cause c))
  have hb := (fitsExit_failure_iff w ty cause).mp hbody.1
  have hf := (fitsExit_failure_iff w ty c).mp hfin.1
  refine ⟨(fitsExit_failure_iff w ty _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
  · rcases (Cause.mem_combine r cause c).mp hr with hm | hm
    · exact hb.1 r hm
    · exact hf.1 r hm
  · rcases (Cause.mem_combine r cause c).mp hr with hm | hm
    · exact hb.2 r hm
    · exact hf.2 r hm
  · rcases (Cause.mem_combine r cause c).mp hr with hm | hm
    · exact hbody.2 r hm
    · exact hfin.2 r hm

/-- **A finalizer's boundary under any continuation** (`finalizerR`, `DenoteR.lean`): the cleanup
typed at `f`, whose error column is below the result's, and the restored exit typed at the result:
the boundary, bound to any continuation, is typed at the result. A succeeding cleanup is followed by
the `finishFinalizer` marker carrying the restored exit, which reads no continuation; a failing
cleanup after a failed body combines both causes; every other exit skips the bind
(`seqGuard_typed`). The scoped exit's close binds the callback's continuation after the boundary
(`prepareScopedExitR`). -/
theorem finalizerBind_typed (root : ProgramSource) {w : World} {ty f : EffTy} {ex : ExitV}
    {cleanup : RProgram} (hex : ExitOk w ty ex) (herr : Ty.subN f.error ty.error = true)
    (hclean : TypedProg root w f cleanup) (next : ExitV → RProgram) :
    TypedProg root w ty ((finalizerR ex cleanup).bind next) := by
  unfold finalizerR
  rw [Effects.Program.bind_assoc]
  refine seqGuard_typed root (mid := ⟨f.answer, ty.error, f.requires⟩) ?_ (Ty.subN_refl _)
    (fun w' o _ _ => .finishFinalizer (strongExit_mono _ _ _ _ o hex))
  cases ex with
  | success v => exact typedProg_widen root (T := f) (Ty.subN_refl _) herr hclean
  | failure cause =>
    refine catchGuard_typed root hclean (Ty.subN_refl _) (fun w' o c hc => ?_)
    exact .pure (exitOk_restore (strongExit_mono _ _ _ _ o hex)
      (exitOk_failure_of_errorN herr hc))

/-- **A finalizer's boundary** (`finalizerR`), at the empty continuation. -/
theorem finalizer_typed (root : ProgramSource) {w : World} {ty f : EffTy} {ex : ExitV}
    {cleanup : RProgram} (hex : ExitOk w ty ex) (herr : Ty.subN f.error ty.error = true)
    (hclean : TypedProg root w f cleanup) : TypedProg root w ty (finalizerR ex cleanup) := by
  have h := finalizerBind_typed root hex herr hclean Effects.Program.pure
  rw [Effects.Program.bind_pure_right] at h
  exact h

/-- **The `onExit` shape** (`onExitR`, `DenoteR.lean`): the body typed at `b`, below the result
in both columns, and the finalizer typed at `f` on every exit `b` admits, its error column below
the result's: the region is typed at the result. The guard's arm takes every exit
(`allGuard_typed`); each runs the finalizer's boundary (`finalizer_typed`). -/
theorem onExit_typed (root : ProgramSource) {w : World} {b f ty : EffTy} {body : RProgram}
    {fin : ExitV → RProgram} {flag : Bool} (hans : Ty.subN b.answer ty.answer = true)
    (herrb : Ty.subN b.error ty.error = true) (herrf : Ty.subN f.error ty.error = true)
    (hbody : TypedProg root w b body)
    (hfin : ∀ w', w.leHost w' → ∀ ex, ExitOk w' b ex → TypedProg root w' f (fin ex)) :
    TypedProg root w ty (onExitR body fin flag) := by
  unfold onExitR
  refine allGuard_typed root (fun ex => by cases ex <;> rfl) hbody (fun w' o ex hex => ?_)
  exact finalizer_typed root (exitOk_widen hans herrb hex) herrf (hfin w' o ex hex)

end Effect4.Program.Typed
