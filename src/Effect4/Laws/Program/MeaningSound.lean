import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Progress
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.Decision
import Effect4.Laws.Program.Typing.Inversion
import Effect4.Laws.Program.Template
import Effect4.Laws.Program.Agreement.Machine

/-!
# Type soundness of the meaning

A typed program of the straight fragment does not go wrong, and what it answers has its type.
This is obligation O9 at the level of the meaning, and `run_typed` carries it to the machine
through `run_eq_meaning`.

* **Not going wrong needs no predicate on exits.** `denoteWith bad` is `denote` with the
  wrong-shape exit as a parameter (`denoteWith_badShape`). A typed program's run does not
  depend on that parameter (`meaning_never_wrong`): no arm that answers it is reached. An exit
  predicate could not say this, because a program may legitimately die.
* **The exit has the type** (`meaning_typed`, `ExitOk`): a success is a valid value of the
  answer type, and every typed failure of a cause is inside the error type. Defects and
  interruptions are outside the error type by construction.
* **The invariant a run keeps** (`TypedAt`): the environment fits its types, every value in it
  is valid in the stores, the stores are well-formed, and every cell holds a number (the one
  cell type this cut spells, `Progress.lean`).

The proof is one induction (`sound`) over a pair of programs run side by side (`SoundP`), with
one sequencing lemma (`SoundP.bind`) that every composite arm uses. What it needed and the
tree did not have: a term over valid values evaluates to a valid value (`evalTerm_validIn`),
what a decision binds is valid (`Decision.decide_validIn`), and cause admission under
`Cause.combine` (`causeAdmits_combine`).

Scope: the empty row table (`nativeSignature` at its default), the straight fragment. Loops
(`denoteB` on `Looped`) and external rows are not covered here.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program
open Conform.Effect4.Typing

/-- `denote`, with the exit of a wrong-shaped program as a parameter. -/
def denoteWith (bad : ExitV) : NativeEff → List Val → Effects.Program StoreSig ExitV
  | .succeed v, env =>
    pure (match evalTerm env v with | some x => Exit.success x | none => bad)
  | .fail e, env =>
    pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => bad)
  | .failCause c, env =>
    pure (match causeOf env c with | some cause => Exit.failure cause | none => bad)
  | .sync t, env => pure (Exit.success ((evalTerm env t).getD Val.unit))
  | .suspend b, env => denoteWith bad b env
  | .perform op r, env =>
    match (NativeOp.row op).kind with
    | .sync =>
      match (evalTerm env r).bind (NativeOp.syncOpOf op) with
      | some o =>
        Effects.Program.bind (Effects.Program.perform (S := StoreSig) o) fun v =>
          pure (Exit.success v)
      | none => pure bad
    | _ => pure outsideExit
  | .bind a b, env =>
    Effects.Program.bind (denoteWith bad a env) (seqExit fun v => denoteWith bad b (env ++ [v]))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteWith bad a (env ++ bound.toList)
    | some (false, bound) => denoteWith bad b (env ++ bound.toList)
    | none => pure bad
  | .exit b, env =>
    Effects.Program.bind (denoteWith bad b env) fun ex => pure (Exit.success (reifyExitVal ex))
  | .catchCause b h, env => Effects.Program.bind (denoteWith bad b env) fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure c => denoteWith bad h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => Effects.Program.bind (denoteWith bad b env) fun
    | Exit.success x => denoteWith bad v (env ++ [x])
    | Exit.failure cause => denoteWith bad c (env ++ [Val.exitErr cause])
  | .onExit b f, env => Effects.Program.bind (denoteWith bad b env) fun ex =>
    Effects.Program.bind (denoteWith bad f (env ++ [reifyExitVal ex])) fun fex =>
      pure (Exit.restoreAfterFinalizer ex (finVoid fex))
  | _, _ => pure outsideExit

/-- At the wrong-shape exit the parameterized meaning is the meaning. -/
theorem denoteWith_badShape : ∀ (e : NativeEff) (env : List Val),
    denoteWith badShapeExit e env = denote e env
  | .succeed v, env | .fail v, env => by
    rw [denoteWith, denote]
    cases evalTerm env v <;> rfl
  | .failCause c, env => by
    rw [denoteWith, denote]
    cases causeOf env c <;> rfl
  | .sync _, _ => by rw [denoteWith, denote]
  | .perform op r, env => by
    rw [denoteWith, denote]
    cases (NativeOp.row op).kind with
    | sync => cases (evalTerm env r).bind (NativeOp.syncOpOf op) <;> rfl
    | async => rfl
    | program => rfl
  | .suspend b, env => by rw [denoteWith, denote, denoteWith_badShape b env]
  | .bind a b, env => by
    rw [denoteWith, denote, denoteWith_badShape a env]
    congr 1
    funext ex
    cases ex with
    | success v => exact denoteWith_badShape b (env ++ [v])
    | failure c => rfl
  | .select t d a b, env => by
    rw [denoteWith, denote]
    cases (evalTerm env t).bind d.decide with
    | none => rfl
    | some r =>
      obtain ⟨flag, bound⟩ := r
      cases flag with
      | true => exact denoteWith_badShape a (env ++ bound.toList)
      | false => exact denoteWith_badShape b (env ++ bound.toList)
  | .exit b, env => by rw [denoteWith, denote, denoteWith_badShape b env]
  | .catchCause b h, env => by
    rw [denoteWith, denote, denoteWith_badShape b env]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denoteWith_badShape h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => by
    rw [denoteWith, denote, denoteWith_badShape b env]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteWith_badShape v (env ++ [x])
    | failure cause => exact denoteWith_badShape c (env ++ [Val.exitErr cause])
  | .onExit b f, env => by
    rw [denoteWith, denote, denoteWith_badShape b env]
    congr 1
    funext ex
    rw [denoteWith_badShape f (env ++ [reifyExitVal ex])]
  | .gen _, _ | .uninterruptible _, _ | .interruptible _, _
  | .iterate _ _ _ _ _ _, _ | .yieldNow _, _ | .awaitFiber _ _, _
  | .withFiber _, _ | .scoped _, _ | .acquireRelease _ _, _ | .provideLayer _ _ _, _
  | .service _, _ | .provideService _ _ _, _ | .catchIf _ _ _, _ => by
    rw [denoteWith, denote]
    all_goals (intros; rename_i heq; cases heq)

theorem valOfErr_validIn (s : Stores) (e : Err) (v : Val) (h : valOfErr e = some v) :
    v.validIn s = true := by
  cases e with
  | boom => cases h
  | tag n => cases h; rfl
  | tagged t m => cases h; rfl
  | text t => cases h; rfl

theorem validIn_list_mem {s : Stores} {vs : List Val} (h : Val.validIn s (.list vs) = true) :
    ∀ x ∈ vs, x.validIn s = true := by
  rw [Val.validIn_list] at h
  exact fun x hx => List.all_eq_true.mp h x hx

theorem validIn_list_of_mem {s : Stores} {vs : List Val} (h : ∀ x ∈ vs, x.validIn s = true) :
    Val.validIn s (.list vs) = true := by
  rw [Val.validIn_list]
  exact List.all_eq_true.mpr h

/-- A list read back holds only valid values when its value is valid: the value is that list,
or the snapshot that carries it (`Val.asList?_exact`). -/
theorem asList?_validIn {s : Stores} {v : Val} {vs : List Val} (h : Val.asList? v = some vs)
    (hv : v.validIn s = true) : ∀ x ∈ vs, x.validIn s = true := by
  rcases Val.asList?_exact h with rfl | rfl
  · exact validIn_list_mem hv
  · exact validIn_list_mem (Bool.and_eq_true_iff.mp hv).1

theorem NativeAtom.eval_validIn (s : Stores) (atom : NativeAtom) (vs : List Val) (v : Val)
    (hvs : ∀ x ∈ vs, x.validIn s = true) (h : atom.eval vs = some v) : v.validIn s = true := by
  unfold NativeAtom.eval at h
  split at h
  case h_9 a b =>
    cases h
    exact validIn_list_of_mem hvs
  case h_10 a rest =>
    cases h
    exact validIn_list_mem (hvs _ (List.mem_cons_self ..)) _ (List.mem_cons_self ..)
  case h_11 a b rest =>
    cases h
    exact validIn_list_mem (hvs _ (List.mem_cons_self ..)) _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  case h_12 =>
    unfold stringsAtom at h
    split at h
    · cases h
      exact validIn_list_of_mem hvs
    · cases h
  case h_13 value | h_15 value | h_16 value =>
    unfold queryTag at h
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  case h_14 value =>
    unfold queryError at h
    obtain ⟨reasons, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    split
    · rfl
    · next error herr =>
      obtain ⟨e, _, he⟩ := Option.bind_eq_some_iff.mp herr
      exact valOfErr_validIn s e error he
  case h_22 fallback =>
    cases h
    exact hvs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  case h_23 value other =>
    cases h
    have := hvs _ (List.mem_cons_self ..)
    exact this
  -- the selection answers one of its branches, whole
  case h_24 c a b =>
    cases h
    cases c
    · exact hvs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact hvs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  case h_25 a =>
    cases h
    exact hvs a (List.mem_cons_self ..)
  -- the list atoms answer members of their list arguments, or a count
  case h_29 x xs =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    have hxs := asList?_validIn hl (hvs xs (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    exact validIn_list_of_mem fun y hy => (List.mem_cons.mp hy).elim
      (fun hyx => hyx ▸ hvs x (List.mem_cons_self ..)) (hxs y)
  case h_30 xs i =>
    obtain ⟨elems, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    split
    · next e he =>
      exact asList?_validIn hl (hvs xs (List.mem_cons_self ..)) e (List.mem_of_getElem? he)
    · rfl
  case h_31 xs =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  case h_32 xs ys =>
    obtain ⟨front, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨back, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact validIn_list_of_mem fun y hy => (List.mem_append.mp hy).elim
      (asList?_validIn hf (hvs xs (List.mem_cons_self ..)) y)
      (asList?_validIn hb (hvs ys (List.mem_cons_of_mem _ (List.mem_cons_self ..))) y)
  all_goals cases h
  all_goals rfl

theorem Lit.toVal_validIn (s : Stores) (l : Lit) (v : Val) (h : l.toVal = some v) :
    v.validIn s = true := by
  cases l with
  | unit => cases h; rfl
  | nat n => cases h; rfl
  | bool b => cases h; rfl
  | str t => cases h; rfl

mutual
/-- A term over valid values evaluates to a valid value: an atom builds scalars or rearranges
its arguments, and no term mints a handle. -/
theorem evalTerm_validIn (s : Stores) (t : Term) (env : List Val) (v : Val)
    (henv : ∀ x ∈ env, x.validIn s = true) (h : evalTerm env t = some v) :
    v.validIn s = true := by
  cases t with
  | var i =>
    have h' : env[i]? = some v := h
    exact henv v (List.mem_of_getElem? h')
  | lit l => exact Lit.toVal_validIn s l v h
  | app atom args =>
    rw [evalTerm_app] at h
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h
    unfold nativeAtom at hv
    obtain ⟨named, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    exact NativeAtom.eval_validIn s named vs v (evalTerms_validIn s args env vs henv hvs) hv
termination_by structural t
theorem evalTerms_validIn (s : Stores) (ts : Terms) (env : List Val) (vs : List Val)
    (henv : ∀ x ∈ env, x.validIn s = true) (h : evalTerms env ts = some vs) :
    ∀ x ∈ vs, x.validIn s = true := by
  cases ts with
  | nil =>
    have h' : some ([] : List Val) = some vs := h
    cases h'
    exact fun _ hx => nomatch hx
  | cons head tail =>
    rw [evalTerms_cons] at h
    obtain ⟨v1, hv1, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
    cases hcons
    intro x hx
    cases hx with
    | head => exact evalTerm_validIn s head env _ henv hv1
    | tail _ hx' => exact evalTerms_validIn s tail env rest henv hrest x hx'
termination_by structural ts
end

/-! ## The invariant and the statement -/

/-- What a run keeps: the environment fits its types and is valid in the stores, the stores
are well-formed, and every cell holds a number. -/
structure TypedAt (tys : TyEnv) (env : List Val) (s : Stores) : Prop where
  fits : Fits env tys
  valid : ∀ v ∈ env, v.validIn s = true
  wf : s.WF
  heap : Stores.HeapNat s

/-- The invariant at a later store, under one more typed and valid binder. -/
theorem TypedAt.push {tys : TyEnv} {env : List Val} {s s' : Stores} (h : TypedAt tys env s)
    (hle : s.le s') (hwf : s'.WF) (hheap : Stores.HeapNat s') {v : Val} {ty : Ty}
    (hv : Val.hasTy v ty = true) (hvalid : v.validIn s' = true) :
    TypedAt (tys ++ [ty]) (env ++ [v]) s' where
  fits := h.fits.append hv
  valid := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Val.validIn_mono hle x (h.valid x hx)
    · cases List.mem_singleton.mp hx
      exact hvalid
  wf := hwf
  heap := hheap

/-- The invariant at a later store. -/
theorem TypedAt.later {tys : TyEnv} {env : List Val} {s s' : Stores} (h : TypedAt tys env s)
    (hle : s.le s') (hwf : s'.WF) (hheap : Stores.HeapNat s') : TypedAt tys env s' where
  fits := h.fits
  valid := fun x hx => Val.validIn_mono hle x (h.valid x hx)
  wf := hwf
  heap := hheap

/-- An exit has a program's type: a success is a valid value of the answer type, and every
typed failure of a cause is inside the error type. -/
def ExitOk (answer error : Ty) (s : Stores) : ExitV → Prop
  | .success v => Val.hasTy v answer = true ∧ v.validIn s = true
  | .failure c => causeAdmits (fun w ty => Val.hasTy w ty) error c = true

/-- Soundness of one run of a pair of programs, the first with the parameter and the second
without: they run alike, the exit has the type, and the store half of the invariant holds. -/
structure SoundP (pw pd : Effects.Program StoreSig ExitV) (s : Stores) (answer error : Ty) :
    Prop where
  independent : runP pw s = runP pd s
  exit : ExitOk answer error (runP pd s).2 (runP pd s).1
  le : s.le (runP pd s).2
  wf : (runP pd s).2.WF
  heap : Stores.HeapNat (runP pd s).2

/-- Soundness of a program's run: it does not depend on the wrong-shape exit, its exit has the
program's type, and the invariant's store half holds after it. -/
abbrev Sound (bad : ExitV) (e : NativeEff) (env : List Val) (s : Stores) (t : EffTy) : Prop :=
  SoundP (denoteWith bad e env) (denote e env) s t.answer t.error

/-- A pure exit on both sides is sound when the exit has the type. -/
theorem SoundP.pure {s : Stores} {answer error : Ty} (hwf : s.WF) (hheap : Stores.HeapNat s)
    (ex : ExitV) (hex : ExitOk answer error s ex) :
    SoundP (Pure.pure ex) (Pure.pure ex) s answer error :=
  ⟨rfl, hex, Stores.le_refl s, hwf, hheap⟩

/-- Cause admission moves along any pointwise implication of membership, across types. -/
theorem causeAdmits_of_forall {f g : Val → Ty → Bool} {ty ty' : Ty}
    (h : ∀ v, f v ty = true → g v ty' = true) (c : CauseV) :
    causeAdmits f ty c = true → causeAdmits g ty' c = true := by
  intro hc
  apply List.all_eq_true.mpr
  intro r hr
  have hr' := List.all_eq_true.mp hc r hr
  cases r with
  | fail e _ =>
    cases e with
    | boom => cases hr'
    | tag n => exact h _ hr'
    | tagged t m => exact h _ hr'
    | text t => exact h _ hr'
  | die _ _ => rfl
  | interrupt _ _ => rfl

theorem ExitOk.widen {a a' e e' : Ty} {s : Stores} {ex : ExitV}
    (ha : ∀ v, Val.hasTy v a = true → Val.hasTy v a' = true)
    (he : ∀ v, Val.hasTy v e = true → Val.hasTy v e' = true)
    (h : ExitOk a e s ex) : ExitOk a' e' s ex := by
  cases ex with
  | success v => exact ⟨ha v h.1, h.2⟩
  | failure c => exact causeAdmits_of_forall he c h

theorem ExitOk.later {a e : Ty} {s s' : Stores} {ex : ExitV} (hle : s.le s')
    (h : ExitOk a e s ex) : ExitOk a e s' ex := by
  cases ex with
  | success v => exact ⟨h.1, Val.validIn_mono hle v h.2⟩
  | failure c => exact h


theorem SoundP.widen {pw pd : Effects.Program StoreSig ExitV} {s : Stores} {a a' e e' : Ty}
    (ha : ∀ v, Val.hasTy v a = true → Val.hasTy v a' = true)
    (he : ∀ v, Val.hasTy v e = true → Val.hasTy v e' = true)
    (h : SoundP pw pd s a e) : SoundP pw pd s a' e' :=
  ⟨h.independent, h.exit.widen ha he, h.le, h.wf, h.heap⟩

/-- Sequencing: a sound first program, and a continuation sound from the state it reaches. -/
theorem SoundP.bind {pw pd : Effects.Program StoreSig ExitV} {s : Stores} {a e a' e' : Ty}
    (h : SoundP pw pd s a e) (kw kd : ExitV → Effects.Program StoreSig ExitV)
    (hk : SoundP (kw (runP pd s).1) (kd (runP pd s).1) (runP pd s).2 a' e') :
    SoundP (Effects.Program.bind pw kw) (Effects.Program.bind pd kd) s a' e' := by
  have hw : runP (Effects.Program.bind pw kw) s = runP (kw (runP pw s).1) (runP pw s).2 :=
    runP_bind pw kw s
  have hd : runP (Effects.Program.bind pd kd) s = runP (kd (runP pd s).1) (runP pd s).2 :=
    runP_bind pd kd s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hw, hd, h.independent, hk.independent]
  · rw [hd]; exact hk.exit
  · rw [hd]; exact Stores.le_trans h.le hk.le
  · rw [hd]; exact hk.wf
  · rw [hd]; exact hk.heap


theorem exitOk_fail {ty : Ty} {s : Stores} {x : Val} (hs : supportedErrTy ty = true)
    (hx : Val.hasTy x ty = true) (answer : Ty) :
    ExitOk answer ty s (Exit.failure (Cause.fail (errOf x))) := by
  show causeAdmits _ ty (Cause.fail (errOf x)) = true
  unfold causeAdmits Cause.fail
  rw [List.all_cons, List.all_nil, Bool.and_true]
  exact errAdmits_errOf ty x [] _ hs hx

/-- A reified exit has the exit type of its program, and is valid where the exit is. -/
theorem reify_ok {a e : Ty} {s : Stores} {ex : ExitV} (h : ExitOk a e s ex) :
    Val.hasTy (reifyExitVal ex) (.exitOf a e) = true ∧ (reifyExitVal ex).validIn s = true := by
  cases ex with
  | success v =>
    refine ⟨?_, ?_⟩
    · show Val.hasTy (Val.exitOk v) (.exitOf a e) = true
      simp only [Val.hasTy]
      exact h.1
    · show Val.validIn s (Val.exitOk v) = true
      rw [Val.validIn_exitOk]
      exact h.2
  | failure c =>
    refine ⟨?_, Val.validIn_exitErr s c⟩
    show Val.hasTy (Val.exitErr c) (.exitOf a e) = true
    rw [hasTy_exitErr]
    exact h


/-- What a decision binds is part of the scrutinee, so it is valid where the scrutinee is. -/
theorem Decision.decide_validIn (d : Decision) (s : Stores) {v x : Val} {first : Bool}
    (hv : Val.validIn s v = true) (h : d.decide v = some (first, some x)) :
    Val.validIn s x = true := by
  cases d with
  | bool => cases v <;> cases h
  | option =>
    cases v <;> cases h
    exact hv
  | tag t =>
    have h' : (match Val.tagPayload? t v with
        | some payload => some (true, some payload)
        | none => some (false, some v)) = some (first, some x) := h
    cases hp : Val.tagPayload? t v with
    | none =>
      rw [hp] at h'
      cases h'
      exact hv
    | some payload =>
      rw [hp] at h'
      cases h'
      unfold Val.tagPayload? at hp
      split at hp
      · next t' payload' =>
        split at hp
        · cases hp
          exact validIn_list_mem hv _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        · cases hp
      · cases hp

/-- The invariant under what a decision binds. -/
theorem TypedAt.bound {tys : TyEnv} {env : List Val} {s : Stores} (h : TypedAt tys env s)
    {bound : Option Val} {arm : List Ty} (hb : Decision.BoundTyped [] bound arm)
    (hvalid : ∀ x, bound = some x → Val.validIn s x = true) :
    TypedAt (tys ++ arm) (env ++ bound.toList) s := by
  cases bound with
  | none =>
    cases arm with
    | nil =>
      rw [List.append_nil]
      show TypedAt tys (env ++ []) s
      rw [List.append_nil]
      exact h
    | cons _ _ => exact hb.elim
  | some x =>
    cases arm with
    | nil => exact hb.elim
    | cons ty rest =>
      cases rest with
      | nil => exact h.push (Stores.le_refl s) h.wf h.heap hb (hvalid x rfl)
      | cons _ _ => exact hb.elim

theorem causeAdmits_combine {f : Val → Ty → Bool} {ty : Ty} {c d : CauseV}
    (hc : causeAdmits f ty c = true) (hd : causeAdmits f ty d = true) :
    causeAdmits f ty (Cause.combine c d) = true := by
  unfold Cause.combine
  split
  · exact hd
  · split
    · exact hc
    · apply List.all_eq_true.mpr
      intro r hr
      rcases List.mem_append.mp ((Cause.mem_dedup r _).mp hr) with hm | hm
      · exact List.all_eq_true.mp hc r hm
      · exact List.all_eq_true.mp hd r hm

/-- The exit a finalizer leaves: the body's exit, or the finalizer's failure, or both. -/
theorem restore_ok {a e ef af : Ty} {s : Stores} {ex fex : ExitV}
    (hex : ExitOk a e s ex) (hfex : ExitOk af ef s fex) :
    ExitOk a (e.join ef) s (Exit.restoreAfterFinalizer ex (finVoid fex)) := by
  cases ex with
  | success v =>
    cases fex with
    | success w => exact ⟨hex.1, hex.2⟩
    | failure cf =>
      exact causeAdmits_of_forall (fun w h => Ty.hasTy_join_right e ef w [] h) cf hfex
  | failure c =>
    have hc : causeAdmits (fun w ty => Val.hasTy w ty) (e.join ef) c = true :=
      causeAdmits_of_forall (fun w h => Ty.hasTy_join_left e ef w [] h) c hex
    cases fex with
    | success w => exact hc
    | failure cf =>
      exact causeAdmits_combine hc
        (causeAdmits_of_forall (fun w h => Ty.hasTy_join_right e ef w [] h) cf hfex)

/-- The main theorem: a typed program of the straight fragment is sound from every state
the invariant holds in. -/
theorem sound (bad : ExitV) : ∀ (e : NativeEff) (tys : TyEnv) (env : List Val) (s : Stores)
    (t : EffTy), Straight e = true → effTy nativeSignature tys e = some t →
    TypedAt tys env s → Sound bad e env s t
  | .succeed v, tys, env, s, t, _, hty, hat => by
    obtain ⟨ty, hv, rfl⟩ := inv_succeed nativeSignature tys v t hty
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (evalTerm_isSome v env tys ty hat.fits hv)
    show SoundP _ _ s _ _
    rw [denoteWith, denote, hx]
    exact SoundP.pure hat.wf hat.heap _
      ⟨evalTerm_hasTy v env tys ty x hat.fits hv hx, evalTerm_validIn s v env x hat.valid hx⟩
  | .sync v, tys, env, s, t, _, hty, hat => by
    obtain ⟨ty, hv, rfl⟩ := inv_sync nativeSignature tys v t hty
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (evalTerm_isSome v env tys ty hat.fits hv)
    show SoundP _ _ s _ _
    rw [denoteWith, denote, hx]
    exact SoundP.pure hat.wf hat.heap _
      ⟨evalTerm_hasTy v env tys ty x hat.fits hv hx, evalTerm_validIn s v env x hat.valid hx⟩
  | .suspend b, tys, env, s, t, hs, hty, hat => by
    show SoundP _ _ s _ _
    rw [denoteWith, denote]
    exact sound bad b tys env s t (Straight.suspend hs)
      (inv_suspend nativeSignature tys b t hty) hat
  | .bind a b, tys, env, s, t, hs, hty, hat => by
    obtain ⟨ha, hb⟩ := Straight.bind hs
    obtain ⟨f, r, hf, hr, rfl⟩ := inv_bind nativeSignature tys a b t hty
    have iha := sound bad a tys env s f ha hf hat
    show SoundP _ _ s _ _
    rw [denoteWith, denote]
    refine SoundP.bind iha _ _ ?_
    have hex := iha.exit
    cases hrun : (runP (denote a env) s).1 with
    | success v =>
      rw [hrun] at hex
      have hat' := hat.push iha.le iha.wf iha.heap hex.1 hex.2
      exact (sound bad b (tys ++ [f.answer]) (env ++ [v]) _ r hb hr hat').widen
        (fun _ h => h) (fun w h => Ty.hasTy_join_right f.error r.error w [] h)
    | failure c =>
      rw [hrun] at hex
      exact SoundP.pure iha.wf iha.heap _
        (causeAdmits_of_forall (fun w h => Ty.hasTy_join_left f.error r.error w [] h) c hex)
  | .fail v, tys, env, s, t, _, hty, hat => by
    obtain ⟨ty, hv, hadm, rfl⟩ := inv_fail nativeSignature tys v t hty
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (evalTerm_isSome v env tys ty hat.fits hv)
    show SoundP _ _ s _ _
    rw [denoteWith, denote, hx]
    exact SoundP.pure hat.wf hat.heap _
      (exitOk_fail hadm (evalTerm_hasTy v env tys ty x hat.fits hv hx) _)
  | .failCause c, tys, env, s, t, _, hty, hat => by
    obtain ⟨ty, hc, rfl⟩ := inv_failCause nativeSignature tys c t hty
    obtain ⟨cause, hcause⟩ :=
      Option.isSome_iff_exists.mp (causeOf_isSome_of_causeTy tys env hat.fits c ty hc)
    show SoundP _ _ s _ _
    rw [denoteWith, denote, hcause]
    exact SoundP.pure hat.wf hat.heap _ (causeOf_admits tys env hat.fits c ty hc cause hcause)
  | .exit b, tys, env, s, t, hs, hty, hat => by
    obtain ⟨tb, htb, rfl⟩ := inv_exit nativeSignature tys b t hty
    have ih := sound bad b tys env s tb (Straight.exit hs) htb hat
    show SoundP _ _ s _ _
    rw [denoteWith, denote]
    refine SoundP.bind ih _ _ ?_
    exact SoundP.pure ih.wf ih.heap _ (reify_ok ih.exit)
  | .catchCause b h, tys, env, s, t, hs, hty, hat => by
    obtain ⟨hsb, hsh⟩ := Straight.catchCause hs
    obtain ⟨tb, th, answer, htb, hth, hans, rfl⟩ := inv_catchCause nativeSignature tys b h t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := sound bad b tys env s tb hsb htb hat
    show SoundP _ _ s _ _
    rw [denoteWith, denote]
    refine SoundP.bind ih _ _ ?_
    have hex := ih.exit
    cases hrun : (runP (denote b env) s).1 with
    | success v =>
      rw [hrun] at hex
      exact SoundP.pure ih.wf ih.heap _
        ⟨Ty.hasTy_join_left tb.answer th.answer v [] hex.1, hex.2⟩
    | failure c =>
      rw [hrun] at hex
      have hc : Val.hasTy (Val.exitErr c) (.causeOf tb.error) = true := by
        rw [hasTy_causeOf_exitErr]; exact hex
      have hat' := hat.push ih.le ih.wf ih.heap hc (Val.validIn_exitErr _ c)
      exact (sound bad h (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr c]) _ th hsh hth
        hat').widen (fun w hw => Ty.hasTy_join_right tb.answer th.answer w [] hw) (fun _ hw => hw)
  | .matchCause b v c, tys, env, s, t, hs, hty, hat => by
    obtain ⟨hsb, hsv, hsc⟩ := Straight.matchCause hs
    obtain ⟨tb, tv, tc, answer, htb, htv, htc, hans, rfl⟩ :=
      inv_matchCause nativeSignature tys b v c t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := sound bad b tys env s tb hsb htb hat
    show SoundP _ _ s _ _
    rw [denoteWith, denote]
    refine SoundP.bind ih _ _ ?_
    have hex := ih.exit
    cases hrun : (runP (denote b env) s).1 with
    | success x =>
      rw [hrun] at hex
      have hat' := hat.push ih.le ih.wf ih.heap hex.1 hex.2
      exact (sound bad v (tys ++ [tb.answer]) (env ++ [x]) _ tv hsv htv hat').widen
        (fun w hw => Ty.hasTy_join_left tv.answer tc.answer w [] hw)
        (fun w hw => Ty.hasTy_join_left tv.error tc.error w [] hw)
    | failure cause =>
      rw [hrun] at hex
      have hc : Val.hasTy (Val.exitErr cause) (.causeOf tb.error) = true := by
        rw [hasTy_causeOf_exitErr]; exact hex
      have hat' := hat.push ih.le ih.wf ih.heap hc (Val.validIn_exitErr _ cause)
      exact (sound bad c (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr cause]) _ tc hsc htc
        hat').widen (fun w hw => Ty.hasTy_join_right tv.answer tc.answer w [] hw)
        (fun w hw => Ty.hasTy_join_right tv.error tc.error w [] hw)
  | .select test d a b, tys, env, s, t, hs, hty, hat => by
    obtain ⟨ha, hb⟩ := Straight.select hs
    obtain ⟨ty, e0, e1, t0, t1, answer, htest, harms, ht0, ht1, hans, rfl⟩ :=
      inv_select nativeSignature tys test d a b t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    obtain ⟨x, hx⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome test env tys ty hat.fits htest)
    have hxty := evalTerm_hasTy test env tys ty x hat.fits htest hx
    have hxv := evalTerm_validIn s test env x hat.valid hx
    obtain ⟨first, bound, hdec, hbound⟩ := Decision.decide_typed d harms hxty
    have hvalid : ∀ y, bound = some y → Val.validIn s y = true := by
      intro y hy
      subst hy
      exact Decision.decide_validIn d s hxv hdec
    show SoundP _ _ s _ _
    rw [denoteWith, denote, hx]
    show SoundP (match (some x).bind d.decide with
        | some (true, bound) => denoteWith bad a (env ++ bound.toList)
        | some (false, bound) => denoteWith bad b (env ++ bound.toList)
        | none => pure bad)
      (match (some x).bind d.decide with
        | some (true, bound) => denote a (env ++ bound.toList)
        | some (false, bound) => denote b (env ++ bound.toList)
        | none => pure badShapeExit) s _ _
    rw [Option.bind_some, hdec]
    cases first with
    | true =>
      exact (sound bad a (tys ++ e0) (env ++ bound.toList) s t0 ha ht0
        (hat.bound hbound hvalid)).widen
        (fun w h => Ty.hasTy_join_left t0.answer t1.answer w [] h)
        (fun w h => Ty.hasTy_join_left t0.error t1.error w [] h)
    | false =>
      exact (sound bad b (tys ++ e1) (env ++ bound.toList) s t1 hb ht1
        (hat.bound hbound hvalid)).widen
        (fun w h => Ty.hasTy_join_right t0.answer t1.answer w [] h)
        (fun w h => Ty.hasTy_join_right t0.error t1.error w [] h)
  | .onExit b f, tys, env, s, t, hs, hty, hat => by
    obtain ⟨hsb, hsf⟩ := Straight.onExit hs
    obtain ⟨tb, tf, htb, htf, rfl⟩ := inv_onExit nativeSignature tys b f t hty
    have ih := sound bad b tys env s tb hsb htb hat
    show SoundP _ _ s _ _
    rw [denoteWith, denote]
    refine SoundP.bind ih _ _ ?_
    have hre := reify_ok ih.exit
    have hat' := hat.push ih.le ih.wf ih.heap hre.1 hre.2
    have ihf := sound bad f (tys ++ [.exitOf tb.answer tb.error])
      (env ++ [reifyExitVal (runP (denote b env) s).1]) _ tf hsf htf hat'
    refine SoundP.bind ihf _ _ ?_
    exact SoundP.pure ihf.wf ihf.heap _ (restore_ok (ih.exit.later ihf.le) ihf.exit)
  | .perform op r, tys, env, s, t, hs, hty, hat => by
    have hkind := Straight.perform_sync hs
    obtain ⟨requestTy, _, hr, hrow⟩ := inv_perform nativeSignature tys op r t hty
    obtain ⟨hcreq, hcans, hcerr⟩ := nativeSignature_row_closed op
    obtain ⟨hsub, rfl⟩ := rowTy_closed_some hcreq hcans hcerr hrow
    obtain ⟨x, hx⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome r env tys requestTy hat.fits hr)
    have hxty := evalTerm_hasTy r env tys requestTy x hat.fits hr hx
    have hxv := evalTerm_validIn s r env x hat.valid hx
    have hreq : Val.hasTy x (NativeOp.row op).request = true := by
      have h1 : Val.hasTy x requestTy.normalize = true := by
        rw [Effect4.Program.hasTy_normalize]; exact hxty
      have h2 := hasTy_sub _ _ x [] hsub h1
      have hrow : (nativeSignature.rowOf op).request = (NativeOp.row op).request.normalize := by
        show ((nativeRowOf [] op).normalizeTypes).request = _
        rw [nativeRowOf_nil]; rfl
      rw [hrow, Ty.normalize_idem, Effect4.Program.hasTy_normalize] at h2
      exact h2
    obtain ⟨o, s', a, ho, hstep, haty, hav, hwf', hheap'⟩ :=
      progress op x s hat.wf hat.heap hkind hreq hxv
    have hrun : runP (denote (.perform op r) env) s = (Exit.success a, s') := by
      have := meaning_perform_sync op r env s hkind hx ho
      rw [hstep] at this
      exact this
    have hrunW : runP (denoteWith bad (.perform op r) env) s = (Exit.success a, s') := by
      rw [← hrun]
      congr 1
      rw [denoteWith, denote]
      simp only [hkind, hx, Option.bind_some, ho]
    have hans : Val.hasTy a (nativeSignature.rowOf op).answer.normalize = true := by
      rw [Effect4.Program.hasTy_normalize]
      show Val.hasTy a ((nativeRowOf [] op).normalizeTypes).answer = true
      rw [nativeRowOf_nil]
      show Val.hasTy a (NativeOp.row op).answer.normalize = true
      rw [Effect4.Program.hasTy_normalize]; exact haty
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hrunW, hrun]
    · rw [hrun]; exact ⟨hans, hav⟩
    · rw [hrun]; exact syncOpStep_le o s s' a hstep
    · rw [hrun]; exact hwf'
    · rw [hrun]; exact hheap'
  -- the non-straight constructors, last: `Straight` answers `false` at each, so the arm is
  -- unreachable. A wildcard would not do — the contradiction is `Straight` REDUCING on the
  -- constructor, and at an opaque `e` there is nothing to reduce
  | .gen _, _, _, _, _, hs, _, _ | .uninterruptible _, _, _, _, _, hs, _, _
  | .interruptible _, _, _, _, _, hs, _, _
  | .iterate _ _ _ _ _ _, _, _, _, _, hs, _, _ | .yieldNow _, _, _, _, _, hs, _, _
  | .awaitFiber _ _, _, _, _, _, hs, _, _
  | .withFiber _, _, _, _, _, hs, _, _ | .scoped _, _, _, _, _, hs, _, _
  | .acquireRelease _ _, _, _, _, _, hs, _, _ | .provideLayer _ _ _, _, _, _, _, hs, _, _
  | .service _, _, _, _, _, hs, _, _ | .provideService _ _ _, _, _, _, _, hs, _, _
  | .catchIf _ _ _, _, _, _, _, hs, _, _ => absurd hs Bool.false_ne_true

/-! ## The corollaries -/

/-- The invariant holds of the empty environment in the empty stores. -/
theorem TypedAt.empty : TypedAt [] [] Stores.empty :=
  ⟨Fits.nil, (fun _ h => nomatch h), Stores.empty_wf, Stores.empty_heapNat⟩

/-- **A typed straight program's meaning has its type.** From the empty stores, the exit is a
valid value of the answer type or a cause inside the error type. -/
theorem meaning_typed (e : NativeEff) (t : EffTy) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t) :
    ExitOk t.answer t.error (meaning e [] Stores.empty).2 (meaning e [] Stores.empty).1 :=
  (sound badShapeExit e [] [] Stores.empty t hs hty TypedAt.empty).exit

/-- **A typed straight program does not go wrong.** Whatever exit the wrong-shape arms are
given, the run is the meaning: no such arm is reached. -/
theorem meaning_never_wrong (bad : ExitV) (e : NativeEff) (t : EffTy) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t) :
    runP (denoteWith bad e []) Stores.empty = meaning e [] Stores.empty :=
  (sound bad e [] [] Stores.empty t hs hty TypedAt.empty).independent

/-- The stores a typed straight program leaves are well-formed, with a number in every cell. -/
theorem meaning_stores (e : NativeEff) (t : EffTy) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t) :
    (meaning e [] Stores.empty).2.WF ∧ Stores.HeapNat (meaning e [] Stores.empty).2 :=
  ⟨(sound badShapeExit e [] [] Stores.empty t hs hty TypedAt.empty).wf,
    (sound badShapeExit e [] [] Stores.empty t hs hty TypedAt.empty).heap⟩

open Effect4.Program.Agreement in
/-- **The machine, on the straight fragment.** The ordinary run of a typed straight program,
at `run_eq_meaning`'s budget, finishes with an exit of the program's type. -/
theorem run_typed (e : NativeEff) (t : EffTy) (fuel : Nat) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      ∃ ex, (Api.run e fuel).exit = some ex ∧
        ExitOk t.answer t.error (Api.run e fuel).stores ex := by
  obtain ⟨hout, hexit, hstores⟩ := run_eq_meaning e fuel hs hd hfuel
  refine ⟨hout, _, hexit, ?_⟩
  rw [hstores]
  exact meaning_typed e t hs hty


end Effect4.Program.Denote
