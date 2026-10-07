import Effect4.Codegen.Forms
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Typing.Sound

/-!
# Shared-form typing transport

`Forms.insert` uses the existing weakening operation. Its typing law covers any
number of inserted slots, arbitrary captured and local variables, and refusals as
well as successful typings. Weakening maps an operation's own term too, so every law that
inserts a slot holds at a signature that types an operation alike once its term is weakened
(`Signature.WeakenNatural`, `Program/Typing.lean`). The template constructor laws state the environments
of their arguments explicitly; an `ArgClass` alone is not a typing premise.

The concrete laws select the existing `Forms.all` rows by id and type their actual
expansions. They introduce no second template table or checker. Continuations may
use the first answer; effect/thunk arguments retain their original environment.
These are laws of the core checker, not host execution or parser correctness.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Forms

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)

/-- Repeated insertion can expose its final weakening at the same cut. -/
theorem insert_succ (cut count : Nat) (program : Eff NativeOp) :
    insert cut (count + 1) program = Eff.weaken cut (insert cut count program) := by
  induction count generalizing program with
  | zero => rfl
  | succ count ih => simpa only [insert] using ih (Eff.weaken cut program)

/-- Insert any finite block of unused slots without changing the complete typing
result. `pre` contains the captured variables before the cut; `post` contains those
after it. The program's own binders are traversed by `Eff.weaken`, an operation's own term
included, so the signature must type an operation alike once its term is weakened
(`Signature.WeakenNatural`). -/
theorem effTy_insert (sig : Signature NativeOp) (hw : sig.WeakenNatural) (pre inserted post : TyEnv)
    (program : Eff NativeOp) :
    effTy sig (pre ++ inserted ++ post) (insert pre.length inserted.length program) =
      effTy sig (pre ++ post) program := by
  induction inserted with
  | nil => simp only [List.append_nil, List.length_nil, insert]
  | cons ty inserted ih =>
      rw [List.append_assoc]
      change effTy sig (pre ++ ty :: (inserted ++ post))
        (insert pre.length (inserted.length + 1) program) = _
      rw [insert_succ, effTy_weaken sig hw]
      simpa only [List.append_assoc] using ih

/-- The common form case: append unused slots after every captured variable. -/
theorem effTy_insert_append (sig : Signature NativeOp) (hw : sig.WeakenNatural)
    (env inserted : TyEnv) (program : Eff NativeOp) :
    effTy sig (env ++ inserted) (insert env.length inserted.length program) =
      effTy sig env program := by
  simpa only [List.append_nil] using effTy_insert sig hw env inserted [] program

/-- An effect slot transports its complete typing result when its recorded cut
and count describe this environment insertion. Slot existence is explicit. -/
theorem Template.argument_typed (sig : Signature NativeOp) (hw : sig.WeakenNatural)
    (n slot offset count : Nat)
    (args : Arguments) (program : Eff NativeOp) (pre inserted post : TyEnv)
    (hslot : args.effects[slot]? = some program)
    (hcut : n + offset = pre.length) (hcount : count = inserted.length) :
    ((Template.argument slot offset count).expand n args).bind
        (effTy sig (pre ++ inserted ++ post)) = effTy sig (pre ++ post) program := by
  simp only [Template.expand, hslot, Option.map_some, Option.bind_some, hcut, hcount]
  exact effTy_insert sig hw pre inserted post program

/-- A bind template uses its continuation under the first argument's answer type.
Both expansion and typing premises are explicit for each template argument. -/
theorem Template.bind_typed (sig : Signature NativeOp) (env : TyEnv) (n : Nat)
    (args : Arguments) (first rest : Template) (p q : Eff NativeOp) (a b : EffTy)
    (hp : first.expand n args = some p) (hq : rest.expand n args = some q)
    (ha : effTy sig env p = some a)
    (hb : effTy sig (env ++ [a.answer]) q = some b) :
    ((Template.bind first rest).expand n args).bind (effTy sig env) =
      some ⟨b.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  simp only [Template.expand, hp, hq, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Conform.Effect4.Typing.effTy_bind, ha, hb]

/-- An exit template gives its finalizer an exit value, not the body's answer.
The finalizer's answer is discarded; its errors and requirements remain. -/
theorem Template.onExit_typed (sig : Signature NativeOp) (env : TyEnv) (n : Nat)
    (args : Arguments) (body finalizer : Template) (p q : Eff NativeOp) (a b : EffTy)
    (hp : body.expand n args = some p) (hq : finalizer.expand n args = some q)
    (ha : effTy sig env p = some a)
    (hb : effTy sig (env ++ [.exitOf a.answer a.error]) q = some b) :
    ((Template.onExit body finalizer).expand n args).bind (effTy sig env) =
      some ⟨a.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  simp only [Template.expand, hp, hq, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Conform.Effect4.Typing.effTy_onExit, ha, hb]

/-- The table's effect-valued `andThen` inserts an unused answer slot into its
second argument. Captures in either argument may refer to any position in `env`. -/
theorem andThenEffect_typed (sig : Signature NativeOp) (hw : sig.WeakenNatural) (env : TyEnv)
    (first second : Eff NativeOp) (a b : EffTy)
    (ha : effTy sig env first = some a) (hb : effTy sig env second = some b) :
    ((all.find? (fun f => f.id == "andThenEffect")).bind
      (fun f => f.expansion.expand env.length { effects := [first, second] })).bind
        (effTy sig env) =
      some ⟨b.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  change effTy sig env (.bind first (insert env.length 1 second)) = _
  have hb' : effTy sig (env ++ [a.answer]) (insert env.length 1 second) = some b :=
    (effTy_insert_append sig hw env [a.answer] second).trans hb
  simp only [Conform.Effect4.Typing.effTy_bind, ha, hb', Option.bind_eq_bind, Option.bind_some]

/-- A continuation-valued `andThen` is already authored under its answer binder;
its argument must not receive the unused-slot insertion of the effect form. -/
theorem andThenContinuation_typed (sig : Signature NativeOp) (env : TyEnv)
    (first continuation : Eff NativeOp) (a b : EffTy)
    (ha : effTy sig env first = some a)
    (hb : effTy sig (env ++ [a.answer]) continuation = some b) :
    ((all.find? (fun f => f.id == "andThenContinuation")).bind
      (fun f => f.expansion.expand env.length { effects := [first, continuation] })).bind
        (effTy sig env) =
      some ⟨b.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  change effTy sig env (.bind first continuation) = _
  simp only [Conform.Effect4.Typing.effTy_bind, ha, hb, Option.bind_eq_bind, Option.bind_some]

/-- The thunk row shares the effect row's core typing rule. This does not claim
that an arbitrary host thunk is an admitted source expression. -/
theorem andThenThunk_typed (sig : Signature NativeOp) (hw : sig.WeakenNatural) (env : TyEnv)
    (first second : Eff NativeOp) (a b : EffTy)
    (ha : effTy sig env first = some a) (hb : effTy sig env second = some b) :
    ((all.find? (fun f => f.id == "andThenThunk")).bind
      (fun f => f.expansion.expand env.length { effects := [first, second] })).bind
        (effTy sig env) =
      some ⟨b.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  exact andThenEffect_typed sig hw env first second a b ha hb

private theorem bind_keep_typed (sig : Signature NativeOp) (env : TyEnv)
    (first continuation : Eff NativeOp) (a b : EffTy)
    (ha : effTy sig env first = some a)
    (hb : effTy sig (env ++ [a.answer]) continuation = some b) :
    effTy sig env (.bind first (.bind continuation (.succeed (.var env.length)))) =
      some ⟨a.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  have hv : termTy sig ((env ++ [a.answer]) ++ [b.answer]) (.var env.length) =
      some a.answer := by
    rw [List.append_assoc]
    change (env ++ [a.answer, b.answer])[env.length]? = some a.answer
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  simp only [Conform.Effect4.Typing.effTy_bind, Conform.Effect4.Typing.effTy_succeed, ha, hb, hv,
    Option.bind_eq_bind, Option.bind_some, Option.map_some, EffTy.pure]
  rw [← Ty.join_assoc, Ty.join_never_right, Ty.normalize_join]
  simp only [Requirement.empty, Requirement.union, Row.union_empty_right]

/-- The table's continuation-valued `tap` retains the first answer even beneath
the continuation's own answer binder. Both error and requirement columns join. -/
theorem tapContinuation_typed (sig : Signature NativeOp) (env : TyEnv)
    (first continuation : Eff NativeOp) (a b : EffTy)
    (ha : effTy sig env first = some a)
    (hb : effTy sig (env ++ [a.answer]) continuation = some b) :
    ((all.find? (fun f => f.id == "tapContinuation")).bind
      (fun f => f.expansion.expand env.length { effects := [first, continuation] })).bind
        (effTy sig env) =
      some ⟨a.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  change effTy sig env (.bind first (.bind continuation (.succeed (.var env.length)))) = _
  exact bind_keep_typed sig env first continuation a b ha hb

/-- An effect-valued `tap` first shifts its captured effect beneath the unused
answer slot, then retains the first answer beneath both new binders. -/
theorem tapEffect_typed (sig : Signature NativeOp) (hw : sig.WeakenNatural) (env : TyEnv)
    (first second : Eff NativeOp) (a b : EffTy)
    (ha : effTy sig env first = some a) (hb : effTy sig env second = some b) :
    ((all.find? (fun f => f.id == "tapEffect")).bind
      (fun f => f.expansion.expand env.length { effects := [first, second] })).bind
        (effTy sig env) =
      some ⟨a.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  change effTy sig env
    (.bind first (.bind (insert env.length 1 second) (.succeed (.var env.length)))) = _
  exact bind_keep_typed sig env first (insert env.length 1 second) a b ha
    ((effTy_insert_append sig hw env [a.answer] second).trans hb)

/-- The literal admitted by `as` supplies the answer. Sequencing with its pure
result normalizes the original error column, as the core bind rule requires. -/
theorem as_typed (sig : Signature NativeOp) (env : TyEnv)
    (body : Eff NativeOp) (value : Lit) (a : EffTy)
    (ha : effTy sig env body = some a) :
    ((all.find? (fun f => f.id == "as")).bind
      (fun f => f.expansion.expand env.length
        { effects := [body], terms := [.lit value] })).bind (effTy sig env) =
      some ⟨value.ty, a.error.normalize, a.requires⟩ := by
  change effTy sig env (.bind body (.succeed (.lit value))) = _
  simp only [Conform.Effect4.Typing.effTy_bind, Conform.Effect4.Typing.effTy_succeed, ha, termTy,
    argTy, litArgTy_false, Option.bind_eq_bind, Option.bind_some, Option.map_some, EffTy.pure,
    Ty.join_never_right, Requirement.empty, Requirement.union, Row.union_empty_right]

/-- The table's `asVoid` is the unit instance of the same core expansion. -/
theorem asVoid_typed (sig : Signature NativeOp) (env : TyEnv)
    (body : Eff NativeOp) (a : EffTy) (ha : effTy sig env body = some a) :
    ((all.find? (fun f => f.id == "asVoid")).bind
      (fun f => f.expansion.expand env.length { effects := [body] })).bind
        (effTy sig env) = some ⟨.unit, a.error.normalize, a.requires⟩ := by
  exact as_typed sig env body .unit a ha

/-- `ensuring` shifts its captured finalizer under an unused exit slot. Its
answer is discarded; its errors and service requirements are still retained. -/
theorem ensuring_typed (sig : Signature NativeOp) (hw : sig.WeakenNatural) (env : TyEnv)
    (body finalizer : Eff NativeOp) (a b : EffTy)
    (ha : effTy sig env body = some a) (hb : effTy sig env finalizer = some b) :
    ((all.find? (fun f => f.id == "ensuring")).bind
      (fun f => f.expansion.expand env.length { effects := [body, finalizer] })).bind
        (effTy sig env) =
      some ⟨a.answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  change effTy sig env (.onExit body (insert env.length 1 finalizer)) = _
  have hb' : effTy sig (env ++ [.exitOf a.answer a.error])
      (insert env.length 1 finalizer) = some b :=
    (effTy_insert_append sig hw env [.exitOf a.answer a.error] finalizer).trans hb
  simp only [Conform.Effect4.Typing.effTy_onExit, ha, hb', Option.bind_eq_bind, Option.bind_some]

/-! ## The remaining eleven rows (R10: each form owes a typing lemma)

Each law types the row's actual expansion through the checker's declarative rule: the
argument typings become derivations (`effTy_sound`), the row's rule assembles them, and
`effTy_complete` returns to the checker. -/

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.void` answers `unit`. -/
theorem void_typed (sig : Signature NativeOp) (env : TyEnv) :
    ((all.find? (fun f => f.id == "void")).bind
      (fun f => f.expansion.expand env.length {})).bind (effTy sig env) =
      some (EffTy.pure .unit) := by
  change effTy sig env (.succeed (.lit .unit)) = _
  exact effTy_complete sig _ env _ (.succeed rfl)

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.die` fails with its defect's cause and answers `never`. -/
theorem die_typed (sig : Signature NativeOp) (env : TyEnv) (value : Term) (ty : Ty)
    (hc : causeTy sig env (.die value) = some ty) :
    ((all.find? (fun f => f.id == "die")).bind
      (fun f => f.expansion.expand env.length { terms := [value] })).bind (effTy sig env) =
      some ⟨.never, ty, Requirement.empty⟩ := by
  change effTy sig env (.failCause (.die value)) = _
  exact effTy_complete sig _ env _ (.failCause hc)

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `yield* Key` answers the key's carrier and requires the key. -/
theorem yieldKey_typed (sig : Signature NativeOp) (env : TyEnv) (key : ServiceKey) (ty : Ty)
    (hk : sig.serviceTy key = some ty) :
    ((all.find? (fun f => f.id == "yieldKey")).bind
      (fun f => f.expansion.expand env.length { keys := [key] })).bind (effTy sig env) =
      some ⟨ty, .never, Requirement.single key⟩ := by
  change effTy sig env (.service key) = _
  exact effTy_complete sig _ env _ (.service hk)

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.matchCause` with term arms: each arm is a value under its binder, and the answers
join. -/
theorem matchCause_typed (sig : Signature NativeOp) (env : TyEnv) (body : Eff NativeOp)
    (onValue onCause : Term) (b : EffTy) (v c answer : Ty)
    (hb : effTy sig env body = some b)
    (hv : termTy sig (env ++ [b.answer]) onValue = some v)
    (hc : termTy sig (env ++ [.causeOf b.error]) onCause = some c)
    (hj : EffTy.joinAnswer (EffTy.pure v).answer (EffTy.pure c).answer = some answer) :
    ((all.find? (fun f => f.id == "matchCause")).bind
      (fun f => f.expansion.expand env.length
        { effects := [body], terms := [onValue, onCause] })).bind (effTy sig env) =
      some ⟨answer, (EffTy.pure v).error.join (EffTy.pure c).error,
        (b.requires.union (EffTy.pure v).requires).union (EffTy.pure c).requires⟩ := by
  change effTy sig env (.matchCause body (.succeed onValue) (.succeed onCause)) = _
  exact effTy_complete sig _ env _
    (.matchCause (effTy_sound sig body env b hb) (.succeed hv) (.succeed hc) hj)

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.matchCauseEffect`: the handlers are programs under their binders. -/
theorem matchCauseEffect_typed (sig : Signature NativeOp) (env : TyEnv)
    (body onValue onCause : Eff NativeOp) (b v c : EffTy) (answer : Ty)
    (hb : effTy sig env body = some b)
    (hv : effTy sig (env ++ [b.answer]) onValue = some v)
    (hc : effTy sig (env ++ [.causeOf b.error]) onCause = some c)
    (hj : EffTy.joinAnswer v.answer c.answer = some answer) :
    ((all.find? (fun f => f.id == "matchCauseEffect")).bind
      (fun f => f.expansion.expand env.length { effects := [body, onValue, onCause] })).bind
        (effTy sig env) =
      some ⟨answer, v.error.join c.error, (b.requires.union v.requires).union c.requires⟩ := by
  change effTy sig env (.matchCause body onValue onCause) = _
  exact effTy_complete sig _ env _ (.matchCause (effTy_sound sig body env b hb)
    (effTy_sound sig onValue _ v hv) (effTy_sound sig onCause _ c hc) hj)

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.yieldNow` answers `unit`. -/
theorem yieldNow_typed (sig : Signature NativeOp) (env : TyEnv) :
    ((all.find? (fun f => f.id == "yieldNow")).bind
      (fun f => f.expansion.expand env.length {})).bind (effTy sig env) =
      some (EffTy.pure .unit) := by
  change effTy sig env (.yieldNow 0) = _
  exact effTy_complete sig _ env _ (.yieldNow 0)

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.forkChild` with the default options answers the child's fiber handle. -/
theorem forkChildDefault_typed (sig : Signature NativeOp) (env : TyEnv) (body : Eff NativeOp)
    (p : EffTy) (hp : effTy sig env body = some p) :
    ((all.find? (fun f => f.id == "forkChildDefault")).bind
      (fun f => f.expansion.expand env.length { effects := [body] })).bind (effTy sig env) =
      some ⟨.fiberOf p.answer p.error, .never, p.requires⟩ := by
  change effTy sig env (.withFiber (.fork body (defaults false))) = _
  exact effTy_complete sig _ env _ (.withFiber (.fork _ (effTy_sound sig body env p hp)))

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.forkDetach` with the default options answers the child's fiber handle. -/
theorem forkDetachDefault_typed (sig : Signature NativeOp) (env : TyEnv) (body : Eff NativeOp)
    (p : EffTy) (hp : effTy sig env body = some p) :
    ((all.find? (fun f => f.id == "forkDetachDefault")).bind
      (fun f => f.expansion.expand env.length { effects := [body] })).bind (effTy sig env) =
      some ⟨.fiberOf p.answer p.error, .never, p.requires⟩ := by
  change effTy sig env (.withFiber (.fork body (defaults true))) = _
  exact effTy_complete sig _ env _ (.withFiber (.fork _ (effTy_sound sig body env p hp)))

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.forkIn` with the default options: the target is a scope handle. -/
theorem forkInDefault_typed (sig : Signature NativeOp) (env : TyEnv) (body : Eff NativeOp)
    (scope : Term) (p : EffTy) (hp : effTy sig env body = some p)
    (hs : termTy sig env scope = some Ty.scope) :
    ((all.find? (fun f => f.id == "forkInDefault")).bind
      (fun f => f.expansion.expand env.length { effects := [body], terms := [scope] })).bind
        (effTy sig env) =
      some ⟨.fiberOf p.answer p.error, .never, p.requires⟩ := by
  change effTy sig env (.withFiber (.forkIn body (defaults true) scope)) = _
  exact effTy_complete sig _ env _ (.withFiber (.forkIn (defaults true) (effTy_sound sig body env p hp) hs (Ty.sub_refl _)))

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.forkScoped` with the default options requires the ambient scope. -/
theorem forkScopedDefault_typed (sig : Signature NativeOp) (env : TyEnv) (body : Eff NativeOp)
    (p : EffTy) (hp : effTy sig env body = some p) :
    ((all.find? (fun f => f.id == "forkScopedDefault")).bind
      (fun f => f.expansion.expand env.length { effects := [body] })).bind (effTy sig env) =
      some ⟨.fiberOf p.answer p.error, .never,
        p.requires.union (Requirement.single sig.scopeKey)⟩ := by
  change effTy sig env (.withFiber (.forkScoped body (defaults true))) = _
  exact effTy_complete sig _ env _ (.withFiber (.forkScoped _ (effTy_sound sig body env p hp)))

open Conform.Effect4.Typing (HasTy ActionHasTy effTy_sound effTy_complete) in
/-- `Effect.acquireRelease` with a one-argument release: the release, written under the
resource's binder, gets an unused exit slot inserted after it. -/
theorem releaseOne_typed (sig : Signature NativeOp) (hw : sig.WeakenNatural) (env : TyEnv)
    (acquire release : Eff NativeOp) (a r : EffTy)
    (ha : effTy sig env acquire = some a)
    (hr : effTy sig (env ++ [a.answer]) release = some r) (hn : r.error.normalize = .never) :
    ((all.find? (fun f => f.id == "releaseOne")).bind
      (fun f => f.expansion.expand env.length { effects := [acquire, release] })).bind
        (effTy sig env) =
      some ⟨a.answer, a.error,
        (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩ := by
  change effTy sig env (.acquireRelease acquire (insert (env.length + 1) 1 release)) = _
  have hlen : (env ++ [a.answer]).length = env.length + 1 := by
    simp only [List.length_append, List.length_singleton]
  have hr' : effTy sig (env ++ [a.answer, .exitOf .unknown .unknown])
      (insert (env.length + 1) 1 release) = some r := by
    have h := effTy_insert_append sig hw (env ++ [a.answer]) [.exitOf .unknown .unknown] release
    rw [hlen, List.append_assoc] at h
    exact h.trans hr
  exact effTy_complete sig _ env _
    (.acquireRelease (effTy_sound sig acquire env a ha) (effTy_sound sig _ _ r hr') hn)

end Effect4.Codegen.Forms
