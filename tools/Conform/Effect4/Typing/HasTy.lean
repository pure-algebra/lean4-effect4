import Effect4.Program.Typing

/-!
# Conform.Effect4.Typing.HasTy — the declarative type system of `Eff`

`src/Effect4/Program/Typing.lean` types a program by *running* an algorithm: six mutually
recursive `Option`-valued functions that thread an environment and refuse by answering `none`.
This file states the same type system the other way round — as a family of mutual inductive
judgments, one relation per checker, one rule per arm, written to be **read**:

| judgment | reads | mirrors |
| --- | --- | --- |
| `HasTy sig env e t` | in `Σ`, under `Γ`, the program `e` has the effect type `t` | `effTy` |
| `StmtsHasTy sig env inLoop b g` | a generator body's statements leave the generator state `g` | `stmtsTy` |
| `EffsHasTy sig env es t` | a race's entrants agree on `t` | `effsTy` |
| `ActionHasTy sig env a t` | a fiber action has the effect type `t` | `actionTy` |
| `LayerHasTy sig l s` | the (closed) layer term `l` has the layer signature `s` | `layerTy` |
| `LayersHasTy sig ls s` | a `mergeAll` spine merges to `s` | `layersTy` |

Each rule's premises are exactly the arm's own: the *leaf* equations of the arm
(`termTy`, `causeTy`, `fiberTy`, `litVal`, `Signature.dom/rowOf/serviceTy`, `EffTy.joinAnswer`,
`GenTy.merge`) stay as equations, and the arm's *recursive* calls become judgments. Where the
arm branches — a `match` on the observer mode, a `Bool` case, a guard — the rule carries the
branch explicitly rather than hiding it in a side condition, so what the checker does is visible
without reading the checker. There is no `Option` plumbing, no `do`, no `wp`, and no `match` in
any rule.

**What the rules make visible** (the register rows these judgments were asked to expose):

* `acquireRelease` — the release's error column `r.error` does not appear in the conclusion:
  a finalizer's failures are not in `E` (DI-63, types seat §3.5). The rule shows this by having
  `r` occur only in `requires`.
* `scoped` — the rule is the identity on the body's type, so the `Scope` requirement the body
  carries is *not* discharged (`Effect.scoped` on rc.112 does discharge it); the row survives
  into the conclusion untouched.
* `layerTy` has no rule for `LayerTerm.ref` and `layersTy` none for the empty spine: those are
  the two structural refusals, and their absence from the system is the statement.
* `stmtsTy` has one `ret` rule and its tail is `.nil`: a statement after a `return` has no rule.
* `breakLoop` is stated only at `inLoop = true`.

Soundness (`effTy sig env e = some t → HasTy sig env e t`) and completeness (the converse)
are in `Conform.Effect4.Typing.Sound`; the per-arm inversions the soundness proof consumes are
generated in `Conform.Effect4.Typing.Inversion`.

Citations are the ones the syntax and the checker already carry: `Effect4.Program.arms`
(`src/Effect4/Program/Eff.lean:539-568`) for the `Eff` constructors, the `LayerTerm` and
`WithFiberAction` constructor docstrings (`Eff.lean:364-393`, `Machine/Fibers.lean:288-348`) for
the layer and action arms; the file is `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`
unless another is named.
-/

namespace Conform.Effect4.Typing

open Std (Format)
open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Machine.Env (Requirement)

variable {Op : Type}

mutual

/-- `Σ; Γ ⊢ e : ⟨A, E, R⟩` — the effect type of a program: its answer, its error union, and the
requirement row it performs against. One rule per arm of `effTy` (`Typing.lean:178-281`). -/
inductive HasTy (sig : Signature Op) : TyEnv → Eff Op → EffTy → Prop
  /-- `Effect.succeed` (`:1275`): the value's type, no error, no requirement. -/
  | succeed {env : TyEnv} {value : Term} {ty : Ty} :
      termTy sig env value = some ty →
      HasTy sig env (.succeed value) (EffTy.pure ty)
  /-- `Effect.fail` (`:1322`): the error's type in `E`; the answer is `never`. -/
  | fail {env : TyEnv} {error : Term} {ty : Ty} :
      termTy sig env error = some ty →
      HasTy sig env (.fail error) ⟨.never, ty, Requirement.empty⟩
  /-- `Effect.failCause` (`:1330`): the cause's `fail` reasons are `E`; a defect and an
  interrupt contribute nothing (`causeTy`, `Typing.lean:83-93`). -/
  | failCause {env : TyEnv} {cause : CauseTerm} {ty : Ty} :
      causeTy sig env cause = some ty →
      HasTy sig env (.failCause cause) ⟨.never, ty, Requirement.empty⟩
  /-- `yield* new E()` (`:1226`): a yieldable error, typed as `fail`. -/
  | yieldError {env : TyEnv} {error : Term} {ty : Ty} :
      termTy sig env error = some ty →
      HasTy sig env (.yieldError error) ⟨.never, ty, Requirement.empty⟩
  /-- `Effect.sync` (`:929`): the thunk's type, no error — a `sync` that throws is a defect. -/
  | sync {env : TyEnv} {thunk : Term} {ty : Ty} :
      termTy sig env thunk = some ty →
      HasTy sig env (.sync thunk) (EffTy.pure ty)
  /-- `Effect.suspend` (`:1093`): the body's type, unchanged. -/
  | suspend {env : TyEnv} {body : Eff Op} {t : EffTy} :
      HasTy sig env body t →
      HasTy sig env (.suspend body) t
  /-- `yield* op(x)`, the row's kind deciding the primitive
  (`git:62c04d9:src/Effect4/StdLib/Links.lean`). Two premises, both explicit: the operation is
  in the signature's domain (DI-54 — an index outside the supplied table is refused here, not
  typed through the placeholder row whose `request := .never` admits any `never` term), and the
  request term has exactly the row's request type. -/
  | perform {env : TyEnv} {op : Op} {request : Term} :
      sig.dom op = true →
      termTy sig env request = some (sig.rowOf op).request →
      HasTy sig env (.perform op request)
        ⟨(sig.rowOf op).answer, (sig.rowOf op).error,
          Requirement.ofList (sig.rowOf op).requires⟩
  /-- `Effect.flatMap` (`:1590`): the continuation is typed under the environment extended by
  the first program's answer; the errors join and the rows union. -/
  | bind {env : TyEnv} {first rest : Eff Op} {f r : EffTy} :
      HasTy sig env first f →
      HasTy sig (env ++ [f.answer]) rest r →
      HasTy sig env (.bind first rest)
        ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩
  /-- `Effect.gen(function* () { … })` (`:1184`): the body is typed as a statement sequence
  outside a loop; a body that never returns answers `void`. -/
  | gen {env : TyEnv} {body : Stmts Op} {g : GenTy} :
      StmtsHasTy sig env false body g →
      HasTy sig env (.gen body) ⟨g.answer.getD .unit, g.error, g.requires⟩
  /-- `Effect.catchCause` (`:2417`): the handler sees `Cause<E>` of the body; the two answers
  must join, and the conclusion's error column is the **handler's** alone — the body's failures
  have been caught. -/
  | catchCause {env : TyEnv} {body handler : Eff Op} {b h : EffTy} {answer : Ty} :
      HasTy sig env body b →
      HasTy sig (env ++ [.causeOf b.error]) handler h →
      EffTy.joinAnswer b.answer h.answer = some answer →
      HasTy sig env (.catchCause body handler)
        ⟨answer, h.error, b.requires.union h.requires⟩
  /-- `Effect.matchCauseEffect` (`:2645`): the success branch sees the answer, the failure
  branch the cause; both branches' answers must join and both branches' errors survive. -/
  | matchCause {env : TyEnv} {body onValue onCause : Eff Op} {b v c : EffTy} {answer : Ty} :
      HasTy sig env body b →
      HasTy sig (env ++ [b.answer]) onValue v →
      HasTy sig (env ++ [.causeOf b.error]) onCause c →
      EffTy.joinAnswer v.answer c.answer = some answer →
      HasTy sig env (.matchCause body onValue onCause)
        ⟨answer, v.error.join c.error, (b.requires.union v.requires).union c.requires⟩
  /-- `Effect.onExit` (`:4006`): the finalizer sees `Exit<A, E>` and its answer is discarded,
  but its errors do join — unlike `acquireRelease` below. -/
  | onExit {env : TyEnv} {body finalizer : Eff Op} {b f : EffTy} :
      HasTy sig env body b →
      HasTy sig (env ++ [.exitOf b.answer b.error]) finalizer f →
      HasTy sig env (.onExit body finalizer)
        ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩
  /-- `Effect.exit` (`:2320`): the failure is reified into the answer, so `E` becomes `never`. -/
  | exit {env : TyEnv} {body : Eff Op} {b : EffTy} :
      HasTy sig env body b →
      HasTy sig env (.exit body) ⟨.exitOf b.answer b.error, .never, b.requires⟩
  /-- `Effect.uninterruptible` (`:4302-4310`): a mask changes no column of the type. -/
  | uninterruptible {env : TyEnv} {body : Eff Op} {t : EffTy} :
      HasTy sig env body t →
      HasTy sig env (.uninterruptible body) t
  /-- `Effect.interruptible` (`:4331-4352`): likewise. -/
  | interruptible {env : TyEnv} {body : Eff Op} {t : EffTy} :
      HasTy sig env body t →
      HasTy sig env (.interruptible body) t
  /-- `if` in a generator body (`E4-FLOW-CE-029`): the test is a `bool` term, the two arms'
  answers must join, and **both** arms' requirements are in the conclusion. (The row that is
  not this one — the `then` arm's alone, which rc.112's printed `Effect.suspend` head infers —
  is the red control `tools/conform-red/RulesNeg.lean`.) -/
  | branch {env : TyEnv} {test : Term} {thenB elseB : Eff Op} {a b : EffTy} {answer : Ty} :
      termTy sig env test = some .bool →
      HasTy sig env thenB a →
      HasTy sig env elseB b →
      EffTy.joinAnswer a.answer b.answer = some answer →
      HasTy sig env (.branch test thenB elseB)
        ⟨answer, a.error.join b.error, a.requires.union b.requires⟩
  /-- `Effect.whileLoop` (`:4628`): the cursor is the next variable, initialised by `initial`;
  the test is a `bool` over the cursor, the body runs over the cursor, and the step must give
  back a term of the **cursor's own type** — the loop's invariant, stated as an equation. The
  answer is `void`: the cursor is not returned. -/
  | whileLoop {env : TyEnv} {initial test step : Term} {body : Eff Op} {cursor : Ty} {b : EffTy} :
      termTy sig env initial = some cursor →
      termTy sig (env ++ [cursor]) test = some .bool →
      HasTy sig (env ++ [cursor]) body b →
      termTy sig (env ++ [cursor, b.answer]) step = some cursor →
      HasTy sig env (.whileLoop initial test step body) ⟨.unit, b.error, b.requires⟩
  /-- `Effect.yieldNowWith` (`:982-990`): pure `void`, whatever the priority. -/
  | yieldNow {env : TyEnv} (priority : Nat) :
      HasTy sig env (.yieldNow priority) (EffTy.pure .unit)
  /-- The row's export as an `Async` (`:1109-1143`). Three premises: the domain check of
  `perform` (DI-54), the row's kind is `async` — a *kind* check, which is not the domain check:
  a supplied table can make an in-range row async while the index is outside another
  signature's domain — and the request term's type. -/
  | callback {env : TyEnv} {register : Op} {request : Term} :
      sig.dom register = true →
      (sig.rowOf register).kind = .async →
      termTy sig env request = some (sig.rowOf register).request →
      HasTy sig env (.callback register request)
        ⟨(sig.rowOf register).answer, (sig.rowOf register).error,
          Requirement.ofList (sig.rowOf register).requires⟩
  /-- `Fiber.join` (`:5291`): the handle's value and error columns become the program's, and
  the failure is observable — so `E` is the fiber's error. -/
  | awaitFiber_join {env : TyEnv} {fiber : Term} {handle : Ty} {value error : Ty} :
      termTy sig env fiber = some handle →
      fiberTy handle = some (value, error) →
      HasTy sig env (.awaitFiber fiber .joinEffect) ⟨value, error, Requirement.empty⟩
  /-- `Fiber.await` (`:5304`): the exit is the answer, so nothing fails — `E` is `never`. -/
  | awaitFiber_await {env : TyEnv} {fiber : Term} {handle : Ty} {value error : Ty} :
      termTy sig env fiber = some handle →
      fiberTy handle = some (value, error) →
      HasTy sig env (.awaitFiber fiber .awaitValue) (EffTy.pure (.exitOf value error))
  /-- `Effect.withFiber` (`:1147`): the action's type is the program's. -/
  | withFiber {env : TyEnv} {action : ActionTerm Op} {t : EffTy} :
      ActionHasTy sig env action t →
      HasTy sig env (.withFiber action) t
  /-- `Effect.scoped` (`:3960`): the body's type, **unchanged** — this rule does *not* discharge
  the body's `Scope` requirement, though rc.112's `Effect.scoped` provides one. The row passes
  straight through, in plain sight (DI-63). -/
  | scoped {env : TyEnv} {body : Eff Op} {t : EffTy} :
      HasTy sig env body t →
      HasTy sig env (.scoped body) t
  /-- `Effect.acquireRelease` (`:3978`): the answer and the error are the **acquire's**; the
  release's error column `r.error` does not appear in the conclusion at all — a finalizer's
  failure is a defect, not an `E` (DI-63, types seat §3.5). `r` occurs only in the requirement
  row, and the conclusion adds this signature's `Scope` key. -/
  | acquireRelease {env : TyEnv} {acquire release : Eff Op} {a r : EffTy} :
      HasTy sig env acquire a →
      HasTy sig (env ++ [a.answer, .exitOf a.answer a.error]) release r →
      HasTy sig env (.acquireRelease acquire release)
        ⟨a.answer, a.error, (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩
  /-- The flows' choice point (`Effects.Flow.RawTerm.choose`; refused by the native printer,
  tape-answered at compile): typed exactly as a branch whose test has already been taken. -/
  | choose {env : TyEnv} (site : Nat) {left right : Eff Op} {l r : EffTy} {answer : Ty} :
      HasTy sig env left l →
      HasTy sig env right r →
      EffTy.joinAnswer l.answer r.answer = some answer →
      HasTy sig env (.choose site left right)
        ⟨answer, l.error.join r.error, l.requires.union r.requires⟩
  /-- `Effect.provide` (`internal/layer.ts:8-22`): the layer is typed closed — no environment —
  its error joins the body's, its own requirements are added, and what it provides is
  discharged from the body's row. `isLocal` chooses the memo map at run time and changes no
  column, so the rule holds for both values of the flag. -/
  | provideLayer {env : TyEnv} {layer : LayerTerm Op} (isLocal : Bool) {body : Eff Op}
      {l : LayerTy} {b : EffTy} :
      LayerHasTy sig layer l →
      HasTy sig env body b →
      HasTy sig env (.provideLayer layer isLocal body)
        ⟨b.answer, b.error.join l.error, Row.union l.requires (Row.diff b.requires l.out)⟩
  /-- `Effect.service` (`:2059`): the carrier from the signature's service table, and the key
  itself as the requirement. -/
  | service {env : TyEnv} {key : ServiceKey} {ty : Ty} :
      sig.serviceTy key = some ty →
      HasTy sig env (.service key) ⟨ty, .never, Requirement.single key⟩
  /-- `Effect.provideService` (`:2202-2232`): the value must have the key's carrier type, and
  the key is discharged from the body's row. -/
  | provideService {env : TyEnv} {key : ServiceKey} {value : Term} {body : Eff Op}
      {ty : Ty} {b : EffTy} :
      sig.serviceTy key = some ty →
      termTy sig env value = some ty →
      HasTy sig env body b →
      HasTy sig env (.provideService key value body)
        ⟨b.answer, b.error, Row.diff b.requires (Requirement.single key)⟩

/-- `Σ; Γ; inLoop ⊢ b ⇒ g` — a generator body's statements leave the generator state `g`: the
answer its `return`s agree on (absent before the first), the errors and requirements so far.
One rule per arm of `stmtsTy` (`Typing.lean:328-356`). -/
inductive StmtsHasTy (sig : Signature Op) : TyEnv → Bool → Stmts Op → GenTy → Prop
  /-- The empty body: no answer yet, no error, no requirement. -/
  | nil {env : TyEnv} {inLoop : Bool} :
      StmtsHasTy sig env inLoop .nil ⟨none, .never, Requirement.empty⟩
  /-- `const aN = yield* e`: the rest is typed under the environment extended by the answer. -/
  | bindYield {env : TyEnv} {inLoop : Bool} {effect : Eff Op} {rest : Stmts Op} {t : EffTy}
      {r : GenTy} :
      HasTy sig env effect t →
      StmtsHasTy sig (env ++ [t.answer]) inLoop rest r →
      StmtsHasTy sig env inLoop (.cons (.bindYield effect) rest)
        ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩
  /-- `yield* e`: the answer is dropped, so the environment does not grow. -/
  | yieldDiscard {env : TyEnv} {inLoop : Bool} {effect : Eff Op} {rest : Stmts Op} {t : EffTy}
      {r : GenTy} :
      HasTy sig env effect t →
      StmtsHasTy sig env inLoop rest r →
      StmtsHasTy sig env inLoop (.cons (.yieldDiscard effect) rest)
        ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩
  /-- `return v`: the answer appears, and the tail is `.nil` — there is **no** rule for a
  statement after a return, which is how `stmtsTy` refuses one. -/
  | ret {env : TyEnv} {inLoop : Bool} {value : Term} {ty : Ty} :
      termTy sig env value = some ty →
      StmtsHasTy sig env inLoop (.cons (.ret value) .nil) ⟨some ty, .never, Requirement.empty⟩
  /-- `if (t) { … } else { … }` block-scoped: the branches' bindings do not survive, so all
  three of the branches and the continuation are typed at the same environment; the three
  generator states merge (`GenTy.merge`, which is where two disagreeing `return` types refuse). -/
  | ifElse {env : TyEnv} {inLoop : Bool} {test : Term} {thenB elseB rest : Stmts Op}
      {a b r ab g : GenTy} :
      termTy sig env test = some .bool →
      StmtsHasTy sig env inLoop thenB a →
      StmtsHasTy sig env inLoop elseB b →
      StmtsHasTy sig env inLoop rest r →
      GenTy.merge a b = some ab →
      GenTy.merge ab r = some g →
      StmtsHasTy sig env inLoop (.cons (.ifElse test thenB elseB) rest) g
  /-- `while (true) { … }`: the body is typed **in** a loop, so a `break` inside it has a rule;
  the continuation keeps the ambient flag. -/
  | whileTrue {env : TyEnv} {inLoop : Bool} {body rest : Stmts Op} {b r g : GenTy} :
      StmtsHasTy sig env true body b →
      StmtsHasTy sig env inLoop rest r →
      GenTy.merge b r = some g →
      StmtsHasTy sig env inLoop (.cons (.whileTrue body) rest) g
  /-- `break`: stated only at `inLoop = true` — outside a loop there is no rule. -/
  | breakLoop {env : TyEnv} {rest : Stmts Op} {g : GenTy} :
      StmtsHasTy sig env true rest g →
      StmtsHasTy sig env true (.cons .breakLoop rest) g

/-- `Σ; Γ ⊢ es ⇉ ⟨A, E, R⟩` — the entrants of a race: every entrant's answer joins with the
rest, the errors union and the rows union. One rule per arm of `effsTy`
(`Typing.lean:359-365`). -/
inductive EffsHasTy (sig : Signature Op) : TyEnv → Effs Op → EffTy → Prop
  /-- The empty race: it never answers and never fails (`Supervision.RaceAllState`: pending
  until interrupted). -/
  | nil {env : TyEnv} :
      EffsHasTy sig env .nil ⟨.never, .never, Requirement.empty⟩
  /-- One more entrant: its answer must join with the rest's. -/
  | cons {env : TyEnv} {head : Eff Op} {tail : Effs Op} {h t : EffTy} {answer : Ty} :
      HasTy sig env head h →
      EffsHasTy sig env tail t →
      EffTy.joinAnswer h.answer t.answer = some answer →
      EffsHasTy sig env (.cons head tail)
        ⟨answer, h.error.join t.error, h.requires.union t.requires⟩

/-- `Σ; Γ ⊢ a ⊸ ⟨A, E, R⟩` — a fiber action's effect type. One rule per arm of `actionTy`
(`Typing.lean:368-434`); the citations are the `WithFiberAction` constructor docstrings
(`src/Effect4/Machine/Fibers.lean:288-348`). -/
inductive ActionHasTy (sig : Signature Op) : TyEnv → ActionTerm Op → EffTy → Prop
  /-- `forkUnsafe` (`:5264-5284`): the answer is the child's handle; a fork never fails, and it
  inherits the child's requirements. -/
  | fork {env : TyEnv} {program : Eff Op} (options : Supervision.ForkOptions) {p : EffTy} :
      HasTy sig env program p →
      ActionHasTy sig env (.fork program options)
        ⟨.fiberOf p.answer p.error, .never, p.requires⟩
  /-- `forkIn` (`:5364-5378`): as `fork`, with the target scope a `Scope.Scope` handle. -/
  | forkIn {env : TyEnv} {program : Eff Op} (options : Supervision.ForkOptions) {scope : Term}
      {p : EffTy} :
      HasTy sig env program p →
      termTy sig env scope = some Ty.scope →
      ActionHasTy sig env (.forkIn program options scope)
        ⟨.fiberOf p.answer p.error, .never, p.requires⟩
  /-- `forkScoped` (`:5400-5406`): `forkIn` on the *ambient* scope, so the action itself
  requires this signature's `Scope` key. -/
  | forkScoped {env : TyEnv} {program : Eff Op} (options : Supervision.ForkOptions) {p : EffTy} :
      HasTy sig env program p →
      ActionHasTy sig env (.forkScoped program options)
        ⟨.fiberOf p.answer p.error, .never, p.requires.union (Requirement.single sig.scopeKey)⟩
  /-- `fiberRunIn` (`:5447-5461`): the target must be a fiber handle and the scope a scope
  handle; the action answers `void`. -/
  | runIn {env : TyEnv} {target scope : Term} {handle : Ty} {value error : Ty} :
      termTy sig env target = some handle →
      fiberTy handle = some (value, error) →
      termTy sig env scope = some Ty.scope →
      ActionHasTy sig env (.runIn target scope) (EffTy.pure .unit)
  /-- `fiberInterrupt` (`:857`): the target must be a fiber handle. -/
  | interrupt {env : TyEnv} {target : Term} {handle : Ty} {value error : Ty} :
      termTy sig env target = some handle →
      fiberTy handle = some (value, error) →
      ActionHasTy sig env (.interrupt target) (EffTy.pure .unit)
  /-- A scope's fiber finalizer (`:5368`, `withFiberId`): typed exactly as `interrupt`. -/
  | interruptScoped {env : TyEnv} {target : Term} {handle : Ty} {value error : Ty} :
      termTy sig env target = some handle →
      fiberTy handle = some (value, error) →
      ActionHasTy sig env (.interruptScoped target) (EffTy.pure .unit)
  /-- `fiberInterruptAll` (`:888-915`) with no interruptor: the running fiber's own id. The
  targets are a **list of** fiber handles. -/
  | interruptAll_self {env : TyEnv} {targets : Term} {inner : Ty} {value error : Ty} :
      termTy sig env targets = some (.list inner) →
      fiberTy inner = some (value, error) →
      ActionHasTy sig env (.interruptAll targets none) (EffTy.pure .unit)
  /-- `fiberInterruptAllAs` (`:888-915`): a named interruptor, whose term is a fiber id — a
  `nat`, not a handle. -/
  | interruptAll_by {env : TyEnv} {targets : Term} {who : Term} {inner : Ty} {value error : Ty} :
      termTy sig env targets = some (.list inner) →
      fiberTy inner = some (value, error) →
      termTy sig env who = some .nat →
      ActionHasTy sig env (.interruptAll targets (some who)) (EffTy.pure .unit)
  /-- `fiberAwaitAll` (`:779`, `:5318-5322`): the list of the targets' exits. -/
  | awaitAll {env : TyEnv} {targets : Term} {inner : Ty} {value error : Ty} :
      termTy sig env targets = some (.list inner) →
      fiberTy inner = some (value, error) →
      ActionHasTy sig env (.awaitAll targets) (EffTy.pure (.list (.exitOf value error)))
  /-- `Effect.all`/`forEach` with concurrency (`Layer.ts:1597-1598`): the same type as
  `awaitAll` — the fail-fast interruption is behaviour, not a column. -/
  | awaitAllFailFast {env : TyEnv} {targets : Term} {inner : Ty} {value error : Ty} :
      termTy sig env targets = some (.list inner) →
      fiberTy inner = some (value, error) →
      ActionHasTy sig env (.awaitAllFailFast targets) (EffTy.pure (.list (.exitOf value error)))
  /-- `awaitAllChildren`'s snapshot (`:5318`): a list of fiber handles whose columns this
  typing does not know, spelled with the opaque handle `"unknown"`. -/
  | snapshotChildren {env : TyEnv} :
      ActionHasTy sig env .snapshotChildren
        (EffTy.pure (.list (.fiberOf (.handle "unknown") (.handle "unknown"))))
  /-- `awaitAllChildren`'s exit half: the snapshot term must be exactly that list. -/
  | awaitNewChildren {env : TyEnv} {snapshot : Term} :
      termTy sig env snapshot = some (.list (.fiberOf (.handle "unknown") (.handle "unknown"))) →
      ActionHasTy sig env (.awaitNewChildren snapshot) (EffTy.pure .unit)
  /-- `raceAll`: the entrants' joined type, unchanged. -/
  | raceAll {env : TyEnv} {entrants : Effs Op} {t : EffTy} :
      EffsHasTy sig env entrants t →
      ActionHasTy sig env (.raceAll entrants) t
  /-- `setContext` (`:709-727`): a `Context.Context<unknown>` handle in, `void` out. -/
  | setContext {env : TyEnv} {context : Term} :
      termTy sig env context = some Ty.context →
      ActionHasTy sig env (.setContext context) (EffTy.pure .unit)
  /-- `fiber.context` as a value (`getContext`, `:2153`). -/
  | getContext {env : TyEnv} :
      ActionHasTy sig env .getContext (EffTy.pure Ty.context)
  /-- `withFiberId`: the running fiber's id, a `nat`. -/
  | getId {env : TyEnv} :
      ActionHasTy sig env .getId (EffTy.pure .nat)
  /-- `scopeClose` from the fiber (`Scope.ts` via `:3826`): a scope handle and an `Exit`. -/
  | closeScope {env : TyEnv} {scope exit : Term} {value error : Ty} :
      termTy sig env scope = some Ty.scope →
      termTy sig env exit = some (.exitOf value error) →
      ActionHasTy sig env (.closeScope scope exit) (EffTy.pure .unit)

/-- `Σ ⊢ l : Layer⟨ROut, E, RIn⟩` — a layer term's signature. Bodies are **closed**: a layer's
own scope is its ambient one (`Layer.ts:1438`), so every body is typed at the empty
environment, which is why this judgment carries no `Γ`. One rule per arm of `layerTy`
(`Typing.lean:290-314`) — except `LayerTerm.ref`, which has none. -/
inductive LayerHasTy (sig : Signature Op) : LayerTerm Op → LayerTy → Prop
  /-- `Layer.succeed(key, value)` (`Layer.ts:1074`): a service from a value already in hand.
  The premise is that the literal is in the machine's value alphabet — a string is not
  (`PROV-FB-STRING-VALUE`) — and the value's *type* plays no part. -/
  | succeed {key : ServiceKey} {value : Lit} {v : _root_.Effect4.Machine.Env.Val} :
      litVal value = some v →
      LayerHasTy sig (.succeed key value) ⟨Requirement.single key, .never, Requirement.empty⟩
  /-- `Layer.effect(key, body)` (`Layer.ts:1427`): the layer provides its key with the body's
  error, and requires the body's **scope-free** row — the layer's own scope answers the body's
  `Scope` requirement (`:1438`, `bodyRequires`). -/
  | effect {key : ServiceKey} {body : Eff Op} {t : EffTy} :
      HasTy sig [] body t →
      LayerHasTy sig (.effect key body) ⟨Requirement.single key, t.error, bodyRequires sig t⟩
  /-- `Layer.effectDiscard(body)` (`Layer.ts:1512`): construction work that provides nothing. -/
  | effectDiscard {body : Eff Op} {t : EffTy} :
      HasTy sig [] body t →
      LayerHasTy sig (.effectDiscard body) ⟨Requirement.empty, t.error, bodyRequires sig t⟩
  /-- `self.pipe(Layer.provide(that))` (`Layer.ts:2258`): the dependency discharges what it
  provides, and only `self`'s output survives (`LayerTy.provide`). -/
  | provide {self that : LayerTerm Op} {s t : LayerTy} :
      LayerHasTy sig self s →
      LayerHasTy sig that t →
      LayerHasTy sig (.provide self that) (s.provide t)
  /-- `self.pipe(Layer.provideMerge(that))` (`Layer.ts:2704`): the same requirement algebra,
  both outputs kept. -/
  | provideMerge {self that : LayerTerm Op} {s t : LayerTy} :
      LayerHasTy sig self s →
      LayerHasTy sig that t →
      LayerHasTy sig (.provideMerge self that) (s.provideMerge t)
  /-- `Layer.merge(left, right)` (`Layer.ts:1850`): siblings share nothing — outputs and
  requirements both union. -/
  | merge {left right : LayerTerm Op} {a b : LayerTy} :
      LayerHasTy sig left a →
      LayerHasTy sig right b →
      LayerHasTy sig (.merge left right) (a.merge b)
  /-- `Layer.fresh(inner)` (`Layer.ts:3850`): the same signature, a private memo map. -/
  | fresh {inner : LayerTerm Op} {l : LayerTy} :
      LayerHasTy sig inner l →
      LayerHasTy sig (.fresh inner) l
  /-- `Layer.orDie(inner)` (`Layer.ts:3327`): the error column becomes `never`. -/
  | orDie {inner : LayerTerm Op} {l : LayerTy} :
      LayerHasTy sig inner l →
      LayerHasTy sig (.orDie inner) l.orDie
  /-- `Layer.mergeAll(a, b, …)` (`Layer.ts:1652`): the spine's merge. -/
  | mergeAll {layers : LayerTerms Op} {l : LayerTy} :
      LayersHasTy sig layers l →
      LayerHasTy sig (.mergeAll layers) l

/-- `Σ ⊢ ls ⇛ Layer⟨…⟩` — the spine of a `Layer.mergeAll` (`Layer.ts:1652`, at least one):
`LayerTy.merge` folded to the right. One rule per arm of `layersTy` (`Typing.lean:318-324`) —
except the empty spine, which has none. -/
inductive LayersHasTy (sig : Signature Op) : LayerTerms Op → LayerTy → Prop
  /-- A one-layer spine is that layer. -/
  | one {head : LayerTerm Op} {l : LayerTy} :
      LayerHasTy sig head l →
      LayersHasTy sig (.cons head .nil) l
  /-- Two or more: the head merged with the rest as siblings. -/
  | cons {head next : LayerTerm Op} {rest : LayerTerms Op} {h t : LayerTy} :
      LayerHasTy sig head h →
      LayersHasTy sig (.cons next rest) t →
      LayersHasTy sig (.cons head (.cons next rest)) (h.merge t)

end

/-! ## The shapes of the six judgments, as a receipt

`#check` on each relation is the machine's statement that the arities above are the checkers'
arities: `HasTy` threads `TyEnv`, `StmtsHasTy` threads `TyEnv` and the loop flag,
`LayerHasTy` and `LayersHasTy` thread neither. -/

section Shapes
variable (sig : Signature Op)

example : TyEnv → Eff Op → EffTy → Prop := HasTy sig
example : TyEnv → Bool → Stmts Op → GenTy → Prop := StmtsHasTy sig
example : TyEnv → Effs Op → EffTy → Prop := EffsHasTy sig
example : TyEnv → ActionTerm Op → EffTy → Prop := ActionHasTy sig
example : LayerTerm Op → LayerTy → Prop := LayerHasTy sig
example : LayerTerms Op → LayerTy → Prop := LayersHasTy sig

end Shapes

end Conform.Effect4.Typing
