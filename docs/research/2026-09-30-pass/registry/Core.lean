import Effect4.Api.Supervision

/-! Registry seat: the shared definitions the probes import (module `registry.Core`).

Research evidence outside the Test root. Base `be15b062`. Compiled into the session scratchpad
and imported by `StaticEnv.lean`, `Declared.lean` and `Proofs.lean` (commands in `note.md`).

Three parts:

1. `staticEnvAt`, a fold along a path giving the checker's static environment there, and an
   oracle that reads the same environment off the real checker's refusals.
2. The proposed fork-ledger record, `ForkRecord`, with its creating-construct field `kind`.
3. The derived registry: a fiber's declared type from its record, the root program and the
   checker, with no type stored in any value; and path C's one-recursion check `fitsB` reading
   that registry. -/

set_option autoImplicit false

namespace Research.Pass.Registry
open Effect4 Effect4.Machine Effect4.Program

variable {Op : Type}

/-! ## 1. The static environment at a path -/

/-- One step of the checker's environment rule: the state at child `i` of node `n`, which sits
at path `p` under state `st` (the environment, and whether `break` is legal). `none` when `n`
has no child `i` or a sibling the rule reads does not check. Each arm transcribes the rule of
`Checker.check`/`checkStmt`/`checkStmts`/`checkEffs`/`checkAction` (`Program/Checker.lean:116-382`)
for that child. Layers are closed: `checkLayer` takes no environment and checks an effect body
at `[]` (`:227-266`). -/
def stepEnv (sig : Signature Op) (st : TyEnv × Bool) (p : List Nat) :
    Node Op → Nat → Option (TyEnv × Bool)
  | .eff (.suspend _), 0 => some st
  | .eff (.bind _ _), 0 => some st
  | .eff (.bind first _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) first).toOption.map fun f => (st.1 ++ [f.answer], st.2)
  | .eff (.gen _), 0 => some (st.1, false)
  | .eff (.catchCause _ _), 0 => some st
  | .eff (.catchCause body _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b =>
      (st.1 ++ [.causeOf b.error], st.2)
  | .eff (.catchIf _ _ _), 0 => some st
  | .eff (.catchIf _ body _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b => (st.1 ++ [b.error], st.2)
  | .eff (.select s d _ _), 0 =>
    ((termTy sig st.1 s).bind d.arms).map fun arms => (st.1 ++ arms.1, st.2)
  | .eff (.select s d _ _), 1 =>
    ((termTy sig st.1 s).bind d.arms).map fun arms => (st.1 ++ arms.2, st.2)
  | .eff (.matchCause _ _ _), 0 => some st
  | .eff (.matchCause body _ _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b => (st.1 ++ [b.answer], st.2)
  | .eff (.matchCause body _ _), 2 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b =>
      (st.1 ++ [.causeOf b.error], st.2)
  | .eff (.onExit _ _), 0 => some st
  | .eff (.onExit body _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) body).toOption.map fun b =>
      (st.1 ++ [.exitOf b.answer b.error], st.2)
  | .eff (.exit _), 0 => some st
  | .eff (.uninterruptible _), 0 => some st
  | .eff (.interruptible _), 0 => some st
  | .eff (.iterate cursorTy initial _ _ _ _), 0 =>
    (termTy sig st.1 initial).map fun c0 => (st.1 ++ [cursorTy.getD c0], st.2)
  | .eff (.withFiber _), 0 => some st
  | .eff (.scoped _), 0 => some st
  | .eff (.acquireRelease _ _), 0 => some st
  | .eff (.acquireRelease acquire _), 1 =>
    (Checker.check sig st.1 (p ++ [0]) acquire).toOption.map fun a =>
      (st.1 ++ [a.answer, .exitOf .unknown .unknown], st.2)
  | .eff (.provideLayer _ _ _), 0 => some ([], false)
  | .eff (.provideLayer _ _ _), 1 => some st
  | .eff (.provideService _ _ _), 0 => some st
  | .action (.fork _ _), 0 => some st
  | .action (.forkIn _ _ _), 0 => some st
  | .action (.forkScoped _ _), 0 => some st
  | .action (.raceAll _), 0 => some st
  | .effs (.cons _ _), 0 => some st
  | .effs (.cons _ _), 1 => some st
  | .layer _, _ => some ([], false)
  | .layers _, _ => some ([], false)
  | .stmts (.cons _ _), 0 => some st
  | .stmts (.cons head _), 1 =>
    (Checker.checkStmt sig st.1 st.2 (p ++ [0]) head).toOption.map fun s =>
      s.fold (fun _ binds => (st.1 ++ binds, st.2)) (fun _ => st) st
  | .stmt (.bindYield _), 0 => some st
  | .stmt (.yieldDiscard _), 0 => some st
  | .stmt (.ifElse _ _ _), 0 => some st
  | .stmt (.ifElse _ _ _), 1 => some st
  | .stmt (.whileTrue _), 0 => some (st.1, true)
  | _, _ => none

/-- The state along a path, from node `n` at path `p` under state `st`. -/
def envAlong (sig : Signature Op) : Node Op → List Nat → TyEnv × Bool → List Nat →
    Option (TyEnv × Bool)
  | _, _, st, [] => some st
  | n, p, st, i :: rest =>
    (stepEnv sig st p n i).bind fun st' =>
      (n.child i).bind fun c => envAlong sig c (p ++ [i]) st' rest

/-- The checker's static environment at `path` in a program checked from the empty
environment, as `typeOf` checks it. -/
def staticEnvAt (sig : Signature Op) (root : Eff Op) (path : List Nat) : Option TyEnv :=
  (envAlong sig (.eff root) [] ([], false) path).map (·.1)

/-! ### The oracle: the environment read off the checker's refusals -/

/-- Replace the node at a path; `none` when the path leaves the tree or the sorts differ. -/
def setAt : Node Op → List Nat → Node Op → Option (Node Op)
  | _, [], x => some x
  | n, i :: rest, x => (n.child i).bind fun c => (setAt c rest x).bind fun c' => n.setChild i c'

/-- The probe of level `i`: the checker always refuses it, naming level `i`'s type
(`exitExpected` or `scopeExpected`) or saying level `i` is unbound (`term`). -/
def probeNode (i : Nat) : Node Op := .eff (.withFiber (.closeScope (.var i) (.var i)))

/-- Level `i` of the environment the checker uses at `p`, read off the refusal of the probed
program: `some (some t)` its type, `some none` when level `i` is unbound there, `none` when the
refusal is not the probe's. -/
def probeEntry (sig : Signature Op) (root : Eff Op) (p : List Nat) (i : Nat) :
    Option (Option Ty) :=
  match setAt (.eff root) p (probeNode i) with
  | some (.eff probed) =>
    match Checker.check sig [] [] probed with
    | .error ⟨q, .exitExpected t⟩ => if q = p ++ [0] then some (some t) else none
    | .error ⟨q, .scopeExpected t⟩ => if q = p ++ [0] then some (some t) else none
    | .error ⟨q, .term (.var j)⟩ => if q = p ++ [0] ∧ j = i then some none else none
    | _ => none
  | _ => none

/-- The environment the checker uses at `p`, read level by level, at most `bound` levels. -/
def probeEnv (sig : Signature Op) (root : Eff Op) (p : List Nat) (bound : Nat) : Option TyEnv :=
  go 0 bound
where
  go (i : Nat) : Nat → Option TyEnv
    | 0 => none
    | k + 1 =>
      match probeEntry sig root p i with
      | some none => some []
      | some (some t) => (go (i + 1) k).map (t :: ·)
      | none => none

/-! ## 2. The proposed ledger record -/

/-- Which caller of `spawn` made the fiber. `spawn` (`Machine/Fibers.lean:924-939`) has exactly
three callers, and each knows its kind as a constant:

* the `fork`, `forkIn` and `forkScoped` arms of `evaluatePrim.withFiber` (`:1212-1238`), and
  their shared twins `FiberAction.fork`/`forkIn`/`forkScoped` (`:1424-1461`), pass the action's
  site;
* `launchEntrant` (`:955-959`, from `Cmd.launch`, `:1852-1869`) passes the race cell;
* `forkFinalizers` (`:965-971`, from the `closePar` arms, `:1311-1316`, `:1475-1480`) passes
  nothing: a parallel scope close has no source node. -/
inductive ForkKind
  | action
  | raceEntrant
  | finalizer
deriving DecidableEq, Repr

/-- One record per forked fiber, appended by `spawn` beside the `forked` event (the fork-ledger
plan's record, `2026-09-30-origin-ledger-and-step-invariants-plan.md` §3, with `kind` added).
Roots get no record. -/
structure ForkRecord where
  child : FiberId
  parent : FiberId
  daemon : Bool
  /-- The source node's path: the action node, the race cell, or the layer node of a layer
  sibling build; `[]` when there is none. -/
  site : List Nat
  kind : ForkKind
deriving DecidableEq, Repr

/-- The record the machine would have written, reconstructed from today's `RunFiber.origin`.
Research stand-in only: today's origin has no kind, so the kind is read back from the node at
the site, and the empty site is read as a finalizer, which the native census supports (the
only native caller that passes `[]` is `forkFinalizers`; `note.md` §1). The ledger removes this
guess by recording `kind` at `spawn`. -/
def recordOf (root : Eff Op) (f : FiberId) : Origin → Option ForkRecord
  | .root => none
  | .forked parent daemon [] => some ⟨f, parent, daemon, [], .finalizer⟩
  | .forked parent daemon site =>
    match Node.at_ (.eff root) site with
    | some (.effs (.cons _ _)) => some ⟨f, parent, daemon, site, .raceEntrant⟩
    | _ => some ⟨f, parent, daemon, site, .action⟩

/-! ## 3. The derived registry -/

/-- The declared type of a program at a site, checked in the site's static environment. -/
def checkedAt (sig : Signature Op) (root : Eff Op) (site : List Nat) (body : Eff Op) :
    Option EffTy :=
  (staticEnvAt sig root site).bind fun env => (Checker.check sig env (site ++ [0]) body).toOption

/-- A forked fiber's declared type, from its record, the root program and the checker. The root
must have its layer references expanded (`Eff.expandRefs`, as `typeOfProgram` checks it); a
reference is a leaf, so every recorded site keeps its path.

* A source fork: the checker's type of the forked program at the site's static environment,
  exactly the `fiberOf` the checker gives the handle (`checkAction`, `Checker.lean:321-332`).
* A race entrant: the entrant's type at the cell's environment (`checkEffs`, `:311-316`).
* A layer sibling build: it answers the built service spine, which no `Ty` names (a probe
  shows `Val.hasTy _ Ty.context` refuses it), so `unknown`; its error is the layer's.
* A finalizer daemon: `unknown`, since the parallel close discards the answer
  (`Cmd.closeParAwait`, `exitAsVoidAll`), and `never`, since a release cannot fail with a typed
  error (`releaseFails`, `Checker.lean:201-210`) and the other finalizer programs
  (`finProgram`, `Machine/Stores.lean:1769-1795`) interrupt, close, remove or complete. -/
def ForkRecord.declared (sig : Signature Op) (root : Eff Op) (r : ForkRecord) : Option EffTy :=
  match r.kind with
  | .action =>
    match Node.at_ (.eff root) r.site with
    | some (.action (.fork body _)) => checkedAt sig root r.site body
    | some (.action (.forkIn body _ _)) => checkedAt sig root r.site body
    | some (.action (.forkScoped body _)) => checkedAt sig root r.site body
    | some (.layer l) =>
      (Checker.checkLayer sig r.site l).toOption.map fun t => ⟨.unknown, t.error, t.requires⟩
    | _ => none
  | .raceEntrant =>
    match Node.at_ (.eff root) r.site with
    | some (.effs (.cons head _)) => checkedAt sig root r.site head
    | _ => none
  | .finalizer => some ⟨.unknown, .never, Env.Requirement.empty⟩

/-- The registry on today's machine: a fiber's declared type by id. The root's is the whole
program's type; a forked fiber's is its record's. `none` for an id the machine does not hold. -/
def fiberDecl (sig : Signature NativeOp) (root : Eff NativeOp) (rootTy : EffTy)
    (m : Api.Machine) (id : FiberId) : Option EffTy :=
  (m.fiber? id).bind fun f =>
    match f.origin with
    | .root => some rootTy
    | origin => (recordOf root id origin).bind (ForkRecord.declared sig root)

/-! ### Path C with the registry: shape and fiber declarations in one recursion -/

/-- Shape and fiber declarations together, over the encoding `Val.hasTy` reads: products as a
two-cell list, Results and exits as constructors, snapshots decoded. Everything else falls back
to the existing shape check. Copied from path C of
`2026-09-30-host-answers-evidence/PathProbes.lean:104-138`, with the allocation table passed
through. -/
def fitsB (decl : FiberId → Option EffTy) (allocated : List String) (v : Val) : Ty → Bool
  | .fiberOf a e =>
    match v with
    | .handle 1 id =>
      match decl ⟨id⟩ with
      | some d => d.answer.sub a && d.error.sub e
      | none => false
    | _ => false
  | .prod a b =>
    match v with
    | .list [x, y] => fitsB decl allocated x a && fitsB decl allocated y b
    | _ => false
  | .except e a =>
    match v with
    | .ctor 0 [err] => fitsB decl allocated err e
    | .ctor 1 [val] => fitsB decl allocated val a
    | _ => false
  | .exitOf a e =>
    match v with
    | .ctor 0 [x] => fitsB decl allocated x a
    | _ => Val.hasTy v (.exitOf a e) allocated
  | .option a =>
    match v with
    | .none => true
    | .some x => fitsB decl allocated x a
    | _ => false
  | .list a =>
    match v with
    | .list xs => xs.attach.all fun ⟨x, _⟩ => fitsB decl allocated x a
    | _ =>
      match Val.snapshot? v with
      | some ids => ids.all fun id => fitsB decl allocated (Value.fiber id.value) a
      | none => false
  | .union l r => fitsB decl allocated v l || fitsB decl allocated v r
  | ty => Val.hasTy v ty allocated

/-! ## Shared fixtures -/

namespace Fixtures

def n (i : Nat) : Term := .lit (.nat i)
def s (x : String) : Term := .lit (.str x)
def v (i : Nat) : Term := .var i
def u : Term := .lit .unit
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def forkOf (body : Eff NativeOp) : Eff NativeOp := .withFiber (.fork body opts)
def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def key2 : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩
def ap (a : String) (xs : List Term) : Term :=
  .app a (xs.foldr (fun t acc => .cons t acc) .nil)

/-- Each binder form of the checker with a fork under it whose body reads the bound level, and
the answer type that body must be declared at. -/
def binderForms : List (String × Eff NativeOp × Ty) := [
  ("bind", .bind (.succeed (s "x")) (forkOf (.succeed (v 0))), .string),
  ("gen.bindYield",
    .gen (.cons (.bindYield (.succeed (s "x")))
      (.cons (.yieldDiscard (forkOf (.succeed (v 0)))) (.cons (.ret (n 1)) .nil))), .string),
  ("catchCause.handler", .catchCause (.fail (n 7)) (forkOf (.succeed (v 0))), .causeOf .nat),
  ("catchIf.handler", .catchIf (.lit (.bool true)) (.fail (n 7)) (forkOf (.succeed (v 0))), .nat),
  ("select.option", .select (ap "some" [n 4]) .option (.succeed u) (forkOf (.succeed (v 0))), .nat),
  ("matchCause.value", .matchCause (.succeed (s "x")) (forkOf (.succeed (v 0))) (.succeed u), .string),
  ("matchCause.cause", .matchCause (.fail (n 7)) (.succeed u) (forkOf (.succeed (v 0))), .causeOf .nat),
  ("onExit.finalizer", .onExit (.succeed (s "x")) (forkOf (.succeed (v 0))), .exitOf .string .never),
  ("iterate.body",
    .iterate none (n 0) (ap "lt" [v 0, n 3]) (ap "succ" [v 0]) (v 0) (forkOf (.succeed (v 0))), .nat),
  ("acquireRelease.release",
    .scoped (.acquireRelease (.succeed (s "x")) (forkOf (.succeed (v 1)))), .exitOf .unknown .unknown),
  ("layer.effect resets",
    .bind (.succeed (n 9)) (.scoped (.provideLayer
      (.effect key (.bind (.succeed (s "x")) (.bind (forkOf (.succeed (v 0))) (.succeed (n 1)))))
      false (.service key))), .string),
  ("provideService.body",
    .provideService key2 (n 9) (.bind (.succeed (s "x")) (forkOf (.succeed (v 0)))), .string),
  ("forkIn", .bind (.perform (.scopeMake .sequential) u)
    (.bind (.succeed (s "x")) (.withFiber (.forkIn (.succeed (v 1)) opts (v 0)))), .string),
  ("forkScoped",
    .scoped (.bind (.succeed (s "x")) (.withFiber (.forkScoped (.succeed (v 0)) opts))), .string),
  ("nested fork",
    .bind (.succeed (s "x")) (forkOf (.bind (.succeed (n 1)) (forkOf (.succeed (v 0))))), .string)]

/-- Layer sibling builds: a reference inside a `merge`, and a sibling that fails. -/
def layerCases : List (String × Eff NativeOp) := [
  ("merge.ref",
    .bind (.provideLayer (.succeed key (.nat 7)) false (.service key))
      (.provideLayer (.merge (.ref [0, 0]) (.succeed key2 (.nat 2))) false (.service key))),
  ("merge.failing",
    .provideLayer (.merge (.succeed key (.nat 1)) (.effect key2 (.fail (n 3)))) false (.service key)),
  ("mergeAll.failing",
    .provideLayer (.mergeAll (.cons (.effect key (.fail (n 3))) (.cons (.succeed key2 (.nat 2)) .nil)))
      false (.service key2))]

end Fixtures

/-! ## Local controls -/

abbrev NEff := Eff NativeOp

private def n (i : Nat) : Term := .lit (.nat i)
private def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩

/-- A fork under a binder whose body reads the binder: `bind (succeed "s") (fork (succeed v0))`. -/
private def underBinder : NEff :=
  .bind (.succeed (.lit (.str "s"))) (.withFiber (.fork (.succeed (.var 0)) opts))

#guard staticEnvAt (nativeSignature []) underBinder [1, 0] = some [.string]
#guard probeEnv (nativeSignature []) underBinder [1] 3 = some [.string]
#guard checkedAt (nativeSignature []) underBinder [1, 0] (.succeed (.var 0)) =
  some (EffTy.pure .string)
-- the body alone, checked at the empty environment, does not type: the environment is needed
#guard (Checker.check (nativeSignature []) [] [1, 0, 0] (.succeed (.var 0) : NEff)).toOption = none

end Research.Pass.Registry
