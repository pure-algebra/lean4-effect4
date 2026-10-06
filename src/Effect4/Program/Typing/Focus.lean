module

public import Effect4.Program.Typing

/-!
# Program.Typing.Focus — the focus at an address: the sub-program, its environment, its type

**The question.** The checker answers one type for a whole program, or its first located
refusal (`Program/Checker.lean`). A tool that stands at one place of a program asks more: which
sub-program stands there, which variables it can read and at which types, and which type it has
there. This module answers the three, with one function, `focusAt`.

An **address** is a path of child indices from the root of a program (`Node.at_`,
`Program/Refs.lean`). The **focus** is the sub-program at an address, with the environment and
the type that the rest of the program gives it (`Focus`).

## What a node reads from above

A typing rule gives each child of a node an environment. What a child reads depends on its sort
(`NodeEnv`), because the six typing judgments have three shapes
(`Laws/Program/Typing/HasTy.lean`):

| Sort of node | Its judgment reads | `NodeEnv` |
| --- | --- | --- |
| a program, the entrants of a race, a fiber action | the types of the variables in scope | `env` |
| a statement list, a statement | those, and whether a loop encloses it | `body` |
| a layer, a layer spine | nothing: a layer is typed closed | `closed` |

## The step, and its fold along a path

`Node.childEnv` is one step: the environment that a node at an environment gives its child. It
has one case for each arm of the generated `Node.child` (`Program/NodeLenses.lean`), in that
function's order. It has one more, because the statements after a `bindYield` read the head's
answer. Each case says what the typing rule of its constructor says:

- most children are typed at their parent's environment;
- a continuation reads the answer of the program before it (`bind`, a `bindYield`);
- a handler reads the error or the cause of its body, a finalizer reads the exit, and a release
  reads the acquired value;
- an arm of `select` reads what the decision binds, and the body of `iterate` reads the cursor;
- the body of a loop is typed in a loop, and the body of a layer at the empty environment.

Where a rule extends the environment by a type, the step asks the checker for that type: `effTy`
on the earlier sibling program, or `termTy` on a term of the node. So a sibling with no type
gives no environment to the children after it, and the step answers `none` there.

`Node.envAt` folds the step along a path: the environment at an address, at every sort of node.
`focusAt` answers at an address of a program: the sub-program, its environment by `Node.envAt`,
and its type by `effTy`.

## What each caller reads

- **A tool at a hole, or at any address of a program**: `focusAt`, and `Sketch.focusAt` at a
  sketch (`Program/Sketch.lean`). The laws of filling and of omitting hold at its answer
  (`Sketch.check_fill_focusAt`, `Sketch.check_omit_focusAt`, `Laws/Program/Sketch.lean`).
- **A reader of a term's type**, as the TypeScript printer at an eliminator. A term has no
  address. Its type is `termTy` at the environment of its node:
  `(n.envAt s ctx path).map NodeEnv.tyEnv`. `Node.envAt` answers at a statement and at a fiber
  action too, and it answers where the node itself has no type. Four kinds of term read an
  extension of their node's environment: the test of `catchIf` reads the body's error; the test
  and the result of `iterate` read the cursor; its step reads the cursor and the body's answer;
  an operation's own term reads its current value. `Checker.check` shows each.

## The cost

Nothing is stored. One call walks one path. On the way it checks each earlier sibling that a
rule reads, once. Those sub-programs are disjoint, so one call costs at most one check of the
program. A walk that asks at every address checks a sub-program once for each step that reads
it, so it costs more than one check.

## The laws

`Laws/Program/Typing/Replace.lean` proves the step against the typing rules, one case for each
case here (`NodeHasTy.child_step`), and it folds that along a path (`NodeHasTy.replace_envAt`).
`Laws/Program/Typing/Focus.lean` has the laws of `focusAt`:

- its answer is the sub-program at the address, typed there (`focusAt_typed`);
- on a typed program it answers at every address of a program (`hasTy_focusAt`);
- a program of the answered type in the answered environment stands in the focus's place, and
  the whole keeps its type (`hasTy_replace_focusAt`, `check_replace_focusAt`).

## What this module is not

- It is not a second checker, and it changes no line of the checker. It calls `effTy` on
  sub-programs.
- It is not a trace. The trace is the machine's list of run events.
- It does not go on past a refusal. A checker that marks every refusal and goes on is another
  slice.
- It knows no gap and no hole. A hole is a host row, and the step reads it as `effTy` does.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- **The environment of a node**: what the typing judgment of a node's sort reads from the
nodes above it. -/
inductive NodeEnv where
  /-- a program, the entrants of a race, a fiber action: the types of the variables in scope -/
  | env (env : TyEnv)
  /-- a statement list, a statement: the types of the variables in scope, and the loop flag -/
  | body (env : TyEnv) (inLoop : Bool)
  /-- a layer, a layer spine: nothing, because a layer is typed closed -/
  | closed
deriving DecidableEq, Repr

namespace NodeEnv

/-- The types of the variables in scope at a node. A layer has none. A term of the node is
typed here, or at an extension of it that the node's rule states. -/
def tyEnv : NodeEnv → TyEnv
  | .env tys => tys
  | .body tys _ => tys
  | .closed => []

/-- Whether a loop encloses a statement. Every other sort answers `false`. -/
def inLoop : NodeEnv → Bool
  | .body _ flag => flag
  | _ => false

end NodeEnv

namespace Node

/-- **The step: the environment that a node at an environment gives its child.** One case for
each arm of `Node.child`, in that function's order, and one more for the statements after a
`bindYield`. Each case is the environment of the child in the typing rule of its constructor
(`HasTy` and its five siblings, `Laws/Program/Typing/HasTy.lean`).

Eleven cases extend the environment by a type that the rule reads first. Eight ask `effTy` for
the type of an earlier sibling program. Three ask `termTy` for the type of a term of the node.
Such a case answers `none` when the checker refuses what it reads. Every case answers the
environment of the child's own sort, from any environment of the node. -/
def childEnv (s : Signature Op) (ctx : NodeEnv) : Node Op → Nat → Option NodeEnv
  | eff (.suspend _), 0 => some (.env ctx.tyEnv)
  | eff (.bind _ _), 0 => some (.env ctx.tyEnv)
  -- the continuation reads the first program's answer
  | eff (.bind a0 _), 1 => (effTy s ctx.tyEnv a0).map fun f => .env (ctx.tyEnv ++ [f.answer])
  -- a generator body starts outside a loop
  | eff (.gen _), 0 => some (.body ctx.tyEnv false)
  | eff (.catchCause _ _), 0 => some (.env ctx.tyEnv)
  -- the handler reads the cause of the body's error
  | eff (.catchCause a0 _), 1 =>
    (effTy s ctx.tyEnv a0).map fun b => .env (ctx.tyEnv ++ [.causeOf b.error])
  | eff (.matchCause _ _ _), 0 => some (.env ctx.tyEnv)
  -- the success branch reads the body's answer
  | eff (.matchCause a0 _ _), 1 =>
    (effTy s ctx.tyEnv a0).map fun b => .env (ctx.tyEnv ++ [b.answer])
  -- the failure branch reads the cause of the body's error
  | eff (.matchCause a0 _ _), 2 =>
    (effTy s ctx.tyEnv a0).map fun b => .env (ctx.tyEnv ++ [.causeOf b.error])
  | eff (.onExit _ _), 0 => some (.env ctx.tyEnv)
  -- the finalizer reads the body's exit
  | eff (.onExit a0 _), 1 =>
    (effTy s ctx.tyEnv a0).map fun b => .env (ctx.tyEnv ++ [.exitOf b.answer b.error])
  | eff (.exit _), 0 => some (.env ctx.tyEnv)
  | eff (.uninterruptible _), 0 => some (.env ctx.tyEnv)
  | eff (.interruptible _), 0 => some (.env ctx.tyEnv)
  | eff (.withFiber _), 0 => some (.env ctx.tyEnv)
  | eff (.scoped _), 0 => some (.env ctx.tyEnv)
  | eff (.acquireRelease _ _), 0 => some (.env ctx.tyEnv)
  -- the release reads the acquired value and the scope's closing exit
  | eff (.acquireRelease a0 _), 1 =>
    (effTy s ctx.tyEnv a0).map fun a =>
      .env (ctx.tyEnv ++ [a.answer, .exitOf .unknown .unknown])
  -- a layer is typed closed
  | eff (.provideLayer _ _ _), 0 => some .closed
  | eff (.provideLayer _ _ _), 1 => some (.env ctx.tyEnv)
  | eff (.provideService _ _ _), 0 => some (.env ctx.tyEnv)
  | eff (.catchIf _ _ _), 0 => some (.env ctx.tyEnv)
  -- the handler reads the body's error
  | eff (.catchIf _ a1 _), 1 =>
    (effTy s ctx.tyEnv a1).map fun b => .env (ctx.tyEnv ++ [b.error])
  -- each arm reads what the decision binds from the type of its term
  | eff (.select t d _ _), 0 =>
    ((termTy s ctx.tyEnv t).bind d.arms).map fun arms => .env (ctx.tyEnv ++ arms.1)
  | eff (.select t d _ _), 1 =>
    ((termTy s ctx.tyEnv t).bind d.arms).map fun arms => .env (ctx.tyEnv ++ arms.2)
  -- the body reads the cursor: its annotation, or the type of the initial term
  | eff (.iterate cursorTy initial _ _ _ _), 0 =>
    (termTy s ctx.tyEnv initial).map fun c0 => .env (ctx.tyEnv ++ [cursorTy.getD c0])
  | eff (.restore _ _), 0 => some (.env ctx.tyEnv)
  | action (.fork _ _), 0 => some (.env ctx.tyEnv)
  | action (.forkIn _ _ _), 0 => some (.env ctx.tyEnv)
  | action (.forkScoped _ _), 0 => some (.env ctx.tyEnv)
  | action (.raceAll _), 0 => some (.env ctx.tyEnv)
  -- the body of a layer is typed at the empty environment
  | layer (.effect _ _), 0 => some (.env [])
  | layer (.effectDiscard _), 0 => some (.env [])
  | layer (.provide _ _), 0 => some .closed
  | layer (.provide _ _), 1 => some .closed
  | layer (.provideMerge _ _), 0 => some .closed
  | layer (.provideMerge _ _), 1 => some .closed
  | layer (.merge _ _), 0 => some .closed
  | layer (.merge _ _), 1 => some .closed
  | layer (.fresh _), 0 => some .closed
  | layer (.orDie _), 0 => some .closed
  | layer (.mergeAll _), 0 => some .closed
  | stmts (.cons _ _), 0 => some (.body ctx.tyEnv ctx.inLoop)
  -- the statements after a `bindYield` read its answer; after every other head, nothing more
  | stmts (.cons (.bindYield e) _), 1 =>
    (effTy s ctx.tyEnv e).map fun t => .body (ctx.tyEnv ++ [t.answer]) ctx.inLoop
  | stmts (.cons _ _), 1 => some (.body ctx.tyEnv ctx.inLoop)
  | stmt (.bindYield _), 0 => some (.env ctx.tyEnv)
  | stmt (.yieldDiscard _), 0 => some (.env ctx.tyEnv)
  | stmt (.ifElse _ _ _), 0 => some (.body ctx.tyEnv ctx.inLoop)
  | stmt (.ifElse _ _ _), 1 => some (.body ctx.tyEnv ctx.inLoop)
  -- the body of a loop is typed in a loop
  | stmt (.whileTrue _), 0 => some (.body ctx.tyEnv true)
  | effs (.cons _ _), 0 => some (.env ctx.tyEnv)
  | effs (.cons _ _), 1 => some (.env ctx.tyEnv)
  | layers (.cons _ _), 0 => some .closed
  | layers (.cons _ _), 1 => some .closed
  | _, _ => none

/-- **The environment at an address**: the step folded along a path, from the environment of
the node at the root. It answers at every sort of node. It answers `none` where the path leaves
the program, or where a step reads a sibling that the checker refuses. It does not ask whether
the node at the address has a type. -/
def envAt (s : Signature Op) : NodeEnv → Node Op → List Nat → Option NodeEnv
  | ctx, _, [] => some ctx
  | ctx, n, i :: rest =>
    (n.child i).bind fun c => (n.childEnv s ctx i).bind fun ctx' => envAt s ctx' c rest

end Node

/-- **A focus**: what stands at an address of a program. It holds the sub-program, the types of
the variables that it can read, and its type there. -/
structure Focus (Op : Type) where
  /-- the sub-program at the address -/
  program : Eff Op
  /-- the environment that the rest of the program gives it -/
  env : TyEnv
  /-- its type in that environment, as the checker answers it -/
  ty : EffTy
deriving DecidableEq

/-- **The focus at an address of a program.** The sub-program at `path` in `p`, the environment
that `p` gives it from the environment `env0` of the root (`Node.envAt`), and its type there
(`effTy`). The answer is `none` in three cases: `path` is no address of a program; a step on the
way reads a sibling that the checker refuses; the sub-program itself has no type.

At the empty path the answer is the checker's own (`focusAt_nil`,
`Laws/Program/Typing/Focus.lean`). -/
def focusAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    Option (Focus Op) :=
  match (Node.eff p).at_ path, (Node.eff p).envAt s (.env env0) path with
  | some (.eff q), some (.env env) => (effTy s env q).map fun t => ⟨q, env, t⟩
  | _, _ => none

end Effect4.Program
