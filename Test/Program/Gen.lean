import Effect4.Api

/-!
# The `Eff` corpus generator — packet P3 of the image-parser spike

Plan: `docs/research/2026-09-05-image-parser-spike.md` §2 (the corpus) and §7 (P3). This is
the seeded generator of `Eff NativeOp` programs the spike ran its parser over, moved out of
`workshop/ImageParser/GenImage.lean` and into the tree, where it is the corpus every
printer and reader claim runs over. The workshop file is now a `--run` driver that imports
this module and writes the bytes; the generator itself lives here.

## What it generates

Every `Eff` constructor the printer accepts — everything but `choose` and the five internal
fiber actions (`interruptScoped`, `awaitAllFailFast`, `snapshotChildren`, `awaitNewChildren`,
`setContext`), which `Effect4/Codegen/Print.lean` refuses by design. The coverage pins below
are one `#guard` per constructor of each family, plus two negative pins saying the refused
arms occur nowhere in the corpus — which is why the zero-refusal pin holds: the generator has
no arm that draws them, not one seed that happened to miss them.

## The seed stream

`pick` is the 64-bit LCG of the spike, taken modulo `2 ^ 63` with the low 16 bits dropped, and
program `i` at depth `d` is `(genEff 0 d).run ⟨1000003 * (i + 1) + 17⟩`. The arithmetic and the
*order* of the draws are the reproducibility contract: `workshop/ImageParser/GenImage.lean`
rendered from this module reproduces the spike's 400 files byte for byte, and any change to a
branch probability or to the sequence of `pick` calls inside an arm is a different corpus.

## Why the recursion is shaped the way it is

The spike's generator was recursive with no measure at all. Here the depth is the fuel and
every function is structural on it: `| 0 => …` draws only from the leaf arms, `| d+1 => …`
may recurse at `d`. Two of the spike's arms are loops on a *count* at a fixed depth — the
race entrants of `genEffs` and the statements of `genStmts` — and both call the program
generator at their own depth, which no single structural argument can express. They are
therefore written as `effsOf`, `stmtsLeafLoop` and `stmtsLoop`: ordinary structural loops on
the count that take the program generator as a parameter. `genStmts` at `d+1` passes
`genEffStep` applied to the depth-`d` generators, which is by definition `genEff · (d+1)`, so
the two agree without either calling the other at its own depth. Nothing here needs a
measure, an `Inhabited` instance, or a bang-index: `atoms` and `fns` are read with `getD`.

Every helper is structural and every pin is a `#guard`, so a pin is a finite probe of the
generator and nothing more (`AGENTS.md`). No helper touches a `String` beyond holding the
literals the syntax carries: the axiom gate holds `Test.*` at `propext`/`Quot.sound`, and
Lean's UTF-8 folds reach `Classical.choice`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.Gen

open Effect4 Effect4.Program

/-! ## The seed stream

The spike's LCG, unchanged: `s ↦ (s * 6364136223846793005 + 1442695040888963407) mod 2^63`,
answering `(s' / 65536) mod max n 1`. Dropping the low 16 bits is what makes the small moduli
below (`pick 2`, `pick 3`) usable at all. -/

/-- The generator's state: one 63-bit word. -/
structure G where
  s : Nat

/-- The generator monad. -/
abbrev M := StateM G

/-- Advance the stream and answer a draw in `[0, max n 1)`. -/
def pick (n : Nat) : M Nat := do
  let g ← get
  let s' := (g.s * 6364136223846793005 + 1442695040888963407) % (2 ^ 63)
  set (⟨s'⟩ : G)
  pure ((s' / 65536) % (max n 1))

/-! ## The alphabets

The pure atoms of the native route with their arities, and the read-modify-write function
names. Both are `getD`-read, so an out-of-range draw (which the moduli make impossible) is a
default rather than a panic. -/

/-- `Effect4/Program/Native.lean` `nativeAtom`, name and arity. -/
def atoms : List (String × Nat) :=
  [("succ", 1), ("pred", 1), ("isZero", 1), ("not", 1), ("add", 2), ("lt", 2), ("eq", 2),
   ("pair", 2), ("fst", 1), ("snd", 1)]

/-- `Effect4.Machine.FnName`, the pure functions a `Ref` row carries. -/
def fns : List Effect4.Machine.FnName :=
  [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-! ## Values -/

/-- `count` terms from one generator, in draw order. -/
def termsOf (gen : M Term) : Nat → M Terms
  | 0 => pure .nil
  | k + 1 => do
    let head ← gen
    let tail ← termsOf gen k
    pure (.cons head tail)

/-- The leaf arms of a term for a draw `k < 10`: a variable when the environment has one,
a literal otherwise. `none` is the draw that asks for an applied atom, which only a positive
depth can answer. -/
def termLeaf (n k : Nat) : M (Option Term) := do
  if k < 3 && n > 0 then pure (some (.var (← pick n)))
  else if k < 5 then pure (some (.lit (.nat (← pick 20))))
  else if k == 5 then pure (some (.lit .unit))
  else if k == 6 then pure (some (.lit (.bool ((← pick 2) == 0))))
  else if k == 7 then pure (some (.lit (.str "hi")))
  else pure none

/-- A term over an environment of `n` variables, nested at most `depth` deep. -/
def genTerm (n : Nat) : Nat → M Term
  | 0 => do
    match ← termLeaf n (← pick 10) with
    | some term => pure term
    | none => pure (.lit (.nat 1))
  | d + 1 => do
    match ← termLeaf n (← pick 10) with
    | some term => pure term
    | none => do
      let (atom, arity) := atoms.getD (← pick atoms.length) ("succ", 1)
      pure (.app atom (← termsOf (genTerm n d) arity))

/-- `Cause.interrupt`, with or without an interruptor. -/
def genInterrupt (n : Nat) : M CauseTerm := do
  if (← pick 2) == 0 then pure (.interrupt none)
  else pure (.interrupt (some (← genTerm n 1)))

/-- A cause over an environment of `n` variables; `both` needs a positive depth. -/
def genCause (n : Nat) : Nat → M CauseTerm
  | 0 => do
    match ← pick 3 with
    | 0 => pure (.fail (← genTerm n 1))
    | 1 => pure (.die (← genTerm n 1))
    | _ => genInterrupt n
  | d + 1 => do
    match ← pick 4 with
    | 0 => pure (.fail (← genTerm n 1))
    | 1 => pure (.die (← genTerm n 1))
    | 2 => genInterrupt n
    | _ => pure (.both (← genCause n d) (← genCause n d))

/-! ## Rows and options -/

/-- The fork options object: both flags and all three mask modes. -/
def genOpts : M Effect4.Supervision.ForkOptions := do
  let m ← pick 3
  pure ⟨(← pick 2) == 0, (← pick 2) == 0,
    if m == 0 then .interruptible else if m == 1 then .uninterruptible else .inherit⟩

/-- A native row: the thirteen `Ref` rows, the five `Deferred` rows the printer prints as
calls, and `Scope.make` at both finalizer strategies. `deferredAwait` is not drawn here — it
is the `callback` arm's row. -/
def genOp : M NativeOp := do
  match ← pick 20 with
  | 0 => pure .refMake
  | 1 => pure .refGet
  | 2 => pure .refSet
  | 3 => pure .refGetAndSet
  | 4 => pure .refSetAndGet
  | 5 => pure (.refUpdate (fns.getD (← pick 5) .incr))
  | 6 => pure (.refGetAndUpdate (fns.getD (← pick 5) .incr))
  | 7 => pure (.refUpdateAndGet (fns.getD (← pick 5) .incr))
  | 8 => pure (.refUpdateSome (fns.getD (← pick 5) .incr))
  | 9 => pure (.refGetAndUpdateSome (fns.getD (← pick 5) .incr))
  | 10 => pure (.refUpdateSomeAndGet (fns.getD (← pick 5) .incr))
  | 11 => pure (.refModify (fns.getD (← pick 5) .incr))
  | 12 => pure (.refModifySome (fns.getD (← pick 5) .incr))
  | 13 => pure .deferredMake
  | 14 => pure .deferredIsDone
  | 15 => pure .deferredPoll
  | 16 => pure .deferredSucceed
  | 17 => pure .deferredFail
  | 18 => pure (.scopeMake .sequential)
  | _ => pure (.scopeMake .parallel)

/-! ## Programs

`genEffLeaf` is the arm table for a draw `k < 8`: every constructor that carries no `Eff`
subterm. `genEffStep` is the arm table for `8 ≤ k < 30`, taking the depth-below generators as
parameters — `prev` for programs and `prevStmts` for generator bodies — so that it can serve
both `genEff` at `d+1` and `genStmts` at `d+1`, which needs exactly that program generator. -/

/-- The leaf arms, for a draw `k < 8`. -/
def genEffLeaf (n : Nat) : Nat → M (Eff NativeOp)
  | 0 => do pure (.succeed (← genTerm n 2))
  | 1 => do pure (.fail (← genTerm n 1))
  | 2 => do pure (.failCause (← genCause n 2))
  | 3 => do pure (.yieldError (← genTerm n 2))
  | 4 => do pure (.sync (← genTerm n 2))
  | 5 => do pure (.perform (← genOp) (← genTerm n 2))
  | 6 => do pure (.yieldNow (← pick 3))
  | _ => do
    match ← pick 3 with
    | 0 => pure (.callback .deferredAwait (← genTerm n 1))
    | 1 => pure (.withFiber .getId)
    | _ => pure (.withFiber .getContext)

/-- A program at depth `0`: a leaf, drawn from the eight leaf arms. -/
def genEff0 (n : Nat) : M (Eff NativeOp) := do genEffLeaf n (← pick 8)

/-- `count` race entrants from one program generator. -/
def effsOf (gen : Nat → M (Eff NativeOp)) (n : Nat) : Nat → M (Effs NativeOp)
  | 0 => pure .nil
  | k + 1 => do pure (.cons (← gen n) (← effsOf gen n k))

/-- A program at a positive depth: the thirty-way arm table. `prev` is the program generator
one depth below and `prevStmts` the statement-list generator one depth below; `9 | 10 | 11`
and `22 | 23` weight `bind` and `fork` up, as the spike did. -/
def genEffStep (prev : Nat → M (Eff NativeOp)) (prevStmts : Nat → Nat → M (Stmts NativeOp))
    (n : Nat) : M (Eff NativeOp) := do
  let k ← pick 30
  if k < 8 then
    genEffLeaf n k
  else
    match k with
    | 8 => pure (.suspend (← prev n))
    | 9 | 10 | 11 => pure (.bind (← prev n) (← prev (n + 1)))
    | 12 => pure (.gen (← prevStmts n (1 + (← pick 3))))
    | 13 => pure (.catchCause (← prev n) (← prev (n + 1)))
    | 14 => pure (.matchCause (← prev n) (← prev (n + 1)) (← prev (n + 1)))
    | 15 => pure (.onExit (← prev n) (← prev (n + 1)))
    | 16 => pure (.exit (← prev n))
    | 17 => pure (.uninterruptible (← prev n))
    | 18 => pure (.interruptible (← prev n))
    | 19 => pure (.branch (← genTerm n 1) (← prev n) (← prev n))
    | 20 =>
      pure (.whileLoop (← genTerm n 1) (← genTerm (n + 1) 1) (← genTerm (n + 1) 1)
        (← prev (n + 1)))
    | 21 =>
      pure (.awaitFiber (← genTerm n 1) (if (← pick 2) == 0 then .awaitValue else .joinEffect))
    | 22 | 23 => pure (.withFiber (.fork (← prev n) (← genOpts)))
    | 24 => pure (.withFiber (.forkScoped (← prev n) (← genOpts)))
    | 25 => pure (.withFiber (.forkIn (← prev n) (← genOpts) (← genTerm n 1)))
    | 26 =>
      match ← pick 6 with
      | 0 => pure (.withFiber (.runIn (← genTerm n 1) (← genTerm n 1)))
      | 1 => pure (.withFiber (.interrupt (← genTerm n 1)))
      | 2 => pure (.withFiber (.interruptAll (← genTerm n 1) none))
      | 3 => pure (.withFiber (.interruptAll (← genTerm n 1) (some (← genTerm n 1))))
      | 4 => pure (.withFiber (.awaitAll (← genTerm n 1)))
      | _ => pure (.withFiber (.closeScope (← genTerm n 1) (← genTerm n 1)))
    | 27 => pure (.withFiber (.raceAll (← effsOf prev n (1 + (← pick 3)))))
    | 28 => pure (.scoped (← prev n))
    | _ => pure (.acquireRelease (← prev n) (← prev (n + 2)))

/-- A generator body at depth `0`: only the three statement forms that need no nested block. -/
def stmtsLeafLoop (gen : Nat → M (Eff NativeOp)) (n : Nat) : Nat → M (Stmts NativeOp)
  | 0 => pure .nil
  | k + 1 => do
    match ← pick 3 with
    | 0 => pure (.cons (.bindYield (← gen n)) (← stmtsLeafLoop gen (n + 1) k))
    | 1 => pure (.cons (.yieldDiscard (← gen n)) (← stmtsLeafLoop gen n k))
    | _ => pure (.cons (.ret (← genTerm n 1)) .nil)

/-- A generator body at a positive depth: all six statement forms. `gen` is the program
generator at *this* depth and `sub` the statement-list generator one depth below, which is
where `ifElse` and `whileTrue` put their blocks. A `ret` ends the list. -/
def stmtsLoop (gen : Nat → M (Eff NativeOp)) (sub : Nat → Nat → M (Stmts NativeOp)) (n : Nat) :
    Nat → M (Stmts NativeOp)
  | 0 => pure .nil
  | k + 1 => do
    match ← pick 6 with
    | 0 => pure (.cons (.bindYield (← gen n)) (← stmtsLoop gen sub (n + 1) k))
    | 1 => pure (.cons (.yieldDiscard (← gen n)) (← stmtsLoop gen sub n k))
    | 2 => pure (.cons (.ret (← genTerm n 1)) .nil)
    | 3 =>
      pure (.cons (.ifElse (← genTerm n 1) (← sub n 1) (← sub n 1)) (← stmtsLoop gen sub n k))
    | 4 => pure (.cons (.whileTrue (← sub n 2)) (← stmtsLoop gen sub n k))
    | _ => pure (.cons .breakLoop (← stmtsLoop gen sub n k))

mutual

/-- A program over an environment of `n` variables, nested at most `depth` deep. -/
def genEff (n : Nat) : Nat → M (Eff NativeOp)
  | 0 => genEff0 n
  | d + 1 => genEffStep (fun m => genEff m d) (fun m count => genStmts m d count) n

/-- A generator body of at most `count` statements over an environment of `n` variables,
nested at most `depth` deep. The program generator it draws from is the one at *its own*
depth, spelled as `genEffStep` over the depth-below generators — which is `genEff · (d+1)`. -/
def genStmts (n : Nat) : Nat → Nat → M (Stmts NativeOp)
  | 0, count => stmtsLeafLoop genEff0 n count
  | d + 1, count =>
    stmtsLoop (genEffStep (fun m => genEff m d) (fun m c => genStmts m d c))
      (fun m c => genStmts m d c) n count

end

/-- `count` race entrants at `depth`. -/
def genEffs (n depth count : Nat) : M (Effs NativeOp) :=
  effsOf (fun m => genEff m depth) n count

/-- Program `i` of the corpus, at `depth`: the generator run from the seed the spike used. -/
def program (i depth : Nat) : Eff NativeOp :=
  ((genEff 0 depth).run ⟨1000003 * (i + 1) + 17⟩).1

/-- The first `count` programs at `depth`. -/
def corpus (count depth : Nat) : List (Eff NativeOp) :=
  (List.range count).map (program · depth)

/-! ## The structural walk the pins read

One walker over the whole mutual family, three node predicates: on programs, on statements,
and on fiber actions. `mentionsEff`, `mentionsStmt` and `mentionsAction` are the three ways a
pin asks it a question, and no pin reads a rendering. -/

mutual

/-- Whether any node of the program satisfies the predicate of its sort. -/
def walkEff (pe : Eff NativeOp → Bool) (ps : Stmt NativeOp → Bool)
    (pa : ActionTerm NativeOp → Bool) : Eff NativeOp → Bool
  | e@(.suspend body) => pe e || walkEff pe ps pa body
  | e@(.bind first rest) => pe e || walkEff pe ps pa first || walkEff pe ps pa rest
  | e@(.gen body) => pe e || walkStmts pe ps pa body
  | e@(.catchCause body handler) => pe e || walkEff pe ps pa body || walkEff pe ps pa handler
  | e@(.matchCause body onValue onCause) =>
    pe e || walkEff pe ps pa body || walkEff pe ps pa onValue || walkEff pe ps pa onCause
  | e@(.onExit body finalizer) => pe e || walkEff pe ps pa body || walkEff pe ps pa finalizer
  | e@(.exit body) => pe e || walkEff pe ps pa body
  | e@(.uninterruptible body) => pe e || walkEff pe ps pa body
  | e@(.interruptible body) => pe e || walkEff pe ps pa body
  | e@(.branch _ thenB elseB) => pe e || walkEff pe ps pa thenB || walkEff pe ps pa elseB
  | e@(.whileLoop _ _ _ body) => pe e || walkEff pe ps pa body
  | e@(.withFiber action) => pe e || walkAction pe ps pa action
  | e@(.scoped body) => pe e || walkEff pe ps pa body
  | e@(.acquireRelease acquire release) =>
    pe e || walkEff pe ps pa acquire || walkEff pe ps pa release
  | e@(.choose _ left right) => pe e || walkEff pe ps pa left || walkEff pe ps pa right
  | e => pe e

def walkStmts (pe : Eff NativeOp → Bool) (ps : Stmt NativeOp → Bool)
    (pa : ActionTerm NativeOp → Bool) : Stmts NativeOp → Bool
  | .nil => false
  | .cons head tail => walkStmt pe ps pa head || walkStmts pe ps pa tail

def walkStmt (pe : Eff NativeOp → Bool) (ps : Stmt NativeOp → Bool)
    (pa : ActionTerm NativeOp → Bool) : Stmt NativeOp → Bool
  | s@(.bindYield effect) => ps s || walkEff pe ps pa effect
  | s@(.yieldDiscard effect) => ps s || walkEff pe ps pa effect
  | s@(.ifElse _ thenB elseB) => ps s || walkStmts pe ps pa thenB || walkStmts pe ps pa elseB
  | s@(.whileTrue body) => ps s || walkStmts pe ps pa body
  | s => ps s

def walkEffs (pe : Eff NativeOp → Bool) (ps : Stmt NativeOp → Bool)
    (pa : ActionTerm NativeOp → Bool) : Effs NativeOp → Bool
  | .nil => false
  | .cons head tail => walkEff pe ps pa head || walkEffs pe ps pa tail

def walkAction (pe : Eff NativeOp → Bool) (ps : Stmt NativeOp → Bool)
    (pa : ActionTerm NativeOp → Bool) : ActionTerm NativeOp → Bool
  | a@(.fork body _) => pa a || walkEff pe ps pa body
  | a@(.forkIn body _ _) => pa a || walkEff pe ps pa body
  | a@(.forkScoped body _) => pa a || walkEff pe ps pa body
  | a@(.raceAll entrants) => pa a || walkEffs pe ps pa entrants
  | a => pa a

end

/-- Whether some program node satisfies `p`. -/
def mentionsEff (p : Eff NativeOp → Bool) (e : Eff NativeOp) : Bool :=
  walkEff p (fun _ => false) (fun _ => false) e

/-- Whether some statement node satisfies `p`. -/
def mentionsStmt (p : Stmt NativeOp → Bool) (e : Eff NativeOp) : Bool :=
  walkEff (fun _ => false) p (fun _ => false) e

/-- Whether some fiber action satisfies `p`. -/
def mentionsAction (p : ActionTerm NativeOp → Bool) (e : Eff NativeOp) : Bool :=
  walkEff (fun _ => false) (fun _ => false) p e

/-! ## Size, structurally

`nodes` counts `Eff` constructors, following the same family; `depth` is the longest chain of
them. Both are read only through `max` over the corpus, and both are the pins that say the
generator still makes programs of the shape the spike measured. -/

mutual

/-- The number of `Eff` nodes in a program. -/
def nodesEff : Eff NativeOp → Nat
  | .suspend body => 1 + nodesEff body
  | .bind first rest => 1 + nodesEff first + nodesEff rest
  | .gen body => 1 + nodesStmts body
  | .catchCause body handler => 1 + nodesEff body + nodesEff handler
  | .matchCause body onValue onCause =>
    1 + nodesEff body + nodesEff onValue + nodesEff onCause
  | .onExit body finalizer => 1 + nodesEff body + nodesEff finalizer
  | .exit body => 1 + nodesEff body
  | .uninterruptible body => 1 + nodesEff body
  | .interruptible body => 1 + nodesEff body
  | .branch _ thenB elseB => 1 + nodesEff thenB + nodesEff elseB
  | .whileLoop _ _ _ body => 1 + nodesEff body
  | .withFiber action => 1 + nodesAction action
  | .scoped body => 1 + nodesEff body
  | .acquireRelease acquire release => 1 + nodesEff acquire + nodesEff release
  | .choose _ left right => 1 + nodesEff left + nodesEff right
  | _ => 1

def nodesStmts : Stmts NativeOp → Nat
  | .nil => 0
  | .cons head tail => nodesStmt head + nodesStmts tail

def nodesStmt : Stmt NativeOp → Nat
  | .bindYield effect => nodesEff effect
  | .yieldDiscard effect => nodesEff effect
  | .ifElse _ thenB elseB => nodesStmts thenB + nodesStmts elseB
  | .whileTrue body => nodesStmts body
  | _ => 0

def nodesEffs : Effs NativeOp → Nat
  | .nil => 0
  | .cons head tail => nodesEff head + nodesEffs tail

def nodesAction : ActionTerm NativeOp → Nat
  | .fork body _ => nodesEff body
  | .forkIn body _ _ => nodesEff body
  | .forkScoped body _ => nodesEff body
  | .raceAll entrants => nodesEffs entrants
  | _ => 0

end

mutual

/-- The longest chain of `Eff` nodes in a program. -/
def depthEff : Eff NativeOp → Nat
  | .suspend body => 1 + depthEff body
  | .bind first rest => 1 + max (depthEff first) (depthEff rest)
  | .gen body => 1 + depthStmts body
  | .catchCause body handler => 1 + max (depthEff body) (depthEff handler)
  | .matchCause body onValue onCause =>
    1 + max (depthEff body) (max (depthEff onValue) (depthEff onCause))
  | .onExit body finalizer => 1 + max (depthEff body) (depthEff finalizer)
  | .exit body => 1 + depthEff body
  | .uninterruptible body => 1 + depthEff body
  | .interruptible body => 1 + depthEff body
  | .branch _ thenB elseB => 1 + max (depthEff thenB) (depthEff elseB)
  | .whileLoop _ _ _ body => 1 + depthEff body
  | .withFiber action => 1 + depthAction action
  | .scoped body => 1 + depthEff body
  | .acquireRelease acquire release => 1 + max (depthEff acquire) (depthEff release)
  | .choose _ left right => 1 + max (depthEff left) (depthEff right)
  | _ => 1

def depthStmts : Stmts NativeOp → Nat
  | .nil => 0
  | .cons head tail => max (depthStmt head) (depthStmts tail)

def depthStmt : Stmt NativeOp → Nat
  | .bindYield effect => depthEff effect
  | .yieldDiscard effect => depthEff effect
  | .ifElse _ thenB elseB => max (depthStmts thenB) (depthStmts elseB)
  | .whileTrue body => depthStmts body
  | _ => 0

def depthEffs : Effs NativeOp → Nat
  | .nil => 0
  | .cons head tail => max (depthEff head) (depthEffs tail)

def depthAction : ActionTerm NativeOp → Nat
  | .fork body _ => depthEff body
  | .forkIn body _ _ => depthEff body
  | .forkScoped body _ => depthEff body
  | .raceAll entrants => depthEffs entrants
  | _ => 0

end

/-! ## The pins

The corpus the spike measured: 400 programs at depth 4. Every pin below is a `#guard` over
`sample`, and every expected value is written out. -/

/-- The pinned corpus: `corpus 400 4`. -/
def sample : List (Eff NativeOp) := corpus 400 4

/-- Whether the printer answers syntax for a program. -/
def prints (e : Eff NativeOp) : Bool :=
  match Api.print e with
  | .ok _ => true
  | .error _ => false

/-- Whether some program of the corpus has a node satisfying `p`. -/
def coversEff (p : Eff NativeOp → Bool) : Bool := sample.any (mentionsEff p)

/-- Whether some program of the corpus has a statement satisfying `p`. -/
def coversStmt (p : Stmt NativeOp → Bool) : Bool := sample.any (mentionsStmt p)

/-- Whether some program of the corpus has a fiber action satisfying `p`. -/
def coversAction (p : ActionTerm NativeOp → Bool) : Bool := sample.any (mentionsAction p)

/-- The largest `Eff` node count over the corpus. -/
def maxNodes : Nat := sample.foldl (fun acc e => max acc (nodesEff e)) 0

/-- The largest `Eff` nesting over the corpus. -/
def maxDepth : Nat := sample.foldl (fun acc e => max acc (depthEff e)) 0

/-- The `Eff` nodes of the whole corpus. -/
def totalNodes : Nat := sample.foldl (fun acc e => acc + nodesEff e) 0

/-- How many of the corpus are well-typed against the native signature. Typing is irrelevant
to the syntax the spike measured; the count is pinned because it moves when the generator
does. -/
def wellTypedCount : Nat := (sample.filter Api.wellTyped).length

/-! ### The corpus is what it was -/

#guard sample.length = 400

/-! ### The printer refuses none of it -/

#guard sample.all prints

/-! ### The well-typed count -/

#guard wellTypedCount = 136

/-! ### Size -/

#guard maxNodes = 22
#guard maxDepth = 5
#guard totalNodes = 2032

/-! ### Every `Eff` constructor the printer accepts occurs -/

#guard coversEff (fun | .succeed _ => true | _ => false)
#guard coversEff (fun | .fail _ => true | _ => false)
#guard coversEff (fun | .failCause _ => true | _ => false)
#guard coversEff (fun | .yieldError _ => true | _ => false)
#guard coversEff (fun | .sync _ => true | _ => false)
#guard coversEff (fun | .suspend _ => true | _ => false)
#guard coversEff (fun | .perform _ _ => true | _ => false)
#guard coversEff (fun | .bind _ _ => true | _ => false)
#guard coversEff (fun | .gen _ => true | _ => false)
#guard coversEff (fun | .catchCause _ _ => true | _ => false)
#guard coversEff (fun | .matchCause _ _ _ => true | _ => false)
#guard coversEff (fun | .onExit _ _ => true | _ => false)
#guard coversEff (fun | .exit _ => true | _ => false)
#guard coversEff (fun | .uninterruptible _ => true | _ => false)
#guard coversEff (fun | .interruptible _ => true | _ => false)
#guard coversEff (fun | .branch _ _ _ => true | _ => false)
#guard coversEff (fun | .whileLoop _ _ _ _ => true | _ => false)
#guard coversEff (fun | .yieldNow _ => true | _ => false)
#guard coversEff (fun | .callback _ _ => true | _ => false)
#guard coversEff (fun | .awaitFiber _ _ => true | _ => false)
#guard coversEff (fun | .withFiber _ => true | _ => false)
#guard coversEff (fun | .scoped _ => true | _ => false)
#guard coversEff (fun | .acquireRelease _ _ => true | _ => false)

/-! The one constructor the printer refuses is the one the generator never draws. -/
#guard !coversEff (fun | .choose _ _ _ => true | _ => false)

/-! ### Both observer modes of `awaitFiber` -/

#guard coversEff (fun | .awaitFiber _ .awaitValue => true | _ => false)
#guard coversEff (fun | .awaitFiber _ .joinEffect => true | _ => false)

/-! ### Every `Stmt` form occurs -/

#guard coversStmt (fun | .bindYield _ => true | _ => false)
#guard coversStmt (fun | .yieldDiscard _ => true | _ => false)
#guard coversStmt (fun | .ret _ => true | _ => false)
#guard coversStmt (fun | .ifElse _ _ _ => true | _ => false)
#guard coversStmt (fun | .whileTrue _ => true | _ => false)
#guard coversStmt (fun | .breakLoop => true | _ => false)

/-! ### Every `ActionTerm` the printer accepts occurs -/

#guard coversAction (fun | .fork _ _ => true | _ => false)
#guard coversAction (fun | .forkIn _ _ _ => true | _ => false)
#guard coversAction (fun | .forkScoped _ _ => true | _ => false)
#guard coversAction (fun | .runIn _ _ => true | _ => false)
#guard coversAction (fun | .interrupt _ => true | _ => false)
#guard coversAction (fun | .interruptAll _ none => true | _ => false)
#guard coversAction (fun | .interruptAll _ (some _) => true | _ => false)
#guard coversAction (fun | .awaitAll _ => true | _ => false)
#guard coversAction (fun | .raceAll _ => true | _ => false)
#guard coversAction (fun | .getContext => true | _ => false)
#guard coversAction (fun | .getId => true | _ => false)
#guard coversAction (fun | .closeScope _ _ => true | _ => false)

/-! The five internal fiber actions the printer refuses never occur. -/
#guard !coversAction (fun
  | .interruptScoped _ => true
  | .awaitAllFailFast _ => true
  | .snapshotChildren => true
  | .awaitNewChildren _ => true
  | .setContext _ => true
  | _ => false)

end Test.Program.Gen
