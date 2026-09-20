import Effect4.Api
import Effect4.Program.Fold

/-!
# The `Eff` corpus generator — packet P3 of the image-parser spike

Plan: `docs/research/2026-09-05-image-parser-spike.md` §2 (the corpus) and §7 (P3). This is
the seeded generator of `Eff NativeOp` programs the spike ran its parser over, moved out of
`Test/Program/Gen.lean` and into the tree, where it is the corpus every
printer and reader claim runs over. The workshop file is now a `--run` driver that imports
this module and writes the bytes; the generator itself lives here.

## What it generates

Every `Eff` constructor the printer accepts — everything but the five internal
fiber actions (`interruptScoped`, `awaitAllFailFast`, `snapshotChildren`, `awaitNewChildren`,
`setContext`), which `src/Effect4/Codegen/Print.lean` refuses by design. The coverage guard
below states that once, against the language's own description of itself (the derived shapes
and the generated fold), instead of once per constructor; the refused arms occur nowhere
because the generator has no arm that draws them, not because a seed happened to miss them.

## The seed stream

`pick` is the 64-bit LCG of the spike, taken modulo `2 ^ 63` with the low 16 bits dropped, and
program `i` at depth `d` is `(genEff 0 d).run ⟨1000003 * (i + 1) + 17⟩`. The arithmetic and the
*order* of the draws are the reproducibility contract: `Test/Program/Gen.lean`
originally reproduced the spike's 400 files byte for byte. The ingestion join adds
three program arms and a layer generator, producing a deliberately different corpus.
The seed formula remains unchanged; the per-program verdicts are the committed corpus index.

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

/-- `src/Effect4/Program/Native.lean` `nativeAtom`, name and arity. -/
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
is the asynchronous leaf arm's row. -/
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

/-- Free numeric service keys for the generated corpus; other carriers have explicit reader pins. -/
def genKey : M ServiceKey := do pure ⟨⟨4 + (← pick 8)⟩, ⟨4⟩⟩

/-- `count` layers one depth below, as a `mergeAll` spine. -/
def genLayers (prevLayer : M (LayerTerm NativeOp)) : Nat → M (LayerTerms NativeOp)
  | 0 => pure .nil
  | count + 1 => do
    let head ← prevLayer
    let tail ← genLayers prevLayer count
    pure (.cons head tail)

/-- One layer arm, with recursive generators already one depth below; the ninth draw (the
host rows slice) is a `mergeAll` of one to three layers. A `ref` is never drawn here: it
names a path of the whole program, which `refPass` chooses after the draw. -/
def genLayerStep (prev : Nat → M (Eff NativeOp)) (prevLayer : M (LayerTerm NativeOp)) :
    M (LayerTerm NativeOp) := do
  match ← pick 9 with
  | 0 => pure (.succeed (← genKey) (.nat (← pick 20)))
  | 1 => pure (.effect (← genKey) (← prev 0))
  | 2 => pure (.effectDiscard (← prev 0))
  | 3 => pure (.provide (← prevLayer) (← prevLayer))
  | 4 => pure (.provideMerge (← prevLayer) (← prevLayer))
  | 5 => pure (.merge (← prevLayer) (← prevLayer))
  | 6 => pure (.fresh (← prevLayer))
  | 7 => pure (.orDie (← prevLayer))
  | _ => pure (.mergeAll (← genLayers prevLayer (1 + (← pick 3))))

/-! ## Programs

`genEffLeaf` supplies the original eight leaf draws. `genEffStep` extends the
thirty-way table to 33 draws for the join, taking the depth-below generators as
parameters — `prev` for programs and `prevStmts` for generator bodies — so that it can serve
both `genEff` at `d+1` and `genStmts` at `d+1`, which needs exactly that program generator. -/

/-- The leaf arms, for a draw `k < 8`. -/
def genEffLeaf (n : Nat) : Nat → M (Eff NativeOp)
  | 0 => do pure (.succeed (← genTerm n 2))
  | 1 => do pure (.fail (← genTerm n 1))
  | 2 => do pure (.failCause (← genCause n 2))
  -- `fail` again: `yieldError` was drawn here until it retired into `fail` (the same draw)
  | 3 => do pure (.fail (← genTerm n 2))
  | 4 => do pure (.sync (← genTerm n 2))
  | 5 => do pure (.perform (← genOp) (← genTerm n 2))
  | 6 => do pure (.yieldNow (← pick 3))
  | _ => do
    match ← pick 3 with
    -- the asynchronous row, a `perform` like every other since `callback` retired (same draw)
    | 0 => pure (.perform .deferredAwait (← genTerm n 1))
    | 1 => pure (.withFiber .getId)
    | _ => pure (.withFiber .getContext)

/-- A program at depth `0`: a leaf, drawn from the eight leaf arms. -/
def genEff0 (n : Nat) : M (Eff NativeOp) := do genEffLeaf n (← pick 8)

/-- `count` race entrants from one program generator. -/
def effsOf (gen : Nat → M (Eff NativeOp)) (n : Nat) : Nat → M (Effs NativeOp)
  | 0 => pure .nil
  | k + 1 => do pure (.cons (← gen n) (← effsOf gen n k))

/-- A program at a positive depth: the 34-way arm table. `prev` is the program generator
one depth below and `prevStmts` the statement-list generator one depth below; `9 | 10 | 11`
and `22 | 23` weight `bind` and `fork` up, as the spike did. -/
def genEffStep (prev : Nat → M (Eff NativeOp)) (prevStmts : Nat → Nat → M (Stmts NativeOp))
    (prevLayer : M (LayerTerm NativeOp)) (n : Nat) : M (Eff NativeOp) := do
  let k ← pick 34
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
    -- the conditional: `select` under `.bool`, drawn as `branch` was (the same three draws)
    | 19 => pure (.select (← genTerm n 1) .bool (← prev n) (← prev n))
    -- the loop: `iterate` answering `unit`, drawn as `whileLoop` was (the same four draws);
    -- no annotation, so the cursor has its initial value's type (DI-91)
    | 20 =>
      pure (.iterate none (← genTerm n 1) (← genTerm (n + 1) 1) (← genTerm (n + 1) 1)
        (.lit .unit) (← prev (n + 1)))
    | 21 =>
      pure (.awaitFiber (← genTerm n 1) (if (← pick 2) == 0 then .awaitValue else .joinEffect))
    | 22 | 23 => pure (.withFiber (.fork (← prev n) (← genOpts)))
    -- a fork into a scope is a daemon at the pin (rc.112): the child form has no spelling and
    -- the printer refuses it, so the corpus draws the daemon form only
    | 24 => pure (.withFiber (.forkScoped (← prev n) { (← genOpts) with daemon := true }))
    | 25 => pure (.withFiber (.forkIn (← prev n) { (← genOpts) with daemon := true } (← genTerm n 1)))
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
    | 29 => pure (.acquireRelease (← prev n) (← prev (n + 2)))
    | 30 => pure (.provideLayer (← prevLayer) ((← pick 2) == 0) (← prev n))
    | 31 => pure (.service (← genKey))
    | 32 => pure (.provideService (← genKey) (← genTerm n 1) (← prev n))
    | _ => pure (.catchIf (← genTerm (n + 1) 1) (← prev n) (← prev (n + 1)))

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
  | d + 1 => genEffStep (fun m => genEff m d) (fun m count => genStmts m d count) (genLayer d) n

/-- A generator body of at most `count` statements over an environment of `n` variables,
nested at most `depth` deep. The program generator it draws from is the one at *its own*
depth, spelled as `genEffStep` over the depth-below generators — which is `genEff · (d+1)`. -/
def genStmts (n : Nat) : Nat → Nat → M (Stmts NativeOp)
  | 0, count => stmtsLeafLoop genEff0 n count
  | d + 1, count =>
    stmtsLoop (genEffStep (fun m => genEff m d) (fun m c => genStmts m d c) (genLayer d))
      (fun m c => genStmts m d c) n count

/-- A closed layer, with both layer and effect recursion decreasing the depth. -/
def genLayer : Nat → M (LayerTerm NativeOp)
  | 0 => do pure (.succeed (← genKey) (.nat (← pick 20)))
  | d + 1 => genLayerStep (fun n => genEff n d) (genLayer d)

end

/-- `count` race entrants at `depth`. -/
def genEffs (n depth count : Nat) : M (Effs NativeOp) :=
  effsOf (fun m => genEff m depth) n count

/-- The host rows slice: a layer reference drawn into a generated program by a post-pass,
since a reference names a path of the whole program and a structural draw has no tree in
hand. The first layer of the program (in program order) is the target and the first later
layer not inside it, if any, becomes `.ref` to it — so every drawn reference satisfies
`layerRefsWF` by construction (the target precedes the site and does not enclose it, and
is no reference itself), and the corpus reaches `LayerTerm.ref`. -/
def refPass (e : Eff NativeOp) : Eff NativeOp :=
  match e.layerPaths [] with
  | target :: rest =>
    match rest.find? (fun site => !Path.properPrefix target site) with
    | some site =>
      match (Node.eff e).replaceLayerAt site (.ref target) with
      | some (Node.eff e') => e'
      | _ => e
    | none => e
  | [] => e

/-- Program `i` of the corpus, at `depth`: the generator run from the seed the spike used,
then the reference pass. -/
def program (i depth : Nat) : Eff NativeOp :=
  refPass ((genEff 0 depth).run ⟨1000003 * (i + 1) + 17⟩).1

/-- The first `count` programs at `depth`. -/
def corpus (count depth : Nat) : List (Eff NativeOp) :=
  (List.range count).map (program · depth)

/-! ## The corpus -/

/-- The pinned corpus: `corpus 400 4`. -/
def sample : List (Eff NativeOp) := corpus 400 4

/-- Whether the printer answers syntax for a program. -/
def prints (e : Eff NativeOp) : Bool :=
  match Api.print e with
  | .ok _ => true
  | .error _ => false

/-! ## Coverage, read off the derived shapes

The corpus must draw every constructor the printer accepts and none it refuses. That is
stated against the language's own description of itself, not once per constructor: the
derived projection (`src/Effect4/Store/Domain/Derived/Program.lean`, the `EffC` block) gives every node its
constructor ordinal (`toValEff e` is `.ctor i _`) and every family its shape (`EffShape`,
`StmtShape`, `ActionTermShape`, `LayerTermShape`: one case per constructor in declaration
order), and the generated fold (`src/Effect4/Program/Fold.lean`, `foldMap_eff`) visits every
node of the mutual family. No arm of the language is spelled here, so a constructor added
upstream appears in its shape and is demanded of the corpus by the guard below with no edit
to this file, and a missing arm fails by name. -/

section Coverage
open Effect4.Store.ProgramGen.EffC (toValEff toValStmt toValActionTerm toValLayerTerm
  EffShape StmtShape ActionTermShape LayerTermShape)

/-- The wire tag of a node's canonical value. -/
def ordinal : Effect4.Store.Val → Option Nat
  | .ctor i _ => some i
  | _ => none

/-- A family with a wire tag: `("Eff", 7)` is `bind`. -/
abbrev Head := String × Nat

/-- Every head a program uses, through the fold and the projection. -/
def heads (e : Eff NativeOp) : List Head :=
  foldMap_eff [] (· ++ ·) e
    (f_eff := fun n => (ordinal (toValEff n)).toList.map ("Eff", ·))
    (f_stmt := fun n => (ordinal (toValStmt n)).toList.map ("Stmt", ·))
    (f_action := fun n => (ordinal (toValActionTerm n)).toList.map ("ActionTerm", ·))
    (f_layer := fun n => (ordinal (toValLayerTerm n)).toList.map ("LayerTerm", ·))

/-- The heads the corpus uses. -/
def covered : List Head := (sample.flatMap heads).eraseDups

/-- The cases of a derived sum, each as its head and its constructor name. -/
def casesOf (family : String) : Effect4.Store.Shape → List (Head × String)
  | .sum _ cases => cases.map fun (n, tag, _) => ((family, tag), n)
  | _ => []

/-- The five internal fiber actions the printer refuses (`src/Effect4/Codegen/Print.lean`). -/
def refusedActions : List String :=
  ["interruptScoped", "awaitAllFailFast", "snapshotChildren", "awaitNewChildren", "setContext"]

/-- Forms kept out of the round-trip corpus until R5 (`docs/research/2026-09-16-select-and-iterate-ready-packet.md` §1.8).
`select` left this list when `branch` retired into it: the corpus draws it under `.bool`, the
conditional the reader reads; its `.option` and `.tag` forms are still not drawn. -/
def pendingEffs : List String :=
  ["iterate"]

/-- Every case the printer accepts and the corpus currently draws. -/
def expected : List (Head × String) :=
  (casesOf "Eff" EffShape).filter (fun c => !pendingEffs.contains c.2) ++
    casesOf "Stmt" StmtShape ++
    (casesOf "ActionTerm" ActionTermShape).filter (fun c => !refusedActions.contains c.2) ++
    casesOf "LayerTerm" LayerTermShape

/-- The accepted cases the corpus never draws, as `family.constructor`. -/
def missing : List String :=
  (expected.filter fun c => !covered.contains c.1).map fun c => c.1.1 ++ "." ++ c.2

/-- The refused actions the corpus draws anyway. -/
def refusedDrawn : List String :=
  ((casesOf "ActionTerm" ActionTermShape).filter fun c =>
    refusedActions.contains c.2 && covered.contains c.1).map (·.2)

/-- The refused names that are not constructors of `ActionTerm`: a renamed arm cannot hide
behind the filter. -/
def refusedUnknown : List String :=
  refusedActions.filter fun n => !(casesOf "ActionTerm" ActionTermShape).any (·.2 == n)

/-- The pending names that are not constructors of `Eff`. -/
def pendingEffsUnknown : List String :=
  pendingEffs.filter fun n => !(casesOf "Eff" EffShape).any (·.2 == n)

/-- Whether some program node of the corpus satisfies `p`, through the fold. -/
def coversEff (p : Eff NativeOp → Bool) : Bool :=
  sample.any fun e => foldMap_eff false (· || ·) e (f_eff := p)

/-- Whether some fiber action of the corpus satisfies `p`, through the fold. -/
def coversAction (p : ActionTerm NativeOp → Bool) : Bool :=
  sample.any fun e => foldMap_eff false (· || ·) e (f_action := p)

end Coverage

/-! ## The pins

What is pinned states a property of the generator. The measured counts (how many programs
are well typed, the node totals) are not pinned here: the committed corpus index
(`generated/corpus-index.tsv`, one row per program with Lean's verdicts, cut by `make corpus`
and held by `make check-gen`) names the programs whose verdict changed, which is the report
DI-60 asks of a narrowing commit. -/

/-! ### Every constructor the printer accepts occurs, and none it refuses -/

#guard missing = []
#guard refusedDrawn = []
#guard refusedUnknown = []
#guard pendingEffsUnknown = []

/-! ### The printer refuses none of it; every drawn layer reference is well formed -/

#guard sample.all prints
#guard sample.all Eff.layerRefsWF

/-! ### Both values of the two enumerated fields that change a program's meaning -/

#guard coversEff (fun | .awaitFiber _ .awaitValue => true | _ => false)
#guard coversEff (fun | .awaitFiber _ .joinEffect => true | _ => false)
#guard coversAction (fun | .interruptAll _ none => true | _ => false)
#guard coversAction (fun | .interruptAll _ (some _) => true | _ => false)

end Test.Program.Gen
