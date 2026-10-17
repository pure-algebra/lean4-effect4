import Effect4.Run.Basic

/-!
# Run.Tree — a program's call tree at a budget, and how a host runs it

A sequential program means a tree of the calls it makes. Each call is a host row's request, or
a cell operation of the stores, and each answer selects the rest of the tree. A loop or a
definition that calls itself makes the tree infinite, so this module builds the tree **at a
budget** `k`: every loop invocation tests its condition at most `k` times, and calls of
definitions nest at most `k` deep. Where the budget ends, the tree has a `cut`. A cut is no exit
and no failure. It says only that the budget found no further answer.

Three facts make the budget usable as a test oracle. The Rocq development of
`docs/research/2026-10-16-itrees/` proves each one of its transcription of this tree.
`Effect4.Laws.Run.Tree` declares them here, as declared exceptions to the proof gates.

* **A larger budget only extends the tree** (`Tree.ofProgram_approx`). A cut may grow into more
  tree, and nothing else changes. So a finish or a wait found at one budget holds at every larger
  one.
* **Every end of the program's run is found at some budget.** A host run that finishes or
  waits on a call has a budget that shows that end (`adequacyD` in Rocq).
* **Divergence is a cut at every budget.** A run that no budget settles is the interaction
  tree `ITree.spin` of the meaning, and conversely (`divergesD_iff` in Rocq). A cut at one
  budget is only a finite probe: `settle` reports it as unsettled, never as divergent.

The tree's arms are `Laws/Program/DenoteRowsB.lean`'s `denoteRowsB` arms. Beside them it has
the definition arms of `rocq/BudgetDefs.v`: `call`, `param`, `invoke`, the root's definition
block, `provideContext` and the `context` read. A program outside these arms, such as a fork, a
scope, a service or a layer, answers `outsideExit`. `covers` decides the fragment before a run,
so a caller can send such a program to the machine instead.

The context is the machine's own (`Machine.Ctx`): the root's is `emptyCtx`, a `context` read
answers its image (`Val.context`, `getContext`), and `provideContext` merges the provided
services over the current ones for its body (`Env.ContextUpdate.provide`, `Ctx.withServices`,
as `Compile.updateContextAt` updates a fiber). The Rocq transcription keeps the context as an
opaque value; the context is a parameter of the tree that adds no node, so the facts about the
tree's shape hold of either.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program

/-- **The call tree of a program at a budget.** -/
inductive Tree where
  /-- The program ended with this exit. -/
  | done (exit : ExitV)
  /-- The budget ended here: a loop's tests, or the depth of the definitions' calls. -/
  | cut
  /-- A host row's call: the row's position in the table and the request. The reply's exit
  resumes the tree. -/
  | call (row : Nat) (request : Val) (resume : ExitV → Tree)
  /-- A cell operation of the stores. The value it answers resumes the tree. -/
  | cell (op : SyncOp) (resume : Val → Tree)

namespace Tree

/-! ## Sequencing -/

/-- Run `t`, then `k` on its exit. A cut stays a cut (`Denote.thenOpt`). -/
def bind : Tree → (ExitV → Tree) → Tree
  | done ex, k => k ex
  | cut, _ => cut
  | call i v resume, k => call i v fun a => bind (resume a) k
  | cell o resume, k => cell o fun a => bind (resume a) k

/-- Run `t`, then `k` on its value. A failure ends the sequence with itself (`Denote.seqRows`). -/
def andThen (t : Tree) (k : Val → Tree) : Tree :=
  t.bind fun
    | .success v => k v
    | .failure c => done (.failure c)

/-! ## The exits the tree writes -/

/-- `Compile.badShape` as an exit: a term that does not evaluate, or a value of the wrong
shape (`Denote.badShapeExit`). -/
def badShapeExit : ExitV := Exit.failure (Cause.die Defect.badName)

/-- A form outside the tree's arms (`Denote.outsideExit`). -/
def outsideExit : ExitV := Exit.failure (Cause.die Defect.notImplemented)

/-- A term's value as an exit, or `badShapeExit`. -/
def valueExit (env : List Val) (t : Term) : ExitV :=
  match evalTerm env t with
  | some v => .success v
  | none => badShapeExit

/-- A finalizer's exit as `Exit.restoreAfterFinalizer` reads it (`Denote.finVoid`). -/
def finVoid : ExitV → VoidExitV
  | .success _ => Exit.void
  | .failure c => .failure c

/-! ## One loop round -/

/-- A loop at the cursor `c`, with `n` tests left (`Denote.iter` over `Denote.loopStep`). The
test runs first: true runs the body and steps the cursor, false answers the result. With no
test left, the tree is cut. -/
def loop (body : List Val → Tree) (env : List Val) (test step result : Term) : Nat → Val → Tree
  | 0, _ => cut
  | n + 1, c =>
    match evalTerm (env ++ [c]) test with
    | some (Val.bool true) =>
      (body (env ++ [c])).bind fun
        | .failure cause => done (.failure cause)
        | .success a =>
          match evalTerm (env ++ [c, a]) step with
          | some c' => loop body env test step result n c'
          | none => done badShapeExit
    | some (Val.bool false) => done (valueExit (env ++ [c]) result)
    | _ => done badShapeExit

/-! ## The tree of a program -/

/-- A frame of the parameters' stack: the programs an invocation passed, and the environment of
the invocation, where they run (`ArgSite`). -/
structure Frame where
  /-- the programs the invocation passed, by parameter -/
  args : List NativeEff
  /-- the invocation's environment -/
  env : List Val

/-- What runs a definition's body or a parameter's program one level of unfolding deeper. -/
abbrev Unfold := NativeEff → List Val → List Frame → Ctx → Tree

/-- The definition bodies of a program's root block (`defBodyPath`); none outside a block. -/
def bodiesOf : NativeEff → List NativeEff
  | .defs _ bodies _ _ => bodies.toList
  | _ => []

/-- **One level of the tree** (`rocq/BudgetDefs.v`, `denoteW`). Each arm is `denoteRowsB`'s at
the loop budget `k`, and a call, an invocation and a parameter's run go to `unfold`. A call runs
the definition's body at the request alone with an empty frame pushed. An invocation pushes the
programs it passes with its own environment. A parameter's run takes the innermost frame's
program at that frame's environment and the request, at the stack below the frame. -/
def level (table : RowTable) (bodies : List NativeEff) (k : Nat) (unfold : Unfold) :
    NativeEff → List Val → List Frame → Ctx → Tree
  | .succeed v, env, _, _ => done (valueExit env v)
  | .fail e, env, _, _ =>
    done (match evalTerm env e with
      | some x => .failure (Cause.fail (errOf x))
      | none => badShapeExit)
  | .failCause c, env, _, _ =>
    done (match causeOf env c with
      | some cause => .failure cause
      | none => badShapeExit)
  | .sync t, env, _, _ => done (.success ((evalTerm env t).getD Val.unit))
  | .suspend b, env, ps, ctx => level table bodies k unfold b env ps ctx
  | .perform op r, env, ps, ctx =>
    match evalTerm env r with
    | none => done badShapeExit
    | some v =>
      match op with
      | .external i => if i < table.length then call i v done else done outsideExit
      | .call d =>
        match bodies[d]? with
        | some body => unfold body [v] (⟨[], []⟩ :: ps) ctx
        | none => done badShapeExit
      | .param j =>
        match ps with
        | frame :: below =>
          match frame.args[j]? with
          | some arg => unfold arg (frame.env ++ [v]) below ctx
          | none => done badShapeExit
        | [] => done badShapeExit
      | _ =>
        match (NativeOp.row op).kind with
        | .sync =>
          match NativeOp.syncOpOf op env v with
          | some o => cell o fun w => done (.success w)
          | none => done badShapeExit
        | _ => done outsideExit
  | .bind a b, env, ps, ctx =>
    (level table bodies k unfold a env ps ctx).andThen fun v =>
      level table bodies k unfold b (env ++ [v]) ps ctx
  | .select t d a b, env, ps, ctx =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => level table bodies k unfold a (env ++ bound.toList) ps ctx
    | some (false, bound) => level table bodies k unfold b (env ++ bound.toList) ps ctx
    | none => done badShapeExit
  | .exit b, env, ps, ctx =>
    (level table bodies k unfold b env ps ctx).bind fun ex => done (.success (reifyExitVal ex))
  | .catchCause b h, env, ps, ctx =>
    (level table bodies k unfold b env ps ctx).bind fun
      | .success v => done (.success v)
      | .failure c => level table bodies k unfold h (env ++ [Val.exitErr c]) ps ctx
  | .catchIf test b h, env, ps, ctx =>
    (level table bodies k unfold b env ps ctx).bind fun
      | .success v => done (.success v)
      | .failure cause =>
        match caughtErrorValue? env test cause with
        | some value => level table bodies k unfold h (env ++ [value]) ps ctx
        | none => done (.failure cause)
  | .matchCause b v c, env, ps, ctx =>
    (level table bodies k unfold b env ps ctx).bind fun
      | .success x => level table bodies k unfold v (env ++ [x]) ps ctx
      | .failure cause => level table bodies k unfold c (env ++ [Val.exitErr cause]) ps ctx
  | .onExit b f, env, ps, ctx =>
    (level table bodies k unfold b env ps ctx).bind fun ex =>
      (level table bodies k unfold f (env ++ [reifyExitVal ex]) ps ctx).bind fun fex =>
        done (Exit.restoreAfterFinalizer ex (finVoid fex))
  | .iterate _ initial test step result body, env, ps, ctx =>
    match evalTerm env initial with
    | some c₀ => loop (fun env' => level table bodies k unfold body env' ps ctx) env test step
        result k c₀
    | none => done badShapeExit
  | .provideContext t b, env, ps, ctx =>
    match (evalTerm env t).bind Val.context? with
    | some built =>
      level table bodies k unfold b env ps
        (Ctx.withServices ((Env.ContextUpdate.provide built.services).apply ctx.services))
    | none => done badShapeExit
  | .withFiber (.context _), _, _, ctx => done (.success (Val.context ctx))
  | .defs _ _ main _, env, ps, ctx => level table bodies k unfold main env ps ctx
  | .invoke d r args, env, ps, ctx =>
    match evalTerm env r, bodies[d]? with
    | some v, some body => unfold body [v] (⟨args.toList, env⟩ :: ps) ctx
    | _, _ => done badShapeExit
  | _, _, _, _ => done outsideExit

/-- **The tree with calls unfolded `depth` levels deep** (`rocq/BudgetDefs.v`, `denoteD`). At
depth zero a call, an invocation and a parameter's run are cut. -/
def unfolded (table : RowTable) (bodies : List NativeEff) (k : Nat) : Nat → Unfold
  | 0 => fun _ _ _ _ => cut
  | d + 1 => level table bodies k (unfolded table bodies k d)

/-- **The tree of a program at the budget `k`**: loops at `k` tests, calls `k` deep, from the
empty environment and stack, under the root's context (`emptyCtx`; `rocq/BudgetDefs.v`,
`denoteBD`). -/
def ofProgram (table : RowTable) (k : Nat) (main : NativeEff) : Tree :=
  level table (bodiesOf main) k (unfolded table (bodiesOf main) k k) main [] [] emptyCtx

/-! ## The fragment -/

/-- Whether one node is one of the tree's arms, read off its head alone. -/
def armOf : NativeEff → Bool
  | .succeed _ | .fail _ | .failCause _ | .sync _ | .suspend _ | .exit _ => true
  | .perform op _ =>
    match op with
    | .external _ | .call _ | .param _ => true
    | _ => (NativeOp.row op).kind == .sync
  | .bind _ _ | .catchCause _ _ | .catchIf _ _ _ | .onExit _ _ | .matchCause _ _ _ => true
  | .select _ _ _ _ | .iterate _ _ _ _ _ _ | .provideContext _ _ => true
  | .withFiber (.context _) => true
  | .defs _ _ _ _ | .invoke _ _ _ => true
  | _ => false

/-- **The first node outside the tree's arms**, by its address in program order, or `none` when
every node is an arm (a fold of the program, `foldMapAt_eff`). A program outside the arms runs on
the machine (`Run.runWith`); its tree would answer `outsideExit` at that node. -/
def outsideAt (program : NativeEff) : Option (List Nat) :=
  foldMapAt_eff none (fun a b => a <|> b) [] program fun node path =>
    if armOf node then none else some path

/-- Whether every node of the program is one of the tree's arms. -/
def covers (program : NativeEff) : Bool := (outsideAt program).isNone

/-! ## Running a tree under a host -/

/-- **A host of the tree**: a row's reply to a request, from the host's own state, as the exit
it gives the program. `none` leaves the call waiting: a frontier, never a failure (`AGENTS.md`). -/
abbrev Host (σ : Type) := Nat → Val → σ → Option (ExitV × σ)

namespace Host

/-- The host that answers no call: every row waits. -/
def silent : Host Unit := fun _ _ _ => none

/-- **A reply tape**: each call takes the tape's next exit, whatever its row; an empty tape
waits (`Denote.tapeHandler`). -/
def tape : Host (List ExitV) := fun _ _ tape =>
  match tape with
  | [] => none
  | ex :: rest => some (ex, rest)

/-- **A reactor as a host** (`Run.Reactor`, so `Reactor.method`, `Reactor.fallible` and
`Reactor.first` serve here unchanged). The reactor reads the row's record from the table; an
answer that is no exit is declined, and the call waits. -/
def ofReactor {σ : Type} (table : RowTable) (r : Reactor σ) : Host σ := fun i v st =>
  match table[i]? with
  | some row =>
    match r row v st with
    | some (.ofExit ex, st') => some (ex, st')
    | _ => none
  | none => none

end Host

/-- One step of a run: a host call with the exit its reply gave, or a cell operation with the
value it answered. -/
inductive Step where
  | called (row : Nat) (request : Val) (answer : ExitV)
  | celled (op : SyncOp) (answer : Val)

/-- **How a run stops**: the program finished, the budget cut it, or a call waits on the host. -/
inductive Stop where
  | finished (exit : ExitV)
  | cut
  | waiting (row : Nat) (request : Val)

/-- Whether the budget cut the run. -/
def Stop.isCut : Stop → Bool
  | .cut => true
  | _ => false

/-- **A run of a tree**: its steps in order, how it stopped, the stores and the host's state it
left. -/
structure Outcome (σ : Type) where
  steps : List Step
  stop : Stop
  stores : Stores
  state : σ

/-- **The run of a tree under a host**, from the stores `s` and the host state `st`. Each call
asks the host; a cell operation steps the stores (`syncOpStep`, with the machine's fallback on
`none`, as `Denote.storeHandler`). `acc` holds the steps so far, the latest first. -/
def runFrom {σ : Type} (host : Host σ) : Tree → Stores → σ → List Step → Outcome σ
  | done ex, s, st, acc => ⟨acc.reverse, .finished ex, s, st⟩
  | cut, s, st, acc => ⟨acc.reverse, .cut, s, st⟩
  | call i v resume, s, st, acc =>
    match host i v st with
    | some (a, st') => runFrom host (resume a) s st' (.called i v a :: acc)
    | none => ⟨acc.reverse, .waiting i v, s, st⟩
  | cell o resume, s, st, acc =>
    match syncOpStep o s with
    | some (s', w) => runFrom host (resume w) s' st (.celled o w :: acc)
    | none => runFrom host (resume Val.unit) s st (.celled o Val.unit :: acc)

/-- The run of a tree from the empty stores. -/
def run {σ : Type} (host : Host σ) (t : Tree) (state : σ) : Outcome σ :=
  t.runFrom host Stores.empty state []

/-! ## Probing a program at budgets -/

/-- **The run of a program at the budget `k`** under a host. -/
def probe {σ : Type} (table : RowTable) (k : Nat) (host : Host σ) (state : σ)
    (program : NativeEff) : Outcome σ :=
  (Tree.ofProgram table k program).run host state

/-- Whether the run at the budget `k` is cut. -/
def cutAt {σ : Type} (table : RowTable) (host : Host σ) (state : σ) (program : NativeEff)
    (k : Nat) : Bool :=
  (probe table k host state program).stop.isCut

/-- The least budget in `(lo, hi]` whose run is not cut, given that `hi`'s is not, by bisection.
`gas` bounds the halvings; `hi + 1` is more than enough, since each one halves the gap. -/
def bisect (cut : Nat → Bool) (lo hi : Nat) : (gas : Nat) → Nat
  | 0 => hi
  | gas + 1 =>
    if hi ≤ lo + 1 then hi
    else
      let mid := (lo + hi) / 2
      if cut mid then bisect cut mid hi gas else bisect cut lo mid gas

/-- A budget up to `limit` whose run is not cut, by doubling from `k` (with `lo` the last cut
budget) and then bisecting; `none` when the run at `limit` is cut too. -/
def gallop (cut : Nat → Bool) (limit lo k : Nat) : (gas : Nat) → Option Nat
  | 0 => none
  | gas + 1 =>
    let k' := min k limit
    if !cut k' then some (bisect cut lo k' (k' + 1))
    else if k' == limit then none
    else gallop cut limit k' (2 * k) gas

/-- **The least budget up to `limit` whose run is not cut**, with that run. `none` when the run is
cut at the budget `limit`: a finite probe, never a divergence.

The search doubles the budget until a run is not cut, then bisects: about `2 log limit` probes,
not `limit`. Bisection finds the least such budget because a larger budget only extends the tree
(`ofProgram_approx`), so the budgets whose run is cut are an initial segment. The
answer is checked: it is the probe at the budget it names, and that probe is not cut
(`settle_sound`, which needs no fact about the search). -/
def settle {σ : Type} (table : RowTable) (limit : Nat) (host : Host σ) (state : σ)
    (program : NativeEff) : Option (Nat × Outcome σ) :=
  let cut := cutAt table host state program
  let found := if !cut 0 then some 0 else gallop cut limit 0 1 (limit + 1)
  match found with
  | none => none
  | some k =>
    let o := probe table k host state program
    if o.stop.isCut then none else some (k, o)

/-- **The frames of a run**: its run at each budget from `0` to `limit`. A frame never takes back
a step of the one before (`ofProgram_approx`), so a view can play them as one growing run. -/
def frames {σ : Type} (table : RowTable) (limit : Nat) (host : Host σ) (state : σ)
    (program : NativeEff) : List (Outcome σ) :=
  (List.range (limit + 1)).map fun k => probe table k host state program

end Tree

end Effect4.Run
