import Effect4.Program.Binders
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.StoreExecution

/-!
# Source addresses and lexical lengths of native callbacks

Concept: store-typing R4, serving `HeapSites.heap_sites_keep` and QueueWorkers `Assertions.jobs_step`.
The predicate retains a source address and its exact generated binder level, without value typing.
A generator name uses its statement counter beneath its generator root.
The writer consumer checks the actual resolved Ref.modify operation against the source-site premise.
These local transports establish no whole-configuration preservation, cell aliases, custody or progress.
-/

set_option autoImplicit false

namespace Effect4.Program.SourceScope

open Effect4 Effect4.Machine Effect4.Program
/-- The lexical level of a source address, using the generated child and binder tables.
Consumer: `HeapSites.SitesKeep` and every scope transport below. -/
def levelAt : Node NativeOp → Nat → List Nat → Option Nat
  | _, n, [] => some n
  | node, n, i :: rest => (node.child i).bind fun c => levelAt c (node.childLevel n i) rest

/-- A source point has the lexical length of its addressed node. -/
def At (root : NativeEff) (p : Point) : Prop :=
  levelAt (.eff root) 0 p.path = some p.env.length

/-- A generator's effective source address includes its statement counter.
Its saved environment lacks the next answer exactly when the name binds that answer. -/
def GenAt (root : NativeEff) (p : Point) (pc : List Nat) (bind : Bool) : Prop :=
  levelAt (.eff root) 0 (p.path ++ [0] ++ pc) =
    some (p.env.length + if bind then 1 else 0)

/-- The existing address walk transports the existing binder walk along a suffix.
Consumer: the callback and iterator transports below. -/
theorem levelAt_suffix (node target : Node NativeOp) (path suffix : List Nat) (n : Nat)
    (found : Node.at_ node path = some target) :
    levelAt node n (path ++ suffix) =
      (levelAt node n path).bind (fun k => levelAt target k suffix) := by
  induction path generalizing node n with
  | nil =>
    cases Option.some.inj found
    rfl
  | cons i path ih =>
    simp only [Node.at_] at found
    cases hc : node.child i with
    | none => rw [hc] at found; cases found
    | some child =>
      rw [hc] at found
      simp only [Option.bind_some] at found
      simp only [List.cons_append, levelAt, hc, Option.bind_some]
      exact ih child (node.childLevel n i) found

/-- Resolution at a scoped point uses the source node at that point.
Consumer: `resolve_modify_keeps`. -/
theorem resolve_at (root : NativeEff) (p : Point) (e : NativeEff)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) :
    resolve root p = compileEff e p := by
  simp only [resolve, found]

/-- A bind callback resumes the actual second child with one new lexical value.
Consumer: queue wrapper continuations and `HeapSites.heap_sites_keep`. -/
theorem bind_contA (root : NativeEff) (p : Point) (first rest : NativeEff) (value : Val)
    (found : Node.at_ (.eff root) p.path = some (.eff (.bind first rest)))
    (hscope : At root p) :
    contAOf root (.cont p) value = compileEff rest (p.childWith 1 value) ∧
      At root (p.childWith 1 value) := by
  refine ⟨?_, ?_⟩
  · change resolve root (p.childWith 1 value) = _
    apply resolve_at
    exact Agreement.at_childWith found 1 value
  · unfold At at hscope ⊢
    change levelAt (.eff root) 0 (p.path ++ [1]) = some (p.env ++ [value]).length
    rw [levelAt_suffix _ _ p.path [1] 0 found, hscope]
    simp only [Option.bind_some, levelAt, Node.childLevel, Node.closedChild, Node.binders,
      List.length_append, List.length_singleton]
    rfl

/-- The release capture and its exit supply the acquire-release node's two lexical binders.
Consumer: `releaseBody_contA` and cleanup writer provenance. -/
theorem capture_release_scope (root : NativeEff) (p : Point) (acquire release : NativeEff)
    (value : Val) (ctx : Ctx) (exit : ExitV)
    (found : Node.at_ (.eff root) p.path = some (.eff (.acquireRelease acquire release)))
    (hs : At root p) :
    At root ((Point.ofCapture (p.capture value ctx)).childWith 1 (reifyExitVal exit)) := by
  unfold At at hs ⊢
  change levelAt (.eff root) 0 (p.path ++ [1]) =
    some ((p.env ++ [value]) ++ [reifyExitVal exit]).length
  rw [levelAt_suffix _ _ p.path [1] 0 found, hs]
  simp only [Option.bind_some, levelAt, Node.childLevel, Node.closedChild, Node.binders,
    List.length_append, List.length_singleton]
  rfl

/-- The actual release callback forwards the correctly scoped captured source to its masked body.
Consumer: cleanup writer provenance for Workers and QueueWorkers. -/
theorem releaseBody_contA (root : NativeEff) (p : Point) (acquire release : NativeEff)
    (value : Val) (ctx previous : Ctx) (exit : ExitV)
    (found : Node.at_ (.eff root) p.path = some (.eff (.acquireRelease acquire release)))
    (hs : At root p) :
    contAOf root (.releaseBody (Point.ofCapture (p.capture value ctx)) exit previous) Val.unit =
      .withFiber (.releaseMasked ((Point.ofCapture (p.capture value ctx)).childWith 1
        (reifyExitVal exit)) previous) ∧
    At root ((Point.ofCapture (p.capture value ctx)).childWith 1 (reifyExitVal exit)) :=
  ⟨rfl, capture_release_scope root p acquire release value ctx exit found hs⟩

/-- Calling a generator name supplies exactly the lexical length of its effective address.
Consumer: `SourceScope.gen_modify`. -/
theorem gen_env (root : NativeEff) (p : Point) (pc : List Nat) (bind : Bool) (value : Val)
    (hscope : GenAt root p pc bind) :
    levelAt (.eff root) 0 (p.path ++ [0] ++ pc) =
      some (if bind then p.env ++ [value] else p.env).length := by
  cases bind with
  | false => exact hscope
  | true =>
    simp only [GenAt, ↓reduceIte, List.length_append, List.length_singleton] at hscope ⊢
    exact hscope

/-- A yielding statement has the same lexical length as its yielded effect.
The advanced generator name retains the answer binder from the generated binder table.
Consumer: `gen_modify`. -/
theorem yield_scopes (root : NativeEff) (p : Point) (pc : List Nat) (env : List Val)
    (e : NativeEff) (rest : Stmts NativeOp) (bind : Bool) (fuel : Nat)
    (found : Node.at_ (.eff root) (p.path ++ [0] ++ pc) =
      some (.stmts (.cons (if bind then .bindYield e else .yieldDiscard e) rest)))
    (hs : levelAt (.eff root) 0 (p.path ++ [0] ++ pc) = some env.length) :
    At root { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 } ∧
      GenAt root { p with env := env } (pc ++ [1]) bind := by
  refine ⟨?_, ?_⟩
  · change levelAt (.eff root) 0 ((p.path ++ [0] ++ pc) ++ [0, 0]) = some env.length
    rw [levelAt_suffix _ _ (p.path ++ [0] ++ pc) [0, 0] 0 found, hs]
    cases bind <;> rfl
  · unfold GenAt
    change levelAt (.eff root) 0 (p.path ++ [0] ++ (pc ++ [1])) = _
    rw [← List.append_assoc, levelAt_suffix _ _ (p.path ++ [0] ++ pc) [1] 0 found, hs]
    cases bind <;> rfl

/-- An actual generator invocation emits a captured Ref.modify operation at its source address.
Its advanced callback retains the correct effective address and answer binder.
Consumer: Atomic and Queue iterator writers in their command preservation obligations. -/
theorem gen_modify (root : NativeEff) (p : Point) (pc : List Nat)
    (bind answerBind : Bool) (answer : Val) (term request : Term) (rest : Stmts NativeOp)
    (fuel : Nat) (q : RefKey)
    (found : Node.at_ (.eff root) (p.path ++ [0] ++ pc) =
      some (.stmts (.cons (if answerBind then .bindYield (.perform (.refModifyWith term) request)
        else .yieldDiscard (.perform (.refModifyWith term) request)) rest)))
    (hs : GenAt root p pc bind) (positive : p.fuel = fuel + 1)
    (reads : evalTerm (if bind then p.env ++ [answer] else p.env) request = some (.cell q)) :
    let env := if bind then p.env ++ [answer] else p.env
    (interpOf root).iterNext (.gen p pc bind) answer =
      ([], IterStep.resume (.sync (.op (.refModify q term env)))
        (.gen { p with env := env } (pc ++ [1]) answerBind)) ∧
      GenAt root { p with env := env } (pc ++ [1]) answerBind := by
  dsimp only
  have hs' := gen_env root p pc bind answer hs
  have hnext := (yield_scopes root p pc _ _ rest answerBind fuel found hs').2
  refine ⟨?_, hnext⟩
  change runStmts root p p.fuel pc (if bind then p.env ++ [answer] else p.env) [] = _
  conv => lhs; rw [positive, runStmts]
  have hb : blockAt root p pc =
      some (.cons (if answerBind then .bindYield (.perform (.refModifyWith term) request)
        else .yieldDiscard (.perform (.refModifyWith term) request)) rest) := by
    simp only [blockAt, found]
  rw [hb]
  have compile := StoreExecution.compile_modify term request
    { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := (if bind then p.env ++ [answer] else p.env), fuel := fuel + 1 }
    fuel q rfl reads
  cases answerBind with
  | false =>
    change runStmts.yieldOf root p (.perform (.refModifyWith term) request) false fuel pc
      (if bind then p.env ++ [answer] else p.env) [] = _
    rw [runStmts.yieldOf, compile]
  | true =>
    change runStmts.yieldOf root p (.perform (.refModifyWith term) request) true fuel pc
      (if bind then p.env ++ [answer] else p.env) [] = _
    rw [runStmts.yieldOf, compile]

end Effect4.Program.SourceScope
