import Effect4.Semantics.Denotation
import Effect4.Target.TypeScript.ScriptFlow

/-!
# Target.TypeScript.ScriptDenotation

Owner: the meaning of the straight-line script embedding (packet D5 of
`docs/research/2026-09-03-reification-plan.md`).

`Effect4/Target/TypeScript/ScriptFlow.lean` embeds a `Script` into a Flow v2
graph. `Effect4/Semantics/Denotation.lean` gives an admitted flow an algebraic
meaning. Until this module nothing related the two: the embedding was checked
by running it (`harness/trace/Generate.lean oracle`), never by a theorem. Here
the script gets a *direct* denotation — the program the script says, read off
the steps and not off the graph — and `Script.toFlow_denote` says the graph's
denotation is that program.

Three facts shape the statements.

* **The table is a parameter.** `tableAlphabet id table` has `Op = Fin
  table.length`, and the embedding mints table rows as it goes, so the
  operations of the denotation are positions in the *final* table. `denoteScript`
  therefore takes that table; `Script.toFlow` is what produces it.
* **The denotation is `Option`-valued.** `Script.toFlow` refuses operations of
  two or more parameters, atoms of the wrong arity, and unknown names, and
  `denoteScript` refuses exactly the same scripts. The theorem relates the two
  `some` cases.
* **The two sides sit in different signatures.** A script performs only its own
  alphabet, so `denoteScript` lands in `Sig`, while a flow denotation lands in
  `FullSig = Sig ⊕ₛ DecSig` and returns a `RunResult` with the unconsumed tape.
  `liftScript` is the (injective, decision-free) embedding between them: a
  straight-line run announces no decision, never touches the tape, and ends
  `done`.

Nothing here renders. The module is String-free in the sense that matters to
the axiom gate: it declares no `Repr`, no rendering, and reaches nothing beyond
`propext` and `Quot.sound`. `String` still appears as the *code* type of the
flow alphabet, which is what `ScriptFlow` already fixed.
-/

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow
open Effects.Trace (Val)

/-! ## Leaves of a program

The walk of a script segment returns an environment, and the next segment reads
that environment. `Leaves` is the only thing needed about the returned value: a
predicate that holds at every leaf, and the congruence that lets a continuation
be rewritten under a `bind`. -/

/-- Every `pure` leaf of a program satisfies `p`. -/
inductive Leaves {S : Signature.{0, 0}} {A : Type} (p : A → Prop) : Program S A → Prop where
  | pure {value : A} : p value → Leaves p (.pure value)
  | vis {operation : S.Op} {next : S.Answer operation → Program S A} :
      (∀ answer, Leaves p (next answer)) → Leaves p (.vis operation next)

namespace Leaves

variable {S : Signature.{0, 0}} {A B : Type} {p : A → Prop}

/-- Leaves compose along a bind. -/
theorem bind {q : B → Prop} {f : A → Program S B} :
    ∀ {program : Program S A}, Leaves p program →
      (∀ value, p value → Leaves q (f value)) → Leaves q (program.bind f)
  | .pure _, .pure holds, step => step _ holds
  | .vis _ _, .vis rest, step => .vis fun answer => bind (rest answer) step

/-- A continuation may be rewritten under a bind wherever the leaves allow it. -/
theorem bind_congr {f g : A → Program S B} :
    ∀ {program : Program S A}, Leaves p program →
      (∀ value, p value → f value = g value) → program.bind f = program.bind g
  | .pure _, .pure holds, agree => agree _ holds
  | .vis operation _, .vis rest, agree =>
      congrArg (Program.vis operation) (funext fun answer => bind_congr (rest answer) agree)

end Leaves

/-! ## The direct denotation of a script -/

/-- The static half of the embedding state: the binders of the open block, and
how many table rows have been minted. It is `Build` with the two fields the
denotation needs and nothing else (`Build.scope` and `Build.table.length`). -/
structure ScriptScope where
  binders : List (String × String)
  cursor : Nat

namespace ScriptScope

/-- `Build.lookupVar`, on the static state. -/
def lookupVar (scope : ScriptScope) (name : String) : Option (Var × String) :=
  match scope.binders.findIdx? (fun entry => entry.1 == name) with
  | some index =>
      match scope.binders[index]? with
      | some entry => some (⟨index⟩, entry.2)
      | none => none
  | none => none

end ScriptScope

/-- The static state of a `Build`. -/
def Build.scriptScope (b : Build) : ScriptScope := ⟨b.scope, b.table.length⟩

/-- What one segment of a script does to the environment: it performs the
segment's operations and returns the environment they extended. Every block of
the embedded graph passes its whole scope forward, so an environment *is* the
scope's values and a performed answer is one more of them. -/
abbrev Walk (id : AlphabetId) (table : List OpSpec) :=
  Env → Program (Sig (tableAlphabet id table)) Env

/-- The empty walk: a variable is already in scope. -/
def Walk.id' {id : AlphabetId} {table : List OpSpec} : Walk id table := fun env => .pure env

/-- Perform the table row at `index` on the parameter `request`, appending the
answer to the environment. `none` when the position is off the end of the
table, which the `Build` invariant rules out; the `env` arm of the `match` is
unreachable for the same reason. -/
def performWalk (id : AlphabetId) (table : List OpSpec) (index : Nat) (request : Var) :
    Option (Walk id table) :=
  ((tableAlphabet id table).lookup ⟨index⟩).map fun op env =>
    match env[request.index]? with
    | some value => .vis ⟨op, value⟩ fun answer : Val => .pure (env ++ [answer])
    | none => .pure env

/-- Perform an operation the table already carries, binding its answer as one
more parameter. Mirrors `Build.performTo`. -/
def performAt (id : AlphabetId) (table : List OpSpec) (scope : ScriptScope)
    (index : Nat) (request : Var) (binder ty : String) :
    Option (ScriptScope × Var × Walk id table) :=
  (performWalk id table index request).map fun walk =>
    ({ scope with binders := scope.binders ++ [(binder, ty)] }, ⟨scope.binders.length⟩, walk)

/-- Mint one table row and perform it. Mirrors `Build.addOp` then
`Build.performTo`. -/
def mintAt (id : AlphabetId) (table : List OpSpec) (scope : ScriptScope)
    (request : Var) (binder ty : String) : Option (ScriptScope × Var × Walk id table) :=
  (performWalk id table scope.cursor request).map fun walk =>
    ({ binders := scope.binders ++ [(binder, ty)], cursor := scope.cursor + 1 },
      ⟨scope.binders.length⟩, walk)

/-- A literal is a pure operation on the input parameter. Mirrors
`Build.literal`. -/
def literalWalk (id : AlphabetId) (table : List OpSpec) (scope : ScriptScope) (ty : String) :
    Option (ScriptScope × Var × Walk id table) :=
  mintAt id table scope ⟨0⟩ "" ty

/-- The walk of a pure term. Clause for clause `materialize`, with a program in
place of a block list. -/
def matWalk (atoms : AtomTable) (id : AlphabetId) (table : List OpSpec) :
    Nat → ScriptScope → PureTerm → Option (ScriptScope × Var × Walk id table)
  | 0, _, _ => none
  | _, scope, .var name => (scope.lookupVar name).map fun (v, _) => (scope, v, Walk.id')
  | _, scope, .nat _ => literalWalk id table scope "number"
  | _, scope, .str _ => literalWalk id table scope "string"
  | fuel + 1, scope, .app atom [arg] => do
      let (scope, v, walk) ← matWalk atoms id table fuel scope arg
      let (_, _, answerTy) ← atoms.find? (·.1 == atom)
      let (scope, v', walk') ← mintAt id table scope v "" answerTy
      some (scope, v', fun env => (walk env).bind walk')
  | _, _, .app _ _ => none

/-- The walk of one `perform` step. Mirrors `embedStep`'s `perform` arm. -/
def stepWalk (rows : ServiceRow) (atoms : AtomTable) (id : AlphabetId) (table : List OpSpec)
    (scope : ScriptScope) (bind : Option String) (op : String) (args : List PureTerm) :
    Option (ScriptScope × Walk id table) := do
  let row ← rows.row? op
  let index ← familyIndex rows op
  let (scope, request, walk) ←
    match args with
    | [] => literalWalk id table scope "void"
    | [arg] => matWalk atoms id table 16 scope arg
    | _ => none
  let (scope, _, walk') ← performAt id table scope index request (bind.getD "") row.tsAnswer
  some (scope, fun env => (walk env).bind walk')

/-- The walk of the remaining steps of a script. A `ret` ends it and every
later step is unreachable, exactly as in the embedded graph; a script with no
`ret` denotes nothing, and its embedding has no terminator. -/
def stepsWalk (rows : ServiceRow) (atoms : AtomTable) (id : AlphabetId) (table : List OpSpec) :
    List Step → ScriptScope → Option (Env → Program (Sig (tableAlphabet id table)) Val)
  | [], _ => none
  | .ret value :: _, scope => do
      let (_, v, walk) ← matWalk atoms id table 16 scope value
      some fun env => (walk env).bind fun env =>
        match env[v.index]? with
        | some result => .pure result
        | none => .pure .unit
  | .perform bind op args :: rest, scope => do
      let (scope, walk) ← stepWalk rows atoms id table scope bind op args
      let continue_ ← stepsWalk rows atoms id table rest scope
      some fun env => (walk env).bind continue_

/-- The direct denotation of a straight-line script: the program its steps say,
over the table its embedding mints. -/
def denoteScript (id : AlphabetId) (rows : ServiceRow) (atoms : AtomTable)
    (table : List OpSpec) (script : Script) (input : Val) :
    Option (Program (Sig (tableAlphabet id table)) Val) :=
  (stepsWalk rows atoms id table script.steps
    { binders := [script.param], cursor := (familyTable rows).length }).map (· [input])

/-- A script's program read as a flow denotation. A straight-line run announces
no decision, so the whole program sits in the left summand; it never reads the
tape, so the tape comes back untouched; and it always returns, so the result is
`done`. -/
def liftScript {Ty : Type} {alphabet : FlowAlphabet Ty}
    (program : Program (Sig alphabet) Val) : Program (FullSig alphabet) (RunResult × Tape) :=
  (Program.inl program).bind fun value => .pure (.done value, [])

/-! ## A pure operation erases

The lemma D5 owes about `interpret`: an operation whose handler is `pure`
contributes nothing to the interpretation but its answer. It is what makes the
literal and atom rows of the embedded table invisible to a handler that answers
them purely, and it is stated for any lawful monad. -/

/-- A pure operation erases: interpreting a `vis` whose handler answers `v`
purely is interpreting the continuation at `v`. -/
theorem interpret_vis_of_pure {S : Signature.{u, 0}} {M : Type → Type} [Monad M] [LawfulMonad M]
    {A : Type} (handler : Handler S M) (operation : S.Op) (value : S.Answer operation)
    (next : S.Answer operation → Program S A)
    (isPure : handler.handle operation = pure value) :
    interpret handler (.vis operation next) = interpret handler (next value) := by
  show handler.handle operation >>= (fun answer => interpret handler (next answer)) = _
  rw [isPure, pure_bind]

/-- Every literal and atom row of an embedded table is answered purely by
`tableService`, so `interpret_vis_of_pure` applies to it. -/
theorem tableService_handle_pure {M : Type → Type} [Monad M] (id : AlphabetId)
    (table : List OpSpec) (family : String → Val → M Val) (atom : String → Val → Val)
    (op : Fin table.length) (request : Val)
    (notFamily : (OpSpec.at table op).kind ≠ .family) :
    (tableService id table family atom).handle op request =
      pure (match (OpSpec.at table op).kind with
        | .lit value => value
        | _ => atom (OpSpec.at table op).name request) := by
  show (match (OpSpec.at table op).kind with
    | .lit value => pure value
    | .atom => pure (atom (OpSpec.at table op).name request)
    | .family => family (OpSpec.at table op).name request) = _
  cases kind : (OpSpec.at table op).kind with
  | family => exact absurd kind notFamily
  | atom => simp
  | lit value => simp


/-! ## Reading the embedded graph

Two facts about the shape `Script.toFlow` produces, proved once: a block list
whose ids run `0, 1, 2, …` resolves positionally, and a block that passes its
whole scope forward reads back exactly the environment it was given. -/

/-- Blocks minted in order: block `i` carries the id `⟨i⟩`. -/
def Ordered (blocks : List (RawBlock String)) : Prop :=
  ∀ i, (h : i < blocks.length) → blocks[i].id = ⟨i⟩

private theorem find?_ordered :
    ∀ (blocks : List (RawBlock String)) (offset i : Nat),
      (∀ j, (h : j < blocks.length) → blocks[j].id = ⟨j + offset⟩) →
      (h : i < blocks.length) →
      blocks.find? (fun block => block.id = ⟨i + offset⟩) = some blocks[i]
  | [], _, _, _, h => absurd h (by simp)
  | block :: rest, offset, 0, ids, _ => by
      have head : block.id = ⟨0 + offset⟩ := ids 0 (by simp)
      simp [List.find?, head]
  | block :: rest, offset, i + 1, ids, h => by
      have head : block.id = ⟨0 + offset⟩ := ids 0 (by simp)
      have index : i + 1 + offset = i + (offset + 1) := by omega
      have miss : decide (block.id = (⟨i + (offset + 1)⟩ : BlockId)) = false := by
        refine decide_eq_false ?_
        rw [head]
        intro eq
        have value : 0 + offset = i + (offset + 1) := congrArg BlockId.value eq
        omega
      have shifted : ∀ j, (hj : j < rest.length) → rest[j].id = ⟨j + (offset + 1)⟩ := by
        intro j hj
        have base := ids (j + 1) (by simpa using Nat.succ_lt_succ hj)
        rw [List.getElem_cons_succ] at base
        have same : j + 1 + offset = j + (offset + 1) := by omega
        rw [same] at base
        exact base
      have tail := find?_ordered rest (offset + 1) i shifted (by simpa using Nat.lt_of_succ_lt_succ h)
      rw [index]
      simp only [List.find?, miss, List.getElem_cons_succ]
      exact tail

/-- An ordered block list resolves positionally. -/
theorem lookupBlock_ordered {raw : RawFlow String} (ordered : Ordered raw.blocks)
    {i : Nat} (h : i < raw.blocks.length) :
    lookupBlock raw ⟨i⟩ = some raw.blocks[i] := by
  have := find?_ordered raw.blocks 0 i (by intro j hj; simpa using ordered j hj) h
  simpa [lookupBlock] using this

private theorem readArgs_range' (env : Env) :
    ∀ (count start : Nat), start + count = env.length →
      readArgs env ((List.range' start count).map Var.mk) = some (env.drop start)
  | 0, start, sized => by
      have : env.length ≤ start := by omega
      simp [List.range', readArgs, List.drop_eq_nil_of_le this]
  | count + 1, start, sized => by
      have bound : start < env.length := by omega
      have tail := readArgs_range' env count (start + 1) (by omega)
      simp only [List.range', List.map_cons, readArgs, tail, List.getElem?_eq_getElem bound]
      rw [List.drop_eq_getElem_cons bound]

/-- A block that passes its whole scope forward reads back the environment it
was given. -/
theorem readArgs_allVars (env : Env) :
    readArgs env ((List.range env.length).map Var.mk) = some env := by
  have := readArgs_range' env env.length 0 (by omega)
  simpa [List.range_eq_range'] using this

/-! ## Segments

A segment is the denotation of one straight stretch of the embedded graph: it
performs the operations of a walk and hands the extended environment to the
next block. Segments compose, and every clause of the embedding contributes
one. -/

/-- Leaves survive the left injection. -/
theorem Leaves.inl {S T : Signature.{0, 0}} {A : Type} {p : A → Prop} :
    ∀ {program : Program S A}, Leaves p program → Leaves p (Program.inl (T := T) program)
  | .pure _, .pure holds => .pure holds
  | .vis _ _, .vis rest => .vis fun answer => Leaves.inl (rest answer)

/-- One straight segment of the embedded graph: started at block `source` with
an environment of `before` values, the run performs exactly the operations of
`walk` and continues at block `target` with the environment `walk` returns,
which holds `after` values. -/
structure Segment {id : AlphabetId} {table : List OpSpec} (raw : RawFlow String)
    (cycles : CyclesWF raw) (source target before after : Nat) (walk : Walk id table) : Prop where
  sized : ∀ env : Env, env.length = before →
    Leaves (fun env' => env'.length = after) (walk env)
  denote : ∀ env : Env, env.length = before →
    denoteGo (alphabet := tableAlphabet id table) raw cycles ⟨source⟩ env [] =
      (Program.inl (walk env)).bind fun env' =>
        denoteGo (alphabet := tableAlphabet id table) raw cycles ⟨target⟩ env' []

namespace Segment

variable {id : AlphabetId} {table : List OpSpec} {raw : RawFlow String} {cycles : CyclesWF raw}

/-- The empty segment: a variable already in scope performs nothing. -/
theorem refl (source before : Nat) :
    Segment (id := id) (table := table) raw cycles source source before before Walk.id' where
  sized := fun _ sized => .pure sized
  denote := fun _ _ => rfl

/-- Segments compose. -/
theorem trans {source middle target before through after : Nat}
    {first second : Walk id table}
    (left : Segment raw cycles source middle before through first)
    (right : Segment raw cycles middle target through after second) :
    Segment raw cycles source target before after (fun env => (first env).bind second) where
  sized := fun env sized => Leaves.bind (left.sized env sized) fun value holds =>
    right.sized value holds
  denote := fun env sized => by
    rw [left.denote env sized]
    rw [Leaves.bind_congr (Leaves.inl (left.sized env sized))
      (fun value holds => right.denote value holds)]
    rw [← Program.bind_assoc, ← Program.inl_bind]

end Segment

/-! ## The block the embedding mints -/

private theorem getElem?_of_append_prefix {α : Type} {l final : List α} {x : α} {n : Nat}
    (pre : l ++ [x] <+: final) (len : l.length = n) : final[n]? = some x := by
  obtain ⟨rest, eq⟩ := pre
  subst eq
  subst len
  simp

/-- An ordered block list resolves positionally, read off `getElem?`. -/
theorem lookupBlock_at {raw : RawFlow String} (ordered : Ordered raw.blocks)
    {i : Nat} {block : RawBlock String} (position : raw.blocks[i]? = some block) :
    lookupBlock raw ⟨i⟩ = some block := by
  have bound : i < raw.blocks.length := by
    rcases Nat.lt_or_ge i raw.blocks.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at position
      exact absurd position (by simp)
  rw [List.getElem?_eq_getElem bound] at position
  rw [lookupBlock_ordered ordered bound]
  exact congrArg some (Option.some.inj position)

/-- A table position resolves exactly when it is a row of the table. -/
theorem tableAlphabet_lookup_iff {id : AlphabetId} {table : List OpSpec} {index : Nat}
    {op : (tableAlphabet id table).Op} :
    (tableAlphabet id table).lookup ⟨index⟩ = some op ↔ ∃ h : index < table.length, op = ⟨index, h⟩ := by
  constructor
  · intro eq
    by_cases h : index < table.length
    · refine ⟨h, ?_⟩
      rw [show ((tableAlphabet id table).lookup ⟨index⟩ : Option (Fin table.length))
        = some ⟨index, h⟩ from dif_pos h] at eq
      exact (Option.some.inj eq).symm
    · rw [show ((tableAlphabet id table).lookup ⟨index⟩ : Option (Fin table.length))
        = none from dif_neg h] at eq
      exact absurd eq (by simp)
  · rintro ⟨h, rfl⟩
    exact dif_pos h

private theorem plan_perform_allVars {id : AlphabetId} {table : List OpSpec}
    {block : RawBlock String} {index : Nat} {request : Var} {target : BlockId} {env : Env}
    (term : block.term = .perform ⟨index⟩ request target ((List.range env.length).map Var.mk))
    (bound : index < table.length) (inScope : request.index < env.length) (tape : Tape) :
    plan (tableAlphabet id table) block env tape =
      .perform ⟨index, bound⟩ (env[request.index]'inScope) target env := by
  simp only [plan, term, List.getElem?_eq_getElem inScope, readArgs_allVars]
  rw [dif_pos bound]

private theorem plan_ret_var {id : AlphabetId} {table : List OpSpec}
    {block : RawBlock String} {v : Var} {env : Env}
    (term : block.term = .ret v) (inScope : v.index < env.length) (tape : Tape) :
    plan (tableAlphabet id table) block env tape = .ret (env[v.index]'inScope) := by
  simp only [plan, term, List.getElem?_eq_getElem inScope]

/-- The block `Build.performTo` mints. -/
def mintedBlock (b : Build) (index : Nat) (request : Var) : RawBlock String :=
  { id := ⟨b.next⟩, params := b.params
    term := RawTerm.perform ⟨index⟩ request ⟨b.next + 1⟩ b.allVars }

/-- The block `embedStep` mints for a `ret`. -/
def retBlock (b : Build) (v : Var) : RawBlock String :=
  { id := ⟨b.next⟩, params := b.params, term := RawTerm.ret v }

theorem performTo_blocks (b : Build) (index : Nat) (request : Var) (binder answerTy : String) :
    (b.performTo index request binder answerTy).blocks =
      b.blocks ++ [mintedBlock b index request] := rfl

/-- The segment of one `Build.performTo`: the block it mints performs the named
table row on `request`, and hands the whole scope plus the answer forward. -/
theorem performTo_segment {id : AlphabetId} {raw : RawFlow String} {cycles : CyclesWF raw}
    {final : Build} (blocksEq : raw.blocks = final.blocks) (ordered : Ordered raw.blocks)
    {b : Build} {index : Nat} {request : Var} {binder answerTy : String}
    (counted : b.blocks.length = b.next)
    (minted : (b.performTo index request binder answerTy).blocks <+: final.blocks)
    (inScope : request.index < b.scope.length)
    {walk : Walk id final.table}
    (walkEq : performWalk id final.table index request = some walk) :
    Segment raw cycles b.next (b.next + 1) b.scope.length (b.scope.length + 1) walk := by
  obtain ⟨op, lookupEq, walkDef⟩ := Option.map_eq_some_iff.mp walkEq
  obtain ⟨bound, rfl⟩ := tableAlphabet_lookup_iff.mp lookupEq
  have shape : ∀ (env : Env) (h : request.index < env.length),
      walk env = .vis ⟨⟨index, bound⟩, env[request.index]⟩
        (fun answer : Val => .pure (env ++ [answer])) := by
    intro env h
    rw [← walkDef]
    simp only [List.getElem?_eq_getElem h]
  have found : lookupBlock raw ⟨b.next⟩ = some (mintedBlock b index request) :=
    lookupBlock_at ordered (getElem?_of_append_prefix (l := b.blocks)
      (blocksEq ▸ (performTo_blocks b index request binder answerTy) ▸ minted) counted)
  refine ⟨fun env sized => ?_, fun env sized => ?_⟩
  · have h : request.index < env.length := by omega
    rw [shape env h]
    exact .vis fun answer => .pure (by simp [sized])
  · have h : request.index < env.length := by omega
    have term : (mintedBlock b index request).term
        = .perform ⟨index⟩ request ⟨b.next + 1⟩ ((List.range env.length).map Var.mk) := by
      simp [mintedBlock, Build.allVars, sized]
    rw [denoteGo_eq (alphabet := tableAlphabet id final.table) cycles found env []]
    rw [plan_perform_allVars (id := id) (table := final.table) term bound h []]
    rw [shape env h]
    rfl

/-- The last block: a `ret` ends the run with the parameter it names. -/
theorem ret_denote {id : AlphabetId} {raw : RawFlow String} {cycles : CyclesWF raw}
    {final : Build} (blocksEq : raw.blocks = final.blocks) (ordered : Ordered raw.blocks)
    {b : Build} {v : Var} (counted : b.blocks.length = b.next)
    (minted : (b.blocks ++ [retBlock b v]) <+: final.blocks)
    {env : Env} (inScope : v.index < env.length) :
    denoteGo (alphabet := tableAlphabet id final.table) raw cycles ⟨b.next⟩ env [] =
      liftScript (match env[v.index]? with
        | some result => (.pure result : Program (Sig (tableAlphabet id final.table)) Val)
        | none => .pure .unit) := by
  have found : lookupBlock raw ⟨b.next⟩ = some (retBlock b v) :=
    lookupBlock_at ordered
      (getElem?_of_append_prefix (l := b.blocks) (blocksEq ▸ minted) counted)
  rw [denoteGo_eq (alphabet := tableAlphabet id final.table) cycles found env []]
  rw [plan_ret_var (id := id) (table := final.table) (block := retBlock b v) rfl inScope []]
  simp only [List.getElem?_eq_getElem inScope]
  rfl

/-! ## The embedding only appends

`Appends` is the growth half of the `Build` invariant: every clause of
`materialize` and `embedStep` extends the block list, the table and the scope,
and keeps `next` counting the blocks. -/

/-- What every clause of the embedding does to a `Build`. -/
structure Appends (b b' : Build) : Prop where
  blocks : b.blocks <+: b'.blocks
  table : b.table <+: b'.table
  scope : b.scope <+: b'.scope
  counted : b.blocks.length = b.next → b'.blocks.length = b'.next
  ordered : b.blocks.length = b.next → Ordered b.blocks → Ordered b'.blocks

namespace Appends

theorem rfl' (b : Build) : Appends b b :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, _root_.id, fun _ o => o⟩

theorem trans {a b c : Build} (first : Appends a b) (second : Appends b c) : Appends a c :=
  ⟨first.blocks.trans second.blocks, first.table.trans second.table,
    first.scope.trans second.scope, fun h => second.counted (first.counted h),
    fun h o => second.ordered (first.counted h) (first.ordered h o)⟩

end Appends

/-- Appending a block with the next id keeps the list ordered. -/
theorem ordered_append_one {blocks : List (RawBlock String)} {block : RawBlock String}
    (ordered : Ordered blocks) (identity : block.id = ⟨blocks.length⟩) :
    Ordered (blocks ++ [block]) := by
  intro i h
  rw [List.length_append, List.length_cons, List.length_nil] at h
  rcases Nat.lt_or_ge i blocks.length with hi | hi
  · rw [List.getElem_append_left hi]
    exact ordered i hi
  · have same : i = blocks.length := by omega
    subst same
    rw [List.getElem_append_right (Nat.le_refl _)]
    simpa using identity

theorem addOp_appends (b : Build) (spec : OpSpec) : Appends b (b.addOp spec).1 :=
  ⟨List.prefix_refl _, ⟨[spec], rfl⟩, List.prefix_refl _, _root_.id, fun _ o => o⟩

theorem performTo_appends (b : Build) (index : Nat) (request : Var) (binder answerTy : String) :
    Appends b (b.performTo index request binder answerTy) := by
  refine ⟨⟨[mintedBlock b index request], rfl⟩, List.prefix_refl _,
    ⟨[(binder, answerTy)], rfl⟩, fun h => ?_, fun h o => ?_⟩
  · show (b.blocks ++ [mintedBlock b index request]).length = b.next + 1
    simp [h]
  · exact ordered_append_one o (by simp [h])

theorem literal_appends (b : Build) (value : Val) (ty : String) :
    Appends b (b.literal value ty).1 :=
  (addOp_appends b _).trans (performTo_appends _ _ _ _ _)

/-- The `app` clause of `materialize`, as a plain `Option` bind. -/
theorem materialize_app_eq (atoms : AtomTable) (fuel : Nat) (b : Build) (atom : String)
    (arg : PureTerm) :
    materialize atoms (fuel + 1) b (.app atom [arg]) =
      (materialize atoms fuel b arg).bind fun r =>
        (atoms.find? (·.1 == atom)).bind fun a =>
          some (((r.1.addOp
              { name := atom, kind := .atom, requestTy := a.2.1, answerTy := a.2.2 }).1.performTo
                (r.1.addOp
                  { name := atom, kind := .atom, requestTy := a.2.1, answerTy := a.2.2 }).2
                r.2.1 "" a.2.2),
            ((r.1.addOp
              { name := atom, kind := .atom, requestTy := a.2.1, answerTy := a.2.2 }).1.performTo
                (r.1.addOp
                  { name := atom, kind := .atom, requestTy := a.2.1, answerTy := a.2.2 }).2
                r.2.1 "" a.2.2).last,
            a.2.2) := rfl

/-- The nullary `perform` clause of `embedStep`, as a plain `Option` bind. -/
theorem embedStep_perform_nil_eq (rows : ServiceRow) (atoms : AtomTable) (b : Build)
    (bind : Option String) (op : String) :
    embedStep rows atoms b (.perform bind op []) =
      (rows.row? op).bind fun row =>
        (familyIndex rows op).bind fun index =>
          some ((b.literal Val.unit "void").1.performTo index (b.literal Val.unit "void").2.1
            (bind.getD "") row.tsAnswer) := rfl

/-- The unary `perform` clause of `embedStep`, as a plain `Option` bind. -/
theorem embedStep_perform_one_eq (rows : ServiceRow) (atoms : AtomTable) (b : Build)
    (bind : Option String) (op : String) (arg : PureTerm) :
    embedStep rows atoms b (.perform bind op [arg]) =
      (rows.row? op).bind fun row =>
        (familyIndex rows op).bind fun index =>
          (materialize atoms 16 b arg).bind fun r =>
            some (r.1.performTo index r.2.1 (bind.getD "") row.tsAnswer) := rfl

/-- Two or more parameters are refused. -/
theorem embedStep_perform_many_eq (rows : ServiceRow) (atoms : AtomTable) (b : Build)
    (bind : Option String) (op : String) (first second : PureTerm) (rest : List PureTerm) :
    embedStep rows atoms b (.perform bind op (first :: second :: rest)) =
      (rows.row? op).bind fun _row =>
        (familyIndex rows op).bind fun _ => (none : Option Build) := rfl

/-- The `ret` clause of `embedStep`, as a plain `Option` bind. -/
theorem embedStep_ret_eq (rows : ServiceRow) (atoms : AtomTable) (b : Build) (value : PureTerm) :
    embedStep rows atoms b (.ret value) =
      (materialize atoms 16 b value).bind fun r =>
        some { r.1 with blocks := r.1.blocks ++ [retBlock r.1 r.2.1], next := r.1.next + 1 } := rfl

theorem materialize_appends (atoms : AtomTable) :
    ∀ (fuel : Nat) (term : PureTerm) (b b' : Build) (v : Var) (ty : String),
      materialize atoms fuel b term = some (b', v, ty) → Appends b b' := by
  intro fuel
  induction fuel with
  | zero => intro term b b' v ty embedded; simp [materialize] at embedded
  | succ fuel ih =>
      intro term
      match term with
      | .var name =>
          intro b b' v ty embedded
          simp only [materialize, Option.map_eq_some_iff] at embedded
          obtain ⟨entry, _, eq⟩ := embedded
          have : b' = b := congrArg Prod.fst eq.symm
          exact this ▸ Appends.rfl' b
      | .nat n =>
          intro b b' v ty embedded
          simp only [materialize, Option.some.injEq] at embedded
          have : b' = (b.literal (.nat n) "number").1 := congrArg Prod.fst embedded.symm
          exact this ▸ literal_appends b _ _
      | .str value =>
          intro b b' v ty embedded
          simp only [materialize, Option.some.injEq] at embedded
          have : b' = (b.literal (.str value) "string").1 := congrArg Prod.fst embedded.symm
          exact this ▸ literal_appends b _ _
      | .app atom [] =>
          intro b b' v ty embedded; simp [materialize] at embedded
      | .app atom (arg :: rest :: more) =>
          intro b b' v ty embedded; simp [materialize] at embedded
      | .app atom [arg] =>
          intro b b' v ty embedded
          rw [materialize_app_eq] at embedded
          obtain ⟨⟨b1, v1, ty1⟩, first, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          obtain ⟨⟨_, requestTy, answerTy⟩, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          have step := ih arg b b1 v1 ty1 first
          have : b' = ((b1.addOp _).1).performTo (b1.addOp _).2 v1 "" answerTy :=
            congrArg Prod.fst (Option.some.inj embedded).symm
          exact this ▸ step.trans ((addOp_appends b1 _).trans (performTo_appends _ _ _ _ _))

theorem embedStep_appends (rows : ServiceRow) (atoms : AtomTable) (b : Build) :
    ∀ (step : Step) (b' : Build), embedStep rows atoms b step = some b' → Appends b b'
  | .perform bind op args, b', embedded => by
      match args, embedded with
      | [], embedded =>
          rw [embedStep_perform_nil_eq] at embedded
          obtain ⟨row, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          obtain ⟨index, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          have : b' = (b.literal Val.unit "void").1.performTo index
              (b.literal Val.unit "void").2.1 (bind.getD "") row.tsAnswer :=
            (Option.some.inj embedded).symm
          exact this ▸ (literal_appends b _ _).trans (performTo_appends _ _ _ _ _)
      | [arg], embedded =>
          rw [embedStep_perform_one_eq] at embedded
          obtain ⟨row, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          obtain ⟨index, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          obtain ⟨⟨b1, request, ty1⟩, first, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          have grows := materialize_appends atoms 16 arg b b1 request ty1 first
          have : b' = b1.performTo index request (bind.getD "") row.tsAnswer :=
            (Option.some.inj embedded).symm
          exact this ▸ grows.trans (performTo_appends _ _ _ _ _)
      | _ :: _ :: _, embedded =>
          rw [embedStep_perform_many_eq] at embedded
          obtain ⟨row, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          obtain ⟨index, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          exact absurd embedded (by simp)
  | .ret value, b', embedded => by
      rw [embedStep_ret_eq] at embedded
      obtain ⟨⟨b1, v, ty1⟩, first, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      have grows := materialize_appends atoms 16 value b b1 v ty1 first
      have : b' = { b1 with blocks := b1.blocks ++ [retBlock b1 v], next := b1.next + 1 } :=
        (Option.some.inj embedded).symm
      refine grows.trans (this ▸ ⟨⟨[retBlock b1 v], rfl⟩, List.prefix_refl _,
        List.prefix_refl _, fun h => ?_, fun h o => ?_⟩)
      · show (b1.blocks ++ [retBlock b1 v]).length = b1.next + 1
        simp [h]
      · exact ordered_append_one o (by simp [retBlock, h])

theorem foldlM_appends (rows : ServiceRow) (atoms : AtomTable) :
    ∀ (steps : List Step) (b b' : Build),
      steps.foldlM (embedStep rows atoms) b = some b' → Appends b b'
  | [], b, b', folded => by
      have : b' = b := (Option.some.inj folded).symm
      exact this ▸ Appends.rfl' b
  | step :: rest, b, b', folded => by
      rw [List.foldlM_cons] at folded
      obtain ⟨b1, first, folded⟩ := Option.bind_eq_some_iff.mp folded
      exact (embedStep_appends rows atoms b step b1 first).trans
        (foldlM_appends rows atoms rest b1 b' folded)

/-! ## The walk of a pure term -/

/-- The `app` clause of `matWalk`, as a plain `Option` bind. -/
theorem matWalk_app_eq (atoms : AtomTable) (id : AlphabetId) (table : List OpSpec) (fuel : Nat)
    (scope : ScriptScope) (atom : String) (arg : PureTerm) :
    matWalk atoms id table (fuel + 1) scope (.app atom [arg]) =
      (matWalk atoms id table fuel scope arg).bind fun r =>
        (atoms.find? (·.1 == atom)).bind fun a =>
          (mintAt id table r.1 r.2.1 "" a.2.2).bind fun m =>
            some (m.1, m.2.1, fun env => (r.2.2 env).bind m.2.2) := rfl

/-- A resolved binder names a parameter of the open block. -/
theorem lookupVar_bound {b : Build} {name : String} {v : Var} {ty : String}
    (found : b.lookupVar name = some (v, ty)) : v.index < b.scope.length := by
  have key : ∀ (o : Option Nat), (match o with
      | some index =>
        match b.scope[index]? with
        | some entry => some ((⟨index⟩ : Var), entry.2)
        | none => none
      | none => none) = some (v, ty) → v.index < b.scope.length := by
    intro o
    cases o with
    | none => intro h; exact absurd h (by simp)
    | some i =>
        intro h
        replace h : (match b.scope[i]? with
          | some entry => some ((⟨i⟩ : Var), entry.2)
          | none => none) = some (v, ty) := h
        cases position : b.scope[i]? with
        | none => rw [position] at h; exact absurd h (by simp)
        | some entry =>
            rw [position] at h
            have vEq : (⟨i⟩ : Var) = v := congrArg Prod.fst (Option.some.inj h)
            have bound : i < b.scope.length := by
              rcases Nat.lt_or_ge i b.scope.length with hb | hb
              · exact hb
              · rw [List.getElem?_eq_none hb] at position
                exact absurd position (by simp)
            rw [← vEq]
            exact bound
  exact key _ found

/-- Minting one table row and performing it: `mintAt` builds exactly the walk
of the block `Build.addOp` then `Build.performTo` mints. -/
theorem mint_segment {id : AlphabetId} {raw : RawFlow String} {cycles : CyclesWF raw}
    {final : Build} (blocksEq : raw.blocks = final.blocks) (ordered : Ordered raw.blocks)
    {b : Build} {spec : OpSpec} {request : Var} {binder ty : String}
    (counted : b.blocks.length = b.next)
    (inScope : request.index < b.scope.length)
    (tablePrefix : ((b.addOp spec).1.performTo (b.addOp spec).2 request binder ty).table
      <+: final.table)
    (blocksPrefix : ((b.addOp spec).1.performTo (b.addOp spec).2 request binder ty).blocks
      <+: final.blocks) :
    ∃ walk : Walk id final.table,
      mintAt id final.table b.scriptScope request binder ty =
        some (((b.addOp spec).1.performTo (b.addOp spec).2 request binder ty).scriptScope,
              ⟨b.scope.length⟩, walk) ∧
      Segment raw cycles b.next (b.next + 1) b.scope.length (b.scope.length + 1) walk := by
  have tableLen : b.table.length < final.table.length := by
    have bound := tablePrefix.length_le
    simp only [Build.addOp, Build.performTo, List.length_append, List.length_cons,
      List.length_nil] at bound
    omega
  have lookupEq : ((tableAlphabet id final.table).lookup ⟨b.table.length⟩
      : Option (Fin final.table.length)) = some ⟨b.table.length, tableLen⟩ := dif_pos tableLen
  have walkEq : performWalk id final.table b.table.length request
      = some (fun env => match env[request.index]? with
          | some value => .vis ⟨⟨b.table.length, tableLen⟩, value⟩
              (fun answer : Val => .pure (env ++ [answer]))
          | none => .pure env) := by
    show (((tableAlphabet id final.table).lookup ⟨b.table.length⟩).map _) = _
    rw [lookupEq]
    rfl
  have scopeEq : ((b.addOp spec).1.performTo (b.addOp spec).2 request binder ty).scriptScope
      = ⟨b.scope ++ [(binder, ty)], b.table.length + 1⟩ := by
    simp [Build.scriptScope, Build.addOp, Build.performTo]
  refine ⟨_, ?_, performTo_segment (b := (b.addOp spec).1) (binder := binder) (answerTy := ty)
    blocksEq ordered counted blocksPrefix inScope walkEq⟩
  show (performWalk id final.table b.table.length request).map
    (fun w => ((⟨b.scope ++ [(binder, ty)], b.table.length + 1⟩ : ScriptScope),
      (⟨b.scope.length⟩ : Var), w)) = _
  rw [walkEq, scopeEq]
  rfl

/-- A literal row: `Build.literal` and `literalWalk` mint the same block. -/
theorem literal_segment {id : AlphabetId} {raw : RawFlow String} {cycles : CyclesWF raw}
    {final : Build} (blocksEq : raw.blocks = final.blocks) (ordered : Ordered raw.blocks)
    {b : Build} {value : Val} {ty : String}
    (counted : b.blocks.length = b.next) (nonempty : 0 < b.scope.length)
    (blocksPre : (b.literal value ty).1.blocks <+: final.blocks)
    (tablePre : (b.literal value ty).1.table <+: final.table) :
    ∃ walk : Walk id final.table,
      literalWalk id final.table b.scriptScope ty
        = some ((b.literal value ty).1.scriptScope, (b.literal value ty).2.1, walk) ∧
      (b.literal value ty).2.1.index < (b.literal value ty).1.scope.length ∧
      Segment raw cycles b.next (b.literal value ty).1.next b.scope.length
        (b.literal value ty).1.scope.length walk := by
  obtain ⟨walk, mintEq, seg⟩ :=
    mint_segment (id := id) (spec := ⟨"lit", .lit value, b.inputTy, ty, "never"⟩)
      blocksEq ordered counted (by simpa using nonempty) tablePre blocksPre
  have scopeLen : (b.literal value ty).1.scope.length = b.scope.length + 1 := by
    simp [Build.literal, Build.performTo, Build.addOp]
  have lastEq : (b.literal value ty).2.1 = (⟨b.scope.length⟩ : Var) := by
    simp [Build.literal, Build.last, Build.performTo, Build.addOp]
  refine ⟨walk, ?_, ?_, ?_⟩
  · rw [lastEq]
    exact mintEq
  · rw [lastEq, scopeLen]
    exact Nat.lt_succ_self _
  · rw [scopeLen]
    exact seg

/-- The `Build` invariant carried through `materialize`: the walk `matWalk`
builds is the segment the blocks `materialize` mints denote. -/
theorem materialize_segment {id : AlphabetId} {atoms : AtomTable}
    {raw : RawFlow String} {cycles : CyclesWF raw} {final : Build}
    (blocksEq : raw.blocks = final.blocks) (ordered : Ordered raw.blocks) :
    ∀ (fuel : Nat) (term : PureTerm) (b b' : Build) (v : Var) (ty : String),
      materialize atoms fuel b term = some (b', v, ty) →
      b'.blocks <+: final.blocks → b'.table <+: final.table →
      b.blocks.length = b.next → 0 < b.scope.length →
      ∃ walk : Walk id final.table,
        matWalk atoms id final.table fuel b.scriptScope term = some (b'.scriptScope, v, walk) ∧
        v.index < b'.scope.length ∧
        Segment raw cycles b.next b'.next b.scope.length b'.scope.length walk := by
  intro fuel
  induction fuel with
  | zero => intro term b b' v ty embedded; simp [materialize] at embedded
  | succ fuel ih =>
      intro term
      match term with
      | .var name =>
          intro b b' v ty embedded _ _ _ _
          rw [show materialize atoms (fuel + 1) b (.var name)
            = (b.lookupVar name).map (fun r => (b, r.1, r.2)) from rfl] at embedded
          obtain ⟨⟨v1, ty1⟩, found, value⟩ := Option.map_eq_some_iff.mp embedded
          have bEq : b' = b := (congrArg Prod.fst value).symm
          have vEq : v = v1 := (congrArg (fun p => p.2.1) value).symm
          subst b'
          subst v
          refine ⟨Walk.id', ?_, lookupVar_bound found, Segment.refl _ _⟩
          show (b.scriptScope.lookupVar name).map (fun r => (b.scriptScope, r.1, Walk.id')) = _
          rw [show b.scriptScope.lookupVar name = b.lookupVar name from rfl, found]
          rfl
      | .nat n =>
          intro b b' v ty embedded blocksPre tablePre counted nonempty
          rw [show materialize atoms (fuel + 1) b (.nat n)
            = some (b.literal (.nat n) "number") from rfl] at embedded
          have bEq : b' = (b.literal (.nat n) "number").1 :=
            (congrArg Prod.fst (Option.some.inj embedded)).symm
          have vEq : v = (b.literal (.nat n) "number").2.1 :=
            (congrArg (fun p => p.2.1) (Option.some.inj embedded)).symm
          subst b'
          subst v
          exact literal_segment blocksEq ordered counted nonempty blocksPre tablePre
      | .str value =>
          intro b b' v ty embedded blocksPre tablePre counted nonempty
          rw [show materialize atoms (fuel + 1) b (.str value)
            = some (b.literal (.str value) "string") from rfl] at embedded
          have bEq : b' = (b.literal (.str value) "string").1 :=
            (congrArg Prod.fst (Option.some.inj embedded)).symm
          have vEq : v = (b.literal (.str value) "string").2.1 :=
            (congrArg (fun p => p.2.1) (Option.some.inj embedded)).symm
          subst b'
          subst v
          exact literal_segment blocksEq ordered counted nonempty blocksPre tablePre
      | .app atom [] =>
          intro b b' v ty embedded; simp [materialize] at embedded
      | .app atom (arg :: second :: rest) =>
          intro b b' v ty embedded; simp [materialize] at embedded
      | .app atom [arg] =>
          intro b b' v ty embedded blocksPre tablePre counted nonempty
          rw [materialize_app_eq] at embedded
          obtain ⟨⟨b1, v1, ty1⟩, first, embedded⟩ := Option.bind_eq_some_iff.mp embedded
          obtain ⟨⟨atomName, requestTy, answerTy⟩, found, embedded⟩ :=
            Option.bind_eq_some_iff.mp embedded
          have bEq : b' = (b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).1.performTo
              (b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).2 v1 "" answerTy :=
            (congrArg Prod.fst (Option.some.inj embedded)).symm
          have vEq : v = ((b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).1.performTo
              (b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).2 v1 "" answerTy).last :=
            (congrArg (fun p => p.2.1) (Option.some.inj embedded)).symm
          subst b'
          subst v
          have grows1 := materialize_appends atoms fuel arg b b1 v1 ty1 first
          have grows2 := (addOp_appends b1 ⟨atom, .atom, requestTy, answerTy, "never"⟩).trans
            (performTo_appends _ (b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).2 v1 "" answerTy)
          have counted1 : b1.blocks.length = b1.next := grows1.counted counted
          obtain ⟨walk1, walkEq1, vBound1, seg1⟩ := ih arg b b1 v1 ty1 first
            (grows2.blocks.trans blocksPre) (grows2.table.trans tablePre) counted nonempty
          obtain ⟨walk2, mintEq, seg2⟩ :=
            mint_segment (id := id) blocksEq ordered counted1 vBound1 tablePre blocksPre
          have lastEq : ((b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).1.performTo
              (b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).2 v1 "" answerTy).last
              = (⟨b1.scope.length⟩ : Var) := by
            simp [Build.last, Build.performTo, Build.addOp]
          refine ⟨fun env => (walk1 env).bind walk2, ?_, ?_, ?_⟩
          · rw [matWalk_app_eq, walkEq1]
            show (atoms.find? (·.1 == atom)).bind _ = _
            rw [found]
            show (mintAt id final.table b1.scriptScope v1 "" answerTy).bind _ = _
            rw [mintEq, lastEq]
            rfl
          · show (Build.last _).index < _
            simp [Build.last, Build.performTo, Build.addOp]
          · have scopeLen : ((b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).1.performTo
                (b1.addOp ⟨atom, .atom, requestTy, answerTy, "never"⟩).2 v1 "" answerTy).scope.length
                = b1.scope.length + 1 := by
              simp [Build.performTo, Build.addOp]
            rw [scopeLen]
            exact seg1.trans seg2

/-! ## The walk of one step, and of a whole script -/

/-- A found index is a position of the list. Core states this through
`List.findIdx?_eq_some_iff_findIdx_eq`, whose proof is classical; the semantic
ceiling of this module is `propext`/`Quot.sound`, so it is reproved here. -/
private theorem findIdx?_lt {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Nat), l.findIdx? p = some i → i < l.length
  | [], _, h => absurd h (by simp [List.findIdx?, List.findIdx?.go])
  | a :: as, i, h => by
      show i < as.length + 1
      cases pa : p a with
      | true =>
          rw [show (a :: as).findIdx? p = some 0 from by rw [List.findIdx?_cons, pa]; rfl] at h
          have zero : i = 0 := (Option.some.inj h).symm
          omega
      | false =>
          rw [show (a :: as).findIdx? p = ((as.findIdx? p).map (fun i => i + 1)) from by
            rw [List.findIdx?_cons, pa]; rfl] at h
          obtain ⟨j, hj, eq⟩ := Option.map_eq_some_iff.mp h
          have bound := findIdx?_lt p as j hj
          have same : i = j + 1 := eq.symm
          omega

/-- A resolved operation is a row of the family's table. -/
theorem familyIndex_lt {rows : ServiceRow} {op : String} {index : Nat}
    (found : familyIndex rows op = some index) : index < (familyTable rows).length := by
  have bound := findIdx?_lt _ rows.ops index found
  simpa [familyTable] using bound

/-- The `perform` step: the argument's own segment, then the block that
performs the family operation. -/
theorem step_segment {id : AlphabetId} {rows : ServiceRow} {atoms : AtomTable}
    {raw : RawFlow String} {cycles : CyclesWF raw} {final : Build}
    (blocksEq : raw.blocks = final.blocks) (ordered : Ordered raw.blocks)
    {b b' : Build} {bind : Option String} {op : String} {args : List PureTerm}
    (embedded : embedStep rows atoms b (.perform bind op args) = some b')
    (blocksPre : b'.blocks <+: final.blocks) (tablePre : b'.table <+: final.table)
    (counted : b.blocks.length = b.next) (nonempty : 0 < b.scope.length)
    (family : (familyTable rows).length ≤ b.table.length) :
    ∃ walk : Walk id final.table,
      stepWalk rows atoms id final.table b.scriptScope bind op args
        = some (b'.scriptScope, walk) ∧
      Segment raw cycles b.next b'.next b.scope.length b'.scope.length walk := by
  have main : ∀ (b1 : Build) (request : Var) (row : OpRow) (index : Nat) (walk1 : Walk id final.table),
      rows.row? op = some row → familyIndex rows op = some index →
      b' = b1.performTo index request (bind.getD "") row.tsAnswer →
      Appends b b1 → request.index < b1.scope.length →
      Segment raw cycles b.next b1.next b.scope.length b1.scope.length walk1 →
      ∃ walk : Walk id final.table,
        (performAt id final.table b1.scriptScope index request (bind.getD "") row.tsAnswer).bind
          (fun r => some (r.1, fun env => (walk1 env).bind r.2.2)) = some (b'.scriptScope, walk) ∧
        Segment raw cycles b.next b'.next b.scope.length b'.scope.length walk := by
    intro b1 request row index walk1 rowEq indexEq b'Eq grows inScope seg1
    subst b'Eq
    have counted1 : b1.blocks.length = b1.next := grows.counted counted
    have indexBound : index < final.table.length := by
      have one := familyIndex_lt indexEq
      have two := grows.table.length_le
      have three := tablePre.length_le
      have four : (b1.performTo index request (bind.getD "") row.tsAnswer).table = b1.table := rfl
      rw [four] at three
      omega
    have lookupEq : ((tableAlphabet id final.table).lookup ⟨index⟩
        : Option (Fin final.table.length)) = some ⟨index, indexBound⟩ := dif_pos indexBound
    obtain ⟨walk2, walkEq⟩ : ∃ w : Walk id final.table,
        performWalk id final.table index request = some w := by
      refine ⟨fun env => match env[request.index]? with
        | some value => .vis ⟨⟨index, indexBound⟩, value⟩
            (fun answer : Val => .pure (env ++ [answer]))
        | none => .pure env, ?_⟩
      show (((tableAlphabet id final.table).lookup ⟨index⟩).map _) = _
      rw [lookupEq]
      rfl
    have seg2 := performTo_segment (b := b1) (cycles := cycles) (binder := bind.getD "")
      (answerTy := row.tsAnswer) blocksEq ordered counted1 blocksPre inScope walkEq
    refine ⟨fun env => (walk1 env).bind walk2, ?_, ?_⟩
    · show ((performWalk id final.table index request).map _).bind _ = _
      rw [walkEq]
      rfl
    · have scopeLen : (b1.performTo index request (bind.getD "") row.tsAnswer).scope.length
          = b1.scope.length + 1 := by simp [Build.performTo]
      rw [scopeLen]
      exact seg1.trans seg2
  match args, embedded with
  | [], embedded =>
      rw [embedStep_perform_nil_eq] at embedded
      obtain ⟨row, rowEq, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      obtain ⟨index, indexEq, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      have b'Eq : b' = (b.literal Val.unit "void").1.performTo index
          (b.literal Val.unit "void").2.1 (bind.getD "") row.tsAnswer :=
        (Option.some.inj embedded).symm
      have grows := literal_appends b Val.unit "void"
      obtain ⟨walk1, litEq, vBound, seg1⟩ := literal_segment (id := id) blocksEq ordered counted
        nonempty (by rw [b'Eq] at blocksPre; exact (performTo_appends _ _ _ _ _).blocks.trans blocksPre)
        (by rw [b'Eq] at tablePre; exact (performTo_appends _ _ _ _ _).table.trans tablePre)
      obtain ⟨walk, walkEq, seg⟩ := main _ _ row index walk1 rowEq indexEq b'Eq grows vBound seg1
      refine ⟨walk, ?_, seg⟩
      show (rows.row? op).bind _ = _
      rw [rowEq]
      show (familyIndex rows op).bind _ = _
      rw [indexEq]
      show (literalWalk id final.table b.scriptScope "void").bind _ = _
      rw [litEq]
      exact walkEq
  | [arg], embedded =>
      rw [embedStep_perform_one_eq] at embedded
      obtain ⟨row, rowEq, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      obtain ⟨index, indexEq, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      obtain ⟨⟨b1, request, ty1⟩, first, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      have b'Eq : b' = b1.performTo index request (bind.getD "") row.tsAnswer :=
        (Option.some.inj embedded).symm
      have grows := materialize_appends atoms 16 arg b b1 request ty1 first
      obtain ⟨walk1, matEq, vBound, seg1⟩ := materialize_segment (id := id) blocksEq ordered
        16 arg b b1 request ty1 first
        (by rw [b'Eq] at blocksPre; exact (performTo_appends _ _ _ _ _).blocks.trans blocksPre)
        (by rw [b'Eq] at tablePre; exact (performTo_appends _ _ _ _ _).table.trans tablePre)
        counted nonempty
      obtain ⟨walk, walkEq, seg⟩ := main _ _ row index walk1 rowEq indexEq b'Eq grows vBound seg1
      refine ⟨walk, ?_, seg⟩
      show (rows.row? op).bind _ = _
      rw [rowEq]
      show (familyIndex rows op).bind _ = _
      rw [indexEq]
      show (matWalk atoms id final.table 16 b.scriptScope arg).bind _ = _
      rw [matEq]
      exact walkEq
  | _ :: _ :: _, embedded =>
      rw [embedStep_perform_many_eq] at embedded
      obtain ⟨row, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      obtain ⟨index, _, embedded⟩ := Option.bind_eq_some_iff.mp embedded
      exact absurd embedded (by simp)

/-- `liftScript` distributes over the walk's binds. -/
theorem liftScript_bind {Ty : Type} {alphabet : FlowAlphabet Ty}
    (program : Program (Sig alphabet) Env) (next : Env → Program (Sig alphabet) Val) :
    liftScript (program.bind next)
      = (Program.inl program).bind fun value => liftScript (next value) := by
  unfold liftScript
  rw [Program.inl_bind, Program.bind_assoc]

/-- The main induction: from the block the next step mints, the flow's
denotation is the walk of the remaining steps. -/
theorem stepsWalk_denote {id : AlphabetId} {rows : ServiceRow} {atoms : AtomTable}
    {raw : RawFlow String} {cycles : CyclesWF raw} {final : Build}
    (blocksEq : raw.blocks = final.blocks) (ordered : Ordered raw.blocks) :
    ∀ (steps : List Step) (b : Build) (env : Env)
      (walk : Env → Program (Sig (tableAlphabet id final.table)) Val),
      steps.foldlM (embedStep rows atoms) b = some final →
      stepsWalk rows atoms id final.table steps b.scriptScope = some walk →
      env.length = b.scope.length → 0 < b.scope.length →
      b.blocks.length = b.next → (familyTable rows).length ≤ b.table.length →
      denoteGo (alphabet := tableAlphabet id final.table) raw cycles ⟨b.next⟩ env []
        = liftScript (walk env)
  | [], b, env, walk, _, walkEq, _, _, _, _ => by
      exact absurd walkEq (by simp [stepsWalk])
  | .ret value :: rest, b, env, walk, folded, walkEq, sized, nonempty, counted, family => by
      rw [List.foldlM_cons] at folded
      obtain ⟨b1, first, folded⟩ := Option.bind_eq_some_iff.mp folded
      rw [embedStep_ret_eq] at first
      obtain ⟨⟨b2, v, ty1⟩, materialized, first⟩ := Option.bind_eq_some_iff.mp first
      have b1Eq : b1 = { b2 with blocks := b2.blocks ++ [retBlock b2 v], next := b2.next + 1 } :=
        (Option.some.inj first).symm
      have grows2 := materialize_appends atoms 16 value b b2 v ty1 materialized
      have toFinal := foldlM_appends rows atoms rest b1 final folded
      have blocksPre : b2.blocks <+: final.blocks := by
        refine List.IsPrefix.trans ?_ toFinal.blocks
        rw [b1Eq]
        exact ⟨[retBlock b2 v], rfl⟩
      have tablePre : b2.table <+: final.table := by
        refine List.IsPrefix.trans ?_ toFinal.table
        rw [b1Eq]
        exact List.prefix_refl _
      obtain ⟨walk1, matEq, vBound, seg⟩ := materialize_segment (id := id) blocksEq ordered
        16 value b b2 v ty1 materialized blocksPre tablePre counted nonempty
      have counted2 : b2.blocks.length = b2.next := grows2.counted counted
      have retPre : (b2.blocks ++ [retBlock b2 v]) <+: final.blocks := by
        refine List.IsPrefix.trans ?_ toFinal.blocks
        rw [b1Eq]
        exact List.prefix_refl _
      have walkDef : walk = fun env => (walk1 env).bind fun env =>
          match env[v.index]? with
          | some result => .pure result
          | none => .pure .unit := by
        have step : stepsWalk rows atoms id final.table (.ret value :: rest) b.scriptScope
            = (matWalk atoms id final.table 16 b.scriptScope value).bind fun r =>
                some (fun env => (r.2.2 env).bind fun env =>
                  match env[r.2.1.index]? with
                  | some result => .pure result
                  | none => .pure .unit) := rfl
        rw [step, matEq] at walkEq
        exact (Option.some.inj walkEq).symm
      rw [walkDef, seg.denote env sized, liftScript_bind]
      refine Leaves.bind_congr (Leaves.inl (seg.sized env sized)) fun env' holds => ?_
      exact ret_denote (id := id) blocksEq ordered counted2 retPre (by omega)
  | .perform bind op args :: rest, b, env, walk, folded, walkEq, sized, nonempty, counted, family => by
      rw [List.foldlM_cons] at folded
      obtain ⟨b1, first, folded⟩ := Option.bind_eq_some_iff.mp folded
      have toFinal := foldlM_appends rows atoms rest b1 final folded
      have grows := embedStep_appends rows atoms b _ b1 first
      obtain ⟨walkStep, stepEq, seg⟩ := step_segment (id := id) blocksEq ordered first
        toFinal.blocks toFinal.table counted nonempty family
      have counted1 : b1.blocks.length = b1.next := grows.counted counted
      have nonempty1 : 0 < b1.scope.length := Nat.lt_of_lt_of_le nonempty grows.scope.length_le
      have family1 : (familyTable rows).length ≤ b1.table.length :=
        Nat.le_trans family grows.table.length_le
      have step : stepsWalk rows atoms id final.table (.perform bind op args :: rest) b.scriptScope
          = (stepWalk rows atoms id final.table b.scriptScope bind op args).bind fun r =>
              (stepsWalk rows atoms id final.table rest r.1).bind fun k =>
                some (fun env => (r.2 env).bind k) := rfl
      rw [step, stepEq] at walkEq
      replace walkEq : (stepsWalk rows atoms id final.table rest b1.scriptScope).bind
          (fun k => some (fun env => (walkStep env).bind k)) = some walk := walkEq
      obtain ⟨k, restEq, walkEq⟩ := Option.bind_eq_some_iff.mp walkEq
      have walkDef : walk = fun env => (walkStep env).bind k := (Option.some.inj walkEq).symm
      rw [walkDef, seg.denote env sized, liftScript_bind]
      refine Leaves.bind_congr (Leaves.inl (seg.sized env sized)) fun env' holds => ?_
      exact stepsWalk_denote blocksEq ordered rest b1 env' k folded restEq holds nonempty1
        counted1 family1

/-! ## D5: the embedding denotes the script -/

/-- The build the embedding starts from. -/
def startBuild (rows : ServiceRow) (script : Script) : Build :=
  { inputTy := script.param.2, table := familyTable rows, blocks := [],
    scope := [script.param], next := 0 }

/-- The graph `Script.toFlow` returns for a finished build. -/
def flowOf (script : Script) (b : Build) : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := script.param.2,
    resultTy := script.result, blocks := b.blocks }

theorem toFlow_eq (rows : ServiceRow) (atoms : AtomTable) (script : Script) :
    Script.toFlow rows atoms script =
      (script.steps.foldlM (embedStep rows atoms) (startBuild rows script)).bind fun b =>
        some (b.table, flowOf script b) := rfl

/-- D5. The graph the embedding builds denotes the program the script says:
`Flow.denoteGo` of `Script.toFlow`'s output, on the empty tape, is
`denoteScript` lifted into the flow's signature. -/
theorem Script.toFlow_denote {id : AlphabetId} {rows : ServiceRow} {atoms : AtomTable}
    {script : Script} {table : List OpSpec} {raw : RawFlow String}
    (embedded : Script.toFlow rows atoms script = some (table, raw))
    (cycles : CyclesWF raw) {input : Val}
    {program : Program (Sig (tableAlphabet id table)) Val}
    (denoted : denoteScript id rows atoms table script input = some program) :
    denoteGo (alphabet := tableAlphabet id table) raw cycles raw.entry [input] []
      = liftScript program := by
  rw [toFlow_eq] at embedded
  obtain ⟨final, folded, value⟩ := Option.bind_eq_some_iff.mp embedded
  have tableEq : table = final.table := (congrArg Prod.fst (Option.some.inj value)).symm
  have rawEq : raw = flowOf script final := (congrArg Prod.snd (Option.some.inj value)).symm
  subst tableEq
  subst rawEq
  have grows := foldlM_appends rows atoms script.steps (startBuild rows script) final folded
  have ordered : Ordered (flowOf script final).blocks :=
    grows.ordered rfl (by intro i h; exact absurd h (by simp [startBuild]))
  obtain ⟨walk, walkEq, programEq⟩ := Option.map_eq_some_iff.mp denoted
  refine Eq.trans ?_ (congrArg liftScript programEq)
  exact stepsWalk_denote (id := id) rfl ordered script.steps (startBuild rows script) [input]
    walk folded walkEq rfl (by simp [startBuild]) rfl (by simp [startBuild])

end Effect4.Target.EffectV4
