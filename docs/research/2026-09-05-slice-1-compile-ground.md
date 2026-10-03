# Slice 1 of the Program and Machine track: the ground under the compile's first theorem

Status: plan, 2026-09-05, Mac seat, base `40f4537`. Cut from
`docs/research/2026-09-05-effects-papers-review.md` §3 G1, G4, G5 and §6 (the owner accepted
the per-track order the same day). Packet: `Test/contracts/program-denotation.contract.md`.
Nothing is built by this plan; the three lanes below are the first work.

## 0. The slice in one paragraph

Three lanes write three new modules and their batteries, edit no existing file under
`src/Effect4`, and hand the coordinator files, not commits. Lane 1 (`Program/Typed.lean`)
types values and proves that well-typed terms evaluate to well-typed values and that a
well-typed request decodes to a store operation. Lane 2 (`Machine/StoresLaws.lean`) orders
the stores by growth, defines handle validity, and proves that a valid operation always steps,
answers a valid value, and grows the store. Lane 3 (`Program/Denote.lean`) sends the
straight-line fragment of `Eff` into `Effects.Program` over the store signature, interprets it
through one handler into `StateT Stores Id`, proves the compositional equations from the
algebra's laws, and pins, by `#guard`, that the meaning agrees with `Api.run` on every
straight-line program of the compile battery. The slice-2 theorem, `run_eq_meaning`, is
stated in the packet now and proved by one design seat afterwards over these three modules
and the clause equations of `Machine/Clauses.lean`. It will be the first theorem in
`Program/Compile.lean`'s graph (today: 0 theorems, 114 guards).

## 1. What is fixed now

### 1.1 The goal theorem of slice 2

```lean
theorem run_eq_meaning (e : NativeEff) (hs : Denote.Straight e = true) (fuel : Nat)
    (hfuel : Denote.cost e ≤ fuel) (hops : Denote.ops e < Effect4.Machine.defaultBudget) :
    let r := Effect4.Api.run e fuel
    let m := Denote.meaning e [] Effect4.Machine.Stores.empty
    r.outcome = Effect4.Api.Outcome.finished ∧ r.exit = some m.1 ∧ r.stores = m.2
```

`Api.run` replays the tape `[evaluate root, flush]` over `load e fuel` (`src/Effect4/Api.lean`),
so the theorem says: on the straight-line fragment, the reference machine's root exit and its
final stores are the algebra's interpretation of the denotation. Two fuels are bounded by one
hypothesis, since `Api.run` hands `fuel` to both the compile's `Point.fuel` (one per child,
`Compile.lean:113`) and the command loop (one per command, `Fibers.lean:1160`): `cost e` must
exceed the term's depth and the number of commands the run takes. `ops e` bounds the loop
iterations so the op budget (`defaultBudget = 2048`, `Stores.lean:1315`) never injects a
yield; the yield-transparency lemma is a later row. `cost` and `ops` are structural functions
the slice-2 seat defines; the packet fixes only that they are computable.

Not claimed by the theorem: agreement on the trace (the machine records frame events the
algebra has no producer for; row `E4-DEN-CE-003`), anything outside `Straight`, and anything
about a second fiber.

### 1.2 The fragment

`Straight : NativeEff → Bool` is true exactly for `succeed`, `fail`, `failCause`, `yieldError`,
`sync`, `suspend`, `perform op _` with `(NativeOp.row op).kind = .sync`, `bind`, `branch`,
`exit`, `catchCause`, `matchCause` and `onExit`, recursively on every subprogram, and false
for everything else (`gen`, `whileLoop`, `choose`, the masks, `yieldNow`, `callback`,
`awaitFiber`, `withFiber`, `scoped`, `acquireRelease`, async and program rows). The masks are
excluded because they compile through `withFiber (act p)` and a fiber action; `gen` and
`whileLoop` because the denotation would need fuel; the rest because they park, fork or reach
the frontier.

### 1.3 Statements fixed and deliberately not proved in this slice

- The bind law has Hazel's neutral-context shape (review §3 G8). It is the induction
  hypothesis of slice 2 (§9) with the outer stack `K` untouched by the inner run; the general
  law is not stated.
- Term centrality at the run level (review §3 G3) and the machine-wide `handles_minted`
  invariant (review §3 G5) wait for the multi-fiber invariant slice. Slice 1 proves the
  store half of validity (lane 2) and the unforgeability that is already definitional: `Lit`
  (`Eff.lean:196-201`) has no handle literal, so a handle enters a program only as an answer.

## 2. Lane 1 brief: `src/Effect4/Program/Typed.lean`

Import `Effect4.Program.Native` (which brings `Typing`, `Eff`, `Stores`). Namespace
`Effect4.Program`. Everything first-order, `Type 0`, no `String` traversal.

### 2.1 Definitions

```lean
/-- Which values inhabit which types of the native cut. -/
def Val.hasTy : Val → Ty → Bool
  | Val.unit, .unit => true
  | Val.nat _, .nat => true
  | Val.bool _, .bool => true
  | Val.cell _, .handle target => target == "Ref.Ref<number>"          -- NativeOp.refTy
  | Val.promise _, .handle target => target == "Deferred.Deferred<number, number>"   -- NativeOp.deferredTy
  | Val.scopeHandle _, .handle target => target == "Scope.Scope"       -- Ty.scope
  | Val.context _, .handle target => target == "Context.Context<unknown>"   -- Ty.context
  | Val.fiber _, .fiberOf _ _ => true
  | Val.fibers _, .list (.fiberOf _ _) => true
  | Val.exitOk v, .exitOf a _ => v.hasTy a
  | Val.exitErr _, .exitOf _ _ => true                                   -- TYPED-FB-CAUSE
  | Val.exitCons a (Val.exitCons b Val.exitNil), .prod ta tb => a.hasTy ta && b.hasTy tb
  | Val.exitNil, .list _ => true
  | Val.exitCons h t, .list ty => h.hasTy ty && t.hasTy (.list ty)
  | v, .union l r => v.hasTy l || v.hasTy r
  | _, _ => false
```

The `String` equality on handle targets is `BEq String`, which is at the ceiling
(`Program/Config.lean` header records the same fact); no function iterates the string. If the
implementer prefers, compare against `NativeOp.refTy` and the other three constants with
`decide` on `Ty`, which `deriving DecidableEq` provides. `.int`, `.string`, `.option`,
`.except`, `.causeOf`, `.never` and unknown handle targets have no value in this cut; each is
a refusal named in the module header, not a silent `false`.

```lean
/-- A positional environment fits a typing environment. -/
def Fits (env : List Val) (tys : TyEnv) : Prop :=
  List.Forall₂ (fun v t => v.hasTy t = true) env tys

/-- No `str` literal anywhere in a term (the one literal `Lit.toVal` refuses). -/
mutual
  def Term.noStr : Term → Bool
  def Terms.noStr : Terms → Bool
end
```

### 2.2 Theorems

| name | statement | route |
| --- | --- | --- |
| `Fits.get?` | `Fits env tys → env[i]? = some v → tys[i]? = some t → v.hasTy t = true` | induction on the `Forall₂` |
| `Fits.length` | `Fits env tys → env.length = tys.length` | `List.Forall₂.length_eq` |
| `Fits.append` | `Fits env tys → v.hasTy t = true → Fits (env ++ [v]) (tys ++ [t])` | `Forall₂` append |
| `Lit.toVal_hasTy` | `l.toVal = some v → v.hasTy l.ty = true` | cases on `Lit` |
| `Lit.toVal_isSome` | `(∀ s, l ≠ .str s) → (l.toVal).isSome` | cases |
| `nativeAtom_typed` | `nativeAtomTy atom tys = some ty → List.Forall₂ (fun v t => v.hasTy t = true) vs tys → ∃ v, nativeAtom atom vs = some v ∧ v.hasTy ty = true` | ten atoms (`Native.lean:63-84`); `pair` answers `Val.tuple [a, b]`, which is the `.prod` shape of `hasTy` |
| `evalTerm_hasTy`, `evalTerms_hasTy` | `Fits env tys → termTy nativeSignature tys t = some ty → evalTerm env t = some v → v.hasTy ty = true` (and the list form) | mutual induction on `Term`/`Terms`; `nativeSignature.atomOf = nativeAtomTy` by `rfl` |
| `evalTerm_isSome`, `evalTerms_isSome` | `Fits env tys → termTy nativeSignature tys t = some ty → t.noStr = true → (evalTerm env t).isSome` | same induction, `Lit.toVal_isSome` at the leaves |
| `syncOpOf_isSome` | `v.hasTy (NativeOp.row op).request = true → (NativeOp.row op).kind = .sync → (NativeOp.syncOpOf op v).isSome` | cases on `op`, then on `v`; the twenty rows at `Native.lean:145-203` against the patterns at `:208-232` |
| `syncOpOf_async_none` | `(NativeOp.row op).kind = .async → NativeOp.syncOpOf op v = none` | the one async row is `deferredAwait` |

The `termTy` of `Typing.lean:63-77` is `Option`-valued and structural; the induction is on
the term with `tys` and `env` generalised. `hasTy` is `Bool`; state every theorem with
`= true` so `decide` closes the guards.

### 2.3 Battery `Test/Program/TypedContract.lean` and report `Test/Program/TypedAxiomReport.lean`

Guards: `hasTy` on one value of each inhabited type and one refusal per uninhabited type;
`evalTerm` on the atoms with their typed arguments; `syncOpOf` on each sync row's request
shape; the two register rows below as pairs of guards. The report is `#print axioms` on every
theorem; expected ceiling `propext`/`Quot.sound` (`decide` on `Bool` needs neither).

Rows (RESERVED in the packet, registered at landing): `E4-TYPED-CE-001` (a `str` literal
types and does not evaluate, so totality carries `noStr`), `E4-TYPED-CE-002` (`Val.nat`
does not inhabit `.int`; `Ty.render` sends both to `number`, the value typing does not).

## 3. Lane 2 brief: `src/Effect4/Machine/StoresLaws.lean`

Import `Effect4.Machine.Stores`. Namespace `Effect4.Machine`.

### 3.1 Definitions

```lean
/-- The stores only grow: a heap never shrinks, a Deferred cell is never freed, a scope entry
is never removed, the name counter never decreases. -/
def Stores.le (s s' : Stores) : Prop :=
  s.refs.length ≤ s'.refs.length ∧
  s.deferreds.cells.length ≤ s'.deferreds.cells.length ∧
  (∀ key, (s.scopes.entryAt key).isSome → (s'.scopes.entryAt key).isSome) ∧
  s.nextName ≤ s'.nextName

/-- A value's handles exist in the store. Fibers are the machine's, not the store's. -/
def Val.validIn (s : Stores) : Val → Bool
  | Val.cell k => k.index < s.refs.length
  | Val.promise k => k.index < s.deferreds.cells.length
  | Val.scopeHandle key => (s.scopes.entryAt key).isSome
  | Val.exitOk v => v.validIn s
  | Val.exitCons h t => h.validIn s && t.validIn s
  | _ => true

/-- An operation's keys and argument values exist in the store. -/
def SyncOp.validIn (s : Stores) : SyncOp → Bool
  -- refMake initial ↦ initial.validIn s; refGet k ↦ k.index < s.refs.length;
  -- refSet k v ↦ k.index < s.refs.length && v.validIn s; the other ref ops on the key;
  -- deferredMake ↦ true; the Deferred ops on the cell index; scopeMake ↦ true;
  -- scopeAdd/scopeRemove/scopeIsClosed on the entry; deferredAwaitCleanup on the cell.

/-- Every value the heap holds is valid in the store that holds it. -/
def Stores.WF (s : Stores) : Prop := ∀ v ∈ s.refs, v.validIn s = true
```

`Stores.empty` is `WF` (empty heap). A `Completion`'s stored program is a `Prim` and is not
traversed by `validIn`; the Deferred half of `WF` is a later row and is named in the header.

### 3.2 Theorems

| name | statement | route |
| --- | --- | --- |
| `Stores.le_refl`, `Stores.le_trans` | | `Nat.le_refl` and friends |
| `refStep_length` | `refStep o heap = some (v, heap') → heap.length ≤ heap'.length` | `refMake` appends; every other arm is `refPoke`, and `List.length_set` |
| `syncOpStep_le` | `syncOpStep o s = some (s', v) → s.le s'` | one case per arm of `Stores.lean:1209-1240`; `DeferredStore.make` appends; `setCell` is `List.set`; `ScopeStore.make` appends, `setEntry` maps in place, `forkChild` is not reachable from `syncOpStep` |
| `Val.validIn_mono` | `s.le s' → v.validIn s = true → v.validIn s' = true` | induction on `v` |
| `SyncOp.validIn_mono` | same for operations | cases |
| `syncOpStep_isSome_of_valid` | `o.validIn s = true → (syncOpStep o s).isSome` | every `none` in `syncOpStep`/`refStep` is a failed lookup; `refUpdateSomeAndGet` re-reads after a `refPoke`, which keeps the length (`List.length_set`) |
| `syncOpStep_wf` | `s.WF → o.validIn s = true → syncOpStep o s = some (s', v) → s'.WF` | heap writes store `f.total a`, `f.modify`, the argument value, or a value already in the heap; `FnName.total` of a `nat` is a `nat` |
| `syncOpStep_answer_valid` | `s.WF → o.validIn s = true → syncOpStep o s = some (s', v) → v.validIn s' = true` | `refMake` answers `cell ⟨heap.length⟩`, valid in `heap ++ [_]`; reads answer heap values, valid by `WF` and `validIn_mono`; `deferredMake` answers the new index; `scopeMake` answers `nextName`, present after `ScopeStore.make` |
| `syncOpStep_read_unchanged` | for `refGet`, `deferredIsDone`, `deferredPoll`, `scopeIsClosed`: `syncOpStep o s = some (s', v) → s' = s` | unfold |

### 3.3 Battery `Test/Machine/Runtime/StoresLawsContract.lean` and report `Test/Machine/Runtime/StoresLawsAxiomReport.lean`

Guards: `syncOpStep` on `Stores.empty` for `refGet ⟨0⟩` (none) and after `refMake` (some);
`validIn` on the answers of a make-then-read sequence; the two rows below. Report as in
`Test/Machine/Runtime/FramesAxiomReport.lean`.

Rows: `E4-STORES-CE-001` (`syncOpStep (refGet ⟨0⟩) Stores.empty = none`, so totality carries
`validIn`), `E4-STORES-CE-002` (a heap `[Val.cell ⟨9⟩]` answers a dangling handle to
`refGet ⟨0⟩`, so answer validity carries `WF`).

## 4. Lane 3 brief: `src/Effect4/Program/Denote.lean`

Import `Effect4.Program.Native` and `Effects.Algebra.Laws` (the package's `Program`,
`Handler`, `interpret`, `interpret_bind`, `interpret_perform`). Namespace
`Effect4.Program.Denote`. Do not import `Effect4.Machine.Fibers` or `Effect4.Api`; the
machine enters only in the battery.

### 4.1 Definitions

```lean
/-- The store signature: every `sync` operation, answered by one value. -/
def StoreSig : Effects.Signature.{0, 0} := ⟨SyncOp, fun _ => Val⟩

/-- `Compile.badShape`, as an exit. -/
def badShapeExit : ExitV := Exit.failure (Cause.die Defect.badName)
/-- Outside the fragment; never reached under `Straight`. -/
def outsideExit : ExitV := Exit.failure (Cause.die Defect.notImplemented)

/-- A finalizer's exit as `Exit.restoreAfterFinalizer` reads it. -/
def finVoid : ExitV → VoidExitV
  | Exit.success _ => Exit.void
  | Exit.failure c => Exit.failure c

/-- Short-circuit on failure. -/
def seqExit (k : Val → Effects.Program StoreSig ExitV) : ExitV → Effects.Program StoreSig ExitV
  | Exit.success v => k v
  | Exit.failure c => pure (Exit.failure c)

def Straight : NativeEff → Bool   -- §1.2

def denote : NativeEff → List Val → Effects.Program StoreSig ExitV
  | .succeed v, env => pure (match evalTerm env v with
      | some x => Exit.success x | none => badShapeExit)
  | .fail e, env => pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => badShapeExit)
  | .failCause c, env => pure (match causeOf env c with
      | some cause => Exit.failure cause | none => badShapeExit)
  | .yieldError e, env => pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => badShapeExit)
  | .sync t, env => pure (Exit.success ((evalTerm env t).getD Val.unit))
  | .suspend b, env => denote b env
  | .perform op r, env =>
    match (NativeOp.row op).kind with
    | .sync =>
      match (evalTerm env r).bind (NativeOp.syncOpOf op) with
      | some o => Effects.Program.perform (S := StoreSig) o >>= fun v => pure (Exit.success v)
      | none => pure badShapeExit
    | _ => pure outsideExit
  | .bind a b, env => denote a env >>= seqExit (fun v => denote b (env ++ [v]))
  | .branch t a b, env =>
    match evalTerm env t with
    | some (Val.bool true) => denote a env
    | some (Val.bool false) => denote b env
    | _ => pure badShapeExit
  | .exit b, env => denote b env >>= fun ex => pure (Exit.success (reifyExitVal ex))
  | .catchCause b h, env => denote b env >>= fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure c => denote h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => denote b env >>= fun
    | Exit.success x => denote v (env ++ [x])
    | Exit.failure cause => denote c (env ++ [Val.exitErr cause])
  | .onExit b f, env => denote b env >>= fun ex =>
    denote f (env ++ [reifyExitVal ex]) >>= fun fex =>
      pure (Exit.restoreAfterFinalizer ex (finVoid fex))
  | _, _ => pure outsideExit

/-- The one handler: the store step, with the machine's fallback on `none`
(`Fibers.lean:834-840`: `syncState = none` falls back to `syncValue`, which is `Val.unit` on an
`EffThunk.op`, `Compile.lean:593-598`). -/
def storeHandler : Effects.Handler StoreSig (StateT Stores Id) where
  handle o := fun s => match syncOpStep o s with
    | some (s', v) => (v, s')
    | none => (Val.unit, s)

/-- The meaning of a straight-line program: its exit and the stores it leaves. -/
def meaning (e : NativeEff) (env : List Val) (s : Stores) : ExitV × Stores :=
  (Effects.interpret storeHandler (denote e env)).run s
```

Each arm mirrors one arm of `compileEff` (`Compile.lean:280-356`) and of the hooks
`syncValueAt` (`:593`), `suspendBodyAt` (`:602`), `contAOf` (`:552`), `contEOf` (`:574`) and
`finalizerProgram` (`:693`); the implementer reads those before writing each arm and records
in the arm's docstring which line it mirrors. The `sync`/`succeed` asymmetry is deliberate
(`E4-DEN-CE-001`). `errOf`, `causeOf`, `reifyExitVal` are the compile's own
(`Compile.lean:244-270`, `Stores.lean:992`).

`Effects.Program.perform (S := StoreSig) o : Effects.Program StoreSig (StoreSig.Answer o)`,
and `StoreSig.Answer o` is `Val` by `rfl`; a `show` may be needed at the bind.

### 4.2 Theorems

| name | statement | route |
| --- | --- | --- |
| `Straight.bind`, `.suspend`, `.branch`, `.exit`, `.catchCause`, `.matchCause`, `.onExit` | the fragment is closed under subprograms: `Straight (.bind a b) = true → Straight a = true ∧ Straight b = true`, and so on | unfold, `Bool.and_eq_true` |
| `denote_*` | the defining equations, one per arm, as `simp` lemmas | `rfl` |
| `meaning_succeed`, `meaning_fail`, `meaning_failCause`, `meaning_yieldError`, `meaning_sync` | `meaning (.succeed v) env s = (…, s)` with the arm's exit | `interpret_pure` |
| `meaning_suspend` | `meaning (.suspend b) env s = meaning b env s` | `rfl` |
| `meaning_perform_sync` | `(NativeOp.row op).kind = .sync → evalTerm env r = some x → NativeOp.syncOpOf op x = some o → meaning (.perform op r) env s = match syncOpStep o s with \| some (s', v) => (Exit.success v, s') \| none => (Exit.success Val.unit, s)` | `interpret_bind`, `interpret_perform` (needs `LawfulMonad (StateT Stores Id)`, which core provides), then `StateT.run_bind` |
| `meaning_perform_bad` | the two `badShapeExit` cases | `interpret_pure` |
| `meaning_bind` | `meaning (.bind a b) env s = let r := meaning a env s; match r.1 with \| Exit.success v => meaning b (env ++ [v]) r.2 \| Exit.failure c => (Exit.failure c, r.2)` | `interpret_bind`; cases on the exit |
| `meaning_branch_true`, `meaning_branch_false`, `meaning_branch_bad` | | unfold |
| `meaning_exit` | `meaning (.exit b) env s = ((fun r => (Exit.success (reifyExitVal r.1), r.2)) (meaning b env s))` | `interpret_bind` |
| `meaning_catchCause`, `meaning_matchCause`, `meaning_onExit` | the same shape as `meaning_bind` with the arm's continuation | `interpret_bind` |
| `meaning_stores_eq_of_pure` | on a program with no `perform`, `(meaning e env s).2 = s` | induction under a `NoPerform` predicate; optional, cheap, useful in slice 2 |

All at `propext`/`Quot.sound`; `Effects.interpret_bind` is at that ceiling
(`EffectsTest/Algebra/AxiomReport.lean`).

### 4.3 Battery `Test/Program/DenoteContract.lean` and report `Test/Program/DenoteAxiomReport.lean`

The battery imports `Effect4.Program.Denote`, `Effect4.Api` and `Test.Program.CompileContract`
(for its programs and `exitOf`, `refsOf`, `replayEff`, `evaluateRoot`; if the coordinator
refuses a battery-to-battery import, copy the straight-line programs into the battery under
the same names). For every program `p` of `CompileContract` with `Straight p = true`, two
guards:

```lean
#guard Straight pBindSync = true
#guard (meaning pBindSync [] Stores.empty).1 = (Api.run pBindSync 400).exit.getD outsideExit
#guard (meaning pBindSync [] Stores.empty).2 = (Api.run pBindSync 400).stores
```

These guards are the executable oracle of `run_eq_meaning`, one program at a time; slice 2
replaces them by the theorem and keeps them as its anti-vacuity kit. The rows: `E4-DEN-CE-001`
(`.sync (.var 3)` at the empty environment answers `success unit` on the machine and in the
denotation, `.succeed (.var 3)` answers `die badName` on both), `E4-DEN-CE-002`
(`storeHandler.handle (SyncOp.refGet ⟨5⟩) Stores.empty = (Val.unit, Stores.empty)`, matching
`stores.syncState`'s `none` and the `syncValue` fallback), `E4-DEN-CE-003` (the machine's
trace of `pBindSync` contains frame events and the denotation has none, so the agreement is
on exit and stores).

## 5. Rules every lane follows (from `AGENTS.md`, restated)

- No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`, `implemented_by`,
  bodyless `opaque`. Every new theorem is expected at `propext`/`Quot.sound`; a lane reports
  its `#print axioms` output verbatim.
- A lane edits only its three files. It does not edit `src/Effect4.lean`, `Test/All.lean`,
  `Test/Audit/AxiomGate.lean`, `lakefile.toml`, or any existing module, and never commits or
  `git add`s.
- Every `#guard` is over first-order values; no battery `def` returns rendered text.
- Elaborate with `lake env lean -M4096 <file>`; do not run `lake build` (one `lake` at a time
  in a working tree; the coordinator builds). During development a lane may keep its
  battery's guards at the foot of its module under a `section` and split them out at handoff,
  so that the battery's import of the unbuilt module is never needed.
- Every rc.112 line a definition mirrors is cited in the docstring; the compile's lines are
  the source for lane 3, `Stores.lean`'s for lane 2, `Native.lean`'s and `Typing.lean`'s for
  lane 1.
- If a statement in §2 to §4 turns out false, the lane does not bend the definition to make
  it true: it records the witness as a guard, names the row, and reports the corrected
  statement. The known soft spots are listed in §7.
- The handoff is a report with: the three files, exact `lake env lean` commands and their
  output, the `#print axioms` block, the guards' count, the rows with their witnesses, and
  every statement that changed from this plan with the reason.

## 6. Proof graph (the coordinator cuts `docs/research/DENOTE-DAG.md` from this at landing)

| node | owner | depends on | discharged by |
| --- | --- | --- | --- |
| `TYPED/value` `hasTy`, `Fits` | lane 1 | `Ty`, `Val` | definitions |
| `TYPED/term` `evalTerm_hasTy`, `evalTerm_isSome` | lane 1 | `nativeAtom_typed`, `Lit.toVal_*` | mutual induction |
| `TYPED/row` `syncOpOf_isSome` | lane 1 | `hasTy` | cases |
| `STORES/order` `Stores.le`, `syncOpStep_le` | lane 2 | `refStep_length` | cases |
| `STORES/valid` `validIn`, `WF`, `syncOpStep_isSome_of_valid`, `syncOpStep_wf`, `syncOpStep_answer_valid` | lane 2 | `STORES/order` | cases |
| `DEN/carrier` `StoreSig`, `denote`, `storeHandler`, `meaning` | lane 3 | `Effects.Program`, `Compile`'s helpers | definitions |
| `DEN/equations` `meaning_*` | lane 3 | `Effects.interpret_bind`, `interpret_perform` | the algebra's laws |
| `DEN/oracle` the guards | lane 3 | `Api.run` | `decide` |
| `PROGRESS/answer` `answer_typed`: `WF s → o.validIn s → v.hasTy (row op).request → syncOpOf op v = some o' → syncOpStep o' s = some (s', a) → a.hasTy (row op).answer` | coordinator, after lanes 1 and 2 | `TYPED/row`, `STORES/valid` | cases over the twenty rows |
| `DEN/agreement` `run_eq_meaning` | slice 2 seat | every node above, `Machine/Clauses.lean` | §9 |
| `DEN/trace` agreement under a mask | later | `Effects.Trace` | not this slice |

## 7. Soft spots, known before the lanes start

- `hasTy` on `exitErr` ignores the cause (`TYPED-FB-CAUSE`); if slice 2 needs the error
  column, the refinement is a `Reason`-level check against `.nat` and `Ty.join`'s members.
- `syncOpStep_wf` must handle `refMake initial` where `initial` is itself a handle; the
  hypothesis `SyncOp.validIn` includes the argument, which is why it is not only the key.
- `Stores.WF` says nothing about a `Completion`'s stored program; a Deferred completed with
  `ofRefGet cell` on a dangling cell is not excluded. Row it, do not widen `WF` in this slice.
- `denote (.onExit …)`: confirm against `contAOf (.restore exit)` (`Compile.lean:555`) and
  `contEOf (.restore exit)` (`:577`) that a *succeeding* finalizer restores the body's exit
  unchanged and a failing one merges through `restoreAfterFinalizer`; the finalizer program
  runs under `finalizerOr` (`Fibers.lean:845-870`) and the restore name is the `contA` of an
  `onSuccess` the machine builds. If the machine sequences it through `onSuccessAndFailure`
  with `mergeName` on the failure arm, the two arms agree with `finVoid`; the guards on
  `pOnExit` and a failing-finalizer variant decide it.
- `meaning_perform_sync` needs `LawfulMonad (StateT Stores Id)`; if instance search stalls,
  use `Effects.interpret_bind_of_equations` with `StateT`'s unit and associativity spelled by
  `rfl`.

## 8. The coordinator's landing

1. `lake build Effect4 Test` at the base before the lanes start, so every import the lanes
   need has an olean; record the job count.
2. Receive the three reports; read every changed statement against §2 to §4.
3. Add the three imports to `src/Effect4.lean` and the six to `Test/All.lean`; `lake build
   Effect4 Test`; the gate must report the same admissions as before (no new
   `Classical.choice` crossing).
4. Register the seven rows in `Test/Counterexamples/REGISTER.md` with status SEEDED and their
   witnesses' file names; move the packet's status from RESERVED to SEEDED.
5. Prove `answer_typed` (§6) in a fourth module `src/Effect4/Program/Progress.lean` that
   imports lanes 1 and 2, or leave it to the slice-2 seat; either way it is the first join.
6. `./scripts/test-trust-gate.sh` and `./scripts/sweep.sh --hermetic` per the verification
   cadence; one commit by pathspec, with the packet.

Landed 2026-09-05, the same day: the three lane modules (lanes 1 and 2 by one Fable agent,
lane 3 by the coordinator), and the slice-2 theorem itself in two modules the coordinator
wrote on the same day — `src/Effect4/Program/Agreement.lean` (the frame machine's local run,
§9's layer A) and `src/Effect4/Program/Agreement/Machine.lean` (the command loop over one
fiber, layer B, and `run_eq_meaning`). The proof graph is `docs/research/DENOTE-DAG.md`.
What §9 called `Straight'` is `Plain` (straight minus `onExit`, `E4-DEN-CE-004`); the two
fuels are `depth` (the compile's) and `2 * steps e + 6` (the commands'); the op budget is a
hypothesis `steps e + 2 ≤ defaultBudget` (`E4-DEN-CE-005`).

The same evening: `onExit` went in (`E4-DEN-CE-004` repaired) — the local step's exit arm
`exitFrom` mirrors the machine's `finalizerOr` (the pop answers an `onExit` frame, the
finalizer program runs under the mask, the restoring frame is passed on the way out), the
fiber carries its interruptible flag through the induction, and the theorem reads
`Straight`. And `answer_typed` (§8.5) landed in `src/Effect4/Program/Progress.lean` by a
second agent, with a finding: `Stores.WF` does not type the answers (a `WF` heap may hold a
`bool`), so the join carries a heap typing `Stores.HeapNat` that the typed route preserves
(`E4-PROGRESS-CE-001/002`). The slice-2 machine side will need `HeapNat` beside `WF` when the
typing is joined to the run.

Later the same night: the run past the budget (`E4-DEN-CE-005` repaired) — the theorem lost
its budget hypothesis. The machine of the simulation carries the resume token beside the
trace (each yield takes one); at the loop with the count at `defaultBudget` the injected
iteration parks the root behind a fresh token with its primitive queued on its own
dispatcher (`Myield`, `drive_loop_yield`); `flush` fires that dispatcher and the one task
resumes the root on its guard, re-entering the loop at count zero (`fire_Myield`); the
simulation `drive_localRun` now owes the exit path or a yield with at least
`defaultBudget - 1` fewer steps left (`Owes`), and the rounds of `flush` reach the exited
machine by induction on the rounds (`flushAll_Myield`). The battery's `pLong` (`2100` binds,
`4200` steps) yields twice under the ordinary run; `pLong_agrees` is the theorem on it. Still
owed on this route: joining `HeapNat` to the run; G2's fuel laws are a separate lane
(`docs/research/2026-09-05-fuel-laws.md` when it lands).

## 9. The path of slice 2 (one design seat, after landing)

The statement is §1.1. The proof is one induction on `e` under `Straight`, generalised over
the point's environment, the stores, the outer stack, and the fuel, with this shape:

```
drive_straight : for K (the outer stack), p with p.env = env and enough fuel,
  the run of the root fiber from (current := compileEff e p, stack := K, state := s)
  reaches, before any frame of K is consulted, the state
  (current := Prim.ofExit ex, stack := K, state := s') with (ex, s') = meaning e env s,
  and continues from there exactly as the run from that state would.
```

Three frictions are known and each has a resolution to pick:

- The trace. `drive` appends events (`RunMachine.emit`, `Fibers.lean:454`) and the algebra
  has none. State the lemma on a projection that forgets `trace` (and `currentOpCount`, next
  item), or prove once that `drive` from states equal up to trace ends in states equal up to
  trace (a shift lemma over `emit`). The projection is smaller.
- `Cmd.loop` against `Cmd.deliver`. A `sync` answers through `Outcome.answered` and
  `settle` schedules a `deliver` (`Fibers.lean:1146-1147`, `Clauses.lean:363`), which skips
  `countOp` and `runloopTop`; a compiled `success` is reached through `loop`. With no deferred
  interrupt in the fragment the two agree up to `currentOpCount`; that is one lemma over
  `iteration` (`Fibers.lean:1035`) and `evaluatePrim`.
- The two fuels and the op budget. `cost e` bounds `Point.fuel` by the term's depth so the
  compile never answers `frontier` (`Compile.lean:283`), and bounds the commands; `ops e`
  keeps `injectYield` (`Fibers.lean:753`) silent under `defaultBudget`. Define both
  structurally and prove `drive` monotone in fuel on runs that finish, which
  `flushAll_idle` (`Clauses.lean:247`) already gives for the final `flush`.

The per-constructor steps, with the clause theorems that drive them:
`succeed`/`fail`/`failCause`: zero steps, the compiled primitive is already `ofExit`
(`yieldableError` takes one `stepFrame` step, `Frames.lean:2395`); `sync`:
`evaluatePrim_sync_pure` (`Clauses.lean:351`) then `settle_answered` (`:363`) and
`drive_deliver` (`:394`); `perform`: `evaluatePrim_sync_answers` (`:337`) with `syncState`
unfolding to `syncOpStep`, then the `[Cmd.drainDue]` nested command, a no-op under the
single-fiber invariant `s.deferreds.due = [] ∧ every cell's waiters = []`, which the fragment
preserves because it never registers a waiter; `suspend`/`branch`: `stepFrame` through
`suspendBodyAt`; `bind`: the `onSuccess` push (`Frames.lean:2404-2407`), the inductive
hypothesis at `p.child 0` with `K' := onSuccess … :: K`, then the pop through
`getCont Arm.contA false` answering the pushed frame and `contAOf (.cont p) v =
compileEff b (p.childWith 1 v)`, then the hypothesis at the child; `catchCause`,
`matchCause`, `exit`, `onExit`: the same with `contE`, both arms, `exitFrame`'s `armA`, and
`finalizerOr` (`Fibers.lean:845`). The root case: `getCont` on the empty stack answers
`ContAnswer.empty`, `resumeValue_empty` (`Frames.lean:2442`) yields the exit, `drive_finish`
(`Clauses.lean:406`) and `exitFiber_no_children` (`:919`) set `exit`, and `finished` holds
with one fiber. The single-fiber invariant also carries `fibers = [root]`, `races = []`,
`armed = []`, `pending = []`, `parked = notParked`, `dispatcher = empty`.

This is the neutral-context bind law of review §3 G8 in the machine's own terms: `K` is the
context the inner run never consults. Size: the archived Flow route's T1 was priced at about
250 lines with one induction on fuel; this is larger, because the frame stack is explicit and
there are thirteen constructors. It is one seat's work, not three.
