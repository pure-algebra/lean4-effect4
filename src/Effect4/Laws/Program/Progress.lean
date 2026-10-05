import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.Typed.Adequacy
import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.Template
import Effect4.Laws.Program.Typing.Inversion

/-!
# Program.Progress — a typed `sync` node steps to a typed answer over a typed store

The straight theorems' store half and their one store step (decisions row 209; the state plan's
T1, `docs/research/2026-10-04-claude-lead/state-any-type-plan.md` §3). Packet:
`Test/contracts/program-denotation.contract.md`. Battery: `Test/Program/ProgressContract.lean`
(the register rows `E4-PROGRESS-CE-001`, `E4-PROGRESS-CE-002` and the coarse-column red control).

* **The store half at a world** (`Denote.StoreFits`): the cell columns (`Typed.CellsTyped`,
  `Typed/Adequacy.lean`: the world declares exactly the allocated cells and Deferred cells, and every
  stored value fits its declared type by `Fits`) and `Stores.WF`. The typed state's `StoreTyped`
  shares the cell columns, so they are defined once. The coarse column `HeapTable` (`Val.hasTy` at a
  cell's declaration) is not enough: it accepts any cell handle at `Ref<A>`, so a nested read loses
  the inner cell's declaration (the red control in the battery).
* **`progress`, at the `perform` node**: a typed `sync` node, in an environment typed at a world whose
  store fits, denotes one store operation, which steps (no frontier) to an answer of the node's type
  at a later world whose store fits again. The request decodes and the row's pre holds by the typed
  state's `syncRow_typed`; the step and the new cell columns are the row's `CellImplements`; the
  answer's type is `syncRow_typed`'s continuation; well-formedness moves by `StoreFits.step`.
  Stated at the node, it names no row, no decoder and no function name, so the rows of the state
  plan's T3 (templates, terms in rows) change its proof and not its statement.

Since the state plan's T3a the `Ref` and `Deferred` rows are templates: `progress` reads the node's
checked instance (`syncRow_typed`), so a cell or a deferred is declared at the instance's types.
The statements quantify over every world.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine
open Conform.Effect4.Typing (inv_perform)

/-! ## The store half at a world -/

namespace Denote

/-- **The store half at a world**: the cell columns the typed state shares (`Typed.CellsTyped`) and
`Stores.WF`: every cell holds a value of its declared type. -/
structure StoreFits (w : Typed.World) : Prop extends Typed.CellsTyped w where
  wf : w.state.WF

/-- **After a run from `w`**: a later world in the host order whose store fits again. -/
structure StoreOk (w w' : Typed.World) : Prop where
  le : w.leHost w'
  store : StoreFits w'

theorem StoreOk.refl {w : Typed.World} (h : StoreFits w) : StoreOk w w := ⟨Typed.leHost_refl w, h⟩

theorem StoreOk.trans {a b c : Typed.World} (hab : StoreOk a b) (hbc : StoreOk b c) :
    StoreOk a c :=
  ⟨Typed.leHost_trans a b c hab.le hbc.le, hbc.store⟩

/-- **The store half moves along a store step** whose cell columns are typed at the new world: every
stored value is valid there (`CellsTyped.fits_validIn`), and the step keeps the closing exits'
validity, the memo entries and the timers (`Stores.WF`'s other clauses). -/
theorem StoreFits.step {w w' : Typed.World} {o : SyncOp} {st' : Stores} {a : Val}
    (store : StoreFits w) (step : syncOpStep o w.state = some (st', a)) (hstate : w'.state = st')
    (cells : Typed.CellsTyped w') : StoreFits w' := by
  refine ⟨cells, ?_⟩
  rw [hstate]
  exact Typed.CellsTyped.wf_step store.wf step hstate cells

end Denote

/-! ## The faces' images agree with the names on every number (the state plan's T3b)

Until the state plan's T5 the faces spell a read-modify-write row's binder term by a name
(`FnName.image`, `Program/FnName.lean`). The image of a name at a shape and a node's level
evaluates, on every number and over every outer environment, to the value the name answers at
that shape (`FnName.valueAt`). Before the rows carried terms a row named its function and
`syncOpOf` handed the store the name's lowering at level 0; on every number that lowering
evaluated to the same value (`FnName.lowering_agrees` and `FnName.image_agrees_lowering` at
`git:0ab2ef09:src/Effect4/Program/FnName.lean` and
`git:0ab2ef09:src/Effect4/Laws/Program/Progress.lean`, proved before the lowerings were deleted).
So a program that named its function runs the same store step on a number cell now that its row
carries the name's image. Two names whose plain terms would repeat have distinct images
(`takeAndBump` at `add(a, 1)`, `zeroWhenPositive` at `add(a, 0)`), and the agreement is what
says the re-imaging moves no value. On a value that is not a number an image of a computing name
stops, since every atom that reads a number refuses any other value: the step is a frontier
there, as it has been since the store ran terms (decisions row 43). -/

/-- **The image of a name agrees with the name on every number**, at every shape, level and outer
environment: at `env ++ [n]` the image at level `env.length` evaluates to the name's value at the
shape. -/
@[semantics "translation-simulation" (requirement := R4)]
theorem _root_.Effect4.Machine.FnName.image_agrees (s : FnShape) (f : FnName) (env : List Val)
    (n : Nat) :
    evalTerm (env ++ [Val.nat n]) (FnName.image s env.length f) = some (f.valueAt s (.nat n)) := by
  rw [FnName.image_eval]
  cases s
  case updateSome =>
    cases f
    case zeroWhenPositive => cases n <;> rfl
    all_goals rfl
  all_goals cases f <;> rfl

/-! ## The native rows' store steps, one row each -/

/-- **Each native `sync` row fulfils itself on the cell columns**: the store operation a request
decodes to is one of the native table's, whose `CellImplements` (`Typed/Adequacy.lean`) holds. One
case a row, `syncOpOf`'s own: the twelve heap kernels by `kernel_cellImplements`, the allocations,
the Deferred reads and completions, the scope and the clock by theirs. -/
theorem NativeOp.syncOpOf_cellImplements (root : Typed.ProgramSource) {op : NativeOp}
    {env : List Val} {v : Val} {o : SyncOp} (ho : NativeOp.syncOpOf op env v = some o) :
    Typed.CellImplements root o := by
  unfold NativeOp.syncOpOf at ho
  split at ho <;> cases ho
  case h_1 => exact Typed.refMake_cellImplements root _
  case h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_8 | h_9 | h_10 | h_11 | h_12 | h_13 =>
    exact Typed.kernel_cellImplements root rfl
  case h_14 => exact Typed.deferredMake_cellImplements root
  case h_15 k => exact Typed.deferredIsDone_cellImplements root ⟨k⟩
  case h_16 k => exact Typed.deferredPoll_cellImplements root ⟨k⟩
  case h_17 | h_18 => exact Typed.deferredCompleteWith_cellImplements root _ _
  case h_19 strategy => exact Typed.scopeMake_cellImplements root strategy
  case h_20 => exact Typed.clockNow_cellImplements root

/-! ## Progress -/

/-- **A typed `sync` node steps to a typed answer** (progress of `syncOpStep` at the node, and
preservation of the store half along it): in an environment typed at a world whose store fits, the
node denotes one store operation, which steps (no frontier) to an answer of the node's type at a
later world whose store fits again. -/
theorem progress (op : NativeOp) (r : Term) (tys : TyEnv) (env : List Val) (w : Typed.World)
    (t : EffTy) (hkind : (NativeOp.row op).kind = .sync)
    (hty : effTy nativeSignature tys (.perform op r) = some t)
    (henv : Typed.EnvTyped w tys env) (store : Denote.StoreFits w) :
    ∃ o w' a, Denote.denote (.perform op r) env =
        Effects.Program.bind (Effects.Program.perform (S := Denote.StoreSig) o)
          (fun v => pure (Exit.success v)) ∧
      syncOpStep o w.state = some (w'.state, a) ∧ Denote.StoreOk w w' ∧
      Typed.Fits w' a t.answer := by
  obtain ⟨requestTy, _, hr, hrow⟩ := inv_perform nativeSignature tys op r t hty
  obtain ⟨x, hx, hxfit⟩ := Typed.evalTerm_progress (sig := nativeSignature) rfl
    (Typed.fitsAll_of_pointwise henv.1 henv.2) r requestTy hr
  have hrowOf : nativeSignature.rowOf op = (NativeOp.row op).normalizeTypes := by
    show (nativeRowOf [] op).normalizeTypes = _
    rw [nativeRowOf_nil]
  rw [hrowOf] at hrow
  have hk : NativeOp.kind op = .sync := by
    rw [← NativeOp.row_kind]
    exact hkind
  let root : Typed.ProgramSource := { program := .perform op r }
  have hsig : root.signature = nativeSignature := rfl
  rw [← hsig] at hrow
  obtain ⟨o, ho, typed⟩ := Typed.syncRow_typed root (req := Env.Requirement.empty) op hk henv
    hrow x hxfit
  obtain ⟨cert, pre, next⟩ := Typed.TypedProg.store_inv typed
  obtain ⟨st', a, step, w', ord, hstate, cells, post⟩ :=
    NativeOp.syncOpOf_cellImplements root ho w cert store.toCellsTyped pre
  have hans := (Typed.TypedProg.pure_inv (next w' ord a post)).1
  refine ⟨o, w', a, ?_, by rw [step, hstate], ⟨ord, store.step step hstate cells⟩, ?_⟩
  · rw [Denote.denote]
    simp only [hkind, hx, Option.bind_some, ho]
  · exact hans

end Effect4.Program
