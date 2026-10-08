import Effect4.Laws.Program.Progress

/-!
# Progress contract — a typed `sync` node steps to a typed answer, frozen

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §6, node `PROGRESS/answer`; restated at
a world by decisions row 209 (the state plan's T1). Packet:
`Test/contracts/program-denotation.contract.md`. The module under contract is
`src/Effect4/Laws/Program/Progress.lean`, the first join of lanes 1 and 2.

Every obligation below is ascribed at its exact proposition and supplied by name with `@`, so
a declaration that keeps the frozen name but weakens the statement fails here
(`Test/Program/ProvisionContract.lean` is the model). The executable receipts are `#guard`s
over first-order values: the store operations the compile contract's programs perform
(`Test/Program/CompileContract.lean`: `pRefSet`, `pRefUpdate`, `pRefModify`), one Deferred and
one Scope sequence for the store rows, the pure functions on numbers, and the two register rows.
Every helper is a store or an answer, never a rendering. The read-modify-write rows carry binder
terms (decisions row 43; the state plan's T3b): the compile contract's programs carry the images
of their names at the node's level, run over the point's environment. On numbers an image
evaluates to the name's value (`FnName.image_agrees`), and on a non-number a computing name's
image stops, where the name answered the value unchanged (the guards of section `Functions`).
`Stores.WF` is decided through the
instance the modules supply. The `Ref` and `Deferred` rows are templates since the state plan's
T3a: every guard reads a row at its `nat` instance (`atNat`), the instance the compile contract's
programs check at, and every cell they reach holds a number, the guard `refs.all (Val.hasTy · .nat)`.
`Val.hasTy` is well-founded, so its guards are evaluations, never `decide`.

Register rows (`Test/Counterexamples/REGISTER.md`), each a group of guards and a theorem at worlds:

* `E4-PROGRESS-CE-001` — a well-formed store answers typed values, so `progress` needs no more
  than `Stores.WF`. Refuted: the heap `[Val.bool true]` is `WF`, `refGet ⟨0⟩` is valid in it,
  and its answer `Val.bool true` has not the answer type `.nat` of the row's `nat` instance. At a
  world where the request `Val.cell ⟨0⟩` fits that instance's request type, the cell columns fail
  (`ce001_columns`); `progress` carries them (`Denote.StoreFits`).
* `E4-PROGRESS-CE-002` — the store half survives every valid step, so `progress` can be stated
  on `SyncOp.validIn`. Refuted: `refMake (Val.bool true)` is valid on the empty store and steps;
  no world over the store it leaves has typed cell columns and admits its answer at the answer
  type of the row's `nat` instance (`ce002_answer`). `progress` is stated on a typed `perform`
  node: the decoder reads any value since T3a, and the node's checked instance is what keeps the
  columns (`Val.bool true` checks `refMake` at `bool`, whose answer `refOf bool` the store's
  column then declares).

The red control of the coarse column (the seat's design note, finding F3): `HeapTable` reads a
stored value with `Val.hasTy`, which accepts every cell handle at `Ref<A>` (decisions row 44).
At `coarseWorld` cell 0 is declared at `Ref<number>` and holds the handle of cell 1, which is
declared at `string`. The coarse column holds there (`coarseWorld_heapTable`) and the cell
columns fail (`coarseWorld_not_cells`), so a read through cell 0 would answer a string at
`number` under the coarse column.
-/

set_option autoImplicit false

namespace Test.Program.ProgressContract

open Effect4
open Effect4.Machine
open Effect4.Program

/-! ## Harness: stores reached by one step, and the answers -/

/-- The store after one step, or the store it started from when the step refuses. -/
def after (o : SyncOp) (s : Stores) : Stores := ((syncOpStep o s).map Prod.fst).getD s

/-- The answer of one step. -/
def answer (o : SyncOp) (s : Stores) : Option Val := (syncOpStep o s).map Prod.snd

/-- `Ref.make(5)` on the empty store: the first step of `pRefSet`, `pRefUpdate` and
`pRefModify`. -/
def s1 : Stores := after (SyncOp.refMake (Val.nat 5)) Stores.empty
/-- `Ref.set(ref, 7)` after `Ref.make(5)`: `pRefSet`'s second step. -/
def s1set : Stores := after (SyncOp.refSet ⟨0⟩ (Val.nat 7)) s1
/-- The environment of `pRefUpdate`'s and `pRefModify`'s second node: the cell bound in front. -/
def cellEnv : List Val := [Val.cell ⟨0⟩]
/-- `incr`'s image at that node's level 1, `succ(var 1)`: `pRefUpdate`'s binder term. -/
def incrAt1 : Term := FnName.image .update 1 .incr
/-- `takeAndBump`'s image at level 1, `pair(var 1, add(var 1, 1))`: `pRefModify`'s binder term. -/
def bumpAt1 : Term := FnName.image .modify 1 .takeAndBump
/-- `Ref.update(ref, incr)` after `Ref.make(5)`: `pRefUpdate`'s second step, running its term at
the node's environment (decisions row 43). -/
def s1upd : Stores := after (SyncOp.refUpdate ⟨0⟩ incrAt1 cellEnv) s1
/-- `Ref.modify(ref, takeAndBump)` after `Ref.make(5)`: `pRefModify`'s second step. -/
def s1mod : Stores := after (SyncOp.refModify ⟨0⟩ bumpAt1 cellEnv) s1
/-- `Deferred.make()` on the empty store. -/
def s2 : Stores := after SyncOp.deferredMake Stores.empty
/-- `Deferred.succeed(d, 1)` after `Deferred.make()`. -/
def s2done : Stores :=
  after (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) s2
/-- A row's type at the `nat` instance, the one the battery's programs check at. -/
def atNat (t : Ty) : Ty := t.instantiate [(0, .nat), (1, .nat)]

/-- A heap holding a boolean: well-formed, not numeric. -/
def boolCell : Stores := { Stores.empty with refs := [Val.bool true] }

/-- `pRefSet`'s `Ref.set` request: the pair of the cell and the number. -/
def setRequest : Val := Val.tuple [Val.cell ⟨0⟩, Val.nat 7]
/-- `Deferred.succeed`'s request: the pair of the promise and the number. -/
def succeedRequest : Val := Val.tuple [Val.promise ⟨0⟩, Val.nat 1]

/-! ## The obligation, ascribed -/

/-- `progress`, at its exact proposition. -/
example : ∀ (op : NativeOp) (r : Term) (tys : TyEnv) (env : List Val) (w : Typed.World)
    (t : EffTy), (NativeOp.row op).kind = .sync →
    effTy nativeSignature tys (.perform op r) = some t →
    Typed.EnvTyped w tys env → Denote.StoreFits w →
    ∃ o w' a, Denote.denote (.perform op r) env =
        Effects.Program.bind (Effects.Program.perform (S := Denote.StoreSig) o)
          (fun v => pure (Exit.success v)) ∧
      syncOpStep o w.state = some (w'.state, a) ∧ Denote.StoreOk w w' ∧
      Typed.Fits w' a t.answer :=
  @progress

/-- The store half at a world: the cell columns and `Stores.WF`. -/
example (w : Typed.World) : Denote.StoreFits w ↔ Typed.CellsTyped w ∧ w.state.WF :=
  ⟨fun h => ⟨h.toCellsTyped, h.wf⟩, fun h => ⟨h.1, h.2⟩⟩

/-- After a run: a later world in the host order whose store fits. -/
example (w w' : Typed.World) : Denote.StoreOk w w' ↔ w.leHost w' ∧ Denote.StoreFits w' :=
  ⟨fun h => ⟨h.le, h.store⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The cutover's connector (the state plan's T3b), at its exact proposition: the image of a name
at a shape and a node's level evaluates, on every number and over every outer environment, to the
name's value at the shape. -/
example : ∀ (s : FnShape) (f : FnName) (env : List Val) (n : Nat),
    Program.evalTerm (env ++ [Val.nat n]) (FnName.image s env.length f) =
      some (f.valueAt s (.nat n)) :=
  @FnName.image_agrees

/-! ## The register rows -/

section Rows

/-- At a world whose cell columns are typed and whose cell 0 holds a boolean, the cell's handle
does not fit `refOf nat`, which reads a cell declared at a type equivalent to `nat`. -/
theorem bool_cell_not_ref (w : Typed.World) (cells : Typed.CellsTyped w)
    (h0 : w.state.refs[0]? = some (Val.bool true)) :
    ¬ Typed.Fits w (Val.cell ⟨0⟩) (.refOf .nat) := by
  intro hfit
  obtain ⟨k, hk, t, declared, equiv⟩ := Typed.fits_refOf_inv hfit
  cases k with
  | mk index =>
    cases hk
    obtain ⟨n, hn⟩ :=
      Typed.fits_nat_inv (Typed.fits_subN w equiv.1 _ (cells.values 0 _ h0 t declared))
    cases hn

-- E4-PROGRESS-CE-001: `WF` is the handle half only; the answer's type needs the cell columns
#guard Stores.WF boolCell
#guard SyncOp.validIn boolCell (SyncOp.refGet ⟨0⟩) = true
#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row .refGet).request)
#guard NativeOp.syncOpOf .refGet [] (Val.cell ⟨0⟩) = some (SyncOp.refGet ⟨0⟩)
#guard answer (SyncOp.refGet ⟨0⟩) boolCell = some (Val.bool true)
#guard Val.hasTy (Val.bool true) (atNat (NativeOp.row .refGet).answer) = false
#guard !boolCell.refs.all (Val.hasTy · .nat)

/-- `E4-PROGRESS-CE-001` at worlds: over the heap `[Val.bool true]`, a world at which `refGet`'s
request `Val.cell ⟨0⟩` fits the row's request type has no typed cell columns. -/
theorem ce001_columns (w : Typed.World) (hs : w.state = boolCell)
    (hreq : Typed.Fits w (Val.cell ⟨0⟩) (atNat (NativeOp.row .refGet).request)) :
    ¬ Typed.CellsTyped w :=
  fun cells => bool_cell_not_ref w cells (by rw [hs]; rfl) hreq

-- E4-PROGRESS-CE-002: validity does not keep the cell columns at the row's types; the typed
-- request does
#guard Stores.empty.refs.all (Val.hasTy · .nat)
#guard SyncOp.validIn Stores.empty (SyncOp.refMake (Val.bool true)) = true
#guard (syncOpStep (SyncOp.refMake (Val.bool true)) Stores.empty).isSome
#guard answer (SyncOp.refMake (Val.bool true)) Stores.empty = some (Val.cell ⟨0⟩)
#guard !(after (SyncOp.refMake (Val.bool true)) Stores.empty).refs.all (Val.hasTy · .nat)
#guard Val.hasTy (Val.bool true) (atNat (NativeOp.row .refMake).request) = false
-- the decoder reads any value since the state plan's T3a: the instance keeps the column
#guard NativeOp.syncOpOf .refMake [] (Val.bool true) = some (SyncOp.refMake (Val.bool true))

/-- `E4-PROGRESS-CE-002` at worlds: no world over the store `refMake (Val.bool true)` leaves has
typed cell columns and admits the answer `Val.cell ⟨0⟩` at the row's answer type. -/
theorem ce002_answer (w : Typed.World)
    (hs : w.state = after (SyncOp.refMake (Val.bool true)) Stores.empty)
    (cells : Typed.CellsTyped w) :
    ¬ Typed.Fits w (Val.cell ⟨0⟩) (atNat (NativeOp.row .refMake).answer) := by
  refine bool_cell_not_ref w cells ?_
  rw [hs, after, Typed.syncOpStep_refMake]
  rfl

end Rows

/-! ## The red control of the coarse column -/

section Coarse

/-- Cell 0 declared at `Ref<number>` holds the handle of cell 1, declared at `string`, which holds
a string. -/
def coarseWorld : Typed.World :=
  { Typed.initialWorld (EffTy.pure .unit) with
    state := { Stores.empty with refs := [Val.cell ⟨1⟩, Val.str "s"] }
    Ρ := fun k => if k.index = 0 then some (.refOf .nat) else if k.index = 1 then some .string
      else none }

-- the coarse leaf accepts the inner handle at `Ref<number>`: handles carry no type in `hasTy`
#guard Val.hasTy (Val.cell ⟨1⟩) (.refOf .nat)
#guard Val.hasTy (Val.str "s") (.refOf .nat) = false

/-- The coarse column holds at `coarseWorld`. -/
theorem coarseWorld_heapTable : Typed.HeapTable coarseWorld := by
  intro i v hv ty hty
  match i, hv, hty with
  | 0, hv, hty =>
    cases hv
    cases hty
    show Val.hasTy (Val.cell ⟨1⟩) (.refOf .nat) [] = true
    simp only [Val.hasTy]
    rfl
  | 1, hv, hty =>
    cases hv
    cases hty
    show Val.hasTy (Val.str "s") .string [] = true
    simp only [Val.hasTy]
  | _ + 2, hv, _ => cases hv

/-- The cell columns fail at `coarseWorld`: the handle in cell 0 fits `Ref<number>` only if
cell 1 is declared equivalent to `nat`, and it is declared at `string`. -/
theorem coarseWorld_not_cells : ¬ Typed.CellsTyped coarseWorld := by
  intro cells
  have h := cells.values 0 (Val.cell ⟨1⟩) rfl (.refOf .nat) rfl
  obtain ⟨t, declared, equiv⟩ : Typed.RefDeclared coarseWorld ⟨1⟩ .nat := h
  cases declared
  obtain ⟨n, hn⟩ := Typed.fits_nat_inv (Typed.fits_subN coarseWorld equiv.1 (Val.str "s") trivial)
  cases hn

end Coarse

/-! ## `pRefSet`: `Ref.make(5)`, `Ref.set(ref, 7)`, `Ref.get(ref)` -/

section RefSet

-- `Ref.make(5)` on the empty store
#guard Stores.empty.refs.all (Val.hasTy · .nat)
#guard Val.hasTy (Val.nat 5) (atNat (NativeOp.row .refMake).request)
#guard NativeOp.syncOpOf .refMake [] (Val.nat 5) = some (SyncOp.refMake (Val.nat 5))
#guard SyncOp.validIn Stores.empty (SyncOp.refMake (Val.nat 5)) = true
#guard answer (SyncOp.refMake (Val.nat 5)) Stores.empty = some (Val.cell ⟨0⟩)
#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row .refMake).answer)
#guard Val.validIn s1 (Val.cell ⟨0⟩)
#guard Stores.WF s1
#guard s1.refs.all (Val.hasTy · .nat)
#guard s1.refs = [Val.nat 5]

-- `Ref.set(ref, 7)`: the request is the pair, the answer is the cell
#guard Val.hasTy setRequest (atNat (NativeOp.row .refSet).request)
#guard Val.validIn s1 setRequest
#guard NativeOp.syncOpOf .refSet [] setRequest = some (SyncOp.refSet ⟨0⟩ (Val.nat 7))
#guard SyncOp.validIn s1 (SyncOp.refSet ⟨0⟩ (Val.nat 7)) = true
#guard answer (SyncOp.refSet ⟨0⟩ (Val.nat 7)) s1 = some (Val.cell ⟨0⟩)
#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row .refSet).answer)
#guard Val.validIn s1set (Val.cell ⟨0⟩)
#guard Stores.WF s1set
#guard s1set.refs.all (Val.hasTy · .nat)
#guard s1set.refs = [Val.nat 7]

-- `Ref.get(ref)`: the answer is the cell's number
#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row .refGet).request)
#guard NativeOp.syncOpOf .refGet [] (Val.cell ⟨0⟩) = some (SyncOp.refGet ⟨0⟩)
#guard SyncOp.validIn s1set (SyncOp.refGet ⟨0⟩) = true
#guard answer (SyncOp.refGet ⟨0⟩) s1set = some (Val.nat 7)
#guard Val.hasTy (Val.nat 7) (atNat (NativeOp.row .refGet).answer)
#guard after (SyncOp.refGet ⟨0⟩) s1set = s1set

end RefSet

/-! ## `pRefUpdate`: `Ref.make(5)`, `Ref.update(ref, incr)`, `Ref.get(ref)` -/

section RefUpdate

#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row (.refUpdateWith incrAt1)).request)
-- the row hands the store its own term and the node's environment
#guard NativeOp.syncOpOf (.refUpdateWith incrAt1) cellEnv (Val.cell ⟨0⟩)
  = some (SyncOp.refUpdate ⟨0⟩ incrAt1 cellEnv)
#guard SyncOp.validIn s1 (SyncOp.refUpdate ⟨0⟩ incrAt1 cellEnv) = true
#guard answer (SyncOp.refUpdate ⟨0⟩ incrAt1 cellEnv) s1 = some Val.unit
#guard Val.hasTy Val.unit (atNat (NativeOp.row (.refUpdateWith incrAt1)).answer)
-- red control: the level-1 term over the empty environment reads past the cell's value
#guard answer (SyncOp.refUpdate ⟨0⟩ incrAt1 []) s1 = none
#guard Stores.WF s1upd
#guard s1upd.refs.all (Val.hasTy · .nat)
#guard s1upd.refs = [Val.nat 6]
#guard answer (SyncOp.refGet ⟨0⟩) s1upd = some (Val.nat 6)
#guard Val.hasTy (Val.nat 6) (atNat (NativeOp.row .refGet).answer)

end RefUpdate

/-! ## `pRefModify`: `Ref.make(5)`, `Ref.modify(ref, takeAndBump)` -/

section RefModify

#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row (.refModifyWith bumpAt1)).request)
#guard NativeOp.syncOpOf (.refModifyWith bumpAt1) cellEnv (Val.cell ⟨0⟩)
  = some (SyncOp.refModify ⟨0⟩ bumpAt1 cellEnv)
#guard SyncOp.validIn s1 (SyncOp.refModify ⟨0⟩ bumpAt1 cellEnv) = true
#guard answer (SyncOp.refModify ⟨0⟩ bumpAt1 cellEnv) s1 = some (Val.nat 5)
-- the row answers its own parameter `B`, `var 1`, here at the `nat` instance
#guard (NativeOp.row (.refModifyWith bumpAt1)).answer = .var 1
#guard Val.hasTy (Val.nat 5) (atNat (NativeOp.row (.refModifyWith bumpAt1)).answer)
#guard Stores.WF s1mod
#guard s1mod.refs.all (Val.hasTy · .nat)
#guard s1mod.refs = [Val.nat 6]

end RefModify

/-! ## The names' meaning on numbers (`FnName.total` and its siblings, `Program/FnName.lean`) -/

section Functions

#guard Val.hasTy (FnName.total .incr (Val.nat 5)) .nat
#guard Val.hasTy (FnName.total .double (Val.nat 5)) .nat
#guard Val.hasTy (FnName.total .noChange (Val.nat 5)) .nat
#guard (FnName.partialUpdate .zeroWhenPositive (Val.nat 5)).map (Val.hasTy · .nat) = some true
#guard FnName.partialUpdate .zeroWhenPositive (Val.nat 0) = none
#guard FnName.partialUpdate .noChange (Val.nat 5) = none
#guard Val.hasTy (FnName.modify .takeAndBump (Val.nat 5)).1 .nat
#guard Val.hasTy (FnName.modify .takeAndBump (Val.nat 5)).2 .nat
#guard Val.hasTy (FnName.modifySome .noChange (Val.nat 5)).1 .nat
#guard Val.hasTy ((FnName.modifySome .noChange (Val.nat 5)).2.getD (Val.nat 5)) .nat
-- the functions fix a non-number, so the typing of the result is the typing of the argument
#guard Val.hasTy (FnName.total .incr (Val.bool true)) .nat = false
-- the connector holds on numbers only (`FnName.image_agrees`; the state plan's T2, ruling D1): a
-- computing name fixes a non-number, and its image stops there; `noChange`'s image is the value
#guard FnName.total .incr (Val.bool true) = Val.bool true
#guard Program.evalTerm [Val.bool true] (FnName.image .update 0 .incr) = none
#guard FnName.modify .incr (Val.bool true) = (Val.bool true, Val.bool true)
#guard Program.evalTerm [Val.bool true] (FnName.image .modify 0 .incr) = none
#guard FnName.partialUpdate .zeroWhenPositive (Val.bool true) = none
#guard Program.evalTerm [Val.bool true] (FnName.image .updateSome 0 .zeroWhenPositive) = none
#guard Program.evalTerm [Val.bool true] (FnName.image .update 0 .noChange) =
  some (FnName.total .noChange (Val.bool true))
-- on numbers every image evaluates to its name's value, at levels 0 to 3 over outer values that
-- are no numbers (a finite reading of `FnName.image_agrees`)
#guard [FnShape.update, .updateSome, .modify, .modifySome].all fun s =>
  fnNames.all fun f => (List.range 4).all fun level => [0, 1, 5].all fun k =>
    Program.evalTerm (List.replicate level (Val.bool true) ++ [Val.nat k])
        (FnName.image s level f) == some (f.valueAt s (Val.nat k))
-- on a number the row at a name's image runs the name's function
#guard answer (SyncOp.refUpdate ⟨0⟩ (FnName.image .update 0 .double) []) s1 = some Val.unit
#guard (after (SyncOp.refUpdate ⟨0⟩ (FnName.image .update 0 .double) []) s1).refs = [Val.nat 10]
#guard answer (SyncOp.refUpdateSomeAndGet ⟨0⟩ (FnName.image .updateSome 0 .zeroWhenPositive) [])
  s1 = some (Val.nat 0)
#guard answer (SyncOp.refModifySome ⟨0⟩ (FnName.image .modifySome 0 .noChange) []) s1 =
  some (Val.nat 5)

end Functions

/-! ## T2's lowerings against the images (the state plan's T3b, ruling D5 (b))

Before the rows carried terms a row named its function, and `syncOpOf` handed the store the
name's lowering: one term per shape, the cell's value at level 0 (seat T2;
`git:0ab2ef09:src/Effect4/Program/FnName.lean`). The cutover deleted the lowerings from the
library. They are kept here as they were written, so that their agreement with the faces' images
stays a theorem: on every number, at every shape, name, level and outer environment, a name's
image evaluates as its lowering did. Two pairs of names shared a lowering at a shape (`incr` with
`takeAndBump`, `zeroWhenPositive` with `noChange`). The images separate them (`takeAndBump` at
`add(a, 1)`, `zeroWhenPositive` at `add(a, 0)`), and the theorem says that this moved no value on
a number. -/

namespace T2

/-- T2's term of a name at `A → A`. -/
def updateTerm : FnName → Term
  | .incr | .takeAndBump => .app "succ" (.cons (.var 0) .nil)
  | .double => .app "mul" (.cons (.var 0) (.cons (.lit (.nat 2)) .nil))
  | .zeroWhenPositive | .noChange => .var 0

/-- T2's term of a name at `A → Option<A>`. -/
def updateSomeTerm : FnName → Term
  | .noChange => .app "none" .nil
  | .zeroWhenPositive =>
    .app "ite" (.cons (.app "lt" (.cons (.lit (.nat 0)) (.cons (.var 0) .nil)))
      (.cons (.app "some" (.cons (.lit (.nat 0)) .nil)) (.cons (.app "none" .nil) .nil)))
  | f => .app "some" (.cons (updateTerm f) .nil)

/-- T2's term of a name at `A → [B, A]`. -/
def modifyTerm (f : FnName) : Term := .app "pair" (.cons (.var 0) (.cons (updateTerm f) .nil))

/-- T2's term of a name at `A → [B, Option<A>]`. -/
def modifySomeTerm : FnName → Term
  | .noChange => .app "pair" (.cons (.var 0) (.cons (.app "none" .nil) .nil))
  | f => .app "pair" (.cons (.var 0) (.cons (.app "some" (.cons (updateTerm f) .nil)) .nil))

/-- T2's lowering of a name at a shape. -/
def lowering (f : FnName) : FnShape → Term
  | .update => updateTerm f
  | .updateSome => updateSomeTerm f
  | .modify => modifyTerm f
  | .modifySome => modifySomeTerm f

/-- On every number T2's lowering evaluates to the name's value at the shape. -/
theorem lowering_agrees (f : FnName) (s : FnShape) (n : Nat) :
    Program.evalTerm [.nat n] (lowering f s) = some (f.valueAt s (.nat n)) := by
  cases s
  case updateSome =>
    cases f
    case zeroWhenPositive => cases n <;> rfl
    all_goals rfl
  all_goals cases f <;> rfl

/-- **A name's image evaluates as T2's lowering did**, on every number, at every shape, name and
outer environment: the image at the node's level over `env ++ [n]`, the lowering over `[n]`. -/
theorem image_agrees_lowering (s : FnShape) (f : FnName) (env : List Val) (n : Nat) :
    Program.evalTerm (env ++ [Val.nat n]) (FnName.image s env.length f) =
      Program.evalTerm [Val.nat n] (lowering f s) := by
  rw [FnName.image_agrees, lowering_agrees]

-- The lowerings repeated a term where the images do not: the two pairs of names.
#guard lowering .incr .update = lowering .takeAndBump .update
#guard FnName.image .update 0 .incr != FnName.image .update 0 .takeAndBump
#guard lowering .zeroWhenPositive .update = lowering .noChange .update
#guard FnName.image .update 0 .zeroWhenPositive != FnName.image .update 0 .noChange
-- The agreement's reach is the numbers. On a boolean `zeroWhenPositive`'s lowering at `update`
-- answered the value, and its image `add(a, 0)` stops.
#guard Program.evalTerm [Val.bool true] (lowering .zeroWhenPositive .update) = some (Val.bool true)
#guard Program.evalTerm [Val.bool true] (FnName.image .update 0 .zeroWhenPositive) = none

end T2

/-! ## The Deferred rows (`Stores.lean:1210-1219`) -/

section Deferred

#guard Val.hasTy Val.unit (atNat (NativeOp.row (.deferredMakeOf .nat .nat)).request)
#guard NativeOp.syncOpOf (.deferredMakeOf .nat .nat) [] Val.unit = some SyncOp.deferredMake
#guard answer SyncOp.deferredMake Stores.empty = some (Val.promise ⟨0⟩)
#guard Val.hasTy (Val.promise ⟨0⟩) (atNat (NativeOp.row (.deferredMakeOf .nat .nat)).answer)
#guard Val.validIn s2 (Val.promise ⟨0⟩)
#guard Stores.WF s2
#guard s2.refs.all (Val.hasTy · .nat)

#guard Val.hasTy succeedRequest (atNat (NativeOp.row .deferredSucceed).request)
#guard Val.validIn s2 succeedRequest
#guard NativeOp.syncOpOf .deferredSucceed [] succeedRequest
  = some (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1))))
#guard SyncOp.validIn s2
  (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) = true
#guard answer
  (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 1)))) s2
  = some (Val.bool true)
#guard Val.hasTy (Val.bool true) (atNat (NativeOp.row .deferredSucceed).answer)
#guard Stores.WF s2done
#guard s2done.refs.all (Val.hasTy · .nat)

#guard Val.hasTy (Val.promise ⟨0⟩) (atNat (NativeOp.row .deferredIsDone).request)
#guard NativeOp.syncOpOf .deferredIsDone [] (Val.promise ⟨0⟩)
  = some (SyncOp.deferredIsDone ⟨0⟩)
#guard answer (SyncOp.deferredIsDone ⟨0⟩) s2done = some (Val.bool true)
#guard Val.hasTy (Val.bool true) (atNat (NativeOp.row .deferredIsDone).answer)
#guard answer (SyncOp.deferredPoll ⟨0⟩) s2 = some (Val.bool false)
#guard Val.hasTy (Val.bool false) (atNat (NativeOp.row .deferredPoll).answer)

-- the async row decodes to nothing: `progress` is stated at `sync` rows only
#guard (NativeOp.row .deferredAwait).kind = .async
#guard NativeOp.syncOpOf .deferredAwait [] (Val.promise ⟨0⟩) = none

end Deferred

/-! ## The Scope row (`Stores.lean:1227-1229`) -/

section Scope

#guard Val.hasTy Val.unit (NativeOp.row (.scopeMake .sequential)).request
#guard NativeOp.syncOpOf (.scopeMake .sequential) [] Val.unit = some (SyncOp.scopeMake .sequential)
#guard answer (SyncOp.scopeMake .sequential) Stores.empty = some (Val.scopeHandle 0)
#guard Val.hasTy (Val.scopeHandle 0) (NativeOp.row (.scopeMake .sequential)).answer
#guard Val.hasTy (Val.scopeHandle 0) (NativeOp.row (.scopeMake .parallel)).answer
#guard Val.validIn (after (SyncOp.scopeMake .sequential) Stores.empty) (Val.scopeHandle 0)
#guard (after (SyncOp.scopeMake .sequential) Stores.empty).refs.all (Val.hasTy · .nat)

end Scope

end Test.Program.ProgressContract
