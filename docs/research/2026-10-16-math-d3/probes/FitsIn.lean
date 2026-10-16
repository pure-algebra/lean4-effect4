import Effect4.Laws.Program.Typed.FitsIn

/-!
# D3 probes: `Fits` and `FitsIn` at a declared name

Finite checks for `docs/research/2026-10-16-math-d3/README.md`. Run with
`LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-16-math-d3/probes/FitsIn.lean`.
Not a battery: no root reaches this file.
-/

namespace Effect4.Program.Typed.D3Probe
open Effect4 Effect4.Machine Effect4.Program

/-- `type Todo = { done: boolean; title: string }`. -/
def todoBody : Ty := .record [("done", false, .bool), ("title", false, .string)]
def todoDecls : TyDecls := [("Todo", todoBody)]
/-- `{ done: false, title: "milk" }`, its names in canonical order. -/
def todoVal : Val := .ctor 0 [.list [.str "done", .str "title"], .list [.bool false, .str "milk"]]

/-- Probe 1 (F2): today's `Fits` refuses a declared record at its name. The reference arm reads a
handle, and a record value reaches the context arm, whose target is not `Todo`. -/
theorem fits_refuses_todo (w : World) : ¬ Fits w todoVal (.app "Todo" []) := by
  intro h
  have h1 : "Todo" = Ty.contextTarget := h.1
  exact absurd h1 (by decide)

/-- Probe 2: membership under the table accepts it, through one unfolding. -/
theorem fitsIn_todo (w : World) : FitsIn todoDecls w todoVal (.app "Todo" []) := by
  rw [fitsIn_unfold (name := "Todo") (body := todoBody) rfl]
  show FitsAt todoDecls w _ todoVal todoBody
  rw [todoBody, fitsAt_record todoDecls w _ rfl]
  exact ⟨trivial, trivial, trivial⟩

/-- Probe 2, agreement: the shape judgment under the table follows (`fitsIn_memberIn`). -/
theorem memberIn_todo (w : World) :
    MemberIn todoDecls w.state.externals.allocated todoVal (.app "Todo" []) :=
  fitsIn_memberIn (fitsIn_todo w)

/-- `type L = null | { head: number; tail: L }`, a recursive list. -/
def listBody : Ty := .union .null (.record [("head", false, .nat), ("tail", false, .app "L" [])])
def listDecls : TyDecls := [("L", listBody)]
/-- `{ head: 1, tail: null }`. -/
def listVal : Val := .ctor 0 [.list [.str "head", .str "tail"], .list [.nat 1, .none]]

/-- Probe 3: a recursive name, unfolded twice: once at the head, once at the field `tail`. -/
theorem fitsIn_list (w : World) : FitsIn listDecls w listVal (.app "L" []) := by
  rw [fitsIn_unfold (name := "L") (body := listBody) rfl]
  refine Or.inr ?_
  rw [fitsAt_record listDecls w _ rfl]
  refine ⟨trivial, ?_, trivial⟩
  show FitsIn listDecls w .none (.app "L" [])
  rw [fitsIn_unfold (name := "L") (body := listBody) rfl]
  exact Or.inl trivial

/-- Probe 4 (red control): `A = A` has no member. The least fixed point admits a value only
through a finite derivation; the greatest would admit every value. -/
theorem fitsIn_selfRef_empty (w : World) (v : Val) :
    ¬ FitsIn [("A", .app "A" [])] w v (.app "A" []) := by
  intro h
  have hn : NameFits [("A", .app "A" [])] w "A" v := h
  refine hn (fun _ _ => False) fun n b u hb hu => ?_
  unfold TyDecls.body? at hb
  simp only [List.lookup] at hb
  split at hb
  · cases hb
    exact hu
  · cases hb

end Effect4.Program.Typed.D3Probe
