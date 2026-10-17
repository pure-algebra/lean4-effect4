import Tools.Session
import Effect4.Laws.Program.Signature
import Effect4.Program.Scoped

/-!
# Probe FGH: what slices F, G and H would need, at the level of the DAG

Slices F to H are scoped, not planned. This probe states the first obligation of each, proves
the two that are cheap, and checks the others on finite cases.

* **F, scope transport.** `effTy_shift`: a program placed under an environment by one shift per
  slot types as at the empty environment, at every signature natural in weakening. It is
  `effTy_weaken` folded over the environment. `SigApp.signature_weakenNatural`: every
  application's signature is natural in weakening, so the shift law holds at an application.
  Placement: concept `initial-algebras-folds`, property `operation-data-scoped` (weakening is
  the frontier fold); question: the proposed claim `fragment-support-transport` (role
  compatibility). Consumer: slice F's import of a fragment into a deeper environment, and the
  catalogue of slice C once it offers candidates from another depth. It does not establish
  transport of a fragment that reads an outside variable, which needs a binder map.
* **F, row relocation.** `relabelExternal` and `check_relabel_stmt`: the checker reads a
  relabelled program at a relabelled table as the original at the original. Statement only. It
  is the R14 open part `sketch-renumbering`.
* **G, a filling observed as a reply.** `fill_by_term_tree_stmt`: on the call tree, a host that
  answers a hole's row with a literal's value observes the same stop and stores as the program
  with that literal filled in, at every budget. Statement only, with finite controls. It is the
  R14 open part `fill-by-term` (decisions row 373 (6)), restricted to literal fillings.
* **H** needs an exact codec of a run's state, which no definition holds yet; the README sizes it.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace ProofScout.FGH

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)

/-! ## F: the shift -/

/-- Shift a program down by `n` slots: one weakening at the front per slot. -/
def shift : Nat → NativeEff → NativeEff
  | 0, e => e
  | n + 1, e => Eff.weaken 0 (shift n e)

/-- **A shifted program types under the environment as at the empty one.** -/
theorem effTy_shift (sig : Signature NativeOp) (hw : sig.WeakenNatural) :
    ∀ (env : TyEnv) (e : NativeEff), effTy sig env (shift env.length e) = effTy sig [] e
  | [], _ => rfl
  | A :: env, e => by
    show effTy sig (A :: env) (Eff.weaken 0 (shift env.length e)) = _
    have h := effTy_weaken sig hw [] env A (shift env.length e)
    simp only [List.nil_append, List.length_nil] at h
    rw [h, effTy_shift sig hw env e]

/-- **Every application's signature is natural in weakening.** -/
theorem SigApp.signature_weakenNatural (app : SigApp) : app.signature.WeakenNatural := by
  intro cut op
  cases op <;> exact ⟨rfl, rfl, rfl⟩

-- A closed fragment, shifted under one string slot, keeps its type (control C3's repair).
def closedAtRoot : NativeEff := .bind (.succeed (.lit (.nat 7))) (.succeed (.var 0))
#guard effTy ({} : SigApp).signature [.string] (shift 1 closedAtRoot) = some (.pure .nat)
#guard effTy ({} : SigApp).signature [.string] closedAtRoot = some (.pure .string)

/-! ## F: row relocation -/

/-- Relabel the external rows of a program. -/
def relabelExternal (f : Nat → Nat) (e : NativeEff) : NativeEff :=
  cata_eff { EffAlgebra.id NativeOp with
    eff_perform := fun op req => match op with
      | .external i => .perform (.external (f i)) req
      | op => .perform op req } e

/-- **Relocation keeps the checker's answer** where the new table holds each used row at its new
position. Statement only. -/
def check_relabel_stmt : Prop :=
  ∀ (app : SigApp) (rows' : RowTable) (f : Nat → Nat) (e : NativeEff) (env : TyEnv)
    (p : List Nat),
    (∀ i, i < app.rows.length → rows'[f i]? = app.rows[i]?) →
    Checker.check { app with rows := rows' }.signature env p (relabelExternal f e) =
      Checker.check app.signature env p e

-- The relocation of control C2: the same bytes read another row after a row is inserted before
-- it, and the relabelled program reads its own row again.
def call0 : NativeEff := .perform (.external 0) (.lit .unit)
def natRows : RowTable := [Row.hole "n" .nat]
def grown : RowTable := [Row.hole "s" .string, Row.hole "n" .nat]
#guard effTy (SigApp.ofTable grown).signature [] call0 = some (.pure .string)
#guard effTy (SigApp.ofTable grown).signature [] (relabelExternal (· + 1) call0) =
  effTy (SigApp.ofTable natRows).signature [] call0

/-! ## G: a literal filling observed as a reply -/

/-- A host that answers one row with one value every time, and leaves every other call waiting. -/
def constHost (n : Nat) (v : Store.Val) : Run.Tree.Host Unit := fun i _ _ =>
  if i = n then some (.success v, ()) else none

/-- **A literal filling and its value as a reply observe one stop and one store.** Statement
only. -/
def fill_by_term_tree_stmt : Prop :=
  ∀ (table : RowTable) (k n : Nat) (l : Lit) (v : Store.Val) (p : List Nat)
    (prog filled : NativeEff),
    l.toVal = some v →
    (Node.eff prog).at_ p = some (.eff (.perform (.external n) (.lit .unit))) →
    (Node.eff prog).replaceAt p (.eff (.succeed (.lit l))) = some (.eff filled) →
    (Run.Tree.probe table k (constHost n v) () prog).stop =
        (Run.Tree.probe table k (constHost n v) () filled).stop ∧
      (Run.Tree.probe table k (constHost n v) () prog).stores =
        (Run.Tree.probe table k (constHost n v) () filled).stores

/-- One finite instance of the statement, read through the stop's and the stores' equality. -/
def agreesAt (table : RowTable) (k n : Nat) (v : Store.Val) (prog filled : NativeEff) : Bool :=
  let a := Run.Tree.probe table k (constHost n v) () prog
  let b := Run.Tree.probe table k (constHost n v) () filled
  (match a.stop, b.stop with
    | .finished x, .finished y => x == y
    | .cut, .cut => true
    | .waiting i r, .waiting j s => i == j && r == s
    | _, _ => false) && a.stores == b.stores

def holeRows : RowTable := [Row.hole "h" .nat]
def hole : NativeEff := Sketch.hole {} 0
-- A hole read by its continuation, a hole performed twice with one filled, and a hole under a
-- failure handler: each agrees at budgets 0 to 4.
def readBack : NativeEff := .bind hole (.succeed (.var 0))
def readBackFilled : NativeEff := .bind (.succeed (.lit (.nat 7))) (.succeed (.var 0))
def twice : NativeEff := .bind hole (.bind hole (.succeed (.var 1)))
def twiceFilled : NativeEff := .bind (.succeed (.lit (.nat 7))) (.bind hole (.succeed (.var 1)))
def handled : NativeEff := .catchCause hole (.succeed (.lit (.nat 0)))
def handledFilled : NativeEff := .catchCause (.succeed (.lit (.nat 7))) (.succeed (.lit (.nat 0)))
#guard (List.range 5).all fun k => agreesAt holeRows k 0 (.nat 7) readBack readBackFilled
#guard (List.range 5).all fun k => agreesAt holeRows k 0 (.nat 7) twice twiceFilled
#guard (List.range 5).all fun k => agreesAt holeRows k 0 (.nat 7) handled handledFilled
-- The red control: a reply of a different value is not the filling.
#guard !(agreesAt holeRows 4 0 (.nat 8) readBack readBackFilled)

end ProofScout.FGH
