import Effect4
import Effect4.Laws.Program.Bounds
import Effect4.Program.Native
import Effect4.Program.NativeAtom

/-!
# The match of a template by bounds (slice MATCH): the controls

`Program/Bounds.lean` matches a template against a request by bounds, and
`Laws/Program/Bounds.lean` proves its laws (decisions rows 299 and 303). These are the finite
evaluations and the readers.

* **Green (tested): the reach of the laws.** Each template of the tree is in reach: the
  parameters of every template atom, the request of every spelled native row, and the result
  template of every binder term.
* **Red (tested): where the reach stops.** A nominal reference, and a parameter under a union.
* **Green (tested): the match.** One candidate binds raw. Two candidates with no order join. A
  cell fixes its parameter through the guard of the match.
* **Red (tested): an invariant occurrence still refuses** a second candidate that is not the
  cell's own content.
* **Tested: a template atom at a proper union of its argument.** Each list atom and each map
  atom answers at the join, and the prelude's whole form lets tsgo compute it.
* **Tested: the interim guard at a binder term**, at the result template of `Ref.modify`. A pair
  whose first part is a union passes. Two pairs whose first parts have no order do not. Two pairs
  whose first parts have an order pass. The guard does not read the cell's parameter. The match
  by bounds alone answers each.
* **Red (tested): a signature's admission** refuses a host row with a parameter under a nominal
  reference, and it admits the same row at a closed argument.
* **Green (proved): three readers** of the laws, at a real row and at a real atom.

No line restates a theorem, and no line prints axioms.
-/

set_option autoImplicit false

namespace Test.Program.BoundsControls

open Effect4 Effect4.Program
open Effect4.Program.Bounds

/-! ## The reach of the laws -/

-- green (tested): the parameters of every template atom are in reach
#guard NativeAtom.all.all fun atom =>
  match (NativeAtom.spec atom).scheme with
  | .poly params _ => params.all templateOKb
  | _ => true
-- green (tested): the request of every spelled native row is in reach
#guard NativeOp.spelled.all fun op => templateOKb (NativeOp.row op).normalizeTypes.request
-- green (tested): the result template of every binder term is in reach
#guard [FnShape.update, .updateSome, .modify, .modifySome].all fun s => templateOKb s.result.normalize

-- red (tested): a nominal reference, and a parameter under a union head
#guard !templateOKb (.app "Context.Context" [.var 0])
#guard !templateOKb (.union (.var 0) .nat)
#guard !templateOKb (.prod (.union .nat .string) (.var 0))

/-! ## The match -/

/-- The binding of parameter `i`, in normal form. -/
def bound (σ : Option Ty.Subst) (i : Nat) : Option Ty :=
  σ.map fun bindings => (Ty.instantiate bindings (.var i)).normalize

-- green (tested): one candidate binds the request's own type
#guard matchB [] (.var 0) .nat == some [(0, .nat)]
#guard matchB [] (.prod (.var 0) (.var 0)) (.prod .nat .nat) == some [(0, .nat), (0, .nat)]
#guard matchB [] (.refOf (.var 0)) (.refOf .nat) == some [(0, .nat)]
-- green (tested): two candidates with no order join, at one template and at an argument list
#guard bound (matchB [] (.prod (.var 0) (.var 0)) (.prod .nat .string)) 0 = some (.union .nat .string)
#guard bound (matchArgsB [.bool, .var 0, .var 0] [.bool, .nat, .string]) 0 =
  some (.union .nat .string)
-- green (tested): a request union is read member by member
#guard bound (matchB [] (.list (.var 0)) (.union (.list .nat) (.list .string))) 0 =
  some (.union .nat .string)
-- green (tested): a cell fixes its parameter. The second candidate is below the cell's content
#guard bound (matchArgsB [.refOf (.var 0), .var 0] [.refOf (.union .nat .string), .string]) 0 =
  some (.union .nat .string)

-- red (tested): a closed template refuses another type
#guard matchB [] .nat .string == none
#guard matchB [] (.refOf .nat) (.refOf .string) == none
-- red (tested): an invariant occurrence still refuses. The join is above the cell's content, and
-- the guard of the match refuses the cell
#guard matchArgsB [.refOf (.var 0), .var 0] [.refOf .nat, .string] == none
-- red (tested): a list of another length
#guard matchArgsB [.var 0] [.nat, .nat] == none

/-! ## A template atom at an argument that is a proper union

The match reads a union argument member by member, and the atom answers at the join of the
members' element types. The prelude takes such an argument at its whole type, so tsgo computes
the same join (`harness/truth/folds.typecheck.ts`, which `make check-truth` runs). At a
declaration with the parameter under the list or the map, tsgo refuses each of these calls
(`TS2345`). -/

/-- Two list types with no order. -/
def twoLists : Ty := .union (.list .nat) (.list .string)

/-- Two map types with no order. -/
def twoMaps : Ty := .union (.map .string .nat) (.map .string .string)

/-- The atom's answer at the arguments is the expected type, up to the normal form. -/
def answersAt (name : String) (arguments : List Ty) (expected : Ty) : Bool :=
  (nativeAtomTy name arguments).map Ty.normalize == some expected.normalize

-- tested: each list atom and each map atom at a proper union of its argument
#guard answersAt "take" [twoLists, .nat] (.list (.union .nat .string))
#guard answersAt "drop" [twoLists, .nat] (.list (.union .nat .string))
#guard answersAt "get" [twoLists, .nat] (.option (.union .nat .string))
#guard answersAt "cons" [.bool, twoLists] (.list (.union .bool (.union .nat .string)))
#guard answersAt "append" [twoLists, .list .bool] (.list (.union .bool (.union .nat .string)))
#guard answersAt "mapGet" [twoMaps, .string] (.option (.union .nat .string))
#guard answersAt "mapKeys" [twoMaps] (.list .string)
#guard answersAt "mapEntries" [twoMaps] (.list (.prod .string (.union .nat .string)))
#guard answersAt "mapSet" [twoMaps, .string, .bool]
  (.map .string (.union .bool (.union .nat .string)))
-- red (tested): the list atoms still refuse an argument that is no list
#guard nativeAtomTy "take" [.union (.list .nat) .nat, .nat] = none

/-! ## The interim guard at a binder term

The probe's controls (`docs/research/2026-10-06-seat-BOUNDS-evidence/scripts/FoldsGuard.tail.lean.txt`),
at the function of the tree. The cell's parameter is the seed's, at `nat`. -/

/-- The result template of `Ref.modify`: the pair of the reply and the cell's next value. -/
def modifyResult : Ty := .prod (.var 1) (.var 0)

/-- Two pairs whose first parts have no order. -/
def twoPairs : Ty := .union (.prod .nat .nat) (.prod .string .nat)

-- green (tested): a pair whose first part is a union offers one lower bound
#guard bound (matchTerm [(0, .nat)] modifyResult (.prod (.union .nat .string) .nat)) 1 =
  some (.union .nat .string)
-- red (tested): two pairs whose first parts have no order offer two, and the guard refuses
#guard matchTerm [(0, .nat)] modifyResult twoPairs == none
-- tested: the match by bounds alone answers there, at the join
#guard bound (matchB [(0, .nat)] modifyResult twoPairs) 1 = some (.union .nat .string)
-- green (tested): two pairs whose first parts have an order pass
#guard bound (matchTerm [(0, .nat)] modifyResult
    (.union (.prod (.lit "a") .nat) (.prod .string .nat))) 1 = some .string
-- green (tested): the guard does not read the cell's parameter
#guard (matchTerm [(0, .union .nat .string)] modifyResult
    (.union (.prod .bool .nat) (.prod .bool .string))).isSome
-- red (tested): the raw reading. The pair of a union passes, and its normal form, two pairs,
-- does not
#guard (Ty.prod (.union .nat .string) .nat).normalize == twoPairs.normalize
#guard matchTerm [(0, .nat)] modifyResult (Ty.prod (.union .nat .string) .nat).normalize == none

/-! ## A signature's admission at a nominal reference -/

/-- A host row whose request holds a parameter under a nominal reference. -/
def boxRow (argument : Ty) : Row :=
  { name := "b", spelling := "B.b", kind := .async, request := .app "Box" [argument],
    answer := .nat, cite := "decisions row 303", registration := .external }

-- red (tested): the admission refuses the row at its request column
#guard (rowChecks (boxRow (.var 0))).any fun check =>
  !check.1 && check.2 == .templateNotAdmissible "request"
-- green (tested): at a closed argument the clause passes
#guard (rowChecks (boxRow .nat)).all fun check =>
  check.1 || check.2 != .templateNotAdmissible "request"

/-! ## The laws, read at a row and at an atom -/

/-- **The complete match at `Ref.set`** (proved, by `matchB_complete`): a normal request below an
instance of the row's request template has a match. -/
theorem refSet_complete {r : Ty} (normal : Ty.Normal r) {τ : Ty.Subst}
    (below : Ty.sub r
      (Ty.instantiate τ (NativeOp.row .refSet).normalizeTypes.request).normalize = true) :
    ∃ σ, matchB [] (NativeOp.row .refSet).normalizeTypes.request r = some σ :=
  matchB_complete [] (templateOK_of _ (by decide +kernel)) normal (fun _ _ h => nomatch h) below

/-- **The least bindings at `ite`** (proved, by `matchArgsB_least`): the answer of `ite` is below
every type that both arms are below. -/
theorem ite_least {X Y : Ty} (normalX : Ty.Normal X) (normalY : Ty.Normal Y) {σ : Ty.Subst}
    (matched : matchArgsB [.bool, .var 0, .var 0] [.bool, X, Y] = some σ) {τ : Ty.Subst}
    (admits : Admits τ [.bool, .var 0, .var 0] [.bool, X, Y]) :
    Ty.subN (Ty.instantiate σ (.var 0)) (Ty.instantiate τ (.var 0)) = true :=
  matchArgsB_least matched
    (fun p hp => by
      have reach : ∀ q ∈ [Ty.bool, .var 0, .var 0], templateOKb q = true := by decide +kernel
      exact templateOK_of p (reach p hp))
    (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Ty.normal_normalize .bool
      rcases List.mem_cons.mp hr with rfl | hr
      · exact normalX
      rcases List.mem_cons.mp hr with rfl | hr
      · exact normalY
      · exact nomatch hr)
    admits 0

/-- **The monotone match at `ite`** (proved, by `matchArgsB_monotone`): smaller arms have a match
with a smaller answer. -/
theorem ite_monotone {X Y X' Y' : Ty} {σ : Ty.Subst}
    (matched : matchArgsB [.bool, .var 0, .var 0] [.bool, X, Y] = some σ)
    (normalX : Ty.Normal X') (normalY : Ty.Normal Y')
    (smallerX : Ty.subN X' X = true) (smallerY : Ty.subN Y' Y = true) :
    ∃ σ', matchArgsB [.bool, .var 0, .var 0] [.bool, X', Y'] = some σ' ∧
      Ty.subN (Ty.instantiate σ' (.var 0)) (Ty.instantiate σ (.var 0)) = true := by
  obtain ⟨σ', matched', smaller⟩ := matchArgsB_monotone (rs' := [.bool, X', Y']) matched
    (fun p hp => by
      have reach : ∀ q ∈ [Ty.bool, .var 0, .var 0], templateOKb q = true := by decide +kernel
      exact templateOK_of p (reach p hp))
    (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Ty.normal_normalize .bool
      rcases List.mem_cons.mp hr with rfl | hr
      · exact normalX
      rcases List.mem_cons.mp hr with rfl | hr
      · exact normalY
      · exact nomatch hr)
    rfl
    (fun rr hrr => by
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact Ty.subN_refl .bool
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact smallerX
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact smallerY
      · exact nomatch hrr)
  exact ⟨σ', matched', smaller 0⟩

end Test.Program.BoundsControls
