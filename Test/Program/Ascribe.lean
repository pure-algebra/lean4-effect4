import Effect4.Api
import Effect4.Program.Authoring.Ascribe
import Effect4.Laws.Program.Authoring.Ascribe
import Effect4.Laws.Modules.Ascribe
import Test.Dogfood.Stage
import ProofGraph.Plan

/-!
# A term at a declared type: the controls of `ascribe`

`Authoring.ascribe ty e` (`src/Effect4/Program/Authoring/Ascribe.lean`) is a record with one
field declared at `ty` that holds `e`, and a read of that field. Its laws are `ascribe_scoped`
(`src/Effect4/Laws/Program/Authoring/Ascribe.lean`), and `types_ascribe`, `ascribe_untyped` and
`reads_ascribe` (`src/Effect4/Laws/Modules/Ascribe.lean`). This battery holds their finite
controls and their instances.

| # | Control | What it shows |
| --- | --- | --- |
| 1 | a typed empty list | a cell made at `ascribe (list string) nil` takes two appends |
| 2 | a wrong element | the bare cell `Ref<never[]>` refuses its first append, and a cell declared at numbers refuses a string |
| 3 | a string through a declared string field | a pair's string tag widens to `string`, and the cell then takes another tag |
| 4 | a wrong declared type | a string declared at `nat` is refused at the record's check |
| 5 | the reading | the form reads the value of its term, at each declared type |

Placement. The typing controls are finite controls of `types_ascribe` and `ascribe_untyped`
(concept `store-typing`, requirement R4). The reading control is one of `reads_ascribe` (concept
`translation-simulation`, requirement R10). The scope control is one of `ascribe_scoped` (concept
`initial-algebras-folds`, requirement R4). Each guard is one build, one typing answer or one
evaluation. None states a law at every type, and none is a host run. The form is no cast and no
`Ref.make<A>`: control 4 and the law `ascribe_untyped` show the first, and nothing here states
the second.
-/

set_option autoImplicit false

namespace Test.Program.Ascribe

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Test.Dogfood (program verdict typingReason? printVerdict readBackVerdict)

def built? (m : Module NativeOp) : Option Effect4.Api.Built :=
  (Effect4.Api.Author.build m).toOption

/-- One entry appended to a log cell, under a minted name for the cell's value. -/
def note (log x : TermSrc) : Src NativeOp :=
  Ref.updateWith log fun xs => app "append" [xs, app "cons" [x, app "nil" []]]

/-- The checker's type of a source term at a scope of names, at the native signature. -/
def typeAt (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  Modules.typeAt nativeSignature names types src

/-- A term's value in a scope of named values. -/
def valueAt (names : List String) (values : List Val) (src : TermSrc) : Option Val :=
  (src { names := names } []).toOption.bind (evalTerm values ·)

/-! ## 1. A typed empty list -/

/-- A log cell declared at lines, two appends, then the log. -/
def lines : Module NativeOp :=
  program (bindName "log" (Ref.make (ascribe (.list .string) (app "nil" []))) fun log =>
    andThen (note log (str "open 1")) (andThen (note log (str "done 1 by 1")) (Ref.get log)))

-- Green: the cell has the declared type, and the program runs to its two lines.
#guard (built? lines).map (fun b => (b.ty.answer, b.runSync)) =
  some (.list .string, .success (.list [.str "open 1", .str "done 1 by 1"]))
-- The form prints as a record literal and a field read, and the module reads back.
#guard (built? lines).map (fun b => (printVerdict b, readBackVerdict b)) = some ("printed", true)
-- The term alone: the empty list at the declared element type, under each scope.
#guard decide (typeAt [] [] (ascribe (.list .string) (app "nil" [])) = some (.list .string))
#guard decide (typeAt ["x"] [.nat] (ascribe (.list (.prod .nat .nat)) (app "nil" [])) =
  some (.list (.prod .nat .nat)))

/-! ## 2. A wrong element -/

/-- The first append at the bare cell, `Ref<never[]>`. -/
def bare : Module NativeOp :=
  program (bindName "log" (Ref.make (app "nil" [])) fun log => note log (str "open 1"))

/-- A string appended to a cell that is declared at numbers. -/
def wrongElement : Module NativeOp :=
  program (bindName "log" (Ref.make (ascribe (.list .nat) (app "nil" []))) fun log =>
    note log (str "open 1"))

-- Red: the bare empty list fixes the cell at `never[]`, and the append's result is refused.
#guard typingReason? bare = some (.resultNotSubtype "refUpdateWith" (.list .string) (.list .never))
-- Red: the declared type is kept. The append's term has a list of a number or a string, and
-- the cell of numbers refuses that result.
#guard typingReason? wrongElement = some (.resultNotSubtype "refUpdateWith" (.list (.union .nat .string)) (.list .nat))

/-! ## 3. A string through a declared string field

A pair keeps a string's literal type (decisions row 256), and a cell is invariant. So a cell
made at a tagged pair takes no other tag. -/

/-- A cell made at a pair with a string tag, then a write of another tag. -/
def tagged : Module NativeOp :=
  program (bindName "c" (Ref.make (app "pair" [str "tag", nat 1])) fun c =>
    Ref.set c (app "pair" [str "other", nat 2]))

/-- The same cell with its tag declared at `string`, the write, and then the cell's value. -/
def widened : Module NativeOp :=
  program (bindName "c" (Ref.make (app "pair" [ascribe .string (str "tag"), nat 1])) fun c =>
    andThen (Ref.set c (app "pair" [str "other", nat 2])) (Ref.get c))

-- Red: the cell holds the literal tag, and the write of another tag is refused at its request.
#guard typingReason? tagged = some (.requestNotSubtype "refSet"
  (.prod (.refOf (.prod (.lit "tag") .nat)) (.prod (.lit "other") .nat))
  (.prod (.refOf (.var 0)) (.var 0)))
-- Green: the declared field widens the tag to `string`. The cell takes the other tag.
#guard (built? widened).map (fun b => (b.ty.answer, b.runSync)) =
  some (.prod .string .nat, .success (.list [.str "other", .nat 2]))
#guard (built? widened).map (fun b => (printVerdict b, readBackVerdict b)) = some ("printed", true)
-- The term alone: a string literal declared at `string` has that type, and its own literal type
-- is what a pair keeps.
#guard decide (typeAt [] [] (ascribe .string (str "tag")) = some .string)
#guard decide (typeAt [] [] (app "pair" [str "tag", nat 1]) = some (.prod (.lit "tag") .nat))
#guard decide (typeAt [] [] (app "pair" [ascribe .string (str "tag"), nat 1]) =
  some (.prod .string .nat))

/-! ## 4. A wrong declared type: the form is no cast -/

-- Red: a string declared at `nat` is refused at the record's check, and so is a number
-- declared at a list.
#guard verdict (program (Ref.make (ascribe .nat (str "a")))) = "typing: recordTerm"
#guard verdict (program (Ref.make (ascribe (.list .nat) (nat 3)))) = "typing: recordTerm"
#guard (typeAt [] [] (ascribe .nat (str "a"))).isNone
-- Red: a declared type is no cast upward either. A list of strings is not below a list of
-- one literal.
#guard (typeAt ["xs"] [.list .string] (ascribe (.list (.lit "a")) (var "xs"))).isNone
-- Green, beside it: the same variable at its own type.
#guard decide (typeAt ["xs"] [.list .string] (ascribe (.list .string) (var "xs")) =
  some (.list .string))

/-! ## 5. The reading -/

-- The form reads the value of its term: the declared type takes no part.
#guard decide (valueAt ["x"] [.nat 7] (ascribe .nat (var "x")) = some (.nat 7))
#guard decide (valueAt [] [] (ascribe (.list .string) (app "nil" [])) = some (.list []))
#guard decide (valueAt [] [] (ascribe .string (str "tag")) = some (.str "tag"))
-- The evaluation has no type check: the declared type is the checker's, and no part of a
-- value. This is why typing is a law of its own.
#guard decide (valueAt [] [] (ascribe .nat (str "a")) = some (.str "a"))

/-! ## The laws at their instances

Each `example` is one application of a law, checked by the kernel. The scope, the path and the
signature are any. -/

section Instances

variable {Op : Type} (sig : Signature Op) (env : Env) (path : List Nat) (types : List Ty)

/-- The typing law at a string literal: its type inside a const-generic position is its literal
type, and its ascription at `string` has one type under each flag. -/
example : TypesEach sig (ascribe .string (str "tag")) env path types .string :=
  types_ascribe rfl (by decide) (types_lit (.str "tag") true) (Ty.sub_lit_string "tag")

/-- The typing law at a number. -/
example : TypesEach sig (ascribe .nat (nat 3)) env path types .nat :=
  types_ascribe rfl (by decide) (types_nat 3 true) (Ty.subN_refl .nat)

/-- The typing law at the empty list, for a signature whose atoms are the native table's. -/
example (atoms : sig.atomOf = nativeAtomTy) :
    TypesEach sig (ascribe (.list .string) nilT) env path types (.list .string) :=
  types_ascribe rfl (by decide) (types_nilT atoms true) (sub_nil_list .string)

/-- The refusal at a string literal declared at `nat`: no type, under either flag. -/
example (const : Bool) (U : Ty) :
    ¬ Types sig (ascribe .nat (str "a")) env path types const U :=
  ascribe_untyped (types_lit (.str "a") true) (by decide +kernel) const U

/-- The reading law at a number. -/
example (vals : List Val) : Reads (ascribe .nat (nat 3)) env path vals (.nat 3) :=
  reads_ascribe .nat (reads_nat 3 env path vals)

/-- The scope law, found by the scope tactic at the form's head. -/
example : (ascribe (.list .nat) (app "nil" [])).Scoped := by authoring_scoped

end Instances

end Test.Program.Ascribe
