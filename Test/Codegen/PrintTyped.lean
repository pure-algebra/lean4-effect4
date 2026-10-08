import Effect4.Laws.Codegen.PrintTyped
import Effect4.Program.Native
import TypeScript.Render

/-!
# The typed print and named join erasure

`printTypedAt` (`Codegen/PrintTyped.lean`) is the table-driven print with the node's address.
The hand annotation supplies the joins that the match by bounds can answer.
The readers apply the raw erasure and read-back laws at concrete programs.
The remaining lines are finite evaluations or controls (decisions row 301).
-/

namespace Test.Codegen.PrintTyped

open Effect4.Program Effect4.Codegen Effect4.Codegen.Templates
open TypeScript (house0)
open TypeScript.Render (expr)

/-- `Ref.modify` whose term answers the pair `["s", a]`, called on the cell `a0`. -/
def modify : Eff NativeOp :=
  .perform (.refModifyWith (.app "pair" (.cons (.lit (.str "s")) (.cons (.var 1) .nil)))) (.var 0)

/-- The call after a first program: it stands at the address `[1]`. -/
def after : Eff NativeOp := .bind (.succeed (.var 0)) modify

/-- An annotation that answers the join `number, number | string` at one address. -/
def joinAt (path : List Nat) : List Nat → Option (List Ty) :=
  fun p => if p = path then some [.nat, .union .nat .string] else none

-- finite evaluation: the call at a join carries the row's bindings on its head, `A` then `B`
#guard (printTypedAt nativeSignature (joinAt []) 1 modify).map (expr house0 0) =
  .ok "Ref.modify<number, number | string>(a0, (a1) => pair(\"s\", a1))"
-- finite evaluation: a child's address is its parent's and its index among the node arguments
#guard (printTypedAt nativeSignature (joinAt [1]) 1 after).map (expr house0 0) =
  .ok "Effect.flatMap(Effect.succeed(a0), (a1) => Ref.modify<number, number | string>(a0, (a2) => pair(\"s\", a1)))"
-- control: an annotation at another address leaves the call as the print prints it
#guard (printTypedAt nativeSignature (joinAt [0]) 1 after).map (expr house0 0) =
  (print nativeSignature 1 after).map (expr house0 0)

/-- A finite successful raw-print comparison. A refusal fails this check. -/
def erases (n : Nat) (p : Eff NativeOp) (annotation : List Nat → Option (List Ty)) : Bool :=
  match printTypedAt nativeSignature annotation n p with
  | .error _ => false
  | .ok typed => match print nativeSignature n p with
    | .error _ => false
    | .ok plain => plain == eraseJoinArgs [] nativeSignature (nativeSpell []) n typed

/-- A finite read through the production erasure and existing reader. -/
def reads (n : Nat) (p : Eff NativeOp) (annotation : List Nat → Option (List Ty)) : Bool :=
  match printTypedAt nativeSignature annotation n p with
  | .error _ => false
  | .ok typed => decide (readTyped [] nativeSignature (nativeSpell []) n typed = .ok p)

#guard erases 1 modify (joinAt [])
#guard reads 1 modify (joinAt [])
#guard erases 1 after (joinAt [1])
#guard reads 1 after (joinAt [1])

/-- A declaration extends the eraser's depth before the second generator statement. -/
def generated : Eff NativeOp := .gen
  (.cons (.bindYield (.succeed (.lit .unit)))
    (.cons (.yieldDiscard after) .nil))

#guard erases 0 generated (joinAt [0, 1, 0, 0, 1])
#guard reads 0 generated (joinAt [0, 1, 0, 0, 1])

/-- The layer body restarts at zero below an outer program binder. -/
def closedLayer : Eff NativeOp := .bind (.succeed (.lit .unit))
  (.provideLayer (.effectDiscard (.bind (.succeed (.lit .unit)) modify)) false
    (.succeed (.lit .unit)))

#guard erases 1 closedLayer (joinAt [1, 0, 0, 1])
#guard reads 1 closedLayer (joinAt [1, 0, 0, 1])

-- Required operation-carried arguments include unions and remain present.
#guard erases 0 (.perform (.deferredMakeOf (.union .nat .string) .never) (.lit .unit))
  (fun _ => none)
#guard reads 0 (.perform (.deferredMakeOf (.union .nat .string) .never) (.lit .unit))
  (fun _ => none)

-- Nonempty insertion refuses instead of overwriting operation-carried arguments.
#guard !(printPerformAt nativeSignature 0 (.deferredMakeOf .nat .never) (.lit .unit)
  (some [.string])).isOk
#guard (printPerformAt nativeSignature 0 (.deferredMakeOf .nat .never) (.lit .unit) (some [])).map
  (expr house0 0) = (printPerform nativeSignature 0 (.deferredMakeOf .nat .never) (.lit .unit)).map
    (expr house0 0)

-- A non-printable inferred argument is a refusal, rather than a successful erasure witness.
#guard !erases 1 modify (fun _ => some [.app "Nominal" [.nat]])

/-- A synthetic unsafe row shares a pure helper spelling. The term capture retains the helper's
required literal argument independently of the program row's spelling. -/
def helperRow : Effect4.Program.Row :=
  ⟨"collision", "recordRequired", .call, [], .sync, .string, .nat, .never, [],
    "scratch control", [], .deferred⟩

def helperSig : Signature Unit :=
  { rowOf := fun _ => helperRow, atomOf := fun _ _ => none,
    scopeKey := ⟨⟨0⟩, ⟨0⟩⟩, serviceTy := fun _ => none }

def helperSpell (s : String) (names : List String) : Option Unit :=
  if s = "recordRequired" ∧ names = [] then some () else none

-- Existing ordinary readable field syntax stays readable even at the unsafe synthetic row.
#guard match print helperSig 0 (.succeed (.field .required (.lit .unit) "x")) with
  | .error _ => false
  | .ok printed =>
    printed == eraseJoinArgs [] helperSig helperSpell 0 printed &&
      (readTyped [] helperSig helperSpell 0 printed).isOk
#guard !rowNamesSafe helperRow

/-- A lawful external row owns the same generic syntax that a typed pure query inserts. -/
def causeRow : Effect4.Program.Row :=
  { name := "queryAsOperation", spelling := "causeError", kind := .sync,
    request := .union (.causeOf .string) (.exitOf .nat .string), answer := .option .string,
    cite := "synthetic erasure ambiguity control", typeArgs := ["unknown", "string"],
    registration := .external }

def causeSig : Signature Unit :=
  { rowOf := fun _ => causeRow, atomOf := fun _ _ => none,
    scopeKey := ⟨⟨0⟩, ⟨0⟩⟩, serviceTy := fun _ => none }

def causeSpell (s : String) (names : List String) : Option Unit :=
  if s = "causeError" ∧ names = [] then some () else none

#guard rowNamesSafe causeRow
#guard LawfulTable [causeRow]
#guard !(printPerformAt causeSig 1 () (.var 0) (some [.nat])).isOk

-- The same target call erases differently at actual term and program occurrences.
#guard EraseTermTypes.eraseTerm 1
  (.call (.generic (.ident "causeError") [.name ["unknown"] [], .name ["string"] []])
    [.ident "a0"]) == .call (.ident "causeError") [.ident "a0"]
#guard match print causeSig 1 (.perform () (.var 0)) with
  | .error _ => false
  | .ok printed =>
    printed == eraseJoinArgs [] causeSig causeSpell 1 printed &&
      (readTyped [] causeSig causeSpell 1 printed).isOk

-- Reader: the raw connector applies to a real joined call under the existing spelling premise.
example (lawful : LawfulSpelling nativeSignature (nativeSpell [])) {x : TypeScript.Expr}
    (printed : printTypedAt nativeSignature (joinAt []) 1 modify = .ok x) :
    print nativeSignature 1 modify = .ok (eraseJoinArgs [] nativeSignature (nativeSpell []) 1 x) :=
  eraseJoinArgs_printTypedAt lawful (by decide) printed

-- Reader: the same law carries declaration depth and source addresses through the generator.
example (lawful : LawfulSpelling nativeSignature (nativeSpell [])) {x : TypeScript.Expr}
    (printed : printTypedAt nativeSignature (joinAt [0, 1, 0, 0, 1]) 0 generated = .ok x) :
    readTyped [] nativeSignature (nativeSpell []) 0 x = .ok generated :=
  readTyped_printTypedAt lawful (by decide) printed

-- Reader: successful typed reading retains ordinary reconstruction at the named erased input.
example (lawful : LawfulSpelling nativeSignature (nativeSpell [])) {x : TypeScript.Expr}
    (read : readTyped [] nativeSignature (nativeSpell []) 1 x = .ok modify) :
    print nativeSignature 1 modify = .ok (eraseJoinArgs [] nativeSignature (nativeSpell []) 1 x) :=
  readTyped_exact lawful read

end Test.Codegen.PrintTyped
