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

/-! The approved typed sites use the public printer and its named reader. -/

/-- A joined option input exercises the branch binder's actual checked environment. -/
def joinedOptions : Ty := .union (.option .nat) (.option .string)

def optionSite : Eff NativeOp :=
  .select (.var 0) .option (.succeed (.lit (.nat 0))) (.succeed (.var 1))

/-- The generator declares an option union before visiting its typed selection. -/
def generatedSites : Eff NativeOp := .gen
  (.cons (.bindYield (.select (.lit (.bool true)) .bool
    (.succeed (.app "some" (.cons (.lit (.nat 3)) .nil)))
    (.succeed (.app "some" (.cons (.lit (.str "three")) .nil)))))
    (.cons (.yieldDiscard optionSite) (.cons (.ret (.lit .unit)) .nil)))

/-- A closed layer below an outer binder still types and erases its body at zero. -/
def layerSites : Eff NativeOp := .bind (.succeed (.lit .unit))
  (.provideLayer (.effectDiscard generatedSites) false (.succeed (.lit .unit)))

/-- Finite public-print reconstruction and reading; either print refusal fails this control. -/
def typedRoundTrip (env : TyEnv) (p : Eff NativeOp) : Bool :=
  match Effect4.Program.printTyped nativeSignature env p, print nativeSignature env.length p with
  | .ok typed, .ok plain =>
    plain == eraseJoinArgs [] nativeSignature (nativeSpell []) env.length typed &&
      decide (readTyped [] nativeSignature (nativeSpell []) env.length typed = .ok p)
  | _, _ => false

#guard typedRoundTrip [joinedOptions] optionSite
#guard typedRoundTrip [] generatedSites
#guard typedRoundTrip [] layerSites
#guard typedRoundTrip [.union (.fiberOf .nat .never) (.fiberOf .string .bool), .scope]
  (.withFiber (.runIn (.var 0) (.var 1)))

-- Reader: actual joined selection reads through the public typed-print theorem.
example (lawful : LawfulSpelling nativeSignature (nativeSpell [])) {x : TypeScript.Expr}
    (printed : Effect4.Program.printTyped nativeSignature [joinedOptions] optionSite = .ok x) :
    readTyped [] nativeSignature (nativeSpell []) 1 x = .ok optionSite :=
  readTyped_printTyped lawful (by decide) printed

-- Reader: the same public theorem carries a generator declaration and its branch binder.
example (lawful : LawfulSpelling nativeSignature (nativeSpell [])) {x : TypeScript.Expr}
    (printed : Effect4.Program.printTyped nativeSignature [] generatedSites = .ok x) :
    print nativeSignature 0 generatedSites = .ok (eraseJoinArgs [] nativeSignature (nativeSpell []) 0 x) :=
  eraseJoinArgs_printTyped lawful (by decide) printed

end Test.Codegen.PrintTyped

namespace Test.Codegen.PrintTyped.P2bControls
open TypeScript Effect4.Codegen
open EraseTermTypes

-- Finite positive: the exact approved wrapper strips only inferred inner A,E.
#guard eraseNode 0
  (.call (.ident "Effect.withFiber") [.arrowBlock []
    [.exprStmt (.call (.generic (.ident "Fiber.runIn") [.name ["number"] [], .name ["never"] []])
      [.ident "a0", .ident "a1"]), .ret (.ident "Effect.void")] none]) ==
  .call (.ident "Effect.withFiber") [.arrowBlock []
    [.exprStmt (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]),
      .ret (.ident "Effect.void")] none]

-- Red controls preserve a different wrapper, generic arity, or declared callback data.
#guard eraseNode 0
  (.call (.ident "foreign") [.arrowBlock []
    [.exprStmt (.call (.generic (.ident "Fiber.runIn") [.name ["number"] [], .name ["never"] []])
      [.ident "a0", .ident "a1"]), .ret (.ident "Effect.void")] none]) ==
  .call (.ident "foreign") [.arrowBlock []
    [.exprStmt (.call (.generic (.ident "Fiber.runIn") [.name ["number"] [], .name ["never"] []])
      [.ident "a0", .ident "a1"]), .ret (.ident "Effect.void")] none]

#guard eraseNode 0
  (.call (.ident "Effect.withFiber") [.arrowBlock []
    [.exprStmt (.call (.generic (.ident "Fiber.runIn") [.name ["number"] []])
      [.ident "a0", .ident "a1"]), .ret (.ident "Effect.void")] none]) ==
  .call (.ident "Effect.withFiber") [.arrowBlock []
    [.exprStmt (.call (.generic (.ident "Fiber.runIn") [.name ["number"] []])
      [.ident "a0", .ident "a1"]), .ret (.ident "Effect.void")] none]

#guard eraseNode 0
  (.call (.ident "Effect.withFiber") [.arrowBlock []
    [.exprStmt (.call (.generic (.ident "Fiber.runIn") [.name ["number"] [], .name ["never"] []])
      [.ident "a0", .ident "a1"]), .ret (.ident "Effect.void")] (some (.name ["void"] []))]) ==
  .call (.ident "Effect.withFiber") [.arrowBlock []
    [.exprStmt (.call (.generic (.ident "Fiber.runIn") [.name ["number"] [], .name ["never"] []])
      [.ident "a0", .ident "a1"]), .ret (.ident "Effect.void")] (some (.name ["void"] []))]

end Test.Codegen.PrintTyped.P2bControls

namespace Test.Codegen.PrintTyped.P2bControls
open TypeScript Effect4.Codegen
open EraseTermTypes

-- The stored B must agree with the repeated callback type before inferred A disappears.
#guard eraseTerm 0
  (.call (.generic (.ident "fold") [.name ["number"] [], .name ["string"] []])
    [.ident "xs", .ident "initial", .lambda
      [{ name := "a0", type := some (.name ["string"] []) }, { name := "a1", type := none }]
      (.ident "a0") none]) ==
  .call (.generic (.ident "fold") [.name ["number"] [], .name ["string"] []])
    [.ident "xs", .ident "initial", .lambda
      [{ name := "a0", type := some (.name ["string"] []) }, { name := "a1", type := none }]
      (.ident "a0") none]

-- A declared result annotation is outside the canonical stored-fold encoding.
#guard eraseTerm 0
  (.call (.generic (.ident "fold") [.name ["number"] [], .name ["string"] []])
    [.ident "xs", .ident "initial", .lambda
      [{ name := "a0", type := some (.name ["number"] []) }, { name := "a1", type := none }]
      (.ident "a0") (some (.name ["number"] []))]) ==
  .call (.generic (.ident "fold") [.name ["number"] [], .name ["string"] []])
    [.ident "xs", .ident "initial", .lambda
      [{ name := "a0", type := some (.name ["number"] []) }, { name := "a1", type := none }]
      (.ident "a0") (some (.name ["number"] []))]

end Test.Codegen.PrintTyped.P2bControls
