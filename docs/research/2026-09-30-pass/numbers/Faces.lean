import Effect4.Api
import TypeScript
import Effect4.Program.Profile

/-! # Numbers seat, probe 1: one program, three faces

Research evidence, outside the Test root. Base `be15b062`. Every check here is finite (`#guard`).

The program adds, subtracts, multiplies and divides naturals. Every literal is at most
`2^53 - 1`, so every literal is inside rc.112's profile (`Program.rc112.natBound`). There is no
host row, so `HostBoundary` never looks at a value. The intermediates pass `2^53` (first binding)
and then `2^62` (fourth and fifth bindings). The result is a nest of pairs:

* `a1 = (2^52 + (2^52 + 1)) - (2^53 - 1)` — passes `2^53`;
* `lt(a3, 1)` where `a3 = 2^61 + (2^61 + 5)` — passes `2^62` by addition;
* `div(a3, 2)`;
* `(a3 - a2) - a2` where `a2 = 2^61` — should give back `5`;
* `mod(a4, 1000)` where `a4 = (2^53 + 1) * 512` — passes `2^62` by multiplication.

This file checks the Lean reference answer, the program's type, the TypeScript the printer
writes for it, and the canonical bytes the OCaml engine decodes (printed by `#eval`). -/

set_option autoImplicit false

namespace Research.Pass.Numbers.Faces

open Effect4 Effect4.Machine Effect4.Program

def lit (n : Nat) : Term := .lit (.nat n)
def var (i : Nat) : Term := .var i
def app2 (f : String) (a b : Term) : Term := .app f (.cons a (.cons b .nil))

/-- The one program all three faces run. Variables are positions from the outermost binder
(`a0` is the first binding). -/
def program : Api.Program :=
  .bind (.succeed (app2 "add" (lit 4503599627370496) (lit 4503599627370497))) <|
  .bind (.succeed (app2 "sub" (var 0) (lit 9007199254740991))) <|
  .bind (.succeed (app2 "mul" (lit 4503599627370496) (lit 512))) <|
  .bind (.succeed (app2 "add" (var 2) (app2 "add" (var 2) (lit 5)))) <|
  .bind (.succeed (app2 "mul" (var 0) (lit 512))) <|
  .succeed
    (app2 "pair" (var 1)
      (app2 "pair" (app2 "lt" (var 3) (lit 1))
        (app2 "pair" (app2 "div" (var 3) (lit 2))
          (app2 "pair" (app2 "sub" (app2 "sub" (var 3) (var 2)) (var 2))
            (app2 "mod" (var 4) (lit 1000))))))

/-- The five observations, as the machine's nested pairs. -/
def result (a1 : Nat) (lt : Bool) (d m s : Nat) : Val :=
  .list [.nat a1, .list [.bool lt, .list [.nat d, .list [.nat s, .nat m]]]]

-- Every literal is inside rc.112's profile.
#guard [4503599627370496, 4503599627370497, 9007199254740991, 512, 5, 1, 2, 1000].all
  (Effect4.Program.rc112.admitsNat ·)

-- The program checks, closed, at a nest of naturals and one Boolean.
#guard Api.typeOf program [] =
  some (EffTy.pure (.prod .nat (.prod .bool (.prod .nat (.prod .nat .nat)))))

-- The Lean reference: exact naturals.
#guard (Api.run program 1000).exit =
  some (.success (result 2 false 2305843009213693954 416 5))

-- The exact intermediates, spelled out.
#guard 4503599627370496 + 4503599627370497 = 2 ^ 53 + 1
#guard 4503599627370496 * 512 = 2 ^ 61
#guard 2 ^ 61 + (2 ^ 61 + 5) = 2 ^ 62 + 5
#guard (2 ^ 53 + 1) * 512 = 2 ^ 62 + 512
#guard (2 ^ 62 + 5) / 2 = 2305843009213693954
#guard (2 ^ 62 + 512) % 1000 = 416

-- The printer accepts it and the reader reads the printing back to the same program.
#guard (Api.print program).isOk
#guard Api.readable program

/-- The printed expression, rendered (a rendering; not used by any theorem). -/
def printedExpr : String :=
  match Api.print program with
  | .ok e => TypeScript.Render.expr TypeScript.house0 0 e
  | .error _ => "refused"

/-- The printed declaration block, rendered. -/
def printedModule : String :=
  match Api.printModule "faces" program with
  | some m => TypeScript.Render.module TypeScript.house0 m
  | none => "refused"

/-- The canonical program bytes, as lowercase hex, for the OCaml engine. -/
def bytesHex : String := String.ofList (Effect4.Store.hexOfBytes (Api.bytesOf program))

-- The bytes decode back to the program.
#guard Api.ofBytes (Api.bytesOf program) = some program

/-! ## A literal above `2^53`: admitted, printed, read back, and different in JavaScript

`2^53 + 3 = 9007199254740995`. The checker admits it, the printer writes its digits
(`Codegen/PrintLeaf.lean:158`, rendered by `TypeScript.Render.expr` as `toString`), and the
reader reads the digits back to the same natural (`Codegen/Read.lean:149`). JavaScript reads the
literal to the nearest double, `9007199254740996` (`ts/faces-run.log`). No step refuses. -/

def bigLiteral : Api.Program := .succeed (lit 9007199254740995)

#guard Api.typeOf bigLiteral [] = some (EffTy.pure .nat)
#guard (Api.run bigLiteral 100).exit = some (.success (.nat 9007199254740995))
#guard (match Api.print bigLiteral with
  | .ok e => TypeScript.Render.expr TypeScript.house0 0 e
  | .error _ => "refused") = "Effect.succeed(9007199254740995)"
#guard Api.read (.call (.ident "Effect.succeed") [.int 9007199254740995]) = .ok bigLiteral
#guard Api.readable bigLiteral

/-- A literal at `2^62`, one past OCaml's `max_int`: Lean runs it; its bytes are printed for
the OCaml decoder (`ocaml/faces.log` shows the engine refusing to decode them). -/
def literal62 : Api.Program := .succeed (lit (2 ^ 62))

#guard (Api.run literal62 100).exit = some (.success (.nat (2 ^ 62)))
#guard Api.ofBytes (Api.bytesOf literal62) = some literal62

#eval IO.println printedExpr
#eval IO.println printedModule
#eval IO.println s!"bytes {(Api.bytesOf program).length}: {bytesHex}"
#eval IO.println s!"literal62 bytes: {String.ofList (Effect4.Store.hexOfBytes (Api.bytesOf literal62))}"

end Research.Pass.Numbers.Faces
