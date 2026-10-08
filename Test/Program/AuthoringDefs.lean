import Effect4.Program.Authoring.Defs
import Effect4.Program.Authoring.Lifts
import Effect4.Codegen.PrintLeaf

/-!
# Authoring definitions: parameter counts

`Def.of` checks the declared parameter count against the operation's curried argument count.
These finite controls cover zero, one and three arguments, and refuse missing or excess declarations.
Low-level `DefSrc` remains explicit. Calls still resolve declarations by name.
-/

set_option autoImplicit false

namespace Test.Program.AuthoringDefs

open Effect4.Program Effect4.Program.Authoring

-- Missing declarations previously substituted unit for the operation's argument.
/--
error: could not synthesize default value for parameter '_arity' using tactics
---
error: Tactic `rfl` failed: The left-hand side
  [].length
is not definitionally equal to the right-hand side
  Params.arity (TermSrc → Src NativeOp)

⊢ [].length = Params.arity (TermSrc → Src NativeOp)
-/
#guard_msgs (error) in
example := Def.of "missing" [] .unit
  (fun (x : TermSrc) => succeed x : TermSrc → Src NativeOp)

-- An excess unit declaration previously admitted the generated zero-argument call.
/--
error: could not synthesize default value for parameter '_arity' using tactics
---
error: Tactic `rfl` failed: The left-hand side
  [("ignored", Ty.unit)].length
is not definitionally equal to the right-hand side
  Params.arity (Src NativeOp)

⊢ [("ignored", Ty.unit)].length = Params.arity (Src NativeOp)
-/
#guard_msgs (error) in
example := Def.of "extra" [("ignored", Ty.unit)] .nat
  (succeed (nat 7) : Src NativeOp)

-- A curried argument cannot be omitted even when the body ignores it.
/--
error: could not synthesize default value for parameter '_arity' using tactics
---
error: Tactic `rfl` failed: The left-hand side
  [("first", Ty.nat)].length
is not definitionally equal to the right-hand side
  Params.arity (TermSrc → TermSrc → Src NativeOp)

⊢ [("first", Ty.nat)].length = Params.arity (TermSrc → TermSrc → Src NativeOp)
-/
#guard_msgs (error) in
example := Def.of "missingSecond" [("first", Ty.nat)] .nat
  (fun (x _ : TermSrc) => succeed x : TermSrc → TermSrc → Src NativeOp)

def zero := Def.of "zero" [] .nat (succeed (nat 7) : Src NativeOp)
def one := Def.of "one" [("x", Ty.nat)] .nat
  (fun (x : TermSrc) => succeed x : TermSrc → Src NativeOp)
def many := Def.of "many" [("a", Ty.nat), ("b", Ty.bool), ("c", Ty.string)] .string
  (fun (_ _ c : TermSrc) => succeed c : TermSrc → TermSrc → TermSrc → Src NativeOp)

#guard Params.arity (F := Src NativeOp) = 0
#guard Params.arity (F := TermSrc → Src NativeOp) = 1
#guard Params.arity (F := TermSrc → TermSrc → TermSrc → Src NativeOp) = 3

#guard zero.src.elaborate {} [0, 0] = .ok (.succeed (.lit (.nat 7)))
#guard one.src.elaborate {} [0, 0] = .ok (.succeed (.var 0))
#guard many.src.elaborate {} [0, 0] =
  .ok (.succeed (.app "snd" (.cons (.app "snd" (.cons (.var 0) .nil)) .nil)))

#guard zero.call { defs := [("zero", 0)] } [] =
  .ok (.perform (.call 0) (.lit .unit))
#guard one.call (nat 11) { defs := [("one", 1)] } [] =
  .ok (.perform (.call 1) (.lit (.nat 11)))
#guard many.call (nat 11) (bool true) (str "last") { defs := [("many", 2)] } [] =
  .ok (.perform (.call 2)
    (.app "pair" (.cons (.lit (.nat 11))
      (.cons (.app "pair" (.cons (.lit (.bool true))
        (.cons (.lit (.str "last")) .nil))) .nil))))

/-! ## Generated binding names

These finite checks exercise target identifier admission and the printer's export-name checks.
The examples do not establish an injectivity theorem.
-/

#guard Def.qualifiedName "Numbers" "take" = "e4$Numbers$take"
#guard Def.qualifiedName "" "" = "e4$$"
#guard Def.qualifiedName "a.b" "take$" = "e4$a_46_b$take_36_"
#guard Def.qualifiedName "_" "λ" = "e4$_95_$_206__187_"
#guard Def.qualifiedName "猫" "offer" = "e4$_231__140__171_$offer"

#guard (["", "Numbers", "1", "a.b", "a$b", "_", "_36_", "a b", "λ", "猫",
    "await", "pipe", "a0", "_%request0", "x\n"] : List String).all fun instanceName =>
  (["", "take", "1", ".", "$", "_", "_36_", "x y", "λ", "猫", "class"] : List String).all
    fun operation =>
      TypeScript.targetIdentifier (Def.qualifiedName instanceName operation) &&
        (exportNameFault (Def.qualifiedName instanceName operation)).isNone

-- Separators and decimal-looking author names cannot imitate encoded components.
#guard Def.qualifiedName "a$b" "c" != Def.qualifiedName "a" "b$c"
#guard Def.qualifiedName "$" "take" != Def.qualifiedName "_36_" "take"
#guard Def.qualifiedName "a_" "b" != Def.qualifiedName "a" "_b"
#guard Def.qualifiedName "" "take" != Def.qualifiedName "take" ""
#guard Def.qualifiedName "λ" "take" != Def.qualifiedName "_206__187_" "take"

end Test.Program.AuthoringDefs
