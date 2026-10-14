import Effect4.Program.Compile

/-!
Finite controls for stage 0a; placement: rows-block-host, translation-simulation, R6.
The controls inspect counted suspension hops, not whole scheduler execution.
The first is a deliberately untyped parameter access across an ordinary call.
The second keeps explicit invocation parameters working.
-/
namespace Proc6LexicalControl
open Effect4 Effect4.Machine Effect4.Program

/-- Follow only suspension bodies, leaving all other instructions unchanged. -/
def hops (root : NativeEff) : Nat → NCode → NCode
  | 0, code => code
  | n + 1, code => match code with
    | Prim.suspend thunk => hops root n (suspendBodyAt root thunk)
    | _ => code

/-- Definition 1 has a parameter; it calls definition 0 without passing one.
Definition 0 attempts to read parameter 0. Its caller's argument returns 99. -/
def nestedCall : NativeEff :=
  .defs []
    (.cons (.perform (.param 0) (.lit .unit))
      (.cons (.perform (.call 0) (.lit .unit)) .nil))
    (.invoke 1 (.lit .unit) (.cons (.succeed (.lit (.nat 99))) .nil)) .nil

def start : Point := { path := [], env := [], fuel := 20, tape := [] }

-- main invoke -> definition 1's call -> definition 0's parameter -> missing parameter.
-- Before stage 0a this reaches success 99 by borrowing the caller's parameter.
#guard (hops nestedCall 3 (compileEff nestedCall start)).asExit? =
  (badShape : NCode).asExit?

-- Inspect the actual ordinary-call hop: it puts an empty frame above its caller's frame.
#guard (match hops nestedCall 2 (compileEff nestedCall start) with
  | Prim.suspend (.body p) => p.params.map List.length
  | _ => []) = [0, 1]

/-- Explicit invocation passes a program that returns 7 to definition 0. -/
def explicitInvoke : NativeEff :=
  .defs [] (.cons (.perform (.param 0) (.lit .unit)) .nil)
    (.invoke 0 (.lit .unit) (.cons (.succeed (.lit (.nat 7))) .nil)) .nil

-- main invoke -> parameter -> explicitly passed program.
#guard (hops explicitInvoke 2 (compileEff explicitInvoke start)).asExit? =
  some (Exit.success (.nat 7))

end Proc6LexicalControl
