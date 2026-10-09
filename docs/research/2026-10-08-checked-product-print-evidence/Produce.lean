import Effect4.Codegen.PrintTyped
import Effect4.Program.NativeAtom
import TypeScript.Render
open Effect4 Effect4.Program Effect4.Machine Effect4.Codegen TypeScript
open TypeScript.Render (expr)
-- Finite full checked-expression output; this is not Api.emitModule.
#eval (Program.printTyped nativeSignature [.union .nat .string, .refOf .nat]
 (.perform (.refModifyWith (.app "tuple" (.cons (.var 0) (.cons (.var 2) .nil)))) (.var 1))).map
 (expr house0 0)
#eval (Program.printTyped nativeSignature [.union .nat .string, .union .nat .string]
 (.succeed (.app "tuple" (.cons (.var 0) (.cons (.var 1) .nil))))).map (expr house0 0)
