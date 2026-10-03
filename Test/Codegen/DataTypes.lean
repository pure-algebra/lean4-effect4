import Effect4.Codegen.Types
import TypeScript.Render

/-!
Finite structural target type controls. The record wrapper consumes this projection.
These controls make no target execution or codec admission claim.
-/

namespace Test.Codegen.DataTypes
open Effect4.Program Effect4.Codegen TypeScript

#guard (Types.ofTy (.record [("nickname", true, .string), ("id", false, .nat)])).map
    (Render.type house0) = some "{ readonly id: number; readonly nickname?: string }"
#guard (Types.ofTy (.record [("nickname", true, .union .string .undefined)])).map
    (Render.type house0) = some "{ readonly nickname?: string | undefined }"
#guard (Types.ofTy (.record [("a-b", false, .null), ("__proto__", false, .number)])).map
    (Render.type house0) = some "{ readonly __proto__: number; readonly \"a-b\": null }"
#guard (Types.ofTy (.tuple [.nat, .record [("x", true, .bytes)]])).map
    (Render.type house0) = some "readonly [number, { readonly x?: Uint8Array }]"
#guard (Types.ofTy (.tuple [])).map (Render.type house0) = some "readonly []"
#guard (Types.ofTy (.map .string (.option .undefined))).map
    (Render.type house0) = some "Readonly<Record<string, Option.Option<undefined>>>"
#guard Types.ofTy (.map .nat .string) = none
#guard Types.ofTy (.map (.var 0) .string) = none
#guard Types.ofTy (.record [("x", true, .var 0)]) = none
#guard Types.ofTy (.app "Unresolved" [.string]) = none

end Test.Codegen.DataTypes
