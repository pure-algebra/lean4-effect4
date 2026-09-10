import Conform.Effect4.LayoutWorld
import Conform.Layout.Native

/-!
# Conform.Effect4.TargetLeanNative — the fifth target: what Lean's own runtime does

**What it is.** The Effect4 configuration of `Conform.Layout.Native`. The other four targets in
this seat are transcriptions of an emitter's source, and §7 of `seat-layout.md` names that
transcription as the tool's one unchecked input. This one is not transcribed: every rule comes
from `Lean.Compiler.LCNF.getCtorLayout` and `hasTrivialStructure?` at reflection time, and the
only rules written by hand are the five *scalar* rules for the runtime's builtin types, which
have no constructor information to read.

| what | rule | where it comes from |
| --- | --- | --- |
| a type the compiler erases to its one relevant field | `unboxed` | `hasTrivialStructure?` — `Effect4.Row`, `Effect4.ServiceName`, `Effect4.ServiceTypeCode` |
| everything else | `indexed`, `intTag` = the runtime tag | `getCtorLayout`'s `CtorInfo.cidx` |
| the payload | `positional`, or `erased` when nothing survives | the same call's `CtorFieldInfo` array |
| `Nat` | `nativeScalar bigint`, domain **`exact`** | a `Nat` is a tagged small value or a GMP bignum: the runtime narrows nothing |
| `String` | `nativeScalar string`, domain `utf8` | a Lean string is its UTF-8 bytes |
| `Bool`, `Unit`, `PUnit` | `nativeScalar` | unboxed scalars (`Bool.false`/`Bool.true` are tags 0 and 1 with no fields) |

**The two answers the brief asked for.**

* **`Option` is tagged, never nullable.** `Option.none` is tag 0 with no fields — an unboxed
  `lean_box(0)` — and `Option.some` is tag 1 with one object field, so `some none` is a boxed
  cell *containing* `lean_box(0)` and is a different runtime value from `lean_box(0)` itself.
  The X2 collision (`Laws.nullable_collides`) cannot be spelled in this layout, for the same
  reason it cannot be spelled in OCaml's: the discrimination is `indexed`, whose admissibility
  condition (`Laws.frame_ne_of_name_ne`) puts **no condition on the payload**.
* **A trivial structure is `unboxed`.** `hasTrivialStructure?` is exactly the compiler's own
  "this single-constructor single-relevant-field type is its field", which is the `unboxed`
  discrimination, admissible under `Laws.Injective.id`. `Effect4.Row` is the case
  `src/OCaml5/Eff/World.lean:116-117` calls "the one non-structural rule" — and it is not an
  exception here either: the Lean runtime erases it for the same reason OCaml carries it as a
  list.

**Whether `layout.injective` passes by construction.** Yes, and the reason is not a measurement.
Every rule of this target is `indexed`, `unboxed` or `nativeScalar`:

* `indexed` is admissible iff the tags are pairwise distinct, and the tags *are*
  `ConstructorVal.cidx`, which the compiler assigns as the position in `InductiveVal.ctors` —
  so they are distinct because they are an enumeration;
* `unboxed` is admissible iff the type has one constructor with one relevant field, which is
  the definition of `hasTrivialStructure?` returning `some`;
* `nativeScalar` is admissible iff the domain is `exact` (or `utf8`/`utf16`), and every scalar
  domain here is one of those — the native runtime is the only one of the five targets that
  narrows **nothing**, so it is the only one that carries no `representation.scalar-domain`
  obligation.

The report is therefore expected to be all-pass, and a refusal in it would be a refutation of
one of those three statements, not a missing rule.

**Depends on.** `Conform.Effect4.LayoutWorld`, `Conform.Layout.Native`.
-/

namespace Conform.Effect4

open Lean (Name)
open Conform.Layout

/-- The five hand rules: the runtime's builtin scalars, which have no constructor information
for `getCtorLayout` to answer with (`Unit.unit` is not even a compiled constructor — `Unit` is
`PUnit`). Each states the domain the *runtime* imposes, which in every case is none. -/
def leanNativeScalars : Array Rule :=
  #[ Build.scalar ``Nat .bigintK .exact none
       "a Nat is a tagged small value or a GMP bignum (lean_object*), so the runtime represents \
every Nat exactly: unlike a JavaScript number (bounded 53) or an OCaml int (bounded 62), this \
target declares no source restriction and needs none"
   , Build.scalar ``String .strK .bytesUtf8 none
       "a Lean String is an object holding its UTF-8 bytes"
   , Build.scalar ``Bool .boolK .exact none
       "Bool.false and Bool.true are getCtorLayout tags 0 and 1 with no fields: two unboxed \
scalars"
   , Build.unitScalar ``Unit "unit" "PUnit.unit is tag 0 with no fields: lean_box(0)"
   , Build.unitScalar ``PUnit "unit" "PUnit.unit is tag 0 with no fields: lean_box(0)" ]

/-- The nestings this target is checked at beyond the world's own field types: the same three
the TypeScript targets declare, so the five reports are comparable subject for subject. -/
def leanNativeUsages : Array Usage :=
  #[ { site := "Effect4.Program.GenTy.joinAnswer result"
       type := .con ``Option [.con ``Option [.con `Effect4.Program.Ty []]] }
   , { site := "the brief's minimal nesting"
       type := .con ``Option [.con ``Option [.con ``Nat []]] }
   , { site := "Effect4.Program.GenTy.merge result"
       type := .con ``Option [.con `Effect4.Program.GenTy []] } ]

/-- The whole table, over a world whose runtime layout has been read. -/
def targetLeanNative (W : World) (natives : Array Native.TypeNative) : Target :=
  Native.target "lean-native"
    "Lean's own runtime layout, read from Lean.Compiler.LCNF.getCtorLayout and \
hasTrivialStructure? rather than transcribed from an emitter; the constructor limits are \
Lean.IR.Checker's, read from the C runtime"
    W leanNativeScalars natives leanNativeUsages

/-- Read the runtime layout of the Effect4 world. -/
def readLeanNative (W : World) : Lean.CoreM (Array Native.TypeNative) := Native.readWorld W

end Conform.Effect4
