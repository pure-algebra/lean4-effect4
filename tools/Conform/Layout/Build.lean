import Conform.Layout.Layout

/-!
# Conform.Layout.Build — materialising a target's convention into explicit rules

**What it is.** A target that says "every other inductive is a tagged object" has a
*convention*, not a rule; `layout.covers` may not read a convention, because a convention is a
default and a default is exactly what hides a missing case. These builders turn a convention
plus one `TypeView` into an explicit `Rule`, so the table a target ships has one row per type
and the check can refuse a type the convention never reached.

Every builder takes its naming as a function argument (`tagOf`, `fieldOf`, `ctorOf`), so the
module names no target and no declaration.

**Depends on.** `Conform.Layout.Layout`.

**Properties.**
* **The payload is the declaration's.** A named payload's field list is the constructor's own
  relevant binder names put through the target's `fieldOf`, in declaration order, so
  `layout.covers`'s arity comparison is against the same list the emitter would write — *by
  construction*.
* **Indices are the declaration's.** `indexed` and `intTagField` take `CtorView.index`, which
  `Conform.Layout.Reflect` read from `InductiveVal.ctors` — *by construction*.
-/

namespace Conform.Layout.Build

open Conform.Layout
open Lean (Name)

/-- Every constructor tagged by a string in a named field, payload in sibling named fields. -/
def tagField (tv : TypeView) (field : String) (tagOf : String → String)
    (fieldOf : String → String) (note : String := "") : Rule :=
  { type := tv.name, discrimination := .tagField field, container := .objectC, note
    ctors := tv.ctors.map fun cv =>
      { ctor := cv.name, tag := tagOf cv.name, intTag := cv.index
        payload := .named (cv.fields.map fun f => fieldOf f.name) } }

/-- One constructor, named payload fields, no tag: a Lean structure in a target that has
records or plain objects. -/
def record (tv : TypeView) (fieldOf : String → String) (note : String := "") : Rule :=
  { type := tv.name, discrimination := .record, container := .objectC, note
    ctors := tv.ctors.map fun cv =>
      { ctor := cv.name, tag := cv.name, intTag := cv.index
        payload := .named (cv.fields.map fun f => fieldOf f.name) } }

/-- The target's own variants, one frame per constructor, arguments positional. -/
def variant (tv : TypeView) (ctorOf : String → String) (note : String := "") : Rule :=
  { type := tv.name, discrimination := .variant, container := .frameC, note
    ctors := tv.ctors.map fun cv =>
      { ctor := cv.name, tag := ctorOf cv.name, intTag := cv.index
        payload := if cv.fields.isEmpty then .erased else .positional } }

/-- The constructor index outside the payload, arguments positional: the canonical wire. -/
def indexed (tv : TypeView) (note : String := "") : Rule :=
  { type := tv.name, discrimination := .indexed, container := .frameC, note
    ctors := tv.ctors.map fun cv =>
      { ctor := cv.name, tag := cv.name, intTag := cv.index
        payload := if cv.fields.isEmpty then .erased else .positional } }

/-- All-nullary constructors as string literals. -/
def literalUnion (tv : TypeView) (tagOf : String → String) (note : String := "") : Rule :=
  { type := tv.name, discrimination := .literalUnion, container := .literalC, note
    ctors := tv.ctors.map fun cv =>
      { ctor := cv.name, tag := tagOf cv.name, intTag := cv.index, payload := .erased } }

/-- A source scalar on one of the target's own scalars. The type needs no world entry: its
values are the language's literals, not constructor applications. -/
def scalar (type : Name) (kind : ScalarKind) (dom : ScalarDomain)
    (restriction : Option String := none) (note : String := "") : Rule :=
  { type, discrimination := .nativeScalar kind, container := .scalarC
    ctors := [], scalar := some dom, domainRestriction := restriction, note }

/-- `Unit`: one nullary constructor carried by the target's own unit. -/
def unitScalar (type : Name) (ctor : String) (note : String := "") : Rule :=
  { type, discrimination := .nativeScalar .unitK, container := .scalarC
    ctors := [{ ctor, payload := .erased }], scalar := some .exact, note }

/-- `Option` as the target's null. -/
def nullableOption (type : Name) (noneCtor someCtor : String)
    (applies : Option (List TypeRef) := none) (note : String := "") : Rule :=
  { type, applies, discrimination := .nullable noneCtor, container := .nullOrC, note
    ctors := [ { ctor := noneCtor, tag := noneCtor, intTag := 0, payload := .erased }
             , { ctor := someCtor, tag := someCtor, intTag := 1, payload := .single } ] }

/-- `Option` as the target's own two-frame option. -/
def nativeOption (type : Name) (noneCtor someCtor noneFrame someFrame : String)
    (note : String := "") : Rule :=
  { type, discrimination := .nativeOption noneFrame someFrame, container := .frameC, note
    ctors := [ { ctor := noneCtor, tag := noneFrame, intTag := 0, payload := .erased }
             , { ctor := someCtor, tag := someFrame, intTag := 1, payload := .single } ] }

/-- A cons-list as the target's own sequence. -/
def nativeSeq (type : Name) (nilCtor consCtor : String) (note : String := "") : Rule :=
  { type, discrimination := .nativeSeq, container := .arrayC, note
    ctors := [ { ctor := nilCtor, tag := nilCtor, intTag := 0, payload := .erased }
             , { ctor := consCtor, tag := consCtor, intTag := 1, payload := .positional } ] }

/-- A single-constructor type as the target's own tuple. -/
def nativeTuple (type : Name) (ctor : String) (note : String := "") : Rule :=
  { type, discrimination := .nativeTuple, container := .tupleC, note
    ctors := [{ ctor, tag := ctor, intTag := 0, payload := .positional }] }

/-- A single-constructor, single-relevant-field type erased to its field. -/
def unboxed (type : Name) (ctor : String) (note : String := "") : Rule :=
  { type, discrimination := .unboxed, container := .scalarC, note
    ctors := [{ ctor, tag := ctor, intTag := 0, payload := .single }] }

/-- Lean's own spelling, unchanged: the identity naming a target uses when it keeps the
declaration's names. -/
def verbatim (s : String) : String := s

end Conform.Layout.Build
