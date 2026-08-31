import Cas.Schema.Deriving
import Cas.Schema.SelfCodec

/-!
# `cas_struct` — the kind-authoring notation

One declaration, three artifacts:

```
cas_struct Sample where
  label : String
  count : SafeInt
```

elaborates to the native structure, its `Described` instance (the
canonical schema code plus the carrier equivalence, via the deriving
handler), and the raw-schema surface:

- `Sample.schemaCode : Ast` — the code the structure is described by;
- `Sample.rawSchema : String` — the canonical schema-node payload
  (`SelfCodec`), the byte form the cross-runtime pin compares.

Its sibling `cas_union` authors a KIND WITH ALTERNATIVES:

```
cas_union Step where
  | wait
  | move (distance : SafeInt)
  | greet (name : String) (title : Option String)
```

which lands the same three artifacts over a tagged union — one member
per constructor, each a struct whose first field is the `_tag` literal,
members ordered by tag, mode `oneOf` — plus the handler's
`Step.schemaDiscriminated`, the proof that the code IS discriminated
and therefore denotes the member sum rather than `Empty`.

Both notations are pure syntax→syntax rewrites. All the semantic work
stays in the deriving handler, where `InductiveVal` is in scope: that
is what keeps `cas_struct`'s emission byte-identical across this
growth, and what will keep both of them unchanged when the next
constructor arrives.

The notation is deliberately the FORWARD-LOOKING seam: literal pins,
kind tags, and named recursion land here as the universe grows,
without touching call sites. Like `Cas.Schema.Deriving`, this module
keeps compiler metaprogramming an opt-in import — tools and examples
import it; the runtime facade does not.
-/

namespace Cas.Schema.Notation

open Lean

/-- One field: `name : type`. -/
syntax casSchemaField := ident " : " term

/-- The kind-authoring notation. A doc comment, when given, lands on
the generated structure. -/
syntax (docComment)? "cas_struct " ident " where "
  withPosition((colGe casSchemaField ppLine)*) : command

macro_rules
  | `($[$doc:docComment]? cas_struct $name:ident where $fields:casSchemaField*) => do
    let mut binders : Array (TSyntax ``Lean.Parser.Command.structExplicitBinder) := #[]
    for f in fields do
      match f with
      | `(casSchemaField| $fname:ident : $ftype:term) =>
        binders := binders.push
          (← `(Lean.Parser.Command.structExplicitBinder| ($fname:ident : $ftype)))
      | _ => Macro.throwUnsupported
    let codeId := mkIdentFrom name (name.getId ++ `schemaCode)
    let rawId := mkIdentFrom name (name.getId ++ `rawSchema)
    let structCmd ← `($[$doc:docComment]? structure $name where
      $[$binders:structExplicitBinder]*
      deriving Cas.Schema.Described)
    let codeCmd ← `(def $codeId : Cas.Schema.Ast :=
      Cas.Schema.Described.code (α := $name))
    let rawCmd ← `(def $rawId : String := Cas.Schema.Ast.payload $codeId)
    return mkNullNode #[structCmd, codeCmd, rawCmd]

/-- One alternative: `| ctor (field : type) …`. Zero fields is a
nullary constructor, which derives as a member carrying nothing but its
own `_tag`. -/
syntax casUnionAlt := " | " ident (ppSpace "(" ident " : " term ")")*

/-- The alternatives-authoring notation. A doc comment, when given,
lands on the generated inductive. -/
syntax (docComment)? "cas_union " ident " where "
  withPosition((colGe casUnionAlt ppLine)*) : command

macro_rules
  | `($[$doc:docComment]? cas_union $name:ident where $alts:casUnionAlt*) => do
    let mut ctors : Array (TSyntax ``Lean.Parser.Command.ctor) := #[]
    for alt in alts do
      match alt with
      | `(casUnionAlt| | $ctor:ident $[($fname:ident : $ftype:term)]*) =>
        let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
        for h : i in *...fname.size do
          binders := binders.push
            (← `(Lean.Parser.Term.bracketedBinderF| ($(fname[i]):ident : $(ftype[i]!))))
        ctors := ctors.push
          (← `(Lean.Parser.Command.ctor| | $ctor:ident $binders*))
      | _ => Macro.throwUnsupported
    let codeId := mkIdentFrom name (name.getId ++ `schemaCode)
    let rawId := mkIdentFrom name (name.getId ++ `rawSchema)
    let indCmd ← `($[$doc:docComment]? inductive $name where
      $[$ctors:ctor]*
      deriving Cas.Schema.Described)
    let codeCmd ← `(def $codeId : Cas.Schema.Ast :=
      Cas.Schema.Described.code (α := $name))
    let rawCmd ← `(def $rawId : String := Cas.Schema.Ast.payload $codeId)
    return mkNullNode #[indCmd, codeCmd, rawCmd]

end Cas.Schema.Notation
