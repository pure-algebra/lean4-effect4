import OCaml5.Eff.World
import Effect4.Program.Typing
import Conform.Layout.Reflect

/-!
# Conform.Effect4.LayoutWorld — the closed world the layout checks run over

**What it is.** The Effect4 *configuration* of `Conform.Layout`: the list of type names, with
the instantiation each is taken at, that the four target files are checked against. It is the
closed world `OCaml5.Eff.World.blocks` already fixes — the same world `ocaml/eff` and
`ts/eff/eff.gen.ts` are generated from — plus the containers every rule needs constructor
information for (`Option`, `List`, `Prod`, `Effect4.Row`) and the two typing carriers the
nested-option collision lives in (`GenTy`, and `EffTy`, which `blocks` already has).

This file names Effect4 declarations; nothing under `Conform/Layout` does.

**Depends on.** `OCaml5.Eff.World` (the family list and its OCaml names),
`Effect4.Program.Typing` (`GenTy`), `Conform.Layout.Reflect`.

**Properties.**
* **The instantiation is the one the estate generates at.** `Eff` and its block are taken at
  `Effect4.Program.NativeOp`, read off `OCaml5.Eff.World.blocks`' own `Spec.params`, so the
  world here and the world `eff_types.ml` was generated from are the same list — *by
  construction* (`otyRef`).
-/

namespace Conform.Effect4

open Lean
open Conform.Layout

/-- The Lean type an `OCaml5.Eff.OTy` parameter instantiation stands for. Only the forms
`OCaml5.Eff.World.blocks` actually uses need an answer. -/
def otyRef : OCaml5.Eff.OTy → Option TypeRef
  | .int => some (.con ``Nat [])
  | .bool => some (.con ``Bool [])
  | .string => some (.con ``String [])
  | .unit => some (.con ``Unit [])
  | .named n =>
    (OCaml5.Eff.allSpecs.find? (·.oname == n)).map fun s => TypeRef.con s.leanName []
  | .requirements => some (.con `Effect4.Row [.con `Effect4.ServiceKey []])
  | .option _ | .list _ | .prod _ _ => none

/-- The containers and carriers that are not families of `blocks` but whose constructor
information every target needs. -/
def extraTypes : Array (Name × List TypeRef) :=
  #[ (``Option, []), (``List, []), (``Prod, []), (`Effect4.Row, [])
   , (`Effect4.Program.GenTy, []) ]

/-- The whole request list, in the order the checks report it. -/
def worldRequests : Array (Name × List TypeRef) :=
  (OCaml5.Eff.allSpecs.map fun s => (s.leanName, s.params.filterMap otyRef)).toArray
    ++ extraTypes

/-- The names of the container types the builtin rules own, so a target's family walk skips
them. -/
def containerNames : List Name := [``Option, ``List, ``Prod, `Effect4.Row]

/-- Read the world with the relevance policy the wire and the `eff/` route use: a `Prop` field
is dropped, a type-former field is not (`OCaml5.Eff.World.readFamily`). -/
def readEffect4World : MetaM Conform.Layout.Reflect.Reading :=
  Conform.Layout.Reflect.readWorld .propsOnly worldRequests [`Effect4.Row]

end Conform.Effect4
