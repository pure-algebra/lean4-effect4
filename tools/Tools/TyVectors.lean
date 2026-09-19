import Effect4.Program.Ty
import Effect4.Program.Native
import Tools.ProfileJson
import Lean.Data.Json

/-!
# Tools.TyVectors — the pairs the assignability differential asks the target about

    lake env lean -M4096 --run tools/Tools/TyVectors.lean <out.tsv>

`Ty.sub` is this language's order. The target has an order of its own, and the two are only
related by a claim nobody had checked: plan 1.10. This driver writes the questions — one line
per ordered pair — and `tools/target/assignability.ts` asks the one compiler and classifies
every disagreement.

    id  left  right  renderLeft  renderRight  subLR  subRL  mutantLR  mutantRL

`left`/`right` are the `Ty` as JSON (`Tools.ProfileJson.tyJson`), `render*` the strings
`Ty.renderRaw` prints — the same printer the row lane uses, so a pair is asked in the syntax a
printed program would actually contain. `sub*` is `Ty.sub` in each direction.

`mutant*` is the red control, and it is why the file has four verdict columns instead of two:
`Ty.sub` is invariant at `refOf` (decisions row 55 — a cell is written through its handle), and
`subMutant` is that one arm swapped for the covariant rule. A differential that cannot tell the
two apart is not measuring anything; `assignability.ts` prints how many pairs catch it.

The alphabet follows `tools/Conform/Effect4/LcnfSemantics.lean`'s `leaves`/`layer`/`small`
(read, not edited) and extends it where that enumeration is silent: the top (`unknown`,
row 46), literals (DI-55), and the two handle heads `refOf`/`deferredOf`. Pairs grow
quadratically, so the alphabet is small per head and the families are deliberate rather than a
full cross product: a core of one type per head, then the variance probes — `Ref<never>`,
`Ref<unknown>`, `Ref<number>` against each other, where a swapped invariance arm hides, and the
`Fiber` family, where a swapped covariance arm does.

The three gaps of `docs/research/2026-09-18-research-type-algebra.md` §5.2 are the first rows:
`gap/option-union` (`option` does not distribute over a union), `gap/prod-never`
(`prod never nat` is uninhabited and is not `never`). The third — function types are absent, so
no contravariant position exists anywhere in the language — has no pair to witness it: there is
no arrow to write on either side. It is recorded here and in the generated file's header.
-/

open Effect4.Program

namespace Tools.TyVectors

/-- `Ty.sub` with one arm swapped: `refOf` read covariantly instead of invariantly. The control
for the differential — nothing else in the tree may use it. -/
def subMutant (a b : Ty) : Bool :=
  match a, b with
  | .refOf x, .refOf y => Ty.sub x y
  | _, _ => Ty.sub a b

def refT : Ty := .handle NativeOp.refTarget

/-- One type per head, plus the top, the bottom and a literal: every pair of these is asked.
`int` is not here: it and `nat` are one type in the target (`renderRaw` prints `number` for
both), so every pair naming them would report the printer's collapse instead of the order's
behaviour. The collapse itself is asked once, in the `spelling` family. -/
def core : List Ty :=
  [ .never, .unknown, .unit, .nat, .string, .bool, .lit "a"
  , .option .nat, .list .nat, .prod .nat .string, .except .string .nat
  , .exitOf .nat .string, .causeOf .string, .fiberOf .nat .string, .union .nat .string
  , .refOf .nat, .deferredOf .nat .string, refT, Ty.scope ]

/-- The alphabet each variance probe ranges over. -/
def probe : List Ty := [.never, .unknown, .nat, .string]

def pairsOf (ids : String) (xs ys : List Ty) : List (String × Ty × Ty) :=
  (xs.zipIdx.flatMap fun (x, i) => ys.zipIdx.map fun (y, j) => (s!"{ids}/{i}-{j}", x, y))

/-- The families, in the order they are written. -/
def families : List (String × List Ty × List Ty) :=
  [ ("core", core, core)
  , ("ref", probe.map Ty.refOf, probe.map Ty.refOf)
  , ("fiber", probe.map (fun t => Ty.fiberOf t .string), probe.map (fun t => Ty.fiberOf t .string))
  , ("fiberError", probe.map (Ty.fiberOf .nat), probe.map (Ty.fiberOf .nat))
  , ("deferred", probe.map (fun t => Ty.deferredOf t .string), probe.map (fun t => Ty.deferredOf t .string))
  , ("option", probe.map Ty.option, probe.map Ty.option)
  , ("list", probe.map Ty.list, probe.map Ty.list)
  , ("cause", probe.map Ty.causeOf, probe.map Ty.causeOf)
  , ("exit", probe.map (fun t => Ty.exitOf t .string), probe.map (fun t => Ty.exitOf t .string))
  , ("except", probe.map (fun t => Ty.except .string t), probe.map (fun t => Ty.except .string t))
  , ("prod", probe.map (fun t => Ty.prod t .nat), probe.map (fun t => Ty.prod t .nat))
  , ("lit", [.lit "a", .lit "b", .string, .union (.lit "a") (.lit "b"), .unknown],
           [.lit "a", .lit "b", .string, .union (.lit "a") (.lit "b"), .unknown])
  , ("union", [.union .nat .string, .nat, .string, .never, .unknown, .union .nat (.lit "a")],
             [.union .nat .string, .nat, .string, .never, .unknown, .union .nat (.lit "a")])
    -- where the printer is not injective: two `Ty` with one target spelling. The order can
    -- tell them apart and the target cannot, which is a cut, not a disagreement.
  , ("spelling", [.nat, .int, .refOf .nat, refT], [.nat, .int, .refOf .nat, refT]) ]

/-- The two gaps a pair can witness (§5.2), first. -/
def gaps : List (String × Ty × Ty) :=
  [ ("gap/option-union", .option (.union .nat .string), .union (.option .nat) (.option .string))
  , ("gap/prod-never", .prod .never .nat, .never) ]

def allPairs : List (String × Ty × Ty) :=
  gaps ++ families.flatMap (fun (id, xs, ys) => pairsOf id xs ys)

def line (p : String × Ty × Ty) : String :=
  let (id, a, b) := p
  let bit (x : Bool) := if x then "true" else "false"
  String.intercalate "\t"
    [ id, (Tools.ProfileJson.tyJson a).compress, (Tools.ProfileJson.tyJson b).compress
    , a.renderRaw, b.renderRaw
    , bit (Ty.sub a b), bit (Ty.sub b a), bit (subMutant a b), bit (subMutant b a) ]

def text : String :=
  "# GENERATED by tools/Tools/TyVectors.lean; the questions of plan 1.10, not a result\n" ++
  "# id\tleft\tright\trenderLeft\trenderRight\tsubLR\tsubRL\tmutantLR\tmutantRL\n" ++
  String.intercalate "\n" (allPairs.map line) ++ "\n"

end Tools.TyVectors

def main (args : List String) : IO UInt32 := do
  let some out := args.head? | do
    IO.eprintln "usage: TyVectors.lean <out.tsv>"; return 2
  IO.FS.writeFile out Tools.TyVectors.text
  IO.println s!"wrote {Tools.TyVectors.allPairs.length} pairs to {out}"
  return 0
