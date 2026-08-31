import Lean
import Cas.Values.Json
import Gate
import Walk

/-!
# The report lane — `lake exe surface`

Per-declaration reports for the whole `Cas` library, extracted from
the COMPILED environment — the pattern source is Concrete's proof
report (`lambdaclass/concrete`, `Concrete/Report/Report.lean`,
observed 2026-08-28): per-definition entries with canonical labels,
an evidence dimension, and summary totals, so the surface is held as
a ledger, not a feeling.

Each declaration carries its name, kind, pretty-printed signature,
and doc coverage; each THEOREM additionally carries its axiom report
(`collectAxioms`), and the document heads with the library-wide axiom
census — the estate's axiom-hygiene obligation, automated. `--check`
is the byte-identity gate in `check:cas`: any change to the type
surface, any new axiom dependency, any lost docstring is a visible
diff, never a drift.

The walk itself lives in `Walk` and is shared with every other
projection over the same environment; this module is the ledger's
rendering and its verdict vocabulary, nothing more. `Walk.libraryImports`
folds the `Cas.Backend.*` leaves into the walk (queue item 24), so the
backend's declarations are in this ledger — the one declared re-gen
event that move cost.

Compiler-generated boilerplate is excluded and field projections stay;
`Walk.isGenerated` is where that line is drawn. Signatures print at a
fixed width by the pinned toolchain's pretty printer; a toolchain bump
that reprints them is a re-gen event the gate makes loud.
-/

open Lean Walk

def outPath : System.FilePath := "meta" / "out" / "surface.META.json"

/-- The ledger's emitted header. The document declared no version
before this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "surface"
  module := "library/cas/tools/Surface.lean"

def rowJson (r : Row) : Cas.Json.Value :=
  .obj <|
    [("name", .str r.name), ("kind", .str r.kind),
     ("signature", .str r.signature),
     ("documented", .bool r.documented)] ++
    (if r.touches.isEmpty then []
     else [("touches", .arr (r.touches.map Cas.Json.Value.str))]) ++
    (if r.carriers.isEmpty then []
     else [("carriers", .arr (r.carriers.map Cas.Json.Value.str))]) ++
    (if r.kind == "theorem" then
      [("axioms", .arr (r.axioms.map Cas.Json.Value.str))]
     else [])

def document (modules : Array (Name × Array Row)) : String :=
  let kinds := ["axiom", "class", "def", "inductive", "instance",
                "opaque", "structure", "theorem"]
  let allRows := (modules.map Prod.snd).flatten
  let totals : List (String × Cas.Json.Value) :=
    kinds.filterMap fun k =>
      let c := allRows.filter (·.kind == k) |>.size
      if c == 0 then none else some (k, .nat c)
  let axiomNames := (allRows.toList.flatMap (·.axioms)).eraseDups.mergeSort (· < ·)
  let axiomCensus : List (String × Cas.Json.Value) :=
    axiomNames.map fun a =>
      (a, .nat (allRows.filter (·.axioms.contains a) |>.size))
  let unclean := axiomNames.filter fun a =>
    !cleanAxioms.any (fun c => c.toString == a)
  let documented := allRows.filter (·.documented) |>.size
  let carrierNames := (allRows.toList.flatMap (·.carriers)).eraseDups.mergeSort (· < ·)
  let carrierCensus : List (String × Cas.Json.Value) :=
    carrierNames.map fun c =>
      (c, .nat (allRows.filter (·.carriers.contains c) |>.size))
  let areaNames := (allRows.toList.flatMap (·.touches)).eraseDups.mergeSort (· < ·)
  let areaCensus : List (String × Cas.Json.Value) :=
    areaNames.map fun a =>
      (a, .nat (allRows.filter (·.touches.contains a) |>.size))
  let moduleJson (m : Name × Array Row) : Cas.Json.Value :=
    .obj [
      ("module", .str m.1.toString),
      ("declarations", .nat m.2.size),
      ("documented", .nat (m.2.filter (·.documented) |>.size)),
      ("surface", .arr (m.2.toList.map rowJson))]
  Cas.Json.render (emitted.obj [
    ("library", .str "Cas"),
    ("declarations", .nat allRows.size),
    ("documented", .nat documented),
    ("totals", .obj totals),
    ("axiomCensus", .obj axiomCensus),
    ("beyondCleanAxioms", .arr (unclean.map Cas.Json.Value.str)),
    ("areaCensus", .obj areaCensus),
    ("carrierCensus", .obj carrierCensus),
    ("modules", .arr (modules.toList.map moduleJson))]) ++ "\n"

/-- The ledger as the driver's single fixture. The environment walk
runs HERE — inside the action the driver forces only after arguments
parse — so a typo'd flag never pays for the whole import. -/
unsafe def fixtures : IO (List Gate.Fixture) := do
  enableInitializersExecution
  let modules ← Walk.run Walk.collect
  let declarations := modules.foldl (fun n m => n + m.2.size) 0
  return [⟨outPath, document modules, s!"{declarations} declarations"⟩]

unsafe def main := Gate.main "lake exe surface" fixtures
