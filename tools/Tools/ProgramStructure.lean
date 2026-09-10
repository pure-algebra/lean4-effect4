import Conform.Source.Description
import Effect4.Program.Native

/-!
Effect4's selected source families and instantiated mutual groups. Generic extraction and
constructor metadata live in Conform.Source; this facade owns the program selection and
its stable JSON projection. Target generators consume this selection.
-/
namespace Tools.ProgramStructure
open Lean Meta

abbrev Shape := Conform.Source.Shape
abbrev Spec := Conform.Source.Spec
abbrev Field := Conform.Source.Field
abbrev Ctor := Conform.Source.Ctor
abbrev Family := Conform.Source.Family

def blocks : List (List Spec) :=
  [ [⟨`Effect4.Program.Ty, "ty", []⟩]
  , [⟨`Effect4.Program.Lit, "lit", []⟩]
  , [⟨`Effect4.Program.Term, "term", []⟩, ⟨`Effect4.Program.Terms, "terms", []⟩]
  , [⟨`Effect4.Program.CauseTerm, "cause_term", []⟩]
  , [⟨`Effect4.Supervision.MaskMode, "mask_mode", []⟩]
  , [⟨`Effect4.Supervision.ForkOptions, "fork_options", []⟩]
  , [⟨`Effect4.Supervision.ObserverMode, "observer_mode", []⟩]
  , [⟨`Effect4.FinalizerStrategy, "finalizer_strategy", []⟩]
  , [⟨`Effect4.Machine.FnName, "fn_name", []⟩]
  , [⟨`Effect4.Program.NativeOp, "native_op", []⟩]
  -- the service key before the `Eff` group since the join (2026-09-07): `provideLayer`,
  -- `service`, `provideService` and `LayerTerm` carry a `ServiceKey`
  , [⟨`Effect4.ServiceName, "service_name", []⟩]
  , [⟨`Effect4.ServiceTypeCode, "service_type_code", []⟩]
  , [⟨`Effect4.ServiceKey, "service_key", []⟩]
  , [ ⟨`Effect4.Program.Eff, "eff", [`Effect4.Program.NativeOp]⟩, ⟨`Effect4.Program.Stmt, "stmt", [`Effect4.Program.NativeOp]⟩
    , ⟨`Effect4.Program.Stmts, "stmts", [`Effect4.Program.NativeOp]⟩, ⟨`Effect4.Program.Effs, "effs", [`Effect4.Program.NativeOp]⟩
    , ⟨`Effect4.Program.ActionTerm, "action_term", [`Effect4.Program.NativeOp]⟩
    , ⟨`Effect4.Program.LayerTerm, "layer_term", [`Effect4.Program.NativeOp]⟩
    -- the host rows slice (2026-09-08): the spine of `LayerTerm.mergeAll`
    , ⟨`Effect4.Program.LayerTerms, "layer_terms", [`Effect4.Program.NativeOp]⟩ ]
  , [⟨`Effect4.Program.RowKind, "row_kind", []⟩]
  , [⟨`Effect4.Program.RowShape, "row_shape", []⟩]
  , [⟨`Effect4.Program.Registration, "registration", []⟩]
  , [⟨`Effect4.Program.Row, "row", []⟩]
  , [⟨`Effect4.Program.EffTy, "eff_ty", []⟩] ]

def allSpecs : List Spec := blocks.flatten

def config : Conform.Source.Config := ⟨allSpecs, [`Effect4.Row]⟩
abbrev groundType := Conform.Source.groundType
def readShape := Conform.Source.readShape config
def readFamily := Conform.Source.readFamily config
def readBlocks : MetaM (List (List Family)) := blocks.mapM (·.mapM readFamily)

/-- Compare selected deriving seeds by instantiated mutual closure, not manifest spelling. -/
def checkProgramSeeds (seeds : Array Expr) : MetaM Unit := do
  let mut actual : List Expr := []
  for seed in seeds do
    let .const name _ := seed.getAppFn | throwError "ProgramStructure: nonnominal seed {seed}"
    let info ← getConstInfoInduct name
    for member in info.all do
      let ty := mkAppN (mkConst member) seed.getAppArgs
      if !actual.contains ty then actual := actual ++ [ty]
  let expected := allSpecs.map groundType
  unless actual.length == expected.length && actual.all expected.contains do
    throwError "ProgramStructure: Program manifest mutual closure differs; missing {expected.filter (!actual.contains ·)}, extra {actual.filter (!expected.contains ·)}"
  -- This also refuses a new unsupported field rather than accepting a name-only match.
  discard readBlocks

abbrev shapeJson := Conform.Source.shapeJson
abbrev familyJson := Conform.Source.familyJson
def descriptorJson := Conform.Source.descriptorJson "effect4-program-structure-v1"

end Tools.ProgramStructure
