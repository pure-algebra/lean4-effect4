import Test.Counterexamples.Program.ContextReset
import Effect4.Laws.Auto.KernelRfl
import ProofGraph.AxiomAudit

/-!
Concept: context-requirements, R5 and R9; row 349 option A.
Helpers serve proposed typed-context-read, provide-context-row and parameter-context-transformer claims.
This probe records row columns until the canonical Ty.contextOf constructor lands.
It adds no program representation or evaluator.
-/
set_option autoImplicit false
namespace Test.MachineModels.ContextSignatures
open Effect4 Effect4.Program Effect4.Machine Effect4.Machine.Env Effect4.Laws.Auto

/-- Answer keys and execution requirements of the proposed typed context reader. -/
def readerColumns (keys : Requirement) : Requirement × Requirement := (keys, keys)

/-- The proposed region preserves answer/error columns and discharges certified supplied keys. -/
def provideColumns (supplied : Requirement) (body : EffTy) : EffTy :=
  { body with requires := Row.diff body.requires supplied }

/-- Discharging provided keys suffices under the merged ambient row.
Consumer: the proposed provideContext typing rule. -/
theorem discharged (ambient supplied required : Requirement)
    (remaining : Row.Subset (Row.diff required supplied) ambient) :
    Row.Subset required (Row.union ambient supplied) := by
  intro key needed
  by_cases provided : key ∈ supplied
  · exact (Row.mem_union key ambient supplied).mpr (Or.inr provided)
  · exact (Row.mem_union key ambient supplied).mpr
      (Or.inl (remaining key ((Row.mem_diff key required supplied).mpr ⟨needed, provided⟩)))

/-- More supplied keys answer a weaker promised context row.
Consumer: the proposed contextOf subtype direction. -/
theorem context_weaken (ctx : Env.Ctx) (promised available : Requirement)
    (subset : Row.Subset promised available) (present : ctx.Satisfies available) :
    ctx.Satisfies promised :=
  Context.satisfies_weaken ctx present subset

/-- Context-transformer metadata over the existing canonical row.
None inherits the invocation context; some replaces it inside an internal region. -/
abbrev Transformer := Option Requirement × Requirement

def apply (t : Transformer) (ambient : Requirement) : Requirement :=
  Row.union (t.1.getD ambient) t.2

def compose (outer inner : Transformer) : Transformer :=
  match inner.1 with
  | some _ => inner
  | none => (outer.1, Row.union outer.2 inner.2)

/-- Calls under inheritance charge only unsupplied keys; replacement must cover all requirements. -/
def parameterCall (t : Transformer) (required : Requirement) : Option Requirement :=
  match t.1 with
  | none => some (Row.diff required t.2)
  | some fixed => if Row.Subset required (Row.union fixed t.2) then some Row.empty else none

/-- The existing address census locates the removed raw source actions.
This is a migration profile probe, not a new admission implementation. -/
def sourceProfile (root : NativeEff) : Bool :=
  (Node.addresses (.eff root)).all (fun path =>
    (Node.at_ (.eff root) path).all (fun node => match node with
      | .action (.setContext _) | .action .getContext => false
      | _ => true))

private def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
private def other : ServiceKey := ⟨⟨5⟩, ⟨5⟩⟩
private def singleton : Requirement := Requirement.single key
private def needsKey : EffTy := ⟨.nat, .never, singleton⟩
private def empty : Requirement := Requirement.empty

-- The reader's selected row is both its answer promise and its execution requirement.
example : readerColumns singleton = (singleton, singleton) := rfl
-- Empty capture provides no evidence for the subsequently required key.
example : (provideColumns empty needsKey).requires = singleton := by
  exact Row.diff_empty singleton
example : (provideColumns singleton needsKey).requires = empty := by
  exact Row.diff_self singleton
example : parameterCall (none, singleton) singleton = some empty := by kernel_rfl
example : parameterCall (some empty, empty) singleton = none := by kernel_rfl
example : parameterCall (some singleton, empty) singleton = some empty := by kernel_rfl
example : apply (compose (none, singleton) (none, Requirement.single other)) empty =
    Requirement.ofList [key, other] := by kernel_rfl
example : apply (compose (none, singleton) (some empty, empty)) singleton = empty := by kernel_rfl

-- The retained CE001 inputs use the removed source actions, including inside a definition.
example : sourceProfile Test.Counterexamples.Program.ContextReset.reset = false := by kernel_rfl
example : sourceProfile Test.Counterexamples.Program.ContextReset.resetInBody = false := by kernel_rfl
private def serviceControl : NativeEff := .provideService key (.lit (.nat 1)) (.service key)
example : sourceProfile serviceControl = true := by kernel_rfl

-- The actual native producer already merges and installs the restoring callback.
private def previous : Machine.Ctx := Machine.Ctx.withServices (Env.Context.empty.addV key (.nat 1))
private def supplied : Env.Ctx := (Env.Context.empty.addV key (.nat 2)).addV other (.nat 3)
private def region : Region := .program (rootPoint 10)
example : ((Env.ContextUpdate.provide supplied).apply previous.services).getV key = some (.nat 2) := by kernel_rfl
example : ((Env.ContextUpdate.provide supplied).apply previous.services).getV other = some (.nat 3) := by kernel_rfl
example : updateThenK serviceControl (.provide supplied) region (Val.context previous) =
    .onSuccess (.withFiber (.setCtx (Machine.Ctx.withServices (previous.services.merge supplied))))
      (.bodyThen region previous) := by kernel_rfl
example : Effect4.Program.contAOf serviceControl (.bodyThen region previous) .unit =
    .onExit (regionCode serviceControl region) (.restoreCtx previous) false := rfl
example : (interpOf serviceControl []).finalizerProgram (.restoreCtx previous) (.success .unit) =
    some (.withFiber (.setCtx previous)) := rfl
end Test.MachineModels.ContextSignatures
#axiom_audit Effect4.Machine.Context Effect4.Program.Compile
