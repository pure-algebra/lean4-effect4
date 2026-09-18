import Effect4.Laws.Codegen.ReadPrint
import Effect4.Laws.Codegen.Module
import Effect4.Laws.Api.Codegen

/-!
# Laws.Codegen.ModuleReadable — the module round trip on the readable domain

`readModule_printModule` (`Laws/Codegen/Module.lean`) is the hoisting inverse composed with
"each piece reads back from its own printing", stated of any reader. Law 11 (`read_print`,
`Laws/Codegen/ReadPrint.lean`) says the table reader has that property on `Readable`. This
module composes the two: a program whose hoisted pieces are readable and whose reference names
decode reads back from the declaration block the module printer prints of it, through the
checked producer (`ModuleEmission`) and the application face (`Api.printModule`).

The domain here is per piece (`moduleReadable`): the main program at depth `0` and every
captured layer at depth `0`, each by the fold `readableAlg`, and each captured path by the name
codec, which has no law of its own and is run. Hoisting is a pass, not a fold, so "a readable
program has readable pieces" is not stated; the layer binder that replaces hoisting will make it
a fold and this a definition.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4.Codegen

variable {Op : Type}

/-- The pieces of a hoisted program are readable and their declared names decode. -/
def moduleReadable (sig : Signature Op) (root : Eff Op) : Bool :=
  match root.hoistAll with
  | .ok (main, history) =>
    Readable sig 0 main && history.all fun entry =>
      (cata_layer (readableAlg sig) entry.2 0).isSome &&
        decide (LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
  | .error _ => false

/-- What `moduleReadable` says of the pieces. -/
theorem moduleReadable_pieces {sig : Signature Op} {root : Eff Op}
    (hr : moduleReadable sig root = true) :
    ∃ main history, root.hoistAll = .ok (main, history) ∧ Readable sig 0 main = true ∧
      (∀ entry ∈ history, ReadableAt sig .layer entry.2 0) ∧
      (∀ entry ∈ history, LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1) := by
  unfold moduleReadable at hr
  split at hr
  · rename_i main history hh
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
    refine ⟨main, history, hh, hr.1, fun entry hm => ?_, fun entry hm => (hr.2 entry hm).2⟩
    have := (hr.2 entry hm).1
    unfold ReadableAt
    simpa only [cataFam, Option.isSome_iff_exists] using this
  · cases hr

/-- **The module inverse on the readable domain.** The declaration block the module printer
prints of a program whose pieces are readable reads back to the program. -/
theorem readModule_printModule_readable {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell) {root : Eff Op}
    (hr : moduleReadable sig root = true) {name : String} {ty : EffTy}
    {decls : List TypeScript.ConstDecl} (printed : printModule sig name ty root = .ok decls) :
    readModule sig spell (decls.map TypeScript.Decl.const) = .ok root := by
  obtain ⟨main, history, hoisted, hmain, hlayers, hnames⟩ := moduleReadable_pieces hr
  exact readModule_printModule hoisted (ReadsBack.of_Readable hl hmain)
    (fun entry hm x hp => readLayer_print hl (hlayers entry hm) hp) hnames printed

end Effect4.Program

namespace Effect4.Codegen

open Effect4.Program

/-- Reading the emitted declaration block recovers its program, when the program's pieces are
readable under the native table. -/
theorem ModuleEmission.readModule {program : NativeEff} {table : RowTable} {name : String}
    (emission : ModuleEmission program table name) (lawful : LawfulTable table = true)
    (readable : moduleReadable (nativeSignature table) program = true) :
    Program.readModule (nativeSignature table) (nativeSpell table) emission.module.decls =
      .ok program := by
  obtain ⟨_, _, printed⟩ := Program.printEntry_ok emission.generated
  exact readModule_printModule_readable (nativeLawful table lawful) readable printed

end Effect4.Codegen

namespace Effect4.Api

open Effect4.Program

/-- Through the application face: a program whose pieces are readable under a lawful table has
a module whose reading is the program. -/
theorem printModule_roundTrip {name : String} {program : Program} {table : RowTable}
    (lawful : LawfulTable table = true)
    (readable : moduleReadable (nativeSignature table) program = true)
    {module : TypeScript.Module} (printed : printModule name program table = some module) :
    readModule module table = .ok program := by
  unfold printModule at printed
  obtain ⟨emission, hemit, hmod⟩ := Option.map_eq_some_iff.mp printed
  subst hmod
  exact emission.readModule lawful readable

end Effect4.Api
