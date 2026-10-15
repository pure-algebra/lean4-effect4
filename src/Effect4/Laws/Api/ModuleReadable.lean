import Effect4.Laws.Codegen.ReadPrint
import Effect4.Laws.Codegen.PrintReadable
import Effect4.Laws.Codegen.PrintTyped
import Effect4.Laws.Codegen.Module
import Effect4.Laws.Codegen.Definitions
import Effect4.Laws.Api.Codegen

/-!
# Laws.Codegen.ModuleReadable — the module round trip on the readable domain

`readModuleWith_printModuleWith` (`Laws/Codegen/Module.lean`) is the hoisting inverse composed
with "each piece reads back from its own printing", stated of any pair of a piece printer and a
piece reader. A pair is lawful when every piece readable at its environment reads back by it
(`PiecesLawful`). The pieces that ship and the typed reader are one (`shippedPieces_lawful`):
the typed print reads back by `readTyped_printTyped` (`Laws/Codegen/PrintTyped.lean`), and the
fold's print, where the typed print refuses, by law 11 at the empty annotation. This module
composes the two: a program whose hoisted pieces are readable and whose reference names decode
reads back from the declaration block the module printer prints of it, at any lawful pair. The
checked producer (`ModuleEmission`) prints its pieces as the module that ships prints them, so
its module reads back by the typed reader, and so does the application face's
(`Api.printModule`, `Api.readModule`).

The domain here is per piece (`moduleReadable`): the main program at depth `0` and every
captured layer at depth `0`, each by the fold `readableAlg`, and each captured path by the name
codec, which has no law of its own and is run. Hoisting is a pass, not a fold, so "a readable
program has readable pieces" is not stated; the layer binder that replaces hoisting will make it
a fold and this a definition.
-/

set_option autoImplicit false

open Effect4.Laws.Auto (bind_eq_ok)

namespace Effect4.Program

open Effect4.Codegen

variable {Op : Type}

open Effect4.Codegen.Classes (Classes)

variable {classes : Classes}

/-- The pieces of a hoisted program with no definition block are readable under the module's
payload classes (decisions row 120, part E2) and their declared names decode. A program with a
block has its own domain (`blockReadable`). -/
def moduleReadable (classes : Classes) (sig : Signature Op) (root : Eff Op) : Bool :=
  match root.hoistAll with
  | .ok (main, history) =>
    main.block?.isNone && Readable classes sig 0 main && history.all fun entry =>
      (cata_layer (readableAlg classes sig) entry.2 0).isSome &&
        decide (LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
  | .error _ => false

/-- What `moduleReadable` says of the pieces. -/
theorem moduleReadable_pieces {sig : Signature Op} {root : Eff Op}
    (hr : moduleReadable classes sig root = true) :
    ∃ main history, root.hoistAll = .ok (main, history) ∧ main.block? = none ∧
      Readable classes sig 0 main = true ∧
      (∀ entry ∈ history, ReadableAt classes sig .layer entry.2 0) ∧
      (∀ entry ∈ history, LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1) := by
  unfold moduleReadable at hr
  split at hr
  · rename_i main history hh
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at hr
    refine ⟨main, history, hh, hr.1.1, hr.1.2, fun entry hm => ?_, fun entry hm => (hr.2 entry hm).2⟩
    have := (hr.2 entry hm).1
    unfold ReadableAt
    simpa only [cataFam, Option.isSome_iff_exists] using this
  · cases hr

/-- **A lawful pair of a piece printer and a piece reader**: at a lawful spelling, every piece
readable at its environment's length reads back by the pair (`ReadsBackBy`). The module round
trips of the readable domain are stated of any lawful pair. -/
def PiecesLawful (pp : PiecePrint Op) (rd : PieceRead Op) (classes : Classes) : Prop :=
  ∀ {sig : Signature Op} {spell : String → List RowArg → Option Op} {env : TyEnv} {e : Eff Op},
    LawfulSpelling sig spell → Readable classes sig env.length e = true →
      ReadsBackBy pp rd classes sig spell env e

/-- **The pieces that ship and the typed reader are a lawful pair**: the typed reader reads every
successful typed print back after the named erasure (`readTyped_printTyped`, the claim
`typed-print-read`), and the fold's print as the typed print at the empty annotation
(`readTyped_printTypedAt`, `printTypedAt_none`), where the typed print refuses. The module that
ships prints its pieces so, and the reading boundary reads them so (`ModuleEmission.readDecls`). -/
theorem shippedPieces_lawful : PiecesLawful (Op := Op) shippedPieces Codegen.readTyped classes := by
  intro sig spell env e hl hr x printed
  cases typed : printTyped sig env e with
  | ok y =>
    simp only [shippedPieces, typed, Except.ok.injEq] at printed
    subst printed
    exact Codegen.readTyped_printTyped hl hr typed
  | error _ =>
    simp only [shippedPieces, typed] at printed
    exact Codegen.readTyped_printTypedAt (ann := fun _ => none) hl hr
      ((Effect4.Codegen.Templates.printTypedAt_none sig env.length e).trans printed)

/-- **The module inverse on the readable domain**, at any lawful pair. The declaration block the
module printer prints of a program whose pieces are readable under the module's classes, after
class declarations that read back to those classes and the services of the rows that the module
declares (`rowServiceDecls`), reads back to the program. -/
theorem readModuleWith_printModuleWith_readable {pp : PiecePrint Op} {rd : PieceRead Op}
    (pieces : PiecesLawful pp rd classes) {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {call param : Nat → Op}
    (hl : LawfulSpelling sig spell)
    {root : Eff Op}
    (hr : moduleReadable classes sig root = true) {classDecls : List TypeScript.ClassDecl}
    (classesRead : Effect4.Codegen.Classes.readClassDecls classDecls = some classes)
    {rows : List Row} {serviceDecls : List TypeScript.ConstDecl}
    (servicesPrinted : rowServiceDecls sig rows = .ok serviceDecls)
    {name : String} {ty : EffTy}
    {decls : List TypeScript.ConstDecl} (printed : printModuleWith pp sig name ty root = .ok decls) :
    readModuleWith rd sig spell call param rows
      (classDecls.map TypeScript.Decl.classDecl ++ serviceDecls.map TypeScript.Decl.const ++
        decls.map TypeScript.Decl.const) = .ok root := by
  obtain ⟨main, history, hoisted, plain, hmain, hlayers, hnames⟩ := moduleReadable_pieces hr
  exact readModuleWith_printModuleWith hoisted plain classesRead servicesPrinted
    (pieces (env := []) hl hmain) (fun entry hm x hp => readLayer_print hl (hlayers entry hm) hp)
    hnames printed

/-! ## A program whose pieces are readable prints as a declaration block -/

/-- A path is its own key. (`simp` proves this through the lawful-`BEq` instance of lists,
which brings `Classical.choice`; this proof does not.) -/
theorem path_beq_self : ∀ (t : List Nat), (t == t) = true
  | [] => rfl
  | a :: as => by
    have ih := path_beq_self as
    show (a == a && (as == as)) = true
    rw [ih, Bool.and_true]
    exact beq_iff_eq.mpr rfl

/-- One captured layer as its declaration: what `printModule` maps over the targets. -/
def capturedDecl (sig : Signature Op) (history : List (List Nat × LayerTerm Op)) (t : List Nat) :
    Except PrintRefusal TypeScript.ConstDecl :=
  match history.find? (·.1 == t) with
  | some (_, l) => do
    let x ← printLayer sig l
    .ok ({ doc := [], name := LayerTerm.refName t, value := x } : TypeScript.ConstDecl)
  | none => .error (.layerRef t)

/-- Each captured layer named in a target list prints as a declaration. -/
theorem captured_mapM_ok {sig : Signature Op} {history : List (List Nat × LayerTerm Op)}
    (hlayers : ∀ entry ∈ history, ReadableAt classes sig .layer entry.2 0) :
    ∀ (targets : List (List Nat)), (∀ t ∈ targets, t ∈ history.map (·.1)) →
    ∃ ds, targets.mapM (capturedDecl sig history) = .ok ds
  | [], _ => ⟨[], rfl⟩
  | t :: rest, hin => by
    obtain ⟨ds, hds⟩ := captured_mapM_ok hlayers rest (fun t' h => hin t' (List.mem_cons_of_mem _ h))
    have hmem := hin t List.mem_cons_self
    obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hmem
    obtain ⟨found, hfound⟩ : ∃ found, history.find? (·.1 == t) = some found := by
      apply Option.isSome_iff_exists.mp
      rw [List.find?_isSome]
      exact ⟨entry, hentry, by rw [hkey]; exact path_beq_self t⟩
    have hfmem := List.mem_of_find?_eq_some hfound
    obtain ⟨x, hx⟩ := printLayer_of_readable (hlayers found hfmem)
    obtain ⟨target, layer⟩ := found
    refine ⟨{ doc := [], name := LayerTerm.refName t, value := x } :: ds, ?_⟩
    simp only [List.mapM_cons, capturedDecl, hfound, hx, ok_bind, hds]
    rfl

/-- **A program whose pieces are readable prints as a declaration block**, at every export
name and every representable declaration type, by any piece printer that prints whatever the
table's fold prints (`prints`): the plain pieces, and the pieces that ship
(`shippedPieces_prints`). -/
theorem printModuleWith_readable {pp : PiecePrint Op}
    (prints : ∀ (sig : Signature Op) env e x, print sig env.length e = .ok x →
      ∃ y, pp sig env e = .ok y)
    {sig : Signature Op} {root : Eff Op}
    (hr : moduleReadable classes sig root = true) (name : String) (ty : EffTy)
    (types : declarationTypeRepresentable ty = true) :
    ∃ decls, printModuleWith pp sig name ty root = .ok decls := by
  obtain ⟨main, history, hoisted, plain, hmain, hlayers, _⟩ := moduleReadable_pieces hr
  obtain ⟨x, hx⟩ := print_of_readable hmain
  obtain ⟨body, hbody⟩ := prints sig [] main x hx
  obtain ⟨ds, hds⟩ := captured_mapM_ok hlayers (Path.sortBy Path.declBefore (history.map (·.1)))
    (fun t ht => (Path.sortBy_perm Path.declBefore _).mem_iff.mp ht)
  obtain ⟨decl, hdecl⟩ := printDecl_readable name ty body types sig.typeEnv
  refine ⟨ds ++ [decl], ?_⟩
  unfold printModuleWith
  rw [hoisted]
  simp only [plain]
  change ((Path.sortBy Path.declBefore (history.map (·.1))).mapM (capturedDecl sig history) >>=
    fun ds => pp sig [] main >>= fun body =>
    printDecl name ty body sig.typeEnv >>= fun decl => .ok (ds ++ [decl])) = _
  simp only [hds, ok_bind, hbody, hdecl]

/-- The pieces that ship print whatever the table's fold prints: the typed print where it
succeeds, and the fold's print where it refuses. A step of `emitModule_complete`. -/
theorem shippedPieces_prints (sig : Signature Op) (env : TyEnv) (e : Eff Op) (x : TypeScript.Expr)
    (printed : print sig env.length e = .ok x) : ∃ y, shippedPieces sig env e = .ok y := by
  cases typed : printTyped sig env e with
  | ok y => exact ⟨y, by simp only [shippedPieces, typed]⟩
  | error _ => exact ⟨x, by simp only [shippedPieces, typed, printed]⟩

/-! ## A program with a definition block (decisions row 328, slice PROC-3) -/

/-- The signature a hoisted layer of a block prints and reads at (decisions row 341, step 3): a
body's own layer at the signature the body's parameters extend, any other at the block's. -/
def layerSigOf (sig : Signature Op) (defs : List DefDecl) (t : List Nat) : Signature Op :=
  match bodyDeclOf defs t with
  | some d => (sig.withDefs defs).withParams d.params
  | none => sig.withDefs defs

/-- The pieces of a hoisted program with a definition block are readable at the block's
signature: each declaration under `sig.typeEnv classes` (`DefDecl.readable`: a column that names a
class reads as the class's record, a named key reads by its name, and the requirement row reads
back), each body at
environment length `1` at the signature its parameters extend (slice HO-3), the main program,
each module layer (decisions row 341, step 2) and each hoisted layer, a body's own at its body's
signature (step 3, `layerSigOf`), and the layers' declared names decode. -/
def blockReadable (classes : Classes) (sig : Signature Op) (root : Eff Op) : Bool :=
  match root.hoistAll with
  | .ok (main, history) =>
    match main.block? with
    | some (defs, bodies, body, layers) =>
      defs.all (DefDecl.readable (sig.typeEnv classes)) &&
        (defs.zip bodies.toList).all (fun p =>
          Readable classes ((sig.withDefs defs).withParams p.1.params) 1 p.2) &&
        Readable classes (sig.withDefs defs) 0 body &&
        layers.toList.all (fun l => (cata_layer (readableAlg classes (sig.withDefs defs)) l 0).isSome) &&
        (List.range layers.toList.length).all (fun k =>
          decide (LayerTerm.readRefName (LayerTerm.refName (Path.layerPath k)) =
            some (Path.layerPath k))) &&
        history.all fun entry =>
          (cata_layer (readableAlg classes (layerSigOf sig defs entry.1)) entry.2 0).isSome &&
            decide (LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    | _ => false
  | .error _ => false

/-- What `blockReadable` says of the pieces. -/
theorem blockReadable_pieces {sig : Signature Op} {root : Eff Op}
    (hr : blockReadable classes sig root = true) :
    ∃ main history defs bodies body layers, root.hoistAll = .ok (main, history) ∧
      main.block? = some (defs, bodies, body, layers) ∧
      (∀ d ∈ defs, d.readable (sig.typeEnv classes) = true) ∧
      (∀ p ∈ defs.zip bodies.toList,
        Readable classes ((sig.withDefs defs).withParams p.1.params) 1 p.2 = true) ∧
      Readable classes (sig.withDefs defs) 0 body = true ∧
      (∀ l ∈ layers.toList, ReadableAt classes (sig.withDefs defs) .layer l 0) ∧
      (∀ k < layers.toList.length,
        LayerTerm.readRefName (LayerTerm.refName (Path.layerPath k)) = some (Path.layerPath k)) ∧
      (∀ entry ∈ history,
        ReadableAt classes (layerSigOf sig defs entry.1) .layer entry.2 0) ∧
      (∀ entry ∈ history, LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1) := by
  unfold blockReadable at hr
  split at hr
  · rename_i main history hh
    split at hr
    · rename_i defs bodies body layers hb
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at hr
      obtain ⟨⟨⟨⟨⟨heads, hbodies⟩, hmain⟩, hmods⟩, hnames⟩, hlayers⟩ := hr
      refine ⟨main, history, defs, bodies, body, layers, hh, hb, heads, hbodies, hmain,
        fun l hm => ?_, hnames, fun entry hm => ?_, fun entry hm => (hlayers entry hm).2⟩
      · have := hmods l hm
        unfold ReadableAt
        simpa only [cataFam, Option.isSome_iff_exists] using this
      · have := (hlayers entry hm).1
        unfold ReadableAt
        simpa only [cataFam, Option.isSome_iff_exists] using this
    · cases hr
  · cases hr

/-- **The module inverse on the readable domain of a definition block**, at any lawful pair. The
declaration block the module printer prints of a program with a block whose pieces are readable
reads back to the program, at a lawful spelling whose invocations and parameter runs are lawful
(`LawfulCalls`, `LawfulParams`, apart from each other) and whose block and parameter names are
readable (`DefsNamed`, `ParamsNamed`). The reader's laws hold at the block's signature
(`LawfulSpelling.withDefs`) and at each body's (`LawfulSpelling.withParams`, slice HO-3), where a
body and its own layers are read (decisions row 341, step 3), and the module law with a block
composes them (`readModuleWith_printModuleWith_defs`). A step of the claim
`module-defs-round-trip`; its consumer is `ModuleEmission.readModule`, at the typed pair. -/
theorem readModuleWith_printModuleWith_defs_readable {pp : PiecePrint Op} {rd : PieceRead Op}
    (pieces : PiecesLawful pp rd classes) {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {call param : Nat → Op}
    (hl : LawfulSpelling sig spell) (calls : LawfulCalls sig spell call)
    (params : LawfulParams sig spell param)
    (apart : ∀ op i, sig.paramOf op = some i → sig.callOf op = none) {root : Eff Op}
    (hr : blockReadable classes sig root = true) (named : DefsNamed spell root.defsOf)
    (paramsNamed : ∀ d ∈ root.defsOf,
      ParamsNamed (defsSpell call root.defsOf spell) d.params)
    {classDecls : List TypeScript.ClassDecl}
    (classesRead : Effect4.Codegen.Classes.readClassDecls classDecls = some classes)
    {rows : List Row} {serviceDecls : List TypeScript.ConstDecl}
    (servicesPrinted : rowServiceDecls sig rows = .ok serviceDecls)
    {name : String} {ty : EffTy}
    {decls : List TypeScript.ConstDecl} (printed : printModuleWith pp sig name ty root = .ok decls) :
    readModuleWith rd sig spell call param rows
      (classDecls.map TypeScript.Decl.classDecl ++ serviceDecls.map TypeScript.Decl.const ++
        decls.map TypeScript.Decl.const) = .ok root := by
  obtain ⟨main, history, defs, bodies, body, layers, hoisted, block, heads, hbodies, hmain, hmods,
    hmodNames, hlayers, hnames⟩ := blockReadable_pieces hr
  have same : root.defsOf = defs :=
    (Eff.hoistAll_defsOf hoisted).symm.trans (Eff.defsOf_of_block? block)
  rw [same] at named paramsNamed
  have hl' := hl.withDefs calls named
  have params' := params.withDefs calls apart defs
  refine readModuleWith_printModuleWith_defs hoisted block classesRead servicesPrinted heads
    (fun p mem => pieces (env := [p.1.request.normalize])
      (hl'.withParams params' apart (paramsNamed p.1 (List.of_mem_zip mem).1)) (hbodies p mem))
    (pieces (env := []) hl' hmain)
    (fun l hm x hp => readLayer_print hl' (hmods l hm) hp) hmodNames
    (fun entry hm d hd x hp => ?_) (fun entry hm hd x hp => ?_) hnames printed
  · -- a body's own layer, read at the signature its parameters extend
    have hread := hlayers entry hm
    simp only [layerSigOf, hd] at hread
    exact readLayer_print (hl'.withParams params' apart (paramsNamed d (bodyDeclOf_mem hd)))
      hread hp
  · -- any other hoisted layer, read at the block's signature
    have hread := hlayers entry hm
    simp only [layerSigOf, hd] at hread
    exact readLayer_print hl' hread hp

end Effect4.Program

namespace Effect4.Codegen

open Effect4.Program

/-- Reading the emitted declarations recovers their program, after the payload classes and the
services of the rows that the module declares (`rowServiceDecls`), when the program's pieces are
readable under the native table: a program with no definition block (`moduleReadable`), or one
with a block (`blockReadable`), whose names and parameter names the printer's own checks made
readable (`defsNamed_of_fault`, `blockParamsNamed`). The emission prints its pieces typed, so the
typed reader reads them (`shippedPieces_lawful`). The envelope (`ModuleEmission.readModule`) and
the file (`ModuleEmission.readFile`) are its two instances. -/
theorem ModuleEmission.readDecls {program : NativeEff} {table : RowTable} {name : String}
    (emission : ModuleEmission program table name) (lawful : LawfulTable table = true)
    (readable : moduleReadable emission.classes (nativeSignature table) program = true ∨
      blockReadable emission.classes (nativeSignature table) program = true)
    {rows : List Program.Row} {serviceDecls : List TypeScript.ConstDecl}
    (servicesPrinted : rowServiceDecls (nativeSignature table) rows = .ok serviceDecls) :
    Program.readModuleTyped (nativeSignature table) (nativeSpell table) NativeOp.call
      NativeOp.param rows (emission.classDecls.map TypeScript.Decl.classDecl ++
        serviceDecls.map TypeScript.Decl.const ++ emission.declarations.map TypeScript.Decl.const) =
      .ok program := by
  obtain ⟨_, _, names, paramNames, _, _, _, printed⟩ :=
    Program.printEntry_checks emission.generated
  have classesRead := Classes.readClassDecls_checked (moduleClasses_checked emission.classified)
  rcases readable with plain | block
  · exact readModuleWith_printModuleWith_readable shippedPieces_lawful (nativeLawful table lawful)
      plain classesRead servicesPrinted printed
  · exact readModuleWith_printModuleWith_defs_readable shippedPieces_lawful
      (nativeLawful table lawful) (nativeCalls table) (nativeParams table) (nativeApart table)
      block (defsNamed_of_fault names) (blockParamsNamed paramNames) classesRead servicesPrinted
      printed

/-- **The envelope reads back**: the declaration block that a host wraps
(`ModuleEmission.module`) declares no service, and reads back at no row's services. -/
theorem ModuleEmission.readModule {program : NativeEff} {table : RowTable} {name : String}
    (emission : ModuleEmission program table name) (lawful : LawfulTable table = true)
    (readable : moduleReadable emission.classes (nativeSignature table) program = true ∨
      blockReadable emission.classes (nativeSignature table) program = true) :
    Program.readModuleTyped (nativeSignature table) (nativeSpell table) NativeOp.call
      NativeOp.param [] emission.module.decls = .ok program := by
  have h := emission.readDecls lawful readable (rowServiceDecls_nil (nativeSignature table))
  simp only [List.map_nil, List.append_nil] at h
  exact h

/-- **The file reads back** (decisions row 378 (19), (20)): the module as a file
(`ModuleEmission.file`) holds the payload classes, the services of the table's rows and the
envelope's declarations, and the file reader reads it back to the program at the table's rows.
Placement: concept `exact-codecs`, the claim `module-defs-round-trip` (R8) at the module's file,
its consumer the file reader `Api.readFile`. It does not say that tsgo accepts the file or that
rc.112 provides its services. -/
theorem ModuleEmission.readFile {program : NativeEff} {table : RowTable} {name : String}
    (emission : ModuleEmission program table name) (lawful : LawfulTable table = true)
    (readable : moduleReadable emission.classes (nativeSignature table) program = true ∨
      blockReadable emission.classes (nativeSignature table) program = true)
    {prelude : String} {except : List String} {file : TypeScript.Module}
    (filed : emission.file prelude except = .ok file) :
    Program.readModuleTyped (nativeSignature table) (nativeSpell table) NativeOp.call
      NativeOp.param table file.decls = .ok program := by
  unfold ModuleEmission.file at filed
  obtain ⟨serviceDecls, servicesPrinted, hfile⟩ := bind_eq_ok.mp filed
  cases hfile
  exact emission.readDecls lawful readable servicesPrinted

/-- Every row of a lawful table has safe names. -/
theorem lawful_rowNamesSafe {table : RowTable} (lawful : LawfulTable table = true) :
    table.find? (fun row => !rowNamesSafe row) = none := by
  apply List.find?_eq_none.mpr
  intro row mem
  simp only [(lawfulTable_member table lawful row mem).2.2, Bool.not_true, Bool.false_eq_true,
    not_false_eq_true]

/-- **Every checked program whose pieces are readable emits**, at a safe export name and a
representable declaration type and stored annotations. The emission prints its pieces as the
module that ships prints them (`shippedPieces`), which prints whatever the table's fold prints
(`shippedPieces_prints`). -/
theorem emitModule_complete {program : NativeEff} {table : RowTable} {name : String}
    (formed : Formation.InputFormed program table)
    (typing : TypedProgram (nativeSignature table) program)
    (safe : exportNameSafe name = true) (lawful : LawfulTable table = true)
    {classes : Classes.Classes} {classDecls : List TypeScript.ClassDecl}
    (classified : ClassTable.moduleClasses (nativeSignature table) name typing.ty program =
      .ok (classes, classDecls))
    (readable : moduleReadable classes (nativeSignature table) program = true)
    (types : declarationTypeRepresentable typing.ty = true)
    (annotations : annotationRefusal program = none)
    (inProfile : natLiteralsInProfile program = true) :
    ∃ emission, emitModule name program table = .ok emission := by
  obtain ⟨decls, printed⟩ :=
    printModuleWith_readable shippedPieces_prints readable name typing.ty types
  obtain ⟨_, _, hoisted, plain, _, _, _⟩ := moduleReadable_pieces readable
  have noDefs : program.defsOf = [] :=
    (Eff.hoistAll_defsOf hoisted).symm.trans (Eff.defsOf_of_block?_none plain)
  have generated : printEntryWith shippedPieces table (nativeSignature table) name typing.ty
      program = .ok decls := by
    simp only [printEntryWith, safe, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      lawful_rowNamesSafe lawful, noDefs, defsNameFault, blockParamsFault, classNameFault,
      List.findSome?_nil, serviceNamesFault_nil, classified,
      annotations, printed]
  exact ⟨⟨formed, typing, inProfile, classes, classDecls, classified, decls, generated⟩,
    ModuleEmission.recheck _⟩

end Effect4.Codegen

namespace Effect4.Api

open Effect4.Program

/-- Through the application face: a program whose pieces are readable under a lawful table has
a module whose reading is the program, with or without a definition block. The module is the
one that ships, its pieces printed typed, and the face's reader reads it after the named
erasure (`ModuleEmission.readModule`). -/
theorem printModule_roundTrip {name : String} {program : Program} {table : RowTable}
    (lawful : LawfulTable table = true)
    (readable : ∀ e : Effect4.Codegen.ModuleEmission program table name,
      moduleReadable e.classes (nativeSignature table) program = true ∨
        blockReadable e.classes (nativeSignature table) program = true)
    {module : TypeScript.Module} (printed : printModule name program table = some module) :
    readModule module table = .ok program := by
  unfold printModule at printed
  obtain ⟨emission, hemit, hmod⟩ := Option.map_eq_some_iff.mp printed
  subst hmod
  exact emission.readModule lawful (readable emission)

end Effect4.Api
