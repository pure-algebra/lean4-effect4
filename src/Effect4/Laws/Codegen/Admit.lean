import Effect4.Codegen.Admit
import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Codegen.Checked
import Effect4.Laws.Codegen.SourceBindings

/-!
# The reading certificate against its own checks

`envelopeCheck` is a computed answer; `EnvelopeValid` is the same five facts as a Prop, and
`envelopeCheck_iff` relates them, so a consumer reasons about the declaration block and not
about the order of a `match`. The certificate is then the pullback of the raw reader's
graph and the checker's graph along that envelope: `ModuleReading.recheck` says the
boundary returns what it holds, `ModuleReading.unique` that a module has one reading, and
`ModuleEmission.admit` that what the producer emitted is admitted, to the same program and
the same typing certificate.

No theorem here widens a declared type, admits a binder annotation, interprets the `effect`
package, or claims target typing or execution.
-/

namespace Effect4.Codegen

open Effect4.Program

variable {table : RowTable} {name : String} {allowed : List Bindings.Origin}
  {ambient : List TypeScript.Import}

/-! ## The envelope as a Prop -/

/-- The five facts the envelope decides, stated on the declaration block: the leading class
declarations read back to the printer's classes (decisions row 120), then the four of the
declaration block after them. -/
structure EnvelopeValid (name : String) (ty : EffTy) (classes : Classes.Classes)
    (decls : List TypeScript.Decl) : Prop where
  safe : exportNameSafe name = true
  declared : Program.blockClasses decls = some classes
  main : ∃ main : TypeScript.ConstDecl,
    (Program.splitClasses decls).2.getLast? = some (.const main) ∧
    main.name = name ∧ main.exported = true ∧ declarationType ty = .ok main.type
  layers : ∀ d ∈ (Program.splitClasses decls).2.dropLast, ∃ c : TypeScript.ConstDecl,
    d = .const c ∧ c.type = none ∧ c.exported = true

theorem mainConst_eq_some {decls : List TypeScript.Decl} {main : TypeScript.ConstDecl} :
    mainConst decls = some main ↔ decls.getLast? = some (.const main) := by
  unfold mainConst
  split <;> simp_all

/-- The plainness check is exactly the plainness of every declaration it walks. -/
theorem layersPlain_iff (ds : List TypeScript.Decl) :
    layersPlain ds = none ↔ ∀ d ∈ ds, ∃ c : TypeScript.ConstDecl,
      d = .const c ∧ c.type = none ∧ c.exported = true := by
  induction ds with
  | nil => simp [layersPlain]
  | cons d rest ih =>
    cases d with
    | const c =>
      simp only [layersPlain, List.mem_cons, forall_eq_or_imp]
      split
      · rename_i plain
        rw [ih]
        constructor
        · intro tail
          exact ⟨⟨c, rfl, plain.1, plain.2⟩, tail⟩
        · intro both
          exact both.2
      · rename_i notPlain
        constructor
        · intro refused
          cases refused
        · rintro ⟨⟨c', heq, hty, hex⟩, -⟩
          cases heq
          exact absurd ⟨hty, hex⟩ notPlain
    | prog p =>
      simp only [layersPlain, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro refused
        cases refused
      · rintro ⟨⟨c, heq, -, -⟩, -⟩
        cases heq
    | effectfulField f =>
      simp only [layersPlain, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro refused
        cases refused
      · rintro ⟨⟨c, heq, -, -⟩, -⟩
        cases heq
    | classDecl k =>
      simp only [layersPlain, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro refused
        cases refused
      · rintro ⟨⟨c, heq, -, -⟩, -⟩
        cases heq
    | raw t =>
      simp only [layersPlain, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro refused
        cases refused
      · rintro ⟨⟨c, heq, -, -⟩, -⟩
        cases heq

/-- The computed envelope admits exactly the stated declaration-block judgment. -/
theorem envelopeCheck_iff (name : String) (ty : EffTy) (classes : Classes.Classes)
    (decls : List TypeScript.Decl) :
    envelopeCheck name ty classes decls = none ↔ EnvelopeValid name ty classes decls := by
  unfold envelopeCheck
  split
  · rename_i unsafe?
    constructor
    · intro refused
      cases refused
    · intro valid
      exact absurd valid.safe unsafe?
  · rename_i notUnsafe
    have safe : exportNameSafe name = true := by simpa using notUnsafe
    split
    · rename_i why hdt
      constructor
      · intro refused
        cases refused
      · intro valid
        obtain ⟨main, _, _, _, htype⟩ := valid.main
        simp [hdt] at htype
    · rename_i expected hdt
      split
      · rename_i wrongClasses
        constructor
        · intro refused
          cases refused
        · intro valid
          exact absurd valid.declared wrongClasses
      · rename_i rightClasses
        have declared : Program.blockClasses decls = some classes := by
          simpa only [ne_eq, Decidable.not_not] using rightClasses
        split
        · rename_i hmain
          constructor
          · intro refused
            cases refused
          · intro valid
            obtain ⟨main, hlast, _, _, _⟩ := valid.main
            rw [mainConst_eq_some.mpr hlast] at hmain
            cases hmain
        · rename_i main hmain
          have hlast : (Program.splitClasses decls).2.getLast? = some (.const main) :=
            mainConst_eq_some.mp hmain
          have uniqueMain : ∀ m : TypeScript.ConstDecl,
              (Program.splitClasses decls).2.getLast? = some (.const m) → m = main := by
            intro m hm
            simpa using hm.symm.trans hlast
          split
          · rename_i wrongName
            constructor
            · intro refused
              cases refused
            · intro valid
              obtain ⟨m, hm, hname, _, _⟩ := valid.main
              cases uniqueMain m hm
              exact absurd hname wrongName
          · rename_i rightName
            have hname : main.name = name := by simpa using rightName
            split
            · rename_i notExported
              constructor
              · intro refused
                cases refused
              · intro valid
                obtain ⟨m, hm, _, hexported, _⟩ := valid.main
                cases uniqueMain m hm
                exact absurd hexported notExported
            · rename_i isExported
              have hexported : main.exported = true := by simpa using isExported
              split
              · rename_i wrongType
                constructor
                · intro refused
                  cases refused
                · intro valid
                  obtain ⟨m, hm, _, _, htype⟩ := valid.main
                  cases uniqueMain m hm
                  rw [hdt] at htype
                  exact absurd (Except.ok.inj htype).symm wrongType
              · rename_i rightType
                have htype : main.type = expected := by simpa using rightType
                rw [layersPlain_iff]
                constructor
                · intro layers
                  exact ⟨safe, declared, ⟨main, hlast, hname, hexported, by rw [hdt, htype]⟩,
                    layers⟩
                · intro valid
                  exact valid.layers

/-! ## The class section -/

/-- A module's classes are the classes its checked declarations read back to: the class table's
declarations are `checkedDecl`'s (decisions row 120). Step of `ModuleEmission.admit` and of the
emitted module's reading (R8). -/
theorem moduleClasses_checked {Op : Type} [ScopedOp Op] {sig : Signature Op} {name : String}
    {ty : EffTy}
    {program : Eff Op} {classes : Classes.Classes} {classDecls : List TypeScript.ClassDecl}
    (h : ClassTable.moduleClasses sig name ty program = .ok (classes, classDecls)) :
    classes.mapM ClassTable.checkedDecl = .ok classDecls := by
  unfold ClassTable.moduleClasses at h
  obtain ⟨_, _, h⟩ := bind_eq_ok.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok.mp h
  obtain ⟨table, _, h⟩ := bind_eq_ok.mp h
  dsimp only at h
  split at h
  · exact nomatch h
  · obtain ⟨decls, hdecls, h⟩ := bind_eq_ok.mp h
    cases h
    exact hdecls

/-! ## The certificate -/

/-- A completed reading is exactly what the computed boundary returns for its module. -/
theorem ModuleReading.recheck (r : ModuleReading table name allowed ambient) :
    admitModule name r.module table allowed ambient = .ok r := by
  obtain ⟨module, program, formed, typing, classes, classDecls, classified, annotations, bound,
    read, env⟩ := r
  unfold admitModule
  split
  · rename_i refused
    rw [bound.recheck] at refused
    cases refused
  · rename_i bound' _
    split
    · rename_i why refused
      rw [read] at refused
      cases refused
    · rename_i program' hread
      have same : program' = program := Except.ok.inj (hread.symm.trans read)
      subst same
      have hformed := (Formation.checkInput_eq_none_iff program' table).mpr formed
      split
      · rename_i why refused
        rw [hformed] at refused
        cases refused
      · split
        · rename_i refused
          rw [checkTypedProgram_eq_some typing] at refused
          cases refused
        · rename_i typing' htyping
          have sameTyping : typing' = typing :=
            Option.some.inj (htyping.symm.trans (checkTypedProgram_eq_some typing))
          subst sameTyping
          split
          · rename_i why refused
            rw [classified] at refused
            cases refused
          · rename_i classes' classDecls' hclasses
            have sameClasses := Except.ok.inj (hclasses.symm.trans classified)
            simp only [Prod.mk.injEq] at sameClasses
            obtain ⟨rfl, rfl⟩ := sameClasses
            split
            · rename_i why refused
              rw [annotations] at refused
              cases refused
            · split
              · rename_i why refused
                rw [env] at refused
                cases refused
              · cases bound'
                cases bound
                rfl

/-- The certificate is indexed by the module it was computed from. -/
theorem admitModule_module {module : TypeScript.Module}
    {r : ModuleReading table name allowed ambient}
    (h : admitModule name module table allowed ambient = .ok r) : r.module = module := by
  unfold admitModule at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · cases h
                rfl

/-- O3: typed reading is a projection of the certificate, at the one core checker. -/
theorem admitModule_typed {module : TypeScript.Module}
    {r : ModuleReading table name allowed ambient}
    (_ : admitModule name module table allowed ambient = .ok r) :
    typeOfProgram (nativeSignature table) r.program = some r.typing.ty :=
  r.typing.typed

/-- The raw reader is the projection of the checked boundary. -/
theorem admitModule_read {module : TypeScript.Module}
    {r : ModuleReading table name allowed ambient}
    (h : admitModule name module table allowed ambient = .ok r) :
    Program.readModule (nativeSignature table) (nativeSpell table) module.decls = .ok r.program := by
  rw [← admitModule_module h]
  exact r.read

/-- The lexical check is the projection of the checked boundary. -/
theorem admitModule_bound {module : TypeScript.Module}
    {r : ModuleReading table name allowed ambient}
    (h : admitModule name module table allowed ambient = .ok r) :
    SourceBindings.WellBound allowed (withAmbient ambient module) := by
  rw [← admitModule_module h]
  exact r.bound.wellBound

/-- O4: the declaration envelope holds of every admitted module, as a Prop. -/
theorem admitModule_envelope {module : TypeScript.Module}
    {r : ModuleReading table name allowed ambient}
    (h : admitModule name module table allowed ambient = .ok r) :
    EnvelopeValid name r.typing.ty r.classes module.decls := by
  rw [← admitModule_module h]
  exact (envelopeCheck_iff _ _ _ _).mp r.envelope

/-- **The envelope admits exactly the printed class declarations** (decisions row 120, part E2):
an admitted module's leading class declarations are the ones the printer writes for the program
it reads to (`ClassTable.moduleClasses`), in order. Concept `exact-codecs`, claim
`payload-class-decl-exact` (R3); with `ModuleEmission.admit`, the class section's exact
embedding at the boundary. -/
@[semantics "exact-codecs" (requirement := R3)]
theorem admitModule_classDecls {module : TypeScript.Module}
    {r : ModuleReading table name allowed ambient}
    (h : admitModule name module table allowed ambient = .ok r) :
    (Program.splitClasses module.decls).1 = r.classDecls :=
  Classes.readClassDecls_eq_checked (admitModule_envelope h).declared
    (moduleClasses_checked r.classified)

/-- For a fixed reading there is one typing certificate; `TypedProgram.unique` is why the
completeness statements below name the recorded type and not the certificate. -/
theorem ModuleReading.typing_eq (r : ModuleReading table name allowed ambient)
    (typing : TypedProgram (nativeSignature table) r.program) : r.typing = typing :=
  TypedProgram.unique _ _

/-- Completeness of source admission against its declared checks, including stored-annotation support. -/
theorem admitModule_complete {module : TypeScript.Module} {program : NativeEff}
    (bound : SourceBindings.Checked allowed (withAmbient ambient module))
    (read : Program.readModule (nativeSignature table) (nativeSpell table) module.decls =
      .ok program)
    (formed : Formation.InputFormed program table)
    (typing : TypedProgram (nativeSignature table) program)
    {classes : Classes.Classes} {classDecls : List TypeScript.ClassDecl}
    (classified : ClassTable.moduleClasses (nativeSignature table) name typing.ty program =
      .ok (classes, classDecls))
    (annotations : annotationRefusal program = none)
    (env : envelopeCheck name typing.ty classes module.decls = none) :
    ∃ r, admitModule name module table allowed ambient = .ok r ∧
      r.program = program ∧ r.typing.ty = typing.ty :=
  ⟨⟨module, program, formed, typing, classes, classDecls, classified, annotations, bound, read,
      env⟩,
    ModuleReading.recheck ⟨module, program, formed, typing, classes, classDecls, classified,
      annotations, bound, read, env⟩, rfl, rfl⟩

/-- A module has one reading: the program, the typing and the evidence are functions of it. -/
theorem ModuleReading.unique (left right : ModuleReading table name allowed ambient)
    (same : left.module = right.module) : left = right := by
  have hl := left.recheck
  rw [same] at hl
  exact Except.ok.inj (hl.symm.trans right.recheck)

/-! ## The producer's output is admitted -/

/-- The round trip in certificate form: what the checked producer emitted, when it reads
back to its program, is admitted by the checked reader to the same program and the same typing
certificate. The host supplies the bindings its prelude provides; everything else is read off
the printer's own equations. (`readModule_printModule` gives the reading from the pieces'.) -/
theorem ModuleEmission.admit {program : NativeEff} {table : RowTable} {name : String}
    (e : ModuleEmission program table name)
    (read : Program.readModule (nativeSignature table) (nativeSpell table) e.module.decls =
      .ok program)
    {allowed : List Bindings.Origin} {ambient : List TypeScript.Import}
    (bound : SourceBindings.Checked allowed (withAmbient ambient e.module)) :
    ∃ r, admitModule name e.module table allowed ambient = .ok r ∧
      r.program = program ∧ r.typing.ty = e.typing.ty := by
  obtain ⟨safe, _, printed⟩ := Program.printEntry_ok e.generated
  obtain ⟨layers, main, body, shape, plain, declaration⟩ := Program.printModule_shape printed
  obtain ⟨hname, _, hexported, htype⟩ := Program.printDecl_fields declaration
  have split : Program.splitClasses e.module.decls =
      (e.classDecls, layers.map TypeScript.Decl.const ++ [.const main]) := by
    simp only [ModuleEmission.module]
    rw [Program.splitClasses_append, shape]
    simp only [List.map_append, List.map_cons, List.map_nil]
  have declared : Program.blockClasses e.module.decls = some e.classes := by
    rw [Program.blockClasses, split]
    exact Classes.readClassDecls_checked (moduleClasses_checked e.classified)
  have env : envelopeCheck name e.typing.ty e.classes e.module.decls = none := by
    refine (envelopeCheck_iff _ _ _ _).mpr
      ⟨safe, declared, ⟨main, ?_, hname, hexported, htype⟩, ?_⟩
    · simp only [split, List.getLast?_append, List.getLast?_singleton, Option.some_or]
    · intro d mem
      rw [split] at mem
      simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at mem
      obtain ⟨c, hc, heq⟩ := List.mem_map.mp mem
      exact ⟨c, heq.symm, (plain c hc).1, (plain c hc).2⟩
  exact admitModule_complete bound read e.formed e.typing e.classified
    (Program.printEntry_annotations e.generated) env

end Effect4.Codegen
