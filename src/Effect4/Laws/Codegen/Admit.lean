import Effect4.Codegen.Admit
import Effect4.Laws.Codegen.Checked
import Effect4.Laws.Codegen.SourceBindings

/-!
# The reading certificate against its own checks

`envelopeCheck` is a computed answer; `EnvelopeValid` is the same four facts as a Prop, and
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

/-- The four facts the envelope decides, stated on the declaration block. -/
structure EnvelopeValid (name : String) (ty : EffTy) (decls : List TypeScript.Decl) : Prop where
  safe : exportNameSafe name = true
  main : ∃ main : TypeScript.ConstDecl, decls.getLast? = some (.const main) ∧
    main.name = name ∧ main.exported = true ∧ declarationType ty = .ok main.type
  layers : ∀ d ∈ decls.dropLast, ∃ c : TypeScript.ConstDecl,
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
theorem envelopeCheck_iff (name : String) (ty : EffTy) (decls : List TypeScript.Decl) :
    envelopeCheck name ty decls = none ↔ EnvelopeValid name ty decls := by
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
      · rename_i hmain
        constructor
        · intro refused
          cases refused
        · intro valid
          obtain ⟨main, hlast, _, _, _⟩ := valid.main
          rw [mainConst_eq_some.mpr hlast] at hmain
          cases hmain
      · rename_i main hmain
        have hlast : decls.getLast? = some (.const main) := mainConst_eq_some.mp hmain
        have uniqueMain : ∀ m : TypeScript.ConstDecl,
            decls.getLast? = some (.const m) → m = main := by
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
                exact ⟨safe, ⟨main, hlast, hname, hexported, by rw [hdt, htype]⟩, layers⟩
              · intro valid
                exact valid.layers

/-! ## The certificate -/

/-- A completed reading is exactly what the computed boundary returns for its module. -/
theorem ModuleReading.recheck (r : ModuleReading table name allowed ambient) :
    admitModule name r.module table allowed ambient = .ok r := by
  obtain ⟨module, program, typing, bound, read, env⟩ := r
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
      split
      · rename_i refused
        rw [checkTypedProgram_eq_some typing] at refused
        cases refused
      · rename_i typing' htyping
        have sameTyping : typing' = typing :=
          Option.some.inj (htyping.symm.trans (checkTypedProgram_eq_some typing))
        subst sameTyping
        split
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
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
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
    EnvelopeValid name r.typing.ty module.decls := by
  rw [← admitModule_module h]
  exact (envelopeCheck_iff _ _ _).mp r.envelope

/-- For a fixed reading there is one typing certificate; `TypedProgram.unique` is why the
completeness statements below name the recorded type and not the certificate. -/
theorem ModuleReading.typing_eq (r : ModuleReading table name allowed ambient)
    (typing : TypedProgram (nativeSignature table) r.program) : r.typing = typing :=
  TypedProgram.unique _ _

/-- Completeness of the boundary against its own four checks. -/
theorem admitModule_complete {module : TypeScript.Module} {program : NativeEff}
    (bound : SourceBindings.Checked allowed (withAmbient ambient module))
    (read : Program.readModule (nativeSignature table) (nativeSpell table) module.decls =
      .ok program)
    (typing : TypedProgram (nativeSignature table) program)
    (env : envelopeCheck name typing.ty module.decls = none) :
    ∃ r, admitModule name module table allowed ambient = .ok r ∧
      r.program = program ∧ r.typing.ty = typing.ty :=
  ⟨⟨module, program, typing, bound, read, env⟩,
    ModuleReading.recheck ⟨module, program, typing, bound, read, env⟩, rfl, rfl⟩

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
  have decls : e.module.decls = layers.map TypeScript.Decl.const ++ [.const main] := by
    simp [ModuleEmission.module, shape, List.map_append]
  have env : envelopeCheck name e.typing.ty e.module.decls = none := by
    refine (envelopeCheck_iff _ _ _).mpr ⟨safe, ⟨main, ?_, hname, hexported, htype⟩, ?_⟩
    · simp [decls, List.getLast?_append, List.getLast?_singleton]
    · intro d mem
      rw [decls] at mem
      simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at mem
      obtain ⟨c, hc, heq⟩ := List.mem_map.mp mem
      exact ⟨c, heq.symm, (plain c hc).1, (plain c hc).2⟩
  exact admitModule_complete bound read e.typing env

end Effect4.Codegen
