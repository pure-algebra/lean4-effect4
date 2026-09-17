import Effect4.Codegen.Templates

/-!
# Codegen.Print — `Eff` into TypeScript: the generated fold over the table of printed clauses

`print` has no clause of its own. It is `cata_eff` of ONE table-driven layer function
(`Templates.printAlg`): choose the row of `Codegen/Templates.lean` for the constructor and its
classifier, print each argument by sort at the depth the row gives it, instantiate the row's
skeleton. What is not a skeleton is a hand field of that algebra: the row call of `perform`
(`printRow`, `Codegen/PrintLeaf.lean`), a generator's statements, and the two spines. The
reader (`Codegen/Read.lean`) runs the same rows the other way.

The target is the pinned lean4-typescript fragment (`TypeScript.Expr`, `TypeScript.Stmt`), which
`TypeScript.Render.expr house0 0` renders at a fixed layout: equal syntax is equal bytes, so the
printer is byte-deterministic without a width heuristic anywhere in it.

What the table refuses, the printer refuses by name rather than by a fallback spelling: the five
internal fiber actions (`interruptScoped`, `awaitAllFailFast`, `snapshotChildren`,
`awaitNewChildren`, `setContext`) have no public rc.112 export with the same frame shape.
`PrintRefusal` is the closed refusal alphabet; a refusal is data, never a printed guess.

The hand printer this replaced (one clause per constructor, six mutual functions) agreed with
the fold on a sample of every constructor and classifier and on the 400 seeded programs before
it was deleted (2026-09-17); the printed bytes are pinned independently by
`Test/Codegen/PrintContract.lean`, the corpus goldens and the truth harness's modules.
-/

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-- `print sig n e` is `e` as one TypeScript expression, with `n` the environment's length.
Every binder a clause introduces is `Var.name` of the position it occupies, as its row's depth
column says. -/
def print (sig : Signature Op) (n : Nat) (e : Eff Op) : Except PrintRefusal TypeScript.Expr :=
  Effect4.Codegen.Templates.printT sig n e

/-- A layer as one TypeScript expression. A layer is closed: its bodies print at environment
length `0`. -/
def printLayer (sig : Signature Op) (l : LayerTerm Op) : Except PrintRefusal TypeScript.Expr :=
  Effect4.Codegen.Templates.printLayerT sig l

/-- A row's invocation prints as its row call: the one hand field of a program's clauses. -/
theorem print_perform (sig : Signature Op) (n : Nat) (op : Op) (request : Term) :
    print sig n (.perform op request) = printRow (sig.rowOf op) request := rfl

/-- The declared type of the main declaration, as target syntax.

**What this does today.** The declared type is `Effect.Effect<A, E>` — the two parameters
`EffTy` spells — exactly when the requirement row is empty. A program *with* a requirement has
no two-parameter spelling here, so it prints with **no declared type at all** and the host
infers one.

**The policy this owes (DI-24, `docs/DESIGN-ISSUES.md`).** A program prints its declared type
*always*, with three parameters — `Effect.Effect<A, E, R>` — because a printed program with no
declared type is the one case where the printed image carries less than the program's own
typing, and the type oracle (DI-29) cannot check what is not printed. What is not settled, and
so is not implemented here, is the *spelling* of `R`: the requirement row is a set of
`ServiceKey`s, and the target spells a requirement as the union of the services' `Identifier`
types, which is the same open question as the class spelling of keys in `printLayer` above.
Until that spelling is fixed under `tsc` on the truth harness, this arm stays two-parameter
and a requirement-carrying program stays untyped in its printed image; the reader
(`Codegen/Read.lean`) reads both shapes.

This function decides that annotation, and the reading boundary
(`Codegen/Admit.lean`) compares a declared annotation with its answer, so the rule has
exactly one owner and DI-24's omission or a later `R` spelling changes one place. -/
def declarationType (ty : EffTy) : Except PrintRefusal (Option TypeScript.TypeRef) :=
  if ty.requires = Requirement.empty then do
    let answer ← match Effect4.Codegen.Types.ofTy ty.answer with
      | some target => .ok target
      | none => .error (.typeSpelling ty.answer.render)
    let error ← match Effect4.Codegen.Types.ofTy ty.error with
      | some target => .ok target
      | none => .error (.typeSpelling ty.error.render)
    .ok (some (.name ["Effect", "Effect"] [answer, error]))
  else .ok none

/-- The printed program as an exported constant carrying `declarationType`'s annotation. -/
def printDecl (name : String) (ty : EffTy) (body : TypeScript.Expr) :
    Except PrintRefusal TypeScript.ConstDecl := do
  let annotation ← declarationType ty
  .ok { doc := [], name := name, value := body, type := annotation }

/-- The raw declaration printer can represent its emitted annotation. This is
not target type checking: requirement-bearing declarations still omit it. -/
def declarationTypeRepresentable (ty : EffTy) : Bool :=
  ty.requires != Requirement.empty ||
    (Effect4.Codegen.Types.ofTy ty.answer).isSome && (Effect4.Codegen.Types.ofTy ty.error).isSome

/-- Legacy malformed type strings now refuse instead of becoming raw target text.
The representability premise states that change in the declaration printer's domain. -/
theorem declarationType_ok {ty : EffTy} (hr : declarationTypeRepresentable ty = true) :
    ∃ annotation, declarationType ty = .ok annotation := by
  unfold declarationTypeRepresentable at hr
  unfold declarationType
  split
  · rename_i h
    simp only [h, bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at hr
    cases ha : Effect4.Codegen.Types.ofTy ty.answer <;>
      cases he : Effect4.Codegen.Types.ofTy ty.error <;> simp_all [bind, Except.bind]
  · exact ⟨_, rfl⟩

/-- Everything a successful declaration retains: its requested name, its body unchanged,
its export flag, and the annotation this type's one owner decided. -/
theorem printDecl_fields {name : String} {ty : EffTy} {body : TypeScript.Expr}
    {decl : TypeScript.ConstDecl} (hp : printDecl name ty body = .ok decl) :
    decl.name = name ∧ decl.value = body ∧ decl.exported = true ∧
      declarationType ty = .ok decl.type := by
  unfold printDecl at hp
  cases h : declarationType ty with
  | error why => simp [h, bind, Except.bind] at hp
  | ok annotation =>
    rw [h] at hp
    simp only [bind, Except.bind] at hp
    cases hp
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful raw declaration retains its expression exactly. -/
theorem printDecl_value {name : String} {ty : EffTy} {body : TypeScript.Expr}
    {decl : TypeScript.ConstDecl} (hp : printDecl name ty body = .ok decl) :
    decl.value = body :=
  (printDecl_fields hp).2.1

/-- A representable declaration type prints, at every name and body. -/
theorem printDecl_readable (name : String) (ty : EffTy) (body : TypeScript.Expr)
    (hr : declarationTypeRepresentable ty = true) :
    ∃ decl, printDecl name ty body = .ok decl := by
  obtain ⟨annotation, ha⟩ := declarationType_ok hr
  refine ⟨{ doc := [], name := name, value := body, type := annotation }, ?_⟩
  simp only [printDecl, ha, bind, Except.bind]

/-- The printed program as a declaration block (the host rows slice): one
`const L_<path> = …` per referenced layer target, in declaration order (`Path.declBefore`: a
target inside another first, then program order), each hoisted out of the program so that
its defining site and every reference print as the one identifier (`Refs.lean` `hoistAll`),
which is one rc.112 layer object and one memo entry; the main declaration last. A program
with no references is `[printDecl name ty (print …)]`. `readModule` (`Codegen/Read.lean`)
is the inverse on what this prints. -/
def printModule (sig : Signature Op) (name : String) (ty : EffTy) (e : Eff Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  match e.hoistAll with
  | .error target => .error (.layerRef target)
  | .ok (main, decls) => do
    let ordered := Path.sortBy Path.declBefore (decls.map (·.1))
    let ds ← ordered.mapM fun t =>
      match decls.find? (·.1 == t) with
      | some (_, l) => do
        let x ← printLayer sig l
        .ok ({ doc := [], name := LayerTerm.refName t, value := x } : TypeScript.ConstDecl)
      | none => .error (.layerRef t)
    let m ← print sig 0 main
    let declaration ← printDecl name ty m
    .ok (ds ++ [declaration])

/-- Print an admitted program against its row table. Refuses by name if the requested
export name is unsafe (a printed binder `a0`, a reserved head, a layer reference name, or
no legal binding at all), and then if any row carries an unsafe name. Refusing the export
name here is what lets the reading boundary compare names at all: a block exporting `a0`
would be read back as a binder. -/
def printEntry (table : List Row) (sig : Signature Op) (name : String) (ty : EffTy) (e : Eff Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  if !exportNameSafe name then .error (.unsafeName name)
  else
    match table.find? (fun row => !rowNamesSafe row) with
    | some row => .error (.unsafeName row.spelling)
    | none => printModule sig name ty e

/-- Everything a successful entry establishes: the export name and every row name are
safe, and the block is exactly what the module printer produced. -/
theorem printEntry_ok {table : List Row} {sig : Signature Op} {name : String} {ty : EffTy}
    {e : Eff Op} {decls : List TypeScript.ConstDecl}
    (h : printEntry table sig name ty e = .ok decls) :
    exportNameSafe name = true ∧ table.find? (fun row => !rowNamesSafe row) = none ∧
      printModule sig name ty e = .ok decls := by
  unfold printEntry at h
  split at h
  · simp at h
  · rename_i unsafe?
    have safe : exportNameSafe name = true := by
      simpa using unsafe?
    split at h
    · simp at h
    · rename_i clean
      exact ⟨safe, clean, h⟩

end Effect4.Program


