import Effect4.Codegen.Templates

/-!
# Codegen.Print — `Eff` into TypeScript: the generated fold over the table of printed clauses

`print` has no clause of its own. It is `cata_eff` of ONE table-driven layer function
(`Templates.printAlg`): choose the row of `Codegen/Templates.lean` for the constructor and its
classifier, print each argument by sort at the depth the row gives it, instantiate the row's
skeleton. Every constructor has a row; the row call of `perform` is the one row that is a codec
and not a skeleton (`printRow`, `Codegen/PrintLeaf.lean`), and the three spines are the
algebra's only hand fields. The reader (`Codegen/Read.lean`) runs the same rows the other way.

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

/-- A row's invocation prints as its row call: the table's `rowCall` row, by computation. -/
theorem print_perform (sig : Signature Op) (n : Nat) (op : Op) (request : Term) :
    print sig n (.perform op request) = printRow (sig.rowOf op) request := rfl

/-- The complete requirement row as target syntax. The empty union is `never`. -/
def requirementType (scopeKey : ServiceKey) (requires : Requirement) : TypeScript.TypeRef :=
  match requires.elems.map (keyIdentifier scopeKey) with
  | [] => .name ["never"] []
  | [one] => one
  | many => .union many

/-- The complete declared type `Effect.Effect<A, E, R>`. The native API defaults to
its reserved scope key; generic module printing passes the signature's scope key.
This is structural annotation evidence, not a general target typing theorem. -/
def declarationType (ty : EffTy) (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    Except PrintRefusal (Option TypeScript.TypeRef) := do
  let answer ← match Effect4.Codegen.Types.ofTy ty.answer with
    | some target => .ok target
    | none => .error (.typeSpelling ty.answer.render)
  let error ← match Effect4.Codegen.Types.ofTy ty.error with
    | some target => .ok target
    | none => .error (.typeSpelling ty.error.render)
  .ok (some (.name ["Effect", "Effect"] [answer, error, requirementType scopeKey ty.requires]))

/-- The printed program as an exported constant carrying `declarationType`'s annotation. -/
def printDecl (name : String) (ty : EffTy) (body : TypeScript.Expr)
    (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    Except PrintRefusal TypeScript.ConstDecl := do
  let annotation ← declarationType ty scopeKey
  .ok { doc := [], name := name, value := body, type := annotation }

/-- Answer and error types must both be representable; a nonempty requirement row
never bypasses that check. Requirement identifiers have a total structural spelling. -/
def declarationTypeRepresentable (ty : EffTy) : Bool :=
  (Effect4.Codegen.Types.ofTy ty.answer).isSome && (Effect4.Codegen.Types.ofTy ty.error).isSome

/-- Representability suffices for a complete annotation at every scope identity. -/
theorem declarationType_ok {ty : EffTy} (hr : declarationTypeRepresentable ty = true)
    (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    ∃ annotation, declarationType ty scopeKey = .ok annotation := by
  simp only [declarationTypeRepresentable, Bool.and_eq_true, Option.isSome_iff_exists] at hr
  obtain ⟨⟨answer, ha⟩, ⟨error, he⟩⟩ := hr
  exact ⟨_, by simp only [declarationType, ha, he, bind, Except.bind]; rfl⟩

/-- A successful declaration always retains all three slots, including the complete
requirement row. Consumer: checked module production and its annotation admission check. -/
theorem declarationType_complete {ty : EffTy} {scopeKey : ServiceKey}
    {annotation : Option TypeScript.TypeRef} (h : declarationType ty scopeKey = .ok annotation) :
    ∃ answer error, annotation = some (.name ["Effect", "Effect"]
      [answer, error, requirementType scopeKey ty.requires]) := by
  unfold declarationType at h
  cases ha : Effect4.Codegen.Types.ofTy ty.answer with
  | none => simp only [ha, bind, Except.bind] at h; cases h
  | some answer =>
    cases he : Effect4.Codegen.Types.ofTy ty.error with
    | none => simp only [ha, he, bind, Except.bind] at h; cases h
    | some error =>
      simp only [ha, he, bind, Except.bind, Except.ok.injEq] at h
      exact ⟨answer, error, h.symm⟩

/-- Everything a successful declaration retains: its requested name, its body unchanged,
its export flag, and the annotation this type's one owner decided. -/
theorem printDecl_fields {scopeKey : ServiceKey} {name : String} {ty : EffTy} {body : TypeScript.Expr}
    {decl : TypeScript.ConstDecl} (hp : printDecl name ty body scopeKey = .ok decl) :
    decl.name = name ∧ decl.value = body ∧ decl.exported = true ∧
      declarationType ty scopeKey = .ok decl.type := by
  unfold printDecl at hp
  cases h : declarationType ty scopeKey with
  | error why => simp only [h, bind, Except.bind] at hp; cases hp
  | ok annotation =>
    rw [h] at hp
    simp only [bind, Except.bind] at hp
    cases hp
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful raw declaration retains its expression exactly. -/
theorem printDecl_value {scopeKey : ServiceKey} {name : String} {ty : EffTy} {body : TypeScript.Expr}
    {decl : TypeScript.ConstDecl} (hp : printDecl name ty body scopeKey = .ok decl) :
    decl.value = body :=
  (printDecl_fields hp).2.1

/-- A representable declaration type prints, at every name and body. -/
theorem printDecl_readable (name : String) (ty : EffTy) (body : TypeScript.Expr)
    (hr : declarationTypeRepresentable ty = true)
    (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    ∃ decl, printDecl name ty body scopeKey = .ok decl := by
  obtain ⟨annotation, ha⟩ := declarationType_ok hr scopeKey
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
    let declaration ← printDecl name ty m sig.scopeKey
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


