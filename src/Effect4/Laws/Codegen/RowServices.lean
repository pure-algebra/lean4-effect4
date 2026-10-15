import Effect4.Codegen.RowServices

/-!
# Laws.Codegen.RowServices — the row namespaces' services read back exactly

A module declares each row namespace that is an Effect service after its payload classes
(`rowServiceDecls`, `Codegen/RowServices.lean`; decisions row 378 (19)). The declarations are a
function of the row table, so the reader takes the table and checks them against the services'
data (`readRowServices`). These are the two laws of an exact embedding of the table's services
into the declarations that follow the classes: the retraction (`readRowServices_rowServiceDecls`)
and exactness (`readRowServices_exact`).

Placement: concept `exact-codecs`, steps of the claim `module-defs-round-trip` (R8) through the
module laws (`readModuleWith_printModuleWith`, `readModuleWith_printModuleWith_defs`,
`Laws/Codegen/Module.lean`), their consumers. Reach: every signature and every row table. They do
not establish that tsgo accepts the declarations or that rc.112 provides the services: the
receipts' finite checks are that evidence.
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-! ## An accessor -/

/-- A method's accessor is an accessor: the check accepts what `accessorExpr` writes. A step of
`readRowServices_rowServiceDecls`. -/
theorem isAccessor_accessorExpr (keyName m : String) (request : Option TypeScript.TypeRef) :
    isAccessor keyName m request (accessorExpr keyName m request) = true := by
  cases request with
  | none => exact decide_eq_true ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some request => exact decide_eq_true ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What the accessor check accepts is exactly what `accessorExpr` writes. A step of
`readRowServices_exact`. -/
theorem isAccessor_exact {keyName m : String} {request : Option TypeScript.TypeRef}
    {e : TypeScript.Expr} (h : isAccessor keyName m request e = true) :
    e = accessorExpr keyName m request := by
  unfold isAccessor at h
  split at h
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := of_decide_eq_true h
    rfl
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := of_decide_eq_true h
    rfl
  · exact absurd h Bool.false_ne_true

/-- A service's accessors are its accessors, in order. A step of
`readRowServices_rowServiceDecls`. -/
theorem isAccessors_map (keyName : String) :
    ∀ methods : List (String × Option TypeScript.TypeRef),
      isAccessors keyName (methods.map fun (m, request) => (m, accessorExpr keyName m request))
        methods = true
  | [] => rfl
  | (m, request) :: methods => by
    show (decide (m = m) && isAccessor keyName m request (accessorExpr keyName m request) &&
      isAccessors keyName _ methods) = true
    rw [decide_eq_true rfl, isAccessor_accessorExpr, isAccessors_map keyName methods]
    rfl

/-- What the accessors' check accepts is exactly a service's accessors. A step of
`readRowServices_exact`. -/
theorem isAccessors_exact {keyName : String} :
    ∀ {entries : List (String × TypeScript.Expr)} {methods : List (String × Option TypeScript.TypeRef)},
      isAccessors keyName entries methods = true →
      entries = methods.map fun (m, request) => (m, accessorExpr keyName m request)
  | [], [], _ => rfl
  | (m', e) :: entries, (m, request) :: methods, h => by
    simp only [isAccessors, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, he⟩, hs⟩ := h
    rw [isAccessor_exact he, isAccessors_exact hs]
    rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true

/-! ## A service's two declarations -/

/-- A service's declarations are its declarations. A step of `readRowServices_rowServiceDecls`. -/
theorem RowServiceData.isDecls_decls (d : RowServiceData) :
    ∃ key ns, d.decls = [key, ns] ∧ d.isDecls key ns = true := by
  refine ⟨_, _, rfl, ?_⟩
  show (decide _ && isAccessors d.keyName _ d.methods) = true
  rw [decide_eq_true ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    isAccessors_map]
  rfl

/-- What the declarations' check accepts is exactly a service's two declarations. A step of
`readRowServices_exact`. -/
theorem RowServiceData.isDecls_exact {d : RowServiceData} {key ns : TypeScript.ConstDecl}
    (h : d.isDecls key ns = true) : d.decls = [key, ns] := by
  unfold RowServiceData.isDecls at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨hd, ha⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := of_decide_eq_true hd
    rw [isAccessors_exact ha]
    rfl
  · exact absurd h Bool.false_ne_true

/-! ## The table's services -/

/-- The services' declarations read back, two for each service, leaving what follows them. A
step of `readRowServices_rowServiceDecls`. -/
theorem readServiceDecls_decls :
    ∀ (data : List RowServiceData) (rest : List TypeScript.Decl),
      readServiceDecls data ((data.flatMap RowServiceData.decls).map .const ++ rest) = some rest
  | [], rest => rfl
  | d :: ds, rest => by
    obtain ⟨key, ns, hd, hk⟩ := d.isDecls_decls
    simp only [List.flatMap_cons, hd, List.map_cons, List.cons_append, List.nil_append,
      readServiceDecls, hk, if_true]
    exact readServiceDecls_decls ds rest

/-- What the services' check accepts is exactly their declarations, two for each service. A step
of `readRowServices_exact`. -/
theorem readServiceDecls_exact :
    ∀ {data : List RowServiceData} {decls rest : List TypeScript.Decl},
      readServiceDecls data decls = some rest →
      decls = (data.flatMap RowServiceData.decls).map .const ++ rest
  | [], decls, rest, h => by
    simp only [readServiceDecls, Option.some.injEq] at h
    subst h
    rfl
  | d :: ds, decls, rest, h => by
    simp only [readServiceDecls] at h
    split at h
    · rename_i key ns tail
      split at h
      · rename_i hk
        rw [readServiceDecls_exact h]
        simp only [List.flatMap_cons, d.isDecls_exact hk, List.map_cons, List.cons_append,
          List.nil_append]
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- A table with no row prints no service: the envelope's case. A step of
`ModuleEmission.readModule`. -/
theorem rowServiceDecls_nil (sig : Signature Op) : rowServiceDecls sig [] = .ok [] := rfl

/-- **The row services read back**: the declarations of a table's services, followed by any
declarations, read back to those that follow. The retraction of the exact embedding of the
table's services into a module's declarations. Concept `exact-codecs`, a step of
`module-defs-round-trip` (R8) through `readModuleWith_printModuleWith` and
`readModuleWith_printModuleWith_defs`. -/
theorem readRowServices_rowServiceDecls {sig : Signature Op} {table : List Row}
    {svc : List TypeScript.ConstDecl} (printed : rowServiceDecls sig table = .ok svc)
    (rest : List TypeScript.Decl) : readRowServices sig table (svc.map .const ++ rest) = some rest := by
  unfold rowServiceDecls at printed
  cases hd : rowServiceData sig table with
  | error why => rw [hd] at printed; exact absurd printed (by simp only [Except.map, reduceCtorEq, not_false_eq_true])
  | ok data =>
    rw [hd] at printed
    simp only [Except.map, Except.ok.injEq] at printed
    subst printed
    simp only [readRowServices, hd]
    exact readServiceDecls_decls data rest

/-- **What the row-service reader accepts is exactly the table's services' declarations**,
followed by what it leaves. Exactness of the embedding: the reader answers only where the table's
services print, and the declarations it consumed are what `rowServiceDecls` prints. -/
theorem readRowServices_exact {sig : Signature Op} {table : List Row}
    {decls rest : List TypeScript.Decl} (h : readRowServices sig table decls = some rest) :
    ∃ svc, rowServiceDecls sig table = .ok svc ∧ decls = svc.map .const ++ rest := by
  unfold readRowServices at h
  cases hd : rowServiceData sig table with
  | error why => rw [hd] at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | ok data =>
    rw [hd] at h
    exact ⟨data.flatMap RowServiceData.decls, by simp only [rowServiceDecls, hd, Except.map],
      readServiceDecls_exact h⟩

end Effect4.Program
