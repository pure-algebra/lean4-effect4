import Lean
import Lean.Util.CollectAxioms
import Effect4.Data.Row

/-!
# Data.Row declaration and proof-graph join

This test-only checker closes the existing `DATA-PG-ROW` graph without
creating another graph.  It separates Lean's complete 72-name module-owned
surface (including generated companions) from the 44 names deliberately
authored as the public Row API.  It also checks the 32 exported theorem
receipts, their exact kernel dependencies, every declaration owner, the exact
standard-order instance binders, and the frozen duplicate-prevention names.
The `DIFFERENCE` edge (`Row.diff` and its nine laws) joined on 2026-09-04 with
the provision algebra (`docs/research/2026-09-04-provision-algebra.md`).

The generic commands at the end exist only for bounded detector-reaction
fixtures.  The generated projection is the authority for edge closure; this
module contains no manual closure flag.
-/

open Lean Meta Elab Command

namespace Test.Data.RowAssurance

private def failJoin (detail : MessageData) : CommandElabM α :=
  throwError m!"data-row assurance mismatch: {detail}"

private def failHypotheses (detail : MessageData) : TermElabM α :=
  throwError m!"data-row assurance mismatch: {detail}"

private def declarationOwner? (environment : Environment) (name : Name) : Option Name := do
  if let some moduleIndex := environment.getModuleIdxFor? name then
    environment.header.moduleNames[moduleIndex]?
  else if environment.contains name then
    some environment.mainModule
  else
    none

private def declarationsOwnedBy (environment : Environment) (owner : Name) : List Name :=
  environment.constants.toList.foldl (init := []) fun declarations entry =>
    let name := entry.1
    if !name.isInternal && declarationOwner? environment name == some owner then
      name :: declarations
    else
      declarations

private def checkOwners (expectedOwner : Name) (names : List Name) : CommandElabM Unit := do
  let environment ← getEnv
  for name in names do
    unless environment.contains name do
      failJoin m!"missing declaration {name}"
    let actualOwner := declarationOwner? environment name
    unless actualOwner == some expectedOwner do
      failJoin m!"owner drift for {name}: expected {expectedOwner}, found {actualOwner}"

private def checkExactModuleSurface
    (expectedOwner : Name) (expected : List Name) : CommandElabM Unit := do
  checkOwners expectedOwner expected
  let actual := declarationsOwnedBy (← getEnv) expectedOwner
  let unexpected := actual.filter fun name => !expected.contains name
  let missing := expected.filter fun name => !actual.contains name
  unless unexpected.isEmpty && missing.isEmpty do
    failJoin m!"owned declaration census for {expectedOwner}: unexpected {unexpected}; missing {missing}"

private def expectedOwnedDeclarations : List Name :=
  [ `Effect4.Ascending
  , `Effect4.Row
  , `Effect4.Row.Subset
  , `Effect4.Row.ascending
  , `Effect4.Row.ascending_insert
  , `Effect4.Row.ascending_normalize
  , `Effect4.Row.casesOn
  , `Effect4.Row.ctorIdx
  , `Effect4.Row.diff
  , `Effect4.Row.diff.congr_simp
  , `Effect4.Row.diff.eq_1
  , `Effect4.Row.diff_empty
  , `Effect4.Row.diff_eq_empty_iff_subset
  , `Effect4.Row.diff_self
  , `Effect4.Row.diff_subset
  , `Effect4.Row.diff_subset_diff_left
  , `Effect4.Row.diff_subset_diff_right
  , `Effect4.Row.diff_union_right
  , `Effect4.Row.elems
  , `Effect4.Row.empty
  , `Effect4.Row.empty.eq_1
  , `Effect4.Row.eq_of_mem_iff
  , `Effect4.Row.insert
  , `Effect4.Row.insert.congr_simp
  , `Effect4.Row.instDecidableMemOfDecidableEq
  , `Effect4.Row.instDecidableSubsetOfDecidableEq
  , `Effect4.Row.instMembership
  , `Effect4.Row.mem_def
  , `Effect4.Row.mem_diff
  , `Effect4.Row.mem_insert
  , `Effect4.Row.mem_normalize
  , `Effect4.Row.mem_singleton
  , `Effect4.Row.mem_union
  , `Effect4.Row.mk
  , `Effect4.Row.mk.congr_simp
  , `Effect4.Row.mk.inj
  , `Effect4.Row.mk.injEq
  , `Effect4.Row.mk.noConfusion
  , `Effect4.Row.mk.sizeOf_spec
  , `Effect4.Row.noConfusion
  , `Effect4.Row.noConfusionType
  , `Effect4.Row.normalize
  , `Effect4.Row.normalize.congr_simp
  , `Effect4.Row.normalize.eq_1
  , `Effect4.Row.normalize.eq_2
  , `Effect4.Row.normalize.eq_def
  , `Effect4.Row.normalize_duplicate
  , `Effect4.Row.normalize_idempotent
  , `Effect4.Row.normalize_of_ascending
  , `Effect4.Row.not_mem_empty
  , `Effect4.Row.rec
  , `Effect4.Row.recOn
  , `Effect4.Row.singleton
  , `Effect4.Row.singleton.eq_1
  , `Effect4.Row.subset_iff
  , `Effect4.Row.subset_refl
  , `Effect4.Row.subset_trans
  , `Effect4.Row.subset_union_left
  , `Effect4.Row.subset_union_right
  , `Effect4.Row.union
  , `Effect4.Row.union.congr_simp
  , `Effect4.Row.union.eq_1
  , `Effect4.Row.union_assoc
  , `Effect4.Row.union_comm
  , `Effect4.Row.union_diff_distrib
  , `Effect4.Row.union_empty_left
  , `Effect4.Row.union_empty_right
  , `Effect4.Row.union_idem
  , `Effect4.ascending_iff
  , `Effect4.instDecidableEqRow
  , `Effect4.instDecidableEqRow.decEq
  , `Effect4.instDecidableEqRow.decEq.match_1
  ]

private def authoredApiDeclarations : List (Name × String) :=
  [ (`Effect4.Ascending, "IDENTITY")
  , (`Effect4.ascending_iff, "IDENTITY")
  , (`Effect4.Row, "IDENTITY")
  , (`Effect4.Row.mk, "IDENTITY")
  , (`Effect4.Row.elems, "IDENTITY")
  , (`Effect4.Row.ascending, "IDENTITY")
  , (`Effect4.Row.mem_def, "IDENTITY")
  , (`Effect4.Row.insert, "INSERT")
  , (`Effect4.Row.mem_insert, "INSERT")
  , (`Effect4.Row.ascending_insert, "INSERT")
  , (`Effect4.Row.normalize, "NORMALIZE")
  , (`Effect4.Row.mem_normalize, "NORMALIZE")
  , (`Effect4.Row.ascending_normalize, "NORMALIZE")
  , (`Effect4.Row.eq_of_mem_iff, "EXTENSIONALITY")
  , (`Effect4.Row.normalize_of_ascending, "NORMALIZE")
  , (`Effect4.Row.normalize_idempotent, "NORMALIZE")
  , (`Effect4.Row.normalize_duplicate, "NORMALIZE")
  , (`Effect4.Row.empty, "UNION")
  , (`Effect4.Row.not_mem_empty, "UNION")
  , (`Effect4.Row.singleton, "UNION")
  , (`Effect4.Row.mem_singleton, "UNION")
  , (`Effect4.Row.union, "UNION")
  , (`Effect4.Row.mem_union, "UNION")
  , (`Effect4.Row.union_assoc, "UNION")
  , (`Effect4.Row.union_comm, "UNION")
  , (`Effect4.Row.union_idem, "UNION")
  , (`Effect4.Row.union_empty_left, "UNION")
  , (`Effect4.Row.union_empty_right, "UNION")
  , (`Effect4.Row.Subset, "WEAKENING")
  , (`Effect4.Row.subset_iff, "WEAKENING")
  , (`Effect4.Row.subset_refl, "WEAKENING")
  , (`Effect4.Row.subset_trans, "WEAKENING")
  , (`Effect4.Row.subset_union_left, "WEAKENING")
  , (`Effect4.Row.subset_union_right, "WEAKENING")
  , (`Effect4.Row.diff, "DIFFERENCE")
  , (`Effect4.Row.mem_diff, "DIFFERENCE")
  , (`Effect4.Row.diff_subset, "DIFFERENCE")
  , (`Effect4.Row.diff_empty, "DIFFERENCE")
  , (`Effect4.Row.diff_self, "DIFFERENCE")
  , (`Effect4.Row.diff_eq_empty_iff_subset, "DIFFERENCE")
  , (`Effect4.Row.diff_union_right, "DIFFERENCE")
  , (`Effect4.Row.union_diff_distrib, "DIFFERENCE")
  , (`Effect4.Row.diff_subset_diff_left, "DIFFERENCE")
  , (`Effect4.Row.diff_subset_diff_right, "DIFFERENCE")
  ]

private def sixOrderHypotheses : List Name :=
  [ `LE, `LT, `DecidableEq, `DecidableLT,
    `Std.IsLinearOrder, `Std.LawfulOrderLT ]

private def hypothesisProfiles : List (Name × List Name) :=
  [ (`Effect4.Ascending, [`LT])
  , (`Effect4.ascending_iff, [`LT])
  , (`Effect4.Row, [`LT])
  , (`Effect4.Row.mk, [`LT])
  , (`Effect4.Row.elems, [`LT])
  , (`Effect4.Row.ascending, [`LT])
  , (`Effect4.Row.mem_def, [`LT])
  , (`Effect4.Row.insert, sixOrderHypotheses)
  , (`Effect4.Row.mem_insert, sixOrderHypotheses)
  , (`Effect4.Row.ascending_insert, sixOrderHypotheses)
  , (`Effect4.Row.normalize, sixOrderHypotheses)
  , (`Effect4.Row.mem_normalize, sixOrderHypotheses)
  , (`Effect4.Row.ascending_normalize, sixOrderHypotheses)
  , (`Effect4.Row.eq_of_mem_iff,
      [`LE, `LT, `Std.IsLinearOrder, `Std.LawfulOrderLT])
  , (`Effect4.Row.normalize_of_ascending, sixOrderHypotheses)
  , (`Effect4.Row.normalize_idempotent, sixOrderHypotheses)
  , (`Effect4.Row.normalize_duplicate, sixOrderHypotheses)
  , (`Effect4.Row.empty, [`LT])
  , (`Effect4.Row.not_mem_empty, [`LT])
  , (`Effect4.Row.singleton, [`LT])
  , (`Effect4.Row.mem_singleton, [`LT])
  , (`Effect4.Row.union, sixOrderHypotheses)
  , (`Effect4.Row.mem_union, sixOrderHypotheses)
  , (`Effect4.Row.union_assoc, sixOrderHypotheses)
  , (`Effect4.Row.union_comm, sixOrderHypotheses)
  , (`Effect4.Row.union_idem, sixOrderHypotheses)
  , (`Effect4.Row.union_empty_left, sixOrderHypotheses)
  , (`Effect4.Row.union_empty_right, sixOrderHypotheses)
  , (`Effect4.Row.Subset, [`LT])
  , (`Effect4.Row.subset_iff, [`LT])
  , (`Effect4.Row.subset_refl, [`LT])
  , (`Effect4.Row.subset_trans, [`LT])
  , (`Effect4.Row.subset_union_left, sixOrderHypotheses)
  , (`Effect4.Row.subset_union_right, sixOrderHypotheses)
  , (`Effect4.Row.diff, sixOrderHypotheses)
  , (`Effect4.Row.mem_diff, sixOrderHypotheses)
  , (`Effect4.Row.diff_subset, sixOrderHypotheses)
  , (`Effect4.Row.diff_empty, sixOrderHypotheses)
  , (`Effect4.Row.diff_self, sixOrderHypotheses)
  , (`Effect4.Row.diff_eq_empty_iff_subset, sixOrderHypotheses)
  , (`Effect4.Row.diff_union_right, sixOrderHypotheses)
  , (`Effect4.Row.union_diff_distrib, sixOrderHypotheses)
  , (`Effect4.Row.diff_subset_diff_left, sixOrderHypotheses)
  , (`Effect4.Row.diff_subset_diff_right, sixOrderHypotheses)
  ]

private def theoremReceipts : List (Name × String) :=
  [ (`Effect4.ascending_iff, "IDENTITY")
  , (`Effect4.Row.mem_def, "IDENTITY")
  , (`Effect4.Row.mem_insert, "INSERT")
  , (`Effect4.Row.ascending_insert, "INSERT")
  , (`Effect4.Row.mem_normalize, "NORMALIZE")
  , (`Effect4.Row.ascending_normalize, "NORMALIZE")
  , (`Effect4.Row.eq_of_mem_iff, "EXTENSIONALITY")
  , (`Effect4.Row.normalize_of_ascending, "NORMALIZE")
  , (`Effect4.Row.normalize_idempotent, "NORMALIZE")
  , (`Effect4.Row.normalize_duplicate, "NORMALIZE")
  , (`Effect4.Row.not_mem_empty, "UNION")
  , (`Effect4.Row.mem_singleton, "UNION")
  , (`Effect4.Row.mem_union, "UNION")
  , (`Effect4.Row.union_assoc, "UNION")
  , (`Effect4.Row.union_comm, "UNION")
  , (`Effect4.Row.union_idem, "UNION")
  , (`Effect4.Row.union_empty_left, "UNION")
  , (`Effect4.Row.union_empty_right, "UNION")
  , (`Effect4.Row.subset_iff, "WEAKENING")
  , (`Effect4.Row.subset_refl, "WEAKENING")
  , (`Effect4.Row.subset_trans, "WEAKENING")
  , (`Effect4.Row.subset_union_left, "WEAKENING")
  , (`Effect4.Row.subset_union_right, "WEAKENING")
  , (`Effect4.Row.mem_diff, "DIFFERENCE")
  , (`Effect4.Row.diff_subset, "DIFFERENCE")
  , (`Effect4.Row.diff_empty, "DIFFERENCE")
  , (`Effect4.Row.diff_self, "DIFFERENCE")
  , (`Effect4.Row.diff_eq_empty_iff_subset, "DIFFERENCE")
  , (`Effect4.Row.diff_union_right, "DIFFERENCE")
  , (`Effect4.Row.union_diff_distrib, "DIFFERENCE")
  , (`Effect4.Row.diff_subset_diff_left, "DIFFERENCE")
  , (`Effect4.Row.diff_subset_diff_right, "DIFFERENCE")
  ]

private def noAxioms : List Name := []
private def propextOnly : List Name := [`propext]
private def propextAndQuot : List Name := [`propext, `Quot.sound]

private def axiomReceipts : List (Name × List Name) :=
  [ (`Effect4.ascending_iff, noAxioms)
  , (`Effect4.Row.mem_def, noAxioms)
  , (`Effect4.Row.mem_insert, propextAndQuot)
  , (`Effect4.Row.ascending_insert, propextAndQuot)
  , (`Effect4.Row.mem_normalize, propextAndQuot)
  , (`Effect4.Row.ascending_normalize, propextAndQuot)
  , (`Effect4.Row.eq_of_mem_iff, propextOnly)
  , (`Effect4.Row.normalize_of_ascending, propextAndQuot)
  , (`Effect4.Row.normalize_idempotent, propextAndQuot)
  , (`Effect4.Row.normalize_duplicate, propextAndQuot)
  , (`Effect4.Row.not_mem_empty, propextOnly)
  , (`Effect4.Row.mem_singleton, propextAndQuot)
  , (`Effect4.Row.mem_union, propextAndQuot)
  , (`Effect4.Row.union_assoc, propextAndQuot)
  , (`Effect4.Row.union_comm, propextAndQuot)
  , (`Effect4.Row.union_idem, propextAndQuot)
  , (`Effect4.Row.union_empty_left, propextAndQuot)
  , (`Effect4.Row.union_empty_right, propextAndQuot)
  , (`Effect4.Row.subset_iff, noAxioms)
  , (`Effect4.Row.subset_refl, noAxioms)
  , (`Effect4.Row.subset_trans, noAxioms)
  , (`Effect4.Row.subset_union_left, propextAndQuot)
  , (`Effect4.Row.subset_union_right, propextAndQuot)
  , (`Effect4.Row.mem_diff, propextAndQuot)
  , (`Effect4.Row.diff_subset, propextAndQuot)
  , (`Effect4.Row.diff_empty, propextAndQuot)
  , (`Effect4.Row.diff_self, propextAndQuot)
  , (`Effect4.Row.diff_eq_empty_iff_subset, propextAndQuot)
  , (`Effect4.Row.diff_union_right, propextAndQuot)
  , (`Effect4.Row.union_diff_distrib, propextAndQuot)
  , (`Effect4.Row.diff_subset_diff_left, propextAndQuot)
  , (`Effect4.Row.diff_subset_diff_right, propextAndQuot)
  ]

private def forbiddenDuplicateDeclarations : List (Name × String) :=
  [ (`Effect4.RowOrder, "duplicate-order")
  , (`Effect4.Row.Comparator, "duplicate-order")
  , (`Effect4.RawRow, "duplicate-carrier")
  , (`Effect4.CheckedRow, "duplicate-carrier")
  , (`Effect4.CanonicalRow, "duplicate-carrier")
  , (`Effect4.Row.ofList, "unchecked-carrier-route")
  , (`Effect4.Row.append, "noncanonical-union-route")
  , (`Effect4.Row.normalization_preserves_denotation, "unowned-semantics")
  ]

private def graphEdges : List (String × String) :=
  [ ("IDENTITY", "DATA-ROW-IDENTITY")
  , ("ORDER", "DATA-ROW-ORDER")
  , ("INSERT", "DATA-ROW-INSERT")
  , ("NORMALIZE", "DATA-ROW-NORMALIZE")
  , ("EXTENSIONALITY", "DATA-ROW-EXTENSIONALITY")
  , ("UNION", "DATA-ROW-UNION")
  , ("DIFFERENCE", "DATA-ROW-DIFFERENCE")
  , ("WEAKENING", "DATA-ROW-WEAKENING")
  , ("COUNTEREXAMPLES", "DATA-ROW-COUNTEREXAMPLES")
  , ("TRUST", "DATA-ROW-TRUST")
  , ("COVERAGE", "DATA-ROW-COVERAGE")
  ]

private def sameNameSet (actual expected : List Name) : Bool :=
  actual.length == expected.length &&
    actual.all expected.contains && expected.all actual.contains

private def instanceBinderHeads (name : Name) : TermElabM (List Name) := do
  let info ← getConstInfo name
  forallTelescope info.type fun xs _ => do
    let mut heads := []
    for x in xs do
      let declaration ← x.fvarId!.getDecl
      if declaration.binderInfo.isInstImplicit then
        let binderType ← instantiateMVars declaration.type
        let some head := binderType.getAppFn.constName?
          | failHypotheses m!"instance binder on {name} has no constant head: {binderType}"
        heads := heads ++ [head]
    pure heads

private def checkHypothesisProfiles : TermElabM Unit := do
  let apiNames := authoredApiDeclarations.map Prod.fst
  let profileNames := hypothesisProfiles.map Prod.fst
  unless sameNameSet apiNames profileNames do
    failHypotheses m!"authored API and standard-hypothesis receipt names differ"
  for (name, expected) in hypothesisProfiles do
    let actual ← instanceBinderHeads name
    unless actual == expected do
      failHypotheses m!"exact standard-order hypotheses for {name}: expected {expected}, found {actual}"

private def checkTheoremReceipts : CommandElabM Unit := do
  let environment ← getEnv
  for (name, _) in theoremReceipts do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | some _ => failJoin m!"contracted theorem {name} is not a theorem declaration"
    | none => failJoin m!"missing contracted theorem {name}"

private def checkAxiomReceipts : CommandElabM Unit := do
  let theoremNames := theoremReceipts.map Prod.fst
  let axiomNames := axiomReceipts.map Prod.fst
  unless sameNameSet theoremNames axiomNames do
    failJoin m!"theorem and axiom receipt names differ"
  for (name, expected) in axiomReceipts do
    let actual := (← collectAxioms name).toList
    unless sameNameSet actual expected do
      failJoin m!"axiom receipt for {name}: expected {expected}, found {actual}"

private def checkForbiddenDuplicates : CommandElabM Unit := do
  let environment ← getEnv
  for (name, defect) in forbiddenDuplicateDeclarations do
    if environment.contains name then
      failJoin m!"forbidden {defect} declaration is present: {name}"

private def checkDataRowAssurance : CommandElabM Unit := do
  checkExactModuleSurface `Effect4.Data.Row expectedOwnedDeclarations
  checkOwners `Effect4.Data.Row (authoredApiDeclarations.map Prod.fst)
  checkTheoremReceipts
  checkAxiomReceipts
  checkForbiddenDuplicates
  liftTermElabM checkHypothesisProfiles

private def namesText (names : List Name) : String :=
  if names.isEmpty then "none" else String.intercalate "," (names.map toString)

private def emitDataRowAssurance : CommandElabM Unit := do
  checkDataRowAssurance
  for name in expectedOwnedDeclarations do
    liftIO <| IO.println s!"E4ROW\towned-declaration\t{name}\tEffect4.Data.Row\tE4-TYPE-DATA-ROW"
  for (name, edge) in authoredApiDeclarations do
    liftIO <| IO.println s!"E4ROW\tapi\t{name}\tEffect4.Data.Row\tDATA-PG-ROW/{edge}"
  for (name, expected) in hypothesisProfiles do
    liftIO <| IO.println s!"E4ROW\thypotheses\t{name}\t{namesText expected}\texact"
  for (name, edge) in theoremReceipts do
    liftIO <| IO.println s!"E4ROW\ttheorem\t{name}\tDATA-PG-ROW/{edge}"
  for (name, expected) in axiomReceipts do
    liftIO <| IO.println s!"E4ROW\taxiom\t{name}\t{namesText expected}\tDATA-AX-ROW"
  for (name, defect) in forbiddenDuplicateDeclarations do
    liftIO <| IO.println s!"E4ROW\tabsent\t{name}\t{defect}\tchecked"
  for (edge, node) in graphEdges do
    liftIO <| IO.println s!"E4ROW\tgraph-edge\tDATA-PG-ROW/{edge}\t{node}\tderived"

syntax (name := effect4CheckDataRowAssurance)
  "#effect4_check_data_row_assurance" : command

syntax (name := effect4EmitDataRowAssurance)
  "#effect4_emit_data_row_assurance" : command

syntax (name := effect4CheckExactCurrentModuleSurface)
  "#effect4_check_exact_current_module_surface " "[" ident,* "]" : command

syntax (name := effect4CheckDataDeclarationOwners)
  "#effect4_check_data_declaration_owners " ident "[" ident,* "]" : command

elab_rules : command
  | `(#effect4_check_data_row_assurance) =>
      checkDataRowAssurance

elab_rules : command
  | `(#effect4_emit_data_row_assurance) =>
      emitDataRowAssurance

elab_rules : command
  | `(#effect4_check_exact_current_module_surface [$names:ident,*]) => do
      let environment ← getEnv
      checkExactModuleSurface environment.mainModule
        (names.getElems.map Syntax.getId).toList

elab_rules : command
  | `(#effect4_check_data_declaration_owners $owner:ident [$names:ident,*]) =>
      checkOwners owner.getId (names.getElems.map Syntax.getId).toList

#effect4_check_data_row_assurance
#effect4_emit_data_row_assurance

end Test.Data.RowAssurance
