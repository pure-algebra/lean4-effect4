import Effect4.Laws.Codegen.ReadLeaf
import Effect4.Laws.Codegen.Services
import Effect4.Laws.Codegen.RowServices
import Effect4.Laws.Program.Hoisting
import Effect4.Laws.Program.HoistingTotal
import Effect4.Laws.Auto.Semantics

/-!
# Declaration-block reconstruction

The existing printer orders captured layers for declaration, while the reader
orders them for restoration. Unique capture paths make that change of order
irrelevant to restoration. The module law below composes this fact with the
existing expression and layer reader laws and the hoisting inverse.

The composition law names successful hoisting, pieces that read back from their own printing,
and emitted reference names that decode. No law assumes a successful module read. Owed with
the structural domain of the table reader (R5.2): deriving the pieces' premises from the
original program's, and successful printing on that domain. Target typing, source-envelope
validation and host execution remain separate obligations.
-/

namespace Effect4.Program

variable {Op : Type}

open Effect4.Codegen.Classes (Classes)

variable {classes : Classes}

open scoped Effect4.Program.Path

private abbrev History (Op : Type) := List (List Nat × LayerTerm Op)

private theorem findHistory_perm {first second : History Op}
    (perm : first.Perm second) (unique : (first.map Prod.fst).Nodup)
    (target : List Nat) : first.find? (·.1 == target) = second.find? (·.1 == target) := by
  cases hf : first.find? (·.1 == target) with
  | none =>
    symm
    apply List.find?_eq_none.mpr
    intro entry mem
    exact List.find?_eq_none.mp hf entry (perm.mem_iff.mpr mem)
  | some entry =>
    have mem := List.mem_of_find?_eq_some hf
    have key : entry.1 = target := by
      simpa only [beq_iff_eq] using List.find?_some hf
    have found := Path.findEntry_of_mem ((perm.map Prod.fst).nodup unique) (perm.mem_iff.mp mem)
    simpa only [key] using found.symm

private theorem sortPaths_perm_eq {first second : List (List Nat)}
    (perm : first.Perm second) (unique : first.Nodup) :
    Path.sortBy Path.lt first = Path.sortBy Path.lt second := by
  apply List.Perm.eq_of_pairwise (le := fun a b => Path.lt a b = true)
  · intro a b _ _ ab ba
    exact Bool.noConfusion ((Field.ltKey_asymm ab).symm.trans ba)
  · exact Path.sortBy_pairwise Path.lt (fun _ _ _ => Field.ltKey_trans)
      (fun _ _ => Field.ltKey_total) unique
  · exact Path.sortBy_pairwise Path.lt (fun _ _ _ => Field.ltKey_trans)
      (fun _ _ => Field.ltKey_total) (perm.nodup unique)
  · exact (Path.sortBy_perm Path.lt first).trans
      (perm.trans (Path.sortBy_perm Path.lt second).symm)

/-- Reordering captured layer declarations does not change restoration when their
path keys are distinct. No equality on layer payloads is required. -/
theorem Eff.restoreAll_perm (root : Eff Op) {first second : History Op}
    (perm : first.Perm second) (unique : (first.map Prod.fst).Nodup) :
    root.restoreAll first = root.restoreAll second := by
  unfold Eff.restoreAll
  rw [sortPaths_perm_eq (perm.map Prod.fst) unique]
  simp only [findHistory_perm perm unique]

private def selectHistory (history : History Op) (targets : List (List Nat)) : History Op :=
  targets.filterMap fun target => history.find? (·.1 == target)

private theorem selectHistory_keys (all rest : History Op)
    (unique : (all.map Prod.fst).Nodup) (contained : ∀ entry ∈ rest, entry ∈ all) :
    selectHistory all (rest.map Prod.fst) = rest := by
  induction rest with
  | nil => rfl
  | cons entry rest ih =>
    have found := Path.findEntry_of_mem unique (contained entry (by simp))
    simp only [selectHistory, List.map_cons, List.filterMap_cons, found]
    congr 1
    exact ih (fun e he => contained e (List.mem_cons_of_mem _ he))

private theorem selectHistory_ordered_perm (history : History Op)
    (unique : (history.map Prod.fst).Nodup) :
    (selectHistory history (Path.sortBy Path.declBefore (history.map Prod.fst))).Perm
      history := by
  have perm := (Path.sortBy_perm Path.declBefore (history.map Prod.fst)).filterMap
    (fun target => history.find? (·.1 == target))
  change (selectHistory history _).Perm (selectHistory history _) at perm
  rw [selectHistory_keys history history unique (fun _ h => h)] at perm
  exact perm

private def printCaptured (sig : Signature Op) (history : History Op) (target : List Nat) :
    Except PrintRefusal TypeScript.ConstDecl :=
  match history.find? (·.1 == target) with
  | some (_, layer) => do
    let x ← printLayer sig layer
    .ok { doc := [], name := LayerTerm.refName target, value := x }
  | none => .error (.layerRef target)

private def readCaptured (classes : Classes) (sig : Signature Op)
    (spell : String → List RowArg → Option Op)
    (decl : TypeScript.Decl) : Except ReadRefusal (List Nat × LayerTerm Op) :=
  readLayerDecl classes sig spell decl

private theorem readCaptured_printCaptured {sig : Signature Op}
    {spell : String → List RowArg → Option Op}
    {history : History Op}
    (layers : ∀ entry ∈ history, entry.2.ReadsBack classes sig spell)
    (names : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {target : List Nat} {entry : List Nat × LayerTerm Op} {decl : TypeScript.ConstDecl}
    (found : history.find? (·.1 == target) = some entry)
    (printed : printCaptured sig history target = .ok decl) :
    readCaptured classes sig spell (.const decl) = .ok entry := by
  have mem := List.mem_of_find?_eq_some found
  have key : entry.1 = target := by
    simpa only [beq_iff_eq] using List.find?_some found
  simp only [printCaptured, found] at printed
  obtain ⟨body, hp, heq⟩ := bind_eq_ok.mp printed
  cases heq
  have hr := layers entry mem _ hp
  simp [readCaptured, readLayerDecl, ← key, names entry mem, hr]

private theorem readCaptured_mapM {sig : Signature Op}
    {spell : String → List RowArg → Option Op}
    {history : History Op}
    (layers : ∀ entry ∈ history, entry.2.ReadsBack classes sig spell)
    (names : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    (targets : List (List Nat)) {decls : List TypeScript.ConstDecl}
    (printed : targets.mapM (printCaptured sig history) = .ok decls) :
    (decls.map TypeScript.Decl.const).mapM (readCaptured classes sig spell) =
      .ok (selectHistory history targets) := by
  induction targets generalizing decls with
  | nil => cases printed; rfl
  | cons target targets ih =>
    simp only [List.mapM_cons] at printed
    obtain ⟨decl, hp, htail⟩ := bind_eq_ok.mp printed
    obtain ⟨rest, hrest, heq⟩ := bind_eq_ok.mp htail
    cases heq
    cases found : history.find? (·.1 == target) with
    | none => simp [printCaptured, found] at hp
    | some entry =>
      have hr := readCaptured_printCaptured layers names found hp
      simp [List.mapM_cons, hr, ih hrest, selectHistory, found]
      rfl

/-- Printed layer declarations begin with no definition constant: the first one's name carries
its path. A step of `readModule_printModule` and `readModule_printModule_defs`. -/
private theorem defsPrefix_layers {sig : Signature Op} {history : History Op}
    (names : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {targets : List (List Nat)} {decls : List TypeScript.ConstDecl}
    (printed : targets.mapM (printCaptured sig history) = .ok decls) :
    defsPrefix (decls.map TypeScript.Decl.const) = ([], decls.map TypeScript.Decl.const) := by
  cases targets with
  | nil => cases printed; rfl
  | cons target targets =>
    simp only [List.mapM_cons] at printed
    obtain ⟨decl, hp, htail⟩ := bind_eq_ok.mp printed
    obtain ⟨rest, _, heq⟩ := bind_eq_ok.mp htail
    cases heq
    cases found : history.find? (·.1 == target) with
    | none => simp only [printCaptured, found, reduceCtorEq] at hp
    | some entry =>
      have mem := List.mem_of_find?_eq_some found
      have key : entry.1 = target := by
        simpa only [beq_iff_eq] using List.find?_some found
      simp only [printCaptured, found] at hp
      obtain ⟨_, _, heq⟩ := bind_eq_ok.mp hp
      cases heq
      have named := names entry mem
      rw [key] at named
      simp only [List.map_cons, defsPrefix, named]

/-- Printed layer declarations begin with no service constant: the first one's name carries its
path. A step of `readModule_printModule_defs`. -/
private theorem servicePrefix_layers {sig : Signature Op} {history : History Op}
    (names : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {targets : List (List Nat)} {decls : List TypeScript.ConstDecl}
    (printed : targets.mapM (printCaptured sig history) = .ok decls) :
    servicePrefix (decls.map TypeScript.Decl.const) = ([], decls.map TypeScript.Decl.const) := by
  cases targets with
  | nil => cases printed; rfl
  | cons target targets =>
    simp only [List.mapM_cons] at printed
    obtain ⟨decl, hp, htail⟩ := bind_eq_ok.mp printed
    obtain ⟨rest, _, heq⟩ := bind_eq_ok.mp htail
    cases heq
    cases found : history.find? (·.1 == target) with
    | none => simp only [printCaptured, found, reduceCtorEq] at hp
    | some entry =>
      have mem := List.mem_of_find?_eq_some found
      have key : entry.1 = target := by
        simpa only [beq_iff_eq] using List.find?_some found
      simp only [printCaptured, found] at hp
      obtain ⟨_, _, heq⟩ := bind_eq_ok.mp hp
      cases heq
      have named := names entry mem
      rw [key] at named
      simp only [List.map_cons, servicePrefix, named]

/-- Definition constants, then declarations that begin with none, split there. A step of
`readModule_printModule_defs`. -/
theorem defsPrefix_append (cs : List TypeScript.ConstDecl) (rest : List TypeScript.Decl)
    (named : ∀ c ∈ cs, LayerTerm.readRefName c.name = none)
    (notService : ∀ c ∈ cs, isServiceConst c = false)
    (after : defsPrefix rest = ([], rest)) :
    defsPrefix (cs.map TypeScript.Decl.const ++ rest) = (cs, rest) := by
  induction cs with
  | nil => simpa only [List.map_nil, List.nil_append] using after
  | cons c cs ih =>
    have hc := named c List.mem_cons_self
    have hs := notService c List.mem_cons_self
    have hrest := ih (fun c' h => named c' (List.mem_cons_of_mem _ h))
      (fun c' h => notService c' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, List.cons_append, defsPrefix, hc, hs, Bool.false_eq_true,
      ↓reduceIte, hrest]

/-- Printed service constants, then declarations that the service prefix stops at, split there.
A step of `readModule_printModule_defs`. -/
theorem servicePrefix_append (svc : List TypeScript.ConstDecl) (rest : List TypeScript.Decl)
    (consts : ∀ c ∈ svc, isServiceConst c = true ∧ LayerTerm.readRefName c.name = none)
    (after : servicePrefix rest = ([], rest)) :
    servicePrefix (svc.map TypeScript.Decl.const ++ rest) = (svc, rest) := by
  induction svc with
  | nil => simpa only [List.map_nil, List.nil_append] using after
  | cons c svc ih =>
    obtain ⟨hs, hc⟩ := consts c List.mem_cons_self
    have hrest := ih (fun c' h => consts c' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, List.cons_append, servicePrefix, hc, hs, ↓reduceIte, hrest]

/-- The definition prefix stops at a block's printed services, or at its layers when it has no
service. A step of `readModule_printModule_defs`. -/
theorem defsPrefix_services (svc : List TypeScript.ConstDecl) (rest : List TypeScript.Decl)
    (consts : ∀ c ∈ svc, isServiceConst c = true ∧ LayerTerm.readRefName c.name = none)
    (after : defsPrefix rest = ([], rest)) :
    defsPrefix (svc.map TypeScript.Decl.const ++ rest) = ([], svc.map TypeScript.Decl.const ++ rest) := by
  cases svc with
  | nil => simpa only [List.map_nil, List.nil_append] using after
  | cons c svc =>
    obtain ⟨hs, hc⟩ := consts c List.mem_cons_self
    simp only [List.map_cons, List.cons_append, defsPrefix, hc, hs, ↓reduceIte]

/-- A block of class declarations, then constants, splits there. -/
theorem splitClasses_append (cs : List TypeScript.ClassDecl) (ds : List TypeScript.ConstDecl) :
    splitClasses (cs.map TypeScript.Decl.classDecl ++ ds.map TypeScript.Decl.const) =
      (cs, ds.map TypeScript.Decl.const) := by
  induction cs with
  | nil => cases ds <;> rfl
  | cons c cs ih => simp only [List.map_cons, List.cons_append, splitClasses, ih]

/-- A block of class declarations, then the rows' service constants, then constants, splits
after the classes. A step of `readModule_printModule` and `readModule_printModule_defs`. -/
theorem splitClasses_rowServices (cs : List TypeScript.ClassDecl)
    (serviceDecls ds : List TypeScript.ConstDecl) :
    splitClasses (cs.map TypeScript.Decl.classDecl ++ serviceDecls.map TypeScript.Decl.const ++
      ds.map TypeScript.Decl.const) =
      (cs, serviceDecls.map TypeScript.Decl.const ++ ds.map TypeScript.Decl.const) := by
  rw [List.append_assoc, ← List.map_append, splitClasses_append, List.map_append]

/-- Reading the declaration block produced by the module printer recovers the original
program, including shared-layer references, when its leading class declarations read back to
the module's payload classes (decisions row 120, part E2), the services of the rows that the
module declares follow them as `rowServiceDecls` prints them (decisions row 378 (19); none for
the envelope that a host wraps), each piece successful hoisting
produced reads back from its own printing under those classes (`ReadsBack`, which `readable`
gives), and the emitted reference names decode. The premises concern the pieces, never the
module read itself, and they are stated of any expression reader: this law is the hoisting
inverse composed with them. Placed at R8 (`translation-simulation`): the module face's round
trip, the class section included.

This is a structural AST equation: it does not validate the declaration's claimed
type, imports, rendered TypeScript bytes, or target execution. -/
theorem readModule_printModule {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {call param : Nat → Op}
    {root main : Eff Op} {history : List (List Nat × LayerTerm Op)}
    (hoisted : root.hoistAll = .ok (main, history))
    (plain : main.block? = none)
    {classDecls : List TypeScript.ClassDecl}
    (classesRead : Effect4.Codegen.Classes.readClassDecls classDecls = some classes)
    {rows : List Row} {serviceDecls : List TypeScript.ConstDecl}
    (servicesPrinted : rowServiceDecls sig rows = .ok serviceDecls)
    (mainReadable : ReadsBack classes sig spell 0 main)
    (layersReadable : ∀ entry ∈ history, entry.2.ReadsBack classes sig spell)
    (namesReadable : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {name : String} {ty : EffTy} {decls : List TypeScript.ConstDecl}
    (printed : printModule sig name ty root = .ok decls) :
    readModule sig spell call param rows
      (classDecls.map TypeScript.Decl.classDecl ++ serviceDecls.map TypeScript.Decl.const ++
        decls.map TypeScript.Decl.const) = .ok root := by
  have ordered := Eff.hoistAll_ordered hoisted
  have unique : (history.map Prod.fst).Nodup := ordered.imp (by
    intro a b before equal
    subst b
    simp only [Path.lt, Field.ltKey_irrefl, Bool.false_eq_true] at before)
  unfold printModule at printed
  rw [hoisted] at printed
  simp only [plain] at printed
  change ((Path.sortBy Path.declBefore (history.map Prod.fst)).mapM
    (printCaptured sig history) >>= fun ds => print sig 0 main >>= fun body =>
    printDecl name ty body sig.scopeKey >>= fun decl => .ok (ds ++ [decl])) = .ok decls at printed
  obtain ⟨ds, hp, hmain⟩ := bind_eq_ok.mp printed
  obtain ⟨body, hbody, hdecl⟩ := bind_eq_ok.mp hmain
  obtain ⟨decl, declaration, heq⟩ := bind_eq_ok.mp hdecl
  cases heq
  have value := printDecl_value declaration
  have hm := mainReadable _ hbody
  have hd := readCaptured_mapM layersReadable namesReadable _ hp
  have restored : main.restoreAll
      (selectHistory history (Path.sortBy Path.declBefore (history.map Prod.fst))) =
      some root := by
    have perm := selectHistory_ordered_perm history unique
    rw [Eff.restoreAll_perm main perm ((perm.map Prod.fst).symm.nodup unique)]
    exact Eff.restoreAll_hoistAll hoisted
  have leading := defsPrefix_layers namesReadable hp
  rw [readModule, blockClasses, splitClasses_rowServices, classesRead]
  simp only [readRowServices_rowServiceDecls servicesPrinted]
  simp only [List.map_append, List.map_cons, List.map_nil,
    List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, value, leading]
  change (readEff classes sig spell 0 body >>= fun e =>
    (ds.map TypeScript.Decl.const).mapM (readCaptured classes sig spell) >>= fun entries =>
    match e.restoreAll entries with
    | some out => .ok out
    | none => .error (.shape "module")) = .ok root
  simp only [hm, ok_bind, hd, restored]

/-- A property every successful element of a traversal carries, carried to the list. -/
private theorem mapM_ok_forall {α β ε : Type} (f : α → Except ε β) (P : β → Prop)
    (step : ∀ a d, f a = .ok d → P d) (l : List α) {ds : List β}
    (h : l.mapM f = .ok ds) : ∀ d ∈ ds, P d := by
  induction l generalizing ds with
  | nil =>
    cases h
    intro d mem
    cases mem
  | cons a rest ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, htail⟩ := bind_eq_ok.mp h
    obtain ⟨bs, hbs, heq⟩ := bind_eq_ok.mp htail
    cases heq
    intro d mem
    rcases List.mem_cons.mp mem with rfl | rest'
    · exact step a d hb
    · exact ih hbs d rest'

/-- Every emitted layer declaration is plain: no annotation, exported. -/
private theorem printCaptured_plain {sig : Signature Op} {history : History Op}
    (target : List Nat) (decl : TypeScript.ConstDecl)
    (printed : printCaptured sig history target = .ok decl) :
    decl.type = none ∧ decl.exported = true := by
  unfold printCaptured at printed
  split at printed
  · obtain ⟨_, _, heq⟩ := bind_eq_ok.mp printed
    cases heq
    exact ⟨rfl, rfl⟩
  · simp at printed

/-! ## A module with a definition block (decisions row 328, slice PROC-3) -/

/-- The declarations of a node's definition block: an `eff` node's own, none elsewhere. -/
def Node.defsOf : Node Op → List DefDecl
  | .eff e => e.defsOf
  | _ => []

/-- A child update keeps a block's declarations. A step of `Eff.hoistAll_defsOf`. -/
theorem Node.setChild_defsOf {node result replacement : Node Op} {index : Nat}
    (updated : node.setChild index replacement = some result) : result.defsOf = node.defsOf := by
  unfold Node.setChild at updated
  split at updated <;> cases updated <;> rfl

/-- Replacing a layer keeps a block's declarations. A step of `Eff.hoistAll_defsOf`. -/
theorem Node.replaceLayerAt_defsOf {node result : Node Op} {path : List Nat}
    {layer : LayerTerm Op} (updated : node.replaceLayerAt path layer = some result) :
    result.defsOf = node.defsOf := by
  cases path with
  | nil =>
    simp only [Node.replaceLayerAt, Node.replaceAt] at updated
    split at updated
    · rename_i same
      cases updated
      cases node with
      | eff e =>
        simp only [Node.ctorIdx] at same
        exact absurd same (by decide)
      | _ => rfl
    · cases updated
  | cons i rest =>
    simp only [Node.replaceLayerAt, Node.replaceAt] at updated
    obtain ⟨_, _, inner⟩ := Option.bind_eq_some_iff.mp updated
    obtain ⟨_, _, set⟩ := Option.bind_eq_some_iff.mp inner
    exact Node.setChild_defsOf set

private theorem hoistFold_defsOf (targets : List (List Nat)) (root : Eff Op)
    (history : List (List Nat × LayerTerm Op)) {final : Eff Op × List (List Nat × LayerTerm Op)}
    (h : targets.foldlM (init := (root, history))
        (fun (acc, decls) target =>
          match (Node.eff acc).layerAt target,
              (Node.eff acc).replaceLayerAt target (.ref target) with
          | some layer, some (Node.eff next) => .ok (next, (target, layer) :: decls)
          | _, _ => .error target) = (Except.ok final : Except (List Nat) _)) :
    final.1.defsOf = root.defsOf := by
  induction targets generalizing root history with
  | nil => cases h; rfl
  | cons target targets ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨step, hstep, rest⟩ := bind_eq_ok.mp h
    split at hstep
    · rename_i layer next _ replaced
      cases hstep
      exact (ih next _ rest).trans (Node.replaceLayerAt_defsOf replaced)
    · cases hstep

/-- **Hoisting keeps a block's declarations**: the hoisted program's block is the program's. A
step of the claim `module-defs-round-trip`: the printer's name check reads the program's
declarations, and the module printer prints the hoisted program's. Its consumer is
`ModuleEmission.readModule_defs`. -/
theorem Eff.hoistAll_defsOf {root main : Eff Op} {history : List (List Nat × LayerTerm Op)}
    (h : root.hoistAll = .ok (main, history)) : main.defsOf = root.defsOf :=
  hoistFold_defsOf _ root [] h



/-- A program whose root holds a block is that block. -/
theorem Eff.eq_of_block? {e : Eff Op} {defs : List DefDecl} {bodies : Effs Op} {body : Eff Op}
    {layers : LayerTerms Op} (h : e.block? = some (defs, bodies, body, layers)) :
    e = .defs defs bodies body layers := by
  cases e <;> simp only [Eff.block?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- A program's block holds the program's declarations. -/
theorem Eff.defsOf_of_block? {e : Eff Op} {defs : List DefDecl} {bodies : Effs Op}
    {body : Eff Op} {layers : LayerTerms Op} (h : e.block? = some (defs, bodies, body, layers)) :
    e.defsOf = defs := by
  rw [Eff.eq_of_block? h]
  rfl

/-- A program with no block has no declarations. -/
theorem Eff.defsOf_of_block?_none {e : Eff Op} (h : e.block? = none) : e.defsOf = [] := by
  cases e <;> simp only [Eff.block?, reduceCtorEq] at h <;> rfl

/-- A printed definition is a constant with no annotation, exported. A step of
`printModule_shape`. -/
theorem printDef_plain {sig : Signature Op} {d : DefDecl} {body : Eff Op}
    {locals : History Op} {c : TypeScript.ConstDecl}
    (printed : printDef sig d body locals = .ok c) :
    c.type = none ∧ c.exported = true ∧ c.name = d.name ∧ isServiceConst c = false := by
  unfold printDef at printed
  obtain ⟨_, _, rest⟩ := bind_eq_ok.mp printed
  obtain ⟨_, _, rest⟩ := bind_eq_ok.mp rest
  obtain ⟨_, _, rest⟩ := bind_eq_ok.mp rest
  obtain ⟨_, _, rest⟩ := bind_eq_ok.mp rest
  obtain ⟨_, _, heq⟩ := bind_eq_ok.mp rest
  cases heq
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every printed definition of a block is a plain constant. A step of `printModule_shape`. -/
theorem printDefs_plain {sig : Signature Op} {k : Nat} {defs : List DefDecl} {bodies : Effs Op}
    {rest : History Op} {out : List TypeScript.ConstDecl × History Op}
    (printed : printDefs sig k defs bodies rest = .ok out) :
    ∀ c ∈ out.1, c.type = none ∧ c.exported = true := by
  induction defs generalizing k bodies rest out with
  | nil =>
    cases bodies with
    | nil => cases printed; intro c mem; cases mem
    | cons _ _ => cases printed
  | cons d ds ih =>
    cases bodies with
    | nil => cases printed
    | cons b bs =>
      simp only [printDefs] at printed
      obtain ⟨c, hc, tail⟩ := bind_eq_ok.mp printed
      obtain ⟨out', hout, heq⟩ := bind_eq_ok.mp tail
      cases heq
      intro c' mem
      rcases List.mem_cons.mp mem with rfl | rest'
      · exact ⟨(printDef_plain hc).1, (printDef_plain hc).2.1⟩
      · exact ih hout c' rest'

/-- An empty requirement row prints as `never`. -/
theorem requirementType_nil (scopeKey : ServiceKey) :
    requirementType scopeKey (Effect4.Machine.Env.Requirement.ofList []) = .name ["never"] [] :=
  rfl

/-! ## The module's layers (decisions row 341, step 2)

The printer writes a block's module layers as constants named by their paths
(`printModuleLayers`), after the services and before the hoisted layers. The reader takes the
declarations whose paths stand in the module back as the block's layers child (`moduleLayersOf`)
and puts the others back at their paths. Each fact is a step of `readModule_printModule_defs`. -/

/-- A spine of layers is the spine of its list. -/
theorem LayerTerms.ofList_toList : ∀ (ls : LayerTerms Op), LayerTerms.ofList ls.toList = ls
  | .nil => rfl
  | .cons h t => by rw [LayerTerms.toList, LayerTerms.ofList, LayerTerms.ofList_toList t]

/-- A printed module layer: the layer's print, under the name of its path. -/
theorem printModuleLayer_spec {sig : Signature Op} {p : LayerTerm Op × Nat}
    {c : TypeScript.ConstDecl} (printed : printModuleLayers.printModuleLayer sig p = .ok c) :
    ∃ x, printLayer sig p.1 = .ok x ∧
      c = { doc := [], name := LayerTerm.refName (Path.layerPath p.2), value := x } := by
  unfold printModuleLayers.printModuleLayer at printed
  obtain ⟨x, hx, heq⟩ := bind_eq_ok.mp printed
  cases heq
  exact ⟨x, hx, rfl⟩

/-- A layer declaration whose name carries its path reads back to the path and the layer. -/
private theorem readLayerDecl_const {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {c : TypeScript.ConstDecl} {t : List Nat} {l : LayerTerm Op}
    (named : LayerTerm.readRefName c.name = some t) (same : LayerTerm.refName t = c.name)
    (read : readLayer classes sig spell c.value = .ok l) :
    readLayerDecl classes sig spell (.const c) = .ok (t, l) := by
  simp only [readLayerDecl, named, if_pos same, read, ok_bind]

/-- The printed module layers read back, each at its path, when each layer reads back from its
printing and each path's name decodes. -/
private theorem readModuleLayers_mapM {sig : Signature Op}
    {spell : String → List RowArg → Option Op} :
    ∀ {ps : List (LayerTerm Op × Nat)} {ms : List TypeScript.ConstDecl},
      (∀ p ∈ ps, p.1.ReadsBack classes sig spell ∧
        LayerTerm.readRefName (LayerTerm.refName (Path.layerPath p.2)) =
          some (Path.layerPath p.2)) →
      ps.mapM (printModuleLayers.printModuleLayer sig) = .ok ms →
      (ms.map TypeScript.Decl.const).mapM (readLayerDecl classes sig spell) =
        .ok (ps.map fun p => (Path.layerPath p.2, p.1))
  | [], _, _, printed => by cases printed; rfl
  | p :: ps, _, hp, printed => by
    simp only [List.mapM_cons] at printed
    obtain ⟨c, hc, tail⟩ := bind_eq_ok.mp printed
    obtain ⟨cs, hcs, heq⟩ := bind_eq_ok.mp tail
    cases heq
    obtain ⟨x, hx, rfl⟩ := printModuleLayer_spec hc
    obtain ⟨hread, named⟩ := hp p List.mem_cons_self
    have ih := readModuleLayers_mapM (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hcs
    have hd := readLayerDecl_const (classes := classes) (spell := spell)
      (c := { doc := [], name := LayerTerm.refName (Path.layerPath p.2), value := x }) named rfl
      (hread x hx)
    simp only [List.map_cons, List.mapM_cons, hd, ih]
    rfl

/-- The definition and service prefixes stop at the first printed module layer, whose name
carries its path; with no module layer, at what follows. -/
private theorem prefixes_moduleLayers {sig : Signature Op} :
    ∀ {ps : List (LayerTerm Op × Nat)} {ms : List TypeScript.ConstDecl} {rest : List TypeScript.Decl},
      (∀ p ∈ ps, LayerTerm.readRefName (LayerTerm.refName (Path.layerPath p.2)) =
        some (Path.layerPath p.2)) →
      ps.mapM (printModuleLayers.printModuleLayer sig) = .ok ms →
      defsPrefix rest = ([], rest) → servicePrefix rest = ([], rest) →
      defsPrefix (ms.map TypeScript.Decl.const ++ rest) = ([], ms.map TypeScript.Decl.const ++ rest) ∧
        servicePrefix (ms.map TypeScript.Decl.const ++ rest) =
          ([], ms.map TypeScript.Decl.const ++ rest)
  | [], _, _, _, printed, hd, hs => by
    cases printed
    exact ⟨hd, hs⟩
  | p :: _, _, _, names, printed, _, _ => by
    simp only [List.mapM_cons] at printed
    obtain ⟨c, hc, tail⟩ := bind_eq_ok.mp printed
    obtain ⟨cs, _, heq⟩ := bind_eq_ok.mp tail
    cases heq
    obtain ⟨x, -, rfl⟩ := printModuleLayer_spec hc
    have named := names p List.mem_cons_self
    simp only [List.map_cons, List.cons_append, defsPrefix, servicePrefix, named, and_self]

/-- A path of the module's layers stands in the module. -/
private theorem inModulePath_layerPath (k : Nat) : inModulePath (Path.layerPath k) = true := rfl

/-- **The reader's split** of a block's layer declarations: the module layers, at their paths in
order, then the hoisted ones, none of which stands in the module. -/
private theorem moduleLayersOf_split (layers : LayerTerms Op)
    (hs : List (List Nat × LayerTerm Op)) (outside : ∀ e ∈ hs, inModulePath e.1 = false) :
    moduleLayersOf ((layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1)) ++ hs) =
        some layers ∧
      ((layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1)) ++ hs).filter
        (fun d => !inModulePath d.1) = hs := by
  have keepMods : (layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1)).filter
      (fun d => inModulePath d.1) = layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1) :=
    List.filter_eq_self.mpr fun d hd => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hd
      exact inModulePath_layerPath p.2
  have dropHist : hs.filter (fun d => inModulePath d.1) = [] := by
    match h : hs.filter (fun d => inModulePath d.1) with
    | [] => exact h
    | e :: _ =>
      have he : e ∈ hs.filter (fun d => inModulePath d.1) := by
        rw [h]
        exact List.mem_cons_self
      obtain ⟨member, kept⟩ := List.mem_filter.mp he
      rw [outside e member] at kept
      exact absurd kept Bool.false_ne_true
  have dropMods : (layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1)).filter
      (fun d => !inModulePath d.1) = [] := by
    match h :
        (layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1)).filter
          (fun d => !inModulePath d.1) with
    | [] => exact h
    | e :: _ =>
      have he : e ∈
          (layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1)).filter
            (fun d => !inModulePath d.1) := by
        rw [h]
        exact List.mem_cons_self
      obtain ⟨member, kept⟩ := List.mem_filter.mp he
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp member
      simp only [inModulePath_layerPath, Bool.not_true] at kept
      exact absurd kept Bool.false_ne_true
  have keepHist : hs.filter (fun d => !inModulePath d.1) = hs :=
    List.filter_eq_self.mpr fun d hd => by rw [outside d hd]; rfl
  refine ⟨?_, by rw [List.filter_append, dropMods, keepHist, List.nil_append]⟩
  unfold moduleLayersOf
  simp only [List.filter_append, keepMods, dropHist, List.append_nil, List.map_map,
    List.length_map, List.length_zipIdx]
  have names : List.map (Prod.fst ∘ fun p : LayerTerm Op × Nat => (Path.layerPath p.2, p.1))
      layers.toList.zipIdx = (List.range layers.toList.length).map Path.layerPath := by
    rw [show (Prod.fst ∘ fun p : LayerTerm Op × Nat => (Path.layerPath p.2, p.1)) =
      Path.layerPath ∘ Prod.snd from rfl, ← List.map_map, List.zipIdx_map_snd, List.range_eq_range']
  have terms : List.map (Prod.snd ∘ fun p : LayerTerm Op × Nat => (Path.layerPath p.2, p.1))
      layers.toList.zipIdx = layers.toList := by
    rw [show (Prod.snd ∘ fun p : LayerTerm Op × Nat => (Path.layerPath p.2, p.1)) = Prod.fst
      from rfl, List.zipIdx_map_fst]
  rw [names, terms, if_pos rfl, LayerTerms.ofList_toList]

/-- The shape of a successful declaration block, read off the printer itself: the layer
declarations first, each plain and exported, then the one main declaration the declaration
printer produced. The reading boundary compares a block against exactly this shape. -/
theorem printModule_shape {sig : Signature Op} {name : String} {ty : EffTy} {root : Eff Op}
    {block : List TypeScript.ConstDecl} (printed : printModule sig name ty root = .ok block) :
    ∃ layers main body, block = layers ++ [main] ∧
      (∀ decl ∈ layers, decl.type = none ∧ decl.exported = true) ∧
      printDecl name ty body sig.scopeKey = .ok main := by
  unfold printModule at printed
  cases hoisted : root.hoistAll with
  | error target => rw [hoisted] at printed; simp only [reduceCtorEq] at printed
  | ok pair =>
    obtain ⟨main, history⟩ := pair
    rw [hoisted] at printed
    cases hb : main.block? with
    | none =>
      simp only [hb] at printed
      change ((Path.sortBy Path.declBefore (history.map Prod.fst)).mapM
        (printCaptured sig history) >>= fun ds => print sig 0 main >>= fun body =>
        printDecl name ty body sig.scopeKey >>= fun decl => .ok (ds ++ [decl])) = .ok block at printed
      obtain ⟨ds, hp, hmain⟩ := bind_eq_ok.mp printed
      obtain ⟨body, _, hdecl⟩ := bind_eq_ok.mp hmain
      obtain ⟨decl, declaration, heq⟩ := bind_eq_ok.mp hdecl
      cases heq
      exact ⟨ds, decl, body, rfl,
        mapM_ok_forall _ _ (fun t d hd => printCaptured_plain t d hd) _ hp, declaration⟩
    | some quad =>
      obtain ⟨defs, bodies, body, mlayers⟩ := quad
      cases defs with
      | nil => simp only [hb, reduceCtorEq] at printed
      | cons d ds =>
        simp only [hb] at printed
        cases hscope : (root.refSites []).find? fun x => !root.inScope x.1 x.2 with
        | some x => simp only [hscope, reduceCtorEq] at printed
        | none =>
        simp only [hscope] at printed
        change (printDefs (sig.withDefs (d :: ds)) 0 (d :: ds) bodies history >>= fun out =>
          printServices (sig.withDefs (d :: ds)) (d :: ds) >>= fun svc =>
          printModuleLayers (sig.withDefs (d :: ds)) mlayers >>= fun ms =>
          (Path.sortBy Path.declBefore (out.2.map Prod.fst)).mapM
            (printCaptured (sig.withDefs (d :: ds)) out.2) >>= fun ls =>
          print (sig.withDefs (d :: ds)) 0 body >>= fun m =>
          printDecl name ty m sig.scopeKey >>= fun decl =>
            .ok (out.1 ++ svc ++ ms ++ ls ++ [decl])) = .ok block at printed
        obtain ⟨out, hout, rest⟩ := bind_eq_ok.mp printed
        obtain ⟨svc, hsvc, rest⟩ := bind_eq_ok.mp rest
        obtain ⟨ms, hms, rest⟩ := bind_eq_ok.mp rest
        obtain ⟨ls, hls, rest⟩ := bind_eq_ok.mp rest
        obtain ⟨m, _, rest⟩ := bind_eq_ok.mp rest
        obtain ⟨decl, declaration, heq⟩ := bind_eq_ok.mp rest
        cases heq
        refine ⟨out.1 ++ svc ++ ms ++ ls, decl, m, by simp only [List.append_assoc], ?_,
          declaration⟩
        intro c mem
        rcases List.mem_append.mp mem with hc | hl
        · rcases List.mem_append.mp hc with hc | hm
          · rcases List.mem_append.mp hc with hc | hs
            · exact printDefs_plain hout c hc
            · obtain ⟨-, hplain, -⟩ := printServices_ok hsvc
              exact ⟨(hplain c hs).1, (hplain c hs).2.1⟩
          · exact mapM_ok_forall _ (fun c : TypeScript.ConstDecl => c.type = none ∧ c.exported = true)
              (fun p d hd => by
                obtain ⟨_, -, rfl⟩ := printModuleLayer_spec hd
                exact ⟨rfl, rfl⟩) _ hms c hm
        · exact mapM_ok_forall _ _ (fun t d hd => printCaptured_plain t d hd) _ hls c hl

/-- **A parameter's binder reads back** (slice HO-3): the binders `printDef` prints of
parameters readable under the module's classes read as the parameters under them. A step of
`readDefHead_printDef`. -/
theorem readParams_printParams {sig : Signature Op} :
    ∀ {ps : List ParamDecl} {fns : List TypeScript.TypeRef}, (∀ q ∈ ps, q.readable classes = true) →
      ps.mapM (paramType sig) = .ok fns →
      ((ps.zip fns).map fun p =>
        ({ name := p.1.name, type := some p.2 } : TypeScript.Parameter)).mapM
          (readParam classes) = .ok ps
  | [], fns, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | q :: qs, fns, readable, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨t, ht, rest⟩ := bind_eq_ok.mp h
    obtain ⟨ts, hts, heq⟩ := bind_eq_ok.mp rest
    cases heq
    have hq := readable q List.mem_cons_self
    simp only [ParamDecl.readable, Bool.and_eq_true] at hq
    obtain ⟨⟨hreq, hans⟩, herr⟩ := hq
    obtain ⟨reqT, hreqT⟩ := Effect4.Codegen.Classes.ofTy_of_readable hreq
    obtain ⟨ansT, hansT⟩ := Effect4.Codegen.Classes.ofTy_of_readable hans
    obtain ⟨errT, herrT⟩ := Effect4.Codegen.Classes.ofTy_of_readable herr
    simp only [paramType, typeRefOf, hreqT, declarationType, hansT, herrT, bind, Except.bind,
      Except.ok.injEq] at ht
    subst ht
    have tail := readParams_printParams (fun q' h' => readable q' (List.mem_cons_of_mem _ h')) hts
    obtain ⟨name, request, answer, error⟩ := q
    simp only [List.zip_cons_cons, List.map_cons, List.mapM_cons, tail, readParam,
      requirementType_nil, ↓reduceIte,
      Effect4.Codegen.Classes.readTyChecked_of_readable hreq hreqT,
      Effect4.Codegen.Classes.readTyChecked_of_readable hans hansT,
      Effect4.Codegen.Classes.readTyChecked_of_readable herr herrT, ok_bind]
    rfl

/-- **A definition's header reads back**: the constant `printDef` prints of a declaration
readable under the module's classes reads as that declaration under them, its requirement row
and its parameters included (slice HO-3), and the printed suspension of its body (`suspension`):
the constants of the body's own layers and the body, printed at the signature its parameters
extend (decisions row 341, step 3). A column that names a payload class reads as the class's
record (decisions row 120), and the requirement row reads back by `readKeys_requirementType`.
Placement: concept `exact-codecs`, a step of the claim `module-defs-round-trip` (R8) through
`readModule_printModule_defs`, its consumer. It states nothing of target typing. -/
theorem readDefHead_printDef {sig : Signature Op} {d : DefDecl} {body : Eff Op}
    {locals : History Op} {c : TypeScript.ConstDecl} (readable : d.readable classes = true)
    (printed : printDef sig d body locals = .ok c) :
    ∃ ls y, (Path.sortBy Path.declBefore (locals.map Prod.fst)).mapM
        (printLocal (sig.withParams d.params) locals) = .ok ls ∧
      print (sig.withParams d.params) 1 body = .ok y ∧
      readDefHead sig classes c = .ok ({ d with role := .plain }, suspension ls y) := by
  simp only [DefDecl.readable, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
    List.all_eq_true] at readable
  obtain ⟨⟨⟨⟨⟨hreq, hans⟩, herr⟩, hrequires⟩, _⟩, hparams⟩ := readable
  unfold printDef at printed
  obtain ⟨request, hrequest, rest⟩ := bind_eq_ok.mp printed
  obtain ⟨fns, hfns, rest⟩ := bind_eq_ok.mp rest
  obtain ⟨result, hresult, rest⟩ := bind_eq_ok.mp rest
  obtain ⟨ls, hls, rest⟩ := bind_eq_ok.mp rest
  obtain ⟨y, hy, heq⟩ := bind_eq_ok.mp rest
  cases heq
  obtain ⟨reqT, hreqT⟩ := Effect4.Codegen.Classes.ofTy_of_readable hreq
  obtain ⟨ansT, hansT⟩ := Effect4.Codegen.Classes.ofTy_of_readable hans
  obtain ⟨errT, herrT⟩ := Effect4.Codegen.Classes.ofTy_of_readable herr
  simp only [typeRefOf, hreqT, Except.ok.injEq] at hrequest
  subst hrequest
  simp only [declarationType, DefDecl.effTy, hansT, herrT, bind, Except.bind,
    Except.ok.injEq] at hresult
  subst hresult
  have hps := readParams_printParams hparams hfns
  refine ⟨ls, y, hls, hy, ?_⟩
  obtain ⟨name, request, answer, error, requires, role, params⟩ := d
  simp only at hrequires hps
  simp only [readDefHead, ↓reduceIte, hps, ok_bind, readKeys_requirementType, hrequires,
    Effect4.Codegen.Classes.readTyChecked_of_readable hreq hreqT,
    Effect4.Codegen.Classes.readTyChecked_of_readable hans hansT,
    Effect4.Codegen.Classes.readTyChecked_of_readable herr herrT]

/-- A header reads alike at a block's signature and at the signature the block extends: the
header reader reads the signature's scope key alone, and the block keeps it. A step of
`readModule_printModule_defs`, whose printer prints the headers at the block's signature and
whose reader reads them before the block is known. -/
theorem readDefHead_withDefs (sig : Signature Op) (defs : List DefDecl) :
    readDefHead (sig.withDefs defs) classes = readDefHead sig classes :=
  rfl

/-! ## A body's own layers (decisions row 341, step 3)

The printer writes a body's hoisted layers as constants at the top of its suspension
(`printDefs`, `printLocal`, `suspension`), and the reader takes them back from there
(`readDefBody`, `readLocal`). Each fact is a step of `readModule_printModule_defs`. -/

/-- The declaration of the definition whose body holds a path of a block, when one does
(`Path.bodyIndex`): a body's own layer prints and reads at the signature that the body's
parameters extend, and any other hoisted layer at the block's. -/
def bodyDeclOf (defs : List DefDecl) (t : List Nat) : Option DefDecl :=
  (Path.bodyIndex t).bind fun i => defs[i]?

/-- The definition that holds a body's layer is one of the block's. -/
theorem bodyDeclOf_mem {defs : List DefDecl} {t : List Nat} {d : DefDecl}
    (h : bodyDeclOf defs t = some d) : d ∈ defs := by
  unfold bodyDeclOf at h
  obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.mp h
  exact List.mem_of_getElem? hi

/-- A path that stands in no body of the block's definitions has no declaration. -/
theorem bodyDeclOf_none {defs : List DefDecl} {t : List Nat}
    (h : ∀ i, i < defs.length → Path.bodyIndex t ≠ some i) : bodyDeclOf defs t = none := by
  unfold bodyDeclOf
  cases hb : Path.bodyIndex t with
  | none => rfl
  | some i =>
    show defs[i]? = none
    apply List.getElem?_eq_none
    cases Nat.lt_or_ge i defs.length with
    | inl hlt => exact absurd hb (h i hlt)
    | inr hge => exact hge

/-- A printed constant of a body's suspension reads back to the hoisted layer it was printed
from, when the layer reads back from its printing and its name decodes. -/
private theorem readLocal_printLocal {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {locals : History Op}
    (layers : ∀ entry ∈ locals, entry.2.ReadsBack classes sig spell)
    (names : ∀ entry ∈ locals,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {target : List Nat} {entry : List Nat × LayerTerm Op} {s : TypeScript.Stmt}
    (found : locals.find? (·.1 == target) = some entry)
    (printed : printLocal sig locals target = .ok s) :
    readLocal classes sig spell s = .ok entry := by
  have mem := List.mem_of_find?_eq_some found
  have key : entry.1 = target := by
    simpa only [beq_iff_eq] using List.find?_some found
  simp only [printLocal, found] at printed
  obtain ⟨x, hp, heq⟩ := bind_eq_ok.mp printed
  cases heq
  have hr := layers entry mem _ hp
  rw [← key]
  simp only [readLocal, names entry mem, ↓reduceIte, hr, ok_bind]

/-- The constants of a body's suspension read back, in their order, to the hoisted layers named
by the printed paths. -/
private theorem readLocals_mapM {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {locals : History Op}
    (layers : ∀ entry ∈ locals, entry.2.ReadsBack classes sig spell)
    (names : ∀ entry ∈ locals,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    (targets : List (List Nat)) {ls : List TypeScript.Stmt}
    (printed : targets.mapM (printLocal sig locals) = .ok ls) :
    ls.mapM (readLocal classes sig spell) = .ok (selectHistory locals targets) := by
  induction targets generalizing ls with
  | nil => cases printed; rfl
  | cons target targets ih =>
    simp only [List.mapM_cons] at printed
    obtain ⟨s, hs, htail⟩ := bind_eq_ok.mp printed
    obtain ⟨rest, hrest, heq⟩ := bind_eq_ok.mp htail
    cases heq
    cases found : locals.find? (·.1 == target) with
    | none => simp only [printLocal, found, reduceCtorEq] at hs
    | some entry =>
      have hr := readLocal_printLocal layers names found hs
      simp only [List.mapM_cons, hr, ih hrest, ok_bind, selectHistory, List.filterMap_cons,
        found]
      rfl

/-- **A body's suspension reads back**: the body, and its own layers in declaration order, when
each layer and the body read back from their printing and the layers' names decode. -/
private theorem readDefBody_suspension {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {locals : History Op} {body : Eff Op} {ls : List TypeScript.Stmt} {y : TypeScript.Expr}
    (layers : ∀ entry ∈ locals, entry.2.ReadsBack classes sig spell)
    (names : ∀ entry ∈ locals,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    (bodyReads : ReadsBack classes sig spell 1 body)
    (hls : (Path.sortBy Path.declBefore (locals.map Prod.fst)).mapM (printLocal sig locals) =
      .ok ls)
    (hy : print sig 1 body = .ok y) :
    readDefBody classes sig spell (suspension ls y) =
      .ok (body, selectHistory locals (Path.sortBy Path.declBefore (locals.map Prod.fst))) := by
  have hread := readLocals_mapM layers names _ hls
  have hb := bodyReads y hy
  cases ls with
  | nil =>
    have empty : selectHistory locals (Path.sortBy Path.declBefore (locals.map Prod.fst)) = [] := by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hread
      exact hread.symm
    rw [empty]
    show (readEff classes sig spell 1 y >>= fun b => .ok (b, [])) = _
    rw [hb]
    rfl
  | cons s ss =>
    simp only [suspension, readDefBody, List.getLast?_concat, List.dropLast_concat, hread, hb,
      ok_bind]

/-- **A block's definitions read back**: the constants `printDefs` prints of readable declarations,
from position `k` of the block's declarations `all`, read as the declarations; their bodies read
back where each body does; and the layers the bodies took into their suspensions read back, so
that with the layers no body took they are the hoisted layers given, up to order. No layer left
stands in a body of these definitions. A step of `readModule_printModule_defs`. -/
theorem readDefs_printDefs {classes : Classes} {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {param : Nat → Op} {all : List DefDecl}
    {k : Nat} {defs : List DefDecl} {bodies : Effs Op} {rest : History Op}
    {out : List TypeScript.ConstDecl × History Op}
    (index : ∀ i, all[k + i]? = defs[i]?)
    (readable : ∀ d ∈ defs, d.readable classes = true)
    (bodiesRead : ∀ p ∈ defs.zip bodies.toList, ReadsBack classes (sig.withParams p.1.params)
      (paramsSpell param p.1.params spell) 1 p.2)
    (localsRead : ∀ e ∈ rest, ∀ d, bodyDeclOf all e.1 = some d →
      e.2.ReadsBack classes (sig.withParams d.params) (paramsSpell param d.params spell))
    (names : ∀ e ∈ rest, LayerTerm.readRefName (LayerTerm.refName e.1) = some e.1)
    (unique : (rest.map Prod.fst).Nodup)
    (printed : printDefs sig k defs bodies rest = .ok out) :
    ∃ heads locals, out.1.mapM (readDefHead sig classes) = .ok heads ∧
      heads.map (·.1) = defs.map (fun d => { d with role := .plain }) ∧
      readDefBodies classes sig spell param heads = .ok (bodies, locals) ∧
      (locals ++ out.2).Perm rest ∧
      (∀ e ∈ out.2, ∀ i, i < defs.length → Path.bodyIndex e.1 ≠ some (k + i)) ∧
      (∀ c ∈ out.1, LayerTerm.readRefName c.name = none) ∧
      ∀ c ∈ out.1, isServiceConst c = false := by
  induction defs generalizing k bodies rest out with
  | nil =>
    cases bodies with
    | nil =>
      cases printed
      exact ⟨[], [], rfl, rfl, rfl, List.Perm.refl rest,
        (fun _ _ i hi => absurd hi (Nat.not_lt_zero i)), (fun _ mem => nomatch mem),
        (fun _ mem => nomatch mem)⟩
    | cons _ _ => cases printed
  | cons d ds ih =>
    cases bodies with
    | nil => cases printed
    | cons b bs =>
      simp only [printDefs] at printed
      obtain ⟨c, hc, tail⟩ := bind_eq_ok.mp printed
      obtain ⟨out', hout, heq⟩ := bind_eq_ok.mp tail
      cases heq
      have hd := readable d List.mem_cons_self
      obtain ⟨ls, y, hls, hy, hhead⟩ := readDefHead_printDef hd hc
      -- the layers that body `k` takes: in its body, so read at its signature
      have here : all[k]? = some d := by
        simpa only [Nat.add_zero, List.getElem?_cons_zero] using index 0
      have mine : ∀ e ∈ rest.filter (fun e => decide (Path.bodyIndex e.1 = some k)),
          e ∈ rest ∧ Path.bodyIndex e.1 = some k := fun e he => by
        obtain ⟨hmem, hdec⟩ := List.mem_filter.mp he
        exact ⟨hmem, of_decide_eq_true hdec⟩
      have mineRead : ∀ e ∈ rest.filter (fun e => decide (Path.bodyIndex e.1 = some k)),
          e.2.ReadsBack classes (sig.withParams d.params) (paramsSpell param d.params spell) :=
        fun e he => localsRead e (mine e he).1 d (by
          unfold bodyDeclOf
          rw [(mine e he).2]
          exact here)
      have mineUnique :
          ((rest.filter (fun e => decide (Path.bodyIndex e.1 = some k))).map Prod.fst).Nodup :=
        (List.filter_sublist.map Prod.fst).nodup unique
      have hb := readDefBody_suspension mineRead (fun e he => names e (mine e he).1)
        (bodiesRead (d, b) (by simp only [Effs.toList, List.zip_cons_cons, List.mem_cons,
          true_or])) hls hy
      -- the layers passed on
      have others : ∀ e ∈ rest.filter (fun e => !decide (Path.bodyIndex e.1 = some k)),
          e ∈ rest := fun e he => (List.mem_filter.mp he).1
      obtain ⟨heads, locals, hheads, hdefs, hbodies, hperm, hleft, hnames, hnot⟩ :=
        ih (k := k + 1) (bodies := bs) (fun i => by
            have h := index (i + 1)
            rw [List.getElem?_cons_succ] at h
            rw [Nat.add_right_comm, Nat.add_assoc]
            exact h)
          (fun d' h => readable d' (List.mem_cons_of_mem _ h))
          (fun p h => bodiesRead p (by simp only [Effs.toList, List.zip_cons_cons, List.mem_cons,
            h, or_true]))
          (fun e he => localsRead e (others e he)) (fun e he => names e (others e he))
          ((List.filter_sublist.map Prod.fst).nodup unique) hout
      refine ⟨({ d with role := .plain }, suspension ls y) :: heads,
        selectHistory (rest.filter fun e => decide (Path.bodyIndex e.1 = some k))
          (Path.sortBy Path.declBefore
            ((rest.filter fun e => decide (Path.bodyIndex e.1 = some k)).map Prod.fst)) ++ locals,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.mapM_cons, hhead, hheads, ok_bind]
        rfl
      · simp only [List.map_cons, hdefs]
      · simp only [readDefBodies, hb, hbodies, ok_bind]
      · rw [List.append_assoc]
        exact ((selectHistory_ordered_perm _ mineUnique).append hperm).trans
          (List.filter_append_perm _ rest)
      · intro e he i hi
        cases i with
        | zero =>
          have hdec := (List.mem_filter.mp (hperm.subset (List.mem_append_right _ he))).2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hdec
          rw [Nat.add_zero]
          exact hdec
        | succ i =>
          have h := hleft e he i (Nat.lt_of_succ_lt_succ hi)
          rw [Nat.add_right_comm, Nat.add_assoc] at h
          exact h
      · intro c' mem
        rcases List.mem_cons.mp mem with rfl | rest'
        · simp only [DefDecl.readable, Bool.and_eq_true, Option.isNone_iff_eq_none] at hd
          rw [(printDef_plain hc).2.2.1]
          exact hd.1.2
        · exact hnames c' rest'
      · intro c' mem
        rcases List.mem_cons.mp mem with rfl | rest'
        · exact (printDef_plain hc).2.2.2
        · exact hnot c' rest'

/-- A block's root reads the module test off a path's head. A step of
`readModule_printModule_defs`. -/
private theorem inModule_of_defsOf {root : Eff Op} (h : root.defsOf ≠ []) (p : List Nat) :
    root.inModule p = inModulePath p := by
  cases root with
  | defs _ _ _ _ => rfl
  | _ => exact absurd rfl h

/-- **G6: the round trip of a module with a definition block** (decisions rows 328 and 341). The
module printer prints a block's definitions as constants, each body's own hoisted layers as
constants at the top of its suspension (decisions row 341, step 3), then the block's services'
keys and layers (decisions rows 338 and 339), then its module layers, each named by its path
(step 2), before the hoisted layers no body took and the main declaration (`printModule`). When
each declaration is readable under the module's classes (`DefDecl.readable`: readable columns, a
canonical requirement row, a name with no layer path); each body and each of its own layers read
back from their printing at
the signature its parameters extend (`bodyDeclOf`); the main program, each module layer and each
other hoisted layer read back at the block's signature through the block's spelling map
(`defsSpell`); and the layers' names decode, the module reads back to the program, after its
payload classes and the services of the rows it declares (`rowServiceDecls`), with each
definition's role given back by the services' layers (`roleOf`, `restoreRoles`) and the module's
layers by their paths (`moduleLayersOf`). No hoisted layer stands in the module
(`Eff.hoistAll_outside`). The premises concern the pieces, as `readModule_printModule`'s do, and
they are stated of any reader.

Restated for step 3: each body reads back itself (it was its suspension), and the hoisted layers'
premise is split by the scope that prints them (`localsReadable`, `layersReadable`).

Placement: concept `exact-codecs`, claim `module-defs-round-trip`, requirement R8. Consumers: the
module round trip of the readable domain (`readModule_printModule_readable`) and, through it,
`ModuleEmission.readModule`. It is a structural equation: it does not say that tsgo accepts the
module or how rc.112 runs it. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readModule_printModule_defs {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {call param : Nat → Op}
    {root main body : Eff Op} {defs : List DefDecl} {bodies : Effs Op} {layers : LayerTerms Op}
    {history : List (List Nat × LayerTerm Op)}
    (hoisted : root.hoistAll = .ok (main, history))
    (block : main.block? = some (defs, bodies, body, layers))
    {classDecls : List TypeScript.ClassDecl}
    (classesRead : Effect4.Codegen.Classes.readClassDecls classDecls = some classes)
    {rows : List Row} {serviceDecls : List TypeScript.ConstDecl}
    (servicesPrinted : rowServiceDecls sig rows = .ok serviceDecls)
    (headsReadable : ∀ d ∈ defs, d.readable classes = true)
    (bodiesReadable : ∀ p ∈ defs.zip bodies.toList,
      ReadsBack classes ((sig.withDefs defs).withParams p.1.params)
        (paramsSpell param p.1.params (defsSpell call defs spell)) 1 p.2)
    (mainReadable : ReadsBack classes (sig.withDefs defs) (defsSpell call defs spell) 0 body)
    (moduleReadable : ∀ l ∈ layers.toList,
      l.ReadsBack classes (sig.withDefs defs) (defsSpell call defs spell))
    (moduleNames : ∀ k < layers.toList.length,
      LayerTerm.readRefName (LayerTerm.refName (Path.layerPath k)) = some (Path.layerPath k))
    (localsReadable : ∀ entry ∈ history, ∀ d, bodyDeclOf defs entry.1 = some d →
      entry.2.ReadsBack classes ((sig.withDefs defs).withParams d.params)
        (paramsSpell param d.params (defsSpell call defs spell)))
    (layersReadable : ∀ entry ∈ history, bodyDeclOf defs entry.1 = none →
      entry.2.ReadsBack classes (sig.withDefs defs) (defsSpell call defs spell))
    (namesReadable : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {name : String} {ty : EffTy} {decls : List TypeScript.ConstDecl}
    (printed : printModule sig name ty root = .ok decls) :
    readModule sig spell call param rows
      (classDecls.map TypeScript.Decl.classDecl ++ serviceDecls.map TypeScript.Decl.const ++
        decls.map TypeScript.Decl.const) = .ok root := by
  have ordered := Eff.hoistAll_ordered hoisted
  have unique : (history.map Prod.fst).Nodup := ordered.imp (by
    intro a b before equal
    subst b
    simp only [Path.lt, Field.ltKey_irrefl, Bool.false_eq_true] at before)
  have shape := Eff.eq_of_block? block
  have rootDefs : root.defsOf = defs := by
    rw [← Eff.hoistAll_defsOf hoisted, Eff.defsOf_of_block? block]
  unfold printModule at printed
  rw [hoisted] at printed
  cases defs with
  | nil => simp only [block, reduceCtorEq] at printed
  | cons d ds =>
    simp only [block] at printed
    cases hscope : (root.refSites []).find? fun x => !root.inScope x.1 x.2 with
    | some x => simp only [hscope, reduceCtorEq] at printed
    | none =>
    simp only [hscope] at printed
    change (printDefs (sig.withDefs (d :: ds)) 0 (d :: ds) bodies history >>= fun out =>
      printServices (sig.withDefs (d :: ds)) (d :: ds) >>= fun svc =>
      printModuleLayers (sig.withDefs (d :: ds)) layers >>= fun ms =>
      (Path.sortBy Path.declBefore (out.2.map Prod.fst)).mapM
        (printCaptured (sig.withDefs (d :: ds)) out.2) >>= fun ls =>
      print (sig.withDefs (d :: ds)) 0 body >>= fun m =>
      printDecl name ty m sig.scopeKey >>= fun decl =>
        .ok (out.1 ++ svc ++ ms ++ ls ++ [decl])) = .ok decls at printed
    obtain ⟨out, hout, rest⟩ := bind_eq_ok.mp printed
    obtain ⟨svc, hsvc, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨ms, hms, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨ls, hls, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨m, hm, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨decl, declaration, heq⟩ := bind_eq_ok.mp rest
    cases heq
    have value := printDecl_value declaration
    obtain ⟨heads, locals, hheads, hdefs, hbodies, hperm, hleft, hnames, hnot⟩ :=
      readDefs_printDefs (all := d :: ds) (k := 0) (fun i => by rw [Nat.zero_add])
        headsReadable bodiesReadable localsReadable namesReadable unique hout
    rw [readDefHead_withDefs] at hheads
    -- the layers no body took: hoisted layers in no body, read at the block's signature
    have leftMem : ∀ e ∈ out.2, e ∈ history := fun e he =>
      hperm.subset (List.mem_append_right _ he)
    have leftOutside : ∀ e ∈ out.2, bodyDeclOf (d :: ds) e.1 = none := fun e he =>
      bodyDeclOf_none fun i hi => by
        have h := hleft e he i hi
        rw [Nat.zero_add] at h
        exact h
    have leftUnique : (out.2.map Prod.fst).Nodup := by
      have h := (hperm.map Prod.fst).symm.nodup unique
      rw [List.map_append] at h
      exact (List.nodup_append.mp h).2.1
    obtain ⟨hfault, hconsts, hread⟩ := printServices_ok hsvc
    have roles := restoreRoles hfault hdefs
    have hmain := mainReadable _ hm
    have hlayers := readCaptured_mapM
      (fun e he => layersReadable e (leftMem e he) (leftOutside e he))
      (fun e he => namesReadable e (leftMem e he)) _ hls
    -- the module's layers: each reads back at its path, and its name stops the prefixes
    have modules : ∀ p ∈ layers.toList.zipIdx,
        p.1.ReadsBack classes (sig.withDefs (d :: ds)) (defsSpell call (d :: ds) spell) ∧
          LayerTerm.readRefName (LayerTerm.refName (Path.layerPath p.2)) =
            some (Path.layerPath p.2) := by
      intro p hp
      have hfst : p.1 ∈ layers.toList.zipIdx.map Prod.fst := List.mem_map_of_mem hp
      have hsnd : p.2 ∈ layers.toList.zipIdx.map Prod.snd := List.mem_map_of_mem hp
      rw [List.zipIdx_map_fst] at hfst
      rw [List.zipIdx_map_snd, List.mem_range'_1] at hsnd
      rw [Nat.zero_add] at hsnd
      exact ⟨moduleReadable p.1 hfst, moduleNames p.2 hsnd.2⟩
    have hmods := readModuleLayers_mapM (fun p hp => modules p hp) hms
    have prefixes := prefixes_moduleLayers (fun p hp => (modules p hp).2) hms
      (defsPrefix_layers (fun e he => namesReadable e (leftMem e he)) hls)
      (servicePrefix_layers (fun e he => namesReadable e (leftMem e he)) hls)
    -- no hoisted layer stands in the module
    have outside : ∀ e ∈ selectHistory out.2 (Path.sortBy Path.declBefore (out.2.map Prod.fst)),
        inModulePath e.1 = false := by
      intro e he
      have hmem := (selectHistory_ordered_perm out.2 leftUnique).mem_iff.mp he
      rw [← inModule_of_defsOf (by rw [rootDefs]; exact List.cons_ne_nil _ _)]
      exact Eff.hoistAll_outside hoisted e (leftMem e hmem)
    obtain ⟨hsplit, hfilter⟩ := moduleLayersOf_split layers _ outside
    -- the bodies' own layers and the layers no body took are the hoisted layers, up to order
    have restored : (Eff.defs (d :: ds) bodies body layers).restoreAll
        (locals ++ selectHistory out.2 (Path.sortBy Path.declBefore (out.2.map Prod.fst))) =
        some root := by
      have perm : history.Perm
          (locals ++ selectHistory out.2 (Path.sortBy Path.declBefore (out.2.map Prod.fst))) :=
        hperm.symm.trans ((selectHistory_ordered_perm out.2 leftUnique).symm.append_left locals)
      rw [← shape, ← Eff.restoreAll_perm main perm unique]
      exact Eff.restoreAll_hoistAll hoisted
    have leading : defsPrefix (out.1.map TypeScript.Decl.const ++ svc.map TypeScript.Decl.const ++
        ms.map TypeScript.Decl.const ++ ls.map TypeScript.Decl.const) =
        (out.1, svc.map TypeScript.Decl.const ++ ms.map TypeScript.Decl.const ++
          ls.map TypeScript.Decl.const) := by
      rw [List.append_assoc, List.append_assoc, List.append_assoc]
      exact defsPrefix_append out.1 _ hnames hnot (defsPrefix_services svc _
        (fun c h => ⟨(hconsts c h).2.2.1, (hconsts c h).2.2.2⟩) prefixes.1)
    have services : servicePrefix (svc.map TypeScript.Decl.const ++ ms.map TypeScript.Decl.const ++
        ls.map TypeScript.Decl.const) =
        (svc, ms.map TypeScript.Decl.const ++ ls.map TypeScript.Decl.const) := by
      rw [List.append_assoc]
      exact servicePrefix_append svc _ (fun c h => ⟨(hconsts c h).2.2.1, (hconsts c h).2.2.2⟩)
        prefixes.2
    have hlayers' : (ms.map TypeScript.Decl.const ++ ls.map TypeScript.Decl.const).mapM
        (readLayerDecl classes (sig.withDefs (d :: ds)) (defsSpell call (d :: ds) spell)) =
        .ok ((layers.toList.zipIdx.map fun p => (Path.layerPath p.2, p.1)) ++
          selectHistory out.2 (Path.sortBy Path.declBefore (out.2.map Prod.fst))) := by
      have hl : (ls.map TypeScript.Decl.const).mapM (readLayerDecl classes
          (sig.withDefs (d :: ds)) (defsSpell call (d :: ds) spell)) =
          .ok (selectHistory out.2 (Path.sortBy Path.declBefore (out.2.map Prod.fst))) :=
        hlayers
      simp only [List.mapM_append, hmods, hl, ok_bind]
      rfl
    obtain ⟨c, cs', hcons⟩ : ∃ c cs', out.1 = c :: cs' := by
      cases bodies with
      | nil => simp only [printDefs, reduceCtorEq] at hout
      | cons b rest =>
        simp only [printDefs] at hout
        obtain ⟨c, _, tail⟩ := bind_eq_ok.mp hout
        obtain ⟨out', _, heq⟩ := bind_eq_ok.mp tail
        exact ⟨c, out'.1, by rw [← Except.ok.inj heq]⟩
    rw [readModule, blockClasses, splitClasses_rowServices, classesRead]
    simp only [readRowServices_rowServiceDecls servicesPrinted]
    simp only [List.map_append, List.map_cons, List.map_nil,
      List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, value, leading]
    rw [hcons] at hheads ⊢
    simp only [hheads, ok_bind, services, hread, roles, hbodies, hmain, hlayers', hsplit, hfilter,
      restored]

end Effect4.Program
