import Effect4.Laws.Codegen.ReadLeaf
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
    exact False.elim (Path.lt_asymm ab ba)
  · exact Path.sortBy_pairwise Path.lt (fun _ _ _ => Path.lt_trans)
      (fun _ _ => Path.lt_total) unique
  · exact Path.sortBy_pairwise Path.lt (fun _ _ _ => Path.lt_trans)
      (fun _ _ => Path.lt_total) (perm.nodup unique)
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

/-- Definition constants, then declarations that begin with none, split there. A step of
`readModule_printModule_defs`. -/
theorem defsPrefix_append (cs : List TypeScript.ConstDecl) (rest : List TypeScript.Decl)
    (named : ∀ c ∈ cs, LayerTerm.readRefName c.name = none)
    (after : defsPrefix rest = ([], rest)) :
    defsPrefix (cs.map TypeScript.Decl.const ++ rest) = (cs, rest) := by
  induction cs with
  | nil => simpa only [List.map_nil, List.nil_append] using after
  | cons c cs ih =>
    have hc := named c List.mem_cons_self
    have hrest := ih (fun c' h => named c' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, List.cons_append, defsPrefix, hc, hrest]

/-- A block of class declarations, then constants, splits there. -/
theorem splitClasses_append (cs : List TypeScript.ClassDecl) (ds : List TypeScript.ConstDecl) :
    splitClasses (cs.map TypeScript.Decl.classDecl ++ ds.map TypeScript.Decl.const) =
      (cs, ds.map TypeScript.Decl.const) := by
  induction cs with
  | nil => cases ds <;> rfl
  | cons c cs ih => simp only [List.map_cons, List.cons_append, splitClasses, ih]

/-- Reading the declaration block produced by the module printer recovers the original
program, including shared-layer references, when its leading class declarations read back to
the module's payload classes (decisions row 120, part E2), each piece successful hoisting
produced reads back from its own printing under those classes (`ReadsBack`, which `readable`
gives), and the emitted reference names decode. The premises concern the pieces, never the
module read itself, and they are stated of any expression reader: this law is the hoisting
inverse composed with them. Placed at R8 (`translation-simulation`): the module face's round
trip, the class section included.

This is a structural AST equation: it does not validate the declaration's claimed
type, imports, rendered TypeScript bytes, or target execution. -/
theorem readModule_printModule {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {call : Nat → Op}
    {root main : Eff Op} {history : List (List Nat × LayerTerm Op)}
    (hoisted : root.hoistAll = .ok (main, history))
    (plain : main.block? = none)
    {classDecls : List TypeScript.ClassDecl}
    (classesRead : Effect4.Codegen.Classes.readClassDecls classDecls = some classes)
    (mainReadable : ReadsBack classes sig spell 0 main)
    (layersReadable : ∀ entry ∈ history, entry.2.ReadsBack classes sig spell)
    (namesReadable : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {name : String} {ty : EffTy} {decls : List TypeScript.ConstDecl}
    (printed : printModule sig name ty root = .ok decls) :
    readModule sig spell call
      (classDecls.map TypeScript.Decl.classDecl ++ decls.map TypeScript.Decl.const) = .ok root := by
  have ordered := Eff.hoistAll_ordered hoisted
  have unique : (history.map Prod.fst).Nodup := ordered.imp (by
    intro a b before equal
    subst b
    simp [Path.lt_irrefl] at before)
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
  rw [readModule, blockClasses, splitClasses_append, classesRead]
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
    (h : e.block? = some (defs, bodies, body)) : e = .defs defs bodies body := by
  cases e <;> simp only [Eff.block?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- A program's block holds the program's declarations. -/
theorem Eff.defsOf_of_block? {e : Eff Op} {defs : List DefDecl} {bodies : Effs Op}
    {body : Eff Op} (h : e.block? = some (defs, bodies, body)) : e.defsOf = defs := by
  rw [Eff.eq_of_block? h]
  rfl

/-- A program with no block has no declarations. -/
theorem Eff.defsOf_of_block?_none {e : Eff Op} (h : e.block? = none) : e.defsOf = [] := by
  cases e <;> simp only [Eff.block?, reduceCtorEq] at h <;> rfl

/-- A printed definition is a constant with no annotation, exported. A step of
`printModule_shape`. -/
theorem printDef_plain {sig : Signature Op} {d : DefDecl} {body : Eff Op}
    {c : TypeScript.ConstDecl} (printed : printDef sig d body = .ok c) :
    c.type = none ∧ c.exported = true ∧ c.name = d.name := by
  unfold printDef at printed
  split at printed
  · cases printed
  · obtain ⟨_, _, rest⟩ := bind_eq_ok.mp printed
    obtain ⟨_, _, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨_, _, heq⟩ := bind_eq_ok.mp rest
    cases heq
    exact ⟨rfl, rfl, rfl⟩

/-- Every printed definition of a block is a plain constant. A step of `printModule_shape`. -/
theorem printDefs_plain {sig : Signature Op} {defs : List DefDecl} {bodies : Effs Op}
    {cs : List TypeScript.ConstDecl} (printed : printDefs sig defs bodies = .ok cs) :
    ∀ c ∈ cs, c.type = none ∧ c.exported = true := by
  induction defs generalizing bodies cs with
  | nil =>
    cases bodies with
    | nil => cases printed; intro c mem; cases mem
    | cons _ _ => cases printed
  | cons d ds ih =>
    cases bodies with
    | nil => cases printed
    | cons b rest =>
      simp only [printDefs] at printed
      obtain ⟨c, hc, tail⟩ := bind_eq_ok.mp printed
      obtain ⟨cs', hcs, heq⟩ := bind_eq_ok.mp tail
      cases heq
      intro c' mem
      rcases List.mem_cons.mp mem with rfl | rest'
      · exact ⟨(printDef_plain hc).1, (printDef_plain hc).2.1⟩
      · exact ih hcs c' rest'

/-- An empty requirement row prints as `never`. -/
theorem requirementType_nil (scopeKey : ServiceKey) :
    requirementType scopeKey (Effect4.Machine.Env.Requirement.ofList []) = .name ["never"] [] :=
  rfl

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
  | error target => rw [hoisted] at printed; simp at printed
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
    | some triple =>
      obtain ⟨defs, bodies, body⟩ := triple
      cases defs with
      | nil => simp only [hb, reduceCtorEq] at printed
      | cons d ds =>
        simp only [hb] at printed
        change (printDefs (sig.withDefs (d :: ds)) (d :: ds) bodies >>= fun cs =>
          (Path.sortBy Path.declBefore (history.map Prod.fst)).mapM
            (printCaptured (sig.withDefs (d :: ds)) history) >>= fun ls =>
          print (sig.withDefs (d :: ds)) 0 body >>= fun m =>
          printDecl name ty m sig.scopeKey >>= fun decl => .ok (cs ++ ls ++ [decl])) =
            .ok block at printed
        obtain ⟨cs, hcs, rest⟩ := bind_eq_ok.mp printed
        obtain ⟨ls, hls, rest⟩ := bind_eq_ok.mp rest
        obtain ⟨m, _, rest⟩ := bind_eq_ok.mp rest
        obtain ⟨decl, declaration, heq⟩ := bind_eq_ok.mp rest
        cases heq
        refine ⟨cs ++ ls, decl, m, List.append_assoc cs ls [decl] ▸ rfl, ?_, declaration⟩
        intro c mem
        rcases List.mem_append.mp mem with hc | hl
        · exact printDefs_plain hcs c hc
        · exact mapM_ok_forall _ _ (fun t d hd => printCaptured_plain t d hd) _ hls c hl

/-- **A definition's header reads back**: the constant `printDef` prints of a readable declaration
reads as that declaration and the printed suspension of its body. A step of
`readModule_printModule_defs`. -/
theorem readDefHead_printDef {sig : Signature Op} {d : DefDecl} {body : Eff Op}
    {c : TypeScript.ConstDecl} (readable : d.readable = true) (printed : printDef sig d body = .ok c) :
    ∃ x, print sig 1 (.suspend body) = .ok x ∧ readDefHead c = .ok (d, x) := by
  simp only [DefDecl.readable, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none]
    at readable
  obtain ⟨⟨⟨⟨hreq, hans⟩, herr⟩, hrequires⟩, _⟩ := readable
  unfold printDef at printed
  split at printed
  · cases printed
  · obtain ⟨request, hrequest, rest⟩ := bind_eq_ok.mp printed
    obtain ⟨result, hresult, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨x, hx, heq⟩ := bind_eq_ok.mp rest
    cases heq
    obtain ⟨reqT, hreqT⟩ := Effect4.Codegen.Classes.ofTy_of_readable hreq
    obtain ⟨ansT, hansT⟩ := Effect4.Codegen.Classes.ofTy_of_readable hans
    obtain ⟨errT, herrT⟩ := Effect4.Codegen.Classes.ofTy_of_readable herr
    simp only [typeRefOf, hreqT, Except.ok.injEq] at hrequest
    subst hrequest
    simp only [declarationType, DefDecl.effTy, hansT, herrT, bind, Except.bind,
      Except.ok.injEq] at hresult
    subst hresult
    refine ⟨x, hx, ?_⟩
    obtain ⟨name, request, answer, error, requires⟩ := d
    simp only at hrequires
    subst hrequires
    simp only [readDefHead, requirementType_nil, ↓reduceIte,
      Effect4.Codegen.Classes.readTyChecked_of_readable hreq hreqT,
      Effect4.Codegen.Classes.readTyChecked_of_readable hans hansT,
      Effect4.Codegen.Classes.readTyChecked_of_readable herr herrT]

/-- **A block's definitions read back**: the constants `printDefs` prints of readable declarations
read as the declarations, and their bodies read back where each body's printed suspension does.
A step of `readModule_printModule_defs`. -/
theorem readDefs_printDefs {classes : Classes} {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {defs : List DefDecl} {bodies : Effs Op}
    {cs : List TypeScript.ConstDecl} (readable : ∀ d ∈ defs, d.readable = true)
    (bodiesRead : ∀ b ∈ bodies.toList, ReadsBack classes sig spell 1 (.suspend b))
    (printed : printDefs sig defs bodies = .ok cs) :
    ∃ heads, cs.mapM readDefHead = .ok heads ∧ heads.map (·.1) = defs ∧
      readDefBodies classes sig spell heads = .ok bodies ∧
      ∀ c ∈ cs, LayerTerm.readRefName c.name = none := by
  induction defs generalizing bodies cs with
  | nil =>
    cases bodies with
    | nil => cases printed; exact ⟨[], rfl, rfl, rfl, fun c mem => nomatch mem⟩
    | cons _ _ => cases printed
  | cons d ds ih =>
    cases bodies with
    | nil => cases printed
    | cons b rest =>
      simp only [printDefs] at printed
      obtain ⟨c, hc, tail⟩ := bind_eq_ok.mp printed
      obtain ⟨cs', hcs, heq⟩ := bind_eq_ok.mp tail
      cases heq
      have hd := readable d List.mem_cons_self
      obtain ⟨x, hx, hhead⟩ := readDefHead_printDef hd hc
      have hread := bodiesRead b (by simp only [Effs.toList, List.mem_cons, true_or]) _ hx
      obtain ⟨heads, hheads, hdefs, hbodies, hnames⟩ :=
        ih (fun d' h => readable d' (List.mem_cons_of_mem _ h))
          (fun b' h => bodiesRead b' (by simp only [Effs.toList, List.mem_cons, h, or_true])) hcs
      refine ⟨(d, x) :: heads, ?_, ?_, ?_, ?_⟩
      · simp only [List.mapM_cons, hhead, hheads, ok_bind]
        rfl
      · simp only [List.map_cons, hdefs]
      · simp only [readDefBodies, readDefBody, hread, ok_bind, hbodies]
      · intro c' mem
        rcases List.mem_cons.mp mem with rfl | rest'
        · simp only [DefDecl.readable, Bool.and_eq_true, Option.isNone_iff_eq_none] at hd
          rw [(printDef_plain hc).2.2]
          exact hd.2
        · exact hnames c' rest'

/-- **G6: the round trip of a module with a definition block** (decisions row 328). The module
printer prints a block's definitions as constants before the layers and the main declaration
(`printModule`). When each declaration is readable (`DefDecl.readable`: readable columns, an
empty requirement row, a name with no layer path), and each body's suspension, the main program
and each layer read back from their printing at the block's signature through the block's
spelling map (`defsSpell`), the module reads back to the program. The premises concern the
pieces, as `readModule_printModule`'s do, and they are stated of any reader.

Placement: concept `exact-codecs`, claim `module-defs-round-trip`, requirement R8. Consumers: the
module round trip of the readable domain (`readModule_printModule_readable`) and, through it,
`ModuleEmission.readModule`. It is a structural equation: it does not say that tsgo accepts the
module or how rc.112 runs it. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readModule_printModule_defs {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {call : Nat → Op}
    {root main body : Eff Op} {defs : List DefDecl} {bodies : Effs Op}
    {history : List (List Nat × LayerTerm Op)}
    (hoisted : root.hoistAll = .ok (main, history))
    (block : main.block? = some (defs, bodies, body))
    {classDecls : List TypeScript.ClassDecl}
    (classesRead : Effect4.Codegen.Classes.readClassDecls classDecls = some classes)
    (headsReadable : ∀ d ∈ defs, d.readable = true)
    (bodiesReadable : ∀ b ∈ bodies.toList,
      ReadsBack classes (sig.withDefs defs) (defsSpell call defs spell) 1 (.suspend b))
    (mainReadable : ReadsBack classes (sig.withDefs defs) (defsSpell call defs spell) 0 body)
    (layersReadable : ∀ entry ∈ history,
      entry.2.ReadsBack classes (sig.withDefs defs) (defsSpell call defs spell))
    (namesReadable : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {name : String} {ty : EffTy} {decls : List TypeScript.ConstDecl}
    (printed : printModule sig name ty root = .ok decls) :
    readModule sig spell call
      (classDecls.map TypeScript.Decl.classDecl ++ decls.map TypeScript.Decl.const) = .ok root := by
  have ordered := Eff.hoistAll_ordered hoisted
  have unique : (history.map Prod.fst).Nodup := ordered.imp (by
    intro a b before equal
    subst b
    simp only [Path.lt_irrefl, Bool.false_eq_true] at before)
  have shape := Eff.eq_of_block? block
  unfold printModule at printed
  rw [hoisted] at printed
  cases defs with
  | nil => simp only [block, reduceCtorEq] at printed
  | cons d ds =>
    simp only [block] at printed
    change (printDefs (sig.withDefs (d :: ds)) (d :: ds) bodies >>= fun cs =>
      (Path.sortBy Path.declBefore (history.map Prod.fst)).mapM
        (printCaptured (sig.withDefs (d :: ds)) history) >>= fun ls =>
      print (sig.withDefs (d :: ds)) 0 body >>= fun m =>
      printDecl name ty m sig.scopeKey >>= fun decl => .ok (cs ++ ls ++ [decl])) =
        .ok decls at printed
    obtain ⟨cs, hcs, rest⟩ := bind_eq_ok.mp printed
    obtain ⟨ls, hls, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨m, hm, rest⟩ := bind_eq_ok.mp rest
    obtain ⟨decl, declaration, heq⟩ := bind_eq_ok.mp rest
    cases heq
    have value := printDecl_value declaration
    obtain ⟨heads, hheads, hdefs, hbodies, hnames⟩ :=
      readDefs_printDefs headsReadable bodiesReadable hcs
    have hmain := mainReadable _ hm
    have hlayers := readCaptured_mapM layersReadable namesReadable _ hls
    have restored : (Eff.defs (d :: ds) bodies body).restoreAll
        (selectHistory history (Path.sortBy Path.declBefore (history.map Prod.fst))) =
        some root := by
      have perm := selectHistory_ordered_perm history unique
      rw [← shape, Eff.restoreAll_perm main perm ((perm.map Prod.fst).symm.nodup unique)]
      exact Eff.restoreAll_hoistAll hoisted
    have leading : defsPrefix (cs.map TypeScript.Decl.const ++ ls.map TypeScript.Decl.const) =
        (cs, ls.map TypeScript.Decl.const) :=
      defsPrefix_append cs _ hnames (defsPrefix_layers namesReadable hls)
    rw [readModule, blockClasses, splitClasses_append, classesRead]
    simp only [List.map_append, List.map_cons, List.map_nil,
      List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, value, leading]
    obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
      cases bodies with
      | nil => simp only [printDefs, reduceCtorEq] at hcs
      | cons b rest =>
        simp only [printDefs] at hcs
        obtain ⟨c, _, tail⟩ := bind_eq_ok.mp hcs
        obtain ⟨cs', _, heq⟩ := bind_eq_ok.mp tail
        exact ⟨c, cs', Except.ok.inj heq.symm⟩
    change ((c :: cs').mapM readDefHead >>= fun heads =>
      readDefBodies classes ((sig.withDefs (heads.map (·.1))))
          (defsSpell call (heads.map (·.1)) spell) heads >>= fun bodies =>
      readEff classes (sig.withDefs (heads.map (·.1))) (defsSpell call (heads.map (·.1)) spell) 0
          m >>= fun e =>
      (ls.map TypeScript.Decl.const).mapM (readCaptured classes (sig.withDefs (heads.map (·.1)))
          (defsSpell call (heads.map (·.1)) spell)) >>= fun entries =>
      match (Eff.defs (heads.map (·.1)) bodies e).restoreAll entries with
      | some out => .ok out
      | none => .error (.shape "module")) = .ok root
    simp only [hheads, ok_bind, hdefs, hbodies, hmain, hlayers, restored]

end Effect4.Program
