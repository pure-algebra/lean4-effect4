import Effect4.Codegen.Read
import Effect4.Laws.Program.Hoisting
import Effect4.Laws.Program.HoistingTotal

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

private def readCaptured (sig : Signature Op) (spell : String → List String → Option Op)
    (decl : TypeScript.Decl) : Except ReadRefusal (List Nat × LayerTerm Op) :=
  match decl with
  | .const c =>
    match LayerTerm.readRefName c.name with
    | some target =>
      if LayerTerm.refName target = c.name then do
        let layer ← readLayer sig spell c.value
        .ok (target, layer)
      else .error (.shape "module")
    | none => .error (.shape "module")
  | _ => .error (.shape "module")

private theorem readCaptured_printCaptured {sig : Signature Op}
    {spell : String → List String → Option Op}
    {history : History Op}
    (layers : ∀ entry ∈ history, entry.2.ReadsBack sig spell)
    (names : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {target : List Nat} {entry : List Nat × LayerTerm Op} {decl : TypeScript.ConstDecl}
    (found : history.find? (·.1 == target) = some entry)
    (printed : printCaptured sig history target = .ok decl) :
    readCaptured sig spell (.const decl) = .ok entry := by
  have mem := List.mem_of_find?_eq_some found
  have key : entry.1 = target := by
    simpa only [beq_iff_eq] using List.find?_some found
  simp only [printCaptured, found] at printed
  obtain ⟨body, hp, heq⟩ := bind_eq_ok.mp printed
  cases heq
  have hr := layers entry mem _ hp
  simp [readCaptured, ← key, names entry mem, hr]

private theorem readCaptured_mapM {sig : Signature Op}
    {spell : String → List String → Option Op}
    {history : History Op}
    (layers : ∀ entry ∈ history, entry.2.ReadsBack sig spell)
    (names : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    (targets : List (List Nat)) {decls : List TypeScript.ConstDecl}
    (printed : targets.mapM (printCaptured sig history) = .ok decls) :
    (decls.map TypeScript.Decl.const).mapM (readCaptured sig spell) =
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

/-- Reading the declaration block produced by the module printer recovers the original
program, including shared-layer references, when each piece successful hoisting produced
reads back from its own printing (`ReadsBack`, which `readable` gives) and the emitted
reference names decode. The premises concern the pieces, never the module read itself, and
they are stated of any expression reader: this law is the hoisting inverse composed with them.

This is a structural AST equation: it does not validate the declaration's claimed
type, imports, rendered TypeScript bytes, or target execution. -/
theorem readModule_printModule {sig : Signature Op}
    {spell : String → List String → Option Op}
    {root main : Eff Op} {history : List (List Nat × LayerTerm Op)}
    (hoisted : root.hoistAll = .ok (main, history))
    (mainReadable : ReadsBack sig spell 0 main)
    (layersReadable : ∀ entry ∈ history, entry.2.ReadsBack sig spell)
    (namesReadable : ∀ entry ∈ history,
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    {name : String} {ty : EffTy} {decls : List TypeScript.ConstDecl}
    (printed : printModule sig name ty root = .ok decls) :
    readModule sig spell (decls.map TypeScript.Decl.const) = .ok root := by
  have ordered := Eff.hoistAll_ordered hoisted
  have unique : (history.map Prod.fst).Nodup := ordered.imp (by
    intro a b before equal
    subst b
    simp [Path.lt_irrefl] at before)
  unfold printModule at printed
  rw [hoisted] at printed
  change ((Path.sortBy Path.declBefore (history.map Prod.fst)).mapM
    (printCaptured sig history) >>= fun ds => print sig 0 main >>= fun body =>
    printDecl name ty body >>= fun decl => .ok (ds ++ [decl])) = .ok decls at printed
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
  simp only [List.map_append, List.map_cons, List.map_nil, readModule,
    List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, value]
  change (readEff sig spell 0 body >>= fun e =>
    (ds.map TypeScript.Decl.const).mapM (readCaptured sig spell) >>= fun entries =>
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

/-- The shape of a successful declaration block, read off the printer itself: the layer
declarations first, each plain and exported, then the one main declaration the declaration
printer produced. The reading boundary compares a block against exactly this shape. -/
theorem printModule_shape {sig : Signature Op} {name : String} {ty : EffTy} {root : Eff Op}
    {block : List TypeScript.ConstDecl} (printed : printModule sig name ty root = .ok block) :
    ∃ layers main body, block = layers ++ [main] ∧
      (∀ decl ∈ layers, decl.type = none ∧ decl.exported = true) ∧
      printDecl name ty body = .ok main := by
  unfold printModule at printed
  cases hoisted : root.hoistAll with
  | error target => rw [hoisted] at printed; simp at printed
  | ok pair =>
    obtain ⟨main, history⟩ := pair
    rw [hoisted] at printed
    change ((Path.sortBy Path.declBefore (history.map Prod.fst)).mapM
      (printCaptured sig history) >>= fun ds => print sig 0 main >>= fun body =>
      printDecl name ty body >>= fun decl => .ok (ds ++ [decl])) = .ok block at printed
    obtain ⟨ds, hp, hmain⟩ := bind_eq_ok.mp printed
    obtain ⟨body, _, hdecl⟩ := bind_eq_ok.mp hmain
    obtain ⟨decl, declaration, heq⟩ := bind_eq_ok.mp hdecl
    cases heq
    exact ⟨ds, decl, body, rfl,
      mapM_ok_forall _ _ (fun t d hd => printCaptured_plain t d hd) _ hp, declaration⟩

end Effect4.Program
