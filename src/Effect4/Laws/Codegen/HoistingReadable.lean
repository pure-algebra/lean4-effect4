import Effect4.Codegen.Read
import Effect4.Program.Binders
import Effect4.Laws.Program.Hoisting

/-!
# Readability survives shared-layer hoisting

Frozen obligation O6 (`2026-09-16-strict-proof-obligations.md`): for arbitrary
operation alphabet, signature, spelling and binder count, a readable program's
successful hoist has a readable main program and readable captured layers, and
every emitted reference name decodes to its original path. The name premise is
inherited from the original readable references; no decimal-codec assumption is
added. This is the existing reader's structural domain, not a target typing or
execution judgment.

Proof graph: contextual projections of the existing readability checks follow
`Node.child`; readable layer lookup and replacement lift those local facts along
paths; the capture fold retains them. No runtime check or tree operation changes.
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

open scoped Effect4.Program.Path

/-- Proof-local projection of the existing checks at a node's binder count. -/
private def nodeReadable (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) : Node Op → Bool
  | .eff e => readable sig spell n e
  | .stmts ss => readableStmts sig spell n ss
  | .stmt s => readableStmts sig spell n (.cons s .nil)
  | .action a => readableAction sig spell n a
  | .effs es => readableEffs sig spell n es
  | .layer l => readableLayer sig spell l
  | .layers ls => readableLayers sig spell ls

/-- Only this statement form extends the following statement list's environment. -/
private def bindsNext : Node Op → Bool
  | .stmt (.bindYield _) => true
  | _ => false

/-- The level of an addressed immediate child: the generated binder table's (`Node.childLevel`,
`Program/Binders.lean`, from `tools/Effect4Gen/binders.json`). -/
private abbrev childLevel (n : Nat) (node : Node Op) (i : Nat) : Nat := Node.childLevel n node i

private theorem bindsNext_setChild {node result replacement : Node Op} {index : Nat}
    (updated : node.setChild index replacement = some result) :
    bindsNext result = bindsNext node := by
  unfold Node.setChild at updated
  split at updated <;> cases updated <;> rfl

private theorem bindsNext_replaceLayerAt {node result : Node Op} {path : List Nat}
    {replacement : LayerTerm Op}
    (updated : node.replaceLayerAt path replacement = some result) :
    bindsNext result = bindsNext node := by
  cases path with
  | nil => cases node <;> cases updated; rfl
  | cons index path =>
      cases first : node.child index with
      | none => simp [Node.replaceLayerAt, first] at updated
      | some next =>
          cases changed : next.replaceLayerAt path replacement with
          | none => simp [Node.replaceLayerAt, first, changed] at updated
          | some next' =>
              apply bindsNext_setChild
              simpa [Node.replaceLayerAt, first, changed] using updated

private theorem nodeReadable_child (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    {node child : Node Op} {index : Nat}
    (hr : nodeReadable sig spell n node = true)
    (found : node.child index = some child) :
    nodeReadable sig spell (childLevel n node index) child = true := by
  unfold Node.child at found
  split at found <;> cases found
  all_goals try { simp_all [nodeReadable, childLevel, Node.childLevel, Node.closedChild, Node.binders, readable, readableLayer,
    readableLayers, readableStmts, readableAction, readableEffs, readable_select_iff, Decision.binds] }
  all_goals rename_i head tail
  all_goals cases head <;> simp_all [nodeReadable, childLevel, Node.childLevel, Node.closedChild, Node.binders, readableStmts]

-- the binder table and `readable` both grew with `select` (2026-09-16); this proof of the
-- hand-written reader's hoisting property runs the same tactic on every constructor and
-- needs a larger budget until R5 retires the reader
set_option maxHeartbeats 1600000 in
private theorem nodeReadable_setChild (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    {node old replacement result : Node Op} {index : Nat}
    (hr : nodeReadable sig spell n node = true)
    (found : node.child index = some old)
    (replacementReadable : nodeReadable sig spell (childLevel n node index) replacement = true)
    (binding : bindsNext replacement = bindsNext old)
    (updated : node.setChild index replacement = some result) :
    nodeReadable sig spell n result = true := by
  unfold Node.setChild at updated
  split at updated <;> cases updated
  all_goals simp only [Node.child, Option.some.injEq] at found
  all_goals subst old
  -- a readable `select` is the conditional (`readable_select_iff`): its decision is `.bool`
  all_goals try { simp_all [nodeReadable, childLevel, Node.childLevel, Node.closedChild, Node.binders, readable, readableLayer,
    readableLayers, readableStmts, readableAction, readableEffs, readable_select_iff, Decision.binds] }

  · rename_i head tail replacement
    cases head <;> cases replacement <;>
      simp_all [nodeReadable, childLevel, Node.childLevel, Node.closedChild, Node.binders, bindsNext, readableStmts]
  · rename_i head oldTail newTail
    cases head <;> simp_all [nodeReadable, childLevel, Node.childLevel, Node.closedChild, Node.binders, readableStmts]

private theorem nodeReadable_layerAt (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    {node : Node Op} {path : List Nat} {layer : LayerTerm Op}
    (hr : nodeReadable sig spell n node = true)
    (found : node.layerAt path = some layer) : readableLayer sig spell layer = true := by
  induction path generalizing node n with
  | nil => cases node <;> cases found; exact hr
  | cons index path ih =>
      cases first : node.child index with
      | none => simp [Node.layerAt_cons, first] at found
      | some next =>
          exact ih (childLevel n node index) (nodeReadable_child sig spell n hr first)
            (by simpa [Node.layerAt_cons, first] using found)

private theorem nodeReadable_replaceLayerAt (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    {node result : Node Op} {path : List Nat} {replacement : LayerTerm Op}
    (hr : nodeReadable sig spell n node = true)
    (hl : readableLayer sig spell replacement = true)
    (updated : node.replaceLayerAt path replacement = some result) :
    nodeReadable sig spell n result = true := by
  induction path generalizing node result n with
  | nil => cases node <;> cases updated; exact hl
  | cons index path ih =>
      cases first : node.child index with
      | none => simp [Node.replaceLayerAt, first] at updated
      | some next =>
          cases changed : next.replaceLayerAt path replacement with
          | none => simp [Node.replaceLayerAt, first, changed] at updated
          | some next' =>
              apply nodeReadable_setChild sig spell n hr first
                (ih (childLevel n node index) (nodeReadable_child sig spell n hr first) changed)
                (bindsNext_replaceLayerAt changed)
              simpa [Node.replaceLayerAt, first, changed] using updated

/-- Every addressed layer of a readable program is readable at its own closed scope. -/
theorem readable_layerAt (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    {root : Eff Op} {path : List Nat} {layer : LayerTerm Op}
    (hr : readable sig spell n root = true)
    (found : (Node.eff root).layerAt path = some layer) :
    readableLayer sig spell layer = true :=
  nodeReadable_layerAt sig spell n (node := .eff root) hr found

/-- Replacing an addressed layer by a readable layer keeps the program readable.
The surrounding binder counts and the layer's closed scope remain unchanged. -/
theorem readable_replaceLayerAt (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    {root result : Eff Op} {path : List Nat} {replacement : LayerTerm Op}
    (hr : readable sig spell n root = true)
    (hl : readableLayer sig spell replacement = true)
    (updated : (Node.eff root).replaceLayerAt path replacement = some (.eff result)) :
    readable sig spell n result = true :=
  nodeReadable_replaceLayerAt sig spell n (node := .eff root) (result := .eff result) hr hl updated

private def namesReadable (sites : List (List Nat × List Nat)) : Bool :=
  sites.all fun entry =>
    decide (LayerTerm.readRefName (LayerTerm.refName entry.2) = some entry.2)

set_option hygiene false in
local macro "close_ref_names" : tactic => `(tactic|
  (first
  | exact True.intro
  | apply eff_refNames
  | apply stmts_refNames
  | apply action_refNames
  | apply effs_refNames
  | apply layer_refNames
  | apply layers_refNames) <;> solve_by_elim [And.left, And.right])

mutual
  private theorem eff_refNames (sig : Signature Op)
      (spell : String → List String → Option Op) (node : Eff Op) (n : Nat) (path : List Nat)
      (hr : readable sig spell n node = true) : namesReadable (node.refSites path) = true := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, readable, readable_select_iff, Eff.refSites, List.all_append,
      Bool.and_eq_true, namesReadable, List.all_nil, Bool.false_eq_true]
    all_goals repeat' apply And.intro
    all_goals close_ref_names

  private theorem stmts_refNames (sig : Signature Op)
      (spell : String → List String → Option Op) (node : Stmts Op) (n : Nat) (path : List Nat)
      (hr : readableStmts sig spell n node = true) : namesReadable (node.refSites path) = true := by
    cases node with
    | nil => rfl
    | cons head tail =>
        cases head <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, readableStmts, Stmts.refSites, Stmt.refSites,
          List.all_append, Bool.and_eq_true, namesReadable, List.all_nil]
        all_goals repeat' apply And.intro
        all_goals close_ref_names

  private theorem action_refNames (sig : Signature Op)
      (spell : String → List String → Option Op) (node : ActionTerm Op) (n : Nat) (path : List Nat)
      (hr : readableAction sig spell n node = true) : namesReadable (node.refSites path) = true := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, readableAction, ActionTerm.refSites, namesReadable,
      List.all_nil, Bool.and_eq_true, Bool.false_eq_true]
    all_goals close_ref_names

  private theorem effs_refNames (sig : Signature Op)
      (spell : String → List String → Option Op) (node : Effs Op) (n : Nat) (path : List Nat)
      (hr : readableEffs sig spell n node = true) : namesReadable (node.refSites path) = true := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, readableEffs, Effs.refSites, List.all_append,
      Bool.and_eq_true, namesReadable, List.all_nil]
    all_goals repeat' apply And.intro
    all_goals close_ref_names

  private theorem layer_refNames (sig : Signature Op)
      (spell : String → List String → Option Op) (node : LayerTerm Op) (path : List Nat)
      (hr : readableLayer sig spell node = true) : namesReadable (node.refSites path) = true := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, readableLayer, LayerTerm.refSites, List.all_append,
      Bool.and_eq_true, namesReadable, List.all_nil, List.all_cons, Bool.and_true]
    all_goals repeat' apply And.intro
    all_goals close_ref_names

  private theorem layers_refNames (sig : Signature Op)
      (spell : String → List String → Option Op) (node : LayerTerms Op) (path : List Nat)
      (hr : readableLayers sig spell node = true) : namesReadable (node.refSites path) = true := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, readableLayers, LayerTerms.refSites, List.all_append,
      Bool.and_eq_true, namesReadable, List.all_nil]
    all_goals repeat' apply And.intro
    all_goals close_ref_names
end

private theorem readable_targetNames {sig : Signature Op}
    {spell : String → List String → Option Op} {n : Nat} {root : Eff Op}
    (hr : readable sig spell n root = true) :
    ∀ target ∈ root.refTargets,
      LayerTerm.readRefName (LayerTerm.refName target) = some target := by
  intro target member
  have inDistinct := (Path.sortBy_perm Path.declBefore
    ((root.refSites []).map Prod.snd).eraseDups).mem_iff.mp member
  have inSites := List.mem_eraseDups.mp inDistinct
  obtain ⟨⟨site, named⟩, atSite, same⟩ := List.mem_map.mp inSites
  cases same
  have good := List.all_eq_true.mp (eff_refNames sig spell root n [] hr) (site, named) atSite
  exact of_decide_eq_true good

private theorem captureFold_readable (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) (targets : List (List Nat))
    {root main : Eff Op} {history declarations : List (List Nat × LayerTerm Op)}
    (hr : readable sig spell n root = true)
    (hh : ∀ entry ∈ history, readableLayer sig spell entry.2 = true ∧
      LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1)
    (names : ∀ target ∈ targets,
      LayerTerm.readRefName (LayerTerm.refName target) = some target)
    (hoisted : targets.foldlM (init := (root, history))
      (fun (acc, decls) target =>
        match (Node.eff acc).layerAt target,
            (Node.eff acc).replaceLayerAt target (.ref target) with
        | some layer, some (Node.eff next) => .ok (next, (target, layer) :: decls)
        | _, _ => .error target) =
      (Except.ok (main, declarations) : Except (List Nat) _)) :
    readable sig spell n main = true ∧
      ∀ entry ∈ declarations, readableLayer sig spell entry.2 = true ∧
        LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1 := by
  induction targets generalizing root history with
  | nil => cases hoisted; exact ⟨hr, hh⟩
  | cons target targets ih =>
      have name := names target (by simp)
      have refReadable : readableLayer sig spell (.ref target : LayerTerm Op) = true := by
        simpa only [readableLayer, decide_eq_true_eq] using name
      cases found : (Node.eff root).layerAt target with
      | none => simp [List.foldlM_cons, found, Bind.bind, Except.bind] at hoisted
      | some layer =>
          cases changed : (Node.eff root).replaceLayerAt target (.ref target) with
          | none => simp [List.foldlM_cons, found, changed, Bind.bind, Except.bind] at hoisted
          | some node =>
              cases node <;>
                simp only [List.foldlM_cons, found, changed, Bind.bind, Except.bind] at hoisted
              all_goals try contradiction
              rename_i next
              have nextReadable := readable_replaceLayerAt sig spell n hr refReadable changed
              apply ih nextReadable (fun entry member => ?_)
                (fun t ht => names t (List.mem_cons_of_mem _ ht)) hoisted
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨readable_layerAt sig spell n hr found, name⟩
              · exact hh entry member

/-- Hoisting a readable program retains readability of its main and every captured
layer. Each emitted path name already passed the original reference's readability
check. The result holds at any outer binder count and assumes only successful
hoisting, not reference well-formedness, typing, or an extra name-codec law. -/
theorem readable_hoistAll {sig : Signature Op}
    {spell : String → List String → Option Op} {n : Nat}
    {root main : Eff Op} {declarations : List (List Nat × LayerTerm Op)}
    (hr : readable sig spell n root = true)
    (hoisted : root.hoistAll = .ok (main, declarations)) :
    readable sig spell n main = true ∧
      ∀ entry ∈ declarations, readableLayer sig spell entry.2 = true ∧
        LayerTerm.readRefName (LayerTerm.refName entry.1) = some entry.1 := by
  apply captureFold_readable sig spell n _ hr (by simp) ?_ hoisted
  intro target member
  exact readable_targetNames hr target
    ((Path.sortBy_perm (fun a b => Path.lt b a) root.refTargets).mem_iff.mp member)

end Effect4.Program
