import Tools.View.Flow
import Tools.View.KeyMap
import Tools.View.Algebra
import Effect4.Laws.Program.Address
import Effect4.Laws.Program.PathFold

/-!
# The page's folds along an edit: what an edit at `a` leaves standing

A session's edit (`fill` or `omit` at the address `a`) replaces the subtree at `a` and nothing else
(`Node.replaceAt`, `Program/Refs.lean`). A node's own text reads its constructor and its arguments
that are no child (`Program.ownText`). So every line outside the subtree at `a`, an ancestor
included, keeps its text. A frame leaves its lines' texts to the next (`Memo`), and the page's lines
along an edit compute the texts under `a` alone (`lines`). This is slice LV-4 of the live view
(`docs/research/2026-10-10-live-view/LANDING.md`).

**The waits are computed fresh.** An await's target reads the binder its term names and the part
that binder binds (`Flow.forkOf`). That part can stand outside the await's subtree, so a sibling
edit changes the target. Codex's review found the stale edge and the missing edge it leaves
(LV-OW-01, `docs/research/2026-10-10-live-view-invalidation-review/README.md`). So the flow along
an edit takes its leaves' texts from the memo and its waits from `Flow.waits` (`flow`). A memo of
the waits needs a record of what each wait read; that design is Codex's, and stays proposed.

## The laws

- `linesWith_map`: the lines along an edit are the fresh lines, each text taken from the memo
  outside the edited subtree;
- `linesWith_eq` (**the text law**): under a memo valid outside `a` (`MemoValid`), the lines along an
  edit at `a` are the fresh lines;
- `next_valid`: the memo a frame leaves is valid for the program after any fill or omit at `a`.

The laws hold for every text of a line that reads no child (`ChildBlind`), as `Program.lines_at`
does. The view's text, `Program.ownText`, reads no child: `argText` answers nothing at a child. It
reads strings, whose functions reach `Classical.choice` on this toolchain, so its instance stands
as a reading of `argText` and as the check at every step of every build
(`Tools.View.LiveChecks`). The laws are a tool's, not registry claims (decisions row 334, point 3).
They serve concept `initial-algebras-folds` and R14's live authoring; their consumer is the live
step (`Tools.View.Live.page`), which draws a page from the lines along each edit.

**What they do not establish.** No law says the flow along an edit is the fresh flow: it is checked
at every step of every build. No law counts the work an edit saves; the probes measured it.
-/

open Effect4 Effect4.Program Tools.View Tools.View.Program

namespace Tools.View.Inc

/-! ## The memo -/

/-- What one frame leaves for the next: each line's own text, by its address. -/
structure Memo where
  texts : KeyMap (List Nat) String := {}

/-- The text a memo keeps at an address. -/
def Memo.textAt? (memo : Memo) (p : List Nat) : Option String := memo.texts.get? p

/-- The memo a frame leaves: its lines' texts, the first line at an address standing. -/
def Memo.next (ls : List Program.Node) : Memo :=
  { texts := ls.foldr (fun n m => m.insert n.path n.text) {} }

/-- A line's text along an edit at `edited`: computed under the edited subtree, else the memo's,
else computed. The computation runs only where the memo does not answer. -/
def textOf (memo : Memo) (edited : Option (List Nat)) (p : List Nat) (compute : Unit → String) : String :=
  match edited with
  | some a =>
    if a.isPrefixOf p then compute ()
    else match memo.textAt? p with
      | some t => t
      | none => compute ()
  | none => compute ()

/-! ## The lines along an edit -/

/-- `Program.layerWith text`, each line's text along an edit at `edited` (`textOf`). -/
def layerAt (text : String → List (ArgF NativeOp Program.Lines) → String) (memo : Memo)
    (edited : Option (List Nat)) (fam : EffFam) (ctor : String) (args : List (ArgF NativeOp Program.Lines)) :
    Program.Lines fam :=
  fun p d =>
    let inner := if Program.spine fam then d else d + 1
    let children := (args.filterMap Program.childLines).zipIdx.flatMap fun (r, i) => r (p ++ [i]) inner
    if Program.spine fam then children
    else ⟨p, d, textOf memo edited p (fun _ => text ctor args), args.findSome? Program.argOp⟩ :: children

/-- The lines of a program along an edit, for a text of a line. -/
def linesWith (text : String → List (ArgF NativeOp Program.Lines) → String) (memo : Memo)
    (edited : Option (List Nat)) (program : Eff NativeOp) : List Program.Node :=
  cata_eff (EffAlgebra.ofLayer (layerAt text memo edited)) program [] 0

/-- The fresh lines of a program, for a text of a line: `Program.lines` is `freshLines ownText`. -/
def freshLines (text : String → List (ArgF NativeOp Program.Lines) → String) (program : Eff NativeOp) :
    List Program.Node :=
  cata_eff (EffAlgebra.ofLayer (Program.layerWith text)) program [] 0

/-- **The page's lines along an edit**: `Program.lines`, each line's own text outside the edited
subtree from the memo. -/
def lines (memo : Memo) (edited : Option (List Nat)) (program : Eff NativeOp) : List Program.Node :=
  linesWith (ownText (R := Program.Lines)) memo edited program

/-! ## The flow along an edit -/

/-- **The program's flow along an edit**: `Flow.ofProgram`, each leaf's text from the memo outside
the edited subtree, and the waits computed fresh (LV-OW-01). -/
def flow (memo : Memo) (edited : Option (List Nat)) (program : NativeEff) : Flow.Flow :=
  let ws := Flow.waits program
  let part := cata_eff (EffAlgebra.ofLayer
    (Flow.flowLayerWith (textOf memo edited) fun k => (ws.lookup k).getD [])) program []
  part.flow.closing part.releases

/-! ## The text law -/

/-- No lines, for every sort: the carrier a child is forgotten into. -/
def noLines : (fam : EffFam) → Program.Lines fam := fun _ _ _ => []

/-- **A text of a line that reads no child**: its answer on any arguments is its answer on them
with every child forgotten. -/
def ChildBlind (text : String → List (ArgF NativeOp Program.Lines) → String) : Prop :=
  ∀ ctor (args : List (ArgF NativeOp Program.Lines)),
    text ctor args = text ctor (args.map (Algebra.mapChild fun fam _ => noLines fam))

/-- A line with its text along an edit. -/
def retext (memo : Memo) (edited : Option (List Nat)) (n : Program.Node) : Program.Node :=
  { n with text := textOf memo edited n.path fun _ => n.text }

/-- Mapping a child twice maps it by the composite. A step of `linesWith_map`. -/
theorem mapChild_mapChild {R S T : EffFam → Type} (f : (fam : EffFam) → R fam → S fam)
    (g : (fam : EffFam) → S fam → T fam) (a : ArgF NativeOp R) :
    Algebra.mapChild g (Algebra.mapChild f a) = Algebra.mapChild (fun fam x => g fam (f fam x)) a := by
  cases a <;> rfl

/-- The children of mapped arguments are the mapped children. A step of `linesWith_map`. -/
theorem filterMap_childLines_map (f : (List Nat → Nat → List Program.Node) → List Nat → Nat → List Program.Node) :
    ∀ (args : List (ArgF NativeOp Program.Lines)),
      (args.map (Algebra.mapChild fun _ r => f r)).filterMap Program.childLines =
        (args.filterMap Program.childLines).map f
  | [] => rfl
  | a :: rest => by
    cases a <;> simp only [List.map_cons, List.filterMap_cons, Algebra.mapChild, Program.childLines,
      filterMap_childLines_map f rest]

/-- The operation of mapped arguments is the operation. A step of `linesWith_map`. -/
theorem findSome_argOp_map {R S : EffFam → Type} (f : (fam : EffFam) → R fam → S fam) :
    ∀ (args : List (ArgF NativeOp R)), (args.map (Algebra.mapChild f)).findSome? Program.argOp =
      args.findSome? Program.argOp
  | [] => rfl
  | a :: rest => by
    cases a <;> simp only [List.map_cons, List.findSome?_cons, Algebra.mapChild, Program.argOp,
      findSome_argOp_map f rest]

/-- **The lines along an edit are the fresh lines, each retexted** from the memo outside the edited
subtree. For every text of a line that reads no child. By fusion of the two folds
(`Algebra.cata_fusion`): a map after the fresh fold that commutes with each layer. A step of the
text law (`linesWith_eq`); placement: concept `initial-algebras-folds`, R14's live authoring. -/
theorem linesWith_map (text : String → List (ArgF NativeOp Program.Lines) → String) (hb : ChildBlind text)
    (memo : Memo) (edited : Option (List Nat)) (program : Eff NativeOp) :
    linesWith text memo edited program = (freshLines text program).map (retext memo edited) := by
  have h := Algebra.cata_fusion (Program.layerWith text) (layerAt text memo edited)
    (fun _ r p d => (r p d).map (retext memo edited)) (fun fam ctor args => by
      funext p d
      have hmap := filterMap_childLines_map (fun r p d => (r p d).map (retext memo edited)) args
      have htext : text ctor (args.map (Algebra.mapChild fun _ r p d => (r p d).map (retext memo edited))) =
          text ctor args := by
        rw [hb ctor args, hb ctor (args.map _), List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        cases a <;> rfl
      simp only [Program.layerWith, layerAt, hmap, htext, findSome_argOp_map, List.zipIdx_map,
        List.flatMap_map]
      split
      · simp only [List.map_flatMap, Prod.map_fst, Prod.map_snd, id_eq]
      · simp only [List.map_cons, retext, List.map_flatMap, Prod.map_fst, Prod.map_snd, id_eq]) .eff program
  exact (congrFun (congrFun h []) 0).symm

/-- **A memo valid outside `a`** for a program's lines: every text it keeps at the address of a line
outside the subtree at `a` is that line's text. -/
def MemoValid (memo : Memo) (a : List Nat) (ls : List Program.Node) : Prop :=
  ∀ n ∈ ls, a.isPrefixOf n.path = false → ∀ s, memo.textAt? n.path = some s → s = n.text

/-- **The text law.** Under a memo valid outside `a`, the lines along an edit at `a` are the fresh
lines: the incremental fold is the fold. For every text of a line that reads no child; the view's
text (`ownText`) reads none. A tool law; its consumer is the live step (`Tools.View.Live.page`).
Placement: concept `initial-algebras-folds`, R14's live authoring. -/
theorem linesWith_eq (text : String → List (ArgF NativeOp Program.Lines) → String) (hb : ChildBlind text)
    (memo : Memo) (a : List Nat) (program : Eff NativeOp) (hv : MemoValid memo a (freshLines text program)) :
    linesWith text memo (some a) program = freshLines text program := by
  rw [linesWith_map text hb]
  conv => rhs; rw [← List.map_id (freshLines text program)]
  apply List.map_congr_left
  intro n hn
  simp only [retext, textOf, id]
  cases hp : a.isPrefixOf n.path with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    cases hs : memo.textAt? n.path with
    | none => rfl
    | some s => simp only [hv n hn hp s hs]

/-! ## The memo a frame leaves -/

/-- The memo a frame leaves answers each address with its first line's text. A step of
`next_valid`. -/
theorem next_textAt (ls : List Program.Node) (q : List Nat) :
    (Memo.next ls).textAt? q = (ls.find? fun n => decide (n.path = q)).map (·.text) := by
  unfold Memo.next Memo.textAt?
  induction ls with
  | nil => exact KeyMap.get?_empty q
  | cons n ns ih =>
    simp only [List.foldr_cons] at ih ⊢
    rw [KeyMap.get?_insert, ih, List.find?_cons]
    by_cases h : n.path = q
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]

/-- A node as a node of the program family, by its sort. -/
def ofFam : (fam : EffFam) → EffSelfCarrier NativeOp fam → Node NativeOp
  | .eff, e => .eff e
  | .stmt, e => .stmt e
  | .stmts, e => .stmts e
  | .effs, e => .effs e
  | .action, e => .action e
  | .layer, e => .layer e
  | .layers, e => .layers e

/-- A child argument, with its sort. -/
def childArg : ArgF NativeOp (EffSelfCarrier NativeOp) → Option ((fam : EffFam) × EffSelfCarrier NativeOp fam)
  | .child fam c => some ⟨fam, c⟩
  | _ => none

/-- **The layer view's children are `Node.child`'s**, in order: the generated view
(`Program/LayerView.lean`) and the generated lenses (`Program/NodeLenses.lean`) read one signature.
A step of `next_valid`. -/
theorem child_view : ∀ (fam : EffFam) (e : EffSelfCarrier NativeOp fam) (i : Nat),
    (ofFam fam e).child i = (((view fam e).2.filterMap childArg)[i]?).map fun c => ofFam c.1 c.2
  | .eff, e, i => by cases e <;> rcases i with _ | _ | _ | i <;> rfl
  | .stmt, e, i => by cases e <;> rcases i with _ | _ | _ | i <;> rfl
  | .stmts, e, i => by cases e <;> rcases i with _ | _ | _ | i <;> rfl
  | .effs, e, i => by cases e <;> rcases i with _ | _ | _ | i <;> rfl
  | .action, e, i => by cases e <;> rcases i with _ | _ | _ | i <;> rfl
  | .layer, e, i => by cases e <;> rcases i with _ | _ | _ | i <;> rfl
  | .layers, e, i => by cases e <;> rcases i with _ | _ | _ | i <;> rfl

/-- A node's own text, for a text of a line: none for a spine, which writes no line; else the text
of its constructor and its arguments, every child forgotten. -/
def nodeText (text : String → List (ArgF NativeOp Program.Lines) → String) : Node NativeOp → Option String
  | .eff e => ofView .eff (view .eff e)
  | .stmt e => ofView .stmt (view .stmt e)
  | .stmts e => ofView .stmts (view .stmts e)
  | .effs e => ofView .effs (view .effs e)
  | .action e => ofView .action (view .action e)
  | .layer e => ofView .layer (view .layer e)
  | .layers e => ofView .layers (view .layers e)
where
  /-- The text of a node one layer down. -/
  ofView (fam : EffFam) (v : String × List (ArgF NativeOp (EffSelfCarrier NativeOp))) : Option String :=
    if Program.spine fam then none else some (text v.1 (v.2.map (Algebra.mapChild fun fam _ => noLines fam)))

/-- `nodeText` of a node of a sort is its text one layer down. -/
theorem nodeText_ofFam (text : String → List (ArgF NativeOp Program.Lines) → String) :
    ∀ (fam : EffFam) (e : EffSelfCarrier NativeOp fam), nodeText text (ofFam fam e) = nodeText.ofView text fam (view fam e)
  | .eff, _ | .stmt, _ | .stmts, _ | .effs, _ | .action, _ | .layer, _ | .layers, _ => rfl

/-- **A child's update keeps its parent's own text**: `setChild` changes a child argument alone. A
step of `next_valid`. -/
theorem nodeText_setChild (text : String → List (ArgF NativeOp Program.Lines) → String)
    {node result child : Node NativeOp} {i : Nat} (h : node.setChild i child = some result) :
    nodeText text result = nodeText text node := by
  unfold Node.setChild at h
  split at h <;> cases h
  all_goals rfl

/-- A member of a list's entries from `k` stands at its position, past `k`. A step of
`mem_lines_at`. -/
theorem getElem?_of_mem_zipIdx {α : Type} : ∀ (l : List α) (k : Nat) (x : α) (i : Nat),
    (x, i) ∈ l.zipIdx k → k ≤ i ∧ l[i - k]? = some x
  | [], _, _, _, h => absurd h List.not_mem_nil
  | y :: ys, k, x, i, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨Nat.le_refl i, by rw [Nat.sub_self]; rfl⟩
    · obtain ⟨hk, hx⟩ := getElem?_of_mem_zipIdx ys (k + 1) x i h
      refine ⟨Nat.le_of_succ_le hk, ?_⟩
      have hi : i - k = (i - (k + 1)) + 1 := by omega
      rw [hi]
      exact hx

/-- The children of folded arguments are the folds of the children. A step of `mem_lines_at`. -/
theorem filterMap_childLines_fold (alg : EffAlgebra NativeOp Program.Lines) :
    ∀ (args : List (ArgF NativeOp (EffSelfCarrier NativeOp))),
      (args.map (ArgF.fold alg)).filterMap Program.childLines =
        (args.filterMap childArg).map fun c => cataFam alg c.1 c.2
  | [] => rfl
  | a :: rest => by
    cases a <;> simp only [List.map_cons, List.filterMap_cons, ArgF.fold, Program.childLines, childArg,
      filterMap_childLines_fold alg rest, List.map_cons]

/-- A line of a layer is its node's own line, or a line of one of its children. A step of
`mem_lines_at`. -/
theorem mem_layerWith (text : String → List (ArgF NativeOp Program.Lines) → String) (fam : EffFam)
    (ctor : String) (args : List (ArgF NativeOp Program.Lines)) (p : List Nat) (d : Nat) (n : Program.Node)
    (h : n ∈ Program.layerWith text fam ctor args p d) :
    (Program.spine fam = false ∧ n.path = p ∧ n.text = text ctor args) ∨
      ∃ r i, (r, i) ∈ (args.filterMap Program.childLines).zipIdx ∧
        n ∈ r (p ++ [i]) (if Program.spine fam then d else d + 1) := by
  unfold Program.layerWith at h
  by_cases hs : Program.spine fam = true
  · simp only [hs, if_true] at h
    obtain ⟨⟨r, i⟩, hri, hn⟩ := List.mem_flatMap.mp h
    exact .inr ⟨r, i, hri, by simp only [hs, if_true]; exact hn⟩
  · have hf : Program.spine fam = false := by
      cases hb : Program.spine fam with
      | true => exact absurd hb hs
      | false => rfl
    simp only [hf, Bool.false_eq_true, if_false, List.mem_cons] at h
    rcases h with h | h
    · exact .inl ⟨hf, by rw [h], by rw [h]⟩
    · obtain ⟨⟨r, i⟩, hri, hn⟩ := List.mem_flatMap.mp h
      exact .inr ⟨r, i, hri, by simp only [hf, Bool.false_eq_true, if_false]; exact hn⟩

/-- **Every line of a program is its node's own line at its address**: the node at the line's
address writes the line's text. For every text of a line that reads no child, at every sort. A
step of `next_valid`. -/
theorem mem_lines_at (text : String → List (ArgF NativeOp Program.Lines) → String) (hb : ChildBlind text)
    (fam : EffFam) (e : EffSelfCarrier NativeOp fam) (p : List Nat) (d : Nat) (n : Program.Node)
    (h : n ∈ Algebra.fold (Program.layerWith text) fam e p d) :
    ∃ q m, n.path = p ++ q ∧ (ofFam fam e).at_ q = some m ∧ nodeText text m = some n.text := by
  have hfold : Algebra.fold (Program.layerWith text) fam e = Program.layerWith text fam (view fam e).1
      ((view fam e).2.map (ArgF.fold (EffAlgebra.ofLayer (Program.layerWith text)))) :=
    cata_build (Program.layerWith text) fam (view fam e).1 (view fam e).2 e (build_view fam e)
  rw [hfold] at h
  rcases mem_layerWith text fam _ _ p d n h with ⟨hs, hpath, htext⟩ | ⟨r, i, hri, hn⟩
  · refine ⟨[], ofFam fam e, by rw [hpath, List.append_nil], rfl, ?_⟩
    rw [nodeText_ofFam]
    unfold nodeText.ofView
    rw [hs, htext, hb (view fam e).1
      ((view fam e).2.map (ArgF.fold (EffAlgebra.ofLayer (Program.layerWith text)))), List.map_map]
    simp only [Bool.false_eq_true, if_false, Option.some.injEq]
    congr 1
    apply List.map_congr_left
    intro a _
    cases a <;> rfl
  · rw [filterMap_childLines_fold] at hri
    obtain ⟨_, hget⟩ := getElem?_of_mem_zipIdx _ 0 r i hri
    rw [Nat.sub_zero, List.getElem?_map] at hget
    cases hc : ((view fam e).2.filterMap childArg)[i]? with
    | none => rw [hc] at hget; cases hget
    | some c =>
      rw [hc, Option.map_some, Option.some.injEq] at hget
      have hchild : (ofFam fam e).child i = some (ofFam c.1 c.2) := by
        rw [child_view, hc]
        rfl
      -- the child lens's measure reads an operation's default size (`Node.sizeOf_child_lt`)
      have : @sizeOf (Node NativeOp) (@Node._sizeOf_inst NativeOp (instSizeOfDefault NativeOp)) (ofFam c.1 c.2) <
          @sizeOf (Node NativeOp) (@Node._sizeOf_inst NativeOp (instSizeOfDefault NativeOp)) (ofFam fam e) :=
        Node.sizeOf_child_lt _ _ _ hchild
      rw [← hget] at hn
      obtain ⟨q, m, hpath, hat, htext⟩ := mem_lines_at text hb c.1 c.2 (p ++ [i]) _ n hn
      refine ⟨i :: q, m, by rw [hpath, List.append_assoc]; rfl, ?_, htext⟩
      simp only [Node.at_, hchild, Option.bind_some]
      exact hat
termination_by @sizeOf (Node NativeOp) (@Node._sizeOf_inst NativeOp (instSizeOfDefault NativeOp)) (ofFam fam e)
decreasing_by exact this

/-- An address outside the subtree at `a` stands above `a`, or leaves `a`'s path at some child. A
step of `nodeText_outside`. -/
theorem outside_cases : ∀ (a q : List Nat), a.isPrefixOf q = false →
    (∃ i rest, a = q ++ i :: rest) ∨
      ∃ c i j rest other, i ≠ j ∧ a = c ++ i :: rest ∧ q = c ++ j :: other
  | [], _, h => by simp only [List.isPrefixOf] at h; cases h
  | i :: rest, [], _ => .inl ⟨i, rest, rfl⟩
  | i :: rest, j :: other, h => by
    by_cases hij : i = j
    · subst hij
      have h' : rest.isPrefixOf other = false := by
        simp only [List.isPrefixOf, show (i == i) = true from decide_eq_true rfl, Bool.true_and] at h
        exact h
      rcases outside_cases rest other h' with ⟨k, r, rfl⟩ | ⟨c, k, l, r, o, hkl, rfl, rfl⟩
      · exact .inl ⟨k, r, rfl⟩
      · exact .inr ⟨i :: c, k, l, r, o, hkl, rfl, rfl⟩
    · exact .inr ⟨[], i, j, rest, other, hij, rfl, rfl⟩

/-- **An edit at `a` keeps every node's own text outside the subtree at `a`**: a node above `a`
has a child replaced, and a node beside `a`'s path is untouched. A step of `next_valid`. -/
theorem nodeText_outside (text : String → List (ArgF NativeOp Program.Lines) → String)
    {root root' r : Node NativeOp} {a q : List Nat} (hedit : root.replaceAt a r = some root')
    (hq : a.isPrefixOf q = false) {m m' : Node NativeOp} (hm : root.at_ q = some m)
    (hm' : root'.at_ q = some m') : nodeText text m' = nodeText text m := by
  rcases outside_cases a q hq with ⟨i, rest, rfl⟩ | ⟨c, i, j, rest, other, hij, rfl, rfl⟩
  · rw [Node.replaceAt_append, hm, Option.bind_some] at hedit
    cases hm'' : m.replaceAt (i :: rest) r with
    | none => rw [hm''] at hedit; cases hedit
    | some m'' =>
      rw [hm'', Option.bind_some] at hedit
      rw [(Node.replaceAt_spec hedit).1, Option.some.injEq] at hm'
      subst hm'
      simp only [Node.replaceAt] at hm''
      cases hc : m.child i with
      | none => rw [hc] at hm''; cases hm''
      | some cm =>
        rw [hc, Option.bind_some] at hm''
        cases hcr : cm.replaceAt rest r with
        | none => rw [hcr] at hm''; cases hm''
        | some cm' =>
          rw [hcr, Option.bind_some] at hm''
          exact nodeText_setChild text hm''
  · have := Node.at_replaceAt_disjoint c rest other hedit (Ne.symm hij)
    rw [this, hm, Option.some.injEq] at hm'
    rw [hm']

/-- **The memo a frame leaves is valid for the next program**, after any edit at `a`: a fill, or an
omit, which fills the address with a hole. For every text of a line that reads no child. A tool
law; with the text law it makes the live step's lines the fresh lines at every step. Placement:
concept `initial-algebras-folds`, R14's live authoring. -/
theorem next_valid (text : String → List (ArgF NativeOp Program.Lines) → String) (hb : ChildBlind text)
    {old new : NativeEff} {a : List Nat} {r : Node NativeOp}
    (hedit : (Node.eff old).replaceAt a r = some (Node.eff new)) :
    MemoValid (Memo.next (freshLines text old)) a (freshLines text new) := by
  intro n hn hq s hs
  rw [next_textAt] at hs
  cases hf : (freshLines text old).find? (fun m => decide (m.path = n.path)) with
  | none => rw [hf] at hs; cases hs
  | some n0 =>
    rw [hf, Option.map_some, Option.some.injEq] at hs
    subst hs
    have hp := List.find?_some hf
    have hpath : n0.path = n.path := of_decide_eq_true hp
    have hn0 := List.mem_of_find?_eq_some hf
    obtain ⟨q0, m0, hp0, hat0, ht0⟩ := mem_lines_at text hb .eff old [] 0 n0 hn0
    obtain ⟨q1, m1, hp1, hat1, ht1⟩ := mem_lines_at text hb .eff new [] 0 n hn
    rw [List.nil_append] at hp0 hp1
    subst hp1
    rw [hpath] at hp0
    subst hp0
    have := nodeText_outside text hedit hq hat0 hat1
    rw [ht1, ht0, Option.some.injEq] at this
    exact this.symm

end Tools.View.Inc
