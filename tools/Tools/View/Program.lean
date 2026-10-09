import Tools.View.Page
import Tools.View.Algebra
import Tools.Code.Module
import Effect4.Program.LayerView
import Effect4.Program.Edit
import Effect4.Codegen.PrintLeaf

/-!
# A program as lines, and the page of an edit session

Slice V1 of the visual pipeline (`docs/research/2026-10-09-visual-pipeline.md`). A program's
lines are one generic layer, folded (`EffAlgebra.ofLayer`, `Program/LayerView.lean`): each node
writes its own line from its constructor's name and its arguments that are no child, and then
its children's lines at their addresses. A term's text is the fold of the term algebra. No
traversal here matches on a constructor of `Eff`: the generated layer names them.

The text of a line transcribes the native view probe's (`ViewLines`,
`docs/research/2026-10-06-native-view-probe/Lines.lean`), with one more argument sort: a
definition block's declarations (`ArgF.decls`, procedures, decisions row 328).

The page of an edit session joins those lines with the session's address table: the type of
each typed address, the refusal at the address it locates, and the name of each hole.
-/

/-! The `Repr` texts that a line writes. The core derives none for these types; this tool
derives them for its own texts, as the probe did. -/
deriving instance Repr for Effect4.Program.Term
deriving instance Repr for Effect4.Program.CauseTerm
deriving instance Repr for Effect4.Supervision.MaskMode
deriving instance Repr for Effect4.Supervision.ObserverMode
deriving instance Repr for Effect4.Supervision.ForkOptions
deriving instance Repr for Effect4.FinalizerStrategy
deriving instance Repr for Effect4.Program.NativeOp

namespace Tools.View.Program

open Effect4 Effect4.Program Tools.View

/-- One line of a program: its address, its depth on the page, its text, and the operation a
`perform` names. -/
structure Node where
  path : List Nat
  depth : Nat
  text : String
  op : Option NativeOp := none

/-- The carrier of the fold: the lines of a subtree, given the subtree's own address and depth. -/
abbrev Lines (_ : EffFam) : Type := List Nat → Nat → List Node

/-- A family whose nodes are the spine of a list: statements, programs and layers. A spine node
is the encoding of a list, not a step of the program, so it writes no line of its own, and its
items stand at one depth. Its address still keys each item's line. -/
def spine : EffFam → Bool
  | .stmts | .effs | .layers => true
  | _ => false

/-- An address as the design language writes it: `[1 1 0]`. -/
def bracket (p : List Nat) : String := "[" ++ " ".intercalate (p.map toString) ++ "]"

/-- A `Repr` text without its namespaces, on one line. -/
def plain (s : String) : String :=
  let short := ["Effect4.Program.", "Effect4.Supervision.", "Effect4.Machine.", "Effect4.",
    "Term.", "Terms.", "Lit.", "NativeOp.", "CauseTerm.", "Ty.", "Decision.", "FnName.",
    "ObserverMode.", "MaskMode.", "ScopeStrategy."].foldl (fun acc pre => acc.replace pre "") s
  " ".intercalate ((short.replace "\n" " " |>.replace "\t" " ").splitOn " " |>.filter (· ≠ ""))

/-- An argument of several words stands in parentheses, as in the sexp form. -/
def paren (s : String) : String := if s.contains ' ' && !s.startsWith "{" then "(" ++ s ++ ")" else s

/-- A literal: the value alone. -/
def litText (l : Lit) : String :=
  let t := plain (reprStr l)
  if t == "unit" then "()"
  else ["nat ", "str ", "bool "].foldl
    (fun acc pre => if acc.startsWith pre then (acc.drop pre.length).toString else acc) t

/-- A term in the sexp form of the design language, as a fold of the generated term algebra.
The argument spine of an application is written as the arguments in order. -/
def termAlgebra : TermAlgebra (fun | .term => String | .terms => List String) where
  term_var v := s!"(var {plain (reprStr v)})"
  term_lit l := s!"(lit {litText l})"
  term_app name args := "(" ++ " ".intercalate (name :: args) ++ ")"
  term_record fields order args :=
    let names := " ".intercalate (fields.map fun f => if f.2.1 then f.1 ++ "?" else f.1)
    "(" ++ " ".intercalate (["record", "{" ++ names ++ "}", "[" ++ " ".intercalate order ++ "]"] ++ args) ++ ")"
  term_field mode t name := s!"(field {plain (reprStr mode)} {t} {name})"
  term_recordSet t name v := s!"(recordSet {t} {name} {v})"
  term_tupleAt t i := s!"(tupleAt {t} {i})"
  term_fold ty a b c :=
    "(" ++ " ".intercalate (["fold"] ++ (ty.map fun t => [t.render]).getD [] ++ [a, b, c]) ++ ")"
  terms_nil := []
  terms_cons t ts := t :: ts

/-- A term's text. -/
def termText (t : Term) : String := cata_term termAlgebra t

/-- The text of one argument that is no child. -/
def argText {R : EffFam → Type} : ArgF NativeOp R → Option String
  | .child _ _ => none
  | .term v => some (termText v)
  | .cause v => some (paren (plain (reprStr v)))
  | .op v => some (paren (plain (reprStr v)))
  | .nat v => some (toString v)
  | .mode v => some (paren (plain (reprStr v)))
  | .bool v => some (toString v)
  | .key v => some (keyText v)
  | .decision v => some (paren (plain (reprStr v)))
  | .optTy v => v.map fun t => t.render
  | .decls v => some ("{" ++ " ".intercalate (v.map fun d => d.name) ++ "}")
  | .forkOptions v => some (paren (plain (reprStr v)))
  | .optTerm v => v.map termText
  | .lit v => some (paren (plain (reprStr v)))
  | .path v => some (bracket v)

/-- The operation of an argument, when it is one. -/
def argOp {R : EffFam → Type} : ArgF NativeOp R → Option NativeOp
  | .op v => some v
  | _ => none

/-- The lines a child argument holds; a leaf holds none. -/
def childLines : ArgF NativeOp Lines → Option (List Nat → Nat → List Node)
  | .child _ r => some r
  | _ => none

/-- One generic layer, the text of a node's own line given by `text`: the node's own line, then
its children's lines one level deeper. A spine node writes no line, and its children stand at
its depth. A child's index counts the child arguments alone, which is `Node.child`'s indexing. -/
def layerWith (text : String → List (ArgF NativeOp Lines) → String) (fam : EffFam) (ctor : String)
    (args : List (ArgF NativeOp Lines)) : Lines fam :=
  fun p d =>
    let inner := if spine fam then d else d + 1
    let children := (args.filterMap childLines).zipIdx.flatMap fun (r, i) => r (p ++ [i]) inner
    if spine fam then children
    else ⟨p, d, text ctor args, args.findSome? argOp⟩ :: children

/-- A node's own text: its constructor's name, then its arguments that are no child. -/
def ownText {R : EffFam → Type} (ctor : String) (args : List (ArgF NativeOp R)) : String :=
  " ".intercalate (ctor :: args.filterMap argText)

/-- The layer of the view: each line's text is its node's own text. -/
def layer : (fam : EffFam) → String → List (ArgF NativeOp Lines) → Lines fam := layerWith (ownText (R := Lines))

/-- A program's lines, in the order of its addresses. -/
def lines (program : Eff NativeOp) : List Node :=
  cata_eff (EffAlgebra.ofLayer layer) program [] 0

/-! ## Equivariance: a subtree's lines anywhere are its lines at the root, moved

Slice A of the view plane's algebra audit (`docs/research/2026-10-09-view-algebra-audit.md`,
finding F2). The lines' fold takes an address and a depth in. Folded at any address and depth,
a program's lines are its lines at the root, each under that address and that depth
(`lines_at`). This is the move law's twin for the program (`lowerCall_move`): it is why a splice
redraws its own subtree and no other line. The proof is fold induction (`cata_keeps`): each
layer keeps the property when its children have it. The law holds whatever text a line shows
(`layerWith`), so it rests on no axiom of the text's string functions. -/

/-- A line under an address and a depth: its address gains `p` as a prefix, its depth gains `d`. -/
def Node.under (p : List Nat) (d : Nat) (n : Node) : Node :=
  { n with path := p ++ n.path, depth := d + n.depth }

/-- A line under one address and then another is under their join. -/
theorem Node.under_under (p q : List Nat) (d e : Nat) (n : Node) :
    (n.under q e).under p d = n.under (p ++ q) (d + e) := by
  simp only [Node.under, List.append_assoc, Nat.add_assoc]

/-- Lines that move: at every address and depth, they are the lines at the root, moved there. -/
def Moves (r : List Nat → Nat → List Node) : Prop := ∀ p d, r p d = (r [] 0).map (Node.under p d)

/-- Two maps of a list's items agree when they agree on each item. -/
theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- **Each layer keeps the move**: a node's lines move when its children's lines do. -/
theorem layer_moves (text : String → List (ArgF NativeOp Lines) → String) (fam : EffFam) (ctor : String)
    (args : List (ArgF NativeOp Lines)) (h : ∀ a ∈ args, Algebra.childOk (fun _ r => Moves r) a) :
    Moves (layerWith text fam ctor args) := by
  have hc : ∀ x ∈ (args.filterMap childLines).zipIdx, Moves x.1 := by
    intro x hx
    obtain ⟨a, ha, hr⟩ := List.mem_filterMap.mp (List.fst_mem_of_mem_zipIdx hx)
    cases a with
    | child fam' r =>
      cases hr
      exact h _ ha
    | _ => cases hr
  have kids (p : List Nat) (d k : Nat) :
      ((args.filterMap childLines).zipIdx.flatMap fun x => x.1 (p ++ [x.2]) (d + k)) =
        ((args.filterMap childLines).zipIdx.flatMap fun x => x.1 [x.2] k).map (Node.under p d) := by
    rw [List.map_flatMap]
    refine flatMap_congr_mem fun x hx => ?_
    rw [hc x hx (p ++ [x.2]), hc x hx [x.2], List.map_map]
    congr 1
    funext n
    simp only [Function.comp, Node.under_under]
  intro p d
  simp only [layerWith]
  cases hs : spine fam with
  | true =>
    simp only [↓reduceIte, List.nil_append]
    have := kids p d 0
    simp only [Nat.add_zero] at this
    exact this
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, Nat.zero_add, List.map_cons]
    rw [kids p d 1]
    simp only [Node.under, List.append_nil, Nat.add_zero]

/-- **Equivariance of the lines**: a program's lines, folded at any address and depth, are its
lines at the root, each under that address and depth. At every sort of the family, for every
text of a line. -/
theorem lines_at (text : String → List (ArgF NativeOp Lines) → String) (fam : EffFam)
    (e : EffSelfCarrier NativeOp fam) (p : List Nat) (d : Nat) :
    cataFam (EffAlgebra.ofLayer (layerWith text)) fam e p d =
      (cataFam (EffAlgebra.ofLayer (layerWith text)) fam e [] 0).map (Node.under p d) :=
  Algebra.cata_keeps (layerWith text) (fun _ r => Moves r) (layer_moves text) fam e p d

/-! ## The page of an edit session -/

/-- A refusal's reason: the name of its kind (`TypeReason.head`). -/
def reasonText (r : TypeRefusal) : String := r.reason.head

/-- The name of the hole a line performs, when it performs one: a host row at a position past
the application's rows. -/
def holeName (l : EditSession) (n : Node) : Option String :=
  match n.op with
  | some (.external k) =>
    if l.app.rows.length ≤ k then (l.sketch.holes[k - l.app.rows.length]?).map (·.name) else none
  | _ => none

/-- How a row is answered, as a mark (the forms note, section 5): a synchronous row keeps its
promise within the step; a deferred one parks and resumes; an external one parks, and the host
decides its answer. A program row has no mark here. -/
def rowMark (row : Row) : Option Mark :=
  match row.kind, row.registration with
  | .sync, _ => some [.filled]
  | .async, .deferred => some [.hollow, .dotted, .filled]
  | .async, .external => some [.hollow, .dotted, .bar, .filled]
  | .program, _ => none

/-- The page of an edit session: one line for each node of its sketch, with the type of each
typed address, the refusal at the address it locates, each hole's name, and the mark of each
operation, by its row in the session's table (`nativeRowOf`). The lines under `lit` are lit. -/
def sessionPage (l : EditSession) (lit : Option (List Nat)) (title judgment place foot : String) :
    Page :=
  let line (n : Node) : Tools.View.Line :=
    let entry := l.table.find? fun e => decide (e.path = n.path)
    let result := entry.bind (·.result)
    let refusedHere := match result with
      | some (.error r) => decide (r.path = n.path)
      | _ => false
    let state : LineState :=
      if refusedHere then .refused
      else match lit with
        | some a => if a.isPrefixOf n.path then .lit else .plain
        | none => .plain
    let type := match result with
      | some (.ok t) => Tools.Code.effTyText t
      | _ => ""
    let note := match result with
      | some (.error r) => if refusedHere then "refused: " ++ reasonText r else ""
      | _ => ""
    let text := match holeName l n with
      | some h => "hole " ++ h
      | none => n.text
    let mark := n.op.bind fun op => rowMark (nativeRowOf (l.app.withHoles l.sketch.holes).rows op)
    { gutter := bracket n.path, depth := n.depth, text, type, mark, note, key := bracket n.path, state }
  { title, judgment, place, foot, lines := ((lines l.sketch.program).map line).toArray }

/-! ## The code plane and the tree's text -/

/-- The code plane of a program in the view: its TypeScript at the plane's width (`Tools.Code`), or
why it has none. -/
def codePanel (program : NativeEff) (table : RowTable) (holes : List String := []) : Option CodePanel :=
  match Tools.Code.codeLines CODE_WIDTH program table holes with
  | .ok lines => some { head := "typescript", lines := lines.toArray }
  | .error why => some { head := "typescript", lines := #["no module: " ++ why] }

/-- A program's tree as the terminal page writes it: address, node and type, one node a line. -/
def treeText (name : String) (program : NativeEff) : String :=
  "\n".intercalate (pageText (sessionPage (EditSession.open {} { program }) none name "" "" "")) ++ "\n"

end Tools.View.Program
