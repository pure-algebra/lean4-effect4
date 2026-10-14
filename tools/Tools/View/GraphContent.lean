import Tools.View.Program
import Tools.View.KeyMap

/-!
# Source content for graph nodes

The generated layer supplies constructor names and ordered arguments.
This fold retains them at the same addresses and depths as `Program.lines`.
Child arguments retain their sorts, without retaining another program tree.
Session metadata records typing observations and declared operation rows, never runtime state.
Text formatting remains in `Program.argText` and `Program.ownText`.
-/

set_option autoImplicit false

namespace Tools.View.GraphContent

open Effect4 Effect4.Program

/-- One original argument, with a placeholder for each folded child. -/
abbrev Argument := ArgF NativeOp (fun _ => Unit)

/-- Constructor content at one source address, before typography or visual role assignment. -/
structure Node where
  path : List Nat
  depth : Nat
  family : EffFam
  ctor : String
  arguments : List Argument
  op : Option NativeOp

/-- The existing view key for this address. No consumer needs to parse its spelling. -/
def Node.key (n : Node) : Key := Program.bracket n.path

private abbrev Content (_ : EffFam) := List Nat → Nat → List Node

/-- Erase only the child carrier. Argument order, child family, and original values remain. -/
def argument {R : EffFam → Type} : ArgF NativeOp R → Argument
  | .child fam _ => .child fam ()
  | .term v => .term v
  | .cause v => .cause v
  | .op v => .op v
  | .nat v => .nat v
  | .mode v => .mode v
  | .bool v => .bool v
  | .key v => .key v
  | .decision v => .decision v
  | .optTy v => .optTy v
  | .decls v => .decls v
  | .forkOptions v => .forkOptions v
  | .optTerm v => .optTerm v
  | .keys v => .keys v
  | .lit v => .lit v
  | .path v => .path v

private def child : ArgF NativeOp Content → Option (List Nat → Nat → List Node)
  | .child _ r => some r
  | _ => none

private def layer (fam : EffFam) (ctor : String)
    (args : List (ArgF NativeOp Content)) : Content fam :=
  fun path depth =>
    let inner := if Program.spine fam then depth else depth + 1
    let children := (args.filterMap child).zipIdx.flatMap fun (r, i) =>
      r (path ++ [i]) inner
    if Program.spine fam then children
    else ⟨path, depth, fam, ctor, args.map argument, args.findSome? Program.argOp⟩ :: children

/-- Project syntax content in source order, with the existing line-address convention. -/
def ofProgram (p : NativeEff) : List Node :=
  cata_eff (EffAlgebra.ofLayer layer) p [] 0

/-- An operation value and its address-local row, when that signature declares the operation. -/
structure Operation where
  value : NativeOp
  row : Option Row

/-- Content with optional typing and display metadata. Absence never means the type `never`. -/
structure Entry where
  node : Node
  typing : Option Table.Entry
  operation : Option Operation
  typeText : Option String := none

private def operationAt (session : EditSession) (n : Node) : Option Operation :=
  n.op.map fun op =>
    let sig := session.sketch.sigAt session.app n.path
    ⟨op, if sig.dom op then some (sig.rowOf op) else none⟩

/-- Join source content with the first table entry at its exact address.
This reads the supplied session table; it does not assert session coherence. -/
def ofSession (session : EditSession) : List Entry :=
  let table := KeyMap.firstBy Table.Entry.path session.table
  (ofProgram session.sketch.program).map fun n =>
    ⟨n, table.get? n.path, operationAt session n, none⟩

/-- Add the supplied page's first type text at each explicit key.
The page may differ from the session; raw typing remains a separate field. -/
def ofSessionPage (session : EditSession) (page : Page) : List Entry :=
  let lines := KeyMap.firstBy Line.key page.lines.toList
  (ofSession session).map fun e =>
    { e with typeText := (lines.get? e.node.key).map (·.type) }

end Tools.View.GraphContent
