import Test.Api.SessionContract
import Tools.View.Glyph
open Effect4 Effect4.Program Effect4.Machine Effect4.Api Test.Api.SessionFixtures

/-! The to-do session object as relations with addresses: nodes, definitions, rows, calls. -/

def addr (p : List Nat) : String := String.intercalate "." (p.map toString)

/-- The constructor word and the op or name an argument carries, at a node. -/
def viewNode (n : Node NativeOp) : String × String × List (ArgF NativeOp (EffSelfCarrier NativeOp)) :=
  match n with
  | .eff e => let (c, a) := view_eff e; ("eff", c, a)
  | .stmts s => let (c, a) := view_stmts s; ("stmts", c, a)
  | .stmt s => let (c, a) := view_stmt s; ("stmt", c, a)
  | .action x => let (c, a) := view_action x; ("action", c, a)
  | .effs x => let (c, a) := view_effs x; ("effs", c, a)
  | .layer l => let (c, a) := view_layer l; ("layer", c, a)
  | .layers l => let (c, a) := view_layers l; ("layers", c, a)

/-- The mark of a constructor, from the glyph table. -/
def markOf (sort ctor : String) : String :=
  let ns : Lean.Name := match sort with
    | "eff" => `Effect4.Program.Eff | "stmt" => `Effect4.Program.Stmt | "stmts" => `Effect4.Program.Stmts
    | "action" => `Effect4.Program.ActionTerm | "effs" => `Effect4.Program.Effs
    | "layer" => `Effect4.Program.LayerTerm | _ => `Effect4.Program.LayerTerms
  match Tools.View.Glyph.table.find? (·.ctor == ns.str ctor) with
  | some r => r.shape.glyph ++ " " ++ r.word
  | none => "· " ++ ctor

/-- What a node names: a definition, a row, a key. -/
def names (b : Built) (args : List (ArgF NativeOp (EffSelfCarrier NativeOp))) : String :=
  let decls := b.program.defsOf
  String.intercalate " " (args.filterMap fun a => match a with
    | .op (.call k) => some s!"call {(decls[k]?.map (·.name)).getD s!"def {k}"}"
    | .op (.external i) => (externalRow b.app.rows i).map fun r => s!"row {r.spelling}"
    | .op _ => some "op"
    | .key k => some s!"key {k.service.value}"
    | .nat k => some s!"{k}"
    | _ => none)

/-- The definition whose body holds an address: the bodies are the cons spine under [0]. -/
def defOf (b : Built) (p : List Nat) : String :=
  match p with
  | 0 :: rest => let k := (rest.takeWhile (· == 1)).length
    if (rest.drop k).head? == some 0 then (b.program.defsOf[k]?.map (·.name)).getD "?" else "defs"
  | 1 :: _ => "main"
  | 2 :: _ => "layers"
  | _ => "block"

def nodeRows (b : Built) : List String :=
  let root := Node.eff b.program
  (root.addresses).filterMap fun p => (Node.at_ root p).map fun n =>
    let (sort, ctor, args) := viewNode n
    s!"{addr p}\t{defOf b p}\t{sort}\t{markOf sort ctor}\t{names b args}"

def defRows (b : Built) : List String :=
  b.program.defsOf.zipIdx.map fun (d, k) =>
    let role := match d.role with
      | .serviceInit s => s!"init of {s}" | .serviceMethod s m _ => s!"method {m} of {s}" | _ => "plain"
    s!"{k}\t{d.name}\t{role}\t{addr ([0] ++ List.replicate k 1 ++ [0])}"

def rowRows (b : Built) : List String :=
  b.app.rows.zipIdx.map fun (r, i) =>
    s!"{i}\t{r.spelling}\t{(r.spelling.splitOn ".").head?.getD ""}\t{reprStr r.request}\t{reprStr r.answer}"

def callRows (b : Built) : List String :=
  (HostSession.callTable b.program b.app).map fun (p, c) =>
    let target := match c.op with
      | .call k => s!"def\t{(b.program.defsOf[k]?.map fun (d : DefDecl) => d.name).getD "?"}\t{addr ([0] ++ List.replicate k 1 ++ [0])}"
      | .external i => s!"row\t{((externalRow b.app.rows i).map fun (r : Program.Row) => r.spelling).getD "?"}\t{i}"
      | _ => "?\t?\t"
    s!"{addr p}\t{defOf b p}\t{target}"

def write (name : String) (header : String) (rows : List String) : IO Unit :=
  IO.FS.writeFile s!"tools/view/out/view-graph/{name}.gen.tsv" (header ++ "\n" ++ String.intercalate "\n" rows ++ "\n")

def proveOut : IO Unit := do
  let some b := todoSession | throw (IO.userError "no session")
  let ns := nodeRows b
  write "nodes" "address\tin\tsort\tmark\tnames" ns
  write "defs" "k\tname\trole\tbody" (defRows b)
  write "rows" "i\tspelling\tnamespace\trequest\tanswer" (rowRows b)
  write "calls" "address\tfrom\ttargetSort\ttarget\ttargetAddress" (callRows b)
  IO.println s!"nodes {ns.length}, defs {(defRows b).length}, rows {(rowRows b).length}, calls {(callRows b).length}"

#eval proveOut
