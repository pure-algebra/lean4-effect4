import Lean

/-!
# Effect4Gen.Check — the projection guard on a generated file

Owner: the check that a generated file still projects the environment it was generated from.

It re-derives the constructor and field lists of every carrier out of the Lean environment and
compares them with what the generated file actually says: the case names and their order in
each `shapeDoc`, the field names and their order and arity inside each case, and the
constructor index each `toVal` clause writes. It refuses on any difference, which is what makes
a hand edit inside a generated file, a reordered constructor upstream, a renamed field or a
dropped case a build failure rather than a silent change of every address in the store.

    lake env lean -M 4096 --run tools\Effect4Gen\Check.lean src\Effect4\Program\Derived.lean

The environment is the one the generated files elaborate in: the tool reads the `import` lines
of every file it is given and imports exactly those modules before it looks anything up.

The comparison is deliberately *independent* of `Effect4Gen.Main`: this file reads the
generated text, not the generator's intermediate representation, and finds each carrier in the
environment by its own search over `env.constants`. Two implementations of the same projection
have to agree, or the guard refuses.

What it does **not** check: the field *types* (the generator's composition rule), the proofs,
the `Content` kinds, or the bytes. Those are the emitted file's own receipts and its
acceptance guards.

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library.
-/

open Lean Meta

namespace Effect4Check

/-- One case of a shape: a constructor's short name and its field names, in order. -/
structure Case where
  name : String
  fields : List String
deriving BEq, Inhabited

def Case.render (c : Case) : String := c.name ++ "(" ++ String.intercalate ", " c.fields ++ ")"

/-- A shape as the generated file states it, or as the environment says it should be. -/
structure Skeleton where
  isStruct : Bool
  name : String
  cases : List Case
deriving Inhabited

def Skeleton.render (s : Skeleton) : String :=
  (if s.isStruct then "struct " else "sum ") ++ s.name ++ " [" ++
    String.intercalate ", " (s.cases.map Case.render) ++ "]"

/-- A struct's constructor may be spelled anything; only its field list is a projection. -/
def Skeleton.agrees (env gen : Skeleton) : Bool :=
  env.isStruct == gen.isStruct &&
    (if gen.isStruct then env.cases.map (·.fields) == gen.cases.map (·.fields)
     else env.cases == gen.cases)

/-! ## Reading the generated text -/

def bracketDepth (s : String) : Int :=
  s.foldl (fun acc c => if c == '[' then acc + 1 else if c == ']' then acc - 1 else acc) 0

/--
The `("name", …` tuples of one shape body, with their bracket depth.

A `sum`'s cases sit at depth 1 and their fields at depth 2; a `struct`'s fields sit at depth 1.
A field's shape is only `.named`, `(shape T).root`, `.list`, `.option` or `.pair`, none of
which contains a bracket, so the depth separates the two levels without a parser.
-/
def scanCases (body : String) (isStruct : Bool) : List Case :=
  match body.splitOn "(\"" with
  | [] => []
  | pre :: segs => go segs (bracketDepth pre) none []
where
  go : List String → Int → Option Case → List Case → List Case
    | [], _, cur, acc => acc ++ cur.toList
    | seg :: rest, d, cur, acc =>
      let name := (seg.takeWhile (· != '"')).toString
      let tail := (seg.drop (name.length + 1)).toString
      let d' := d + bracketDepth tail
      if isStruct then
        if d == 1 then
          go rest d' (some { name := "·", fields := (cur.map (·.fields)).getD [] ++ [name] }) acc
        else go rest d' cur acc
      else if d == 1 then
        go rest d' (some { name := name, fields := [] }) (acc ++ cur.toList)
      else if d == 2 then
        go rest d' (cur.map fun k => { k with fields := k.fields ++ [name] }) acc
      else go rest d' cur acc

/-- The head of a `.sum "N"` / `.struct "N"` in a body, whichever comes first. -/
def shapeHead (body : String) : Option (Bool × String) :=
  let quoted (marker : String) : Option (Nat × String) :=
    match body.splitOn marker with
    | pre :: seg :: _ => some (pre.length, (seg.takeWhile (· != '"')).toString)
    | _ => none
  match quoted ".struct \"", quoted ".sum \"" with
  | some (i, n), some (j, m) => if i < j then some (true, n) else some (false, m)
  | some (_, n), none => some (true, n)
  | none, some (_, m) => some (false, m)
  | none, none => none

/-- Every shape a generated file declares: the body of each `def …Shape : Shape :=` and of each
`def shapeDoc : ShapeDoc :=`, up to the blank line the generator always leaves after it. -/
def fileShapes (lines : Array String) : List Skeleton := Id.run do
  let mut out : List Skeleton := []
  let mut i := 0
  while i < lines.size do
    let l := lines[i]!
    if (l.startsWith "def " && l.endsWith "Shape : Shape :=") ||
        l == "def shapeDoc : ShapeDoc :=" then
      let mut body := ""
      let mut j := i + 1
      while j < lines.size && lines[j]! != "" do
        body := body ++ "\n" ++ lines[j]!
        j := j + 1
      if let some (isStruct, name) := shapeHead body then
        out := out ++ [{ isStruct, name, cases := scanCases body isStruct }]
      i := j
    else
      i := i + 1
  return out

/-- The constructor index each `toVal` clause writes, keyed by the member the definition
belongs to: `toValEff` and `EffC.toVal` both key as `Eff`. A shared constructor name — `fail`
is `Eff`'s second and `CauseTerm`'s first — is why the keys are needed. -/
def fileCtorIndices (lines : Array String) : List (String × String × Nat) := Id.run do
  let mut out : List (String × String × Nat) := []
  let mut ns := ""
  let mut key := ""
  for l in lines do
    if l.startsWith "namespace " then
      ns := (l.drop 10).toString
    else if l.startsWith "def toVal" then
      let defName := ((l.drop 4).takeWhile (fun c => c != ' ')).toString
      key := if defName == "toVal" then
          (if ns.endsWith "C" then (ns.dropEnd 1).toString else ns)
        else (defName.drop 5).toString
    else if l.startsWith "  | ." then
      match l.splitOn " => .ctor " with
      | [lhs, rhs] =>
        let ctor := ((lhs.drop 5).takeWhile (fun c => c != ' ')).toString
        out := out ++ [(key, ctor, (rhs.takeWhile Char.isDigit).toString.toNat!)]
      | _ => pure ()
  return out

/-- The `import` lines of a generated file: the modules it elaborates in. -/
def fileImports (lines : Array String) : List String :=
  lines.toList.filterMap fun l =>
    if l.startsWith "import " then some ((l.drop 7).copy.trimAscii.copy) else none

/-! ## Reading the environment -/

/-- The constructor and field lists of an inductive, in declaration order. -/
def envSkeleton (n : Name) : MetaM Skeleton := do
  let env ← getEnv
  let info ← getConstInfoInduct n
  let mut cases : List Case := []
  for c in info.ctors do
    let ci ← getConstInfoCtor c
    let fields ← forallTelescope ci.type fun xs _ => do
      let mut fs : List String := []
      for i in [ci.numParams:xs.size] do
        let s := (← xs[i]!.fvarId!.getUserName).toString
        fs := fs ++ [if s.isEmpty || s.any (fun ch => ch == '✝' || ch == '.')
          then s!"arg{i - ci.numParams}" else s]
      return fs
    cases := cases ++ [{ name := (c.toString.splitOn ".").getLast!, fields }]
  return { isStruct := isStructure env n, name := (n.toString.splitOn ".").getLast!, cases }

/-- Every inductive in the environment whose last name component is `short`. -/
def candidates (short : String) : MetaM (Array Name) := do
  let env ← getEnv
  let mut hits : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if !n.isInternal && (n.toString.splitOn ".").getLast! == short then
      if let .inductInfo _ := ci then hits := hits.push n
  return hits.qsort (fun a b => a.toString < b.toString)

/-- Check one generated file. Returns `true` when it refused. -/
def checkFile (path : String) : MetaM Bool := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").toArray.map (·.replace "\r" "")
  let shapes := fileShapes lines
  let indices := fileCtorIndices lines
  let mut failed := false
  if shapes.isEmpty then
    IO.println s!"REFUSED {path}: no shape declaration found"
    failed := true
  for s in shapes do
    let cands ← candidates s.name
    let mut agreed : Option Name := none
    let mut report : Array String := #[]
    for c in cands do
      let e ← envSkeleton c
      if e.agrees s then agreed := some c else report := report.push s!"      {c}: {e.render}"
    match agreed with
    | some c => IO.println s!"ok      {path}: {s.name} projects {c} ({s.cases.length} cases)"
    | none =>
      IO.println s!"REFUSED {path}: shape \"{s.name}\" projects no carrier in the environment"
      IO.println s!"        generated: {s.render}"
      for r in report do IO.println r
      failed := true
    -- Every `toVal` clause must write its constructor's declaration position.
    unless s.isStruct do
      for i in [0:s.cases.length] do
        let c := s.cases[i]!
        match indices.find? (fun p => p.1 == s.name && p.2.1 == c.name) with
        | some (_, _, j) =>
          if j != i then
            IO.println s!"REFUSED {path}: toVal writes .ctor {j} for {s.name}.{c.name}, \
which is constructor {i}"
            failed := true
        | none =>
          IO.println s!"REFUSED {path}: no toVal clause for {s.name}.{c.name}"
          failed := true
  return failed

end Effect4Check

open Effect4Check in
def main (argv : List String) : IO Unit := do
  if argv.isEmpty then
    throw (IO.userError "no generated files given")
  -- Import the union of the files' own imports: the environment each file elaborates in.
  let mut mods : Array Name := #[]
  for path in argv do
    let text ← IO.FS.readFile path
    let lines := (text.splitOn "\n").toArray.map (·.replace "\r" "")
    for m in fileImports lines do
      let n := m.toName
      unless mods.contains n do mods := mods.push n
  if mods.isEmpty then
    throw (IO.userError "the given files import nothing; nothing to check against")
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m }) {} 0
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let act : MetaM Bool := do
    let mut failed := false
    for path in argv do
      if ← checkFile path then failed := true
    return failed
  let (failed, _) ← (act.run' {}).toIO ctx { env := env }
  if failed then
    IO.println "the projection guard refused"
    IO.Process.exit 1
  else
    IO.println "the projection guard agrees"
