import Lean
import OCaml5.Lcnf.Naming
import OCaml5.Ml.Syntax

/-!
# OCaml5.Lcnf.Public

**What it is.** The public face of the LCNF route (Codex's R6.2, the naming slice; slice 1.2 of
the OCaml estate plan): the manifest of every public name and the facade module made from it.

* **The manifest** (`ocaml/gen/public-names.tsv`, generated and committed) lists every public
  name: each public root of the recipe (`OCaml5.Lcnf.Export`), each program type at its owner
  (`Eff_types`) with its constructors and fields, and each sealed package of the implementation
  unit, abstract. A row gives the kind, the public path (`OCaml5.Lcnf.publicName`), the Lean
  source, the type's arity and the implementation the facade aliases.
* **The append-only check** (`breaches`) refuses a manifest that moves or drops a path of the
  committed one, at one version. A declared breaking version (the recipe's `facade.version`, a
  larger number) admits it; a smaller number is refused.
* **The facade** (`facadeModule`) is one OCaml module named by the recipe (`Effect4`) whose
  module tree follows the public paths: a program type's module aliases its owner's module, so
  its constructors and fields keep their owner's names and its type stays equal; a sealed
  package's `t` aliases the implementation's abstract type; a value aliases the implementation's
  value. It is additive: `Api_gen` keeps today's names (`globalName`).

**Depends on.** `OCaml5.Lcnf.Naming` (`publicName`, `publicNames`, `ownedCtor`, `fieldName`),
`OCaml5.Ml.Syntax`, `Lean.Environment` (a type's constructors and fields).

**Properties.**
* **One path per name.** Every row's path comes from `publicNames`, which refuses two
  declarations with one path by both names — *tested* (`aB`/`a_b`, `OCaml5.Lcnf.Naming`).
* **Members have a source and keep their owner's spelling.** A constructor or field the owner
  declares in OCaml and the Lean type does not declare refuses the manifest (`ownerMembers`), and
  so does a member whose public name is not the one its owner declares (`spellingMismatches`) —
  *by construction*; the second *tested* (the controls below).
* **Append only.** At one version, every committed row keeps its path and arity — *tested*
  (the controls below: a moved path, a dropped path, a version that goes back).
* **The facade holds the manifest and nothing else.** One binding per value row, one `t` per
  sealed row, one alias per owner type; a module that aliases an owner holds no other public name
  — *tested* (the controls below); *checked* by `ocamlopt` against the implementation before
  publication (`scripts/lib/lcnf_interfaces.py`) and by an outside project
  (`scripts/check-public-facade.py`).
-/

namespace OCaml5.Lcnf.Public

open Lean

/-- One public name with what the facade needs to spell it. -/
structure Row where
  name : PublicName
  /-- A sealed package: the facade's `t` is abstract. -/
  isAbstract : Bool := false
  /-- A type's parameters, as the implementation declares them; empty otherwise. -/
  params : List String := []
  /-- What the facade aliases: a value or type path, or an owner's module. -/
  implementation : String
deriving Repr, Inhabited

/-- The manifest's kind column: what the row names, and a sealed type as `abstract`. -/
def Row.kind (r : Row) : String :=
  match r.name.kind with
  | .value => "value"
  | .type => if r.isAbstract then "abstract" else "type"
  | .ctor => "constructor"
  | .field => "field"

/-- The arity column: a type's parameter count, `-` for any other row. -/
def Row.arity (r : Row) : String :=
  if r.name.kind == .type then toString r.params.length else "-"

/-- The order of the manifest and of the facade: by path, then by kind. -/
def sortRows (rows : List Row) : List Row :=
  rows.mergeSort fun a b => a.name.path < b.name.path || (a.name.path == b.name.path && a.kind ≤ b.kind)

/-! ## The rows -/

/-- What the facade is made from, as one artifact's run reads it. -/
structure Inputs where
  /-- The implementation unit (`Api_gen`) and each public root with the name it is emitted as. -/
  unit : String
  values : List (Name × String)
  /-- The program types' owner unit (`Eff_types`) and each type at its owner: its OCaml module
  and its declaration there. -/
  owner : String
  ownerTypes : List (Name × String × Ml.TypeDecl)
  /-- Each sealed package: its OCaml type name in the implementation unit and its parameters. -/
  sealed : List (Name × String × List String)
deriving Inhabited

/-- The constructors and fields of one owner type, each with its Lean source and the name the
owner's declaration spells: a variant's constructors (`ownedCtor`) and a record's fields
(`fieldName`), read off the Lean type as `OCaml5.Lcnf.Types` reads it. A member the owner declares
and the Lean type does not is refused, and so is a Lean constructor the owner does not declare.
An abbreviation has no member. -/
def ownerMembers (env : Environment) (n : Name) (d : Ml.TypeDecl) :
    Except String (List (PublicKind × Name × String)) := do
  match d.body with
  | .variant cs =>
    let some (.inductInfo info) := env.find? n
      | throw s!"public names: {n} is no inductive type"
    let named := info.ctors.map fun c => (ownedCtor (shortName c), c)
    for c in cs do
      unless named.any (·.1 == c.name) do
        throw s!"public names: {n} declares the constructor {c.name}, which no Lean constructor names"
    for (o, c) in named do
      unless cs.any (·.name == o) do
        throw s!"public names: the owner of {n} does not declare {c} as {o}"
    return named.map fun (o, c) => (.ctor, c, o)
  | .record fs =>
    let fields := (getStructureFields env n).toList.map fun f => (fieldName f.toString, n ++ f)
    for f in fs do
      unless fields.any (·.1 == f.name) do
        throw s!"public names: {n} declares the field {f.name}, which no Lean field names"
    return (fields.filter fun (o, _) => fs.any (·.name == o)).map fun (o, f) => (.field, f, o)
  | .alias _ | .abstract => return []

/-- The constructors and fields whose public name is not the name their owner declares: the
facade reaches them through the owner's module, so the two must agree. -/
def spellingMismatches (rows : List Row) : List String :=
  rows.filterMap fun r =>
    let spelled := ((r.implementation.splitOn ".").getLast?).getD ""
    if (r.name.kind == .ctor || r.name.kind == .field) && spelled != r.name.localName then
      some s!"public names: the owner spells {r.name.source} `{spelled}`, the public rule `{r.name.localName}`"
    else none

/-- Every public name the facade re-exports, with its implementation, in manifest order. The
paths come from one call of `publicNames`, so two declarations with one path refuse the whole
manifest by both names. A constructor's or field's public name must be the one its owner
declares, since the facade reaches it through the owner's module: a difference is refused. -/
def rows (env : Environment) (inputs : Inputs) : Except String (List Row) := do
  let mut wanted : Array (PublicKind × Name × Row) := #[]
  for (n, m, d) in inputs.ownerTypes do
    let path := inputs.owner ++ "." ++ m
    wanted := wanted.push (.type, n, { name := default, params := d.params, implementation := path })
    for (k, s, spelled) in ← ownerMembers env n d do
      wanted := wanted.push (k, s, { name := default, implementation := path ++ "." ++ spelled })
  for (n, t, ps) in inputs.sealed do
    wanted := wanted.push (.type, n,
      { name := default, isAbstract := true, params := ps, implementation := inputs.unit ++ "." ++ t })
  for (n, o) in inputs.values do
    wanted := wanted.push (.value, n, { name := default, implementation := inputs.unit ++ "." ++ o })
  let names ← match publicNames (wanted.toList.map fun (k, s, _) => (k, s)) with
    | .ok ns => pure ns
    | .error r => throw r.message
  unless names.length == wanted.size do
    throw "public names: a declaration is listed twice in the facade's inputs"
  let named := names.zipWith (fun p (_, _, r) => { r with name := p }) wanted.toList
  if let some m := (spellingMismatches named).head? then throw m
  return sortRows named

/-! ## The manifest -/

/-- The facade module's header comment. -/
def facadeComment : String :=
  "GENERATED by OCaml5.Lcnf.Public (src/OCaml5/Lcnf/Public.lean) from the public roots of\n" ++
  "   ocaml/gen/roots.json, as the manifest ocaml/gen/public-names.tsv lists them. Do not edit.\n" ++
  "   Regenerate with: make gen-lcnf\n" ++
  "   The public facade: each public root, program type, constructor, field and sealed package at\n" ++
  "   its Lean path. It aliases Api_gen and Eff_types, whose own names are no public promise."

/-- The manifest's header line. -/
def header : String :=
  "GENERATED by OCaml5.Lcnf.Public (src/OCaml5/Lcnf/Public.lean) from the public roots of " ++
  "ocaml/gen/roots.json; do not edit. Regenerate with: make gen-lcnf"

/-- The columns of a manifest row. -/
def columns : List String := ["kind", "path", "source", "arity", "implementation"]

/-- The manifest's text: the header, the version, the columns, then one row per public name. -/
def render (version : Nat) (rows : List Row) : String :=
  let line (r : Row) : String :=
    "\t".intercalate [r.kind, r.name.path, r.name.source.toString (escape := false), r.arity, r.implementation]
  "\n".intercalate (["# " ++ header, s!"# version {version}", "\t".intercalate columns] ++ rows.map line) ++ "\n"

/-- One committed row, as text: what the append-only check compares. -/
structure Line where
  kind : String
  path : String
  source : String
  arity : String
deriving BEq, Repr, Inhabited

/-- A row as the append-only check reads it back from the manifest. -/
def Row.line (r : Row) : Line :=
  { kind := r.kind, path := r.name.path, source := r.name.source.toString (escape := false),
    arity := r.arity }

/-- A committed manifest: its version and its rows. -/
def parse (text : String) : Except String (Nat × List Line) := do
  let lines := (text.splitOn "\n").filter (!·.isEmpty)
  let some versionLine := lines.find? (·.startsWith "# version ")
    | throw "public manifest: no `# version` line"
  let some version := (versionLine.drop "# version ".length).toString.toNat?
    | throw s!"public manifest: `{versionLine}` is no version"
  let body := lines.filter fun l => !l.startsWith "#" && l != "\t".intercalate columns
  let rows ← body.mapM fun l => match l.splitOn "\t" with
    | [k, p, s, a, _] => pure { kind := k, path := p, source := s, arity := a }
    | _ => throw s!"public manifest: `{l}` has not {columns.length} columns"
  return (version, rows)

/-- Why a new manifest may not replace the committed one. -/
inductive Breach where
  /-- A committed row whose source no new row of its kind names. -/
  | dropped (kind source path : String)
  /-- A committed row whose source now has another path or arity. -/
  | moved (kind source oldPath newPath oldArity newArity : String)
  /-- The new version is smaller than the committed one. -/
  | versionBack (old new : Nat)
deriving BEq, Repr, Inhabited

/-- The breach as one line of the generator's report. -/
def Breach.message : Breach → String
  | .dropped k s p => s!"public manifest: the {k} {s} drops its public path {p}"
  | .moved k s p q a b =>
    s!"public manifest: the {k} {s} moves from {p} (arity {a}) to {q} (arity {b})"
  | .versionBack a b => s!"public manifest: version {b} is older than the committed version {a}"

/-- The append-only check (R6.2's `public_name_stable`, as a finite check of two manifests): at
one version every committed row keeps its kind, source, path and arity in the new manifest. A
larger version is a declared break and admits any change; a smaller one is refused. -/
def breaches (old : Nat × List Line) (new : Nat × List Line) : List Breach :=
  if new.1 < old.1 then [.versionBack old.1 new.1]
  else if new.1 > old.1 then []
  else old.2.filterMap fun o =>
    match new.2.find? (fun n => n.kind == o.kind && n.source == o.source) with
    | none => some (.dropped o.kind o.source o.path)
    | some n =>
      if n.path == o.path && n.arity == o.arity then none
      else some (.moved o.kind o.source o.path n.path o.arity n.arity)

/-! ## The facade -/

/-- What one public name puts at its module path in the facade. -/
private inductive Item where
  /-- `let name = implementation`. -/
  | value (localName implementation : String)
  /-- `type ('a, …) t = ('a, …) implementation`: a sealed package, abstract through the alias. -/
  | sealed (params : List String) (implementation : String)
  /-- The module is `module M = implementation`, the owner's module. -/
  | owner (implementation : String)
  /-- A constructor or a field: it comes with its owner's alias. -/
  | member
deriving Inhabited

/-- The structure items of one module of the facade, from the items at or below it (each with its
path below this module). `fuel` bounds the depth; `facadeModule` gives one more than the deepest
path, so it never runs out. -/
private def build : Nat → List (List String × Item) → Except String (List Ml.Decl)
  | 0, items => if items.isEmpty then .ok [] else .error "public facade: the module tree is deeper than its bound"
  | fuel + 1, items => do
    let here := items.filterMap fun (path, item) => if path.isEmpty then some item else none
    if here.any (fun i => (i matches .owner _) || (i matches .member)) then
      throw "public facade: a type's name at the facade's own top"
    let below := items.filterMap fun (path, item) => match path with
      | m :: rest => some (m, rest, item)
      | [] => none
    let mut children : List Ml.Decl := []
    for m in (below.map (·.1)).eraseDups do
      let sub := below.filterMap fun (h, rest, item) => if h == m then some (rest, item) else none
      match sub.findSome? (fun (rest, item) => match rest, item with
          | [], .owner impl => some impl
          | _, _ => none) with
      | some impl =>
        unless sub.all (fun (rest, item) => rest.isEmpty && ((item matches .owner _) || (item matches .member))) do
          throw s!"public facade: the module {m} aliases {impl} and holds another public name"
        children := children ++ [.moduleAliasD m impl]
      | none =>
        if sub.any (fun (rest, item) => rest.isEmpty && (item matches .member)) then
          throw s!"public facade: a constructor or field of {m} has no owner type"
        children := children ++ [.moduleD m [] (← build fuel sub)]
    let types := here.filterMap fun
      | .sealed ps impl => some (Ml.Decl.types
          [{ name := "t", params := ps, body := .alias (.con impl (ps.map Ml.Ty.var)) }])
      | _ => none
    let values := here.filterMap fun
      | .value l impl => some (Ml.Decl.letD false [{ name := l, body := .var impl }])
      | _ => none
    return types ++ children ++ values

/-- The facade module: one OCaml unit (`unit`, the recipe's `facade.module`) whose module tree
holds every row at its path. A row outside the unit's namespace is refused. -/
def facadeModule (unit : String) (comment : String) (rows : List Row) : Except String Ml.Module := do
  let mut items : List (List String × Item) := []
  for r in rows do
    let path ← match r.name.modules with
      | top :: rest =>
        if top == unit then pure rest
        else throw s!"public facade: {r.name.path} lies outside the facade module {unit}"
      | [] => throw s!"public facade: {r.name.path} has no module"
    let item : Item := match r.name.kind with
      | .value => .value r.name.localName r.implementation
      | .type => if r.isAbstract then .sealed r.params r.implementation else .owner r.implementation
      | .ctor | .field => .member
    items := items ++ [(path, item)]
  let depth := (items.map (·.1.length)).foldl max 0
  return { name := unit, header := some comment, items := ← build (depth + 1) items }

/-! ## Controls -/

private def line (k p s a : String) : Line := { kind := k, path := p, source := s, arity := a }
private def committed : Nat × List Line :=
  (0, [line "value" "Effect4.Run.Tree.of_program" "Effect4.Run.Tree.ofProgram" "-",
       line "type" "Effect4.Program.Eff.t" "Effect4.Program.Eff" "1"])
-- green: the same rows with one appended; red: a moved path, a dropped path, a version that goes back
#guard breaches committed (0, committed.2 ++ [line "value" "Effect4.Run.Tree.run" "Effect4.Run.Tree.run" "-"]) == []
#guard breaches committed
    (0, [line "value" "Effect4.Run.Tree.program" "Effect4.Run.Tree.ofProgram" "-", committed.2[1]!])
  == [.moved "value" "Effect4.Run.Tree.ofProgram" "Effect4.Run.Tree.of_program" "Effect4.Run.Tree.program" "-" "-"]
#guard breaches committed (0, [committed.2[0]!])
  == [.dropped "type" "Effect4.Program.Eff" "Effect4.Program.Eff.t"]
#guard breaches committed (0, [committed.2[0]!, line "type" "Effect4.Program.Eff.t" "Effect4.Program.Eff" "2"])
  == [.moved "type" "Effect4.Program.Eff" "Effect4.Program.Eff.t" "Effect4.Program.Eff.t" "1" "2"]
-- a declared break admits the drop; going back is refused
#guard breaches committed (1, [committed.2[0]!]) == []
#guard breaches (1, committed.2) committed == [.versionBack 1 0]
-- the manifest reads back what it renders
private def sample : List Row :=
  [{ name := { source := `Effect4.Run.Tree.ofProgram, kind := .value, modules := ["Effect4", "Run", "Tree"],
               localName := "of_program" }, implementation := "Api_gen.run_tree_of_program" },
   { name := { source := `Effect4.Program.Eff, kind := .type, modules := ["Effect4", "Program", "Eff"],
               localName := "t" }, params := ["op"], implementation := "Eff_types.Eff" },
   { name := { source := `Effect4.Program.Eff.succeed, kind := .ctor, modules := ["Effect4", "Program", "Eff"],
               localName := "Succeed" }, implementation := "Eff_types.Eff.Succeed" },
   { name := { source := `Effect4.Api.Built, kind := .type, modules := ["Effect4", "Api", "Built"],
               localName := "t" }, isAbstract := true, implementation := "Api_gen.built" }]
#guard (parse (render 0 (sortRows sample))).toOption.map (·.2.length) == some 4
#guard (parse (render 0 (sortRows sample))).toOption.map (·.1) == some 0
-- the facade: an owner type is a module alias, a sealed type an abstract `t`, a value a binding
#guard match facadeModule "Effect4" "c" (sortRows sample) with
  | .ok m => m.items.length == 3
  | .error _ => false
-- red: a module that aliases an owner and holds a value; a name outside the facade's namespace
private def inOwner : Row :=
  { name := { source := `Effect4.Program.Eff.size, kind := .value,
              modules := ["Effect4", "Program", "Eff"], localName := "size" },
    implementation := "Api_gen.size" }
#guard match facadeModule "Effect4" "c" (sample ++ [inOwner]) with
  | .error _ => true
  | .ok _ => false
#guard match facadeModule "Other" "c" sample with
  | .error _ => true
  | .ok _ => false
-- a member's public name is its owner's spelling; red: an owner that spells a field otherwise
#guard spellingMismatches sample == []
private def respelled : Row :=
  { name := { source := `Effect4.ServiceKey.type, kind := .field, modules := ["Effect4", "ServiceKey"],
              localName := "type_" }, implementation := "Eff_types.ServiceKey.«type»" }
#guard (spellingMismatches [respelled]).length == 1

end OCaml5.Lcnf.Public
