import Lean

/-!
# Effect4Gen.Main — the generator of `Canonical` instances

Owner: the tool that reads inductives out of the Lean environment and emits the Lean text of
their `Canonical` instances — `shapeDoc`, `toVal`, `ofVal`, `ofVal_toVal`, `ofVal_exact`,
`fits` and the instance — exactly as lane S1's templates write them by hand
(`Test/Store/Templates.lean` after the landing; `workshop/Cas/Cas/{Templates,Program}.lean` in
the spike), and, where a group asks for it, the `Content` instance that files the carrier under
its kind.

The rules it follows are the facts note's Q2 and Q5, not choices: a structure is constructor 0
with its fields in declaration order; an inductive's constructors are numbered in declaration
order; a field goes through its own type's `Canonical` instance and is never inlined; a mutual
block is one `ShapeDoc` whose `defs` bind every member by name and whose members refer to each
other through `.named`.

    lake env lean -M 4096 --run tools\Effect4Gen\Main.lean --group Json \
      --imports Effect4.Store.Canonical --out src\Effect4\Store\Derived\Json.lean \
      --append tools\Effect4Gen\guards\json.lean Effect4.Float64 Effect4.Json

`--imports` names the modules the emitted file imports; the tool imports exactly those before
it reads the carriers, so the environment it generates from is the environment the emitted file
elaborates in. `--kind <Type>=<kind>` emits `instance : Content <Type> := ⟨.<kind>⟩` right
after that type's `Canonical` instance (the type spelled as on the command line, `@` for a
space): a typed reference field (`source : Ref Source`) needs the target's `Content` before the
referring type's instance can be derived, and types are emitted in the order given, so a group
lists its targets first. `scripts\generate-derived.ps1` holds the manifest and runs this once
per group.

The environment walk is `src/OCaml5/Tools/Describe.lean`'s (`getConstInfoInduct`,
`forallTelescope`, `isStructure`, `InductiveVal.all`); the "generated Lean text with a guard"
pattern is `src/OCaml5/Lib/Derived.lean`'s.

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library, and its own axioms
are not the emitted code's. The emitted code's receipts are printed by the emitted file.

## What decides the shape of the emitted proof

An *item* is one requested type together with its mutual block (`InductiveVal.all`) and the
applied nominal carriers that mention a block member (`ElementOf Representation` and kin), all
of which share one `defs` table and refer to each other by `.named`. An item is *recursive*
when any constructor argument mentions a member.

- A recursive item reads through `guarded toVal raw` (`Store/Canonical.lean`): `raw` is the
  structural reader, the guard compares the re-encoding, so `ofVal_toVal` needs only the left
  inverse `raw (toVal a) = some a` and `ofVal_exact` is free. That is S1's recipe for the `Eff`
  family, moved here verbatim.
- A non-recursive item reads structurally, with S1's template scripts: the all-nullary and
  at-most-one-argument sums by the `first`-combinator script of `LitC`, a structure by the
  bullet script of `Entry`/`ForkOptions`. Anything else falls back to `guarded`.

`toVal` is the same function either way, so the bytes are the same either way.
-/

open Lean Meta

namespace Effect4Gen

/-! ## The intermediate representation -/

/-- A container position that needs its own companion function inside the block. -/
inductive AuxKind where
  | list
  | option
  | pair
deriving BEq, Inhabited

/-- Where a constructor argument's codec comes from. -/
inductive Slot where
  /-- Another member of this block: `toVal<ident>` / `raw<ident>` / `fits<ident>`. -/
  | member (idx : Nat)
  /-- A type with its own instance: `Canonical.toVal` / `Canonical.ofVal` / `lift_<ident>`. -/
  | foreign (idx : Nat)
  /-- A `List`, `Option` or `×` over something that mentions a member. -/
  | aux (idx : Nat)
deriving BEq, Inhabited

structure Aux where
  kind : AuxKind
  ty : Expr
  tyText : String
  /-- One inner slot for `list`/`option`, two for `pair`. -/
  inner : Array Slot
deriving Inhabited

structure CtorInfo where
  /-- The constructor's last name component. -/
  name : String
  args : Array (String × Slot)
deriving Inhabited

structure MemberInfo where
  ty : Expr
  tyText : String
  /-- The name this member is bound under in `defs` and referred to by `.named`. -/
  shapeName : String
  /-- The suffix of every function and theorem about this member. -/
  ident : String
  isStruct : Bool
  ctors : Array CtorInfo
deriving Inhabited

structure ForeignInfo where
  ty : Expr
  tyText : String
  ident : String
deriving Inhabited

structure St where
  members : Array MemberInfo := #[]
  foreigns : Array ForeignInfo := #[]
  auxes : Array Aux := #[]
deriving Inhabited

abbrev GenM := StateRefT St MetaM

/-- A `--kind` request: the carrier and the `Kind` constructor its nodes file under. -/
structure KindReq where
  ty : Expr
  kind : String
deriving Inhabited

/-! ## Printing a type as Lean source -/

/-- The last component of a name, as an identifier. -/
def shortName (n : Name) : String := n.componentsRev.head!.toString

/-- A type as Lean source text, fully qualified from the root so that no `namespace` in the
emitted file can capture it. -/
partial def tyText (e : Expr) : String :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const n _ =>
    let base := "_root_." ++ n.toString
    if args.isEmpty then base
    else base ++ " " ++ String.intercalate " " (args.toList.map fun a => "(" ++ tyText a ++ ")")
  | _ => "«unprintable»"

/-- A type as Lean source text, parenthesised when it is an application, so that it can stand
as one argument. -/
def tyTextP (e : Expr) : String :=
  let s := tyText e
  if s.any (· == ' ') then "(" ++ s ++ ")" else s

/-- An identifier for a type: the head's short name followed by its arguments' identifiers. -/
partial def identOf (e : Expr) : String :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const n _ => shortName n ++ String.join (args.toList.map identOf)
  | _ => "X"

/-- Does `needle` occur in `e`? Structural, because every type here is first order. -/
partial def occurs (needle : Expr) (e : Expr) : Bool :=
  if e == needle then true
  else match e with
    | .app f a => occurs needle f || occurs needle a
    | _ => false

/-- A binder name Lean can print back: an inaccessible or empty name becomes `arg<i>`. -/
def argName (n : Name) (i : Nat) : String :=
  let s := n.toString
  if s.isEmpty || s.any (fun c => c == '✝' || c == '.') then s!"arg{i}" else s

/-- Duplicate-free, order preserving. -/
def dedup [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-! ## Reading the environment -/

/-- The declared argument names and instantiated argument types of one constructor of an
applied inductive. -/
def ctorFields (memberTy : Expr) (ctorName : Name) : MetaM (Array (String × Expr)) := do
  let ci ← getConstInfoCtor ctorName
  let args := memberTy.getAppArgs
  if args.size != ci.numParams then
    throwError "{ctorName} takes {ci.numParams} parameters but was asked for {args.size} \
      in {memberTy.dbgToString}"
  forallTelescope ci.type fun xs _ => do
    if xs.size < ci.numParams then
      throwError "{ctorName}: telescope of {xs.size} under {ci.numParams} parameters"
    let params := xs[0:ci.numParams].toArray
    let fields := xs[ci.numParams:].toArray
    let mut out := #[]
    for i in [0:fields.size] do
      let x := fields[i]!
      let nm ← x.fvarId!.getUserName
      let raw ← instantiateMVars (← inferType x)
      -- Substitute the block's parameters by the requested arguments, so that a member of
      -- `Eff Op` is read at `Eff NativeOp` and no binder escapes its telescope.
      let raw := raw.replaceFVars params args
      let t ← withReducible (whnf raw)
      out := out.push (argName nm i, t)
    return out

/-- The constructors of an applied inductive, in declaration order. -/
def ctorNamesOf (ty : Expr) : MetaM (List Name) := do
  let .const n _ := ty.getAppFn | throwError "not a constant head: {ty}"
  let info ← getConstInfoInduct n
  return info.ctors

/-- Every applied nominal carrier inside `t` that mentions a member and is not `List`,
`Option` or `×`: the companions a mutual block silently acquires. -/
partial def collectNominals (memberTys : Array Expr) (t : Expr) : MetaM (Array Expr) := do
  let fn := t.getAppFn
  let args := t.getAppArgs
  match fn with
  | .const n _ =>
    if n == ``List || n == ``Option || n == ``Prod then
      let mut acc := #[]
      for a in args do
        if memberTys.any (fun m => occurs m a) then
          acc := acc ++ (← collectNominals memberTys a)
      return acc
    else if memberTys.any (fun m => m == t) then
      return #[]
    else
      return #[t]
  | _ => throwError "cannot analyse the type {t}"

/-- The members of an item: the requested type's mutual block, applied to the same arguments,
plus the applied nominal carriers that mention one of them, to a fixpoint. -/
def blockMembers (seed : Expr) : MetaM (Array Expr) := do
  let .const n _ := seed.getAppFn | throwError "not a constant head: {seed}"
  let info ← getConstInfoInduct n
  let args := seed.getAppArgs
  let mut members : Array Expr := #[]
  for m in info.all do
    let ci ← getConstInfoInduct m
    let lvls := ci.levelParams.map fun _ => Level.zero
    members := members.push (mkAppN (mkConst m lvls) args)
  let mut todo := members
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    for c in (← ctorNamesOf t) do
      for (_, ft) in ← ctorFields t c do
        if members.any (fun m => occurs m ft) then
          for nom in ← collectNominals members ft do
            unless members.any (fun m => m == nom) do
              members := members.push nom
              todo := todo.push nom
  return members

/-! ## Classification -/

def mkAux (kind : AuxKind) (ty : Expr) (inner : Array Slot) : GenM Slot := do
  let st ← get
  match st.auxes.findIdx? (fun a => a.ty == ty) with
  | some i => return .aux i
  | none =>
    modify fun s =>
      { s with auxes := s.auxes.push { kind, ty, tyText := tyText ty, inner } }
    return .aux st.auxes.size

def addForeign (ty : Expr) : GenM Slot := do
  let st ← get
  match st.foreigns.findIdx? (fun f => f.ty == ty) with
  | some i => return .foreign i
  | none =>
    -- Parenthesised: a foreign type stands as one argument of `shape`, `Canonical.ofVal` and
    -- every binder the emitted file writes it into.
    modify fun s =>
      { s with foreigns := s.foreigns.push { ty, tyText := tyTextP ty, ident := identOf ty } }
    return .foreign st.foreigns.size

partial def classify (t : Expr) : GenM Slot := do
  let st ← get
  match st.members.findIdx? (fun m => m.ty == t) with
  | some i => return .member i
  | none =>
    if !(st.members.any (fun m => occurs m.ty t)) then
      addForeign t
    else
      let fn := t.getAppFn
      let args := t.getAppArgs
      match fn with
      | .const n _ =>
        if n == ``List && args.size == 1 then
          mkAux .list t #[← classify args[0]!]
        else if n == ``Option && args.size == 1 then
          mkAux .option t #[← classify args[0]!]
        else if n == ``Prod && args.size == 2 then
          mkAux .pair t #[← classify args[0]!, ← classify args[1]!]
        else
          throwError "a member occurs under {n}, which the generator does not compose"
      | _ => throwError "cannot classify {t}"

/-- Build the item: the members with their classified constructors, the foreign types, the
container companions. -/
def buildItem (seed : Expr) : MetaM (St × Bool) := do
  let tys ← blockMembers seed
  let env ← getEnv
  let mut st : St := {}
  -- Reserve the member rows first, so that `classify` can see every member.
  let mut idents : Array String := #[]
  for t in tys do
    let .const n _ := t.getAppFn | throwError "not a constant head: {t}"
    let base := shortName n
    let ident := if idents.contains base then identOf t else base
    idents := idents.push ident
    let row : MemberInfo :=
      { ty := t, tyText := tyText t, shapeName := ident, ident := ident,
        isStruct := isStructure env n, ctors := #[] }
    st := { st with members := st.members.push row }
  let act : GenM Unit := do
    for i in [0:tys.size] do
      let t := tys[i]!
      let mut ctors : Array CtorInfo := #[]
      for c in ← ctorNamesOf t do
        let mut args : Array (String × Slot) := #[]
        for (nm, ft) in ← ctorFields t c do
          args := args.push (nm, ← classify ft)
        ctors := ctors.push { name := shortName c, args }
      modify fun s => { s with members := s.members.set! i { s.members[i]! with ctors } }
  let (_, final) ← act.run st
  let recursive := final.members.size > 1 || final.members.any fun m =>
    m.ctors.any fun c => c.args.any fun (_, sl) => match sl with
      | .foreign _ => false
      | _ => true
  return (final, recursive)

/-! ## Emitting -/

structure Out where
  lines : Array String := #[]

abbrev EmitM := StateRefT Out MetaM

def emit (s : String) : EmitM Unit :=
  modify fun o => { o with lines := o.lines.push s.trimAsciiEnd.copy }

/-- `k` spaces. -/
def spaces (k : Nat) : String := String.ofList (List.replicate k ' ')

/-- Emit `head`, then `items` joined by `sep` and closed by `tail`, wrapped near column 98
with `cont` as the continuation indent. The separator stays at the end of a broken line, the
way the store modules break a long list. -/
def emitJoin (head : String) (items : List String) (sep : String) (tail : String)
    (cont : String) : EmitM Unit := do
  if items.isEmpty then
    emit (head ++ tail)
  else
    let mut line := head
    for i in [0:items.length] do
      let chunk := items[i]! ++ (if i + 1 == items.length then tail else sep)
      if line.length + chunk.length > 98 && !line.trimAscii.copy.isEmpty then
        emit line
        line := cont ++ chunk
      else
        line := line ++ chunk
    emit line

/-- One line if it fits, two if it does not. -/
def emitTwo (indent : String) (a b : String) : EmitM Unit :=
  if (indent ++ a ++ " " ++ b).length <= 98 then emit (indent ++ a ++ " " ++ b)
  else do
    emit (indent ++ a)
    emit (indent ++ "  " ++ b)

/-- `exact <head> (acceptsFields_cons … (acceptsFields_nil _))`, one field per line. -/
def emitFitsChain (indent : String) (head : String) (args : List String) : EmitM Unit := do
  let ex := if head.isEmpty then indent ++ "exact" else indent ++ "exact " ++ head
  if args.isEmpty then
    emit (ex ++ " (acceptsFields_nil _)")
  else
    emit ex
    let n := args.length
    for i in [0:n] do
      let ind := indent ++ "  " ++ spaces (2 * i)
      if i + 1 == n then
        emit (ind ++ "(acceptsFields_cons _ _ _ _ _ _ (" ++ args[i]! ++
          ") (acceptsFields_nil _))" ++ String.ofList (List.replicate (n - 1) ')'))
      else
        emit (ind ++ "(acceptsFields_cons _ _ _ _ _ _ (" ++ args[i]! ++ ")")

/-- The shape of a slot, as Lean source. -/
partial def shapeOf (st : St) : Slot → String
  | .member i => s!".named \"{st.members[i]!.shapeName}\""
  | .foreign i => s!"(shape {st.foreigns[i]!.tyText}).root"
  | .aux i =>
    let a := st.auxes[i]!
    match a.kind with
    | .list => s!".list ({shapeOf st a.inner[0]!})"
    | .option => s!".option ({shapeOf st a.inner[0]!})"
    | .pair => s!".pair ({shapeOf st a.inner[0]!}) ({shapeOf st a.inner[1]!})"

/-- The `toVal` of a slot at a term. -/
def toValOf (st : St) (sl : Slot) (term : String) : String :=
  match sl with
  | .member i => s!"toVal{st.members[i]!.ident} {term}"
  | .foreign _ => s!"Canonical.toVal {term}"
  | .aux i =>
    match st.auxes[i]!.kind with
    | .list => s!".list (toValL{i} {term})"
    | .option => s!"toValO{i} {term}"
    | .pair => s!"toValP{i} {term}"

/-- The `raw` of a slot at a term. A `list` slot reads the already-destructured element list. -/
def rawOf (st : St) (sl : Slot) (term : String) : String :=
  match sl with
  | .member i => s!"raw{st.members[i]!.ident} {term}"
  | .foreign i => s!"Canonical.ofVal (α := {st.foreigns[i]!.tyText}) {term}"
  | .aux i =>
    match st.auxes[i]!.kind with
    | .list => s!"rawL{i} {term}"
    | .option => s!"rawO{i} {term}"
    | .pair => s!"rawP{i} {term}"

/-- The pattern a `raw` clause binds an argument with: a `list` slot destructures. -/
def rawPat (st : St) (sl : Slot) (v : String) : String :=
  match sl with
  | .aux i => match st.auxes[i]!.kind with
    | .list => s!"(.list {v})"
    | _ => v
  | _ => v

/-- The `simp` lemma that discharges a slot inside `raw_toVal`. -/
def rawToValOf (st : St) (sl : Slot) (term : String) : String :=
  match sl with
  | .member i =>
    let d := st.members[i]!.ident
    s!"raw{d}_toVal{d} {term}"
  | .foreign _ => "Canonical.ofVal_toVal"
  | .aux i =>
    match st.auxes[i]!.kind with
    | .list => s!"rawL{i}_toValL{i} {term}"
    | .option => s!"rawO{i}_toValO{i} {term}"
    | .pair => s!"rawP{i}_toValP{i} {term}"

/-- The `fits` proof of a slot at a term. -/
def fitsOf (st : St) (sl : Slot) (term : String) : String :=
  match sl with
  | .member i => s!"fits{st.members[i]!.ident} {term}"
  | .foreign i => s!"lift_{st.foreigns[i]!.ident} {term}"
  | .aux i =>
    match st.auxes[i]!.kind with
    | .list => s!"accepts_list _ _ _ (fitsL{i} {term})"
    | .option => s!"fitsO{i} {term}"
    | .pair => s!"fitsP{i} {term}"

/-- Membership of the `i`-th of `n` left-associated appended tables. -/
def appendChain (n i : Nat) (inner : String) : String :=
  if n <= 1 then inner
  else if i + 1 == n then s!"mem_append_of_right ({inner})"
  else s!"mem_append_of_left ({appendChain (n - 1) i inner})"

/-- `List.Mem.tail` repeated `k` times around `inner`. -/
def tailChain (k : Nat) (inner : String) : String :=
  match k with
  | 0 => inner
  | k + 1 => s!"List.Mem.tail _ ({tailChain k inner})"

/-- `List.Mem.head` under `i` tails: the `i`-th entry of a `::` chain. -/
def memAt (i : Nat) : String := tailChain i "List.Mem.head _"

/-- The fields of a case or structure, as `[("name", shape), …]`. -/
def fieldsText (st : St) (c : CtorInfo) : String :=
  "[" ++ String.intercalate ", "
    (c.args.toList.map fun (n, sl) => s!"(\"{n}\", {shapeOf st sl})") ++ "]"

/-- The shape of one member, indented under its `def`: a struct as one field list, a sum as one
case per line with its own field list wrapped under it. -/
def emitMemberShape (st : St) (m : MemberInfo) (head cont tail : String) : EmitM Unit := do
  if m.isStruct && m.ctors.size == 1 then
    emitJoin (head ++ s!".struct \"{m.shapeName}\" [")
      (m.ctors[0]!.args.toList.map fun (n, sl) => s!"(\"{n}\", {shapeOf st sl})") ", "
      ("]" ++ tail) cont
  else
    emit (head ++ s!".sum \"{m.shapeName}\"")
    let n := m.ctors.size
    for i in [0:n] do
      let c := m.ctors[i]!
      let opener := if i == 0 then "[" else " "
      let closer := if i + 1 == n then "])]" ++ tail else "]),"
      emitJoin (cont ++ opener ++ s!"(\"{c.name}\", [")
        (c.args.toList.map fun (nm, sl) => s!"(\"{nm}\", {shapeOf st sl})") ", " closer
        (cont ++ "   ")

/-- The defs table of a recursive item: the members by name, then the field types' tables. -/
def emitDefs (st : St) : EmitM Unit := do
  let heads := st.members.toList.map fun m => s!"(\"{m.shapeName}\", {m.ident}Shape)"
  if st.foreigns.isEmpty then
    emitJoin "  " (heads ++ ["[]"]) " :: " "" "    "
  else
    emitJoin "  " heads " :: " " ::" "    "
    emitJoin "    ("
      (st.foreigns.toList.map fun f => s!"(shape {f.tyText}).defs") " ++ " ")" "      "

/-- The appended tail of a block's table, as the `mem_tail` lemma states it. -/
def foreignAppend (st : St) : List String :=
  st.foreigns.toList.map fun f => s!"(shape {f.tyText}).defs"

/-- The defs table of a non-recursive item: the field types' tables only. -/
def emitForeignDefs (st : St) (tail : String) : EmitM Unit :=
  if st.foreigns.isEmpty then
    emit ("   []" ++ tail)
  else
    emitJoin "   " (st.foreigns.toList.map fun f => s!"(shape {f.tyText}).defs") " ++ " tail
      "     "

def argBinders (c : CtorInfo) : String :=
  String.join (c.args.toList.mapIdx fun i _ => s!" a{i}")

def valBinders (st : St) (c : CtorInfo) : String :=
  "[" ++ String.intercalate ", "
    (c.args.toList.mapIdx fun i (_, sl) => rawPat st sl s!"v{i}") ++ "]"

/-- The `--kind` request for a member, if the group made one. -/
def kindFor (kinds : Array KindReq) (m : MemberInfo) : Option String :=
  (kinds.find? fun k => k.ty == m.ty).map (·.kind)

/-- The `Content` instance right after a member's `Canonical` instance: the kind byte's row for
every node carrying the carrier (`Store/Node.lean`, `Content`). -/
def emitContent (name : String) (m : MemberInfo) (kind : String) : EmitM Unit := do
  emit s!"/-- Every node carrying a `{m.shapeName}` files under kind `{kind}`. -/"
  emitTwo "" s!"instance {name} :" s!"Content ({m.tyText}) := ⟨.{kind}⟩"
  emit ""

/-! ### The recursive item -/

def emitRecursive (st : St) (ns : String) (kinds : Array KindReq) : EmitM Unit := do
  emit s!"namespace {ns}"
  emit ""
  emit "/-! The block's shapes: every member by name, every field through its own type. -/"
  emit ""
  for m in st.members do
    emit s!"def {m.ident}Shape : Shape :="
    emitMemberShape st m "  " "     " ""
    emit ""
  emit "/-- One table for the block, then the field types' tables. -/"
  emit "def defs : List (String × Shape) :="
  emitDefs st
  emit ""
  -- toVal
  emit "mutual"
  for m in st.members do
    emitTwo "" s!"def toVal{m.ident} :" s!"{m.tyText} → Val"
    for ci in [0:m.ctors.size] do
      let c := m.ctors[ci]!
      emitJoin s!"  | .{c.name}{argBinders c} => .ctor {ci} ["
        (c.args.toList.mapIdx fun i (_, sl) => toValOf st sl s!"a{i}") ", " "]" "      "
  for i in [0:st.auxes.size] do
    let a := st.auxes[i]!
    match a.kind with
    | .list =>
      emit s!"def toValL{i} : {a.tyText} → List Val"
      emit "  | [] => []"
      emit s!"  | x :: xs => {toValOf st a.inner[0]! "x"} :: toValL{i} xs"
    | .option =>
      emit s!"def toValO{i} : {a.tyText} → Val"
      emit "  | none => .none"
      emit s!"  | some x => .some ({toValOf st a.inner[0]! "x"})"
    | .pair =>
      emit s!"def toValP{i} : {a.tyText} → Val"
      emit s!"  | (x, y) => .pair ({toValOf st a.inner[0]! "x"}) ({toValOf st a.inner[1]! "y"})"
  emit "end"
  emit ""
  -- raw
  emit "/-! The structural readers. Exactness is bought by the re-encode guard, so a reader"
  emit "only has to be a left inverse. -/"
  emit ""
  emit "mutual"
  for m in st.members do
    emitTwo "" s!"def raw{m.ident} :" s!"Val → Option ({m.tyText})"
    for ci in [0:m.ctors.size] do
      let c := m.ctors[ci]!
      if c.args.isEmpty then
        emit s!"  | .ctor {ci} [] => some .{c.name}"
      else
        emitJoin s!"  | .ctor {ci} ["
          (c.args.toList.mapIdx fun i (_, sl) => rawPat st sl s!"v{i}") ", " "] =>" "      "
        emitJoin "    match "
          (c.args.toList.mapIdx fun i (_, sl) => rawOf st sl s!"v{i}") ", " " with" "        "
        emitJoin "    | " (c.args.toList.mapIdx fun i _ => s!"some a{i}") ", "
          s!" => some (.{c.name}{argBinders c})" "      "
        emitJoin "    | " (c.args.toList.map fun _ => "_") ", " " => none" "      "
    emit "  | _ => none"
  for i in [0:st.auxes.size] do
    let a := st.auxes[i]!
    match a.kind with
    | .list =>
      let pat := rawPat st a.inner[0]! "v"
      emit s!"def rawL{i} : List Val → Option ({a.tyText})"
      emit "  | [] => some []"
      emit s!"  | {pat} :: vs =>"
      emit s!"    match {rawOf st a.inner[0]! "v"}, rawL{i} vs with"
      emit "    | some x, some xs => some (x :: xs)"
      emit "    | _, _ => none"
      if pat != "v" then emit "  | _ => none"
    | .option =>
      emit s!"def rawO{i} : Val → Option ({a.tyText})"
      emit "  | .none => some none"
      emit s!"  | .some {rawPat st a.inner[0]! "v"} =>"
      emit s!"    match {rawOf st a.inner[0]! "v"} with"
      emit "    | some x => some (some x)"
      emit "    | none => none"
      emit "  | _ => none"
    | .pair =>
      emit s!"def rawP{i} : Val → Option ({a.tyText})"
      emit s!"  | .pair {rawPat st a.inner[0]! "v"} {rawPat st a.inner[1]! "w"} =>"
      emit s!"    match {rawOf st a.inner[0]! "v"}, {rawOf st a.inner[1]! "w"} with"
      emit "    | some x, some y => some (x, y)"
      emit "    | _, _ => none"
      emit "  | _ => none"
  emit "end"
  emit ""
  -- raw_toVal
  emit "mutual"
  for m in st.members do
    emitTwo "" s!"theorem raw{m.ident}_toVal{m.ident}" s!"(a : {m.tyText}) :"
    emit s!"    raw{m.ident} (toVal{m.ident} a) = some a := by"
    emit "  cases a with"
    for c in m.ctors do
      if c.args.isEmpty then
        emit s!"  | «{c.name}»{argBinders c} => rfl"
      else
        emit s!"  | «{c.name}»{argBinders c} =>"
        emitJoin s!"    simp [toVal{m.ident}, raw{m.ident}, "
          (dedup (c.args.toList.mapIdx fun i (_, sl) => rawToValOf st sl s!"a{i}")) ", " "]"
          "      "
    emit "termination_by structural a"
  for i in [0:st.auxes.size] do
    let a := st.auxes[i]!
    match a.kind with
    | .list =>
      emit s!"theorem rawL{i}_toValL{i} (xs : {a.tyText}) :"
      emit s!"    rawL{i} (toValL{i} xs) = some xs := by"
      emit "  match xs with"
      emit "  | [] => rfl"
      emit "  | x :: xs =>"
      emitJoin s!"    simp [toValL{i}, rawL{i}, "
        [rawToValOf st a.inner[0]! "x", s!"rawL{i}_toValL{i} xs"] ", " "]" "      "
      emit "termination_by structural xs"
    | .option =>
      emit s!"theorem rawO{i}_toValO{i} (o : {a.tyText}) :"
      emit s!"    rawO{i} (toValO{i} o) = some o := by"
      emit "  match o with"
      emit "  | none => rfl"
      emit "  | some x =>"
      emitJoin s!"    simp [toValO{i}, rawO{i}, " [rawToValOf st a.inner[0]! "x"] ", " "]" "      "
      emit "termination_by structural o"
    | .pair =>
      emit s!"theorem rawP{i}_toValP{i} (p : {a.tyText}) :"
      emit s!"    rawP{i} (toValP{i} p) = some p := by"
      emit "  match p with"
      emit "  | (x, y) =>"
      emitJoin s!"    simp [toValP{i}, rawP{i}, "
        (dedup [rawToValOf st a.inner[0]! "x", rawToValOf st a.inner[1]! "y"]) ", " "]" "      "
      emit "termination_by structural p"
  emit "end"
  emit ""
  -- memberships and lifts
  emit "/-! The table memberships and the field lifts, one per member and one per field type. -/"
  emit ""
  for i in [0:st.members.size] do
    let m := st.members[i]!
    emitTwo "" s!"theorem mem_{m.ident} : (\"{m.shapeName}\", {m.ident}Shape) ∈ defs :=" (memAt i)
  emit ""
  let nf := st.foreigns.size
  if nf > 0 then
    emit "/-- Into the appended tail of the block's table. -/"
    emit "theorem mem_tail {p : String × Shape}"
    emitJoin "    (h : p ∈ " (foreignAppend st) " ++ " ") : p ∈ defs :=" "      "
    emit s!"  {tailChain st.members.size "h"}"
    emit ""
  for i in [0:nf] do
    let f := st.foreigns[i]!
    emit s!"theorem lift_{f.ident} (x : {f.tyText}) :"
    emitTwo "    " s!"acceptsIn defs (shape {f.tyText}).root" "(Canonical.toVal x) = true :="
    emitTwo "  " "acceptsIn_mono_of_subset"
      s!"(fun _ hp => mem_tail ({appendChain nf i "hp"}))"
    emit "    _ _ (Canonical.fits x)"
  emit ""
  -- fits
  emit "mutual"
  for m in st.members do
    emitTwo "" s!"theorem fits{m.ident}" s!"(a : {m.tyText}) :"
    emit s!"    acceptsIn defs (.named \"{m.shapeName}\") (toVal{m.ident} a) = true := by"
    emit s!"  apply accepts_named_of_mem _ _ {m.ident}Shape _ mem_{m.ident}"
    emit "  cases a with"
    for ci in [0:m.ctors.size] do
      let c := m.ctors[ci]!
      let head :=
        if m.isStruct && m.ctors.size == 1 then "acceptsAt_struct _ _ _ _"
        else if c.args.isEmpty then s!"acceptsAt_sum _ _ _ {ci} \"{c.name}\" [] [] rfl"
        else s!"acceptsAt_sum _ _ _ {ci} \"{c.name}\" _ _ rfl"
      emit s!"  | «{c.name}»{argBinders c} =>"
      emitFitsChain "    " head (c.args.toList.mapIdx fun i (_, sl) => fitsOf st sl s!"a{i}")
    emit "termination_by structural a"
  for i in [0:st.auxes.size] do
    let a := st.auxes[i]!
    match a.kind with
    | .list =>
      emit s!"theorem fitsL{i} (xs : {a.tyText}) :"
      emit s!"    ∀ v ∈ toValL{i} xs,"
      emit s!"      acceptsIn defs ({shapeOf st a.inner[0]!}) v = true := by"
      emit "  match xs with"
      emit "  | [] =>"
      emit "    intro v hv"
      emit "    exact nomatch hv"
      emit "  | x :: xs =>"
      emit "    intro v hv"
      emit s!"    simp only [toValL{i}, List.mem_cons] at hv"
      emit "    rcases hv with rfl | hv"
      emit s!"    · exact {fitsOf st a.inner[0]! "x"}"
      emit s!"    · exact fitsL{i} xs v hv"
      emit "termination_by structural xs"
    | .option =>
      emit s!"theorem fitsO{i} (o : {a.tyText}) :"
      emit s!"    acceptsIn defs (.option ({shapeOf st a.inner[0]!}))"
      emit s!"      (toValO{i} o) = true := by"
      emit "  match o with"
      emit "  | none => exact accepts_option_none _ _"
      emit "  | some x =>"
      emit s!"    exact accepts_option_some _ _ _ ({fitsOf st a.inner[0]! "x"})"
      emit "termination_by structural o"
    | .pair =>
      emit s!"theorem fitsP{i} (p : {a.tyText}) :"
      emit s!"    acceptsIn defs (.pair ({shapeOf st a.inner[0]!}) ({shapeOf st a.inner[1]!}))"
      emit s!"      (toValP{i} p) = true := by"
      emit "  match p with"
      emit "  | (x, y) =>"
      emit "    exact accepts_pair _ _ _ _ _"
      emit s!"      ({fitsOf st a.inner[0]! "x"}) ({fitsOf st a.inner[1]! "y"})"
      emit "termination_by structural p"
  emit "end"
  emit ""
  for m in st.members do
    emitTwo "" s!"instance instCanonical{m.ident} :" s!"Canonical ({m.tyText}) :="
    emit s!"  ⟨⟨.named \"{m.shapeName}\", defs⟩, toVal{m.ident}, guarded toVal{m.ident} raw{m.ident},"
    emit s!"    fun a => guarded_toVal _ _ a (raw{m.ident}_toVal{m.ident} a), fun h => guarded_exact h,"
    emit s!"    fits{m.ident}⟩"
    emit ""
    if let some k := kindFor kinds m then
      emitContent s!"instContent{m.ident}" m k
  emit s!"end {ns}"
  emit ""

/-! ### The non-recursive item -/

def emitPlain (st : St) (ns : String) (kinds : Array KindReq) : EmitM Unit := do
  let m := st.members[0]!
  let nf := st.foreigns.size
  emit s!"namespace {ns}"
  emit ""
  emit "def shapeDoc : ShapeDoc :="
  emitMemberShape st m "  ⟨" "     " ","
  emitForeignDefs st "⟩"
  emit ""
  emit s!"def toVal : {m.tyText} → Val"
  for ci in [0:m.ctors.size] do
    let c := m.ctors[ci]!
    emitJoin s!"  | .{c.name}{argBinders c} => .ctor {ci} ["
      (c.args.toList.mapIdx fun i (_, sl) => toValOf st sl s!"a{i}") ", " "]" "      "
  emit ""
  emit s!"def ofVal : Val → Option ({m.tyText})"
  let isStructLike := m.ctors.size == 1 && m.isStruct
  if isStructLike then
    let c := m.ctors[0]!
    emitJoin "  | .ctor 0 ["
      (c.args.toList.mapIdx fun i (_, sl) => rawPat st sl s!"v{i}") ", " "] =>" "      "
    emitJoin "    match "
      (c.args.toList.mapIdx fun i (_, sl) => rawOf st sl s!"v{i}") ", " " with" "        "
    emitJoin "    | " (c.args.toList.mapIdx fun i _ => s!"some a{i}") ", "
      (" => some ⟨" ++ String.intercalate ", " (c.args.toList.mapIdx fun i _ => s!"a{i}") ++ "⟩")
      "      "
    emitJoin "    | " (c.args.toList.map fun _ => "_") ", " " => none" "      "
    emit "  | _ => none"
  else
    for ci in [0:m.ctors.size] do
      let c := m.ctors[ci]!
      if c.args.isEmpty then
        emit s!"  | .ctor {ci} [] => some .{c.name}"
      else if c.args.size == 1 then
        emit s!"  | .ctor {ci} [v0] => ({rawOf st c.args[0]!.2 "v0"}).map .{c.name}"
      else
        -- A case of arity two or more reads like the recursive emitter's `raw` (above): one
        -- `match` over every argument's reader. Found by lane X on `Effect4.Char.Evidence`
        -- (2026-09-05): the single-argument form was emitted whatever the arity.
        emitJoin s!"  | .ctor {ci} ["
          (c.args.toList.mapIdx fun i (_, sl) => rawPat st sl s!"v{i}") ", " "] =>" "      "
        emitJoin "    match "
          (c.args.toList.mapIdx fun i (_, sl) => rawOf st sl s!"v{i}") ", " " with" "        "
        emitJoin "    | " (c.args.toList.mapIdx fun i _ => s!"some a{i}") ", "
          s!" => some (.{c.name}{argBinders c})" "      "
        emitJoin "    | " (c.args.toList.map fun _ => "_") ", " " => none" "      "
    emit "  | _ => none"
  emit ""
  if isStructLike then
    let c := m.ctors[0]!
    let binders := String.intercalate ", " (c.args.toList.mapIdx fun i _ => s!"a{i}")
    emit s!"theorem ofVal_toVal (a : {m.tyText}) : ofVal (toVal a) = some a := by"
    emit s!"  obtain ⟨{binders}⟩ := a"
    emit "  simp [toVal, ofVal, Canonical.ofVal_toVal]"
    emit ""
    emit ("theorem ofVal_exact {v : Val} {a : " ++ m.tyText ++ "} (h : ofVal v = some a) :")
    emit "    v = toVal a := by"
    emit "  unfold ofVal at h"
    emit "  split at h"
    emit s!"  · next {String.intercalate " " (c.args.toList.mapIdx fun i _ => s!"v{i}")} =>"
    emit "    split at h"
    let bs := String.intercalate " " (c.args.toList.mapIdx fun i _ => s!"b{i}")
    let hs := String.intercalate " " (c.args.toList.mapIdx fun i _ => s!"h{i}")
    emit s!"    · next {bs} {hs} =>"
    emit "      injection h with h"
    emit "      subst h"
    emit "      simp only [toVal]"
    emitJoin "      rw ["
      (c.args.toList.mapIdx fun i _ => s!"Canonical.ofVal_exact h{i}") ", " "]" "        "
    emit "    · exact nomatch h"
    emit "  · exact nomatch h"
  else
    -- A nullary case of a sum closes without the field law, which the linter reports as an
    -- unused `simp` argument; the same script is the templates' `LitC.ofVal_toVal`.
    emit "set_option linter.unusedSimpArgs false in"
    emit s!"theorem ofVal_toVal (a : {m.tyText}) : ofVal (toVal a) = some a := by"
    emit "  cases a <;> simp [toVal, ofVal, Canonical.ofVal_toVal]"
    emit ""
    emit ("theorem ofVal_exact {v : Val} {a : " ++ m.tyText ++ "} (h : ofVal v = some a) :")
    emit "    v = toVal a := by"
    emit "  unfold ofVal at h"
    emit "  split at h"
    emit "  all_goals first"
    emit "    | (injection h with h; subst h; rfl)"
    emit "    | (rename_i w"
    emit "       obtain ⟨x, hx, hj⟩ := Option.map_eq_some_iff.mp h"
    emit "       subst hj"
    emit "       simp only [toVal]"
    emit "       rw [Canonical.ofVal_exact hx])"
    -- One alternative per arity of two or more present in the sum. The inner `match` is split;
    -- `injection` closes every failing arm (`none = some a`) and reduces the success arm; the
    -- success arm's `b`s and `h`s (the order `split` introduces them) are named and rewritten;
    -- `done` makes a wrong-arity alternative fail and fall through. No nested `first`: its
    -- last alternative would run with error recovery and admit the goal with a `sorry`
    -- (measured 2026-09-05 on `Effect4.Char.Evidence`, arities 2 and 3 mixed).
    let arities := ((m.ctors.toList.map fun c => c.args.size).filter (· ≥ 2)).eraseDups
    for n in arities do
      let bs := String.intercalate " " ((List.range n).map fun i => s!"b{i}")
      let hs := String.intercalate " " ((List.range n).map fun i => s!"h{i}")
      let rws := String.intercalate ", " ((List.range n).map fun i => s!"Canonical.ofVal_exact h{i}")
      -- `split` puts the success arm first and compiles the wildcard into one or more arms
      -- with `h : none = some a`; `injection … with` would refuse a name on those, so the
      -- success arm is focused and the rest closed by `nomatch`.
      emit "    | (split at h"
      emit s!"       · rename_i {bs} {hs}"
      emit "         injection h with h"
      emit "         subst h"
      emit "         simp only [toVal]"
      emit s!"         rw [{rws}]"
      emit "         done"
      emit "       all_goals exact nomatch h)"
    emit "    | exact nomatch h"
  emit ""
  for i in [0:nf] do
    let f := st.foreigns[i]!
    emit s!"theorem lift_{f.ident} (x : {f.tyText}) :"
    emitTwo "    " s!"acceptsIn shapeDoc.defs (shape {f.tyText}).root"
      "(Canonical.toVal x) = true :="
    emit s!"  acceptsIn_mono_of_subset (fun _ hp => {appendChain nf i "hp"})"
    emit "    _ _ (Canonical.fits x)"
  if nf > 0 then emit ""
  emit s!"theorem fits (a : {m.tyText}) : shapeDoc.accepts (toVal a) = true := by"
  if isStructLike then
    let c := m.ctors[0]!
    let binders := String.intercalate ", " (c.args.toList.mapIdx fun i _ => s!"a{i}")
    emit s!"  obtain ⟨{binders}⟩ := a"
    emit "  apply accepts_struct"
    emitFitsChain "  " "" (c.args.toList.mapIdx fun i (_, sl) => fitsOf st sl s!"a{i}")
  else
    emit "  cases a with"
    for ci in [0:m.ctors.size] do
      let c := m.ctors[ci]!
      let head :=
        if c.args.isEmpty then s!"accepts_sum _ _ _ {ci} \"{c.name}\" [] [] rfl"
        else s!"accepts_sum _ _ _ {ci} \"{c.name}\" _ _ rfl"
      emit s!"  | «{c.name}»{argBinders c} =>"
      emitFitsChain "    " head (c.args.toList.mapIdx fun i (_, sl) => fitsOf st sl s!"a{i}")
  emit ""
  emit s!"instance instCanonical : Canonical ({m.tyText}) :="
  emit "  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩"
  emit ""
  if let some k := kindFor kinds m then
    emitContent "instContent" m k
  emit s!"end {ns}"
  emit ""

/-! ## The file -/

/-- The module a declaration was compiled in, for the header's provenance line. -/
def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!.toString
  | none => "<local>"

/-- Parse `A B (C D)`: a whitespace-separated application with parentheses. -/
partial def parseTy (toks : List String) : MetaM (Expr × List String) := do
  let (head, rest) ← parseAtom toks
  let mut e := head
  let mut ts := rest
  let mut args := #[]
  while !ts.isEmpty && ts.head! != ")" do
    let (a, r) ← parseAtom ts
    args := args.push a
    ts := r
  return (mkAppN e args, ts)
where
  parseAtom (toks : List String) : MetaM (Expr × List String) := do
    match toks with
    | [] => throwError "empty type expression"
    | "(" :: rest => do
      let (e, r) ← parseTy rest
      match r with
      | ")" :: r' => return (e, r')
      | _ => throwError "unbalanced parentheses"
    | t :: rest => do
      let n := t.toName
      let ci ← getConstInfo n
      let lvls := ci.levelParams.map fun _ => Level.zero
      return (mkConst n lvls, rest)

/-- Split a type expression into tokens. `@` reads as a space, so that an applied type is one
shell word: `Effect4.Program.Eff@Effect4.Program.NativeOp`. -/
def tokenise (s : String) : List String :=
  ((s.replace "@" " ").replace "(" " ( ").replace ")" " ) " |>.splitOn " " |>.filter (·  != "")

def elabTy (s : String) : MetaM Expr := do
  let (e, rest) ← parseTy (tokenise s)
  unless rest.isEmpty do throwError "trailing tokens in {s}"
  return e

structure Args where
  group : String := "Group"
  imports : List String := []
  out : Option String := none
  append : Option String := none
  /-- `--kind <Type>=<kind>`, in the order given. -/
  kinds : List (String × String) := []
  types : List String := []

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a =>
    parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--kind" :: k :: rest, a =>
    match k.splitOn "=" with
    | [ty, kind] => if ty.isEmpty || kind.isEmpty then .error s!"--kind {k}: expected <Type>=<kind>"
      else parseArgs rest { a with kinds := a.kinds ++ [(ty, kind)] }
    | _ => .error s!"--kind {k}: expected <Type>=<kind>"
  | t :: rest, a =>
    if t.startsWith "--" then
      if rest.isEmpty then .error s!"{t} needs a value" else .error s!"unknown option {t}"
    else parseArgs rest { a with types := a.types ++ [t] }

def run (args : Args) : MetaM (Array String) := do
  let env ← getEnv
  let mut out : Out := {}
  -- The regenerating command, wrapped over `--`-comment lines so that no header line runs long.
  let outPath := args.out.getD ("<stdout>")
  let head := "lake env lean -M 4096 --run tools\\Effect4Gen\\Main.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports
    ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p | none => "")
    ++ String.join (args.kinds.map fun (t, k) => " --kind " ++ t ++ "=" ++ k)
  let mut cmdLines : Array String := #["--   " ++ head ++ " \\"]
  let mut cur := "--    "
  for t in args.types do
    if cur.length + t.length + 1 > 96 then
      cmdLines := cmdLines.push (cur ++ " \\")
      cur := "--    " ++ t
    else
      cur := cur ++ " " ++ t
  cmdLines := cmdLines.push cur
  let mut seeds : Array Expr := #[]
  for t in args.types do
    seeds := seeds.push (← elabTy t)
  let mut kinds : Array KindReq := #[]
  for (t, k) in args.kinds do
    kinds := kinds.push { ty := ← elabTy t, kind := k }
  let mut mods : Array String := #[]
  for s in seeds do
    let .const n _ := s.getAppFn | throwError "not a constant head: {s}"
    let m := moduleOf env n
    unless mods.contains m do mods := mods.push m
  out := { out with lines := out.lines
    ++ #["-- GENERATED by tools/Effect4Gen/Main.lean from the Lean environment. Do not edit.",
         "-- Regenerate (scripts\\generate-derived.ps1 runs this for every group; -Verify refuses a diff):"]
    ++ cmdLines
    ++ #["-- Carriers read from: " ++ String.intercalate ", " mods.toList]
    ++ (match args.append with
        | some p => #["-- Acceptance guards appended verbatim from: " ++ p]
        | none => #[])
    ++ (args.imports.map fun i => "import " ++ i).toArray
    ++ #["",
         "/-!",
         "# " ++ args.group ++ " — generated `Canonical` instances",
         "",
         "One emitted declaration per rule of the facts note's Q2 and Q5: `shapeDoc`, `toVal`,",
         "`ofVal`, `ofVal_toVal`, `ofVal_exact`, `fits` and the instance, per type, in",
         "declaration order, fields through their own types' instances; a `Content` instance",
         "follows where the group names the carrier's kind. The proofs are lane S1's template",
         "scripts; nothing here was written or repaired by hand.",
         "-/",
         "",
         "set_option autoImplicit false",
         "",
         "namespace Effect4.Store",
         "",
         "namespace " ++ args.group ++ "Gen",
         ""] }
  -- One item per requested type, skipping a type already emitted as a member of an earlier item.
  let mut done : Array Expr := #[]
  let mut receipts : Array String := #[]
  for s in seeds do
    if done.any (fun d => d == s) then continue
    let (st, recursive) ← buildItem s
    for m in st.members do
      done := done.push m.ty
    let ns := st.members[0]!.ident ++ "C"
    let emitAct : EmitM Unit :=
      if recursive then emitRecursive st ns kinds else emitPlain st ns kinds
    let (_, o) ← emitAct.run { lines := #[] }
    out := { out with lines := out.lines ++ o.lines }
    let prefix' := args.group ++ "Gen." ++ ns ++ "."
    if recursive then
      for m in st.members do
        receipts := receipts.push (prefix' ++ "toVal" ++ m.ident)
        receipts := receipts.push (prefix' ++ "raw" ++ m.ident ++ "_toVal" ++ m.ident)
        receipts := receipts.push (prefix' ++ "fits" ++ m.ident)
        receipts := receipts.push (prefix' ++ "instCanonical" ++ m.ident)
        if (kindFor kinds m).isSome then
          receipts := receipts.push (prefix' ++ "instContent" ++ m.ident)
    else
      receipts := receipts.push (prefix' ++ "toVal")
      receipts := receipts.push (prefix' ++ "ofVal_toVal")
      receipts := receipts.push (prefix' ++ "ofVal_exact")
      receipts := receipts.push (prefix' ++ "fits")
      receipts := receipts.push (prefix' ++ "instCanonical")
      if (kindFor kinds st.members[0]!).isSome then
        receipts := receipts.push (prefix' ++ "instContent")
  -- Every `--kind` must name a type this group emitted.
  for k in kinds do
    unless done.any (fun d => d == k.ty) do
      throwError "--kind names {k.ty}, which this group does not emit"
  out := { out with lines := out.lines ++ #["end " ++ args.group ++ "Gen", ""] }
  if let some p := args.append then
    let txt ← IO.FS.readFile p
    out := { out with lines := out.lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "") }
  out := { out with lines := out.lines ++ #["/-! ## Receipts -/", ""] }
  for r in receipts do
    out := { out with lines := out.lines.push ("#print axioms " ++ r) }
  out := { out with lines := out.lines ++ #["", "end Effect4.Store"] }
  return out.lines

end Effect4Gen

open Effect4Gen in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  if args.types.isEmpty then
    throw (IO.userError "no types to generate")
  initSearchPath (← findSysroot)
  -- The environment the tool reads is the environment the emitted file elaborates in.
  let env ← importModules (args.imports.map fun i => { module := i.toName }).toArray {} 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default }
  let act : MetaM Unit := do
    let lines ← run args
    let text := String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
