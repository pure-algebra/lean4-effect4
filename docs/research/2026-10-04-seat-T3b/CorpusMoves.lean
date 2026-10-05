import Test.Program.Gen
import Effect4.Store.Domain.ProgramWire
import Effect4.Api

/-! Measurement for seat T3b's design note (phase 1), at `5949fe4b`. The corpus `make corpus`
indexes (`tools/Drivers/Corpus.lean`: 400 generated programs at depth 4, and the wire corpus):

1. every read-modify-write `perform`, by row and function name, in a program the printer prints
   (its text is the index's `chars` column);
2. every program whose checker refusal is `requestNotSubtype` at a read-modify-write row, with the
   request type the checker reports: a request typed `refOf T` with `T` not `nat` is where the
   template row can move the verdict (the term then types at `T`, or refuses as a term).

Replay from the worktree root under the shared lock:
`lake env lean -M8192 docs/research/2026-10-04-seat-T3b/CorpusMoves.lean`. -/

open Effect4 Effect4.Program Effect4.Machine

def rmw? : NativeOp → Option (String × FnName)
  | .refUpdate f => some ("refUpdate", f)
  | .refGetAndUpdate f => some ("refGetAndUpdate", f)
  | .refUpdateAndGet f => some ("refUpdateAndGet", f)
  | .refUpdateSome f => some ("refUpdateSome", f)
  | .refGetAndUpdateSome f => some ("refGetAndUpdateSome", f)
  | .refUpdateSomeAndGet f => some ("refUpdateSomeAndGet", f)
  | .refModify f => some ("refModify", f)
  | .refModifySome f => some ("refModifySome", f)
  | _ => none

def fnText : FnName → String
  | .incr => "incr" | .double => "double" | .zeroWhenPositive => "zeroWhenPositive"
  | .noChange => "noChange" | .takeAndBump => "takeAndBump"

def rmwOf (p : Eff NativeOp) : List (String × FnName) :=
  foldMap_eff [] (· ++ ·) p (f_eff := fun e => match e with
    | .perform op _ => (rmw? op).toList
    | _ => [])

def corpusPrograms : List (String × Eff NativeOp) :=
  ((List.range 400).map fun i => (s!"g{i}", Test.Program.Gen.program i 4)) ++ Wire.Corpus.all

#eval show IO Unit from do
  let mut pairs : Std.HashMap String Nat := {}
  let mut programs := 0
  let mut printedWith := 0
  let mut typedWith := 0
  let mut refusedAtRow := 0
  for (name, p) in corpusPrograms do
    let uses := rmwOf p
    if uses.isEmpty then continue
    programs := programs + 1
    let printed := (Api.print p).isOk
    if printed then printedWith := printedWith + 1
    if Api.wellTyped p then typedWith := typedWith + 1
    if printed then
      for (row, f) in uses do
        let k := s!"{row} {fnText f}"
        pairs := pairs.insert k (pairs.getD k 0 + 1)
    match Api.explain p with
    | some ⟨path, .requestNotSubtype row r expected⟩ =>
      if (["refUpdate", "refGetAndUpdate", "refUpdateAndGet", "refUpdateSome",
          "refGetAndUpdateSome", "refUpdateSomeAndGet", "refModify", "refModifySome"].contains row) then
        refusedAtRow := refusedAtRow + 1
        let cellTy := match r.normalize with
          | .refOf t => s!"refOf {t.render}"
          | t => s!"not a cell: {t.render}"
        IO.println s!"refused at a read-modify-write row: {name} path {path} row {row} request {cellTy} expected {expected.render} readable {Api.readable p}"
    | _ => pure ()
  IO.println s!"programs with a read-modify-write perform: {programs}; printed {printedWith}; wellTyped {typedWith}; refused at such a row with requestNotSubtype: {refusedAtRow}"
  let sorted := pairs.toList.toArray.qsort (fun a b => a.1 < b.1)
  for (k, n) in sorted do
    IO.println s!"  printed use: {k}: {n}"

/-! ## Which printed programs a canonical face would move

T2's lowerings collide at a shape (`incr` and `takeAndBump` lower to one term at every shape;
`zeroWhenPositive` and `noChange` lower to one term at the two total shapes). A face that prints
one name per term prints a migrated program's other name differently. Two candidate tables:
`declOrder` takes the first name in `FnName`'s declaration order whose lowering is the term;
`home` takes the name whose own shape this is (`incr` at the update shapes, `takeAndBump` at the
two `modify` shapes, `noChange` for the identity). -/

def shapeOf : String → Nat
  | "refUpdate" | "refGetAndUpdate" | "refUpdateAndGet" => 0
  | "refUpdateSome" | "refGetAndUpdateSome" | "refUpdateSomeAndGet" => 1
  | "refModify" => 2
  | _ => 3

def lower (shape : Nat) (f : FnName) : Program.Term :=
  match shape with
  | 0 => f.updateTerm | 1 => f.updateSomeTerm | 2 => f.modifyTerm | _ => f.modifySomeTerm

def names : List FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

def declOrder (shape : Nat) (f : FnName) : FnName :=
  (names.find? fun g => lower shape g == lower shape f).getD f

def home (shape : Nat) (f : FnName) : FnName :=
  let pref : List FnName := match shape with
    | 2 | 3 => [.takeAndBump, .double, .noChange, .zeroWhenPositive, .incr]
    | _ => [.incr, .double, .noChange, .zeroWhenPositive, .takeAndBump]
  (pref.find? fun g => lower shape g == lower shape f).getD f

#eval show IO Unit from do
  for (label, canon) in [("declOrder", declOrder), ("home", home)] do
    let mut moved : List String := []
    let mut uses := 0
    for (name, p) in corpusPrograms do
      unless (Api.print p).isOk do continue
      let changed := (rmwOf p).filter fun (row, f) => canon (shapeOf row) f != f
      unless changed.isEmpty do
        moved := moved ++ [name]
        uses := uses + changed.length
    IO.println s!"{label}: {moved.length} printed programs move ({uses} uses): {moved}"
