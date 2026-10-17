import Effect4.Run.Tree
import Effect4.Api.RefusalsDerived
import Effect4.Api.RunnerDerived

/-!
# Run.Kit — what the native kit lowers

The native kit (`ocaml/kit/`) is OCaml made from Lean by LCNF (`ocaml/gen/roots.json`, artefact
`ocaml/kit/kit_gen.ml`). It runs the call tree of `Effect4.Run.Tree`, checks a program with the
checker of `Effect4.Api`, and moves every carrier it takes or gives through that carrier's
canonical image. This module names those entry points as monomorphic constants, so the generated
OCaml has one function or one value for each. It declares no new behaviour: each definition is
a function of `Effect4.Api`, `Effect4.Run.Tree` or the carrier's `Canonical` instance.

**The carriers' images.** For each carrier the kit reads or writes, the kit takes its shape
document (`Canonical.shape`), its value tree (`Canonical.toVal`) and its exact reading
(`Canonical.ofVal`). The kit's one JSON printer and one JSON reader interpret a shape document
over a value tree (`Kit_json`, the OCaml twin of `ShapeDoc.print` and `Canonical.ofJsonAnyOrder`).
So a program, a row table, a type, an exit and a refusal print as the session tool prints them,
and read back exactly where the value tree reads. A JSON number crosses as a natural: the tree's
own JSON keeps numbers as binary64 bit patterns, which the lowered `UInt64` holds only below 2^62
(`src/OCaml5/Lcnf/Builtins.lean`).
-/

set_option autoImplicit false

namespace Effect4.Run.Kit

open Effect4 Effect4.Store Effect4.Program Effect4.Machine

/-! ## The checker -/

/-- **The checker's answer**: the program's type at the application, or where and why it is
refused (`Api.check`, which is total by `Api.explain_none_iff`). -/
def check (app : SigApp) (program : NativeEff) : Except TypeRefusal EffTy :=
  (Api.check program app).map (·.certificate.ty)

/-- **Program admission**, as far as the native route lowers it (`Program.admitProgram`): the
signature's own admission (`admitSig`: each row's registration and kind, its key, the service
declarations), then no empty answer or error column in the program's type
(`findEmptyColumnInEffTy`). `none` when both pass. Typing's located refusal is `check`'s, so a
program that does not type answers `none` here. Raw formation (`Formation.checkInput`) is the one
part not decided here: its view of a program (`Eff.view`) has a child field whose type depends on
another field (`ArgF.child`'s `R fam`), which the LCNF route does not spell. -/
def admit (app : SigApp) (program : NativeEff) : Option AdmitRefusal :=
  match admitSig app with
  | .error why => some (.signature why)
  | .ok () =>
    match Api.typeOf program app with
    | some t => (findEmptyColumnInEffTy t).map .emptyColumn
    | none => none

/-- An admission refusal's shape document. -/
def admitShape : ShapeDoc := Canonical.shape AdmitRefusal
/-- An admission refusal's value tree. -/
def admitToVal (r : AdmitRefusal) : Store.Val := Canonical.toVal r

/-! ## Reply admission -/

/-- Why a host's reply does not fit its call's row. -/
inductive ReplyFault where
  /-- a success whose value is no member of the row's answer type -/
  | answerType (expected : Ty)
  /-- a failure with a reason outside the row's error column -/
  | errorType (expected : Ty)
  /-- a failure that carries one of the machine's own markers of malformed code -/
  | reservedDefect

/-- **Why a host's reply does not fit the row of its call**, as reply admission reads it
(`Program.admitAnswer`: membership under the application's named types, `Val.memberIn`, at no
allocated handle; a reserved defect first, then each reason against the error column). `none`
when it fits. A reply that does not fit is not applied: the call stays waiting (decisions row 408
(1) and (2)). -/
def replyFault (app : SigApp) (row : Nat) : ExitV → Option ReplyFault
  | .success v =>
    match columns app row with
    | some r => if (externalValue app.types r.answer [] v).isNone then some (.answerType r.answer) else none
    | none => none
  | .failure cause =>
    match columns app row with
    | some r =>
      if cause.reasons.any reservedDie then some .reservedDefect
      else if cause.reasons.all (errAdmits app.types r.error) then none
      else some (.errorType r.error)
    | none => none
where
  /-- The row's type columns in the native signature's canonical view (`Row.normalizeTypes`),
  whatever its registration: the tree's host answers every host row. -/
  columns (app : SigApp) (row : Nat) : Option Program.Row := (app.rows[row]?).map Program.Row.normalizeTypes

/-! ## Replies drawn from the types: every path of a program -/

/-- **A few members of a type**, under the application's named types: the small values a test
would try first (zero, one and two; the empty and a one-letter string; `none` and one `some`; the
lists of zero, one and two items; each union member's). Each candidate is
kept only where it is a member (`Val.memberIn`), so the list holds members and nothing else;
a type with no small member, such as a handle, gives none. `depth` bounds the nesting. -/
def samples (decls : TyDecls) : Nat → Ty → List Store.Val
  | 0, _ => []
  | n + 1, t =>
    let first (t : Ty) : List Store.Val := (samples decls n t).take 1
    let candidates : List Store.Val := match t with
      | .unit | .undefined => [.unit]
      | .nat | .number => [.nat 0, .nat 1, .nat 2]
      | .int => [.nat 0, .negInt 0]
      | .string => [.str "", .str "a"]
      | .bool => [.bool false, .bool true]
      | .lit text => [.str text]
      | .null => [.none]
      | .bytes => [.bytes []]
      | .unknown => [.unit]
      | .option a => .none :: (first a).map .some
      | .list a => .list [] :: (first a).flatMap fun x => [.list [x], .list [x, x]]
      | .prod a b => (first a).flatMap fun x => (first b).map fun y => .list [x, y]
      | .tuple ts =>
        match ts.mapM fun t => (first t).head? with
        | some xs => [.list xs]
        | none => []
      | .union a b => (samples decls n a).take 1 ++ (samples decls n b).take 1
      | .except e a => (first e).map (fun x => .ctor 0 [x]) ++ (first a).map (fun x => .ctor 1 [x])
      | .record fs =>
        match (fs.filter fun f => !f.2.1).mapM (fun f => (first f.2.2).head?.map (f.1, ·)) with
        | some kvs => [.ctor 0 [.list (kvs.map fun kv => .str kv.1), .list (kvs.map (·.2))]]
        | none => []
      | .map _ _ => [.list []]
      | .app _ _ =>
        match decls.unfold? t with
        | some (_, body) => samples decls n body
        | none => []
      | _ => []
    candidates.filter fun v => Val.memberIn decls v t []

/-- **The replies a row can give**, drawn from its types: a success at each sample of its answer
type, and a failure at each sample of its error column, each one that reply admission takes
(`replyFault`). -/
def replies (app : SigApp) (row : Nat) : List ExitV :=
  match (app.rows[row]?).map Program.Row.normalizeTypes with
  | none => []
  | some r =>
    let oks := (samples app.types 4 r.answer).map Exit.success
    let errs := (samples app.types 4 r.error).map fun v => (Exit.failure (Cause.fail (errOf v)) : ExitV)
    (oks ++ errs).filter fun ex => (replyFault app row ex).isNone

/-- **Every path of a program** at the budget `k`, its replies drawn from the rows' types
(`replies`), the first `width` in depth-first order. Each path's replies are a reply tape that
the machine, or rc.112, replays. -/
def explore (app : SigApp) (k width : Nat) (program : NativeEff) : List Tree.Path :=
  Tree.paths app.rows k (fun i _ => replies app i) width program

/-! ## The carriers' images -/

/-- A program's shape document. -/
def programShape : ShapeDoc := Canonical.shape NativeEff
/-- A program's value tree. -/
def programToVal (p : NativeEff) : Store.Val := Canonical.toVal p
/-- A program from its value tree, exactly. -/
def programOfVal (v : Store.Val) : Option NativeEff := Canonical.ofVal v

/-- A row table's shape document. -/
def rowsShape : ShapeDoc := Canonical.shape RowTable
/-- A row table's value tree. -/
def rowsToVal (rows : RowTable) : Store.Val := Canonical.toVal rows
/-- A row table from its value tree, exactly. -/
def rowsOfVal (v : Store.Val) : Option RowTable := Canonical.ofVal v

/-- The service declarations' shape document. -/
def servicesShape : ShapeDoc := Canonical.shape (List (ServiceKey × Ty))
/-- Service declarations from their value tree, exactly. -/
def servicesOfVal (v : Store.Val) : Option (List (ServiceKey × Ty)) := Canonical.ofVal v

/-- A type's shape document. -/
def tyShape : ShapeDoc := Canonical.shape Ty
/-- A type's value tree. -/
def tyToVal (t : Ty) : Store.Val := Canonical.toVal t

/-- A program type's shape document. -/
def effTyShape : ShapeDoc := Canonical.shape EffTy
/-- A program type's value tree. -/
def effTyToVal (t : EffTy) : Store.Val := Canonical.toVal t

/-- A refusal's shape document. -/
def refusalShape : ShapeDoc := Canonical.shape TypeRefusal
/-- A refusal's value tree. -/
def refusalToVal (r : TypeRefusal) : Store.Val := Canonical.toVal r

/-- An exit's shape document. -/
def exitShape : ShapeDoc := Canonical.shape ExitV
/-- An exit's value tree. -/
def exitToVal (ex : ExitV) : Store.Val := Canonical.toVal ex
/-- An exit from its value tree, exactly. -/
def exitOfVal (v : Store.Val) : Option ExitV := Canonical.ofVal v

/-- A value's shape document: the value tree itself. -/
def valShape : ShapeDoc := Canonical.shape Store.Val

/-- The TypeScript spelling of a type (`Ty.render`). -/
def tyText (t : Ty) : String := t.render

end Effect4.Run.Kit
