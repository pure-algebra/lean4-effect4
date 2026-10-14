import Tools.View.GraphContent
import Tools.View.FlowSpecimen

/-!
# Finite graph content controls

These controls compare content with the existing line fold on the real flow specimens.
They inspect syntax arguments, declared rows, and typing observations independently.
Rendered bytes appear only inside guards.
No control describes runtime execution or proves a general agreement theorem.
-/

open Effect4 Effect4.Program Tools.View

namespace GraphContentProbe

private def nodeAt (nodes : List GraphContent.Node) (path : List Nat) :
    Option GraphContent.Node :=
  nodes.find? fun n => decide (n.path = path)

private def entryAt (entries : List GraphContent.Entry) (path : List Nat) :
    Option GraphContent.Entry :=
  entries.find? fun e => decide (e.node.path = path)

private def typingAt (entries : List GraphContent.Entry) (path : List Nat) :
    Option Table.Entry :=
  (entryAt entries path).bind (·.typing)

private def rowAt (entries : List GraphContent.Entry) (path : List Nat) : Option Row :=
  (entryAt entries path).bind (·.operation) |>.bind (·.row)

-- The finite specimen comparison includes non-program families and suppressed list spines.
#guard FlowSpecimen.programs.all fun (_, _, p) =>
  let content := GraphContent.ofProgram p
  let lines := Program.lines p
  content.length == lines.length && (content.zip lines).all fun (n, l) =>
    n.path == l.path && n.depth == l.depth && decide (n.op = l.op) &&
      Program.ownText n.ctor n.arguments == l.text

#guard FlowSpecimen.programs.all fun (_, _, p) =>
  (GraphContent.ofProgram p).all fun n =>
    n.key == Program.bracket n.path && !Program.spine n.family

private def serviceProgram : NativeEff :=
  .provideService nativeScopeKey (.lit .unit) (.yieldNow 5)

-- Original argument order retains two non-child values before child zero.
#guard (nodeAt (GraphContent.ofProgram serviceProgram) []).any fun n =>
  match n.arguments with
  | [.key key, .term (.lit .unit), .child .eff ()] => decide (key = nativeScopeKey)
  | _ => false
#guard (GraphContent.ofProgram serviceProgram).map (·.path) == [[], [0]]
#guard (GraphContent.ofProgram serviceProgram).map (·.depth) == [0, 1]
#guard (nodeAt (GraphContent.ofProgram serviceProgram) [0]).any fun n =>
  match n.arguments with
  | [.nat 5] => true
  | _ => false

private def binderOp : NativeOp := .refModifyWith (.app "pair" (.cons (.var 0) (.cons (.var 0) .nil)))

-- An operation's binder remains original Term data inside NativeOp.
#guard (nodeAt (GraphContent.ofProgram (.perform binderOp (.var 0))) []).any fun n =>
  match n.arguments with
  | [.op op, .term (.var 0)] => decide (op = binderOp) && decide (n.op = some binderOp)
  | _ => false

private def admitted : EditSession :=
  EditSession.open {} { program := .bind (.succeed (.lit (.nat 7))) (.fail (.var 0)) }
private def admittedContent := GraphContent.ofSession admitted

#guard (typingAt admittedContent []).bind (·.result) =
  some (.ok ⟨.never, .nat, Effect4.Machine.Env.Requirement.empty⟩)
#guard (typingAt admittedContent [0]).bind (·.result) = some (.ok (EffTy.pure .nat))
#guard (typingAt admittedContent [1]).bind (·.env) = some (.env [.nat])
#guard (entryAt admittedContent [0]).bind (·.operation) |>.isNone
#guard (entryAt admittedContent [0]).bind (·.typeText) |>.isNone

private def refused : EditSession :=
  EditSession.open {} { program := .bind (.succeed (.var 0)) (.succeed (.lit .unit)) }
private def refusedContent := GraphContent.ofSession refused

-- The enclosing refusal retains its located child address.
#guard ((typingAt refusedContent []).bind (·.result)).any fun r =>
  match r with
  | .error refusal => refusal.path == [0]
  | .ok _ => false
#guard ((typingAt refusedContent [0]).bind (·.result)).any fun r =>
  match r with
  | .error refusal => refusal.path == [0]
  | .ok _ => false
-- An unreached sibling has an entry, but no environment or checker result.
#guard (typingAt refusedContent [1]).isSome
#guard (typingAt refusedContent [1]).bind (·.env) |>.isNone
#guard (typingAt refusedContent [1]).bind (·.result) |>.isNone
-- A supplied incomplete session table is distinct from that unreached entry.
#guard (typingAt (GraphContent.ofSession { admitted with table := [] }) [1]).isNone

private def serviceSession : EditSession :=
  EditSession.open {} { program := .service nativeScopeKey }

-- Requirements and variable environments remain different observations.
#guard ((typingAt (GraphContent.ofSession serviceSession) []).bind (·.result)).any fun r =>
  match r with
  | .ok t => !decide (t.requires = Effect4.Machine.Env.Requirement.empty)
  | .error _ => false
#guard (typingAt (GraphContent.ofSession serviceSession) []).bind (·.env) = some (.env [])

private def externalRow : Row :=
  { name := "lookup", spelling := "Cache.lookup", kind := .async,
    registration := .external, request := .string, answer := .nat, error := .string,
    cite := "probe" }
private def externalSession : EditSession :=
  EditSession.open { rows := [externalRow] }
    { program := .perform (.external 0) (.lit (.str "key")) }

#guard (rowAt (GraphContent.ofSession externalSession) []) = some externalRow
#guard ((entryAt (GraphContent.ofSession externalSession) []).bind (·.operation)).any fun op =>
  decide (op.value = .external 0)
#guard (rowAt (GraphContent.ofSession (EditSession.open {}
  { program := .perform (.external 0) (.lit .unit) })) []).isNone
#guard ((entryAt (GraphContent.ofSession (EditSession.open {}
  { program := .perform (.external 0) (.lit .unit) })) []).bind (·.operation)).isSome

private def holeSession : EditSession :=
  EditSession.open {} { program := Sketch.hole {} 0, holes := [Row.hole "remaining" .bool] }

#guard (rowAt (GraphContent.ofSession holeSession) []) = some (Row.hole "remaining" .bool)
#guard (typingAt (GraphContent.ofSession holeSession) []).bind (·.result) =
  some (.ok (EffTy.pure .bool))

private def declaration : DefDecl :=
  { name := "apply", request := .nat, answer := .nat,
    params := [{ name := "f", request := .nat, answer := .nat }] }
private def moduleSession : EditSession :=
  EditSession.open {} { program := (.defs [declaration]
      (.cons (.perform (.param 0) (.var 0)) .nil)
      (.invoke 0 (.lit (.nat 1)) (.cons (.succeed (.var 0)) .nil)) .nil) }

-- The local parameter row differs from the top-level placeholder for the same operation.
#guard (rowAt (GraphContent.ofSession moduleSession) [0, 0]) =
  (declaration.params[0]?).map ParamDecl.row
#guard (rowAt (GraphContent.ofSession (EditSession.open {}
  { program := .perform (.param 0) (.lit (.nat 1)) })) []).isNone
#guard ((nodeAt (GraphContent.ofProgram moduleSession.sketch.program) []).any fun n =>
  match n.arguments with
  | [.decls [d], .child .effs (), .child .eff (), .child .layers ()] => decide (d = declaration)
  | _ => false)

private def callDeclaration : DefDecl :=
  { name := "read", request := .nat, answer := .nat }
private def callSession : EditSession :=
  EditSession.open {} { program := (.defs [callDeclaration]
      (.cons (.succeed (.var 0)) .nil) (.perform (.call 0) (.lit (.nat 1))) .nil) }

#guard (rowAt (GraphContent.ofSession callSession) [1]) = some callDeclaration.row
#guard (rowAt (GraphContent.ofSession (EditSession.open {}
  { program := .perform (.call 0) (.lit (.nat 1)) })) []).isNone
-- Every spelled built-in reads its row without collapsing kind or registration fields.
#guard NativeOp.spelled.all fun op =>
  rowAt (GraphContent.ofSession (EditSession.open {}
    { program := .perform op (.lit .unit) })) [] == some op.row.normalizeTypes

private def deferredSession : EditSession :=
  EditSession.open {} { program := .perform (.deferredMakeOf .nat .string) (.lit .unit) }

#guard (typingAt (GraphContent.ofSession deferredSession) []).bind (·.result) =
  some (.ok (EffTy.pure (.deferredOf .nat .string)))

private def page : Page :=
  { title := "supplied display",
    lines := #[{ gutter := "", depth := 0, text := "", key := "[0]", type := "first display" },
      { gutter := "", depth := 0, text := "", key := "[0]", type := "second display" }] }
private def pageContent := GraphContent.ofSessionPage admitted page

#guard (entryAt pageContent [0]).bind (·.typeText) = some "first display"
#guard (entryAt pageContent [1]).bind (·.typeText) |>.isNone
#guard (typingAt pageContent [0]).bind (·.result) = some (.ok (EffTy.pure .nat))
#guard (typingAt (GraphContent.ofSession { admitted with
  table := ⟨[0], some (.env [.bool]), none⟩ :: admitted.table }) [0]).bind (·.env) =
  some (.env [.bool])

#eval IO.println s!"graph-content finite fixtures: {FlowSpecimen.programs.length} specimen programs"

end GraphContentProbe
