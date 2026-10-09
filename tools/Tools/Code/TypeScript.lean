import Tools.Code.Doc
import Tools.Code.TsFold
import TypeScript.Render

/-!
# Printed TypeScript: the house and the layout, two algebras of one syntax

The readable form of the printer's TypeScript (`Effect4.Codegen`, the pinned `TypeScript.Syntax`).
TypeScript's syntax (`Expr`, `Stmt`, `ObjectEntry`) is a free object whose fold is generated
(`Tools/Code/TsFold.lean`; slice F of `docs/research/2026-10-09-view-algebra-audit.md`). Two
printers are algebras of it:

- **the house** (`renderAlg`): the pinned renderer's text at each depth. The pinned renderer is
  its fold (`render_eq_expr`, `render_eq_stmt`), by uniqueness (`hom_eq_cata_expr`);
- **the layout** (`docAlg`): a document at each depth (`Tools.Code.Doc`). A call's arguments, an
  inline object's fields and an inline array's items form a group: flat as the house writes it,
  or one item a line. A block is the house's block. Where the house chooses between inline and
  multiline, the layout asks the same question of its children's flat prints.

They agree because their algebras do. The flat print is a map of algebras from the layout to the
house (`flatHom`): one square for each constructor, which assumes nothing of the children. So the
layout's fold, laid flat, is the house's fold (`flat_fold_expr`, `flat_fold_stmt`), and undoing a
layout's breaks gives it back (`undo_layout`). Every break of the layout is `delimited`'s, whose
alternatives differ only in whitespace, so a laid out file differs from the checked bytes only in
whitespace at breaks: by construction, until slice F2 of the algebra audit states it as a law. No
proof walks a whole expression: the fold does the walking, once, for every algebra.

The width of Effect's own source is 120 columns (`vendor/effect-4.0.1/src/internal/effect.ts`:
one line of 6,978 is longer), and generated files use it (`width`).
-/

namespace Tools.Code.Ts

open TypeScript Tools.Code Doc

/-- The width of a generated file: Effect's own. -/
def width : Nat := 120

/-- The house style of the pinned printer. -/
abbrev house : Style := house0

/-- Whether a rendered text holds a newline: the pinned renderer's own test, restated (its
definition is private there). -/
def hasNewline (value : String) : Bool := value.toUTF8.toList.contains 10

/-- The lines of a multiline literal: each on its own line, after a newline. -/
def lines : List Doc → Doc
  | [] => .nil
  | x :: rest => .hard ++ x ++ lines rest

/-- A multiline literal: `op`, its lines one level in, then `cl` on a line of its own. -/
def multiline (op cl : String) (items : List Doc) : Doc :=
  .text op ++ .block 2 (lines items) ++ .hard ++ .text cl

/-- A block of statements: `head`, the statements one level in, then `}` on a line of its own. -/
def braces (head : String) (body : Doc) : Doc := .text head ++ .block 2 body ++ .hard ++ .text "}"

/-- The text before a label's loop. -/
def labelText : Option String → String
  | some l => l ++ ": "
  | none => ""

/-! ## The house's clauses

Lean does not generate the equations of `TypeScript.Render.expr` in an importing module: the
generator stops at its fixed `whnf` limit (found 2026-10-09; the renderer's other functions
generate theirs). Each clause the laws below unfold is restated here, as the pinned renderer
writes it, and proved by `rfl`. An inline literal's test is `hasNewline`, the same function as
the renderer's private one. -/

section House
variable (d : Nat)

theorem house_call (fn : Expr) (args : List Expr) : Render.expr house d (.call fn args) =
    Render.expr house d fn ++ "(" ++ String.intercalate ", " (Render.exprs house d args) ++ ")" := rfl

/-- The house's inline-or-multiline choice for the fields of an object literal, the field written
by `name`. -/
def houseObject (name : String → String) (fields : List (String × Expr)) : String :=
  if fields.isEmpty then "{}"
  else
    let rendered := Render.objectFields house (d + 1) fields
    if rendered.all (fun field => !hasNewline field.2) then
      "{ " ++ String.intercalate ", " (rendered.map fun (n, value) => name n ++ ": " ++ value) ++ " }"
    else
      "{\n" ++ String.intercalate "\n" (rendered.map fun (n, value) =>
        Render.indentOf house (d + 1) ++ name n ++ ": " ++ value ++ ",") ++ "\n" ++
        Render.indentOf house d ++ "}"

/-- The house's multiline object literal, the field written by `name`. -/
def houseObjectML (name : String → String) (fields : List (String × Expr)) : String :=
  if fields.isEmpty then "{}"
  else
    "{\n" ++ String.intercalate "\n" ((Render.objectFields house (d + 1) fields).map fun (n, value) =>
      Render.indentOf house (d + 1) ++ name n ++ ": " ++ value ++ ",") ++ "\n" ++
      Render.indentOf house d ++ "}"

theorem house_object (fields : List (String × Expr)) :
    Render.expr house d (.object fields) = houseObject d (fun n => n) fields := rfl
theorem house_objectML (fields : List (String × Expr)) :
    Render.expr house d (.objectML fields) = houseObjectML d (fun n => n) fields := rfl
theorem house_objectQuoted (fields : List (String × Expr)) :
    Render.expr house d (.objectQuoted fields) = houseObject d (Render.quoted house) fields := rfl
theorem house_objectQuotedML (fields : List (String × Expr)) :
    Render.expr house d (.objectQuotedML fields) = houseObjectML d (Render.quoted house) fields := rfl

theorem house_objectFromEntries (fields : List (String × Expr)) :
    Render.expr house d (.objectFromEntries fields) =
      "Object.fromEntries([" ++ String.intercalate ", " ((Render.objectFields house d fields).map
        fun (name, value) => "[" ++ Render.quoted house name ++ ", " ++ value ++ "]") ++ "])" := rfl

theorem house_arr (items : List Expr) : Render.expr house d (.arr items) =
    if items.isEmpty then "[]"
    else
      let rendered := Render.exprs house (d + 1) items
      if rendered.all (fun item => !hasNewline item) then "[" ++ String.intercalate ", " rendered ++ "]"
      else
        "[\n" ++ String.intercalate "\n" (rendered.map fun item =>
          Render.indentOf house (d + 1) ++ item ++ ",") ++ "\n" ++ Render.indentOf house d ++ "]" := rfl

theorem house_arrow (returnType : Option TypeRef) (body : Expr) :
    Render.expr house d (.arrow returnType body) =
      "()" ++ Render.annotation house returnType ++ " => " ++ Render.expr house d body := rfl

theorem house_generic (fn : Expr) (typeArgs : List TypeRef) : Render.expr house d (.generic fn typeArgs) =
    Render.expr house d fn ++ "<" ++ String.intercalate ", " (Render.types house typeArgs) ++ ">" := rfl

theorem house_lambda (params : List Parameter) (body : Expr) (returnType : Option TypeRef) :
    Render.expr house d (.lambda params body returnType) =
      "(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
        Render.annotation house returnType ++ " => " ++ Render.expr house d body := rfl

theorem house_method (target : Expr) (name : String) (args : List Expr) :
    Render.expr house d (.method target name args) =
      Render.expr house d target ++ "." ++ name ++ "(" ++
        String.intercalate ", " (Render.exprs house d args) ++ ")" := rfl

theorem house_member (target : Expr) (name : String) :
    Render.expr house d (.member target name) = Render.expr house d target ++ "." ++ name := rfl

theorem house_generator (body : List Stmt) : Render.expr house d (.generator body) =
    "function* () {\n" ++ Render.stmts house (d + 1) body ++ Render.indentOf house d ++ "}" := rfl

theorem house_cond (test thenBranch elseBranch : Expr) :
    Render.expr house d (.cond test thenBranch elseBranch) =
      Render.expr house d test ++ " ? " ++ Render.expr house d thenBranch ++ " : " ++
        Render.expr house d elseBranch := rfl

theorem house_arrowBlock (params : List Parameter) (body : List Stmt) (returnType : Option TypeRef) :
    Render.expr house d (.arrowBlock params body returnType) =
      "(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
        Render.annotation house returnType ++ " => {\n" ++ Render.stmts house (d + 1) body ++
        Render.indentOf house d ++ "}" := rfl

theorem house_index (target key : Expr) : Render.expr house d (.index target key) =
    Render.expr house d target ++ "[" ++ Render.expr house d key ++ "]" := rfl

theorem house_new (callee : Expr) (args : List Expr) : Render.expr house d (.new callee args) =
    "new " ++ Render.expr house d callee ++ "(" ++ String.intercalate ", " (Render.exprs house d args) ++ ")" :=
  rfl

theorem house_objectWith (keys : KeyForm) (entries : List ObjectEntry) :
    Render.expr house d (.objectWith keys entries) =
      if entries.isEmpty then "{}"
      else
        let rendered := Render.objectEntries house keys (d + 1) entries
        if rendered.all (fun entry => !hasNewline entry.2) then
          "{ " ++ String.intercalate ", " (rendered.map fun (head, value) => head ++ value) ++ " }"
        else
          "{\n" ++ String.intercalate "\n" (rendered.map fun (head, value) =>
            Render.indentOf house (d + 1) ++ head ++ value ++ ",") ++ "\n" ++
            Render.indentOf house d ++ "}" := rfl

end House

/-! ## Laying a literal flat -/

/-- The lines of a multiline literal, laid flat at the indent `c`, against the house's lines joined
by newlines: each line is the indent and its item's flat print. -/
theorem flat_lines {α : Type} (c : Nat) (F : α → Doc) (G : α → String)
    (hFG : ∀ a, spaces c ++ (F a).flat c = G a) :
    ∀ (l : List α), l ≠ [] → ∀ rest : String,
      "\n" ++ (String.intercalate "\n" (l.map G) ++ rest) = (lines (l.map F)).flat c ++ rest
  | [], h, _ => absurd rfl h
  | [a], _, rest => by
    simp only [List.map_cons, List.map_nil, String.intercalate_singleton, lines, Doc.append_def,
      Doc.flat, ← hFG, String.append_assoc, String.append_empty]
  | a :: b :: l, _, rest => by
    have ih := flat_lines c F G hFG (b :: l) (List.cons_ne_nil b l) rest
    simp only [List.map_cons] at ih
    simp only [List.map_cons, String.intercalate_cons_cons, String.append_assoc]
    rw [ih]
    simp only [lines, Doc.append_def, Doc.flat, ← hFG, String.append_assoc]

/-- A multiline literal laid flat at the house's depth `d` is the house's multiline literal over the
items' renderings `P`, each line written by `g`. -/
theorem flat_multiline {α β : Type} (d : Nat) (op cl : String) (xs : List α) (F : α → Doc)
    (P : α → β) (g : β → String) (hx : xs ≠ [])
    (hFG : ∀ a, spaces (2 * (d + 1)) ++ (F a).flat (2 * (d + 1)) = g (P a)) :
    (multiline op cl (xs.map F)).flat (2 * d) =
      op ++ ("\n" ++ (String.intercalate "\n" ((xs.map P).map g) ++ ("\n" ++ (Render.indentOf house d ++ cl)))) := by
  rw [List.map_map, flat_lines (2 * (d + 1)) F (g ∘ P) hFG xs hx]
  simp only [multiline, Doc.append_def, Doc.flat, String.append_assoc]
  rfl

/-- The inline form of a literal laid flat: its items' texts joined by `", "` between its padded
delimiters. -/
theorem flat_inline {β : Type} (b : Nat) (op cl pad : String) (xs : List β) (T : β → String)
    (hx : xs ≠ []) :
    (delimited op cl pad (xs.map fun x => .text (T x))).flat b =
      op ++ pad ++ String.intercalate ", " (xs.map T) ++ pad ++ cl := by
  rw [flat_delimited b op cl pad _ (by simpa only [ne_eq, List.map_eq_nil_iff] using hx), List.map_map]
  rfl

/-- `"X\n"` as `"X" ++ "\n"`: the house writes a newline inside a literal, a document as a hard
break. -/
theorem nl_split (y x : String) (h : x ++ "\n" = y := by rfl) : y = x ++ "\n" := h.symm

/-! ## The house as an algebra -/

/-- What the house writes for each sort: an expression's text and a statement's text at a depth;
an object entry's head and value at a key form and a depth. -/
abbrev Text : ExprFam → Type
  | .expr => Nat → String
  | .stmt => Nat → String
  | .objectentry => KeyForm → Nat → String × String

/-- Statements' texts at a depth, one a line, each followed by a newline. -/
def stmtsText : List (Nat → String) → Nat → String
  | [], _ => ""
  | s :: rest, d => s d ++ "\n" ++ stmtsText rest d

/-- A switch's cases' texts at a depth: each case's head, its block, and its brace. -/
def casesText : List (Nat × List (Nat → String)) → Nat → String
  | [], _ => ""
  | (i, body) :: rest, d =>
    Render.indentOf house d ++ "case " ++ toString i ++ ": {\n" ++ stmtsText body (d + 1) ++
      Render.indentOf house d ++ "}\n" ++ casesText rest d

/-- The house's object literal over its rendered fields: inline when no field holds a newline,
else one field a line; each field's name written by `name`. -/
def objectText (name : String → String) (rendered : List (String × String)) (d : Nat) : String :=
  if rendered.isEmpty then "{}"
  else if rendered.all (fun field => !hasNewline field.2) then
    "{ " ++ String.intercalate ", " (rendered.map fun (n, value) => name n ++ ": " ++ value) ++ " }"
  else
    "{\n" ++ String.intercalate "\n" (rendered.map fun (n, value) =>
      Render.indentOf house (d + 1) ++ name n ++ ": " ++ value ++ ",") ++ "\n" ++
      Render.indentOf house d ++ "}"

/-- The house's multiline object literal over its rendered fields. -/
def objectMLText (name : String → String) (rendered : List (String × String)) (d : Nat) : String :=
  if rendered.isEmpty then "{}"
  else
    "{\n" ++ String.intercalate "\n" (rendered.map fun (n, value) =>
      Render.indentOf house (d + 1) ++ name n ++ ": " ++ value ++ ",") ++ "\n" ++
      Render.indentOf house d ++ "}"

/-- The fields of an object, each value at the depth `d`. -/
def at_ (fields : List (String × (Nat → String))) (d : Nat) : List (String × String) :=
  fields.map fun p => (p.1, p.2 d)

/-- **The house**, an algebra of the syntax: each field is a clause of `TypeScript.Render`, written
over its children's texts. -/
def renderAlg : ExprAlgebra Text where
  expr_ident name := fun _ => name
  expr_str value := fun _ => Render.quoted house value
  expr_int value := fun _ => toString value
  expr_float64Bits bits := fun _ => Render.float64Bits bits
  expr_bool value := fun _ => if value then "true" else "false"
  expr_jsNull := fun _ => "null"
  expr_call fn args := fun d => fn d ++ "(" ++ String.intercalate ", " (args.map (· d)) ++ ")"
  expr_object fields := fun d => objectText (fun n => n) (at_ fields (d + 1)) d
  expr_objectML fields := fun d => objectMLText (fun n => n) (at_ fields (d + 1)) d
  expr_objectQuoted fields := fun d => objectText (Render.quoted house) (at_ fields (d + 1)) d
  expr_objectQuotedML fields := fun d => objectMLText (Render.quoted house) (at_ fields (d + 1)) d
  expr_objectFromEntries fields := fun d =>
    "Object.fromEntries([" ++ String.intercalate ", " ((at_ fields d).map fun (name, value) =>
      "[" ++ Render.quoted house name ++ ", " ++ value ++ "]") ++ "])"
  expr_arr items := fun d =>
    if items.isEmpty then "[]"
    else
      let rendered := items.map (· (d + 1))
      if rendered.all (fun item => !hasNewline item) then "[" ++ String.intercalate ", " rendered ++ "]"
      else
        "[\n" ++ String.intercalate "\n" (rendered.map fun item =>
          Render.indentOf house (d + 1) ++ item ++ ",") ++ "\n" ++ Render.indentOf house d ++ "]"
  expr_arrow returnType body := fun d => "()" ++ Render.annotation house returnType ++ " => " ++ body d
  expr_generic fn typeArgs := fun d =>
    fn d ++ "<" ++ String.intercalate ", " (Render.types house typeArgs) ++ ">"
  expr_lambda params body returnType := fun d =>
    "(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
      Render.annotation house returnType ++ " => " ++ body d
  expr_method target name args := fun d =>
    target d ++ "." ++ name ++ "(" ++ String.intercalate ", " (args.map (· d)) ++ ")"
  expr_member target name := fun d => target d ++ "." ++ name
  expr_generator body := fun d =>
    "function* () {\n" ++ stmtsText body (d + 1) ++ Render.indentOf house d ++ "}"
  expr_cond test thenBranch elseBranch := fun d =>
    test d ++ " ? " ++ thenBranch d ++ " : " ++ elseBranch d
  expr_arrowBlock params body returnType := fun d =>
    "(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
      Render.annotation house returnType ++ " => {\n" ++ stmtsText body (d + 1) ++
      Render.indentOf house d ++ "}"
  expr_index target key := fun d => target d ++ "[" ++ key d ++ "]"
  expr_new callee args := fun d =>
    "new " ++ callee d ++ "(" ++ String.intercalate ", " (args.map (· d)) ++ ")"
  expr_objectWith keys entries := fun d =>
    if entries.isEmpty then "{}"
    else
      let rendered := entries.map (· keys (d + 1))
      if rendered.all (fun entry => !hasNewline entry.2) then
        "{ " ++ String.intercalate ", " (rendered.map fun (head, value) => head ++ value) ++ " }"
      else
        "{\n" ++ String.intercalate "\n" (rendered.map fun (head, value) =>
          Render.indentOf house (d + 1) ++ head ++ value ++ ",") ++ "\n" ++
          Render.indentOf house d ++ "}"
  stmt_constYield name value declaredType := fun d =>
    Render.indentOf house d ++ "const " ++ name ++ Render.annotation house declaredType ++
      " = yield* " ++ value d
  stmt_ret value := fun d => Render.indentOf house d ++ "return " ++ value d
  stmt_yieldDiscard value := fun d => Render.indentOf house d ++ "yield* " ++ value d
  stmt_letDefinite name declaredType := fun d =>
    Render.indentOf house d ++ "let " ++ name ++ "!: " ++ Render.type house declaredType
  stmt_letInit name value declaredType := fun d =>
    Render.indentOf house d ++ "let " ++ name ++ Render.annotation house declaredType ++ " = " ++ value d
  stmt_assign name value := fun d => Render.indentOf house d ++ name ++ " = " ++ value d
  stmt_whileTrue label body := fun d =>
    Render.indentOf house d ++ (match label with | some l => l ++ ": " | none => "") ++
      "while (true) {\n" ++ stmtsText body (d + 1) ++ Render.indentOf house d ++ "}"
  stmt_switch scrutinee cases := fun d =>
    Render.indentOf house d ++ "switch (" ++ scrutinee d ++ ") {\n" ++ casesText cases (d + 1) ++
      Render.indentOf house d ++ "}"
  stmt_ifElse condition thenBranch elseBranch := fun d =>
    Render.indentOf house d ++ "if (" ++ condition d ++ ") {\n" ++ stmtsText thenBranch (d + 1) ++
      Render.indentOf house d ++ "}" ++
      (if elseBranch.isEmpty then ""
       else " else {\n" ++ stmtsText elseBranch (d + 1) ++ Render.indentOf house d ++ "}")
  stmt_labelled label body := fun d =>
    Render.indentOf house d ++ label ++ ": {\n" ++ stmtsText body (d + 1) ++ Render.indentOf house d ++ "}"
  stmt_scopedGen name body onExit := fun d =>
    Render.indentOf house d ++ "const " ++ name ++
      " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
      stmtsText body (d + 1) ++ Render.indentOf house d ++ "}), " ++ onExit d ++ "))"
  stmt_scopedGenMasked name body onExit := fun d =>
    Render.indentOf house d ++ "const " ++ name ++
      " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
      stmtsText body (d + 1) ++ Render.indentOf house d ++ "}), " ++ onExit d ++ ")))"
  stmt_breakTo label := fun d =>
    Render.indentOf house d ++ "break" ++ (match label with | some l => " " ++ l | none => "")
  stmt_continueTo label := fun d =>
    Render.indentOf house d ++ "continue" ++ (match label with | some l => " " ++ l | none => "")
  stmt_exprStmt value := fun d => Render.indentOf house d ++ value d
  objectentry_property name value := fun keys d => (Render.propertyName house keys name ++ ": ", value d)
  objectentry_spread value := fun _ d => ("...", value d)

/-! ## The pinned renderer is the house's fold -/

/-- An object entry as the house writes it: its head and its value. -/
def houseEntry (e : ObjectEntry) : KeyForm → Nat → String × String :=
  fun keys d => match e with
    | .property name value => (Render.propertyName house keys name ++ ": ", Render.expr house d value)
    | .spread value => ("...", Render.expr house d value)

theorem exprs_eq (d : Nat) : ∀ xs : List Expr, Render.exprs house d xs = (xs.map fun e d => Render.expr house d e).map (· d)
  | [] => rfl
  | x :: xs => by simp only [Render.exprs, exprs_eq d xs, List.map_cons, List.map_map]

theorem objectFields_eq (d : Nat) : ∀ fs : List (String × Expr),
    Render.objectFields house d fs = at_ (fs.map (prodMapSnd fun e d => Render.expr house d e)) d
  | [] => rfl
  | (n, v) :: fs => by simp only [Render.objectFields, objectFields_eq d fs, at_, List.map_cons, prodMapSnd_mk]

theorem objectEntries_eq (keys : KeyForm) (d : Nat) : ∀ es : List ObjectEntry,
    Render.objectEntries house keys d es = (es.map houseEntry).map (· keys d)
  | [] => rfl
  | .property n v :: es => by simp only [Render.objectEntries, objectEntries_eq keys d es, List.map_cons, houseEntry]
  | .spread v :: es => by simp only [Render.objectEntries, objectEntries_eq keys d es, List.map_cons, houseEntry]

theorem stmts_eq (d : Nat) : ∀ ss : List Stmt,
    Render.stmts house d ss = stmtsText (ss.map fun s d => Render.stmt house d s) d
  | [] => rfl
  | s :: ss => by simp only [Render.stmts, stmts_eq d ss, List.map_cons, stmtsText]

theorem switchCases_eq (d : Nat) : ∀ cs : List (Nat × List Stmt),
    Render.switchCases house d cs =
      casesText (cs.map (prodMapSnd (List.map fun s d => Render.stmt house d s))) d
  | [] => rfl
  | (i, body) :: cs => by
    simp only [Render.switchCases, switchCases_eq d cs, stmts_eq, List.map_cons, prodMapSnd_mk, casesText]

/-- The pinned renderer, as a homomorphism of the house's algebra. -/
def renderHom : ExprHom renderAlg := by
  apply ExprHom.mk (f_expr := fun e d => Render.expr house d e) (f_stmt := fun s d => Render.stmt house d s)
    (f_objectentry := houseEntry)
  all_goals intros
  all_goals funext d
  case h_expr_call => rw [house_call, exprs_eq]; rfl
  case h_expr_method => rw [house_method, exprs_eq]; rfl
  case h_expr_new => rw [house_new, exprs_eq]; rfl
  case h_expr_object =>
    simp only [renderAlg, house_object, houseObject, objectText, objectFields_eq, at_, List.isEmpty_map]
    rfl
  case h_expr_objectML =>
    simp only [renderAlg, house_objectML, houseObjectML, objectMLText, objectFields_eq, at_, List.isEmpty_map]
  case h_expr_objectQuoted =>
    simp only [renderAlg, house_objectQuoted, houseObject, objectText, objectFields_eq, at_, List.isEmpty_map]
    rfl
  case h_expr_objectQuotedML =>
    simp only [renderAlg, house_objectQuotedML, houseObjectML, objectMLText, objectFields_eq, at_, List.isEmpty_map]
  case h_expr_objectFromEntries => rw [house_objectFromEntries, objectFields_eq]; rfl
  case h_expr_arr => simp only [renderAlg, house_arr, exprs_eq, List.isEmpty_map]
  case h_expr_generator => rw [house_generator, stmts_eq]; rfl
  case h_expr_arrowBlock => rw [house_arrowBlock, stmts_eq]; rfl
  case h_expr_objectWith => simp only [renderAlg, house_objectWith, objectEntries_eq, List.isEmpty_map]
  case h_stmt_whileTrue => simp only [Render.stmt, stmts_eq]; rfl
  case h_stmt_switch => simp only [Render.stmt, switchCases_eq]; rfl
  case h_stmt_ifElse => simp only [renderAlg, Render.stmt, stmts_eq, List.isEmpty_map]
  case h_stmt_labelled => simp only [Render.stmt, stmts_eq]; rfl
  case h_stmt_scopedGen => simp only [Render.stmt, stmts_eq]; rfl
  case h_stmt_scopedGenMasked => simp only [Render.stmt, stmts_eq]; rfl
  all_goals rfl

/-- **The pinned renderer is the house's fold**, for an expression. -/
theorem render_eq_expr (e : Expr) (d : Nat) : cata_expr renderAlg e d = Render.expr house d e :=
  (congrFun (hom_eq_cata_expr renderHom e) d).symm

/-- The pinned renderer is the house's fold, for a statement. -/
theorem render_eq_stmt (s : Stmt) (d : Nat) : cata_stmt renderAlg s d = Render.stmt house d s :=
  (congrFun (hom_eq_cata_stmt renderHom s) d).symm

/-! ## The readable layout as an algebra -/

/-- What the layout gives each sort: an expression's document and a statement's document (without
its indent) at a depth; an object entry's head and its value's document. -/
abbrev Laid : ExprFam → Type
  | .expr => Nat → Doc
  | .stmt => Nat → Doc
  | .objectentry => KeyForm → Nat → String × Doc

/-- Statements' documents at a depth, each after a hard break. -/
def stmtsDoc : List (Nat → Doc) → Nat → Doc
  | [], _ => .nil
  | s :: rest, d => .hard ++ s d ++ stmtsDoc rest d

/-- A switch's cases' documents at a depth, each after a hard break with its block. -/
def casesDoc : List (Nat × List (Nat → Doc)) → Nat → Doc
  | [], _ => .nil
  | (i, body) :: rest, d =>
    .hard ++ braces ("case " ++ toString i ++ ": {") (stmtsDoc body (d + 1)) ++ casesDoc rest d

/-- An expression's document laid flat at its depth: the house's text, by `flat_fold_expr`. -/
def flatE (r : Nat → Doc) : Nat → String := fun d => (r d).flat (2 * d)

/-- A statement's document laid flat after its indent. -/
def flatS (r : Nat → Doc) : Nat → String := fun d => Render.indentOf house d ++ (r d).flat (2 * d)

/-- An object entry's head, and its value laid flat. -/
def flatO (r : KeyForm → Nat → String × Doc) : KeyForm → Nat → String × String :=
  fun keys d => ((r keys d).1, (r keys d).2.flat (2 * d))

/-- An object literal's document: inline when no field's flat print holds a newline, as the house
decides, else one field a line. -/
def objectDoc (name : String → String) (fields : List (String × (Nat → Doc))) (d : Nat) : Doc :=
  if fields.isEmpty then .text "{}"
  else
    let rendered := at_ (fields.map (prodMapSnd flatE)) (d + 1)
    if rendered.all (fun field => !hasNewline field.2) then
      delimited "{" "}" " " (rendered.map fun p => .text (name p.1 ++ ": " ++ p.2))
    else
      multiline "{" "}" (fields.map fun p => .text (name p.1 ++ ": ") ++ p.2 (d + 1) ++ .text ",")

/-- A multiline object literal's document. -/
def objectMLDoc (name : String → String) (fields : List (String × (Nat → Doc))) (d : Nat) : Doc :=
  if fields.isEmpty then .text "{}"
  else multiline "{" "}" (fields.map fun p => .text (name p.1 ++ ": ") ++ p.2 (d + 1) ++ .text ",")

/-- **The readable layout**, an algebra of the syntax: a call's arguments, an inline object's
fields and an inline array's items form a group, flat when they fit and one a line when not; a
block is the house's block. Where the house chooses between inline and multiline, the layout
asks the same question of its children's flat prints. -/
def docAlg : ExprAlgebra Laid where
  expr_ident name := fun _ => .text name
  expr_str value := fun _ => .text (Render.quoted house value)
  expr_int value := fun _ => .text (toString value)
  expr_float64Bits bits := fun _ => .text (Render.float64Bits bits)
  expr_bool value := fun _ => .text (if value then "true" else "false")
  expr_jsNull := fun _ => .text "null"
  expr_call fn args := fun d => fn d ++ delimited "(" ")" "" (args.map (· d))
  expr_object fields := objectDoc (fun n => n) fields
  expr_objectML fields := objectMLDoc (fun n => n) fields
  expr_objectQuoted fields := objectDoc (Render.quoted house) fields
  expr_objectQuotedML fields := objectMLDoc (Render.quoted house) fields
  expr_objectFromEntries fields := fun d =>
    .text "Object.fromEntries(" ++
      delimited "[" "]" "" (fields.map fun p => .text ("[" ++ Render.quoted house p.1 ++ ", ") ++ p.2 d ++ .text "]") ++
      .text ")"
  expr_arr items := fun d =>
    if items.isEmpty then .text "[]"
    else
      let rendered := (items.map flatE).map (· (d + 1))
      if rendered.all (fun item => !hasNewline item) then delimited "[" "]" "" (rendered.map .text)
      else multiline "[" "]" (items.map fun item => item (d + 1) ++ .text ",")
  expr_arrow returnType body := fun d => .text ("()" ++ Render.annotation house returnType ++ " => ") ++ body d
  expr_generic fn typeArgs := fun d =>
    fn d ++ .text ("<" ++ String.intercalate ", " (Render.types house typeArgs) ++ ">")
  expr_lambda params body returnType := fun d =>
    .text ("(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
      Render.annotation house returnType ++ " => ") ++ body d
  expr_method target name args := fun d =>
    target d ++ .text ("." ++ name) ++ delimited "(" ")" "" (args.map (· d))
  expr_member target name := fun d => target d ++ .text ("." ++ name)
  expr_generator body := fun d => braces "function* () {" (stmtsDoc body (d + 1))
  expr_cond test thenBranch elseBranch := fun d =>
    test d ++ .text " ? " ++ thenBranch d ++ .text " : " ++ elseBranch d
  expr_arrowBlock params body returnType := fun d =>
    braces ("(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
      Render.annotation house returnType ++ " => {") (stmtsDoc body (d + 1))
  expr_index target key := fun d => target d ++ .text "[" ++ key d ++ .text "]"
  expr_new callee args := fun d => .text "new " ++ callee d ++ delimited "(" ")" "" (args.map (· d))
  expr_objectWith keys entries := fun d =>
    if entries.isEmpty then .text "{}"
    else
      let rendered := (entries.map flatO).map (· keys (d + 1))
      if rendered.all (fun entry => !hasNewline entry.2) then
        delimited "{" "}" " " (rendered.map fun p => .text (p.1 ++ p.2))
      else
        multiline "{" "}" (entries.map fun e => .text (e keys (d + 1)).1 ++ (e keys (d + 1)).2 ++ .text ",")
  stmt_constYield name value declaredType := fun d =>
    .text ("const " ++ name ++ Render.annotation house declaredType ++ " = yield* ") ++ value d
  stmt_ret value := fun d => .text "return " ++ value d
  stmt_yieldDiscard value := fun d => .text "yield* " ++ value d
  stmt_letDefinite name declaredType := fun _ => .text ("let " ++ name ++ "!: " ++ Render.type house declaredType)
  stmt_letInit name value declaredType := fun d =>
    .text ("let " ++ name ++ Render.annotation house declaredType ++ " = ") ++ value d
  stmt_assign name value := fun d => .text (name ++ " = ") ++ value d
  stmt_whileTrue label body := fun d => braces (labelText label ++ "while (true) {") (stmtsDoc body (d + 1))
  stmt_switch scrutinee cases := fun d =>
    .text "switch (" ++ scrutinee d ++ braces ") {" (casesDoc cases (d + 1))
  stmt_ifElse condition thenBranch elseBranch := fun d =>
    .text "if (" ++ condition d ++ braces ") {" (stmtsDoc thenBranch (d + 1)) ++
      (if elseBranch.isEmpty then .nil else braces " else {" (stmtsDoc elseBranch (d + 1)))
  stmt_labelled label body := fun d => braces (label ++ ": {") (stmtsDoc body (d + 1))
  stmt_scopedGen name body onExit := fun d =>
    braces ("const " ++ name ++ " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {")
      (stmtsDoc body (d + 1)) ++ .text "), " ++ onExit d ++ .text "))"
  stmt_scopedGenMasked name body onExit := fun d =>
    braces ("const " ++ name ++
      " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {")
      (stmtsDoc body (d + 1)) ++ .text "), " ++ onExit d ++ .text ")))"
  stmt_breakTo label := fun _ => .text ("break" ++ (match label with | some l => " " ++ l | none => ""))
  stmt_continueTo label := fun _ => .text ("continue" ++ (match label with | some l => " " ++ l | none => ""))
  stmt_exprStmt value := value
  objectentry_property name value := fun keys d => (Render.propertyName house keys name ++ ": ", value d)
  objectentry_spread value := fun _ d => ("...", value d)

/-! ## The flat print is a map of algebras -/

/-- Statements laid flat, after a newline: the house's lines of their flat prints. -/
theorem flat_stmtsDoc (d : Nat) : ∀ (ss : List (Nat → Doc)) (rest : String),
    "\n" ++ (stmtsText (ss.map flatS) d ++ rest) = (stmtsDoc ss d).flat (2 * d) ++ ("\n" ++ rest)
  | [], rest => by simp only [List.map_nil, stmtsText, stmtsDoc, Doc.flat, String.empty_append]
  | s :: ss, rest => by
    have ih := flat_stmtsDoc d ss rest
    simp only [List.map_cons, stmtsText, stmtsDoc, Doc.append_def, Doc.flat, flatS, String.append_assoc]
    rw [ih]
    rfl

/-- A switch's cases laid flat, after a newline: the house's cases. -/
theorem flat_casesDoc (d : Nat) : ∀ (cs : List (Nat × List (Nat → Doc))) (rest : String),
    "\n" ++ (casesText (cs.map (prodMapSnd (List.map flatS))) d ++ rest) =
      (casesDoc cs d).flat (2 * d) ++ ("\n" ++ rest)
  | [], rest => by simp only [List.map_nil, casesText, casesDoc, Doc.flat, String.empty_append]
  | (i, body) :: cs, rest => by
    have ihb := flat_stmtsDoc (d + 1) body
      (Render.indentOf house d ++ ("}" ++ ("\n" ++ (casesText (cs.map (prodMapSnd (List.map flatS))) d ++ rest))))
    have ih := flat_casesDoc d cs rest
    simp only [List.map_cons, prodMapSnd_mk, casesText, casesDoc, braces, Doc.append_def, Doc.flat,
      String.append_assoc]
    rw [nl_split ": {\n" ": {", show ("}\n" : String) = "}" ++ "\n" from rfl]
    simp only [String.append_assoc]
    rw [ihb, ih]
    rfl

/-- A delimited list laid flat: its items' flat prints joined by `", "`, between its delimiters. -/
theorem flat_delimited_any (b : Nat) (op cl : String) : ∀ xs : List Doc,
    (delimited op cl "" xs).flat b = op ++ String.intercalate ", " (xs.map (·.flat b)) ++ cl
  | [] => by simp only [flat_delimited_nil, List.map_nil, String.intercalate_nil, String.append_empty]
  | x :: xs => by
    rw [flat_delimited b op cl "" _ (List.cons_ne_nil x xs)]
    simp only [String.append_empty]

/-- The fields of an object, laid flat at a depth. -/
theorem at_flat (fields : List (String × (Nat → Doc))) (d : Nat) :
    at_ (fields.map (prodMapSnd flatE)) d = fields.map fun p => (p.1, flatE p.2 d) := by
  simp only [at_, List.map_map]
  rfl

/-- An object literal's document laid flat is the house's object literal over the fields' flat
prints. -/
theorem flat_objectDoc (name : String → String) (fields : List (String × (Nat → Doc))) (d : Nat) :
    (objectDoc name fields d).flat (2 * d) = objectText name (at_ (fields.map (prodMapSnd flatE)) (d + 1)) d := by
  cases fields with
  | nil => rfl
  | cons f fs =>
    have hr : at_ ((f :: fs).map (prodMapSnd flatE)) (d + 1) ≠ [] := by
      simp only [at_, List.map_cons]; exact List.cons_ne_nil _ _
    simp only [objectDoc, objectText, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    have hne : (at_ ((f :: fs).map (prodMapSnd flatE)) (d + 1)).isEmpty = false := by
      simp only [at_, List.map_cons, List.isEmpty_cons]
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hn : ((at_ ((f :: fs).map (prodMapSnd flatE)) (d + 1)).all fun field => !hasNewline field.2) = true
    · simp only [hn, ↓reduceIte]
      rw [flat_inline _ _ _ _ _ _ hr]
      simp only [String.append_assoc]
      rfl
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
      rw [at_flat, flat_multiline d "{" "}" _ _ (fun p => (p.1, flatE p.2 (d + 1)))
        (fun q => Render.indentOf house (d + 1) ++ name q.1 ++ ": " ++ q.2 ++ ",") (List.cons_ne_nil f fs)
        (fun a => by simp only [Doc.append_def, Doc.flat, flatE, String.append_assoc]; rfl),
        nl_split "{\n" "{"]
      simp only [String.append_assoc]

/-- A multiline object literal's document laid flat is the house's. -/
theorem flat_objectMLDoc (name : String → String) (fields : List (String × (Nat → Doc))) (d : Nat) :
    (objectMLDoc name fields d).flat (2 * d) = objectMLText name (at_ (fields.map (prodMapSnd flatE)) (d + 1)) d := by
  cases fields with
  | nil => rfl
  | cons f fs =>
    have hne : (at_ ((f :: fs).map (prodMapSnd flatE)) (d + 1)).isEmpty = false := by
      simp only [at_, List.map_cons, List.isEmpty_cons]
    simp only [objectMLDoc, objectMLText, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [at_flat, flat_multiline d "{" "}" _ _ (fun p => (p.1, flatE p.2 (d + 1)))
      (fun q => Render.indentOf house (d + 1) ++ name q.1 ++ ": " ++ q.2 ++ ",") (List.cons_ne_nil f fs)
      (fun a => by simp only [Doc.append_def, Doc.flat, flatE, String.append_assoc]; rfl),
      nl_split "{\n" "{"]
    simp only [String.append_assoc]

/-- A block of statements laid flat: its head, a newline, the house's lines, the indent and the
brace, then whatever follows. -/
theorem flat_block (head : String) (ss : List (Nat → Doc)) (d : Nat) (tail : String) :
    (braces head (stmtsDoc ss (d + 1))).flat (2 * d) ++ tail =
      head ++ ("\n" ++ (stmtsText (ss.map flatS) (d + 1) ++ (Render.indentOf house d ++ ("}" ++ tail)))) := by
  rw [flat_stmtsDoc (d + 1) ss]
  simp only [braces, Doc.append_def, Doc.flat, String.append_assoc]
  rfl

/-- A switch's block of cases laid flat. -/
theorem flat_blockCases (head : String) (cs : List (Nat × List (Nat → Doc))) (d : Nat) (tail : String) :
    (braces head (casesDoc cs (d + 1))).flat (2 * d) ++ tail =
      head ++ ("\n" ++ (casesText (cs.map (prodMapSnd (List.map flatS))) (d + 1) ++
        (Render.indentOf house d ++ ("}" ++ tail)))) := by
  rw [flat_casesDoc (d + 1) cs]
  simp only [braces, Doc.append_def, Doc.flat, String.append_assoc]
  rfl

/-- An array literal's document laid flat is the house's array over the items' flat prints. -/
theorem flat_arr (items : List (Nat → Doc)) (d : Nat) :
    (docAlg.expr_arr items d).flat (2 * d) = renderAlg.expr_arr (items.map flatE) d := by
  cases items with
  | nil => rfl
  | cons x xs =>
    have hr : ((x :: xs).map flatE).map (· (d + 1)) ≠ [] := by
      simp only [List.map_cons]; exact List.cons_ne_nil _ _
    have hne : ((x :: xs).map flatE).isEmpty = false := by simp only [List.map_cons, List.isEmpty_cons]
    simp only [docAlg, renderAlg, List.isEmpty_cons, hne, Bool.false_eq_true, ↓reduceIte]
    by_cases hn : ((((x :: xs).map flatE).map (· (d + 1))).all fun item => !hasNewline item) = true
    · simp only [hn, ↓reduceIte]
      rw [flat_delimited_any, List.map_map]
      exact congrArg (fun t => "[" ++ String.intercalate ", " t ++ "]") (List.map_id'' (fun _ => rfl) _)
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
      rw [flat_multiline d "[" "]" (x :: xs) (fun item => item (d + 1) ++ .text ",") (fun item => flatE item (d + 1))
        (fun q => Render.indentOf house (d + 1) ++ q ++ ",") (List.cons_ne_nil x xs)
        (fun a => by simp only [Doc.append_def, Doc.flat, flatE, String.append_assoc]; rfl),
        nl_split "[\n" "["]
      simp only [String.append_assoc, List.map_map]
      rfl

/-- An object literal of entries laid flat is the house's over the entries' flat prints. -/
theorem flat_objectWith (keys : KeyForm) (entries : List (KeyForm → Nat → String × Doc)) (d : Nat) :
    (docAlg.expr_objectWith keys entries d).flat (2 * d) = renderAlg.expr_objectWith keys (entries.map flatO) d := by
  cases entries with
  | nil => rfl
  | cons x xs =>
    have hr : ((x :: xs).map flatO).map (· keys (d + 1)) ≠ [] := by
      simp only [List.map_cons]; exact List.cons_ne_nil _ _
    have hne : ((x :: xs).map flatO).isEmpty = false := by simp only [List.map_cons, List.isEmpty_cons]
    simp only [docAlg, renderAlg, List.isEmpty_cons, hne, Bool.false_eq_true, ↓reduceIte]
    by_cases hn : ((((x :: xs).map flatO).map (· keys (d + 1))).all fun entry => !hasNewline entry.2) = true
    · simp only [hn, ↓reduceIte]
      rw [flat_inline _ _ _ _ _ _ hr]
      simp only [String.append_assoc]
      rfl
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
      rw [flat_multiline d "{" "}" (x :: xs) (fun e => .text (e keys (d + 1)).1 ++ (e keys (d + 1)).2 ++ .text ",")
        (fun e => flatO e keys (d + 1)) (fun q => Render.indentOf house (d + 1) ++ q.1 ++ q.2 ++ ",")
        (List.cons_ne_nil x xs) (fun a => by simp only [Doc.append_def, Doc.flat, flatO, String.append_assoc]; rfl),
        nl_split "{\n" "{"]
      simp only [String.append_assoc, List.map_map]
      rfl

/-! ### One square for each constructor that holds a list or a block

Each states: lay the layout's node flat, or write the house's node over its children laid flat,
and the text is the same. The other constructors' squares hold by unfolding alone. -/

theorem sq_object (fields : List (String × (Nat → Doc))) :
    flatE (docAlg.expr_object fields) = renderAlg.expr_object (fields.map (prodMapSnd flatE)) :=
  by
    funext d
    simp only [flatE, docAlg, renderAlg]
    exact flat_objectDoc _ fields d

theorem sq_objectML (fields : List (String × (Nat → Doc))) :
    flatE (docAlg.expr_objectML fields) = renderAlg.expr_objectML (fields.map (prodMapSnd flatE)) :=
  by
    funext d
    simp only [flatE, docAlg, renderAlg]
    exact flat_objectMLDoc _ fields d

theorem sq_objectQuoted (fields : List (String × (Nat → Doc))) :
    flatE (docAlg.expr_objectQuoted fields) = renderAlg.expr_objectQuoted (fields.map (prodMapSnd flatE)) :=
  by
    funext d
    simp only [flatE, docAlg, renderAlg]
    exact flat_objectDoc _ fields d

theorem sq_objectQuotedML (fields : List (String × (Nat → Doc))) :
    flatE (docAlg.expr_objectQuotedML fields) = renderAlg.expr_objectQuotedML (fields.map (prodMapSnd flatE)) :=
  by
    funext d
    simp only [flatE, docAlg, renderAlg]
    exact flat_objectMLDoc _ fields d

theorem sq_objectFromEntries (fields : List (String × (Nat → Doc))) :
    flatE (docAlg.expr_objectFromEntries fields) = renderAlg.expr_objectFromEntries (fields.map (prodMapSnd flatE)) := by
  funext d
  simp only [flatE, docAlg, renderAlg, Doc.append_def, Doc.flat, flat_delimited_any, List.map_map, at_]
  rw [show ("Object.fromEntries([" : String) = "Object.fromEntries(" ++ "[" from rfl,
    show ("])" : String) = "]" ++ ")" from rfl]
  simp only [String.append_assoc, Function.comp_def, Doc.flat, prodMapSnd, flatE]

theorem sq_arr (items : List (Nat → Doc)) : flatE (docAlg.expr_arr items) = renderAlg.expr_arr (items.map flatE) :=
  funext (flat_arr items)

theorem sq_objectWith (keys : KeyForm) (entries : List (KeyForm → Nat → String × Doc)) :
    flatE (docAlg.expr_objectWith keys entries) = renderAlg.expr_objectWith keys (entries.map flatO) :=
  funext (flat_objectWith keys entries)

theorem sq_generator (body : List (Nat → Doc)) :
    flatE (docAlg.expr_generator body) = renderAlg.expr_generator (body.map flatS) := by
  funext d
  have h := flat_block "function* () {" body d ""
  simp only [String.append_empty] at h
  refine h.trans ?_
  simp only [renderAlg]
  rw [nl_split "function* () {\n" "function* () {"]
  simp only [String.append_assoc]

theorem sq_arrowBlock (params : List Parameter) (body : List (Nat → Doc)) (returnType : Option TypeRef) :
    flatE (docAlg.expr_arrowBlock params body returnType) =
      renderAlg.expr_arrowBlock params (body.map flatS) returnType := by
  funext d
  have h := flat_block ("(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
    Render.annotation house returnType ++ " => {") body d ""
  simp only [String.append_empty] at h
  refine h.trans ?_
  simp only [renderAlg]
  rw [nl_split " => {\n" " => {"]
  simp only [String.append_assoc]

theorem sq_whileTrue (label : Option String) (body : List (Nat → Doc)) :
    flatS (docAlg.stmt_whileTrue label body) = renderAlg.stmt_whileTrue label (body.map flatS) := by
  funext d
  have h := flat_block (labelText label ++ "while (true) {") body d ""
  simp only [String.append_empty] at h
  simp only [flatS, docAlg]
  rw [h]
  simp only [renderAlg]
  rw [nl_split "while (true) {\n" "while (true) {"]
  simp only [String.append_assoc]
  cases label <;> rfl

theorem sq_labelled (label : String) (body : List (Nat → Doc)) :
    flatS (docAlg.stmt_labelled label body) = renderAlg.stmt_labelled label (body.map flatS) := by
  funext d
  have h := flat_block (label ++ ": {") body d ""
  simp only [String.append_empty] at h
  simp only [flatS, docAlg]
  rw [h]
  simp only [renderAlg]
  rw [nl_split ": {\n" ": {"]
  simp only [String.append_assoc]

theorem sq_switch (scrutinee : Nat → Doc) (cases : List (Nat × List (Nat → Doc))) :
    flatS (docAlg.stmt_switch scrutinee cases) =
      renderAlg.stmt_switch (flatE scrutinee) (cases.map (prodMapSnd (List.map flatS))) := by
  funext d
  have h := flat_blockCases ") {" cases d ""
  simp only [String.append_empty] at h
  simp only [flatS, docAlg, Doc.append_def, Doc.flat]
  rw [h]
  simp only [renderAlg, flatE]
  rw [nl_split ") {\n" ") {"]
  simp only [String.append_assoc]

theorem sq_ifElse (condition : Nat → Doc) (thenBranch elseBranch : List (Nat → Doc)) :
    flatS (docAlg.stmt_ifElse condition thenBranch elseBranch) =
      renderAlg.stmt_ifElse (flatE condition) (thenBranch.map flatS) (elseBranch.map flatS) := by
  funext d
  cases elseBranch with
  | nil =>
    have h := flat_block ") {" thenBranch d ""
    simp only [String.append_empty] at h
    simp only [flatS, flatE, docAlg, renderAlg, Doc.append_def, Doc.flat, List.isEmpty_nil, ↓reduceIte,
      List.map_nil, String.append_empty]
    rw [h, nl_split ") {\n" ") {"]
    simp only [String.append_assoc]
  | cons x xs =>
    have he := flat_block " else {" (x :: xs) d ""
    have ht := flat_block ") {" thenBranch d ((braces " else {" (stmtsDoc (x :: xs) (d + 1))).flat (2 * d))
    simp only [String.append_empty] at he
    simp only [flatS, flatE, docAlg, renderAlg, Doc.append_def, Doc.flat, List.isEmpty_cons, List.map_cons,
      Bool.false_eq_true, ↓reduceIte, String.append_assoc]
    rw [ht, he, nl_split ") {\n" ") {", nl_split " else {\n" " else {"]
    simp only [String.append_assoc, List.map_cons]

theorem sq_scopedGen (name : String) (body : List (Nat → Doc)) (onExit : Nat → Doc) :
    flatS (docAlg.stmt_scopedGen name body onExit) = renderAlg.stmt_scopedGen name (body.map flatS) (flatE onExit) := by
  funext d
  have h := flat_block ("const " ++ name ++ " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {")
    body d ("), " ++ ((onExit d).flat (2 * d) ++ "))"))
  simp only [flatS, docAlg, Doc.append_def, Doc.flat, String.append_assoc]
  simp only [String.append_assoc] at h
  rw [h]
  simp only [renderAlg, flatE]
  rw [nl_split " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {\n"
    " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {", show ("}), " : String) = "}" ++ "), " from rfl]
  simp only [String.append_assoc]

theorem sq_scopedGenMasked (name : String) (body : List (Nat → Doc)) (onExit : Nat → Doc) :
    flatS (docAlg.stmt_scopedGenMasked name body onExit) =
      renderAlg.stmt_scopedGenMasked name (body.map flatS) (flatE onExit) := by
  funext d
  have h := flat_block ("const " ++ name ++
    " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {")
    body d ("), " ++ ((onExit d).flat (2 * d) ++ ")))"))
  simp only [flatS, docAlg, Doc.append_def, Doc.flat, String.append_assoc]
  simp only [String.append_assoc] at h
  rw [h]
  simp only [renderAlg, flatE]
  rw [nl_split " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {\n"
    " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {",
    show ("}), " : String) = "}" ++ "), " from rfl]
  simp only [String.append_assoc]

/-- A switch's cases with their statements mapped twice are mapped once by the composite. -/
theorem cases_map {α β γ : Type} (cs : List (Nat × List α)) (f : α → β) (g : β → γ) :
    (cs.map (prodMapSnd (List.map f))).map (prodMapSnd (List.map g)) =
      cs.map (prodMapSnd (List.map fun x => g (f x))) := by
  simp only [List.map_map]
  congr 1
  funext c
  simp only [Function.comp, prodMapSnd, List.map_map]
  rfl

/-- **The flat print, as a homomorphism of the house's algebra**: the layout's fold, laid flat. Each
equation is one constructor's square. -/
def flatHom : ExprHom renderAlg := by
  apply ExprHom.mk (f_expr := fun e => flatE (cata_expr docAlg e)) (f_stmt := fun s => flatS (cata_stmt docAlg s))
    (f_objectentry := fun o => flatO (cata_objectentry docAlg o))
  all_goals intros
  all_goals simp only [cata_expr, cata_stmt, cata_objectentry, cata_pos_list_expr_eq,
    cata_pos_list_prod_string_expr_eq, cata_pos_list_stmt_eq, cata_pos_list_objectentry_eq,
    cata_pos_list_prod_nat_list_stmt_eq]
  case h_expr_object => rw [sq_object, List.map_map]; rfl
  case h_expr_objectML => rw [sq_objectML, List.map_map]; rfl
  case h_expr_objectQuoted => rw [sq_objectQuoted, List.map_map]; rfl
  case h_expr_objectQuotedML => rw [sq_objectQuotedML, List.map_map]; rfl
  case h_expr_objectFromEntries => rw [sq_objectFromEntries, List.map_map]; rfl
  case h_expr_arr => rw [sq_arr, List.map_map]; rfl
  case h_expr_generator => rw [sq_generator, List.map_map]; rfl
  case h_expr_arrowBlock => rw [sq_arrowBlock, List.map_map]; rfl
  case h_expr_objectWith => rw [sq_objectWith, List.map_map]; rfl
  case h_stmt_whileTrue => rw [sq_whileTrue, List.map_map]; rfl
  case h_stmt_switch => rw [sq_switch, cases_map]
  case h_stmt_ifElse => rw [sq_ifElse, List.map_map, List.map_map]; rfl
  case h_stmt_labelled => rw [sq_labelled, List.map_map]; rfl
  case h_stmt_scopedGen => rw [sq_scopedGen, List.map_map]; rfl
  case h_stmt_scopedGenMasked => rw [sq_scopedGenMasked, List.map_map]; rfl
  case h_objectentry_property => rfl
  case h_objectentry_spread => rfl
  all_goals funext d
  all_goals simp only [flatE, flatS, flatO, docAlg, renderAlg, Doc.append_def, Doc.flat, flat_delimited_any,
    List.map_map, Function.comp_def, String.append_assoc]

/-- **The flat print of the layout is the house print**, for an expression at every depth: the
two folds agree because their algebras do (`flatHom`, `hom_eq_cata_expr`), and the house's fold is
the pinned renderer (`render_eq_expr`). So a laid-out file differs from the checked bytes only in
whitespace at breaks (`undo_layout`). -/
theorem flat_fold_expr (e : Expr) (d : Nat) : (cata_expr docAlg e d).flat (2 * d) = Render.expr house d e :=
  (congrFun (hom_eq_cata_expr flatHom e) d).trans (render_eq_expr e d)

/-- The flat print of the layout is the house print, for a statement after its indent. -/
theorem flat_fold_stmt (s : Stmt) (d : Nat) :
    Render.indentOf house d ++ (cata_stmt docAlg s d).flat (2 * d) = Render.stmt house d s :=
  (congrFun (hom_eq_cata_stmt flatHom s) d).trans (render_eq_stmt s d)

/-! ## Declarations -/

/-- An exported constant: the house's doc block, then the declaration as a document. -/
def constDecl (declaration : ConstDecl) : String × Doc :=
  (Render.docBlock declaration.doc,
    .text ((if declaration.exported then "export " else "") ++ "const " ++ declaration.name ++
      Render.annotation house declaration.type ++ " = ") ++ cata_expr docAlg declaration.value 0)

/-- A declaration laid out at the width `w`. A constant is a document; the house writes the
others, which hold no program. -/
def decl (w : Nat) : Decl → String
  | .const declaration =>
    let (docs, body) := constDecl declaration
    docs ++ body.layout w ++ "\n"
  | other => Render.decl house other

end Tools.Code.Ts
