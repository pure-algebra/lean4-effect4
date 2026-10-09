import Tools.Code.Doc
import TypeScript.Render

/-!
# Printed TypeScript as a document

The readable form of the printer's TypeScript (`Effect4.Codegen`, the pinned `TypeScript.Syntax`).
Each function here follows its namesake in `TypeScript.Render` case by case, so the flat print of
a document is the house print (`flat_expr`), and a layout only breaks lines. A call's arguments,
an inline object's fields and an inline array's items form a group: flat as the house writes it,
or one item a line. A block (a generator's body, a loop's, a branch's) is the house's block. A
member the house writes inline stays one text: what the house decides is never undone.

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

mutual

/-- An expression at the house's depth `d`. -/
def expr (d : Nat) : Expr → Doc
  | .ident name => .text name
  | .str value => .text (Render.quoted house value)
  | .int value => .text (toString value)
  | .float64Bits bits => .text (Render.float64Bits bits)
  | .bool value => .text (if value then "true" else "false")
  | .jsNull => .text "null"
  | .call fn args => expr d fn ++ delimited "(" ")" "" (exprs d args)
  | .object fields =>
    if fields.isEmpty then .text "{}"
    else
      let rendered := Render.objectFields house (d + 1) fields
      if rendered.all (fun field => !hasNewline field.2) then
        delimited "{" "}" " " (rendered.map fun p => .text (p.1 ++ ": " ++ p.2))
      else
        multiline "{" "}" ((objectFields (d + 1) fields).map fun p => .text (p.1 ++ ": ") ++ p.2 ++ .text ",")
  | .objectML fields =>
    if fields.isEmpty then .text "{}"
    else
      multiline "{" "}" ((objectFields (d + 1) fields).map fun p => .text (p.1 ++ ": ") ++ p.2 ++ .text ",")
  | .objectQuoted fields =>
    if fields.isEmpty then .text "{}"
    else
      let rendered := Render.objectFields house (d + 1) fields
      if rendered.all (fun field => !hasNewline field.2) then
        delimited "{" "}" " " (rendered.map fun p => .text (Render.quoted house p.1 ++ ": " ++ p.2))
      else
        multiline "{" "}" ((objectFields (d + 1) fields).map fun p =>
          .text (Render.quoted house p.1 ++ ": ") ++ p.2 ++ .text ",")
  | .objectQuotedML fields =>
    if fields.isEmpty then .text "{}"
    else
      multiline "{" "}" ((objectFields (d + 1) fields).map fun p =>
        .text (Render.quoted house p.1 ++ ": ") ++ p.2 ++ .text ",")
  | .objectFromEntries fields =>
    .text "Object.fromEntries(" ++
      delimited "[" "]" "" ((objectFields d fields).map fun p =>
        .text ("[" ++ Render.quoted house p.1 ++ ", ") ++ p.2 ++ .text "]") ++
      .text ")"
  | .arr items =>
    if items.isEmpty then .text "[]"
    else
      let rendered := Render.exprs house (d + 1) items
      if rendered.all (fun item => !hasNewline item) then
        delimited "[" "]" "" (rendered.map .text)
      else
        multiline "[" "]" ((exprs (d + 1) items).map fun item => item ++ .text ",")
  | .arrow returnType body =>
    .text ("()" ++ Render.annotation house returnType ++ " => ") ++ expr d body
  | .generic fn typeArgs =>
    expr d fn ++ .text ("<" ++ String.intercalate ", " (Render.types house typeArgs) ++ ">")
  | .lambda params body returnType =>
    .text ("(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
      Render.annotation house returnType ++ " => ") ++ expr d body
  | .method target name args =>
    expr d target ++ .text ("." ++ name) ++ delimited "(" ")" "" (exprs d args)
  | .member target name => expr d target ++ .text ("." ++ name)
  | .generator body => braces "function* () {" (stmts (d + 1) body)
  | .cond test thenBranch elseBranch =>
    expr d test ++ .text " ? " ++ expr d thenBranch ++ .text " : " ++ expr d elseBranch
  | .arrowBlock params body returnType =>
    braces ("(" ++ String.intercalate ", " (params.map (Render.parameter house)) ++ ")" ++
      Render.annotation house returnType ++ " => {") (stmts (d + 1) body)
  | .index target key => expr d target ++ .text "[" ++ expr d key ++ .text "]"
  | .new callee args => .text "new " ++ expr d callee ++ delimited "(" ")" "" (exprs d args)
  | .objectWith keys entries =>
    if entries.isEmpty then .text "{}"
    else
      let rendered := Render.objectEntries house keys (d + 1) entries
      if rendered.all (fun entry => !hasNewline entry.2) then
        delimited "{" "}" " " (rendered.map fun p => .text (p.1 ++ p.2))
      else
        multiline "{" "}" ((objectEntries keys (d + 1) entries).map fun p => .text p.1 ++ p.2 ++ .text ",")

/-- Expressions, each at the depth `d`. -/
def exprs (d : Nat) : List Expr → List Doc
  | [] => []
  | item :: rest => expr d item :: exprs d rest

/-- An object's fields, each value at the depth `d`. -/
def objectFields (d : Nat) : List (String × Expr) → List (String × Doc)
  | [] => []
  | (name, value) :: rest => (name, expr d value) :: objectFields d rest

/-- An `objectWith` literal's entries: each head as the house spells it, and its value. -/
def objectEntries (keys : KeyForm) (d : Nat) : List ObjectEntry → List (String × Doc)
  | [] => []
  | .property name value :: rest =>
    (Render.propertyName house keys name ++ ": ", expr d value) :: objectEntries keys d rest
  | .spread value :: rest => ("...", expr d value) :: objectEntries keys d rest

/-- A statement, without the indent the house writes before it. -/
def stmt (d : Nat) : Stmt → Doc
  | .constYield name value declaredType =>
    .text ("const " ++ name ++ Render.annotation house declaredType ++ " = yield* ") ++ expr d value
  | .ret value => .text "return " ++ expr d value
  | .yieldDiscard value => .text "yield* " ++ expr d value
  | .letDefinite name declaredType => .text ("let " ++ name ++ "!: " ++ Render.type house declaredType)
  | .letInit name value declaredType =>
    .text ("let " ++ name ++ Render.annotation house declaredType ++ " = ") ++ expr d value
  | .assign name value => .text (name ++ " = ") ++ expr d value
  | .whileTrue label body => braces (labelText label ++ "while (true) {") (stmts (d + 1) body)
  | .switch scrutinee cases =>
    .text "switch (" ++ expr d scrutinee ++ braces ") {" (switchCases (d + 1) cases)
  | .ifElse condition thenBranch elseBranch =>
    .text "if (" ++ expr d condition ++ braces ") {" (stmts (d + 1) thenBranch) ++
      (if elseBranch.isEmpty then .nil else braces " else {" (stmts (d + 1) elseBranch))
  | .labelled label body => braces (label ++ ": {") (stmts (d + 1) body)
  | .scopedGen name body onExit =>
    braces ("const " ++ name ++ " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {")
      (stmts (d + 1) body) ++ .text "), " ++ expr d onExit ++ .text "))"
  | .scopedGenMasked name body onExit =>
    braces ("const " ++ name ++
      " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {")
      (stmts (d + 1) body) ++ .text "), " ++ expr d onExit ++ .text ")))"
  | .breakTo label => .text ("break" ++ (match label with | some l => " " ++ l | none => ""))
  | .continueTo label => .text ("continue" ++ (match label with | some l => " " ++ l | none => ""))
  | .exprStmt value => expr d value

/-- Statements, each on its own line. -/
def stmts (d : Nat) : List Stmt → Doc
  | [] => .nil
  | first :: rest => .hard ++ stmt d first ++ stmts d rest

/-- A switch's cases, each on its own line with its block. -/
def switchCases (d : Nat) : List (Nat × List Stmt) → Doc
  | [] => .nil
  | (index, body) :: rest =>
    .hard ++ braces ("case " ++ toString index ++ ": {") (stmts (d + 1) body) ++ switchCases d rest

end

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

/-! ## The flat print is the house print -/

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

mutual

/-- **The flat print of an expression is the house print**, at every depth. -/
theorem flat_expr (d : Nat) : ∀ e : Expr, (expr d e).flat (2 * d) = Render.expr house d e
  | .ident _ => rfl
  | .str _ => rfl
  | .int _ => rfl
  | .float64Bits _ => rfl
  | .bool _ => rfl
  | .jsNull => rfl
  | .call fn args => by
    have ih := flat_exprs d args
    simp only [expr, house_call, Doc.append_def, Doc.flat, flat_expr d fn, String.append_assoc]
    rw [← ih]
    generalize exprs d args = xs
    cases xs with
    | nil => simp only [flat_delimited_nil, List.map_nil, String.intercalate_nil, String.empty_append]
    | cons x xs =>
      rw [flat_delimited _ _ _ _ _ (List.cons_ne_nil x xs)]
      simp only [String.append_empty, String.append_assoc]
  | .object fields => by
    have ihf := flat_objectFields (d + 1) fields
    simp only [expr, house_object, houseObject]
    cases fields with
    | nil => rfl
    | cons f fs =>
      have hx : objectFields (d + 1) (f :: fs) ≠ [] := by
        obtain ⟨n, v⟩ := f
        exact List.cons_ne_nil _ _
      have hr : Render.objectFields house (d + 1) (f :: fs) ≠ [] := by
        rw [← ihf]; simpa only [ne_eq, List.map_eq_nil_iff] using hx
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      by_cases hn : ((Render.objectFields house (d + 1) (f :: fs)).all fun field => !hasNewline field.2) = true
      · simp only [hn, ↓reduceIte]
        rw [flat_inline _ _ _ _ _ _ hr]
        simp only [String.append_assoc]
        rfl
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        rw [← ihf, flat_multiline d "{" "}" _ _ (fun p => (p.1, p.2.flat (2 * (d + 1))))
          (fun q => Render.indentOf house (d + 1) ++ q.1 ++ ": " ++ q.2 ++ ",") hx
          (fun a => by simp only [Doc.append_def, Doc.flat, String.append_assoc]; rfl),
          nl_split "{\n" "{"]
        simp only [String.append_assoc]
  | .objectML fields => by
    have ihf := flat_objectFields (d + 1) fields
    simp only [expr, house_objectML, houseObjectML]
    cases fields with
    | nil => rfl
    | cons f fs =>
      have hx : objectFields (d + 1) (f :: fs) ≠ [] := by
        obtain ⟨n, v⟩ := f
        exact List.cons_ne_nil _ _
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [← ihf, flat_multiline d "{" "}" _ _ (fun p => (p.1, p.2.flat (2 * (d + 1))))
        (fun q => Render.indentOf house (d + 1) ++ q.1 ++ ": " ++ q.2 ++ ",") hx
        (fun a => by simp only [Doc.append_def, Doc.flat, String.append_assoc]; rfl),
        nl_split "{\n" "{"]
      simp only [String.append_assoc]
  | .objectQuoted fields => by
    have ihf := flat_objectFields (d + 1) fields
    simp only [expr, house_objectQuoted, houseObject]
    cases fields with
    | nil => rfl
    | cons f fs =>
      have hx : objectFields (d + 1) (f :: fs) ≠ [] := by
        obtain ⟨n, v⟩ := f
        exact List.cons_ne_nil _ _
      have hr : Render.objectFields house (d + 1) (f :: fs) ≠ [] := by
        rw [← ihf]; simpa only [ne_eq, List.map_eq_nil_iff] using hx
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      by_cases hn : ((Render.objectFields house (d + 1) (f :: fs)).all fun field => !hasNewline field.2) = true
      · simp only [hn, ↓reduceIte]
        rw [flat_inline _ _ _ _ _ _ hr]
        simp only [String.append_assoc]
        rfl
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        rw [← ihf, flat_multiline d "{" "}" _ _ (fun p => (p.1, p.2.flat (2 * (d + 1))))
          (fun q => Render.indentOf house (d + 1) ++ Render.quoted house q.1 ++ ": " ++ q.2 ++ ",") hx
          (fun a => by simp only [Doc.append_def, Doc.flat, String.append_assoc]; rfl),
          nl_split "{\n" "{"]
        simp only [String.append_assoc]
  | .objectQuotedML fields => by
    have ihf := flat_objectFields (d + 1) fields
    simp only [expr, house_objectQuotedML, houseObjectML]
    cases fields with
    | nil => rfl
    | cons f fs =>
      have hx : objectFields (d + 1) (f :: fs) ≠ [] := by
        obtain ⟨n, v⟩ := f
        exact List.cons_ne_nil _ _
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [← ihf, flat_multiline d "{" "}" _ _ (fun p => (p.1, p.2.flat (2 * (d + 1))))
        (fun q => Render.indentOf house (d + 1) ++ Render.quoted house q.1 ++ ": " ++ q.2 ++ ",") hx
        (fun a => by simp only [Doc.append_def, Doc.flat, String.append_assoc]; rfl),
        nl_split "{\n" "{"]
      simp only [String.append_assoc]
  | .objectFromEntries fields => by
    have ihf := flat_objectFields d fields
    simp only [expr, house_objectFromEntries, Doc.append_def, Doc.flat]
    rw [← ihf]
    generalize objectFields d fields = xs
    cases xs with
    | nil => rfl
    | cons x xs =>
      rw [flat_delimited _ _ _ _ _ (mt List.map_eq_nil_iff.mp (List.cons_ne_nil x xs)), List.map_map,
        List.map_map, show ("Object.fromEntries([" : String) = "Object.fromEntries(" ++ "[" from rfl,
        show ("])" : String) = "]" ++ ")" from rfl]
      simp only [Function.comp_def, Doc.flat, String.append_assoc, String.empty_append]
  | .arr items => by
    have ihx := flat_exprs (d + 1) items
    simp only [expr, house_arr]
    cases items with
    | nil => rfl
    | cons i is =>
      have hx : exprs (d + 1) (i :: is) ≠ [] := List.cons_ne_nil _ _
      have hr : Render.exprs house (d + 1) (i :: is) ≠ [] := List.cons_ne_nil _ _
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      by_cases hn : ((Render.exprs house (d + 1) (i :: is)).all fun item => !hasNewline item) = true
      · simp only [hn, ↓reduceIte]
        rw [flat_inline _ _ _ _ _ _ hr]
        simp only [List.map_id', String.append_empty, String.append_assoc]
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        rw [← ihx, flat_multiline d "[" "]" _ _ (·.flat (2 * (d + 1)))
          (fun item => Render.indentOf house (d + 1) ++ item ++ ",") hx
          (fun a => by simp only [Doc.append_def, Doc.flat, String.append_assoc]; rfl),
          nl_split "[\n" "["]
        simp only [String.append_assoc]
  | .arrow returnType body => by
    simp only [expr, house_arrow, Doc.append_def, Doc.flat, flat_expr d body, String.append_assoc]
  | .generic fn typeArgs => by
    simp only [expr, house_generic, Doc.append_def, Doc.flat, flat_expr d fn, String.append_assoc]
  | .lambda params body returnType => by
    simp only [expr, house_lambda, Doc.append_def, Doc.flat, flat_expr d body, String.append_assoc]
  | .method target name args => by
    have ih := flat_exprs d args
    simp only [expr, house_method, Doc.append_def, Doc.flat, flat_expr d target, String.append_assoc]
    rw [← ih]
    generalize exprs d args = xs
    cases xs with
    | nil => simp only [flat_delimited_nil, List.map_nil, String.intercalate_nil, String.empty_append]
    | cons x xs =>
      rw [flat_delimited _ _ _ _ _ (List.cons_ne_nil x xs)]
      simp only [String.append_empty, String.append_assoc]
  | .member target name => by
    simp only [expr, house_member, Doc.append_def, Doc.flat, flat_expr d target, String.append_assoc]
  | .generator body => by
    have ih := flat_stmts (d + 1) body (Render.indentOf house d ++ "}")
    simp only [expr, house_generator, braces, Doc.append_def, Doc.flat]
    rw [nl_split "function* () {\n" "function* () {"]
    simp only [String.append_assoc]
    rw [ih]
    rfl
  | .cond test thenBranch elseBranch => by
    simp only [expr, house_cond, Doc.append_def, Doc.flat, flat_expr d test, flat_expr d thenBranch,
      flat_expr d elseBranch, String.append_assoc]
  | .arrowBlock params body returnType => by
    have ih := flat_stmts (d + 1) body (Render.indentOf house d ++ "}")
    simp only [expr, house_arrowBlock, braces, Doc.append_def, Doc.flat]
    rw [nl_split " => {\n" " => {"]
    simp only [String.append_assoc]
    rw [ih]
    rfl
  | .index target key => by
    simp only [expr, house_index, Doc.append_def, Doc.flat, flat_expr d target, flat_expr d key,
      String.append_assoc]
  | .new callee args => by
    have ih := flat_exprs d args
    simp only [expr, house_new, Doc.append_def, Doc.flat, flat_expr d callee, String.append_assoc]
    rw [← ih]
    generalize exprs d args = xs
    cases xs with
    | nil => simp only [flat_delimited_nil, List.map_nil, String.intercalate_nil, String.empty_append]
    | cons x xs =>
      rw [flat_delimited _ _ _ _ _ (List.cons_ne_nil x xs)]
      simp only [String.append_empty, String.append_assoc]
  | .objectWith keys entries => by
    have ihe := flat_objectEntries keys (d + 1) entries
    simp only [expr, house_objectWith]
    cases entries with
    | nil => rfl
    | cons e es =>
      have hx : objectEntries keys (d + 1) (e :: es) ≠ [] := by
        cases e <;> exact List.cons_ne_nil _ _
      have hr : Render.objectEntries house keys (d + 1) (e :: es) ≠ [] := by
        rw [← ihe]; simpa only [ne_eq, List.map_eq_nil_iff] using hx
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      by_cases hn : ((Render.objectEntries house keys (d + 1) (e :: es)).all fun entry => !hasNewline entry.2) = true
      · simp only [hn, ↓reduceIte]
        rw [flat_inline _ _ _ _ _ _ hr]
        simp only [String.append_assoc]
        rfl
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        rw [← ihe, flat_multiline d "{" "}" _ _ (fun p => (p.1, p.2.flat (2 * (d + 1))))
          (fun q => Render.indentOf house (d + 1) ++ q.1 ++ q.2 ++ ",") hx
          (fun a => by simp only [Doc.append_def, Doc.flat, String.append_assoc]; rfl),
          nl_split "{\n" "{"]
        simp only [String.append_assoc]

/-- Expressions laid flat are the house's. -/
theorem flat_exprs (d : Nat) : ∀ es : List Expr,
    (exprs d es).map (·.flat (2 * d)) = Render.exprs house d es
  | [] => rfl
  | e :: es => by
    simp only [exprs, Render.exprs, List.map_cons, flat_expr d e, flat_exprs d es]

/-- An object's fields laid flat are the house's. -/
theorem flat_objectFields (d : Nat) : ∀ fs : List (String × Expr),
    (objectFields d fs).map (fun p => (p.1, p.2.flat (2 * d))) = Render.objectFields house d fs
  | [] => rfl
  | (name, value) :: rest => by
    simp only [objectFields, Render.objectFields, List.map_cons, flat_expr d value,
      flat_objectFields d rest]

/-- An `objectWith` literal's entries laid flat are the house's. -/
theorem flat_objectEntries (keys : KeyForm) (d : Nat) : ∀ es : List ObjectEntry,
    (objectEntries keys d es).map (fun p => (p.1, p.2.flat (2 * d))) = Render.objectEntries house keys d es
  | [] => rfl
  | .property name value :: rest => by
    simp only [objectEntries, Render.objectEntries, List.map_cons, flat_expr d value,
      flat_objectEntries keys d rest]
  | .spread value :: rest => by
    simp only [objectEntries, Render.objectEntries, List.map_cons, flat_expr d value,
      flat_objectEntries keys d rest]

/-- A statement as the house writes it: its indent, then its flat print. -/
theorem flat_stmt (d : Nat) : ∀ s : Stmt,
    Render.stmt house d s = Render.indentOf house d ++ (stmt d s).flat (2 * d)
  | .constYield name value declaredType => by
    simp only [stmt, Render.stmt, Doc.append_def, Doc.flat, flat_expr d value, String.append_assoc]
  | .ret value => by
    simp only [stmt, Render.stmt, Doc.append_def, Doc.flat, flat_expr d value, String.append_assoc]
  | .yieldDiscard value => by
    simp only [stmt, Render.stmt, Doc.append_def, Doc.flat, flat_expr d value, String.append_assoc]
  | .letDefinite name declaredType => by
    simp only [stmt, Render.stmt, Doc.flat, String.append_assoc]
  | .letInit name value declaredType => by
    simp only [stmt, Render.stmt, Doc.append_def, Doc.flat, flat_expr d value, String.append_assoc]
  | .assign name value => by
    simp only [stmt, Render.stmt, Doc.append_def, Doc.flat, flat_expr d value, String.append_assoc]
  | .whileTrue label body => by
    have ih := flat_stmts (d + 1) body (Render.indentOf house d ++ "}")
    simp only [stmt, Render.stmt, braces, Doc.append_def, Doc.flat]
    rw [nl_split "while (true) {\n" "while (true) {"]
    simp only [String.append_assoc]
    rw [ih]
    cases label <;> rfl
  | .switch scrutinee cases => by
    have ih := flat_switchCases (d + 1) cases (Render.indentOf house d ++ "}")
    simp only [stmt, Render.stmt, braces, Doc.append_def, Doc.flat, flat_expr d scrutinee]
    rw [nl_split ") {\n" ") {"]
    simp only [String.append_assoc]
    rw [ih]
    rfl
  | .ifElse condition thenBranch elseBranch => by
    have iht := flat_stmts (d + 1) thenBranch
    have ihe := flat_stmts (d + 1) elseBranch (Render.indentOf house d ++ "}")
    simp only [stmt, Render.stmt, braces, Doc.append_def, Doc.flat, flat_expr d condition]
    rw [nl_split ") {\n" ") {"]
    cases elseBranch with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte, Doc.flat, String.append_empty, String.append_assoc]
      rw [iht]
      rfl
    | cons e es =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Doc.flat]
      rw [nl_split " else {\n" " else {"]
      simp only [String.append_assoc]
      rw [iht, ihe]
      rfl
  | .labelled label body => by
    have ih := flat_stmts (d + 1) body (Render.indentOf house d ++ "}")
    simp only [stmt, Render.stmt, braces, Doc.append_def, Doc.flat]
    rw [nl_split ": {\n" ": {"]
    simp only [String.append_assoc]
    rw [ih]
    rfl
  | .scopedGen name body onExit => by
    have ih := flat_stmts (d + 1) body (Render.indentOf house d ++ ("}), " ++ (Render.expr house d onExit ++ "))")))
    simp only [stmt, Render.stmt, braces, Doc.append_def, Doc.flat, flat_expr d onExit]
    rw [nl_split " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" " = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {"]
    simp only [String.append_assoc]
    rw [ih, show ("}), " : String) = "}" ++ "), " from rfl]
    simp only [String.append_assoc]
    rfl
  | .scopedGenMasked name body onExit => by
    have ih := flat_stmts (d + 1) body (Render.indentOf house d ++ ("}), " ++ (Render.expr house d onExit ++ ")))")))
    simp only [stmt, Render.stmt, braces, Doc.append_def, Doc.flat, flat_expr d onExit]
    rw [nl_split " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" " = yield* Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(function* () {"]
    simp only [String.append_assoc]
    rw [ih, show ("}), " : String) = "}" ++ "), " from rfl]
    simp only [String.append_assoc]
    rfl
  | .breakTo label => by
    cases label <;> simp only [stmt, Render.stmt, Doc.flat, String.append_assoc]
  | .continueTo label => by
    cases label <;> simp only [stmt, Render.stmt, Doc.flat, String.append_assoc]
  | .exprStmt value => by
    simp only [stmt, Render.stmt, flat_expr d value]

/-- Statements as the house writes them, one a line: after a newline, they are the flat print of
their document, and a newline. -/
theorem flat_stmts (d : Nat) : ∀ (ss : List Stmt) (rest : String),
    "\n" ++ (Render.stmts house d ss ++ rest) = (stmts d ss).flat (2 * d) ++ ("\n" ++ rest)
  | [], rest => by simp only [Render.stmts, stmts, Doc.flat, String.empty_append]
  | s :: ss, rest => by
    have ih := flat_stmts d ss rest
    simp only [Render.stmts, stmts, Doc.append_def, Doc.flat, flat_stmt d s, String.append_assoc]
    rw [ih]
    rfl

/-- A switch's cases as the house writes them, after a newline. -/
theorem flat_switchCases (d : Nat) : ∀ (cs : List (Nat × List Stmt)) (rest : String),
    "\n" ++ (Render.switchCases house d cs ++ rest) = (switchCases d cs).flat (2 * d) ++ ("\n" ++ rest)
  | [], rest => by simp only [Render.switchCases, switchCases, Doc.flat, String.empty_append]
  | (index, body) :: cs, rest => by
    have ihb := flat_stmts (d + 1) body (Render.indentOf house d ++ ("}" ++ ("\n" ++ (Render.switchCases house d cs ++ rest))))
    have ih := flat_switchCases d cs rest
    simp only [Render.switchCases, switchCases, braces, Doc.append_def, Doc.flat, String.append_assoc]
    rw [nl_split ": {\n" ": {", show ("}\n" : String) = "}" ++ "\n" from rfl]
    simp only [String.append_assoc]
    rw [ihb, ih]
    rfl

end

/-- An exported constant: the house's doc block, then the declaration as a document. -/
def constDecl (declaration : ConstDecl) : String × Doc :=
  (Render.docBlock declaration.doc,
    .text ((if declaration.exported then "export " else "") ++ "const " ++ declaration.name ++
      Render.annotation house declaration.type ++ " = ") ++ expr 0 declaration.value)

/-- A declaration laid out at the width `w`. A constant is a document; the house writes the
others, which hold no program. -/
def decl (w : Nat) : Decl → String
  | .const declaration =>
    let (docs, body) := constDecl declaration
    docs ++ body.layout w ++ "\n"
  | other => Render.decl house other

end Tools.Code.Ts
