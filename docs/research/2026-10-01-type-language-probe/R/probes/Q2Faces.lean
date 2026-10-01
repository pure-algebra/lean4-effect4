import Effect4.Codegen.Read
import Effect4.Codegen.SourceBindings
import Effect4.Program.Ty

/-!
# Seat R, question 2: name preservation on the faces (print and read of the record forms)

Type-language probe, 2026-10-01. A model, not the tree. The terms are `Q1Positional.lean`'s
(row 119's positional values, `field` with its checked position) with the typing rule for
`field` stated through `fieldPos` (the canonical position of the name; equal to `Q1`'s rule
when canonical names are distinct, which `canon` makes them). The printed syntax `PExpr` is the
fragment of the vendored `TypeScript.Expr` (`.lake/packages/typescript/TypeScript/Syntax.lean`)
the record forms need, objects as parallel key and value lists, plus the two forms the vendored
syntax lacks: `index` (`t["k"]`) and `objectComputed` (`{ ["k"]: v }`). `render` spells it as the
vendored renderer does (`#guard`s against `TypeScript.Render.expr`). Binder names and their
reading are the tree's own (`Var.name`, `Var.read`, `Var.read_name`, `Codegen/Read.lean:1096-1132`).

What it shows:
1. positional values carry no names, so printing a value is type-directed: one value prints as
   `{ body: "x" }` at one type and `{ name: "x" }` at another (`printVal_needs_type`);
2. the printed projection drops the position, so no reader that does not consult types can
   invert the printer on well-typed terms (`no_untyped_reader`);
3. a reader that resolves the position from the target's type inverts it: `read_print` on every
   well-typed term and `read_exact` on every accepted tree (`read_print`, `read_exact`);
4. with names carried in the value (`Q1Named.lean`'s clause) the untyped reader inverts it
   (`Named.read_print`, `Named.read_exact`);
5. the image per name class: identifiers unquoted with dot access; any other name quoted with
   bracket access; `__proto__` computed; the reader accepts exactly that image.
-/

set_option autoImplicit false

namespace SeatR.Faces

open Effect4.Machine
open Effect4.Program (Lit)

/-! ## 1. Names, their order, the canonical field list -/

/-- The UTF-8 byte order on names: the key order `Ty.key` uses for a `lit` (`Ty.lean:155-176`). -/
def nameLt (a b : String) : Bool :=
  Effect4.Program.Ty.ltKey (Effect4.Program.Ty.key (.lit a)) (Effect4.Program.Ty.key (.lit b))

/-- Insert by name; an equal name already present wins, so a left fold keeps the first. -/
def ins {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs => if nameLt p.1 q.1 then p :: q :: qs else if p.1 = q.1 then q :: qs else q :: ins p qs

/-- Canonical field order: ascending by name, the first of a repeated name kept. -/
def canon {α : Type} (xs : List (String × α)) : List (String × α) :=
  xs.foldl (fun acc p => ins p acc) []

theorem ins_map {α β : Type} (f : α → β) (p : String × α) (l : List (String × α)) :
    ins (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) = (ins p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [List.map_cons, ins, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp only [List.map_cons, ins, if_neg h1, if_pos h2]
      · simp only [List.map_cons, ins, if_neg h1, if_neg h2, ih]

theorem foldl_ins_map {α β : Type} (f : α → β) (xs acc : List (String × α)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => ins p a) (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => ins p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ins_map f x acc]
    exact ih (ins x acc)

/-- The canonicaliser is payload-polymorphic: it commutes with any map of the payloads. -/
theorem canon_map {α β : Type} (f : α → β) (xs : List (String × α)) :
    canon (xs.map (fun q => (q.1, f q.2))) = (canon xs).map (fun q => (q.1, f q.2)) :=
  foldl_ins_map f xs []

theorem mem_ins {α : Type} (p x : String × α) (l : List (String × α)) (h : x ∈ ins p l) :
    x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [ins, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [ins, if_pos h1, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2] at h
        exact Or.inr h
      · simp only [ins, if_neg h1, if_neg h2, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem mem_foldl_ins {α : Type} (x : String × α) (xs acc : List (String × α))
    (h : x ∈ xs.foldl (fun a p => ins p a) acc) : x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons y ys ih =>
    simp only [List.foldl_cons] at h
    rcases ih (ins y acc) h with h' | h'
    · rcases mem_ins y x acc h' with h'' | h''
      · exact Or.inr (List.mem_cons.mpr (Or.inl h''))
      · exact Or.inl h''
    · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- Every field of the canonical list is a field of the input. -/
theorem mem_canon {α : Type} (x : String × α) (xs : List (String × α)) (h : x ∈ canon xs) :
    x ∈ xs := by
  rcases mem_foldl_ins x xs [] h with h' | h'
  · cases h'
  · exact h'

/-- The value of a name in a field list, first match. -/
def lookupName {α : Type} (n : String) : List (String × α) → Option α
  | [] => none
  | (m, a) :: rest => if m = n then some a else lookupName n rest


/-- The canonical position of a name: the first field that carries it. -/
def fieldPos {α : Type} (n : String) : List (String × α) → Option (Nat × α)
  | [] => none
  | (m, a) :: rest => if m = n then some (0, a) else (fieldPos n rest).map (fun p => (p.1 + 1, p.2))

/-! ## 2. Types, terms and the typer (as `Q1Positional`, `field` through `fieldPos`) -/

inductive MTy where
  | unit
  | nat
  | string
  | bool
  | lit (s : String)
  | prod (a b : MTy)
  | union (a b : MTy)
  | record (fields : List (String × MTy))

mutual
  inductive Term
    | var (index : Nat)
    | lit (value : Lit)
    | app (atom : String) (args : Terms)
    | record (labels : List String) (args : Terms)
    | field (target : Term) (index : Nat) (name : String)
  inductive Terms
    | nil
    | cons (head : Term) (tail : Terms)
end

deriving instance DecidableEq for Term, Terms

structure Sig where
  atomOf : String → List MTy → Option MTy
  constAtom : String → Bool

def litArgTy (const : Bool) : Lit → MTy
  | .str s => if const then .lit s else .string
  | .unit => .unit
  | .nat _ => .nat
  | .bool _ => .bool

def distinct : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && distinct ns

def fieldTy : MTy → Nat → String → Option MTy
  | .record fs, i, n =>
    match fieldPos n (canon fs) with
    | some (j, τ) => if j = i then some τ else none
    | none => none
  | _, _, _ => none

mutual
  def argTy (sig : Sig) (env : List MTy) (const : Bool) : Term → Option MTy
    | .var index => env[index]?
    | .lit value => some (litArgTy const value)
    | .app atom args => do
      let tys ← argsTy sig env (sig.constAtom atom) args
      sig.atomOf atom tys
    | .record labels args => do
      let tys ← argsTy sig env false args
      if labels.length = tys.length ∧ distinct labels = true then
        some (.record (labels.zip tys))
      else none
    | .field target index name => do
      let r ← argTy sig env false target
      fieldTy r index name
  def argsTy (sig : Sig) (env : List MTy) (const : Bool) : Terms → Option (List MTy)
    | .nil => some []
    | .cons head tail => do
      let t ← argTy sig env const head
      let rest ← argsTy sig env const tail
      some (t :: rest)
end

/-! ## 3. The printed fragment, its name classes, and its spelling -/

inductive PExpr
  | ident (name : String)
  | int (value : Nat)
  | str (value : String)
  | bool (value : Bool)
  | call (fn : String) (args : List PExpr)
  /-- The vendored `object`: unquoted keys. -/
  | object (keys : List String) (values : List PExpr)
  /-- The vendored `objectQuoted`: every key quoted. -/
  | objectQuoted (keys : List String) (values : List PExpr)
  /-- Not in the vendored syntax: every key computed, `{ ["k"]: v }`. -/
  | objectComputed (keys : List String) (values : List PExpr)
  /-- The vendored `member`: `t.name`. -/
  | member (target : PExpr) (name : String)
  /-- Not in the vendored syntax: `t["key"]`. -/
  | index (target : PExpr) (key : String)

/-- A name that may be written bare: the binding check's identifier bytes (`SourceBindings.lean:
46-49`, keywords allowed as properties), and not `__proto__`, which a bare or quoted literal key
turns into a prototype assignment (`host/names/field-names.cjs`). -/
def identName (n : String) : Bool :=
  Effect4.Codegen.SourceBindings.identifierBytes n.toUTF8.data.toList && !(n == "__proto__")

inductive ObjForm
  | plain
  | quoted
  | computed
deriving DecidableEq

/-- The one object image of a key list. -/
def objForm (keys : List String) : ObjForm :=
  if keys.any (· == "__proto__") then .computed else if keys.all identName then .plain else .quoted

def mkObject (keys : List String) (values : List PExpr) : PExpr :=
  match objForm keys with
  | .plain => .object keys values
  | .quoted => .objectQuoted keys values
  | .computed => .objectComputed keys values

/-- The one access image of a name. -/
def mkAccess (t : PExpr) (n : String) : PExpr := if identName n then .member t n else .index t n

def quoted (s : String) : String := TypeScript.Render.quoted TypeScript.house0 s

def objText (key : String → String) (ks vs : List String) : String :=
  if ks.isEmpty then "{}"
  else "{ " ++ String.intercalate ", " ((ks.zip vs).map fun p => key p.1 ++ ": " ++ p.2) ++ " }"

mutual
def render : PExpr → String
  | .ident n => n
  | .int k => toString k
  | .str s => quoted s
  | .bool b => if b then "true" else "false"
  | .call fn args => fn ++ "(" ++ String.intercalate ", " (renderList args) ++ ")"
  | .object ks vs => objText (fun k => k) ks (renderList vs)
  | .objectQuoted ks vs => objText quoted ks (renderList vs)
  | .objectComputed ks vs => objText (fun k => "[" ++ quoted k ++ "]") ks (renderList vs)
  | .member t n => render t ++ "." ++ n
  | .index t k => render t ++ "[" ++ quoted k ++ "]"
def renderList : List PExpr → List String
  | [] => []
  | x :: xs => render x :: renderList xs
end

-- the shared fragment spells as the vendored renderer does
#guard render (.object ["a", "b"] [.int 1, .str "x"]) ==
  TypeScript.Render.expr TypeScript.house0 0 (.object [("a", .int 1), ("b", .str "x")])
#guard render (.objectQuoted ["a-b", "a\"b"] [.int 1, .bool true]) ==
  TypeScript.Render.expr TypeScript.house0 0 (.objectQuoted [("a-b", .int 1), ("a\"b", .bool true)])
#guard render (.member (.ident "a0") "name") ==
  TypeScript.Render.expr TypeScript.house0 0 (.member (.ident "a0") "name")
#guard render (.call "pair" [.int 200, .member (.ident "a0") "name"]) ==
  TypeScript.Render.expr TypeScript.house0 0 (.call (.ident "pair") [.int 200, .member (.ident "a0") "name"])
#guard render (.object [] []) == TypeScript.Render.expr TypeScript.house0 0 (.object [])

/-! ## 4. The printer -/

def printLit : Lit → PExpr
  | .unit => .ident "undefined"
  | .nat n => .int n
  | .bool b => .bool b
  | .str s => .str s

mutual
def printTerm : Term → PExpr
  | .var i => .ident (Effect4.Program.Var.name i)
  | .lit v => printLit v
  | .app atom args => .call atom (printTerms args)
  | .record labels args => mkObject labels (printTerms args)
  | .field t _ n => mkAccess (printTerm t) n
def printTerms : Terms → List PExpr
  | .nil => []
  | .cons h t => printTerm h :: printTerms t
end

/-! ## 5. Positional values: printing a value is type-directed -/

def applyPos : List Val → List (String × (Val → Option PExpr)) → Option (List PExpr)
  | [], [] => some []
  | v :: vs, (_, p) :: ps => do
    let x ← p v
    let xs ← applyPos vs ps
    some (x :: xs)
  | _, _ => none

mutual
/-- A value printed at its type. The record arm takes its keys from the type. -/
def printVal : MTy → Val → Option PExpr
  | .unit, v => match v with | .unit => some (.ident "undefined") | _ => none
  | .nat, v => match v with | .nat n => some (.int n) | _ => none
  | .string, v => match v with | .str s => some (.str s) | _ => none
  | .bool, v => match v with | .bool b => some (.bool b) | _ => none
  | .lit s, v => match v with | .str t => if t = s then some (.str t) else none | _ => none
  | .prod a b, v =>
    match v with
    | .list [x, y] => do
      let px ← printVal a x
      let py ← printVal b y
      some (.call "pair" [px, py])
    | _ => none
  | .union a b, v => (printVal a v).orElse (fun _ => printVal b v)
  | .record fs, v =>
    match v with
    | .ctor 0 vs =>
      (applyPos vs (canon (printers fs))).map (mkObject ((canon (printers fs)).map Prod.fst))
    | _ => none
def printers : List (String × MTy) → List (String × (Val → Option PExpr))
  | [] => []
  | (n, t) :: fs => (n, printVal t) :: printers fs
end

/-- One positional value, two record types, two printed objects. -/
theorem printVal_needs_type :
    printVal (.record [("body", .string)]) (.ctor 0 [.str "x"]) = some (.object ["body"] [.str "x"]) ∧
      printVal (.record [("name", .string)]) (.ctor 0 [.str "x"]) = some (.object ["name"] [.str "x"]) := by
  constructor <;> rfl

#guard ((printVal (.record [("status", .nat), ("body", .string)]) (.ctor 0 [.str "bob", .nat 200])).map render) ==
  some "{ body: \"bob\", status: 200 }"

/-! ## 6. The typed reader: the projection's position resolved from the target's type -/

/-- Resolve a read projection: type the target, find the name's canonical position. -/
def resolve (sig : Sig) (Γ : List MTy) (target : Option Term) (n : String) : Option Term := do
  let tt ← target
  let r ← argTy sig Γ false tt
  match r with
  | .record fs => (fieldPos n (canon fs)).map (fun p => .field tt p.1 n)
  | _ => none

mutual
def readTermT (sig : Sig) (Γ : List MTy) : PExpr → Option Term
  | .ident s =>
    match Effect4.Program.Var.read Γ.length s with
    | some i => some (.var i)
    | none => if s = "undefined" then some (.lit .unit) else none
  | .int k => some (.lit (.nat k))
  | .str s => some (.lit (.str s))
  | .bool b => some (.lit (.bool b))
  | .call atom args => (readTermsT sig Γ args).map (.app atom)
  | .object keys values =>
    if objForm keys = .plain then (readTermsT sig Γ values).map (.record keys) else none
  | .objectQuoted keys values =>
    if objForm keys = .quoted then (readTermsT sig Γ values).map (.record keys) else none
  | .objectComputed keys values =>
    if objForm keys = .computed then (readTermsT sig Γ values).map (.record keys) else none
  | .member t n => if identName n then resolve sig Γ (readTermT sig Γ t) n else none
  | .index t n => if identName n then none else resolve sig Γ (readTermT sig Γ t) n
def readTermsT (sig : Sig) (Γ : List MTy) : List PExpr → Option Terms
  | [] => some .nil
  | x :: xs => do
    let t ← readTermT sig Γ x
    let ts ← readTermsT sig Γ xs
    some (.cons t ts)
end

theorem fieldTy_inv {r : MTy} {i : Nat} {n : String} {τ : MTy} (h : fieldTy r i n = some τ) :
    ∃ fs, r = .record fs ∧ fieldPos n (canon fs) = some (i, τ) := by
  cases r with
  | record fs =>
    simp only [fieldTy] at h
    split at h
    · rename_i j σ hpos
      split at h
      · rename_i hj
        subst hj
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨fs, rfl, hpos⟩
      · exact nomatch h
    · exact nomatch h
  | _ => simp only [fieldTy, reduceCtorEq] at h

theorem read_mkObject (sig : Sig) (Γ : List MTy) (keys : List String) (values : List PExpr)
    (args : Terms) (h : readTermsT sig Γ values = some args) :
    readTermT sig Γ (mkObject keys values) = some (.record keys args) := by
  unfold mkObject
  split
  · rename_i hf
    simp only [readTermT, hf, ↓reduceIte, h, Option.map_some]
  · rename_i hf
    simp only [readTermT, hf, ↓reduceIte, h, Option.map_some]
  · rename_i hf
    simp only [readTermT, hf, ↓reduceIte, h, Option.map_some]

theorem read_undefined (sig : Sig) (Γ : List MTy) :
    readTermT sig Γ (.ident "undefined") = some (.lit .unit) := by
  have hnone : Effect4.Program.Var.read Γ.length "undefined" = none :=
    Effect4.Program.Var.read_none (fun i => Effect4.Program.Var.name_ne_undefined i)
  simp only [readTermT, hnone, ↓reduceIte]

mutual
/-- `read_print` for the typed reader: every well-typed term reads back as itself. -/
theorem read_print (sig : Sig) (Γ : List MTy) :
    ∀ (t : Term) (c : Bool) (τ : MTy), argTy sig Γ c t = some τ →
      readTermT sig Γ (printTerm t) = some t
  | .var i, c, τ, h => by
    simp only [argTy] at h
    have hi : i < Γ.length := (List.getElem?_eq_some_iff.mp h).1
    simp only [printTerm, readTermT, Effect4.Program.Var.read_name hi]
  | .lit v, c, τ, h => by
    cases v with
    | unit => simp only [printTerm, printLit, read_undefined]
    | nat n => simp only [printTerm, printLit, readTermT]
    | bool b => simp only [printTerm, printLit, readTermT]
    | str s => simp only [printTerm, printLit, readTermT]
  | .app atom args, c, τ, h => by
    simp only [argTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨tys, htys, _⟩ := h
    simp only [printTerm, readTermT, read_printArgs sig Γ args (sig.constAtom atom) tys htys,
      Option.map_some]
  | .record labels args, c, τ, h => by
    simp only [argTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨tys, htys, _⟩ := h
    simp only [printTerm]
    exact read_mkObject sig Γ labels (printTerms args) args (read_printArgs sig Γ args false tys htys)
  | .field t i n, c, τ, h => by
    simp only [argTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, hfield⟩ := h
    obtain ⟨fs, rfl, hpos⟩ := fieldTy_inv hfield
    have ih := read_print sig Γ t false (.record fs) hr
    simp only [printTerm, mkAccess]
    cases hn : identName n with
    | true =>
      simp only [↓reduceIte, readTermT, hn, ih, resolve, hr, hpos, Option.bind_eq_bind,
        Option.bind_some, Option.map_some]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, readTermT, hn, ih, resolve, hr, hpos,
        Option.bind_eq_bind, Option.bind_some, Option.map_some]
theorem read_printArgs (sig : Sig) (Γ : List MTy) :
    ∀ (ts : Terms) (c : Bool) (tys : List MTy), argsTy sig Γ c ts = some tys →
      readTermsT sig Γ (printTerms ts) = some ts
  | .nil, c, tys, h => rfl
  | .cons head tail, c, tys, h => by
    simp only [argsTy, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t, ht, rest, hrest, _⟩ := h
    simp only [printTerms, readTermsT, read_print sig Γ head c t ht,
      read_printArgs sig Γ tail c rest hrest, Option.bind_eq_bind, Option.bind_some]
end

theorem resolve_some {sig : Sig} {Γ : List MTy} {target : Option Term} {n : String} {t : Term}
    (h : resolve sig Γ target n = some t) :
    ∃ tt i, target = some tt ∧ t = .field tt i n := by
  simp only [resolve, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨tt, htt, r, _, hm⟩ := h
  refine ⟨tt, ?_⟩
  split at hm
  · obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨p.1, htt, hp.symm⟩
  · exact nomatch hm

mutual
/-- `read_exact` for the typed reader: an accepted tree is the printing of what was read. -/
theorem read_exact (sig : Sig) (Γ : List MTy) :
    ∀ (x : PExpr) (t : Term), readTermT sig Γ x = some t → printTerm t = x
  | .ident s, t, h => by
    simp only [readTermT] at h
    split at h
    · rename_i i hi
      simp only [Option.some.injEq] at h
      subst h
      simp only [printTerm, (Effect4.Program.Var.read_exact hi).1]
    · split at h
      · rename_i hs
        simp only [Option.some.injEq] at h
        subst h
        subst hs
        rfl
      · exact nomatch h
  | .int k, t, h => by
    simp only [readTermT, Option.some.injEq] at h
    subst h
    rfl
  | .str s, t, h => by
    simp only [readTermT, Option.some.injEq] at h
    subst h
    rfl
  | .bool b, t, h => by
    simp only [readTermT, Option.some.injEq] at h
    subst h
    rfl
  | .call atom args, t, h => by
    simp only [readTermT] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [printTerm, read_exactArgs sig Γ args ts hts]
  | .object keys values, t, h => by
    simp only [readTermT] at h
    split at h
    · rename_i hf
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkObject, hf, read_exactArgs sig Γ values ts hts]
    · exact nomatch h
  | .objectQuoted keys values, t, h => by
    simp only [readTermT] at h
    split at h
    · rename_i hf
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkObject, hf, read_exactArgs sig Γ values ts hts]
    · exact nomatch h
  | .objectComputed keys values, t, h => by
    simp only [readTermT] at h
    split at h
    · rename_i hf
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkObject, hf, read_exactArgs sig Γ values ts hts]
    · exact nomatch h
  | .member target n, t, h => by
    simp only [readTermT] at h
    split at h
    · rename_i hn
      obtain ⟨tt, i, htt, rfl⟩ := resolve_some h
      simp only [printTerm, mkAccess, hn, ↓reduceIte, read_exact sig Γ target tt htt]
    · exact nomatch h
  | .index target n, t, h => by
    simp only [readTermT] at h
    split at h
    · exact nomatch h
    · rename_i hn
      obtain ⟨tt, i, htt, rfl⟩ := resolve_some h
      simp only [printTerm, mkAccess, hn, Bool.false_eq_true, ↓reduceIte,
        read_exact sig Γ target tt htt]
theorem read_exactArgs (sig : Sig) (Γ : List MTy) :
    ∀ (xs : List PExpr) (ts : Terms), readTermsT sig Γ xs = some ts → printTerms ts = xs
  | [], ts, h => by
    simp only [readTermsT, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, ts, h => by
    simp only [readTermsT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t, ht, rest, hrest, rfl⟩ := h
    simp only [printTerms, read_exact sig Γ x t ht, read_exactArgs sig Γ xs rest hrest]
end

/-! ## 7. No reader that ignores types inverts the printer on well-typed terms -/

def sig0 : Sig := { atomOf := fun _ _ => none, constAtom := fun _ => false }
def layoutAB : MTy := .record [("a", .nat), ("b", .string)]
def layoutBC : MTy := .record [("b", .nat), ("c", .string)]

theorem no_untyped_reader : ¬ ∃ read : PExpr → Option Term,
    ∀ (Γ : List MTy) (t : Term) (τ : MTy), argTy sig0 Γ false t = some τ →
      read (printTerm t) = some t := by
  intro ⟨read, h⟩
  have h1 := h [layoutAB] (.field (.var 0) 1 "b") .string rfl
  have h2 := h [layoutBC] (.field (.var 0) 0 "b") .nat rfl
  have hp : printTerm (.field (.var 0) 1 "b") = printTerm (.field (.var 0) 0 "b") := rfl
  rw [hp, h2, Option.some.injEq] at h1
  injection h1 with _ hi
  exact absurd hi (by decide)

/-! ## 8. The image per name class, rendered (the lines of `host/names/forms-green.ts`) -/

def pTerm (t : Term) : String := render (printTerm t)

-- `{ b: "x", a: 1 }`: identifiers bare, written order kept
#guard pTerm (.record ["b", "a"] (.cons (.lit (.str "x")) (.cons (.lit (.nat 1)) .nil))) == "{ b: \"x\", a: 1 }"
-- one name outside the profile quotes them all; bracket access for it
#guard pTerm (.record ["a-b", "default"] (.cons (.lit (.nat 1)) (.cons (.lit (.bool true)) .nil))) ==
  "{ \"a-b\": 1, \"default\": true }"
#guard pTerm (.field (.var 0) 0 "a-b") == "a0[\"a-b\"]"
#guard pTerm (.field (.var 0) 0 "default") == "a0.default"
-- `__proto__`: computed keys (own property), bracket access
#guard pTerm (.record ["__proto__", "a"] (.cons (.lit (.str "x")) (.cons (.lit (.nat 1)) .nil))) ==
  "{ [\"__proto__\"]: \"x\", [\"a\"]: 1 }"
#guard pTerm (.field (.var 0) 0 "__proto__") == "a0[\"__proto__\"]"
-- Unicode is outside the ASCII profile: quoted, bracket
#guard pTerm (.field (.var 0) 0 "名前") == "a0[\"名前\"]"
#guard identName "naïve" == false
-- the reader refuses every other spelling of the same object or access
#guard (readTermT sig0 [] (.objectQuoted ["a"] [.int 1])).isNone
#guard (readTermT sig0 [] (.object ["a-b"] [.int 1])).isNone
#guard (readTermT sig0 [] (.object ["__proto__"] [.int 1])).isNone
#guard (readTermT sig0 [] (.objectQuoted ["__proto__"] [.int 1])).isNone
#guard (readTermT sig0 [layoutAB] (.index (.ident "a0") "b")).isNone
#guard (readTermT sig0 [layoutAB] (.member (.ident "a0") "b")) == some (.field (.var 0) 1 "b")
#guard (readTermT sig0 [layoutBC] (.member (.ident "a0") "b")) == some (.field (.var 0) 0 "b")
#guard (readTermT sig0 [layoutAB] (.member (.ident "a0") "z")).isNone

end SeatR.Faces

/-! ## 9. With names in the value: the untyped reader inverts the printer -/

namespace SeatR.Faces.Named

open SeatR.Faces (PExpr mkObject mkAccess identName objForm ObjForm printLit read_undefined)
open Effect4.Program (Lit)

mutual
  inductive Term
    | var (index : Nat)
    | lit (value : Lit)
    | app (atom : String) (args : Terms)
    | record (labels : List String) (args : Terms)
    | field (target : Term) (name : String)
  inductive Terms
    | nil
    | cons (head : Term) (tail : Terms)
end

mutual
def inScope (n : Nat) : Term → Bool
  | .var i => decide (i < n)
  | .lit _ => true
  | .app _ args => scopedArgs n args
  | .record _ args => scopedArgs n args
  | .field t _ => inScope n t
def scopedArgs (n : Nat) : Terms → Bool
  | .nil => true
  | .cons h t => inScope n h && scopedArgs n t
end

mutual
def printTerm : Term → PExpr
  | .var i => .ident (Effect4.Program.Var.name i)
  | .lit v => printLit v
  | .app atom args => .call atom (printTerms args)
  | .record labels args => mkObject labels (printTerms args)
  | .field t n => mkAccess (printTerm t) n
def printTerms : Terms → List PExpr
  | .nil => []
  | .cons h t => printTerm h :: printTerms t
end

mutual
/-- The reader with no types: depth only, as `Codegen/Read.lean`'s `readTerm`. -/
def readTerm (n : Nat) : PExpr → Option Term
  | .ident s =>
    match Effect4.Program.Var.read n s with
    | some i => some (.var i)
    | none => if s = "undefined" then some (.lit .unit) else none
  | .int k => some (.lit (.nat k))
  | .str s => some (.lit (.str s))
  | .bool b => some (.lit (.bool b))
  | .call atom args => (readTerms n args).map (.app atom)
  | .object keys values =>
    if objForm keys = .plain then (readTerms n values).map (.record keys) else none
  | .objectQuoted keys values =>
    if objForm keys = .quoted then (readTerms n values).map (.record keys) else none
  | .objectComputed keys values =>
    if objForm keys = .computed then (readTerms n values).map (.record keys) else none
  | .member t name => if identName name then (readTerm n t).map (fun tt => .field tt name) else none
  | .index t name => if identName name then none else (readTerm n t).map (fun tt => .field tt name)
def readTerms (n : Nat) : List PExpr → Option Terms
  | [] => some .nil
  | x :: xs => do
    let t ← readTerm n x
    let ts ← readTerms n xs
    some (.cons t ts)
end

theorem read_mkObject (n : Nat) (keys : List String) (values : List PExpr) (args : Terms)
    (h : readTerms n values = some args) :
    readTerm n (mkObject keys values) = some (.record keys args) := by
  unfold mkObject
  split
  · rename_i hf
    simp only [readTerm, hf, ↓reduceIte, h, Option.map_some]
  · rename_i hf
    simp only [readTerm, hf, ↓reduceIte, h, Option.map_some]
  · rename_i hf
    simp only [readTerm, hf, ↓reduceIte, h, Option.map_some]

theorem read_undefinedN (n : Nat) : readTerm n (.ident "undefined") = some (.lit .unit) := by
  have hnone : Effect4.Program.Var.read n "undefined" = none :=
    Effect4.Program.Var.read_none (fun i => Effect4.Program.Var.name_ne_undefined i)
  simp only [readTerm, hnone, ↓reduceIte]

mutual
/-- `read_print` with no types: every scoped term reads back as itself. -/
theorem read_print (n : Nat) : ∀ (t : Term), inScope n t = true → readTerm n (printTerm t) = some t
  | .var i, h => by
    simp only [inScope, decide_eq_true_eq] at h
    simp only [printTerm, readTerm, Effect4.Program.Var.read_name h]
  | .lit v, _ => by
    cases v with
    | unit => simp only [printTerm, printLit, read_undefinedN]
    | nat k => simp only [printTerm, printLit, readTerm]
    | bool b => simp only [printTerm, printLit, readTerm]
    | str s => simp only [printTerm, printLit, readTerm]
  | .app atom args, h => by
    simp only [inScope] at h
    simp only [printTerm, readTerm, read_printArgs n args h, Option.map_some]
  | .record labels args, h => by
    simp only [inScope] at h
    simp only [printTerm]
    exact read_mkObject n labels (printTerms args) args (read_printArgs n args h)
  | .field t name, h => by
    simp only [inScope] at h
    simp only [printTerm, mkAccess]
    cases hn : identName name with
    | true => simp only [↓reduceIte, readTerm, hn, read_print n t h, Option.map_some]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, readTerm, hn, read_print n t h, Option.map_some]
theorem read_printArgs (n : Nat) : ∀ (ts : Terms), scopedArgs n ts = true →
    readTerms n (printTerms ts) = some ts
  | .nil, _ => rfl
  | .cons h t, hs => by
    simp only [scopedArgs, Bool.and_eq_true] at hs
    simp only [printTerms, readTerms, read_print n h hs.1, read_printArgs n t hs.2,
      Option.bind_eq_bind, Option.bind_some]
end

mutual
/-- `read_exact` with no types. -/
theorem read_exact (n : Nat) : ∀ (x : PExpr) (t : Term), readTerm n x = some t → printTerm t = x
  | .ident s, t, h => by
    simp only [readTerm] at h
    split at h
    · rename_i i hi
      simp only [Option.some.injEq] at h
      subst h
      simp only [printTerm, (Effect4.Program.Var.read_exact hi).1]
    · split at h
      · rename_i hs
        simp only [Option.some.injEq] at h
        subst h
        subst hs
        rfl
      · exact nomatch h
  | .int k, t, h => by
    simp only [readTerm, Option.some.injEq] at h
    subst h
    rfl
  | .str s, t, h => by
    simp only [readTerm, Option.some.injEq] at h
    subst h
    rfl
  | .bool b, t, h => by
    simp only [readTerm, Option.some.injEq] at h
    subst h
    rfl
  | .call atom args, t, h => by
    simp only [readTerm] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [printTerm, read_exactArgs n args ts hts]
  | .object keys values, t, h => by
    simp only [readTerm] at h
    split at h
    · rename_i hf
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkObject, hf, read_exactArgs n values ts hts]
    · exact nomatch h
  | .objectQuoted keys values, t, h => by
    simp only [readTerm] at h
    split at h
    · rename_i hf
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkObject, hf, read_exactArgs n values ts hts]
    · exact nomatch h
  | .objectComputed keys values, t, h => by
    simp only [readTerm] at h
    split at h
    · rename_i hf
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkObject, hf, read_exactArgs n values ts hts]
    · exact nomatch h
  | .member target name, t, h => by
    simp only [readTerm] at h
    split at h
    · rename_i hn
      obtain ⟨tt, htt, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkAccess, hn, ↓reduceIte, read_exact n target tt htt]
    · exact nomatch h
  | .index target name, t, h => by
    simp only [readTerm] at h
    split at h
    · exact nomatch h
    · rename_i hn
      obtain ⟨tt, htt, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printTerm, mkAccess, hn, Bool.false_eq_true, ↓reduceIte, read_exact n target tt htt]
theorem read_exactArgs (n : Nat) :
    ∀ (xs : List PExpr) (ts : Terms), readTerms n xs = some ts → printTerms ts = xs
  | [], ts, h => by
    simp only [readTerms, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, ts, h => by
    simp only [readTerms, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t, ht, rest, hrest, rfl⟩ := h
    simp only [printTerms, read_exact n x t ht, read_exactArgs n xs rest hrest]
end

end SeatR.Faces.Named

#print axioms SeatR.Faces.printVal_needs_type
#print axioms SeatR.Faces.read_print
#print axioms SeatR.Faces.read_exact
#print axioms SeatR.Faces.no_untyped_reader
#print axioms SeatR.Faces.Named.read_print
#print axioms SeatR.Faces.Named.read_exact
