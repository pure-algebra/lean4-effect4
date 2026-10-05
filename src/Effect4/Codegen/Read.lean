import Effect4.Codegen.Print
import Effect4.Codegen.Templates
import Effect4.Program.Native
import Effect4.Program.Table

/-!
# Codegen.Read — the printer's image back into `Eff`, read from the table the printer prints from

`readT` is ONE generic step over the table of printed clauses (`Codegen/Templates.lean`): the
first row of a family whose skeleton matches the tree (`Template.matchT`), its arguments read by
sort from what the skeleton captured, and the constructor rebuilt by the generated `build`
(`Program/LayerView.lean`). A child is read by the same step, so the reader has no arm per
constructor. It recurses on the size of the tree: a rigid skeleton captures only proper
sub-expressions (`Template.match_below`), and a transparent row (`withFiber`, a bare hole over
its action) hands the same tree to a strictly lower family. This is proved for ANY table; what a
good table adds is the laws, not totality.

What is not a skeleton is read as the printer's hand fields print it: a generator's statements,
and the row call of `perform` (the inverse of the signature's `spell`). The leaf readers (terms,
causes, keys, fork options, literals, rows) are below. Their reconstruction laws are in
`Laws/Codegen/ReadLeaf.lean`.

A row is accepted only when the printer would choose it for the arguments read
(`Row.selects`), so what is read prints back to the tree read: `Effect.catchIf` with a literal
`true` test is refused, because the printer writes that program as `Effect.catch`.

`readable` is the round trip itself: printing the program and reading it back gives the program.
What it excludes is what the printer loses and no reader can recover: a variable out of scope,
the request of a `unit`-request row (the printer drops it), the `daemon` flag of a scoped fork
(the options object has no such field), a loop's cursor annotation (no reader of types exists,
B19). `LawfulSpelling` is what the row reader needs of a signature.

Binders are recovered by comparison, never by decoding: `Var.read n s` is the position `i < n`
with `Var.name i = s`. Nothing here folds over a string (`String.toList` and its kin reach
`Classical.choice` on this toolchain).

Owed (R5.2): `read_print` and `read_exact` over the table, through the engine lemmas
`match_inst` and `inst_of_match` (`Laws/Codegen/Template.lean`). The hand reader they were
proved for is deleted; on the seeded corpus the table reader agrees with it wherever it read,
reads 44 more images, and is exact on all 400.
-/

namespace Effect4.Program

open TypeScript (Expr Stmt)

/-! ## Refusals -/

/-- Why the reader declined a tree. -/
inductive ReadRefusal
  /-- A call whose head is a reserved name with no `Eff` reading in that position
  (`Cause.fail` outside a cause, `Effect.whileLoop` outside its suspend). -/
  | unknownHead (name : String)
  /-- An identifier that is no binder, no reserved name, and no value row. -/
  | unknownIdent (name : String)
  /-- A row called with an argument list its row table does not print. -/
  | arity (head : String)
  /-- A lambda, `const` or `step` parameter that is not the binder due at that position. -/
  | binder (expected : String)
  /-- Any other form the printer never emits; `what` names the position. -/
  | shape (what : String)
  /-- A negative integer literal. -/
  | negative (value : Int)
  /-- A statement form the printer never emits. -/
  | unsupportedStmt
  /-- A binder, return or local annotation the raw printer never emits; `site` names the
  position. This is not `arity` (an argument list the row table does not print) and not
  `unsupportedStmt` (a statement form with no reading): a consumer routing on the alphabet
  must be able to tell "annotated, not admitted here" from "wrong shape". -/
  | annotation (site : String)
deriving DecidableEq, Repr

/-! ## Annotations the raw reader does not admit

The raw reader accepts the unannotated image the printer emits. Where a tree carries an
annotation in a position the printer leaves bare, the refusal says so by name instead of
falling through to the arity or statement-shape refusal. These two functions sit in the
row reader's refusal arms. -/

/-- The annotated position of an expression the printer would have emitted bare. -/
def annotationSite : Expr → Option String
  | .arrow (some _) _ => some "thunk return"
  | .lambda params _ type | .arrowBlock params _ type =>
    if params.any (fun param => param.type.isSome) then some "parameter"
    else if type.isSome then some "return" else none
  | _ => none

/-- The refusal of a reserved head applied to an argument list no arm reads: an annotation
where the printer emits none, otherwise the argument list itself. -/
def callRefusal (head : Head) (args : List Expr) : ReadRefusal :=
  match args.findSome? annotationSite with
  | some site => .annotation (head.spelling ++ " " ++ site)
  | none => .arity head.spelling

/-- The refusal of a statement the generator reader does not read: an annotated local or
yielded constant by name, otherwise the statement form. -/
def stmtRefusal : TypeScript.Stmt → ReadRefusal
  | .constYield _ _ (some _) => .annotation "yielded const"
  | .letInit _ _ (some _) => .annotation "local const"
  | _ => .unsupportedStmt

/-! ## Binders -/

/-- The position `i < n` whose binder is `s`, searched from the newest binder down; `none`
when `s` is no binder of the first `n` positions. Comparison only: no digit is decoded. -/
def Var.read : Nat → String → Option Nat
  | 0, _ => none
  | n + 1, s => if Var.name n = s then some n else Var.read n s

/-! ## The reserved heads -/

-- `Head`, `Head.spelling`, `heads`, and `reserved` are imported from `Effect4.Codegen.Print`.

/-- The head a spelling names, if any. -/
def headOf (s : String) : Option Head := heads.find? fun h => decide (h.spelling = s)

theorem heads_complete (h : Head) : h ∈ heads := by cases h <;> decide

theorem headOf_spelling (h : Head) : headOf h.spelling = some h := by cases h <;> decide

theorem headOf_exact {s : String} {h : Head} (hh : headOf s = some h) : s = h.spelling := by
  have := List.find?_some hh
  simp at this
  exact this.symm

theorem headOf_none {s : String} (hs : s ∉ reserved) : headOf s = none := by
  unfold headOf
  rw [List.find?_eq_none]
  intro h _ hp
  simp at hp
  exact hs (hp ▸ List.mem_map.mpr ⟨h, heads_complete h, rfl⟩)

theorem mem_reserved_of_headOf {s : String} {h : Head} (hh : headOf s = some h) :
    s ∈ reserved :=
  headOf_exact hh ▸ List.mem_map.mpr ⟨h, heads_complete h, rfl⟩

/-! ## Terms -/

/-- The refusal of an expression that no term arm reads: a list fold with a type argument by
name, since a stated accumulator type is printed and not read (B19; decisions row 228), and the
term shape otherwise. -/
def termRefusal : Expr → ReadRefusal
  | .call (.generic (.ident head) _) _ =>
    if head = "fold" then .annotation "fold accumulator" else .shape "term"
  | _ => .shape "term"

mutual
  /-- Recover a pure term from its target expression, including raw record declarations.
  Generic wrapper heads distinguish the new forms from arbitrary legacy atom calls.
  Variable scope is checked here; type formation and target admission remain separate.
  A class construction `new Tag({ … })` (decisions row 120) reads as the record term whose
  fields the module's `classes` declare for `Tag`, with `_tag` restored first; it is accepted
  only when the printer prints that term as this construction (`Classes.classTag?`), and a
  structural record the printer would print as a construction is refused. A list fold
  `fold(list, init, (aN, aM) => body)` (decisions row 228) reads its list and its initial value
  at the level `n` and its body at `n + 2`; its two parameters are the binders due there
  (`ListFold.read`). -/
  def readTerm (classes : Effect4.Codegen.Classes.Classes) (n : Nat) (x : Expr) :
      Except ReadRefusal Term :=
    match hc : Effect4.Codegen.Classes.readClass x with
    | some (tag, names, values) =>
      have := Effect4.Codegen.Classes.readClass_size x tag names values hc
      match classes.lookup tag with
      | none => .error (.unknownIdent tag)
      | some fields => do
        let vs ← readTerms classes n values
        if Effect4.Codegen.Classes.classTag? fields ("_tag" :: names) (.cons (.lit (.str tag)) vs) =
            some tag then
          .ok (.record fields ("_tag" :: names) (.cons (.lit (.str tag)) vs))
        else .error (.shape "class")
    | none =>
    match hr : Effect4.Codegen.Record.readRecord x with
    | some (fields, names, values) => do
      have := Effect4.Codegen.Record.readRecord_size x fields names values hr
      let vs ← readTerms classes n values
      if (Effect4.Codegen.Classes.classTag? fields names vs).isNone then .ok (.record fields names vs)
      else .error (.shape "record in class form")
    | none =>
      match hf : Effect4.Codegen.Record.readField x with
      | some (optional, name, target) =>
        have := Effect4.Codegen.Record.readField_size x optional name target hf
        (readTerm classes n target).map fun t =>
          .field (if optional then .optional else .required) t name
      | none =>
        match hs : Effect4.Codegen.Record.readSet x with
        | some (name, target, value) => do
          have := Effect4.Codegen.Record.readSet_size x name target value hs
          let t ← readTerm classes n target
          let v ← readTerm classes n value
          .ok (.recordSet t name v)
        | none =>
          match ht : Effect4.Codegen.Tuple.readAt x with
          | some (index, target) =>
            have := Effect4.Codegen.Tuple.readAt_size x index target ht
            (readTerm classes n target).map fun t => .tupleAt t index
          | none =>
            match hl : Effect4.Codegen.ListFold.read n x with
            | some (list, init, body) => do
              have := Effect4.Codegen.ListFold.read_size n x list init body hl
              let l ← readTerm classes n list
              let i ← readTerm classes n init
              let b ← readTerm classes (n + 2) body
              .ok (.fold none l i b)
            | none =>
              match x with
              | .ident s =>
                match Var.read n s with
                | some i => .ok (.var i)
                | none => if s = "undefined" then .ok (.lit .unit) else .error (.unknownIdent s)
              | .int k => if 0 ≤ k then .ok (.lit (.nat k.toNat)) else .error (.negative k)
              | .bool b => .ok (.lit (.bool b))
              | .str s => .ok (.lit (.str s))
              | .call (.ident atom) args => (readTerms classes n args).map (.app atom)
              | _ => .error (termRefusal x)
  termination_by sizeOf x
  decreasing_by all_goals simp_wf; all_goals omega

  /-- An argument list, in order. -/
  def readTerms (classes : Effect4.Codegen.Classes.Classes) (n : Nat) (xs : List Expr) :
      Except ReadRefusal Terms :=
    match xs with
    | [] => .ok .nil
    | x :: rest => do
      let t ← readTerm classes n x
      let ts ← readTerms classes n rest
      .ok (.cons t ts)
  termination_by sizeOf xs
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- A cause back from the public `Cause` constructors the printer spells. -/
def readCause (classes : Effect4.Codegen.Classes.Classes) (n : Nat) (x : Expr) :
    Except ReadRefusal CauseTerm :=
  match x with
  | .call (.ident s) args =>
    match headOf s, args with
    | some .causeFail, [e] => (readTerm classes n e).map .fail
    | some .causeDie, [d] => (readTerm classes n d).map .die
    | some .causeInterrupt, [] => .ok (.interrupt none)
    | some .causeInterrupt, [who] => (readTerm classes n who).map fun w => .interrupt (some w)
    | some .causeCombine, [l, r] => do
      let a ← readCause classes n l
      let b ← readCause classes n r
      .ok (.both a b)
    | _, _ => .error (.shape "cause")
  | _ => .error (.shape "cause")
termination_by structural x

/-- The fork options object back into `ForkOptions`. The object carries no `daemon`
field: `Effect.forkChild` against `Effect.forkDetach` decides it for a plain fork, and the
scoped forks (`forkIn`, `forkScoped`) read it as `false`. -/
def readForkOptions (daemon : Bool) (x : Expr) :
    Except ReadRefusal Effect4.Supervision.ForkOptions :=
  match x with
  | .object [(f1, .bool start), (f2, u)] =>
    if f1 = "startImmediately" ∧ f2 = "uninterruptible" then
      match u with
      | .bool true => .ok ⟨start, daemon, .uninterruptible⟩
      | .bool false => .ok ⟨start, daemon, .interruptible⟩
      | .str s => if s = "inherit" then .ok ⟨start, daemon, .inherit⟩ else .error (.shape "forkOptions")
      | _ => .error (.shape "forkOptions")
    else .error (.shape "forkOptions")
  | _ => .error (.shape "forkOptions")

/-! ## Rows

The reader takes `spell : String → List String → Option Op`, the inverse of a row's
(spelling, trailing names): the trailing names are part of a row's identity in the image
(`Ref.update(ref, incr)` and `Ref.update(ref, double)` are two rows of one spelling). A call
row's argument list is the trailing names alone on a `unit` request, and the request
followed by the trailing names otherwise; the reader tries both readings, and
`LawfulSpelling` is what makes at most one succeed. -/

variable {Op : Type}

/-- The names of an argument list made of identifiers only. -/
def idents? : List Expr → Option (List String)
  | [] => some []
  | .ident s :: rest => (idents? rest).map (s :: ·)
  | _ :: _ => none

/-- The reading of a row: a `perform`, the one invocation form. The row's kind selects the
route at the compile, not the syntax. (The row stays a parameter so that the readers of the
four row shapes keep one signature.) -/
def rowAnswer (_row : Row) (op : Op) (request : Term) : Eff Op := .perform op request

/-- A bare identifier as a value row. -/
def readRowValue (sig : Signature Op) (spell : String → List String → Option Op)
    (s : String) : Except ReadRefusal (Eff Op) :=
  match spell s [] with
  | some op =>
    if (sig.rowOf op).shape = .value then .ok (rowAnswer (sig.rowOf op) op (.lit .unit))
    else .error (.arity s)
  | none => .error (.unknownIdent s)

/-- The saved variable whose two components a tuple-call row receives, when its two
arguments are exactly `fst(a)` and `snd(a)` of one identifier `a` (source-repairs §18). -/
def savedVar? : Expr → Expr → Option String
  | .call (.ident f) [.ident v], .call (.ident g) [.ident w] =>
    if f = "fst" ∧ g = "snd" ∧ v = w then some v else none
  | _, _ => none

theorem savedVar?_some {x y : Expr} {v : String} (h : savedVar? x y = some v) :
    x = .call (.ident "fst") [.ident v] ∧ y = .call (.ident "snd") [.ident v] := by
  unfold savedVar? at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- The request of a tuple-call row from its two arguments: the components of one saved
variable read back as that variable, any other two terms as their `pair` application. -/
def readTupleArgs (classes : Effect4.Codegen.Classes.Classes) (n : Nat) (x y : Expr) :
    Except ReadRefusal Term :=
  match savedVar? x y with
  | some v => readTerm classes n (.ident v)
  | none => do
    let a ← readTerm classes n x
    let b ← readTerm classes n y
    .ok (.app "pair" (.cons a (.cons b .nil)))

/-- A call as a call row; `none` when no row of the table has this head and argument
shape, so the caller may read an atom application instead. A call row's argument list is
the trailing names alone on a `unit` request, and the request followed by the trailing
names otherwise; a tuple-call row's is its two request arguments followed by the trailing
names. The three readings are tried in that order, and `LawfulSpelling` is what makes at
most one succeed. -/
def readRowCall (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    (s : String) (typeArgs : List TypeScript.TypeRef) (args : List Expr) : Option (Except ReadRefusal (Eff Op)) :=
  -- the call's type arguments must be exactly the ones the row declares: a row that needs
  -- them refuses a bare call, and a row that declares none refuses a call that carries any
  -- (`E4-CHECK-CE-013`)
  match (idents? args).bind (spell s) with
  | some op =>
    some (if (sig.rowOf op).shape = .call ∧ (sig.rowOf op).request = Ty.unit ∧
        rowTypeArgs (sig.rowOf op) = some typeArgs then
      .ok (rowAnswer (sig.rowOf op) op (.lit .unit))
    else .error (.arity s))
  | none =>
    match args with
    | request :: rest =>
      match (idents? rest).bind (spell s) with
      | some op =>
        some (if (sig.rowOf op).shape = .call ∧ (sig.rowOf op).request ≠ Ty.unit ∧
            rowTypeArgs (sig.rowOf op) = some typeArgs then
          (readTerm classes n request).map (rowAnswer (sig.rowOf op) op)
        else .error (.arity s))
      | none =>
        match rest with
        | second :: names =>
          match (idents? names).bind (spell s) with
          | some op =>
            some (if (sig.rowOf op).shape = .tupleCall ∧
                rowTypeArgs (sig.rowOf op) = some typeArgs then
              (readTupleArgs classes n request second).map (rowAnswer (sig.rowOf op) op)
            else .error (.arity s))
          | none => none
        | [] => none
    | [] => none

/-- The ordinary call view of each row's method arguments; row identities and
argument-name hygiene are unchanged. -/
def methodSignature (sig : Signature Op) : Signature Op :=
  { sig with rowOf := fun op => methodArgsRow (sig.rowOf op) }

def addReceiver (sig : Signature Op) (receiver : Term) : Eff Op → Except ReadRefusal (Eff Op)
  | .perform op args =>
    if (sig.rowOf op).shape = .method then
      .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil))))
    else .error (.shape "method row")
  | _ => .error (.shape "method row")

/-- Method arguments use the same three arity readings as ordinary row calls. -/
def readRowMethod (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    (receiver : Expr) (s : String) (typeArgs : List TypeScript.TypeRef) (args : List Expr) :
    Except ReadRefusal (Eff Op) := do
  let recv ← readTerm classes n receiver
  let body ← (readRowCall classes (methodSignature sig) spell n s typeArgs args).getD
    (.error (.unknownHead s))
  addReceiver sig recv body

/-- Methods have their own receiver syntax. Empty generic lists are outside the printed image. -/
def readMethod (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat)
    (x : Expr) : Except ReadRefusal (Eff Op) :=
  match x with
  | .method receiver s args => readRowMethod classes sig spell n receiver s [] args
  | .call (.generic (.member receiver s) (ta :: tas)) args =>
    readRowMethod classes sig spell n receiver s (ta :: tas) args
  | _ => .error (.shape "expression")

/-- The digit a byte spells, `'0'` as `0`. -/
abbrev digitOfByte := Effect4.Data.NatDecimal.digitOfByte

/-- The number a byte string spells in decimal. -/
abbrev decodeBytes := Effect4.Data.NatDecimal.decodeBytes

/-- Decode the two numeric fields; `readKey` checks the complete canonical spelling. -/
def keyFromText (text : String) : ServiceKey :=
  let bytes := text.toByteArray.data.toList.drop 1
  ⟨⟨decodeBytes (bytes.takeWhile (· != 95))⟩,
    ⟨decodeBytes ((bytes.dropWhile (· != 95)).drop 1)⟩⟩

/-- Only the exact printed key is admitted. Identifier, runtime spelling and carrier
must agree; the distinguished scope is represented only by the genuine `Scope.Scope`. -/
def readKey {Op : Type} (sig : Signature Op) : Expr → Except ReadRefusal ServiceKey
  | .ident head =>
    if head = "Scope.Scope" then .ok sig.scopeKey else .error (.shape "service key")
  | .call (.ident head) [.str text] =>
    let key := keyFromText text
    if key ≠ sig.scopeKey ∧ head = "Context.Service" ∧ sig.serviceTy key = none ∧ text = keyText key then
      .ok key
    else .error (.shape "service key")
  | .call (.generic (.ident head) [identity, arg]) [.str text] =>
    let key := keyFromText text
    match sig.serviceTy key with
    | some ty =>
      if key ≠ sig.scopeKey ∧ head = "Context.Service" ∧ identity = .literal (keyText key) ∧
          Effect4.Codegen.Types.ofTy ty = some arg ∧ text = keyText key then
        .ok key
      else .error (.shape "service key")
    | none => .error (.shape "service key")
  | _ => .error (.shape "service key")

/-- The literal domain of `Layer.succeed`, using the ordinary term reader. A literal holds no
record, so it reads under no class. -/
def readLiteral (x : Expr) : Except ReadRefusal Lit := do
  let term ← readTerm [] 0 x
  match term with
  | .lit value => .ok value
  | _ => .error (.shape "literal")

/-! ## The reader: one generic step over the table -/

section TableReader

open Effect4.Codegen.Template (Arg Subst matchT match_below)
open Effect4.Codegen

/-- The capture at hole `i`, with the fact that it is one of `σ`'s (what the recursion's measure
is stated over). -/
def captured : (σ : Subst) → (i : Nat) → Option {a : Arg // (i, a) ∈ σ}
  | [], _ => none
  | (j, a) :: rest, i =>
    if h : j = i then some ⟨a, h ▸ List.mem_cons_self⟩
    else (captured rest i).map fun ⟨b, hb⟩ => ⟨b, List.mem_cons_of_mem _ hb⟩

/-- A refusal with where it happened. `path` is the constructor and argument index at each step
from the root down to the node that refused, outermost first (a list's items are its `cons`
cells: argument `0` the item, `1` the rest). `expected` is set when a reserved head matched no
row: the steps down the nearest row's skeleton to where the tree parts from it, and what the
skeleton has there. The refusal itself stays flat, so nothing that compares refusals moves. -/
structure ReadFailure where
  path : List (String × Nat) := []
  why : ReadRefusal
  expected : Option (List String × String) := none
deriving DecidableEq, Repr

/-- A refusal at the node being read. -/
def ReadFailure.here (why : ReadRefusal) : ReadFailure := { why }

/-- The same failure, seen from the argument `i` of a `ctor` node above it. -/
def ReadFailure.under (ctor : String) (i : Nat) (f : ReadFailure) : ReadFailure :=
  { f with path := (ctor, i) :: f.path }

/-- For a person: `bind.1 > succeed.0: unknownIdent a1`, and what was expected where. -/
def ReadFailure.render (f : ReadFailure) : String :=
  let at_ := " > ".intercalate (f.path.map fun (ctor, i) => ctor ++ "." ++ toString i)
  let why := reprStr f.why
  let expected := match f.expected with
    | some (steps, what) =>
      "; expected " ++ what ++ (if steps.isEmpty then "" else " at " ++ " > ".intercalate steps)
    | none => ""
  (if at_.isEmpty then "" else at_ ++ ": ") ++ why ++ expected

/-- A table that does not fit the constructor declarations (no `build` for what a row read, a
sort no capture fills). It is a defect of the table, never of the tree read. -/
def readDefect : ReadRefusal := .shape "table"

/-- A leaf argument from its capture, by sort, at the depth its row gives it. A scoped fork's
options object carries no `daemon` field: the row's pattern decides it for a plain fork, and
`forkIn` / `forkScoped` fork a daemon at the pin (`internal/effect.ts:5366`, `:5406`). -/
def readLeaf {R : EffFam → Type} (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (d : Nat) (daemon : Bool) :
    ArgSort → Arg → Except ReadRefusal (ArgF Op R)
  | .term, .expr y => (readTerm classes d y).map .term
  | .optTerm, .expr y => (readTerm classes d y).map fun t => .optTerm (some t)
  | .cause, .expr y => (readCause classes d y).map .cause
  | .lit, .expr y => (readLiteral y).map .lit
  | .key, .expr y => (readKey sig y).map .key
  | .forkOptions, .expr y => (readForkOptions daemon y).map .forkOptions
  | .decision, .str t => .ok (.decision (.tag t))
  | .decision, .expr (.str t) => .ok (.decision (.recordTag t))
  | .nat, .int v => if 0 ≤ v then .ok (.nat v.toNat) else .error (.negative v)
  | .path, .expr (.ident s) =>
    match LayerTerm.readRefName s with
    | some target => if LayerTerm.refName target = s then .ok (.path target) else .error (.shape "layer")
    | none => .error (.shape "layer")
  -- no reader of types exists, by design (B19): the annotated loop prints and is not read
  | .optTy, .type _ => .error (.annotation "local const")
  | _, _ => .error (.shape "argument")

/-- The daemon flag a row reads a fork's options under. -/
def rowDaemon (row : Templates.Row) : Bool :=
  match row.fixed.findSome? fun (_, p) => match p with | .daemon b => some b | _ => none with
  | some b => b
  | none => true

/-- One capture as the argument of sort `s`: a child is handed to the recursion with the fact
that it is one of the captures (what the recursion's measure is stated over); anything else goes
through the leaf reader of its sort. -/
def readCapture (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (daemon : Bool) (σ : Subst)
    (child : (fam : EffFam) → Nat → (y : Expr) → (i : Nat) → (i, Arg.expr y) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam))
    (children : (fam : EffFam) → Nat → (ys : List Expr) → (i : Nat) → (i, Arg.exprs ys) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam))
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, Arg.stmts ss) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op .stmts))
    (d : Nat) (s : ArgSort) (i : Nat) :
    (a : Arg) → (i, a) ∈ σ → Except ReadFailure (ArgF Op (EffSelfCarrier Op))
  | .expr y, h =>
    match s with
    | .child fam => (child fam d y i h).map (.child fam)
    | s => (readLeaf classes sig d daemon s (.expr y)).mapError .here
  | .exprs ys, h =>
    match s with
    | .child fam => (children fam d ys i h).map (.child fam)
    | s => (readLeaf classes sig d daemon s (.exprs ys)).mapError .here
  | .stmts body, h =>
    match s with
    | .child .stmts => (block d body i h).map (.child .stmts)
    | s => (readLeaf classes sig d daemon s (.stmts body)).mapError .here
  | .str v, _ => (readLeaf classes sig d daemon s (.str v)).mapError .here
  | .int v, _ => (readLeaf classes sig d daemon s (.int v)).mapError .here
  | .type t, _ => (readLeaf classes sig d daemon s (.type t)).mapError .here

/-- The argument at position `i`, of sort `s`, at the depth its hole is under
(`RowOut.levelAt`, `Templates.argDepth`): supplied when the classifier fixes it, otherwise read
from what the skeleton captured there. -/
def readArg (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (n : Nat) (row : Templates.Row) (σ : Subst)
    (child : (fam : EffFam) → Nat → (y : Expr) → (i : Nat) → (i, Arg.expr y) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam))
    (children : (fam : EffFam) → Nat → (ys : List Expr) → (i : Nat) → (i, Arg.exprs ys) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam))
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, Arg.stmts ss) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op .stmts))
    (s : ArgSort) (i : Nat) : Except ReadFailure (ArgF Op (EffSelfCarrier Op)) :=
  match row.supplied i with
  | some a => .ok a
  | none =>
    match captured σ i with
    | some ⟨a, h⟩ =>
      readCapture classes sig (rowDaemon row) σ child children block
        (Templates.argDepth row.fam s n (row.out.levelAt i)) s i a h
    | none => .error (.here readDefect)

/-- The arguments of a row, in declaration order. A failure below an argument is seen from that
argument of the row's constructor. -/
def readArgs (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (n : Nat) (row : Templates.Row) (σ : Subst)
    (child : (fam : EffFam) → Nat → (y : Expr) → (i : Nat) → (i, Arg.expr y) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam))
    (children : (fam : EffFam) → Nat → (ys : List Expr) → (i : Nat) → (i, Arg.exprs ys) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam))
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, Arg.stmts ss) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op .stmts)) :
    List ArgSort → Nat → Except ReadFailure (List (ArgF Op (EffSelfCarrier Op)))
  | [], _ => .ok []
  | s :: ss, i => do
    let a ← (readArg classes sig n row σ child children block s i).mapError (·.under row.ctor i)
    let rest ← readArgs classes sig n row σ child children block ss (i + 1)
    .ok (a :: rest)

/-- The arguments read select this row: the printer would choose it for them, so what is read
prints back to the tree read. -/
def printedRow (fam : EffFam) (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op)))
    (k : Nat) : Bool :=
  decide (Templates.table.findIdx? (fun r => r.selects fam ctor args) = some k)

/-- What a row accepts of the arguments it read: the printer would choose this row for them
(exactness), and they make a node of the row's constructor. Every row ends here. -/
def buildRow (fam : EffFam) (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op)))
    (k : Nat) : Except ReadFailure (EffSelfCarrier Op fam) :=
  if printedRow fam ctor args k then
    match build fam ctor args with
    | some e => .ok e
    | none => .error (.here readDefect)
  else .error (.here (.shape "not the printed row"))

/-- The reserved names that head a program's printed clause: the heads (`Tpl.head?`) of the
table's program and action rows. A reserved name that heads none of them has no reading in
program position (`Cause.fail` outside a cause, `Layer.merge` outside a layer). -/
def programHeads : List String :=
  Templates.table.filterMap fun row =>
    if row.fam = .eff ∨ row.fam = .action then
      match row.out with
      | .tpl t => t.head?
      | _ => none
    else none

/-- What is not a skeleton, read as the hand fields print it: a bare identifier as a value row,
a call as a call row, a method call as a method row. A reserved head no row matched is refused
by its argument list when it heads a program clause, and by its name otherwise. What it reads is
the operation the row spells, its face (`Signature.face`): the row's call shows no binder term,
and `readPerform` installs the function that follows the call's arguments. -/
def readPerformFace (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
    (n : Nat) (x : Expr) : Except ReadRefusal (Eff Op) :=
  match x with
  | .ident s =>
    match Var.read n s with
    | some _ => .error (.shape "bare binder")
    | none =>
      match headOf s with
      | some .undefined => .error (.shape "bare value")
      | some _ => .error (.unknownHead s)
      | none => readRowValue sig spell s
  | .int k => if 0 ≤ k then .error (.shape "bare value") else .error (.negative k)
  | .bool _ => .error (.shape "bare value")
  | .str _ => .error (.shape "bare value")
  | .call (.ident s) args =>
    match headOf s with
    | some h => if s ∈ programHeads then .error (callRefusal h args) else .error (.unknownHead s)
    | none => (readRowCall classes sig spell n s [] args).getD (.error (.unknownHead s))
  | .call (.generic (.ident s) (ta :: tas)) args =>
    (readRowCall classes sig spell n s (ta :: tas) args).getD (.error (.unknownHead s))
  | _ => readMethod classes sig spell n x

/-- The row call an expression holds before its last argument, and that argument's body, when
the last argument is a function of the current value at level `n`: `(aN) => body`, the binder due
at the node's level, unannotated (`Binders.read n [0]`). The printer writes an operation's
binder term there (`withFunction`, `Codegen/PrintLeaf.lean`). `none` for any other tree. -/
def splitFunction (n : Nat) : Expr → Option (Expr × Expr)
  | .call head args =>
    args.getLast?.bind fun last =>
      (Effect4.Codegen.Binders.read n [0] last).map fun body => (.call head args.dropLast, body)
  | .method receiver name args =>
    args.getLast?.bind fun last =>
      (Effect4.Codegen.Binders.read n [0] last).map fun body =>
        (.method receiver name args.dropLast, body)
  | _ => none

/-- A row call read at its face, with the function that followed its arguments installed as the
operation's binder term (`Signature.withTerm`). An operation that carries no term takes no
function: the call is refused by its row's spelling, as an argument list the row does not
print. -/
def installTerm (sig : Signature Op) (f : Term) : Eff Op → Except ReadRefusal (Eff Op)
  | .perform op r =>
    if (sig.termOf op).isSome then .ok (.perform (sig.withTerm op f) r)
    else .error (.arity (sig.rowOf op).spelling)
  | _ => .error (.shape "operation data")

/-- A row call read at its face with no function after its arguments: an operation that carries
no binder term. A term row called without its function is refused by its spelling, never read
at the face's placeholder term. -/
def termFree (sig : Signature Op) : Eff Op → Except ReadRefusal (Eff Op)
  | .perform op r =>
    if (sig.termOf op).isNone then .ok (.perform op r)
    else .error (.arity (sig.rowOf op).spelling)
  | _ => .error (.shape "operation data")

/-- The row call at a node of level `n`. A call whose last argument is the function of the
current value is a term row's: the call before it is read at its face (`readPerformFace`), the
function's body as a term one level up, where the current value is the binder at `n`
(`ScopedOp`'s convention), and the term is installed in the spelled operation. Any other tree is
read at its face and must name an operation that carries no term. -/
def readPerform (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) (x : Expr) : Except ReadRefusal (Eff Op) :=
  match splitFunction n x with
  | some (call, body) => do
    let face ← readPerformFace classes sig spell n call
    let f ← readTerm classes (n + 1) body
    installTerm sig f face
  | none => (readPerformFace classes sig spell n x).bind (termFree sig)

/-- The refusal of a tree that no row of its family matches, named by the family. -/
def unread : EffFam → ReadRefusal
  | .layer | .layers => .shape "layer"
  | _ => .shape "expression"

/-- A family a transparent row may hand the same expression to: strictly lower. -/
def famRank : EffFam → Nat
  | .eff => 1
  | _ => 0

/-- The name at the head of a tree, as `Tpl.head?` is of a skeleton. -/
def exprHead? : Expr → Option String
  | .ident name => some name
  | .call (.ident name) _ => some name
  | _ => none

/-- Where `x` parts from the nearest row of the families a program is read through: the first
row with `x`'s head. For a refusal's message; it decides nothing. -/
def nearestRow (n : Nat) (x : Expr) : Option (List String × String) :=
  match exprHead? x with
  | none => none
  | some head =>
    Templates.table.findSome? fun row =>
      match row.out with
      | .tpl t => if t.head? = some head then Template.explainT n t x else none
      | _ => none

/-- One row against a tree; `none` when the row does not match. It has no recursion of its own:
the readers of what it captures are handed in, each with the fact that makes the recursion
terminate (a rigid skeleton's captures are strictly inside the tree, `match_below`; a
transparent row hands the SAME tree to a strictly lower family). So what is true of a row is
stated and proved here, once, with the recursion as a hypothesis. -/
def readRow (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op) (fam : EffFam)
    (n : Nat) (x : Expr) (row : Templates.Row) (k : Nat)
    (child : (fam' : EffFam) → Nat → (y : Expr) → sizeOf y < sizeOf x →
      Except ReadFailure (EffSelfCarrier Op fam'))
    (children : (fam' : EffFam) → Nat → (ys : List Expr) → sizeOf ys < sizeOf x →
      Except ReadFailure (EffSelfCarrier Op fam'))
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf x →
      Except ReadFailure (EffSelfCarrier Op .stmts))
    (same : (fam' : EffFam) → famRank fam' < famRank fam → Nat →
      Option (Except ReadFailure (EffSelfCarrier Op fam'))) :
    Option (Except ReadFailure (EffSelfCarrier Op fam)) :=
  if row.fam = fam then
    match row.out with
    | .refuse _ | .stmt _ => none
    -- the row call stands last among the program rows: a tree is one when it is nothing else
    | .rowCall =>
      match fam with
      | .eff => some ((readPerform classes sig spell n x).mapError fun why =>
          { why, expected := nearestRow n x })
      | _ => none
    | .tpl t =>
      match hσ : matchT n t x with
      | none => none
      | some σ =>
        match argSorts fam row.ctor with
        | none => none
        | some sorts =>
          if hr : t.rigid = true then
            some do
              let args ← readArgs classes sig n row σ
                (fun fam' d y i hy => child fam' d y (match_below n t x σ hr hσ (i, .expr y) hy))
                (fun fam' d ys i hy =>
                  children fam' d ys (match_below n t x σ hr hσ (i, .exprs ys) hy))
                (fun d body i hy => block d body (match_below n t x σ hr hσ (i, .stmts body) hy))
                sorts 0
              buildRow fam row.ctor args k
          else
            match sorts with
            | [.child fam'] =>
              if hk : famRank fam' < famRank fam then
                (same fam' hk (Templates.argDepth fam (.child fam') n 0)).map fun r => do
                  let c ← r.mapError (·.under row.ctor 0)
                  buildRow fam row.ctor [.child fam' c] k
              else none
            -- one leaf read of the whole tree, at the depth the printer prints it at
            -- (`Templates.argDepth`), as the child above is handed its depth
            | [sort] =>
              match readLeaf (R := EffSelfCarrier Op) classes sig
                  (Templates.argDepth fam sort n 0) true sort (.expr x) with
              | .ok a => (buildRow fam row.ctor [a] k).toOption.map .ok
              | .error _ => none
            | _ => none
  else none

/-- One statement row against a statement, with the binders its skeleton declares for the
statements after it; `none` when the row does not match. -/
def readStmtRow (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (n : Nat) (s : TypeScript.Stmt) (row : Templates.Row)
    (k : Nat)
    (child : (fam' : EffFam) → Nat → (y : Expr) → sizeOf y < sizeOf s →
      Except ReadFailure (EffSelfCarrier Op fam'))
    (children : (fam' : EffFam) → Nat → (ys : List Expr) → sizeOf ys < sizeOf s →
      Except ReadFailure (EffSelfCarrier Op fam'))
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf s →
      Except ReadFailure (EffSelfCarrier Op .stmts)) :
    Option (Except ReadFailure (Stmt Op × Nat)) :=
  if row.fam = .stmt then
    match row.out with
    | .stmt t =>
      match hσ : Template.matchStmt n t s with
      | none => none
      | some σ =>
        match argSorts .stmt row.ctor with
        | none => none
        | some sorts =>
          some do
            let args ← readArgs classes sig n row σ
              (fun fam' d y i hy =>
                child fam' d y (Template.matchStmt_below n t s σ hσ (i, .expr y) hy))
              (fun fam' d ys i hy =>
                children fam' d ys (Template.matchStmt_below n t s σ hσ (i, .exprs ys) hy))
              (fun d body i hy =>
                block d body (Template.matchStmt_below n t s σ hσ (i, .stmts body) hy))
              sorts 0
            let st ← buildRow .stmt row.ctor args k
            .ok (st, t.declares)
    | _ => none
  else none

mutual
  /-- `readT sig spell fam n x`: the first row of `fam` that reads `x` (`readRow`); `none` when
  no row matches. -/
  def readT (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
      (fam : EffFam) (n : Nat) (x : Expr) : Option (Except ReadFailure (EffSelfCarrier Op fam)) :=
    Templates.table.zipIdx.findSome? fun (row, k) =>
      readRow classes sig spell fam n x row k
        (fun fam' d y _ => (readT classes sig spell fam' d y).getD (.error (.here (unread fam'))))
        (fun fam' d ys _ => readSpine classes sig spell fam' d ys)
        (fun d body _ => readStmts classes sig spell d body)
        (fun fam' _ d => readT classes sig spell fam' d x)
  termination_by (sizeOf x, famRank fam)

  /-- A spine of programs or of layers, item by item. -/
  def readSpine (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
      (fam : EffFam) (n : Nat) (xs : List Expr) : Except ReadFailure (EffSelfCarrier Op fam) :=
    match fam, xs with
    | .effs, [] => .ok .nil
    | .effs, y :: rest => do
      let e ← ((readT classes sig spell .eff n y).getD (.error (.here (unread .eff)))).mapError
        (·.under "cons" 0)
      let es ← (readSpine classes sig spell .effs n rest).mapError (·.under "cons" 1)
      .ok (.cons e es)
    | .layers, [] => .ok .nil
    | .layers, y :: rest => do
      let l ← ((readT classes sig spell .layer n y).getD (.error (.here (unread .layer)))).mapError
        (·.under "cons" 0)
      let ls ← (readSpine classes sig spell .layers n rest).mapError (·.under "cons" 1)
      .ok (.cons l ls)
    | _, _ => .error (.here readDefect)
  termination_by (sizeOf xs, 0)

  /-- The spine of statements: each statement through the first statement row that reads it
  (`readStmtRow`), the rest under the binders that row's skeleton declares, as the printer's
  spine threads them. -/
  def readStmts (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) (stmts : List TypeScript.Stmt) : Except ReadFailure (Stmts Op) :=
    match stmts with
    | [] => .ok .nil
    | s :: rest =>
      let byRow := Templates.table.zipIdx.findSome? fun (row, k) =>
        readStmtRow classes sig n s row k
          (fun fam' d y _ => (readT classes sig spell fam' d y).getD (.error (.here (unread fam'))))
          (fun fam' d ys _ => readSpine classes sig spell fam' d ys)
          (fun d body _ => readStmts classes sig spell d body)
      match byRow with
      | some r => do
        let (st, declared) ← r.mapError (·.under "cons" 0)
        let tail ← (readStmts classes sig spell (n + declared) rest).mapError (·.under "cons" 1)
        .ok (.cons st tail)
      | none => .error ((ReadFailure.here (stmtRefusal s)).under "cons" 0)
  termination_by (sizeOf stmts, 0)
end

/-- A program from a tree, at environment length `n`, under the module's payload classes. -/
def readEffAt (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
    (n : Nat) (x : Expr) : Except ReadFailure (Eff Op) :=
  (readT classes sig spell .eff n x).getD (.error (.here (unread .eff)))

/-- The same with the refusal alone: where it happened is `readEffAt`'s. -/
def readEff (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
    (n : Nat) (x : Expr) : Except ReadRefusal (Eff Op) :=
  (readEffAt classes sig spell n x).mapError (·.why)

/-- A layer from a tree. A layer is closed: its bodies are read at environment length `0`. -/
def readLayerAt (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
    (x : Expr) : Except ReadFailure (LayerTerm Op) :=
  (readT classes sig spell .layer 0 x).getD (.error (.here (unread .layer)))

def readLayer (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op) (spell : String → List String → Option Op)
    (x : Expr) : Except ReadRefusal (LayerTerm Op) :=
  (readLayerAt classes sig spell x).mapError (·.why)

end TableReader

/-- A block's leading class declarations (decisions row 120: the module declares its payload
classes first) and the declarations after them. -/
def splitClasses : List TypeScript.Decl → List TypeScript.ClassDecl × List TypeScript.Decl
  | .classDecl c :: rest => ((splitClasses rest).1.cons c, (splitClasses rest).2)
  | ds => ([], ds)

/-- The payload classes a block declares (`Classes.readClassDecls` of its leading class
declarations), when every one reads back. A tag declared twice reads as its first declaration;
the checked boundary compares the classes with the printer's (`Codegen.envelopeCheck`). -/
def blockClasses (decls : List TypeScript.Decl) : Option Effect4.Codegen.Classes.Classes :=
  Effect4.Codegen.Classes.readClassDecls (splitClasses decls).1

/-- A declaration block back to the program (the host rows slice): its leading class
declarations read as the payload classes the rest is read under (decisions row 120), every
`const L_<path> = <layer>` read as a layer at the path its name carries and put back at that
path (`Refs.lean` `restoreAll`, ancestors first), the last declaration the main program.
The program reconstruction law applies to successfully printed modules under its stated
readability and hoisting premises. This raw reader ignores declaration type annotations,
export flags and the main declaration's name; it is not exact source-module admission.
A class declaration that does not read back returns `shape "class"`; malformed declaration forms,
layer paths and failed restoration return `shape "module"`. -/
def readModule (sig : Signature Op) (spell : String → List String → Option Op)
    (decls : List TypeScript.Decl) : Except ReadRefusal (Eff Op) :=
  match blockClasses decls with
  | none => .error (.shape "class")
  | some classes =>
    match (splitClasses decls).2.getLast?, (splitClasses decls).2.dropLast with
    | some (.const main), layerDecls => do
      let e ← readEff classes sig spell 0 main.value
      let ds ← layerDecls.mapM fun d =>
        match d with
        | .const c =>
          match LayerTerm.readRefName c.name with
          | some t =>
            if LayerTerm.refName t = c.name then do
              let l ← readLayer classes sig spell c.value
              .ok (t, l)
            else .error (.shape "module")
          | none => .error (.shape "module")
        | _ => .error (.shape "module")
      match e.restoreAll ds with
      | some e' => .ok e'
      | none => .error (.shape "module")
    | _, _ => .error (.shape "module")

/-- The reader after the printer: the executed shadow of `read_print`, under the classes the
program's constructions name (`classesOf`, what its module declares; an operation's binder term
is read through `ScopedOp.term?`). The printer's refusal alphabet is not the reader's, so a
printer refusal is reported as the `shape` named `printer`. -/
def roundTrip [ScopedOp Op] (sig : Signature Op) (spell : String → List String → Option Op)
    (n : Nat) (e : Eff Op) : Except ReadRefusal (Eff Op) :=
  match print sig n e with
  | .ok x => readEff (classesOf e) sig spell n x
  | .error _ => .error (.shape "printer")

/-- The program comes back from its own printing: the domain of the round trip, as the round
trip. What it excludes is listed in the module note. -/
def readable [DecidableEq Op] [ScopedOp Op] (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) (e : Eff Op) : Bool :=
  match roundTrip sig spell n e with
  | .ok e' => decide (e' = e)
  | .error _ => false

/-- `readable` is the round trip. -/
theorem roundTrip_eq [DecidableEq Op] [ScopedOp Op] {sig : Signature Op}
    {spell : String → List String → Option Op} {n : Nat} {e : Eff Op}
    (hr : readable sig spell n e = true) : roundTrip sig spell n e = .ok e := by
  unfold readable at hr
  split at hr
  · rename_i e' he
    rw [he, of_decide_eq_true hr]
  · cases hr

/-- The program reads back from whatever the printer prints of it, under a module's payload
classes: the premise the module law composes, stated of any reader. -/
def ReadsBack (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) (e : Eff Op) : Prop :=
  ∀ x, print sig n e = .ok x → readEff classes sig spell n x = .ok e

/-- The same of a layer. -/
def LayerTerm.ReadsBack (classes : Effect4.Codegen.Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (l : LayerTerm Op) : Prop :=
  ∀ x, printLayer sig l = .ok x → readLayer classes sig spell x = .ok l

theorem ReadsBack.of_readable [DecidableEq Op] [ScopedOp Op] {sig : Signature Op}
    {spell : String → List String → Option Op} {n : Nat} {e : Eff Op}
    (hr : readable sig spell n e = true) : ReadsBack (classesOf e) sig spell n e := by
  intro x hp
  have h := roundTrip_eq hr
  unfold roundTrip at h
  rw [hp] at h
  exact h

/-! ## What the printer loses -/

/-- The identifiers an argument list prints as, when every argument prints as one: a
variable as its binder, the unit literal as `undefined`. -/
def Terms.names? : Terms → Option (List String)
  | .nil => some []
  | .cons (.var index) rest => (names? rest).map (Var.name index :: ·)
  | .cons (.lit .unit) rest => (names? rest).map ("undefined" :: ·)
  | .cons _ _ => none

/-- No row of the table reads the head `atom` on these arguments, in either of the two
readings `readRowCall` tries. -/
def noRow (spell : String → List String → Option Op) (atom : String) (args : Terms) : Bool :=
  ((args.names?).bind (spell atom)).isNone &&
    match args with
    | .cons _ rest =>
      ((rest.names?).bind (spell atom)).isNone &&
        match rest with
        | .cons _ names => ((names.names?).bind (spell atom)).isNone
        | .nil => true
    | .nil => true

/-- What the printer keeps of a row's request: nothing on a value row or a `unit` request
(the request must then be exactly the unit literal), the term otherwise. A tuple-call
row keeps a `pair` application of scoped components or a scoped variable; a `pair` whose
printed components spell the saved-variable form `fst(a)`, `snd(a)` reads back as that
variable and is outside the image (source-repairs §18). -/
def tupleRequestReadable (n : Nat) (request : Term) : Bool :=
    match pairArgs? request with
    | some (x, y) =>
      x.scoped n && y.scoped n && (savedVar? (printTerm n x) (printTerm n y)).isNone
    | none =>
      -- the requests whose printed form is one identifier: a binder, or `undefined`
      match request with
      | .var _ => request.scoped n
      | .lit .unit => true
      | _ => false

/-- A sufficient readable-domain condition for service keys: an ordinary key
with a known carrier needs its structural target representation. The distinguished
scope key prints directly as `Scope.Scope`, independently of its carrier. -/
def keyReadable (sig : Signature Op) (key : ServiceKey) : Bool :=
  match sig.serviceTy key with
  | none => true
  | some ty => (Effect4.Codegen.Types.ofTy ty).isSome

/-- The raw printed-image domain includes structural type-argument representability
for call and method rows. Value rows do not print their type arguments. -/
def requestReadable (row : Row) (n : Nat) (request : Term) : Bool :=
  match row.shape with
  | .value => decide (request = .lit .unit)
  | .call =>
    (rowTypeArgs row).isSome &&
      if row.request = Ty.unit then decide (request = .lit .unit) else request.scoped n
  | .tupleCall => (rowTypeArgs row).isSome && tupleRequestReadable n request
  | .method =>
    (rowTypeArgs row).isSome && match pairArgs? request with
    | some (receiver, args) =>
      receiver.scoped n &&
        if (methodArgsRow row).shape = .tupleCall then tupleRequestReadable n args
        else if (methodArgsRow row).request = Ty.unit then decide (args = .lit .unit)
        else args.scoped n
    | none => false

/-- A row's printed head reads back (`printRowHead`): a value row prints none, and another
row's declared type arguments have a legacy spelling (`rowTypeArgs`). A row the printer refuses
by name (`PrintRefusal.typeSpelling`) is outside: `Deferred.make` at an instance other than the
faces' (`NativeOp.deferredTypeArgs`). -/
def rowHeadReadable (row : Row) : Bool :=
  decide (row.shape = .value) || (rowTypeArgs row).isSome

/-- An operation's binder term reads back at a node of level `n` on its row: the term is in
scope one level up (the current value is the binder at `n`, `ScopedOp`'s convention), the
module's classes cover its class constructions, no list fold in it states its accumulator's
type (a stated type is printed and not read), and the row prints a call, which carries the
term's function (`withFunction`). An operation that carries no term reads back. -/
def termReadable (classes : Effect4.Codegen.Classes.Classes) (n : Nat) (row : Row) :
    Option Term → Bool
  | none => true
  | some f =>
    f.scoped (n + 1) && f.covers classes && f.unannotated && !decide (row.shape = .value)

/-! ## What the reader needs of a signature -/

/-- `spell` inverts the row table on (spelling, trailing names) at every row whose head reads
back (`rowHeadReadable`), up to the operation's binder term: it answers the operation's face
(`Signature.face`), since a row's key does not show the term. A value row has no trailing names
(the printer drops them), and no spelling or trailing name is a binder name, `undefined`, or a
reserved head. The last five laws are what a reader needs of an operation's binder term
(`Signature.termOf`, `Signature.withTerm`): the row does not depend on it, and replacing it is
an exact update. A signature with the default hooks, which carries no term, meets each by
computation. -/
structure LawfulSpelling (sig : Signature Op) (spell : String → List String → Option Op) :
    Prop where
  spell_row : ∀ op, sig.dom op = true → rowHeadReadable (sig.rowOf op) = true →
    spell (sig.rowOf op).spelling (sig.rowOf op).trailing = some (sig.face op)
  row_of_spell : ∀ s names op, spell s names = some op →
    (sig.rowOf op).spelling = s ∧ (sig.rowOf op).trailing = names
  value_trailing : ∀ op, (sig.rowOf op).shape = .value → (sig.rowOf op).trailing = []
  spelling_ne_name : ∀ op i, (sig.rowOf op).spelling ≠ Var.name i
  spelling_not_reserved : ∀ op, (sig.rowOf op).spelling ∉ reserved
  trailing_ne_name : ∀ op i, Var.name i ∉ (sig.rowOf op).trailing
  trailing_ne_undefined : ∀ op, "undefined" ∉ (sig.rowOf op).trailing
  /-- An operation's row does not depend on its binder term: the faces print the term as a
  function after the row's call (the state plan's T5). -/
  withTerm_row : ∀ op f, sig.rowOf (sig.withTerm op f) = sig.rowOf op
  /-- Replacing an operation's term installs the term, and an operation that carries none still
  carries none. -/
  termOf_withTerm : ∀ op f,
    (sig.termOf (sig.withTerm op f)).map (·.term) = (sig.termOf op).map fun _ => f
  /-- Replacing an operation's term by itself is the operation. -/
  withTerm_termOf : ∀ op b, sig.termOf op = some b → sig.withTerm op b.term = op
  /-- Replacing the term twice is replacing it once. -/
  withTerm_withTerm : ∀ op f g, sig.withTerm (sig.withTerm op f) g = sig.withTerm op g
  /-- An operation that carries no term is fixed. -/
  withTerm_none : ∀ op f, sig.termOf op = none → sig.withTerm op f = op

/-! ## The native profile

`nativeSpell` inverts `NativeOp.row` on (spelling, trailing names) over one representative per
key (`NativeOp.spelled`): each of the eight read-modify-write rows at its face, whose term the
reader replaces by the function it read (`NativeOp.withTerm`), the two `Scope.make` rows told
apart by the `"parallel"` strategy, and `Deferred.make` as the one instance whose type arguments
the faces spell. `nativeLawful` is the receipt that the native table meets `LawfulSpelling`; the
two theorems specialise to it below. -/

/-- The four table requirements: unique keys, no built-in collision, no dropped
trailing names on a value row, and names outside the reserved/binder alphabets.
Split between the program plane (`Table.lawful`) and the codegen name-safety hygiene (`rowNamesSafe`). -/
def LawfulTable (table : RowTable) : Bool :=
  Table.lawful table && table.all rowNamesSafe

/-- Built-ins are checked first; the external key identifies its position in the
supplied table. No external index is recovered by parsing an identifier. -/
def nativeSpell (table : RowTable := []) (s : String) (names : List String) : Option NativeOp :=
  match NativeOp.spelled.find? (fun op => decide (rowKey op.row = (s, names))) with
  | some op => some op
  | none => (table.findIdx? (fun row => decide (rowKey row = (s, names)))).map NativeOp.external


end Effect4.Program
