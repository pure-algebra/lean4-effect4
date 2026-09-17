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
causes, keys, fork options, literals, rows) are below with their round trips.

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

mutual
  /-- A pure term back from its printing: a binder as its variable, `undefined` as the unit
  literal, a non-negative integer, a Boolean, a string, and `atom(args)` as the application.
  Atoms are not checked against `reserved` in term position; the printer never puts a
  combinator there. -/
  def readTerm (n : Nat) (x : Expr) : Except ReadRefusal Term :=
    match x with
    | .ident s =>
      match Var.read n s with
      | some i => .ok (.var i)
      | none => if s = "undefined" then .ok (.lit .unit) else .error (.unknownIdent s)
    | .int k => if 0 ≤ k then .ok (.lit (.nat k.toNat)) else .error (.negative k)
    | .bool b => .ok (.lit (.bool b))
    | .str s => .ok (.lit (.str s))
    | .call (.ident atom) args => (readTerms n args).map (.app atom)
    | _ => .error (.shape "term")
  termination_by structural x

  /-- An argument list, in order. -/
  def readTerms (n : Nat) (xs : List Expr) : Except ReadRefusal Terms :=
    match xs with
    | [] => .ok .nil
    | x :: rest => do
      let t ← readTerm n x
      let ts ← readTerms n rest
      .ok (.cons t ts)
  termination_by structural xs
end

/-- A cause back from the public `Cause` constructors the printer spells. -/
def readCause (n : Nat) (x : Expr) : Except ReadRefusal CauseTerm :=
  match x with
  | .call (.ident s) args =>
    match headOf s, args with
    | some .causeFail, [e] => (readTerm n e).map .fail
    | some .causeDie, [d] => (readTerm n d).map .die
    | some .causeInterrupt, [] => .ok (.interrupt none)
    | some .causeInterrupt, [who] => (readTerm n who).map fun w => .interrupt (some w)
    | some .causeCombine, [l, r] => do
      let a ← readCause n l
      let b ← readCause n r
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
def readTupleArgs (n : Nat) (x y : Expr) : Except ReadRefusal Term :=
  match savedVar? x y with
  | some v => readTerm n (.ident v)
  | none => do
    let a ← readTerm n x
    let b ← readTerm n y
    .ok (.app "pair" (.cons a (.cons b .nil)))

/-- A call as a call row; `none` when no row of the table has this head and argument
shape, so the caller may read an atom application instead. A call row's argument list is
the trailing names alone on a `unit` request, and the request followed by the trailing
names otherwise; a tuple-call row's is its two request arguments followed by the trailing
names. The three readings are tried in that order, and `LawfulSpelling` is what makes at
most one succeed. -/
def readRowCall (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
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
          (readTerm n request).map (rowAnswer (sig.rowOf op) op)
        else .error (.arity s))
      | none =>
        match rest with
        | second :: names =>
          match (idents? names).bind (spell s) with
          | some op =>
            some (if (sig.rowOf op).shape = .tupleCall ∧
                rowTypeArgs (sig.rowOf op) = some typeArgs then
              (readTupleArgs n request second).map (rowAnswer (sig.rowOf op) op)
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
def readRowMethod (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (receiver : Expr) (s : String) (typeArgs : List TypeScript.TypeRef) (args : List Expr) :
    Except ReadRefusal (Eff Op) := do
  let recv ← readTerm n receiver
  let body ← (readRowCall (methodSignature sig) spell n s typeArgs args).getD
    (.error (.unknownHead s))
  addReceiver sig recv body

/-- Methods have their own receiver syntax. Empty generic lists are outside the printed image. -/
def readMethod (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (x : Expr) : Except ReadRefusal (Eff Op) :=
  match x with
  | .method receiver s args => readRowMethod sig spell n receiver s [] args
  | .call (.generic (.member receiver s) (ta :: tas)) args =>
    readRowMethod sig spell n receiver s (ta :: tas) args
  | _ => .error (.shape "expression")

/-- The digit a byte spells, `'0'` as `0`. -/
def digitOfByte (b : UInt8) : Nat := b.toNat - 48

/-- The number a byte string spells in decimal. -/
def decodeBytes (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 10 + digitOfByte b) 0

/-- Decode the two numeric fields; `readKey` checks the complete canonical spelling. -/
def keyFromText (text : String) : ServiceKey :=
  let bytes := text.toByteArray.data.toList.drop 1
  ⟨⟨decodeBytes (bytes.takeWhile (· != 95))⟩,
    ⟨decodeBytes ((bytes.dropWhile (· != 95)).drop 1)⟩⟩

def keyText (key : ServiceKey) : String :=
  "k" ++ toString key.name.value ++ "_" ++ toString key.service.value

/-- Only the exact printed key is admitted, including its optional type argument. -/
def readKey {Op : Type} (sig : Signature Op) : Expr → Except ReadRefusal ServiceKey
  | .call (.ident head) [.str text] =>
    let key := keyFromText text
    if head = "Context.Service" ∧ sig.serviceTy key = none ∧ text = keyText key then
      .ok key
    else .error (.shape "service key")
  | .call (.generic (.ident head) [arg]) [.str text] =>
    let key := keyFromText text
    match sig.serviceTy key with
    | some ty =>
      if head = "Context.Service" ∧ Effect4.Codegen.Types.ofTy ty = some arg ∧ text = keyText key then
        .ok key
      else .error (.shape "service key")
    | none => .error (.shape "service key")
  | _ => .error (.shape "service key")

/-- The literal domain of `Layer.succeed`, using the ordinary term reader. -/
def readLiteral (x : Expr) : Except ReadRefusal Lit := do
  let term ← readTerm 0 x
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

/-- A table that does not fit the constructor declarations (no `build` for what a row read, a
sort no capture fills). It is a defect of the table, never of the tree read. -/
def readDefect : ReadRefusal := .shape "table"

/-- A leaf argument from its capture, by sort, at the depth its row gives it. A scoped fork's
options object carries no `daemon` field: the row's pattern decides it for a plain fork, and
`forkIn` / `forkScoped` fork a daemon at the pin (`internal/effect.ts:5366`, `:5406`). -/
def readLeaf {R : EffFam → Type} (sig : Signature Op) (d : Nat) (daemon : Bool) :
    ArgSort → Arg → Except ReadRefusal (ArgF Op R)
  | .term, .expr y => (readTerm d y).map .term
  | .optTerm, .expr y => (readTerm d y).map fun t => .optTerm (some t)
  | .cause, .expr y => (readCause d y).map .cause
  | .lit, .expr y => (readLiteral y).map .lit
  | .key, .expr y => (readKey sig y).map .key
  | .forkOptions, .expr y => (readForkOptions daemon y).map .forkOptions
  | .decision, .str t => .ok (.decision (.tag t))
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

/-- The arguments of a row from what its skeleton captured, in declaration order, each at the
depth its hole is under (`Template.levelAt`). An argument the classifier determines is supplied; a child is handed to the recursion with the fact that it
is one of the captures; a leaf goes through its own reader. -/
def readArgs (sig : Signature Op) (n : Nat) (row : Templates.Row) (t : Template.Tpl) (σ : Subst)
    (child : (fam : EffFam) → Nat → (y : Expr) → (i : Nat) → (i, Arg.expr y) ∈ σ →
      Except ReadRefusal (EffSelfCarrier Op fam))
    (children : (fam : EffFam) → Nat → (ys : List Expr) → (i : Nat) → (i, Arg.exprs ys) ∈ σ →
      Except ReadRefusal (EffSelfCarrier Op fam)) :
    List ArgSort → Nat → Except ReadRefusal (List (ArgF Op (EffSelfCarrier Op)))
  | [], _ => .ok []
  | s :: ss, i => do
    let d := Templates.argDepth s n (Template.levelAt t i)
    let a ← match (row.fixed.find? (·.1 == i)).bind (·.2.supplies) with
      | some a => .ok a
      | none => match s, captured σ i with
        | .child fam, some ⟨.expr y, h⟩ => (child fam d y i h).map (.child fam)
        | .child fam, some ⟨.exprs ys, h⟩ => (children fam d ys i h).map (.child fam)
        | s, some ⟨a, _⟩ => readLeaf sig d (rowDaemon row) s a
        | _, none => .error readDefect
    let rest ← readArgs sig n row t σ child children ss (i + 1)
    .ok (a :: rest)

/-- The reserved names that head a program's printed clause: the heads of the table's program
and action rows, and the generator. A reserved name that heads none of them has no reading in
program position (`Cause.fail` outside a cause, `Layer.merge` outside a layer). -/
def programHeads : List String :=
  Templates.genHead :: Templates.table.filterMap fun row =>
    if row.fam = .eff ∨ row.fam = .action then
      match row.out with
      | .tpl (.call (.ident s) _) => some s
      | .tpl (.callSpread (.ident s) _) => some s
      | _ => none
    else none

/-- What is not a skeleton, read as the hand fields print it: a bare identifier as a value row,
a call as a call row, a method call as a method row. A reserved head no row matched is refused
by its argument list when it heads a program clause, and by its name otherwise. -/
def readPerform (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (x : Expr) : Except ReadRefusal (Eff Op) :=
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
    | none => (readRowCall sig spell n s [] args).getD (.error (.unknownHead s))
  | .call (.generic (.ident s) (ta :: tas)) args =>
    (readRowCall sig spell n s (ta :: tas) args).getD (.error (.unknownHead s))
  | _ => readMethod sig spell n x

/-- The refusal of a tree that no row of its family matches, named by the family. -/
def unread : EffFam → ReadRefusal
  | .layer | .layers => .shape "layer"
  | _ => .shape "expression"

/-- A family a transparent row may hand the same expression to: strictly lower. -/
def famRank : EffFam → Nat
  | .eff => 1
  | _ => 0

mutual
  /-- `readT sig spell fam n x`: the first row of `fam` whose skeleton matches `x`, its
  arguments read; `none` when no row matches. A transparent row (a bare hole: `withFiber` over
  its action) hands the same expression to its child's family and matches when that does. For a
  program, what no row matches is a generator or a row call. -/
  def readT (sig : Signature Op) (spell : String → List String → Option Op) (fam : EffFam)
      (n : Nat) (x : Expr) : Option (Except ReadRefusal (EffSelfCarrier Op fam)) :=
    let byRow := Templates.table.zipIdx.findSome? fun (row, k) =>
      if row.fam = fam then
        match row.out with
        | .refuse _ => none
        | .tpl t =>
          match hσ : matchT n t x with
          | none => none
          | some σ =>
            match argSorts fam row.ctor with
            | none => none
            | some sorts =>
              if hr : t.rigid = true then
                some do
                  let args ← readArgs sig n row t σ
                    (fun fam' d y i hy =>
                      have : sizeOf y < sizeOf x := match_below n t x σ hr hσ (i, .expr y) hy
                      (readT sig spell fam' d y).getD (.error (unread fam')))
                    (fun fam' d ys i hy =>
                      have : sizeOf ys < sizeOf x := match_below n t x σ hr hσ (i, .exprs ys) hy
                      readSpine sig spell fam' d ys)
                    sorts 0
                  -- exactness: the printer would choose this row for what was read
                  if Templates.table.findIdx? (fun r => r.selects fam row.ctor args) = some k then
                    match build fam row.ctor args with
                    | some e => .ok e
                    | none => .error readDefect
                  else .error (.shape "not the printed row")
              else
                match sorts with
                | [.child fam'] =>
                  if _hk : famRank fam' < famRank fam then
                    (readT sig spell fam' (Templates.argDepth (.child fam') n 0) x).map fun r => do
                      let c ← r
                      match build fam row.ctor [.child fam' c] with
                      | some e => .ok e
                      | none => .error readDefect
                  else none
                | [sort] =>
                  match readLeaf (R := EffSelfCarrier Op) sig n true sort (.expr x) with
                  | .ok a => (build fam row.ctor [a]).map .ok
                  | .error _ => none
                | _ => none
      else none
    match byRow with
    | some r => some r
    | none =>
      match fam with
      | .eff => some (
          match x with
          | .call (.ident s) [.generator body] =>
            if s = Templates.genHead then (readStmts sig spell n body).map .gen
            else readPerform sig spell n x
          | _ => readPerform sig spell n x)
      | _ => none
  termination_by (sizeOf x, famRank fam)

  /-- A spine of programs or of layers, item by item. -/
  def readSpine (sig : Signature Op) (spell : String → List String → Option Op) (fam : EffFam)
      (n : Nat) (xs : List Expr) : Except ReadRefusal (EffSelfCarrier Op fam) :=
    match fam, xs with
    | .effs, [] => .ok .nil
    | .effs, y :: rest => do
      let e ← (readT sig spell .eff n y).getD (.error (unread .eff))
      let es ← readSpine sig spell .effs n rest
      .ok (.cons e es)
    | .layers, [] => .ok .nil
    | .layers, y :: rest => do
      let l ← (readT sig spell .layer n y).getD (.error (unread .layer))
      let ls ← readSpine sig spell .layers n rest
      .ok (.cons l ls)
    | _, _ => .error readDefect
  termination_by (sizeOf xs, 0)

  /-- A generator body, statement by statement, with the binder counts of the printer. -/
  def readStmts (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
      (stmts : List TypeScript.Stmt) : Except ReadRefusal (Stmts Op) :=
    match stmts with
    | [] => .ok .nil
    | .constYield x value none :: rest =>
      if x = Var.name n then do
        let e ← (readT sig spell .eff n value).getD (.error (.shape "expression"))
        let tail ← readStmts sig spell (n + 1) rest
        .ok (.cons (.bindYield e) tail)
      else .error (.binder (Var.name n))
    | .yieldDiscard value :: rest => do
      let e ← (readT sig spell .eff n value).getD (.error (.shape "expression"))
      let tail ← readStmts sig spell n rest
      .ok (.cons (.yieldDiscard e) tail)
    | .ret value :: rest => do
      let v ← readTerm n value
      let tail ← readStmts sig spell n rest
      .ok (.cons (.ret v) tail)
    | .ifElse test thenB elseB :: rest => do
      let t ← readTerm n test
      let a ← readStmts sig spell n thenB
      let b ← readStmts sig spell n elseB
      let tail ← readStmts sig spell n rest
      .ok (.cons (.ifElse t a b) tail)
    | .whileTrue none body :: rest => do
      let b ← readStmts sig spell n body
      let tail ← readStmts sig spell n rest
      .ok (.cons (.whileTrue b) tail)
    | .breakTo none :: rest => do
      let tail ← readStmts sig spell n rest
      .ok (.cons .breakLoop tail)
    | stmt :: _ => .error (stmtRefusal stmt)
  termination_by (sizeOf stmts, 0)
end

/-- A program from a tree, at environment length `n`. -/
def readEff (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (x : Expr) : Except ReadRefusal (Eff Op) :=
  (readT sig spell .eff n x).getD (.error (unread .eff))

/-- A layer from a tree. A layer is closed: its bodies are read at environment length `0`. -/
def readLayer (sig : Signature Op) (spell : String → List String → Option Op)
    (x : Expr) : Except ReadRefusal (LayerTerm Op) :=
  (readT sig spell .layer 0 x).getD (.error (unread .layer))

end TableReader

/-- A declaration block back to the program (the host rows slice): every
`const L_<path> = <layer>` read as a layer at the path its name carries and put back at that
path (`Refs.lean` `restoreAll`, ancestors first), the last declaration the main program.
The program reconstruction law applies to successfully printed modules under its stated
readability and hoisting premises. This raw reader ignores declaration type annotations,
export flags and the main declaration's name; it is not exact source-module admission.
Malformed declaration forms, layer paths and failed restoration return `shape "module"`. -/
def readModule (sig : Signature Op) (spell : String → List String → Option Op)
    (decls : List TypeScript.Decl) : Except ReadRefusal (Eff Op) :=
  match decls.getLast?, decls.dropLast with
  | some (.const main), layerDecls => do
    let e ← readEff sig spell 0 main.value
    let ds ← layerDecls.mapM fun d =>
      match d with
      | .const c =>
        match LayerTerm.readRefName c.name with
        | some t =>
          if LayerTerm.refName t = c.name then do
            let l ← readLayer sig spell c.value
            .ok (t, l)
          else .error (.shape "module")
        | none => .error (.shape "module")
      | _ => .error (.shape "module")
    match e.restoreAll ds with
    | some e' => .ok e'
    | none => .error (.shape "module")
  | _, _ => .error (.shape "module")

/-- The reader after the printer: the executed shadow of `read_print`. The printer's refusal
alphabet is not the reader's, so a printer refusal is reported as the `shape` named `printer`. -/
def roundTrip (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (e : Eff Op) : Except ReadRefusal (Eff Op) :=
  match print sig n e with
  | .ok x => readEff sig spell n x
  | .error _ => .error (.shape "printer")

/-- The program comes back from its own printing: the domain of the round trip, as the round
trip. What it excludes is listed in the module note. -/
def readable [DecidableEq Op] (sig : Signature Op) (spell : String → List String → Option Op)
    (n : Nat) (e : Eff Op) : Bool :=
  match roundTrip sig spell n e with
  | .ok e' => decide (e' = e)
  | .error _ => false

/-- `readable` is the round trip. -/
theorem roundTrip_eq [DecidableEq Op] {sig : Signature Op}
    {spell : String → List String → Option Op} {n : Nat} {e : Eff Op}
    (hr : readable sig spell n e = true) : roundTrip sig spell n e = .ok e := by
  unfold readable at hr
  split at hr
  · rename_i e' he
    rw [he, of_decide_eq_true hr]
  · cases hr

/-- The program reads back from whatever the printer prints of it: the premise the module law
composes, stated of any reader. -/
def ReadsBack (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (e : Eff Op) : Prop :=
  ∀ x, print sig n e = .ok x → readEff sig spell n x = .ok e

/-- The same of a layer. -/
def LayerTerm.ReadsBack (sig : Signature Op) (spell : String → List String → Option Op)
    (l : LayerTerm Op) : Prop :=
  ∀ x, printLayer sig l = .ok x → readLayer sig spell x = .ok l

theorem ReadsBack.of_readable [DecidableEq Op] {sig : Signature Op}
    {spell : String → List String → Option Op} {n : Nat} {e : Eff Op}
    (hr : readable sig spell n e = true) : ReadsBack sig spell n e := by
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
    | some (x, y) => x.scoped n && y.scoped n && (savedVar? (printTerm x) (printTerm y)).isNone
    | none =>
      -- the requests whose printed form is one identifier: a binder, or `undefined`
      match request with
      | .var _ => request.scoped n
      | .lit .unit => true
      | _ => false

/-- A service key can be printed exactly when its optional signature type has a
structural target representation. This premise replaces the old total string spelling. -/
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

/-! ## What the reader needs of a signature -/

/-- `spell` inverts the row table on (spelling, trailing names), a value row has no trailing
names (the printer drops them), and no spelling or trailing name is a binder name,
`undefined`, or a reserved head. -/
structure LawfulSpelling (sig : Signature Op) (spell : String → List String → Option Op) :
    Prop where
  spell_row : ∀ op, sig.dom op = true →
    spell (sig.rowOf op).spelling (sig.rowOf op).trailing = some op
  row_of_spell : ∀ s names op, spell s names = some op →
    (sig.rowOf op).spelling = s ∧ (sig.rowOf op).trailing = names
  value_trailing : ∀ op, (sig.rowOf op).shape = .value → (sig.rowOf op).trailing = []
  spelling_ne_name : ∀ op i, (sig.rowOf op).spelling ≠ Var.name i
  spelling_not_reserved : ∀ op, (sig.rowOf op).spelling ∉ reserved
  trailing_ne_name : ∀ op i, Var.name i ∉ (sig.rowOf op).trailing
  trailing_ne_undefined : ∀ op, "undefined" ∉ (sig.rowOf op).trailing

/-! ## Receipts: what the reader needs of `Except` -/

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem map_ok {ε α β : Type} (f : α → β) (a : α) :
    (Except.ok a : Except ε α).map f = .ok (f a) := rfl

theorem bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [Bind.bind, Except.bind]

theorem map_eq_ok {ε α β : Type} {m : Except ε α} {f : α → β} {b : β} :
    m.map f = .ok b ↔ ∃ a, m = .ok a ∧ f a = b := by
  cases m <;> simp [Except.map]

/-! ## Binders are injective

`Var.name i = "a" ++ Nat.repr i`, and `Nat.repr` is `String.ofList` of the decimal digits.
The string layer's injectivity lemmas reach `Classical.choice` on this toolchain (they go
through `String.toList`), so injectivity is taken from the bytes instead: the UTF-8 bytes of
a decimal string are its digits, and `decodeBytes` reads the number back. -/

theorem decodeBytes_append (bs : List UInt8) (b : UInt8) :
    decodeBytes (bs ++ [b]) = decodeBytes bs * 10 + digitOfByte b := by
  simp [decodeBytes, List.foldl_append]

theorem utf8_digitChar : ∀ m, m < 10 →
    String.utf8EncodeChar (Nat.digitChar m) = [UInt8.ofNat (48 + m)] := by decide

theorem digitOfByte_digit : ∀ m, m < 10 → digitOfByte (UInt8.ofNat (48 + m)) = m := by decide

theorem toDigitsCore_append (fuel : Nat) : ∀ (n : Nat) (ds : List Char), n < fuel →
    Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds := by
  induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
    intro n ds hn
    simp only [Nat.toDigitsCore]
    by_cases h0 : n / 10 = 0
    · simp [h0]
    · simp only [h0, if_false]
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) (by omega),
        ih (n / 10) [Nat.digitChar (n % 10)] (by omega), List.append_assoc]
      rfl

theorem decodeBytes_toDigitsCore (fuel : Nat) : ∀ n, n < fuel →
    decodeBytes ((Nat.toDigitsCore 10 fuel n []).flatMap String.utf8EncodeChar) = n := by
  induction fuel with
  | zero => intro n h; omega
  | succ fuel ih =>
    intro n hn
    have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
    simp only [Nat.toDigitsCore]
    by_cases h0 : n / 10 = 0
    · simp only [h0, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        utf8_digitChar _ hm]
      simp only [decodeBytes, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add,
        digitOfByte_digit _ hm]
      omega
    · simp only [h0, if_false]
      rw [toDigitsCore_append fuel (n / 10) [Nat.digitChar (n % 10)] (by omega),
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        utf8_digitChar _ hm, decodeBytes_append, ih (n / 10) (by omega), digitOfByte_digit _ hm]
      omega

theorem decodeBytes_repr (n : Nat) : decodeBytes (Nat.repr n).toByteArray.data.toList = n := by
  rw [Nat.repr, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    Nat.toDigits]
  exact decodeBytes_toDigitsCore (n + 1) n (Nat.lt_succ_self n)

theorem readKey_exact {Op : Type} {sig : Signature Op} {x : Expr} {key : ServiceKey}
    (h : readKey sig x = .ok key) : printKey sig key = .ok x := by
  unfold readKey at h
  split at h
  · dsimp only at h
    split at h
    · rename_i heq
      cases h
      simp only [printKey, heq.2.1, ok_bind, heq.1, Except.ok.injEq,
        Expr.call.injEq, List.cons.injEq, Expr.str.injEq, and_true, true_and]
      exact heq.2.2.symm
    · cases h
  · dsimp only at h
    split at h
    · rename_i ty hty
      split at h
      · rename_i heq
        cases h
        simp only [printKey, hty, heq.2.1, ok_bind, heq.1, Except.ok.injEq,
          Expr.call.injEq, List.cons.injEq, Expr.str.injEq, and_true, true_and]
        exact heq.2.2.symm
      · cases h
    · cases h
  · cases h

private theorem repr_no_separator (n : Nat) :
    ∀ b ∈ (Nat.repr n).toByteArray.data.toList, (b != (95 : UInt8)) = true := by
  rw [Nat.repr, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    Nat.toDigits]
  suffices h : ∀ fuel n ds, n < fuel →
      (∀ c ∈ ds, ∀ b ∈ String.utf8EncodeChar c, (b != (95 : UInt8)) = true) →
      ∀ b ∈ (Nat.toDigitsCore 10 fuel n ds).flatMap String.utf8EncodeChar,
        (b != (95 : UInt8)) = true from h (n + 1) n [] (Nat.lt_succ_self n) (by simp)
  intro fuel
  induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
    intro n ds hn hds
    have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
    have hd : ∀ b ∈ String.utf8EncodeChar (Nat.digitChar (n % 10)),
        (b != (95 : UInt8)) = true := by
      rw [utf8_digitChar _ hm]
      have : ∀ m, m < 10 → ((UInt8.ofNat (48 + m)) != (95 : UInt8)) = true := by decide
      simp only [List.mem_singleton]
      intro b hb
      subst b
      exact this _ hm
    have hcons : ∀ c ∈ Nat.digitChar (n % 10) :: ds,
        ∀ b ∈ String.utf8EncodeChar c, (b != (95 : UInt8)) = true := by
      intro c hc
      cases List.mem_cons.mp hc with
      | inl h => subst c; exact hd
      | inr h => exact hds c h
    rw [Nat.toDigitsCore]
    split
    · intro b hb
      obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
      exact hcons c hc b hb
    · exact ih (n / 10) _ (by omega) hcons

private theorem split_separator (xs ys : List UInt8)
    (h : ∀ b ∈ xs, (b != (95 : UInt8)) = true) :
    (xs ++ 95 :: ys).takeWhile (· != 95) = xs ∧
      (xs ++ 95 :: ys).dropWhile (· != 95) = 95 :: ys := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    have hb := h b (List.mem_cons_self)
    have hbs : ∀ c ∈ bs, (c != (95 : UInt8)) = true :=
      fun c hc => h c (List.mem_cons_of_mem b hc)
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
      hb, if_true, (ih hbs).1, (ih hbs).2, and_self]

theorem keyFromText_print (name service : Nat) :
    keyFromText ("k" ++ toString name ++ "_" ++ toString service) = ⟨⟨name⟩, ⟨service⟩⟩ := by
  have hk : "k".toByteArray.data.toList = [107] := by decide
  have hs : "_".toByteArray.data.toList = [95] := by decide
  simp only [keyFromText, String.toByteArray_append, ByteArray.data_append,
    Array.toList_append, hk, hs, List.append_assoc, List.cons_append,
    List.nil_append, List.drop_succ_cons, List.drop_zero]
  change ServiceKey.mk
    ⟨decodeBytes (((Nat.repr name).toByteArray.data.toList ++
      95 :: (Nat.repr service).toByteArray.data.toList).takeWhile (· != 95))⟩
    ⟨decodeBytes ((((Nat.repr name).toByteArray.data.toList ++
      95 :: (Nat.repr service).toByteArray.data.toList).dropWhile (· != 95)).drop 1)⟩ = _
  rw [(split_separator _ _ (repr_no_separator name)).1,
    (split_separator _ _ (repr_no_separator name)).2]
  simp only [List.drop_succ_cons, List.drop_zero, decodeBytes_repr]


/-- The successful structural key image reads back. Unsupported legacy type text
now refuses printing, so success is explicit instead of assuming a total string printer. -/
theorem readKey_printKey {Op : Type} (sig : Signature Op) (key : ServiceKey)
    {x : Expr} (hp : printKey sig key = .ok x) : readKey sig x = .ok key := by
  obtain ⟨⟨name⟩, ⟨service⟩⟩ := key
  cases ht : sig.serviceTy ⟨⟨name⟩, ⟨service⟩⟩ with
  | none =>
    simp only [printKey, ht, ok_bind, Except.ok.injEq] at hp
    subst x
    simp only [readKey, keyFromText_print, ht, keyText, and_self, if_true]
  | some ty =>
    cases hty : Effect4.Codegen.Types.ofTy ty with
    | none => simp [printKey, ht, hty, bind_eq_ok] at hp
    | some target =>
      simp only [printKey, ht, hty, ok_bind, Except.ok.injEq] at hp
      subst x
      simp only [readKey, keyFromText_print, ht, hty, keyText, and_self, if_true]

theorem printKey_readable (sig : Signature Op) (key : ServiceKey)
    (hr : keyReadable sig key = true) : ∃ x, printKey sig key = .ok x := by
  cases ht : sig.serviceTy key with
  | none => exact ⟨_, by simp only [printKey, ht, ok_bind]; rfl⟩
  | some ty =>
    simp only [keyReadable, ht, Option.isSome_iff_exists] at hr
    obtain ⟨target, htarget⟩ := hr
    exact ⟨_, by simp only [printKey, ht, htarget, ok_bind]; rfl⟩

theorem repr_inj {a b : Nat} (h : Nat.repr a = Nat.repr b) : a = b := by
  have := congrArg (fun s => decodeBytes s.toByteArray.data.toList) h
  simpa [decodeBytes_repr] using this

theorem Var.name_inj {i j : Nat} (h : Var.name i = Var.name j) : i = j :=
  repr_inj (String.append_right_inj _ |>.mp h)

theorem Var.name_head (i : Nat) : (Var.name i).toByteArray.data.toList.head? = some 97 := by
  have ha : "a".toByteArray.data.toList = [97] := by decide
  rw [Var.name, String.toByteArray_append, ByteArray.data_append, Array.toList_append, ha]
  rfl

/-- A string whose first byte is not `'a'` is no binder name. -/
theorem Var.name_ne {s : String} (hs : s.toByteArray.data.toList.head? ≠ some 97) (i : Nat) :
    Var.name i ≠ s := fun h => hs (h ▸ Var.name_head i)

theorem Var.name_ne_undefined (i : Nat) : Var.name i ≠ "undefined" := Var.name_ne (by decide) i

theorem Var.name_ne_fiberId (i : Nat) : Var.name i ≠ "Effect.fiberId" :=
  Var.name_ne (by decide) i

theorem Var.read_exact : ∀ {n : Nat} {s : String} {i : Nat},
    Var.read n s = some i → s = Var.name i ∧ i < n
  | 0, _, _, h => by simp [Var.read] at h
  | n + 1, s, i, h => by
    simp only [Var.read] at h
    split at h
    · rename_i heq; cases h; exact ⟨heq.symm, Nat.lt_succ_self _⟩
    · obtain ⟨hs, hi⟩ := Var.read_exact h; exact ⟨hs, Nat.lt_succ_of_lt hi⟩

theorem Var.read_name : ∀ {n i : Nat}, i < n → Var.read n (Var.name i) = some i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [Var.read]
    split
    · rename_i heq; rw [Var.name_inj heq]
    · rename_i hne
      have : i ≠ n := fun e => hne (by rw [e])
      exact Var.read_name (by omega)

theorem Var.read_none : ∀ {n : Nat} {s : String}, (∀ i, Var.name i ≠ s) → Var.read n s = none
  | 0, _, _ => rfl
  | n + 1, s, h => by simp only [Var.read]; rw [if_neg (h n)]; exact Var.read_none h

/-! ## Terms round-trip -/

mutual
  theorem readTerm_printTerm {n : Nat} (t : Term) (h : Term.scoped n t = true) :
      readTerm n (printTerm t) = .ok t :=
    match t, h with
    | .var i, h => by
      simp only [Term.scoped, decide_eq_true_eq] at h
      simp [printTerm, readTerm, Var.read_name h]
    | .lit .unit, _ => by
      simp [printTerm, printLit, readTerm, Var.read_none Var.name_ne_undefined]
    | .lit (.nat k), _ => by simp [printTerm, printLit, readTerm]
    | .lit (.bool b), _ => by simp [printTerm, printLit, readTerm]
    | .lit (.str s), _ => by simp [printTerm, printLit, readTerm]
    | .app atom args, h => by
      simp only [Term.scoped] at h
      simp [printTerm, readTerm, readTerms_printTerms args h]
  termination_by structural t

  theorem readTerms_printTerms {n : Nat} (ts : Terms) (h : Terms.scoped n ts = true) :
      readTerms n (printTerms ts) = .ok ts :=
    match ts, h with
    | .nil, _ => by simp [printTerms, readTerms]
    | .cons t ts, h => by
      simp only [Terms.scoped, Bool.and_eq_true] at h
      simp [printTerms, readTerms, readTerm_printTerm t h.1, readTerms_printTerms ts h.2]
  termination_by structural ts
end

mutual
  theorem readTerm_exact {n : Nat} (x : Expr) {t : Term} (h : readTerm n x = .ok t) :
      printTerm t = x :=
    match x, h with
    | .ident s, h => by
      simp only [readTerm] at h
      split at h
      · rename_i i hi; cases h; obtain ⟨hs, _⟩ := Var.read_exact hi; simp [printTerm, hs]
      · split at h
        · cases h; rename_i hs; simp [printTerm, printLit, hs]
        · cases h
    | .int k, h => by
      simp only [readTerm] at h
      split at h
      · cases h; rename_i hk; simp [printTerm, printLit, Int.toNat_of_nonneg hk]
      · cases h
    | .bool b, h => by simp [readTerm] at h; subst h; rfl
    | .str s, h => by simp [readTerm] at h; subst h; rfl
    | .call (.ident atom) args, h => by
      simp only [readTerm, map_eq_ok] at h
      obtain ⟨ts, hts, rfl⟩ := h
      simp [printTerm, readTerms_exact args hts]
    | .call (.str _) _, h | .call (.int _) _, h | .call (.float64Bits _) _, h
    | .call (.bool _) _, h | .call .jsNull _, h | .call (.call _ _) _, h
    | .call (.object _) _, h | .call (.objectML _) _, h | .call (.objectQuoted _) _, h
    | .call (.objectQuotedML _) _, h | .call (.objectFromEntries _) _, h | .call (.arr _) _, h
    | .call (.arrow _ _) _, h | .call (.generic _ _) _, h | .call (.lambda _ _) _, h
    | .call (.method _ _ _) _, h | .call (.member _ _) _, h | .call (.generator _) _, h
    | .call (.cond _ _ _) _, h | .call (.arrowBlock _ _) _, h => by simp [readTerm] at h
    | .float64Bits _, h | .jsNull, h | .object _, h | .objectML _, h | .objectQuoted _, h
    | .objectQuotedML _, h | .objectFromEntries _, h | .arr _, h | .arrow _ _, h
    | .generic _ _, h | .lambda _ _, h | .method _ _ _, h | .member _ _, h | .generator _, h
    | .cond _ _ _, h | .arrowBlock _ _, h => by simp [readTerm] at h
  termination_by structural x

  theorem readTerms_exact {n : Nat} (xs : List Expr) {ts : Terms} (h : readTerms n xs = .ok ts) :
      printTerms ts = xs :=
    match xs, h with
    | [], h => by simp [readTerms] at h; subst h; rfl
    | x :: rest, h => by
      simp only [readTerms, bind_eq_ok] at h
      obtain ⟨t, ht, ts', hts', hts⟩ := h
      cases hts
      simp [printTerms, readTerm_exact x ht, readTerms_exact rest hts']
  termination_by structural xs
end

theorem readLiteral_print (value : Lit) : readLiteral (printLit value) = .ok value := by
  unfold readLiteral
  have ht := readTerm_printTerm (n := 0) (.lit value) rfl
  change readTerm 0 (printLit value) = .ok (.lit value) at ht
  rw [ht]
  rfl

theorem readLiteral_exact {x : Expr} {value : Lit} (h : readLiteral x = .ok value) :
    printLit value = x := by
  simp only [readLiteral, bind_eq_ok] at h
  obtain ⟨term, ht, h⟩ := h
  cases term with
  | var _ | app _ _ => cases h
  | lit v =>
    cases h
    exact readTerm_exact x ht

/-! ## Causes, fork options, rows: the small round trips -/

theorem headOf_lit (h : Head) (s : String) (hs : h.spelling = s) : headOf s = some h :=
  hs ▸ headOf_spelling h

theorem readCause_printCause {n : Nat} (c : CauseTerm) (h : CauseTerm.scoped n c = true) :
    readCause n (printCause c) = .ok c := by
  induction c with
  | fail e =>
    simp only [CauseTerm.scoped] at h
    rw [printCause]; unfold readCause; simp [headOf_lit .causeFail "Cause.fail" rfl, readTerm_printTerm e h]
  | die d =>
    simp only [CauseTerm.scoped] at h
    rw [printCause]; unfold readCause; simp [headOf_lit .causeDie "Cause.die" rfl, readTerm_printTerm d h]
  | interrupt who =>
    cases who with
    | none => rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl]
    | some w =>
      simp only [CauseTerm.scoped] at h
      rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl, readTerm_printTerm w h]
  | both l r ihl ihr =>
    simp only [CauseTerm.scoped, Bool.and_eq_true] at h
    rw [printCause]; unfold readCause; simp [headOf_lit .causeCombine "Cause.combine" rfl, ihl h.1, ihr h.2]

theorem readCause_exact {n : Nat} (x : Expr) {c : CauseTerm} (h : readCause n x = .ok c) :
    printCause c = x := by
  induction x using readCause.induct generalizing c with
  | case1 s e hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact e ht, headOf_exact hh]
  | case2 s d hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact d ht, headOf_exact hh]
  | case3 s hh => unfold readCause at h; simp only [hh] at h; cases h; simp [printCause, Head.spelling, headOf_exact hh]
  | case4 s w hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact w ht, headOf_exact hh]
  | case5 s l r hh ihl ihr =>
    unfold readCause at h; simp only [hh, bind_eq_ok] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    cases hab
    simp [printCause, Head.spelling, ihl ha, ihr hb, headOf_exact hh]
  | case6 s args h1 h2 h3 h4 h5 => unfold readCause at h; split at h <;> simp_all
  | case7 t hne => unfold readCause at h; split at h <;> simp_all

theorem readForkOptions_print (o : Effect4.Supervision.ForkOptions) :
    readForkOptions o.daemon (printForkOptions o) = .ok o := by
  obtain ⟨s, d, m⟩ := o
  cases m <;> simp [printForkOptions, readForkOptions]

theorem readForkOptions_exact {d : Bool} {x : Expr} {o : Effect4.Supervision.ForkOptions}
    (h : readForkOptions d x = .ok o) : printForkOptions o = x ∧ o.daemon = d := by
  unfold readForkOptions at h
  split at h
  · split at h
    · rename_i hf
      split at h
      · cases h; simp [printForkOptions, hf]
      · cases h; simp [printForkOptions, hf]
      · split at h
        · cases h; rename_i hs; simp [printForkOptions, hf, hs]
        · cases h
      · cases h
    · cases h
  · cases h

theorem idents?_map (l : List String) : idents? (l.map Expr.ident) = some l := by
  induction l with
  | nil => rfl
  | cons s rest ih => simp [idents?, ih]

theorem idents?_exact {args : List Expr} {l : List String} (h : idents? args = some l) :
    args = l.map Expr.ident := by
  induction args generalizing l with
  | nil => simp [idents?] at h; subst h; rfl
  | cons x rest ih =>
    cases x <;> (unfold idents? at h; simp at h)
    obtain ⟨l', hl', rfl⟩ := h
    simp [ih hl']

theorem idents?_cons_none {e : Expr} {l : List Expr} (h : ∀ x, e ≠ Expr.ident x) :
    idents? (e :: l) = none := by
  cases e <;> first | exact absurd rfl (h _) | (unfold idents?; simp)

theorem idents?_printTerms : ∀ ts : Terms, idents? (printTerms ts) = ts.names?
  | .nil => rfl
  | .cons t rest => by
    cases t with
    | var i => simp [printTerms, printTerm, idents?, Terms.names?, idents?_printTerms rest]
    | lit v => cases v <;> simp [printTerms, printTerm, printLit, idents?, Terms.names?, idents?_printTerms rest]
    | app a args => simp [printTerms, printTerm, idents?, Terms.names?]

theorem printTerm_ident {t : Term} {x : String} (h : printTerm t = .ident x) :
    (∃ i, t = .var i ∧ x = Var.name i) ∨ (t = .lit .unit ∧ x = "undefined") := by
  cases t with
  | var i => simp [printTerm] at h; exact .inl ⟨i, rfl, h.symm⟩
  | lit v => cases v <;> simp [printTerm, printLit] at h; exact .inr ⟨rfl, h.symm⟩
  | app a args => simp [printTerm] at h

theorem printTerm_eq_bool (term : Term) (value : Bool) :
    printTerm term = .bool value ↔ term = .lit (.bool value) := by
  cases term with
  | var _ => simp [printTerm]
  | app _ _ => simp [printTerm]
  | lit literal => cases literal <;> simp [printTerm, printLit]

/-- An atom application that is no row reads as no row call, so the caller may read it as a
term. -/
theorem readRowCall_none {sig : Signature Op} {spell : String → List String → Option Op} {n : Nat}
    {atom : String} {args : Terms} (h : noRow spell atom args = true) :
    readRowCall sig spell n atom [] (printTerms args) = none := by
  cases args with
  | nil =>
    simp only [noRow, Bool.and_true, Option.isNone_iff_eq_none] at h
    unfold readRowCall; rw [idents?_printTerms, h]; simp [printTerms]
  | cons t rest =>
    cases rest with
    | nil =>
      simp only [noRow, Bool.and_eq_true, Bool.and_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [idents?_printTerms (.cons t .nil), h.1]
      simp only [printTerms]
      rw [show idents? ([] : List Expr) = Terms.nil.names? from rfl, h.2]
    | cons u names =>
      simp only [noRow, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [idents?_printTerms (.cons t (.cons u names)), h.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [idents?_printTerms (.cons u names), h.2.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [idents?_printTerms names, h.2.2]

theorem readRowCall_unit {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request = Ty.unit)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall sig spell n (sig.rowOf op).spelling typeArgs
        ((sig.rowOf op).trailing.map Expr.ident)
      = some (.ok (rowAnswer (sig.rowOf op) op (.lit .unit))) := by
  unfold readRowCall
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape, hreq, hta]

theorem readRowCall_request {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request ≠ Ty.unit)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall sig spell n (sig.rowOf op).spelling typeArgs
        (printTerm r :: (sig.rowOf op).trailing.map Expr.ident)
      = some ((readTerm n (printTerm r)).map (rowAnswer (sig.rowOf op) op)) := by
  have key : ∀ x, (∀ op', x ∉ (sig.rowOf op').trailing) →
      spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) = none := by
    intro x hx
    cases hsp : spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      exact hx op' (htr ▸ List.mem_cons_self)
  have hA : ((idents? (printTerm r :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases r with
    | var i =>
      simp [printTerm, idents?, idents?_map, key (Var.name i) (fun op' => hl.trailing_ne_name op' i)]
    | lit v =>
      cases v with
      | unit => simp [printTerm, printLit, idents?, idents?_map, key "undefined" hl.trailing_ne_undefined]
      | nat k => simp [printTerm, printLit, idents?]
      | bool b => simp [printTerm, printLit, idents?]
      | str s => simp [printTerm, printLit, idents?]
    | app a args => simp [printTerm, idents?]
  unfold readRowCall
  rw [hA]
  dsimp only
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape, hreq, hta]

/-! ## `read_print`: what the printer prints of a readable program reads back to it -/

theorem readable_row_unit {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .call)
    (hreq : row.request = Ty.unit) (h : requestReadable row n r = true) : r = .lit .unit := by
  simp only [requestReadable, hshape, hreq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

theorem readable_row_value {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .value)
    (h : requestReadable row n r = true) : r = .lit .unit := by
  simp only [requestReadable, hshape, decide_eq_true_eq] at h; exact h

theorem readable_row_request {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .call)
    (hreq : row.request ≠ Ty.unit) (h : requestReadable row n r = true) : r.scoped n = true := by
  simp only [requestReadable, hshape, hreq, if_false, Bool.and_eq_true] at h; exact h.2

/-- A printed term is an identifier only as a binder or as `undefined`, never as a trailing
name of any row. -/
theorem printTerm_ident_not_trailing {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell) (r : Term)
    (op : Op) (v : String) (h : printTerm r = .ident v) : v ∉ (sig.rowOf op).trailing := by
  cases r with
  | var i =>
    simp only [printTerm, Expr.ident.injEq] at h
    subst h
    exact hl.trailing_ne_name op i
  | lit value =>
    cases value with
    | unit =>
      simp only [printTerm, printLit, Expr.ident.injEq] at h
      subst h
      exact hl.trailing_ne_undefined op
    | nat _ | bool _ | str _ => simp [printTerm, printLit] at h
  | app _ _ => simp [printTerm] at h

/-- The tuple reading of a row: two arguments that are not trailing names, then the row's
trailing names, read through `readTupleArgs`. -/
theorem readRowCall_tuple {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (x y : Expr)
    (hshape : (sig.rowOf op).shape = .tupleCall)
    (hx : ∀ op' v, x = .ident v → v ∉ (sig.rowOf op').trailing)
    (hy : ∀ op' v, y = .ident v → v ∉ (sig.rowOf op').trailing) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall sig spell n (sig.rowOf op).spelling typeArgs
        (x :: y :: (sig.rowOf op).trailing.map Expr.ident)
      = some ((readTupleArgs n x y).map (rowAnswer (sig.rowOf op) op)) := by
  have key : ∀ (names : List String) (v : String), (∀ op', v ∉ (sig.rowOf op').trailing) →
      spell (sig.rowOf op).spelling (v :: names) = none := by
    intro names v hv
    cases hsp : spell (sig.rowOf op).spelling (v :: names) with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      exact hv op' (htr ▸ List.mem_cons_self)
  have hA : ((idents? (x :: y :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases x
    case ident v =>
      cases y
      case ident w =>
        simp only [idents?, idents?_map, Option.map_some, Option.bind_some]
        exact key _ v (fun op' => hx op' v rfl)
      all_goals simp [idents?]
    all_goals simp [idents?]
  have hB : ((idents? (y :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases y
    case ident w =>
      simp only [idents?, idents?_map, Option.map_some, Option.bind_some]
      exact key _ w (fun op' => hy op' w rfl)
    all_goals simp [idents?]
  unfold readRowCall
  rw [hA]
  dsimp only
  rw [hB]
  dsimp only
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape, hta]

/-- The tuple request round trip is shared by free calls and receiver methods. -/
theorem readRowCall_printTupleArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .tupleCall) (r : Term)
    (h : tupleRequestReadable n r = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall sig spell n (sig.rowOf op).spelling typeArgs
      (printTupleArgs r ++ (sig.rowOf op).trailing.map Expr.ident) =
      some (.ok (rowAnswer (sig.rowOf op) op r)) := by
  simp only [tupleRequestReadable] at h
  rcases hpa : pairArgs? r with _ | ⟨x, y⟩
  · simp only [hpa] at h
    cases r with
    | var i =>
      simp only at h
      simp only [printTupleArgs, hpa, printTerm, List.cons_append, List.nil_append]
      rw [readRowCall_tuple hl op hd _ _ hshape
        (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy) hta]
      have hv : readTerm n (.ident (Var.name i)) = .ok (.var i) :=
        readTerm_printTerm (.var i) h
      simp [readTupleArgs, savedVar?, hv]
    | lit value =>
      cases value with
      | unit =>
        simp only [printTupleArgs, hpa, printTerm, printLit, List.cons_append, List.nil_append]
        rw [readRowCall_tuple hl op hd _ _ hshape
          (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy) hta]
        have hv : readTerm n (.ident "undefined") = .ok (.lit .unit) :=
          readTerm_printTerm (.lit .unit) rfl
        simp [readTupleArgs, savedVar?, hv]
      | nat _ | bool _ | str _ => simp at h
    | app _ _ => simp at h
  · simp only [hpa, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨hx, hy⟩, hsv⟩ := h
    obtain rfl := pairArgs?_some hpa
    simp only [printTupleArgs, hpa, List.cons_append, List.nil_append]
    rw [readRowCall_tuple hl op hd _ _ hshape
      (fun op' v hv => printTerm_ident_not_trailing hl x op' v hv)
      (fun op' v hv => printTerm_ident_not_trailing hl y op' v hv) hta]
    simp [readTupleArgs, hsv, readTerm_printTerm x hx, readTerm_printTerm y hy]

/-- Method projection keeps the same row identities and name hygiene. -/
theorem methodLawful {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) : LawfulSpelling (methodSignature sig) spell where
  spell_row := hl.spell_row
  row_of_spell := hl.row_of_spell
  value_trailing := by
    intro op hv
    have hs := methodArgsRow_shape (sig.rowOf op)
    change (methodArgsRow (sig.rowOf op)).shape = .value at hv
    rcases hs with hs | hs <;> simp [hs] at hv
  spelling_ne_name := hl.spelling_ne_name
  spelling_not_reserved := hl.spelling_not_reserved
  trailing_ne_name := hl.trailing_ne_name
  trailing_ne_undefined := hl.trailing_ne_undefined

theorem readRowCall_methodArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (args : Term)
    (h : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall (methodSignature sig) spell n (sig.rowOf op).spelling typeArgs
      (printMethodArgs (sig.rowOf op) args) = some (.ok (rowAnswer (sig.rowOf op) op args)) := by
  have hm := methodLawful hl
  rcases methodArgsRow_shape (sig.rowOf op) with hs | hs
  · simp only [hs, reduceCtorEq, if_false] at h
    by_cases ht : (methodArgsRow (sig.rowOf op)).request = Ty.unit
    · simp only [ht, if_true, decide_eq_true_eq] at h
      subst args
      simp only [printMethodArgs, hs, reduceCtorEq, if_false, ht, if_true]
      have result := readRowCall_unit (n := n) hm op hd hs ht hta
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
    · simp only [ht, if_false] at h
      simp only [printMethodArgs, hs, reduceCtorEq, if_false, ht]
      have result := readRowCall_request (n := n) hm op hd args hs ht hta
      rw [readTerm_printTerm args h] at result
      simp only [map_ok] at result
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
  · simp only [hs, if_true] at h
    simp only [printMethodArgs, hs, if_true]
    have result := readRowCall_printTupleArgs (n := n) hm op hd hs args h hta
    dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
    exact result

theorem readRowMethod_print {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (receiver args : Term) (hs : (sig.rowOf op).shape = .method)
    (hr : receiver.scoped n = true)
    (ha : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowMethod sig spell n (printTerm receiver) (sig.rowOf op).spelling typeArgs
      (printMethodArgs (sig.rowOf op) args) =
      .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil)))) := by
  simp only [readRowMethod, readTerm_printTerm receiver hr, ok_bind,
    readRowCall_methodArgs hl op hd args ha hta, Option.getD_some]
  simp only [rowAnswer, addReceiver, hs, if_true]

/-- The printed form of a row answer is the row's printed call. -/
theorem print_rowAnswer {sig : Signature Op} {n : Nat} (op : Op) (r : Term) :
    print sig n (rowAnswer (sig.rowOf op) op r) = printRow (sig.rowOf op) r := by
  simp only [rowAnswer, print_perform]

/-- The reader's two call arms agree on a row's printed head: with no declared type
arguments it is a plain `spelling(...)` call, and with them a `spelling<T…>(...)` call; both
route to `readRowCall` at the row's own type arguments (`E4-CHECK-CE-013`). -/
theorem readPerform_printRowHead {sig : Signature Op} {spell : String → List String → Option Op}
    {n : Nat} (op : Op) (args : List Expr) (answer : Except ReadRefusal (Eff Op))
    (hhead : headOf (sig.rowOf op).spelling = none)
    {typeArgs : List TypeScript.TypeRef} (hta : rowTypeArgs (sig.rowOf op) = some typeArgs)
    (hrow : readRowCall sig spell n (sig.rowOf op).spelling typeArgs args = some answer)
    {head : Expr} (hp : printRowHead (sig.rowOf op) = .ok head) :
    readPerform sig spell n (.call head args) = answer := by
  cases typeArgs with
  | nil =>
    simp only [printRowHead, hta, Except.ok.injEq] at hp
    subst head
    simp only [readPerform, hhead, hrow, Option.getD_some]
  | cons a rest =>
    simp only [printRowHead, hta, Except.ok.injEq] at hp
    subst head
    simp only [readPerform, hrow, Option.getD_some]

/-- A successfully printed readable row reads back to its row answer. -/
theorem read_printRow {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (h : requestReadable (sig.rowOf op) n r = true)
    {x : Expr} (hp : printRow (sig.rowOf op) r = .ok x) :
    readPerform sig spell n x = .ok (rowAnswer (sig.rowOf op) op r) := by
  have hname : ∀ i, Var.name i ≠ (sig.rowOf op).spelling := fun i => (hl.spelling_ne_name op i).symm
  have hhead : headOf (sig.rowOf op).spelling = none := headOf_none (hl.spelling_not_reserved op)
  cases hshape : (sig.rowOf op).shape with
  | value =>
    have hr := readable_row_value hshape h
    subst r
    have htr := hl.value_trailing op hshape
    have hsp := hl.spell_row op hd
    rw [htr] at hsp
    simp only [printRow, hshape, Except.ok.injEq] at hp
    subst x
    simp [readPerform, Var.read_none hname, hhead, readRowValue, hsp, hshape]
  | call =>
    have htypes : (rowTypeArgs (sig.rowOf op)).isSome = true := by
      simp only [requestReadable, hshape, Bool.and_eq_true] at h
      exact h.1
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp htypes
    simp only [printRow, hshape, bind_eq_ok] at hp
    obtain ⟨head, hprint, hp⟩ := hp
    by_cases hreq : (sig.rowOf op).request = Ty.unit
    · have hr := readable_row_unit hshape hreq h
      subst r
      simp only [hreq, if_true, Except.ok.injEq] at hp
      subst x
      exact readPerform_printRowHead op _ _ hhead hta
        (readRowCall_unit hl op hd hshape hreq hta) hprint
    · simp only [hreq, if_false, Except.ok.injEq] at hp
      subst x
      rw [readPerform_printRowHead op _ _ hhead hta
        (readRowCall_request hl op hd r hshape hreq hta) hprint]
      simp [readTerm_printTerm r (readable_row_request hshape hreq h)]
  | tupleCall =>
    simp only [requestReadable, hshape, Bool.and_eq_true] at h
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp h.1
    simp only [printRow, hshape, bind_eq_ok] at hp
    obtain ⟨head, hprint, hp⟩ := hp
    simp only [Except.ok.injEq] at hp
    subst x
    exact readPerform_printRowHead op _ _ hhead hta
      (readRowCall_printTupleArgs hl op hd hshape r h.2 hta) hprint
  | method =>
    simp only [requestReadable, hshape, Bool.and_eq_true] at h
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp h.1
    have h := h.2
    cases hpair : pairArgs? r with
    | none => simp [hpair] at h
    | some parts =>
      obtain ⟨receiver, args⟩ := parts
      simp only [hpair, Bool.and_eq_true_iff] at h
      obtain ⟨hr, ha⟩ := h
      have hm := readRowMethod_print hl op hd receiver args hshape hr ha hta
      obtain rfl := pairArgs?_some hpair
      cases typeArgs with
      | nil =>
        simp only [printRow, hshape, pairArgs?, ↓reduceIte, printMethod, hta,
          Except.ok.injEq] at hp
        subst x
        simp [readPerform, readMethod, hm]
      | cons t ts =>
        simp only [printRow, hshape, pairArgs?, ↓reduceIte, printMethod, hta,
          Except.ok.injEq] at hp
        subst x
        simp [readPerform, readMethod, hm]




/-- The tuple reading reconstructs its two arguments: a saved variable prints as its two
component reads, any other pair as the printed components. -/
theorem readTupleArgs_exact {n : Nat} {x y : Expr} {r : Term}
    (h : readTupleArgs n x y = .ok r) : printTupleArgs r = [x, y] := by
  unfold readTupleArgs at h
  split at h
  · rename_i v hv
    obtain ⟨rfl, rfl⟩ := savedVar?_some hv
    have hp := readTerm_exact (.ident v) h
    have hpa : pairArgs? r = none := by
      cases r with
      | var _ => rfl
      | lit _ => rfl
      | app _ _ => simp [printTerm] at hp
    simp [printTupleArgs, hpa, hp]
  · simp only [bind_eq_ok] at h
    obtain ⟨a, ha, b, hb, he⟩ := h
    cases he
    simp [printTupleArgs, pairArgs?, readTerm_exact x ha, readTerm_exact y hb]

section ReadExact

/-- Closes an arm of a wildcard case of the reader: the arm's own negated-pattern hypothesis
is contradictory, or the arm is a refusal. -/
local macro "close_arm" h:ident : tactic => `(tactic| first
  | (exfalso; subst_vars; solve_by_elim [rfl])
  | cases $h:ident
  | (split at $h:ident <;> first | (exfalso; subst_vars; solve_by_elim [rfl]) | cases $h:ident))

/-- The call reader recovers the method's row identity and exactly its argument syntax. -/
theorem readRowCall_method_parts {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {s : String} {ta : List TypeScript.TypeRef} {args : List Expr}
    {e : Eff Op}
    (h : readRowCall (methodSignature sig) spell n s ta args = some (.ok e)) :
    ∃ op r, e = rowAnswer (sig.rowOf op) op r ∧ (sig.rowOf op).spelling = s ∧
      rowTypeArgs (sig.rowOf op) = some ta ∧ printMethodArgs (sig.rowOf op) r = args := by
  unfold readRowCall at h
  split at h
  · rename_i op hA
    simp only [Option.some.injEq] at h
    split at h
    · rename_i hc
      dsimp only [methodSignature] at hc
      cases h
      obtain ⟨names, hn, hsp⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
      refine ⟨op, .lit .unit, rfl, hs, hc.2.2, ?_⟩
      rw [idents?_exact hn]
      simp only [printMethodArgs, hc.1, reduceCtorEq, if_false, hc.2.1, if_true, htr]
    · cases h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        split at h
        · rename_i hc
          dsimp only [methodSignature] at hc
          obtain ⟨r, hr, rfl⟩ := map_eq_ok.mp h
          obtain ⟨names, hn, hsp⟩ :=
            Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
          obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
          refine ⟨_, r, rfl, hs, hc.2.2, ?_⟩
          rw [idents?_exact hn]
          simp only [printMethodArgs, hc.1, reduceCtorEq, if_false, hc.2.1, htr,
            readTerm_exact _ hr]
        · cases h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            split at h
            · rename_i hc
              dsimp only [methodSignature] at hc
              obtain ⟨r, hr, rfl⟩ := map_eq_ok.mp h
              obtain ⟨names, hn, hsp⟩ :=
                Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
              obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
              refine ⟨_, r, rfl, hs, hc.2, ?_⟩
              rw [idents?_exact hn]
              simp only [printMethodArgs, hc.1, if_true, htr, readTupleArgs_exact hr,
                List.cons_append, List.nil_append]
            · cases h
          · cases h
        · cases h
    · cases h

theorem addReceiver_rowAnswer (sig : Signature Op) (receiver : Term) (op : Op) (args : Term) :
    addReceiver sig receiver (rowAnswer (sig.rowOf op) op args) =
      if (sig.rowOf op).shape = .method then
        .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil))))
      else .error (.shape "method row") := by
  unfold rowAnswer
  split <;> simp [addReceiver, rowAnswer, *]

theorem readRowMethod_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {receiver : Expr} {s : String}
    {ta : List TypeScript.TypeRef} {args : List Expr} {e : Eff Op}
    (h : readRowMethod sig spell n receiver s ta args = .ok e) :
    print sig n e = .ok (match ta with
      | [] => .method receiver s args
      | ts => .call (.generic (.member receiver s) ts) args) := by
  unfold readRowMethod at h
  obtain ⟨recv, hr, h⟩ := bind_eq_ok.mp h
  obtain ⟨body, hb, h⟩ := bind_eq_ok.mp h
  cases hc : readRowCall (methodSignature sig) spell n s ta args with
  | none => simp [hc] at hb
  | some answer =>
    simp only [hc, Option.getD_some] at hb
    rw [hb] at hc
    obtain ⟨op, request, rfl, hs, ht, ha⟩ := readRowCall_method_parts hl hc
    rw [addReceiver_rowAnswer] at h
    split at h
    · rename_i hshape
      cases h
      simp [print_rowAnswer, printRow, hshape, pairArgs?, printMethod,
        hs, ht, ha, readTerm_exact _ hr]
      cases ta <;> rfl
    · cases h

theorem readMethod_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readMethod sig spell n x = .ok e) : print sig n e = .ok x := by
  unfold readMethod at h
  split at h
  · exact readRowMethod_exact hl h
  · exact readRowMethod_exact hl h
  · cases h


end ReadExact

/-! ## The native profile

`nativeSpell` inverts `NativeOp.row` on (spelling, trailing names): the forty read-modify-write
rows share eight spellings and are told apart by the pure function's name, the two `Scope.make`
rows by the `"parallel"` strategy. `nativeLawful` is the receipt that the native table meets
`LawfulSpelling`; the two theorems specialise to it below. -/

/-- The four table requirements: unique keys, no built-in collision, no dropped
trailing names on a value row, and names outside the reserved/binder alphabets.
Split between the program plane (`Table.lawful`) and the codegen name-safety hygiene (`rowNamesSafe`). -/
def LawfulTable (table : RowTable) : Bool :=
  Table.lawful table && table.all rowNamesSafe

/-- Built-ins are checked first; the external key identifies its position in the
supplied table. No external index is recovered by parsing an identifier. -/
def nativeSpell (table : RowTable := []) (s : String) (names : List String) : Option NativeOp :=
  match NativeOp.all.find? (fun op => decide (rowKey op.row = (s, names))) with
  | some op => some op
  | none => (table.findIdx? (fun row => decide (rowKey row = (s, names)))).map NativeOp.external

theorem name_notin (l : List String) (h : ∀ s ∈ l, s.toByteArray.data.toList.head? ≠ some 97)
    (i : Nat) : Var.name i ∉ l := fun hm => Var.name_ne (h _ hm) i rfl

theorem NativeOp.external_not_mem_all (i : Nat) : NativeOp.external i ∉ NativeOp.all := by
  simp [NativeOp.all, fnNames]

theorem NativeOp.all_complete (op : NativeOp) (h : ∀ i, op ≠ .external i) :
    op ∈ NativeOp.all := by
  cases op <;> first
    | decide
    | (rename_i f; cases f <;> decide)
    | exact (h _ rfl).elim

theorem nativeRowOf_mem_all (table : RowTable) (op : NativeOp) (h : op ∈ NativeOp.all) :
    nativeRowOf table op = op.row := by
  cases op <;> first | rfl | exact (NativeOp.external_not_mem_all _ h).elim

theorem nativeRowOf_external (table : RowTable) (i : Nat) (hi : i < table.length) :
    nativeRowOf table (.external i) = table[i] := by
  simp [nativeRowOf, List.getElem?_eq_getElem hi]

theorem lawfulTable_member (table : RowTable) (h : LawfulTable table = true)
    (row : Row) (hr : row ∈ table) :
    rowKey row ∉ NativeOp.all.map (rowKey ∘ NativeOp.row) ∧
    (row.shape = .value → row.trailing = []) ∧ rowNamesSafe row = true := by
  simp only [LawfulTable, Table.lawful, Bool.and_eq_true] at h
  refine ⟨?_, ?_, List.all_eq_true.mp h.2 row hr⟩
  · have hc := List.all_eq_true.mp h.1.1.2 row hr
    simpa [Row.key] using hc
  · have hv := List.all_eq_true.mp h.1.2 row hr
    intro hs
    simpa [hs] using hv

theorem nativeRow_hygiene (table : RowTable) (h : LawfulTable table = true) (op : NativeOp) :
    ((nativeRowOf table op).shape = .value → (nativeRowOf table op).trailing = []) ∧
      rowNamesSafe (nativeRowOf table op) = true := by
  cases op with
  | external i =>
    by_cases hi : i < table.length
    · rw [nativeRowOf_external table i hi]
      exact (lawfulTable_member table h _ (List.getElem_mem hi)).2
    · simp only [nativeRowOf, List.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none]
      decide
  | _ => first
    | (simp only [nativeRowOf]; decide)
    | (rename_i f; cases f <;> simp only [nativeRowOf] <;> decide)

theorem nativeLawful (table : RowTable := []) (h : LawfulTable table = true := by decide) :
    LawfulSpelling (nativeSignature table) (nativeSpell table) where
  spell_row := by
    intro op hd
    cases op with
    | external i =>
      have hi : i < table.length := of_decide_eq_true hd
      change nativeSpell table (nativeRowOf table (.external i)).spelling
        (nativeRowOf table (.external i)).trailing = some (.external i)
      rw [nativeRowOf_external table i hi]
      have hn : (table.map rowKey).Nodup := by
        simp only [LawfulTable, Table.lawful, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1.1
      have hc := (lawfulTable_member table h _ (List.getElem_mem hi)).1
      have hb := builtinLookup_none (rowKey table[i]) hc
      have hf := rowIndex_roundTrip table hn i hi
      dsimp +instances only [rowKey] at hb hf
      unfold nativeSpell rowKey
      rw [hb, hf]
      rfl
    | _ => first
      | rfl
      | (rename_i f; cases f <;> rfl)
  row_of_spell := by
    intro s names op hs
    unfold nativeSpell at hs
    split at hs
    · rename_i found hfound
      have heq : found = op := Option.some.inj hs
      subst op
      have hm := List.mem_of_find?_eq_some hfound
      have hk := List.find?_some
        (p := fun op : NativeOp => decide (rowKey op.row = (s, names))) hfound
      change (nativeRowOf table found).spelling = s ∧ (nativeRowOf table found).trailing = names
      rw [nativeRowOf_mem_all table found hm]
      exact Prod.mk.inj (of_decide_eq_true hk)
    · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨hlt, hk⟩ := rowIndex_exact table (s, names) i hi
      change (nativeRowOf table (.external i)).spelling = s ∧
        (nativeRowOf table (.external i)).trailing = names
      rw [nativeRowOf_external table i hlt]
      exact Prod.mk.inj hk
  value_trailing := fun op => (nativeRow_hygiene table h op).1
  spelling_ne_name := by
    intro op i
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    exact (Var.name_ne (by simpa [firstByte, nativeSignature, Program.Row.normalizeTypes] using hn.1.1) i).symm
  spelling_not_reserved := by
    intro op
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    simpa [nativeSignature, Program.Row.normalizeTypes] using hn.1.2
  trailing_ne_name := by
    intro op i
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    apply name_notin
    intro name hm
    have ht := List.all_eq_true.mp hn.2 name hm
    simpa [firstByte, nativeSignature, Program.Row.normalizeTypes] using (Bool.and_eq_true_iff.mp ht).1
  trailing_ne_undefined := by
    intro op hm
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have ht := List.all_eq_true.mp hn.2 "undefined" hm
    simp at ht

end Effect4.Program
