import OCaml5.Ml.Render

/-!
# OCaml5.Ml.Passes

Transformations on `Expr`, each with its precondition stated and a checker that decides whether
it fired.

There is one pass, and it is the one a Lean-to-OCaml port cannot do without: **pure update to
mutation**. Lean threads a record through pure updates; an OCaml runtime mutates one in place.
The rewrite is mechanical on one shape and only on that shape, which is what makes it checkable:

```
let f = { f with x = v; y = w } in body            ⟶   f.x <- v; f.y <- w; body
let f = { f with g = { f.g with x = v } } in body  ⟶   f.g.x <- v; body
```

## The precondition

`mutate linear e` is meaning-preserving when, for every name `f` in `linear`:

1. **`f` is used linearly.** After `let f = { f with … } in body`, the *old* value of `f` is
   never read again — not by `body`, not by a closure that escaped earlier, not by a data
   structure that captured it. Overwriting it is then unobservable.
2. **`f`'s record type has the updated fields declared `mutable`.** The pass writes
   `f.x <- v`; `ocamlc` rejects it otherwise, so this half of the precondition is checked by the
   compiler and needs no checker here.
3. **The `let` rebinds the name it updates.** This the pass checks itself: it fires only on
   `let f = { f with … }`, never on `let g = { f with … }`, which is a copy and must stay one.

Condition 1 is the one a caller asserts, by putting the name in `linear`. It is not decidable
here — it is a fact about the Lean function the expression was transcribed from — so it is
declared rather than inferred, and the declaration is one list per call site.

## The residue checker

`residue` is the answer to "did the pass fire everywhere?": it lists the `{ … with … }`
occurrences that survive. A caller `#guard`s that `residue (mutate linear e)` is empty and that
`residue e` is not, so "the pass applied to every update" is a fact and not a hope. A surviving
`{ … with … }` is not wrong — it is a copy — but in a transcribed Lean function it is almost
always an update the caller forgot to declare linear.

## What the pass does not do

It does not reorder, does not float, does not inline, does not eliminate a `let` whose value is
not a record update, and does not look inside `Expr.raw`. Everything else it traverses and leaves
alone.
-/

namespace OCaml5.Ml

/-- The nested case: `{ f.g with x = v }` under `{ f with g = … }` targets `f.g`. Returns the
flat updates and the nested ones, the latter keyed by their dotted path. -/
private def flatten (f : String) :
    List (String × Expr) → List (String × Expr) × List (String × Expr)
  | [] => ([], [])
  | (g, .recordWith (.field (.var f') g') inner) :: rest =>
      let (flat, nested) := flatten f rest
      if f' == f && g' == g then (flat, inner.map (fun kv => (g ++ "." ++ kv.1, kv.2)) ++ nested)
      else ((g, .recordWith (.field (.var f') g') inner) :: flat, nested)
  | kv :: rest => let (flat, nested) := flatten f rest; (kv :: flat, nested)

private def setPath (f : String) (path : String) (v : Expr) : Expr :=
  match path.splitOn "." with
  | [k] => .setField (.var f) k v
  | [g, k] => .setField (.field (.var f) g) k v
  | _ => .raw ("(* unsupported update path " ++ path ++ " *)")

private def setChainPaths (f : String) (fs : List (String × Expr)) (body : Expr) : Expr :=
  match fs, body with
  | [], _ => body
  -- a trailing `()` is the statement itself; do not sequence it
  | [(k, v)], .unit => setPath f k v
  | [(k, v)], _ => .seq (setPath f k v) body
  | (k, v) :: rest, _ => .seq (setPath f k v) (setChainPaths f rest body)

mutual

/-- The pass. Structural; the only rewrite is the one in the module docstring.

When the body is just `f` — a Lean function returning the updated record — the result is `()`,
because the OCaml caller already holds the record and a returned copy would be a second one. -/
def mutate (linear : List String) : Expr → Expr
  | .letIn n (.recordWith (.var f) fs) body =>
      let fs' := mutateFields linear fs
      let body' := mutate linear body
      if n == f && linear.contains f then
        let (flat, nested) := flatten f fs'
        let tail := match body with
          | .var b => if b == f then Expr.unit else body'
          | _ => body'
        setChainPaths f (flat ++ nested) tail
      else .letIn n (.recordWith (.var f) fs') body'
  | .letIn n v b => .letIn n (mutate linear v) (mutate linear b)
  | .letPat p v b => .letPat p (mutate linear v) (mutate linear b)
  | .openIn path b => .openIn path (mutate linear b)
  | .ctor n args => .ctor n (mutates linear args)
  | .polyCtor t a => .polyCtor t (mutateOpt linear a)
  | .app f args => .app (mutate linear f) (mutates linear args)
  | .appL f args => .appL (mutate linear f) (mutateLabelled linear args)
  | .binop op l r => .binop op (mutate linear l) (mutate linear r)
  | .fn ps b => .fn ps (mutate linear b)
  | .lam ps b => .lam (mutateParams linear ps) (mutate linear b)
  | .functionE arms => .functionE (mutateArms linear arms)
  | .letRecIn bs b => .letRecIn (mutateBinds linear bs) (mutate linear b)
  | .seq a b => .seq (mutate linear a) (mutate linear b)
  | .ifThen c t e => .ifThen (mutate linear c) (mutate linear t) (mutate linear e)
  | .ifThenOnly c t => .ifThenOnly (mutate linear c) (mutate linear t)
  | .whileE c b => .whileE (mutate linear c) (mutate linear b)
  | .forE n lo hi d b => .forE n (mutate linear lo) (mutate linear hi) d (mutate linear b)
  | .matchE s arms => .matchE (mutate linear s) (mutateArms linear arms)
  | .tryWith b arms => .tryWith (mutate linear b) (mutateArms linear arms)
  | .record fs => .record (mutateFields linear fs)
  | .recordWith b fs => .recordWith (mutate linear b) (mutateFields linear fs)
  | .field e n => .field (mutate linear e) n
  | .setField e n v => .setField (mutate linear e) n (mutate linear v)
  | .tuple ps => .tuple (mutates linear ps)
  | .listLit xs => .listLit (mutates linear xs)
  | .arrayLit xs => .arrayLit (mutates linear xs)
  | .arrayGet a i => .arrayGet (mutate linear a) (mutate linear i)
  | .arraySet a i v => .arraySet (mutate linear a) (mutate linear i) (mutate linear v)
  | .mkRef e => .mkRef (mutate linear e)
  | .deref e => .deref (mutate linear e)
  | .assign r v => .assign (mutate linear r) (mutate linear v)
  | .raiseE e => .raiseE (mutate linear e)
  | .assertE e => .assertE (mutate linear e)
  | .lazyE e => .lazyE (mutate linear e)
  | .perform e => .perform (mutate linear e)
  | .continueK k v => .continueK (mutate linear k) (mutate linear v)
  | .discontinueK k e => .discontinueK (mutate linear k) (mutate linear e)
  | .shallowContinue k v h =>
      .shallowContinue (mutate linear k) (mutate linear v) (mutate linear h)
  | .shallowDiscontinue k e h =>
      .shallowDiscontinue (mutate linear k) (mutate linear e) (mutate linear h)
  | .reperform e k l => .reperform (mutate linear e) (mutate linear k) (mutate linear l)
  | .matchWith c a ty rv r ex ef =>
      .matchWith (mutate linear c) (mutate linear a) ty rv (mutate linear r)
        (mutateArms linear ex) (mutateEffc linear ef)
  | .tryWithEff c a ty ef =>
      .tryWithEff (mutate linear c) (mutate linear a) ty (mutateEffc linear ef)
  | .matchWithK kind c a h =>
      .matchWithK kind (mutate linear c) (mutate linear a) (mutate linear h)
  | .handler kind ty retc ex ef =>
      .handler kind ty (match retc with
                        | none => none
                        | some (v, r) => some (v, mutate linear r))
        (mutateArms linear ex) (mutateEffc linear ef)
  | .annot e ty => .annot (mutate linear e) ty
  | .hole note fill => .hole note (mutate linear fill)
  | e => e

def mutates (linear : List String) : List Expr → List Expr
  | [] => []
  | e :: rest => mutate linear e :: mutates linear rest

def mutateLabelled (linear : List String) :
    List (ArgLabel × Expr) → List (ArgLabel × Expr)
  | [] => []
  | (l, e) :: rest => (l, mutate linear e) :: mutateLabelled linear rest

def mutateOpt (linear : List String) : Option Expr → Option Expr
  | none => none
  | some e => some (mutate linear e)

def mutateFields (linear : List String) : List (String × Expr) → List (String × Expr)
  | [] => []
  | (n, e) :: rest => (n, mutate linear e) :: mutateFields linear rest

def mutateBinds (linear : List String) :
    List (String × List String × Expr) → List (String × List String × Expr)
  | [] => []
  | (n, ps, e) :: rest => (n, ps, mutate linear e) :: mutateBinds linear rest

def mutateArms (linear : List String) : List Arm → List Arm
  | [] => []
  | .mk p g b :: rest =>
      .mk p (match g with
             | none => none
             | some ge => some (mutate linear ge))
        (mutate linear b) :: mutateArms linear rest

def mutateEffc (linear : List String) : List Effc → List Effc
  | [] => []
  | .mk n args k b :: rest => .mk n args k (mutate linear b) :: mutateEffc linear rest

def mutateParams (linear : List String) : List Param → List Param
  | [] => []
  | .mk l p t d :: rest =>
      .mk l p t (match d with
                 | none => none
                 | some e => some (mutate linear e)) :: mutateParams linear rest

end

mutual

/-- Every `{ … with … }` the pass left behind, named by the field it updates. Empty means the
pass fired everywhere. -/
def residue : Expr → List String
  | .recordWith b fs => fs.map (·.1) ++ residue b ++ residueFields fs
  | .letIn _ v b => residue v ++ residue b
  | .letPat _ v b => residue v ++ residue b
  | .openIn _ b => residue b
  | .ctor _ args => residues args
  | .polyCtor _ a => residueOpt a
  | .app f args => residue f ++ residues args
  | .appL f args => residue f ++ residueLabelled args
  | .binop _ l r => residue l ++ residue r
  | .fn _ b => residue b
  | .lam ps b => residueParams ps ++ residue b
  | .functionE arms => residueArms arms
  | .letRecIn bs b => residueBinds bs ++ residue b
  | .seq a b => residue a ++ residue b
  | .ifThen c t e => residue c ++ residue t ++ residue e
  | .ifThenOnly c t => residue c ++ residue t
  | .whileE c b => residue c ++ residue b
  | .forE _ lo hi _ b => residue lo ++ residue hi ++ residue b
  | .matchE s arms => residue s ++ residueArms arms
  | .tryWith b arms => residue b ++ residueArms arms
  | .record fs => residueFields fs
  | .field e _ => residue e
  | .setField e _ v => residue e ++ residue v
  | .tuple ps => residues ps
  | .listLit xs => residues xs
  | .arrayLit xs => residues xs
  | .arrayGet a i => residue a ++ residue i
  | .arraySet a i v => residue a ++ residue i ++ residue v
  | .mkRef e => residue e
  | .deref e => residue e
  | .assign r v => residue r ++ residue v
  | .raiseE e => residue e
  | .assertE e => residue e
  | .lazyE e => residue e
  | .perform e => residue e
  | .continueK k v => residue k ++ residue v
  | .discontinueK k e => residue k ++ residue e
  | .shallowContinue k v h => residue k ++ residue v ++ residue h
  | .shallowDiscontinue k e h => residue k ++ residue e ++ residue h
  | .reperform e k l => residue e ++ residue k ++ residue l
  | .matchWith c a _ _ r ex ef =>
      residue c ++ residue a ++ residue r ++ residueArms ex ++ residueEffc ef
  | .tryWithEff c a _ ef => residue c ++ residue a ++ residueEffc ef
  | .matchWithK _ c a h => residue c ++ residue a ++ residue h
  | .handler _ _ retc ex ef =>
      (match retc with | none => [] | some (_, r) => residue r)
        ++ residueArms ex ++ residueEffc ef
  | .annot e _ => residue e
  | .hole _ fill => residue fill
  | _ => []

def residues : List Expr → List String
  | [] => []
  | e :: rest => residue e ++ residues rest

def residueLabelled : List (ArgLabel × Expr) → List String
  | [] => []
  | (_, e) :: rest => residue e ++ residueLabelled rest

def residueOpt : Option Expr → List String
  | none => []
  | some e => residue e

def residueFields : List (String × Expr) → List String
  | [] => []
  | (_, e) :: rest => residue e ++ residueFields rest

def residueBinds : List (String × List String × Expr) → List String
  | [] => []
  | (_, _, e) :: rest => residue e ++ residueBinds rest

def residueArms : List Arm → List String
  | [] => []
  | .mk _ g b :: rest =>
      (match g with | none => [] | some ge => residue ge) ++ residue b ++ residueArms rest

def residueEffc : List Effc → List String
  | [] => []
  | .mk _ _ _ b :: rest => residue b ++ residueEffc rest

def residueParams : List Param → List String
  | [] => []
  | .mk _ _ _ d :: rest =>
      (match d with | none => [] | some e => residue e) ++ residueParams rest

end

/-- The pass fired everywhere on this expression: no `{ … with … }` survives. -/
def mutated (linear : List String) (e : Expr) : Bool := (residue (mutate linear e)).isEmpty

/-- The pass had something to fire on: the input does contain a `{ … with … }`. Guarding both
this and `mutated` is what keeps a vacuous "no residue" from passing for a result. -/
def hasUpdates (e : Expr) : Bool := !(residue e).isEmpty

/-! ## Checks -/

private def park : Expr :=
  .letIn "f"
    (.recordWith (.var "f")
      [("parked", .ctor "WithGuard" [.field (.var "p") "token"]),
       ("pending", .binop "@" (.field (.var "f") "pending") (.listLit [.var "p"]))])
    (.var "f")

#guard hasUpdates park
#guard mutated ["f"] park
#guard renderExpr 0 (mutate ["f"] park) ==
  "f.parked <- WithGuard p.token;\nf.pending <- f.pending @ [p]"

-- The nested case: `{ f with g = { f.g with x = v } }` becomes one `f.g.x <- v`.
private def nested : Expr :=
  .letIn "f"
    (.recordWith (.var "f")
      [("frame", .recordWith (.field (.var "f") "frame") [("interrupted", .bool true)])])
    .unit

#guard renderExpr 0 (mutate ["f"] nested) == "f.frame.interrupted <- true"

-- A copy is not an update: the `let` binds a different name, so the pass leaves it alone.
private def copy : Expr := .letIn "g" (.recordWith (.var "f") [("x", .int 1)]) (.var "g")
#guard !(mutated ["f"] copy)
#guard renderExpr 0 (mutate ["f"] copy) == "let g = { f with x = 1 } in\ng"

-- …and a name the caller did not declare linear is left alone too.
#guard !(mutated ["g"] park)

-- The pass reaches inside every binding form: an update under a `match` arm, a handler clause
-- and a `lam` default all fire.
private def underArm : Expr :=
  .matchE (.var "x") [.mk .wild none park]
#guard mutated ["f"] underArm

end OCaml5.Ml
