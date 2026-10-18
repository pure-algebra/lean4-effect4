import Effect4.Program.Check
import Effect4.Program.Typing.SourceDocument

/-!
# Program.Typing.CheckCache — contextual suggestions at a focus

The checker cache this module once held is gone: `Check.Memo` owns reuse (`Program/Check.lean`).
What stays is the suggestion: candidate programs for an address, each with its evidence. A
candidate is evaluated by the same `keepExact` feed that certifies a fill (`suggestOne`), so a
suggestion and a fill never disagree. Every check goes through the oracle, so a memo learns it.
-/

set_option autoImplicit false
namespace Effect4.Program.CheckCache
open Effect4 Effect4.Program Check
/-- The contextual evidence for a candidate at a target address and focus. -/
inductive Evidence where
  /-- The candidate types at the target's signature and environment with the focus's exact type (`ty`). -/
  | exactFit (ty : EffTy)
  /-- The candidate types at the target's signature and environment with a different type (`actual` vs `expected`). -/
  | typeMismatch (expected actual : EffTy)
  /-- The candidate is refused by the checker at the target's signature, environment and path. -/
  | refused (why : TypeRefusal)
  /-- The `keepExact` feed refuses the candidate for a reason other than its part's type. -/
  | feedRefused (why : FeedRefusal)
  /-- The candidate comes from another lexical environment (`sourceEnv` vs `targetEnv`); moving it needs a scope shift (Slice F). -/
  | differentEnv (sourceEnv targetEnv : TyEnv)
deriving DecidableEq

/-- One candidate returned by `suggest`, with its source address (if local), its context key, and
its contextual evidence. -/
structure Suggestion where
  program : NativeEff
  sourcePath : Option (List Nat)
  key : CheckInput
  evidence : Evidence
deriving DecidableEq

/-- **Evaluate one candidate** at a focus through the same `keepExact` feed that certifies a fill.
Its key is the module key at the root and the part key below it (`SourceSession.partKey`). A path
with no program or no typed part refuses before any check; no key is invented. -/
def suggestOne (o : Oracle) (d : Doc) (focus : Focus NativeOp)
    (path : List Nat) (sourcePath : Option (List Nat)) (sourceEnv : TyEnv)
    (program : NativeEff) : Checked (Except FeedRefusal Suggestion) := do
  let candidate : Except FeedRefusal Sketch ← match d.session.sketch.fillAt path program with
    | none => pure (.error (.noProgram path))
    | some candidate => pure (.ok candidate)
  match candidate with
  | .error why => return .error why
  | .ok candidate =>
    let key := if path.isEmpty then
      some (.module d.session.app candidate.holes candidate.program)
      else d.session.partKey path program
    match key with
    | none => return .error (.noFocus path)
    | some key =>
      if sourceEnv ≠ focus.env then
        return .ok ⟨program,sourcePath,key,.differentEnv sourceEnv focus.env⟩
      match ← d.session.feed o .keepExact (.fill path program) with
      | .ok _ => return .ok ⟨program,sourcePath,key,.exactFit focus.ty⟩
      | .error (.notKept _ verdict) =>
        let evidence := match verdict with
          | .ok actual => Evidence.typeMismatch focus.ty actual
          | .error why => .refused ⟨path ++ why.path,why.reason⟩
        return .ok ⟨program,sourcePath,key,evidence⟩
      | .error why => return .ok ⟨program,sourcePath,key,.feedRefused why⟩

/-- **Evaluate a page of candidates** in order; the first refusal refuses the page. -/
def suggestPage (o : Oracle) (d : Doc) (focus : Focus NativeOp) (path : List Nat) :
    List (Option (List Nat) × TyEnv × NativeEff) → Checked (Except FeedRefusal (List Suggestion))
  | [] => pure (.ok [])
  | (sourcePath,sourceEnv,program) :: rest => do
    match ← suggestOne o d focus path sourcePath sourceEnv program with
    | .error why => pure (.error why)
    | .ok item =>
      match ← suggestPage o d focus path rest with
      | .error why => pure (.error why)
      | .ok later => pure (.ok (item :: later))

/-- Harvest local candidate items `(sourcePath, sourceEnv, prog)` for `d` at `targetPath` and
`focus`:
1. Any caller-supplied candidate programs `supplied`, checked at `focus.env`.
2. Variables in `focus.env` as `.succeed (.var i)`.
3. Unit-request external rows in `(d.session.app.withHoles d.session.sketch.holes).rows` as
   `.perform (.external i) (.lit .unit)`.
4. Typed sub-programs in `d.session.table` outside `targetPath`, with their own `e.path` and
   `e.env`. -/
def localCandidates (d : Doc) (targetPath : List Nat) (focus : Focus NativeOp)
    (supplied : List NativeEff := []) : List (Option (List Nat) × TyEnv × NativeEff) :=
  let suppliedItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    supplied.map fun p => (none, focus.env, p)
  let varItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    (List.range focus.env.length).map fun i => (none, focus.env, .succeed (.var i))
  let allRows := (d.session.app.withHoles d.session.sketch.holes).rows
  let rowItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    allRows.zipIdx.filterMap fun (r, i) =>
      if r.request == .unit then some (none, focus.env, .perform (.external i) (.lit .unit))
      else none
  let tableItems : List (Option (List Nat) × TyEnv × NativeEff) :=
    d.session.table.filterMap fun e =>
      if decide (e.path = targetPath) then none
      else
        match (Node.eff d.session.sketch.program).at_ e.path, e.env with
        | some (.eff p), some (.env tys) => some (some e.path, tys, p)
        | _, _ => none
  (suppliedItems ++ varItems ++ rowItems ++ tableItems).eraseDups

/-- Bounded search response from `suggest`, carrying its pagination bounds, next cursor, document
revision, target context, and candidate suggestions. -/
structure SuggestResult where
  doc : DocId
  revision : Nat
  path : List Nat
  cursor : Nat
  limit : Nat
  total : Nat
  nextCursor : Option Nat
  sig : SigData
  env : TyEnv
  expected : EffTy
  suggestions : List Suggestion

def suggest (o : Oracle) (d : Doc) (path : List Nat) (limit : Nat := 16)
    (cursor : Nat := 0) (supplied : List NativeEff := []) : Checked (Option SuggestResult) := do
  match d.session.focusAt path with
  | none => pure none
  | some focus =>
    let sig := sketchSigData d.session.sketch d.session.app path
    let all := localCandidates d path focus supplied
    let total := all.length
    let page := (all.drop cursor).take limit
    let nextCursor := if cursor + limit < total then some (cursor + limit) else none
    match ← suggestPage o d focus path page with
    | .error _ => pure none
    | .ok suggestions => pure (some {
        doc := d.id, revision := d.revision, path := path,
        cursor := cursor, limit := limit, total := total, nextCursor := nextCursor,
        sig := sig, env := focus.env, expected := focus.ty, suggestions := suggestions })
end Effect4.Program.CheckCache
