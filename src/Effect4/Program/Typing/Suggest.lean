import Effect4.Program.Check
import Effect4.Program.Typing.SourceDocument

/-!
# Program.Typing.Suggest — contextual suggestions at a focus

Candidate programs for an address, each with its evidence. A candidate is evaluated by the same
`keepExact` feed that certifies a fill (`suggestOne`), so a suggestion and a fill never disagree.
Every check goes through the oracle, so a memo learns it. `page` is the one paging owner: the tool's
`suggest` query answers it.
-/

set_option autoImplicit false
namespace Effect4.Program.Suggest
open Effect4 Effect4.Program Check
/-- The contextual evidence for a candidate at a target address and focus. -/
inductive Evidence where
  /-- The candidate types at the target's signature and environment with the focus's exact type (`ty`). -/
  | exactFit (ty : EffTy)
  /-- The candidate types at the target's signature and environment with a different type (`actual` vs `expected`). -/
  | typeMismatch (expected actual : EffTy)
  /-- The candidate is refused by the checker at the target's signature and environment; the
  refusal is located at the program's own address, as the feed answers it. -/
  | refused (why : TypeRefusal)
  /-- The `keepExact` feed refuses the candidate for a reason other than its part's type. -/
  | feedRefused (why : FeedRefusal)
  /-- The candidate comes from another lexical environment (`sourceEnv` vs `targetEnv`); moving it needs a scope shift (Slice F). -/
  | differentEnv (sourceEnv targetEnv : TyEnv)
deriving DecidableEq

/-- **One suggestion**: the candidate program, its source address (if local), its check key, and its
contextual evidence. -/
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
          | .error why => .refused why
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

/-- **A page of suggestions** at an address: the candidates `localCandidates` lists, from `cursor`, at
most `limit`, each evaluated by `suggestOne`; and the next cursor, where candidates remain past a
non-empty page. An address with no focus refuses before any check. -/
def page (o : Oracle) (d : Doc) (path : List Nat) (supplied : List NativeEff) (cursor limit : Nat) :
    Checked (Except FeedRefusal (List Suggestion × Option Nat)) := do
  match d.session.focusAt path with
  | none => pure (.error (.noFocus path))
  | some focus =>
    let all := localCandidates d path focus supplied
    match ← suggestPage o d focus path ((all.drop cursor).take limit) with
    | .error why => pure (.error why)
    | .ok items =>
      let next := if 0 < limit ∧ cursor + limit < all.length then some (cursor + limit) else none
      pure (.ok (items, next))
end Effect4.Program.Suggest
