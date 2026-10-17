import Tools.Session
import Effect4.Laws.Program.SourceTable

/-!
# Probe B: context inspection and atomic checked edits

Slice B of the authoring review. A model of the atomic wrapper over `SourceSession`, its
soundness lemma, and the controls of the review's acceptance cases 1, 2, 4 to 8 and 13.

* `Doc`, `EditTarget`, `Change`, `Policy`, `Doc.commit`: the proposed data and operation. The
  document is the existing source session with a revision counter. The target names the
  revision, the source address and the expected sub-program as written. A change fills the
  address or omits it, the hole row declaring the focus's type. `commit` validates and commits
  in one function: a refusal returns no document, so the caller keeps the old one.
* `Doc.commit_sound`: an accepted edit keeps the session coherent, holds the edited sketch,
  bumps the revision, and the source check through the references types the new sketch. Under
  `keepExactType` the old root type and the focus's environment and type stay. Placement:
  concept `initial-algebras-folds`, property `source-session-coherent`; question: the proposed
  claim `checked-edit-atomic` (role compatibility), whose pointer this lemma would be. Reach: one
  coherent session, any target, change and policy. It does not establish execution admission
  (control 13), behaviour, or that an exact fill is always accepted (that direction is tested
  below, not proved). Consumer: the session tool's `replace` and `omit`. Requirement R14.

It composes `SourceSession.feed_coherent`, `SourceSession.feed_keeps`, `SourceSession.view_type`,
`Node.replaceAt_eff`, `Sketch.fillAt_of_replaceAt` and `Effect4.Laws.Auto.toOption_eq_some`. Its
one step, `edit_exists`, says that the edit a change makes exists at an address that holds a
program.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace ProofScout.B

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)

/-! ## The data and the operation -/

/-- A document: the source session and its revision. -/
structure Doc where
  session : SourceSession
  revision : Nat

/-- Open a document at revision zero. -/
def Doc.open (app : SigApp) (s : Sketch) : Doc := ⟨SourceSession.open app s, 0⟩

/-- An edit target: the revision it was read at, the source address, and the sub-program as
written that the address held then. -/
structure EditTarget where
  revision : Nat
  path : List Nat
  expected : NativeEff

/-- What an edit does at its target. -/
inductive Change
  /-- put the program at the address -/
  | fill (q : NativeEff)
  /-- declare a hole with the focus's type and put it at the address -/
  | omitHole (name : String)

/-- The two policies of the review. -/
inductive Policy
  | keepExactType
  | recheckSource
deriving DecidableEq

/-- Why an edit is refused. -/
inductive Refusal
  /-- the target was read at another revision; the current one is given -/
  | stale (current : Nat)
  /-- the address no longer holds the expected sub-program -/
  | moved
  /-- an omission at an address with no typed focus -/
  | noFocus
  /-- the candidate source has no type: its refusals, the first one the check's -/
  | refused (why : List TypeRefusal)
  /-- `keepExactType`: the root type would change -/
  | typeChanged (old : Option EffTy) (new : EffTy)
  /-- `keepExactType`: the focus's environment or type would change -/
  | localChanged (old new : Option (TyEnv × EffTy))
deriving DecidableEq

/-- The target that `inspect` hands out: the current revision, the address and its sub-program
as written, where the address holds one. -/
def Doc.target (d : Doc) (path : List Nat) : Option EditTarget :=
  match (Node.eff d.session.sketch.program).at_ path with
  | some (.eff q) => some ⟨d.revision, path, q⟩
  | _ => none

/-- The edit a change makes at a target. -/
def Doc.editOf (d : Doc) (t : EditTarget) : Change → Option Edit
  | .fill q => some (.fill t.path q)
  | .omitHole name => (d.session.focusAt t.path).map fun f =>
    .omitAt t.path (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems)

/-- The candidate session after an edit. -/
def Doc.after (d : Doc) (e : Edit) : SourceSession := (d.session.feed e).1

/-- **Atomic checked edit.** -/
def Doc.commit (d : Doc) (t : EditTarget) (c : Change) (policy : Policy) : Except Refusal Doc :=
  if t.revision ≠ d.revision then .error (.stale d.revision)
  else if (Node.eff d.session.sketch.program).at_ t.path ≠ some (.eff t.expected) then .error .moved
  else
    match d.editOf t c with
    | none => .error .noFocus
    | some e =>
      match (d.after e).view.type with
      | none => .error (.refused (d.after e).view.refusals)
      | some T' =>
        match policy with
        | .recheckSource => .ok ⟨d.after e, d.revision + 1⟩
        | .keepExactType =>
          if d.session.view.type ≠ some T' then .error (.typeChanged d.session.view.type T')
          else if Table.typedAt (d.after e).table t.path ≠ Table.typedAt d.session.table t.path
          then .error (.localChanged (Table.typedAt d.session.table t.path)
            (Table.typedAt (d.after e).table t.path))
          else .ok ⟨d.after e, d.revision + 1⟩

/-! ## Soundness -/

/-- The edit a change makes exists where the address holds a program. -/
theorem edit_exists {d : Doc} {t : EditTarget} {c : Change} {e : Edit}
    (hat : (Node.eff d.session.sketch.program).at_ t.path = some (.eff t.expected))
    (he : d.editOf t c = some e) : ∃ s', d.session.sketch.edit d.session.app e = some s' := by
  cases c with
  | fill q =>
    cases he
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff q hat
    exact ⟨_, Sketch.fillAt_of_replaceAt hrep⟩
  | omitHole name =>
    unfold Doc.editOf at he
    obtain ⟨f, -, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff (Sketch.hole d.session.app d.session.sketch.holes.length) hat
    exact ⟨_, Sketch.fillAt_of_replaceAt (s := { d.session.sketch with
      holes := d.session.sketch.holes ++ [Row.hole name f.ty.answer f.ty.error f.ty.requires.elems] })
      hrep⟩

/-- **An accepted edit is the checked edit.** -/
theorem Doc.commit_sound {d d' : Doc} {t : EditTarget} {c : Change} {policy : Policy}
    (hc : d.session.Coherent) (h : d.commit t c policy = .ok d') :
    t.revision = d.revision ∧ d'.revision = d.revision + 1 ∧ d'.session.Coherent ∧
      d'.session.app = d.session.app ∧
      (∃ e, d.editOf t c = some e ∧ d.session.sketch.edit d.session.app e = some d'.session.sketch) ∧
      ∃ T', d'.session.sketch.sourceCheck d.session.app = .ok T' ∧
        (policy = .keepExactType →
          d.session.sketch.sourceCheck d.session.app = .ok T' ∧
          Table.typedAt d'.session.table t.path = Table.typedAt d.session.table t.path) := by
  unfold Doc.commit at h
  split at h
  · cases h
  · rename_i hrev'
    have hrev : t.revision = d.revision := Decidable.of_not_not hrev'
    split at h
    · cases h
    · rename_i hat'
      have hat : (Node.eff d.session.sketch.program).at_ t.path = some (.eff t.expected) :=
        Decidable.of_not_not hat'
      split at h
      · cases h
      · rename_i e he
        obtain ⟨s', hedit⟩ := edit_exists hat he
        have hcoh : (d.after e).Coherent := SourceSession.feed_coherent hc _
        have hkeep := SourceSession.feed_keeps d.session e
        have hsk : (d.after e).sketch = s' := hkeep.2 _ hedit
        have happ : (d.after e).app = d.session.app := hkeep.1
        have hview := SourceSession.view_type hcoh
        rw [happ] at hview
        have hed : d.session.sketch.edit d.session.app e = some (d.after e).sketch := by
          rw [hsk]
          exact hedit
        split at h
        · cases h
        · rename_i T' hT
          have hsrc : (d.after e).sketch.sourceCheck d.session.app = .ok T' :=
            Effect4.Laws.Auto.toOption_eq_some.mp (hview ▸ hT)
          split at h
          · cases h
            exact ⟨hrev, rfl, hcoh, happ, ⟨e, he, hed⟩, T', hsrc, fun hp => nomatch hp⟩
          · split at h
            · cases h
            · rename_i hold'
              have hold : d.session.view.type = some T' := Decidable.of_not_not hold'
              split at h
              · cases h
              · rename_i hloc'
                have hloc : Table.typedAt (d.after e).table t.path =
                    Table.typedAt d.session.table t.path := Decidable.of_not_not hloc'
                cases h
                have hold2 := SourceSession.view_type hc
                rw [hold] at hold2
                exact ⟨hrev, rfl, hcoh, happ, ⟨e, he, hed⟩, T', hsrc,
                  fun _ => ⟨Effect4.Laws.Auto.toOption_eq_some.mp hold2.symm, hloc⟩⟩

/-! ## Controls -/

def nat7 : NativeEff := .succeed (.lit (.nat 7))
def strX : NativeEff := .succeed (.lit (.str "x"))
def natTy : EffTy := .pure .nat
def strTy : EffTy := .pure .string

def isOk {α : Type} : Except Refusal α → Bool
  | .ok _ => true
  | .error _ => false

def refusalOf {α : Type} : Except Refusal α → Option Refusal
  | .ok _ => none
  | .error r => some r

-- Case 2 and case 4: a hole beneath a binder shows its environment, and an exact fill applies.
def draft : Sketch := { program := .bind nat7 (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
def d0 : Doc := Doc.open {} draft
#guard (d0.session.focusAt [1]).map (·.env) = some [.nat]
#guard (d0.target [1]).map (·.expected) = some (Sketch.hole {} 0)
def exactFill := (d0.target [1]).map fun t => d0.commit t (.fill (.succeed (.var 0))) .keepExactType
#guard (exactFill.map isOk) = some true
#guard (exactFill.bind fun r => r.toOption.map (·.session.view.type)) = some (some natTy)
#guard (exactFill.bind fun r => r.toOption.map (·.revision)) = some 1

-- Case 6: an ill-typed candidate is refused and returns no document; the raw draft operation
-- (`SourceSession.feed`) keeps it instead (control C5).
def badFill := (d0.target [1]).map fun t => d0.commit t (.fill (.succeed (.var 42))) .recheckSource
#guard (badFill.map isOk) = some false
#guard ((d0.session.feed (.fill [1] (.succeed (.var 42)))).1.view.type) = none

-- Case 5: a stale target is refused after an ancestor edit (control C6) ...
def d1 : Doc := match (d0.target []).map fun t => d0.commit t (.fill (.bind nat7 nat7)) .recheckSource with
  | some (.ok d) => d
  | _ => d0
#guard d1.revision = 1
#guard (((d0.target [1]).map fun t => d1.commit t (.fill nat7) .recheckSource).map refusalOf) =
  some (some (.stale 1))

-- ... and after a preceding-binder edit that keeps the target's bytes: the environment moved.
def binder : Sketch := { program := .bind nat7 (.succeed (.var 0)) }
def b0 : Doc := Doc.open {} binder
def b1 : Doc := match (b0.target [0]).map fun t => b0.commit t (.fill strX) .recheckSource with
  | some (.ok d) => d
  | _ => b0
#guard (b1.target [1]).map (·.expected) = (b0.target [1]).map (·.expected)
#guard (b0.session.focusAt [1]).map (·.env) = some [.nat]
#guard (b1.session.focusAt [1]).map (·.env) = some [.string]
#guard (((b0.target [1]).map fun t => b1.commit t (.fill (.succeed (.var 0))) .keepExactType).map
  refusalOf) = some (some (.stale 1))

-- Case 7: a changed root type is refused under the exact policy and accepted under the whole
-- source check.
def root : Doc := Doc.open {} { program := nat7 }
#guard (((root.target []).map fun t => root.commit t (.fill strX) .keepExactType).map isOk) = some false
#guard (((root.target []).map fun t => root.commit t (.fill strX) .recheckSource).bind fun r =>
  r.toOption.map (·.session.view.type)) = some (some strTy)

-- The exact policy also refuses a local change that keeps the root type: the left child's answer
-- moves from a number to a string, so the right child's environment moves (control C4).
def pair : Doc := Doc.open {} { program := .bind nat7 nat7 }
#guard (((pair.target [0]).map fun t => pair.commit t (.fill strX) .keepExactType).map refusalOf) =
  some (some (.localChanged (some ([], natTy)) (some ([], strTy))))
#guard (((pair.target [0]).map fun t => pair.commit t (.fill strX) .recheckSource).map isOk) = some true

-- Case 8: a candidate whose forward reference the source rules refuse is refused, though its
-- expansion splices (the additional review's control A).
def keyA : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def appA : SigApp := { services := [(keyA, .string)] }
def strA : NativeEff := .succeed (.lit (.str "a"))
def nat2 : NativeEff := .succeed (.lit (.nat 2))
def laterLayer : Sketch := {
  program := .bind (.succeed (.lit (.nat 1))) (.provideLayer (.effect keyA strA) false nat2) }
def forward : Doc := Doc.open appA laterLayer
def forwardUse : NativeEff := .provideLayer (.ref [1, 0]) false nat7
#guard (((forward.target [0]).map fun t => forward.commit t (.fill forwardUse) .recheckSource).map
  (fun r => match r with
    | .error (.refused (_ :: _)) => true
    | _ => false)) = some true

-- An edit inside a referenced layer checks the session again and keeps both types, so the exact
-- policy accepts it although the delta is not a splice (the additional review's control A).
def refs : Sketch := {
  program := .provideLayer (.effect keyA strA) false
    (.bind (Sketch.hole appA 0) (.provideLayer (.ref [0]) false nat2))
  holes := [Row.hole "hole" .nat] }
def refDoc : Doc := Doc.open appA refs
#guard (refDoc.session.feed (.fill [0, 0] (.succeed (.lit (.str "b"))))).2 = .rechecked
#guard (((refDoc.target [0, 0]).map fun t =>
  refDoc.commit t (.fill (.succeed (.lit (.str "b")))) .keepExactType).map isOk) = some true

-- An atomic omission keeps the type, and the hole row declares the focus's type.
def omitted := (pair.target [0]).map fun t => pair.commit t (.omitHole "left") .keepExactType
#guard (omitted.map isOk) = some true
#guard (omitted.bind fun r => r.toOption.map (·.session.sketch.holes.length)) = some 1
#guard (omitted.bind fun r => r.toOption.map (·.session.view.type)) = some (some natTy)

-- Case 13: a sketch with a reference-valued hole edits and checks, and execution admission still
-- refuses its row (control C9).
def handleHole : Sketch :=
  { program := .bind nat7 (Sketch.hole {} 0), holes := [Row.hole "h" (.refOf .nat)] }
def hd : Doc := Doc.open {} handleHole
#guard (((hd.target [0]).map fun t => hd.commit t (.fill (.succeed (.lit (.nat 8)))) .keepExactType).map
  isOk) = some true
#guard (admitProgram handleHole.program (({} : SigApp).withHoles handleHole.holes)).toOption.isNone

end ProofScout.B
