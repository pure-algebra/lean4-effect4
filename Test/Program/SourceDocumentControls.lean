import Tools.Session
import Effect4.Laws.Program.SourceDocument

/-!
# Document identity, context inspection and atomic checked edits: controls (slice B)

1. **Case 2 (`inspect`)**: a hole beneath a `bind` reports `[nat]` in its focus environment and
   hands out an `EditTarget`.
2. **Case 4 (`Doc.commit`, `replace`)**: an exact fill is accepted at revision 1 with root type
   `nat`.
3. **Case 5 (`stale`)**: a stale target refuses after an ancestor edit and after a preceding-binder
   edit that keeps the target's bytes while moving its environment from `[nat]` to `[string]`.
4. **Case 6 (`refused` vs `draft`)**: an ill-typed fill returns no document under `Doc.commit` /
   `replace`, while `Doc.draft` / `draft` keeps it as a draft.
5. **Case 7 (`keepExactType` vs `recheckSource`)**: a root type change refuses under
   `keepExactType` and passes under `recheckSource`.
6. **Control C4 (`localChanged`)**: a local change at `[0]` that keeps the root type refuses under
   `keepExactType`.
7. **Case 8 (layer references)**: a forward reference refuses with its refusals; an edit inside a
   referenced layer is accepted under `keepExactType` although the session checks again.
8. **Case 13 (C9)**: a reference-valued hole edits and checks, while `admitProgram` refuses it.
9. **Checked omission (`omitHole`)**: declares one hole row and keeps the type.
10. **F3 (`foreign`)**: `docText` refuses `docNat`'s target with `Refusal.foreign` under both
    `recheckSource` and `keepExactType`.
11. **Distinct opening generations and `fork`**: two documents opened from equal sketches (or forked
    from one document) receive distinct identities and refuse each other's targets as `foreign`.
12. **Monotonic revision across `undo`**: after `undo`, a target taken before the undone edit
    refuses as `stale` because the revision moved on.
-/

set_option autoImplicit false

namespace Test.Program.SourceDocumentControls

open Effect4 Effect4.Program Tools.Session Tools.JsonBridge

def nat7 : NativeEff := .succeed (.lit (.nat 7))
def strX : NativeEff := .succeed (.lit (.str "x"))
def natTy : EffTy := .pure .nat
def strTy : EffTy := .pure .string

def isOk {α : Type} : Except Doc.Refusal α → Bool
  | .ok _ => true
  | .error _ => false

def refusalOf {α : Type} : Except Doc.Refusal α → Option Doc.Refusal
  | .ok _ => none
  | .error r => some r

/-- Reader: `Doc.commit_sound` applied to a coherent document. -/
example {d d' : Doc} {t : EditTarget} {c : Change} {policy : Policy}
    (hc : d.session.Coherent) (h : d.commit t c policy = .ok d') :
    t.doc = d.id ∧ t.revision = d.revision ∧ d'.id = d.id ∧ d'.revision = d.revision + 1 ∧
      d'.session.Coherent := by
  obtain ⟨hdoc, hrev, hid, hrev', hcoh, -⟩ := Doc.commit_sound hc h
  exact ⟨hdoc, hrev, hid, hrev', hcoh⟩

-- Controls 1 & 2 (Cases 2 and 4): `inspect` beneath `bind` shows `[.nat]`, and `commit` accepts an
-- exact fill at revision 1.
#guard
  let draft : Sketch := { program := .bind nat7 (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
  let d0 : Doc := Doc.open {} draft ⟨"d", 0⟩
  let ins := d0.inspect [1]
  let exactFill := (d0.target [1]).map fun t =>
    d0.commit t (.fill (.succeed (.var 0))) .keepExactType
  (ins.bind (·.focus)).map (·.env) == some [.nat] &&
    (ins.map (·.target.expected)) == some (Sketch.hole {} 0) &&
    (exactFill.map isOk) == some true &&
    (exactFill.bind fun r => r.toOption.map (·.session.view.type)) == some (some natTy) &&
    (exactFill.bind fun r => r.toOption.map (·.revision)) == some 1

-- Control 4 (Case 6): an ill-typed fill is refused by `Doc.commit` and kept by `Doc.draft`.
#guard
  let draft : Sketch := { program := .bind nat7 (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
  let d0 : Doc := Doc.open {} draft ⟨"d", 0⟩
  let badFill := (d0.target [1]).map fun t =>
    d0.commit t (.fill (.succeed (.var 42))) .recheckSource
  let drafted := (d0.draft (.fill [1] (.succeed (.var 42)))).1
  (badFill.map isOk) == some false &&
    drafted.session.view.type == none &&
    drafted.revision == 1

-- Control 3 (Case 5): a stale target is refused after an ancestor edit and after a preceding
-- binder edit that keeps the target's bytes while moving the environment from `[.nat]` to
-- `[.string]`.
#guard
  let draft : Sketch := { program := .bind nat7 (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
  let d0 : Doc := Doc.open {} draft ⟨"d", 0⟩
  let d1 : Doc :=
    match (d0.target []).map fun t => d0.commit t (.fill (.bind nat7 nat7)) .recheckSource with
    | some (.ok d) => d
    | _ => d0
  let binder : Sketch := { program := .bind nat7 (.succeed (.var 0)) }
  let b0 : Doc := Doc.open {} binder ⟨"b", 0⟩
  let b1 : Doc :=
    match (b0.target [0]).map fun t => b0.commit t (.fill strX) .recheckSource with
    | some (.ok d) => d
    | _ => b0
  d1.revision == 1 &&
    (((d0.target [1]).map fun t => d1.commit t (.fill nat7) .recheckSource).map refusalOf) ==
      some (some (.stale 1)) &&
    (b1.target [1]).map (·.expected) == (b0.target [1]).map (·.expected) &&
    (b0.session.focusAt [1]).map (·.env) == some [.nat] &&
    (b1.session.focusAt [1]).map (·.env) == some [.string] &&
    (((b0.target [1]).map fun t => b1.commit t (.fill (.succeed (.var 0))) .keepExactType).map
      refusalOf) == some (some (.stale 1))

-- Controls 5 & 6 (Case 7 and C4): `keepExactType` refuses a root type change and a local type
-- change at `[0]` that keeps the root type, while `recheckSource` accepts both.
#guard
  let root : Doc := Doc.open {} { program := nat7 } ⟨"r", 0⟩
  let pair : Doc := Doc.open {} { program := .bind nat7 nat7 } ⟨"p", 0⟩
  (((root.target []).map fun t => root.commit t (.fill strX) .keepExactType).map isOk) ==
      some false &&
    (((root.target []).map fun t => root.commit t (.fill strX) .recheckSource).bind fun r =>
      r.toOption.map (·.session.view.type)) == some (some strTy) &&
    (((pair.target [0]).map fun t => pair.commit t (.fill strX) .keepExactType).map refusalOf) ==
      some (some (.localChanged (some ([], natTy)) (some ([], strTy)))) &&
    (((pair.target [0]).map fun t => pair.commit t (.fill strX) .recheckSource).map isOk) ==
      some true

-- Control 7 (Case 8): a forward layer reference is refused, while an edit inside a referenced
-- layer is accepted under `keepExactType` although the session checks again.
#guard
  let keyA : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
  let appA : SigApp := { services := [(keyA, .string)] }
  let strA : NativeEff := .succeed (.lit (.str "a"))
  let nat2 : NativeEff := .succeed (.lit (.nat 2))
  let laterLayer : Sketch :=
    { program := .bind (.succeed (.lit (.nat 1))) (.provideLayer (.effect keyA strA) false nat2) }
  let forward : Doc := Doc.open appA laterLayer ⟨"f", 0⟩
  let forwardUse : NativeEff := .provideLayer (.ref [1, 0]) false nat7
  let refs : Sketch :=
    { program := .provideLayer (.effect keyA strA) false
        (.bind (Sketch.hole appA 0) (.provideLayer (.ref [0]) false nat2))
      holes := [Row.hole "hole" .nat] }
  let refDoc : Doc := Doc.open appA refs ⟨"ref", 0⟩
  (((forward.target [0]).map fun t => forward.commit t (.fill forwardUse) .recheckSource).map
    (fun r => match r with
      | .error (.refused (_ :: _)) => true
      | _ => false)) == some true &&
    (refDoc.session.feed (.fill [0, 0] (.succeed (.lit (.str "b"))))).2 == .rechecked &&
    (((refDoc.target [0, 0]).map fun t =>
      refDoc.commit t (.fill (.succeed (.lit (.str "b")))) .keepExactType).map isOk) == some true

-- Controls 8 & 9 (Case 13 and checked omission): a checked omission declares one hole row and
-- keeps the type; a reference-valued hole edits and checks while `admitProgram` refuses it.
#guard
  let pair : Doc := Doc.open {} { program := .bind nat7 nat7 } ⟨"p", 0⟩
  let omitted := (pair.target [0]).map fun t => pair.commit t (.omitHole "left") .keepExactType
  let handleHole : Sketch :=
    { program := .bind nat7 (Sketch.hole {} 0), holes := [Row.hole "h" (.refOf .nat)] }
  let hd : Doc := Doc.open {} handleHole ⟨"h", 0⟩
  (omitted.map isOk) == some true &&
    (omitted.bind fun r => r.toOption.map (·.session.sketch.holes.length)) == some 1 &&
    (omitted.bind fun r => r.toOption.map (·.session.view.type)) == some (some natTy) &&
    (((hd.target [0]).map fun t =>
      hd.commit t (.fill (.succeed (.lit (.nat 8)))) .keepExactType).map isOk) == some true &&
    (admitProgram handleHole.program (({} : SigApp).withHoles handleHole.holes)).toOption.isNone

-- Controls 10, 11 & 12 (F3 `foreign`, distinct opening generations, `fork`, and `undo` revision):
-- `docText` refuses `docNat`'s target with `.foreign` under both policies; two `open` calls on
-- equal sketches and `fork` produce distinct generations; and after `undo`, a target taken before
-- the undone edit refuses as `stale`.
#guard
  let docNat : Doc := Doc.open {} { program := .bind nat7 nat7 } ⟨"docNat", 0⟩
  let docText : Doc := Doc.open {} { program := .bind nat7 strX } ⟨"docText", 0⟩
  let foreignRecheck := (docNat.target [0]).map fun t =>
    docText.commit t (.fill strX) .recheckSource
  let foreignExact := (docNat.target [0]).map fun t =>
    docText.commit t (.fill nat7) .keepExactType
  let r0 := answer {} { op := "open", program := some (toHex (Eff.bind nat7 nat7 : NativeEff)) }
  let r1 := answer r0.1 { op := "open", program := some (toHex (Eff.bind nat7 nat7 : NativeEff)) }
  let rFork := answer r1.1 { op := "fork", docName := some "branch" }
  let rEdit := answer r1.1
    { op := "replace", path := [0], revision := some 0,
      expected := some (toHex nat7),
      replacement := some (toHex (Eff.succeed (.lit (.nat 8)) : NativeEff)) }
  let rUndo := answer rEdit.1 { op := "undo" }
  let rStaleAfterUndo := answer rUndo.1
    { op := "replace", path := [0], revision := some 1,
      expected := some (toHex (Eff.succeed (.lit (.nat 8)) : NativeEff)),
      replacement := some (toHex nat7) }
  (foreignRecheck.map refusalOf) == some (some (.foreign ⟨"docText", 0⟩)) &&
    (foreignExact.map refusalOf) == some (some (.foreign ⟨"docText", 0⟩)) &&
    r0.1.docId != r1.1.docId &&
    r1.1.docId != rFork.1.docId &&
    rEdit.2.ok && rEdit.1.revision == 1 &&
    rUndo.2.ok && rUndo.1.revision == 2 &&
    !rStaleAfterUndo.2.ok &&
    rStaleAfterUndo.2.result.getObjValD "reason" == Lean.Json.str "stale"

end Test.Program.SourceDocumentControls
