import Effect4.Program.Typing.PartsTable

/-! Finite controls only. Placement and limits are in PLAN.md.
The committed base lacks the new defs field. This mirrors only the draft part reader. -/
namespace ModuleLayerPartsReview
open Effect4 Effect4.Program

def sig := nativeSignature []
def unitP : NativeEff := .succeed (.lit .unit)
def badP : NativeEff := .succeed (.var 0)
def bindP : NativeEff := .bind (.succeed (.lit (.nat 7))) (.succeed (.var 0))
def callP : NativeEff := .perform .refMake (.lit (.nat 7))
def releaseP : NativeEff := .scoped (.acquireRelease (.succeed (.lit (.nat 7)))
  (.succeed (.var 0)))
def one (e : NativeEff) : LayerTerms NativeOp := .cons (.effectDiscard e) .nil

def adapter (ls : LayerTerms NativeOp) : NativeEff :=
  .provideLayer (.mergeAll ls) false unitP

-- The draft partAt uses this wrapper only when the list is nonempty.
def referenceEntries (ls : LayerTerms NativeOp) : List Table.Entry :=
  (Node.addresses (.layers ls)).map fun r =>
    match ls with
    | .nil => ⟨2 :: r, none, none⟩
    | .cons _ _ =>
      let n := Node.eff (adapter ls)
      let env := n.envAt sig (.env []) (0 :: 0 :: r)
      ⟨2 :: r, env, match n.at_ (0 :: 0 :: r), env with
        | some (.eff q), some (.env tys) => some (Checker.check sig tys (2 :: r) q)
        | _, _ => none⟩

-- One existing annotator supplies the entries. No second checker is needed.
def candidateEntries (ls : LayerTerms NativeOp) : List Table.Entry :=
  match ls with
  | .nil => [⟨[2], none, none⟩]
  | .cons _ _ => (Annotate.checkLayers sig [2] ls).1

def samples : List (LayerTerms NativeOp) :=
  [.nil, one unitP, one badP, one bindP, one callP, one releaseP,
   .cons (.effectDiscard badP) (one unitP),
   .cons (.merge (.effectDiscard unitP) (.effectDiscard bindP)) .nil,
   .cons (.ref [2, 0]) .nil]

#guard samples.all fun ls => candidateEntries ls == referenceEntries ls
#guard samples.all fun ls => (candidateEntries ls).map (·.path) ==
  (Node.addresses (.layers ls)).map (2 :: ·)
#guard candidateEntries .nil == [⟨[2], none, none⟩]
#guard (Annotate.checkLayers sig [2] (.nil : LayerTerms NativeOp)).1 != candidateEntries .nil
#guard (Checker.checkLayers sig [2] (.nil : LayerTerms NativeOp)).isOk
#guard !(Checker.check sig [] [] (adapter .nil)).isOk
#guard (candidateEntries (one unitP)).any fun e => e.path == [2,0,0] && e.result.isSome
#guard (candidateEntries (one unitP)).all fun e => e.path.head? == some 2
#guard (Node.eff (adapter (one bindP))).at_ [0,0,0,0,1] ==
  (Node.layers (one bindP)).at_ [0,0,1]
#guard callAt sig [] (adapter (one callP)) [0,0,0,0] == callAt sig [] callP []
#guard (callAt sig [] callP []).isSome
#guard (Node.eff (adapter (one unitP))).replaceAt [0,0,0,0] (.eff bindP) ==
  some (.eff (adapter (one bindP)))
#guard (Node.layers (one unitP)).replaceAt [0,0] (.eff bindP) == some (.layers (one bindP))

-- Renaming only entry paths leaves refusals pointing inside the temporary wrapper.
def renameOnly (ls : LayerTerms NativeOp) : List Table.Entry :=
  (Annotate.check sig [] [] (adapter ls)).1.filterMap fun e =>
    match e.path with
    | 0 :: 0 :: r => some { e with path := 2 :: r }
    | _ => none
#guard renameOnly (one unitP) == candidateEntries (one unitP)
#guard renameOnly (one badP) != candidateEntries (one badP)
#guard (candidateEntries (one badP)).any fun e =>
  match e.result with
  | some (.error r) => r.path == [2,0,0]
  | _ => false
#guard (renameOnly (one badP)).any fun e =>
  match e.result with
  | some (.error r) => r.path == [0,0,0,0]
  | _ => false

#guard (Checker.check sig [] [] releaseP).isOk
#guard (candidateEntries (one releaseP)).any fun e =>
  e.path == [2,0,0,0,1] && e.env == some (.env [.nat, .exitOf .unknown .unknown])
#guard ((callAt sig [] callP []).map fun c => (c.request, c.answer)) == some (.nat, .refOf .nat)
#guard (candidateEntries (.cons (.effectDiscard badP) (one unitP))).any fun e =>
  e.path == [2,1,0,0] && e.result == some (.ok (EffTy.pure .unit))

#eval samples.length
#eval samples.foldl (fun n ls => n + (candidateEntries ls).length) 0
end ModuleLayerPartsReview
