import Effect4.Laws.Program.AddressMove
import Test.Program.ReferenceExpansion

/-!
# Test.Program.AddressMove — a pasted subtree's references: the law at real programs, and why each premise stands

`references_move` (`src/Effect4/Laws/Program/AddressMove.lean`) is the law, the proposed claim
`references-move`: a subtree whose references stay inside it, pasted with `Node.rebaseRefs` at an
address outside the module's layers that has one scope, keeps the host's references well formed.
The programs are the reference battery's (`Test/Program/ReferenceExpansion.lean`): `oneRef` holds
one reference, at `[0, 1]`, to the layer at `[0, 0]`.

- **Seat ORG's probe, both ways** (finite evaluations; the theory map,
  `docs/research/2026-10-08-seat-ORG-theory-map.md` §3.3). Pasted under a `suspend` as it is, the
  reference keeps the target `[0, 0]`, which now names the merge that encloses it, and the program
  is refused at the reference (`encloses`). Pasted with its references moved, the target is
  `[0, 0, 0]`, and the program is well formed.
- **The reader**: the law applied at the same paste, every premise discharged at the real programs,
  and the scope premise read off `Eff.scopeOf_append`.
- **Four red controls**, one for each premise that a paste can break: a reference that leaves the
  subtree (`inner`), a host reference into the pasted address (`outside`), a paste into the
  module's layers (`hmod`), and a paste at a block's bodies, which has no one scope (`hscope`).
  Each source and host is well formed, and each result is refused at its own fault.

Placement. Each guard is a finite instance of the proposed claim `references-move` (concept
`initial-algebras-folds`, requirement R14) or of a premise's failure. The battery states nothing of
typing or of a run.
-/

set_option autoImplicit false

namespace Test.Program.AddressMove

open Effect4 Effect4.Program
open Test.Program.ReferenceExpansion (key leaf around oneRef moduleDecl)

/-- The host of seat ORG's probe: a `suspend` whose body the paste replaces, at `[0]`. -/
def host : NativeEff := .suspend (.succeed (.lit .unit))

/-- The probe's paste, as it is: the target `[0, 0]` stays. -/
def stale : Option (Node NativeOp) := (Node.eff host).replaceAt [0] (.eff oneRef)

/-- The probe's paste with the references moved: `Node.rebaseRefs [] [0]`. -/
def moved : Option (Node NativeOp) :=
  (Node.eff host).replaceAt [0] (Node.rebaseRefs [] [0] (.eff oneRef))

/-- The verdict of a pasted program: its first ill-formed reference, located. -/
def fault : Option (Node NativeOp) → Option (Option (List Nat × List Nat × RefFault))
  | some (.eff p) => some p.firstRefFault
  | _ => none

/-! ## Seat ORG's probe, both ways -/

#guard oneRef.layerRefsWF && host.layerRefsWF
-- As it is: the reference at `[0, 0, 1]` names `[0, 0]`, the merge that encloses it.
#guard fault stale = some (some ([0, 0, 1], [0, 0], .encloses))
-- Moved: the target is `[0, 0, 0]`, the layer it named in the source, and nothing is refused.
#guard moved = some (.eff (.suspend (around (.merge leaf (.ref [0, 0, 0])))))
#guard fault moved = some none

/-! ## The reader: the law at the probe's paste -/

example : (Eff.suspend (oneRef.rebaseRefs [] [0])).layerRefsWF = true :=
  references_move (root := oneRef) (host := host) (src := []) (dst := [0])
    (n := .eff oneRef) rfl (.inr rfl) rfl (fun x _ _ => ⟨x.2, rfl⟩) rfl
    (fun x hx => by
      rw [show host.refSites [] = [] from rfl] at hx
      cases hx)
    (List.cons_ne_nil 0 []) rfl
    (Eff.scopeOf_append (m := .eff (.succeed (.lit .unit))) rfl (fun _ h => nomatch h)
      (List.cons_ne_nil 0 []))
    rfl

/-! ## Red controls: each premise, broken -/

/-- `inner` broken: the source's layer `.fresh (.ref [0, 0])` at `[0, 1]` names `[0, 0]`, outside
it. Pasted at `[0, 0]` of a well-formed host, its reference keeps the target, which now encloses
it. -/
def leaving : NativeEff := around (.merge leaf (.fresh (.ref [0, 0])))

#guard leaving.layerRefsWF
#guard fault ((Node.eff (around (.merge leaf leaf))).replaceAt [0, 0]
    (Node.rebaseRefs [0, 1] [0, 0] (.layer (.fresh (.ref [0, 0]))))) =
  some (some ([0, 0, 0], [0, 0], .encloses))

/-- `outside` broken: the host's reference at `[0, 1]` names `[0, 0, 0]`, inside the address
`[0, 0]` that the paste replaces by a layer with no child. -/
def reaching : NativeEff := around (.merge (.fresh leaf) (.ref [0, 0, 0]))

#guard reaching.layerRefsWF
#guard fault ((Node.eff reaching).replaceAt [0, 0] (Node.rebaseRefs [0] [0, 0] (.layer leaf))) =
  some (some ([0, 1], [0, 0, 0], .noLayer))

/-- `hmod` broken: `oneRef`'s layer, with its inner reference, pasted as the module's first layer.
A reference may name only a whole module layer, and the moved target is a piece inside one. -/
def moduleHost : NativeEff :=
  .defs [moduleDecl] (.cons (.succeed (.var 0)) .nil) (.succeed (.lit (.nat 1))) (.cons leaf .nil)

#guard moduleHost.layerRefsWF
#guard fault ((Node.eff moduleHost).replaceAt [2, 0]
    (Node.rebaseRefs [0] [2, 0] (.layer (.merge leaf (.ref [0, 0]))))) =
  some (some ([2, 0, 1], [2, 0, 0], .otherScope))

/-- `hscope` broken: a race's entrants in one scope, the second naming the first's layer, pasted as
a block's bodies. There each entrant is a definition's body, so the reference crosses two scopes. -/
def racing : NativeEff :=
  .withFiber (.raceAll (.cons (.provideLayer leaf false (.service key))
    (.cons (.provideLayer (.ref [0, 0, 0, 0]) false (.service key)) .nil)))

/-- A block with two definitions, whose bodies the paste replaces. -/
def twoBodies : NativeEff :=
  .defs [moduleDecl, moduleDecl] (.cons (.succeed (.var 0)) (.cons (.succeed (.var 0)) .nil))
    (.succeed (.lit (.nat 1))) .nil

#guard racing.layerRefsWF && twoBodies.layerRefsWF
#guard (Node.eff racing).at_ [0, 0] = some (.effs (.cons (.provideLayer leaf false (.service key))
    (.cons (.provideLayer (.ref [0, 0, 0, 0]) false (.service key)) .nil)))
#guard twoBodies.scopeOf ([0] ++ [0]) = some 0 && twoBodies.scopeOf [0] = none
#guard fault ((Node.eff twoBodies).replaceAt [0] (Node.rebaseRefs [0, 0] [0]
    (.effs (.cons (.provideLayer leaf false (.service key))
      (.cons (.provideLayer (.ref [0, 0, 0, 0]) false (.service key)) .nil))))) =
  some (some ([0, 1, 0, 0], [0, 0, 0], .otherScope))

/-! ## A path relocated: the branch no theorem states -/

-- A path that is not below the base stays as it is; one below it moves.
#guard Path.rebase [0, 1] [5] [0, 0] = [0, 0] && Path.rebase [0, 1] [5] [0, 1, 2] = [5, 2]
#guard Path.below [0, 1] [0] = none && Path.below [0, 1] [0, 2, 3] = none

end Test.Program.AddressMove
