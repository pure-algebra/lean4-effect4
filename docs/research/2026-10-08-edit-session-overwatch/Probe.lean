import Effect4.Author
import Effect4.Library
import Effect4.Program.Edit
import Test.Program.EditControls

/-!
Review at fdbae937; production stays unchanged.
Placement: initial-algebras-folds, R14, edit-session-coherent.
The candidate changes only when the fallback computation executes.
Its equality example connects the candidate to the existing feed and its registered laws.
Observation: the returned session and delta, for every session and edit, without extra premises.
It establishes no cost, rendering, transport, or program-execution theorem.
The finite controls serve the proposed repair and the future address-delta consumer.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace EditOverwatch
open Effect4 Effect4.Program Effect4.Program.Authoring
open Test.Program.EditControls
open Test.Program.SketchControls Test.Program.SpliceControls

/-- Review-only candidate: defer the full annotation until a fallback branch selects it. -/
def feedDeferred {Op : Type} (l : EditSession Op) : Edit Op → EditSession Op × Edit.Delta
  | .replace a q =>
    match (Node.eff l.program).replaceAt a (.eff q) with
    | some (.eff p') =>
      let rechecked : Unit → EditSession Op × Edit.Delta := fun _ =>
        ({ l with program := p', table := annotate l.sig l.env p' }, .rechecked)
      match Table.typedAt l.table [], Table.typedAt l.table a with
      | some _, some (tys, ty) =>
        match Annotate.check l.sig tys a q with
        | (sub, .ok ty') =>
          if ty' = ty then
            ({ l with program := p', table := Table.splice l.table a sub },
              .spliced (sub.map (·.path)))
          else rechecked ()
        | (_, .error _) => rechecked ()
      | _, _ => rechecked ()
    | _ => (l, .unchanged)

-- A kernel-checked equality reader: all existing feed results and laws remain applicable.
example {Op : Type} (l : EditSession Op) (e : Edit Op) : feedDeferred l e = l.feed e := rfl

#guard (feedDeferred opened keep).2 = .spliced [[0]]
#guard (feedDeferred opened change).2 = .rechecked
#guard (feedDeferred opened change).1.view.refusals.length = 1
#guard (feedDeferred opened (.replace [7] (.succeed (.lit (.nat 6))))).2 = .unchanged

/-- A shape-growing edit has the same answer type. -/
def expanded := (opened.feed (.replace [0] (.suspend (.succeed (.lit (.nat 6)))))).1
#guard expanded.table.length = 8
#guard expanded.view.type = opened.view.type
#guard expanded.table.any (fun e => e.path == [0, 0])

/-- A shape-shrinking edit deletes an old address outside the returned new-address list. -/
def shrunk := expanded.feed keep
#guard shrunk.2 = .spliced [[0]]
#guard shrunk.1.table.length = 7
#guard !(shrunk.1.table.any (fun e => e.path == [0, 0]))
#guard !(shownOf shrunk.2).any (fun ps => ps.contains [0, 0])

/-- Build a concrete module caller through the public author surface. -/
def semaphoreClient : Src NativeOp :=
  bindWith (Semaphore.make 2) fun q => Semaphore.takeIfAvailable q (nat 1)

/-- Wrap the public caller without changing its checked result type. -/
def moduleSplices : Bool :=
  match Api.Author.program semaphoreClient with
  | .error _ => false
  | .ok built =>
    let opened := EditSession.open (nativeSignature built.table) [] built.program
    let (next, delta) := feedDeferred opened (.replace [] (.suspend built.program))
    match delta with
    | .spliced _ => next.view.type == opened.view.type && next.view.refusals.isEmpty
    | _ => false
#guard moduleSplices

-- A stored signature retains already-declared holes for sequential filling.
def holeSession := EditSession.open (({} : SigApp).withHoles (sketchAt .nat).holes).signature [] (sketchAt .nat).program
#guard holeSession.view.type.isSome
#guard (holeSession.feed keep).2 = .spliced [[0]]
#guard (EditSession.open ({} : SigApp).signature [] (sketchAt .nat).program).view.type.isNone

end EditOverwatch
