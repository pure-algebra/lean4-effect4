import ProbeView.Inc

open Effect4 Effect4.Program Tools.View

deriving instance BEq for Tools.View.Flow.Flow

namespace LiveWaitSiblingReview

def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def source : NativeEff := .withFiber (.fork (.succeed (.lit .unit)) later)
def old : NativeEff := .bind source (.awaitFiber (.var 0) .awaitValue)
def replacement : NativeEff := .bind (.yieldNow 0) source
def fresh : NativeEff := .bind replacement (.awaitFiber (.var 0) .awaitValue)
def oldSession := EditSession.open {} { program := old }
def edited := oldSession.feedStep (.fill [0] replacement)
def memo := Inc.Memo.next (Program.lines old) (Flow.waits old)

-- The actual edit keeps the source's type and takes the spliced path.
#guard oldSession.view.type.isSome
#guard (EditSession.open {} { program := fresh }).view.type.isSome
#guard match edited.2.delta with | .spliced _ => true | _ => false
#guard edited.1.sketch.program == fresh

-- Controls: no source change, and a fresh query without a memo.
#guard Inc.waits memo (some [0]) old == Flow.waits old
#guard Inc.waits memo none fresh == Flow.waits fresh

-- The await stays at [1], but the source at [0] changes its structural origin.
#guard Flow.waits old == [("[1]", ["[0 0]"])]
#guard Flow.waits fresh == []
#guard Inc.waits memo (some [0]) fresh == [("[1]", ["[0 0]"])]
#guard Inc.waits memo (some [0]) fresh != Flow.waits fresh

-- The text-cache premise still holds for the same edit.
#guard (Inc.lines memo (some [0]) fresh).map (fun n => (n.path, n.depth, n.text)) ==
  (Program.lines fresh).map (fun n => (n.path, n.depth, n.text))

-- Reverse edit: the stale cache now misses an edge that the fresh query finds.
def freshMemo := Inc.Memo.next (Program.lines fresh) (Flow.waits fresh)
#guard Inc.waits freshMemo (some [0]) old == []
#guard Inc.waits freshMemo (some [0]) old != Flow.waits old

-- A checked reverse edit produces a newly resolvable join.
def reverseSession := EditSession.open {} { program := fresh }
def reverseEdit := reverseSession.feedStep (.fill [0] source)
#guard match reverseEdit.2.delta with | .spliced _ => true | _ => false
#guard reverseEdit.1.sketch.program == old
#guard Flow.unresolvedWaits fresh == ["[1]"]
#guard Flow.unresolvedWaits old == []
#guard Inc.flow freshMemo (some [0]) old [] != Flow.ofProgram old
#guard match (Effect4.Program.Node.eff fresh).at_ [0, 0] with
  | some (.eff (.yieldNow 0)) => true
  | _ => false

-- Minimal repair candidate: recompute wait targets, retaining the text cache.
def recomputedWaits (_memo : Inc.Memo) (_edited : Option (List Nat))
    (program : NativeEff) := Flow.waits program
#guard recomputedWaits memo (some [0]) fresh == Flow.waits fresh
#guard recomputedWaits freshMemo (some [0]) old == Flow.waits old

#guard Inc.flow memo (some [0]) fresh (recomputedWaits memo (some [0]) fresh) == Flow.ofProgram fresh
#guard Inc.flow freshMemo (some [0]) old (recomputedWaits freshMemo (some [0]) old) == Flow.ofProgram old

#eval ("reverse edit delta", reverseEdit.2.delta)
#eval ("reverse cached flow equals fresh", Inc.flow freshMemo (some [0]) old [] == Flow.ofProgram old)
#eval ("old waits", Flow.waits old)
#eval ("fresh waits", Flow.waits fresh)
#eval ("cached waits after edit", Inc.waits memo (some [0]) fresh)
#eval ("edit delta", edited.2.delta)

end LiveWaitSiblingReview
