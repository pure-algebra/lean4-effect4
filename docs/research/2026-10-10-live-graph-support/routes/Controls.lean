import Tools.View.Graph

namespace RouteControls
open Tools.View

/-- A point with zero height. -/
def point (key : Key) (y : Int) : Placed := { key, x := 0, y, w := 0 }

/-- A box with the existing view height. -/
def box (key : Key) (y : Int) : Placed :=
  { key, x := 0, y, w := 20, node := some { key, line1 := "" } }

/-- A layout with one downward route. -/
def chain (ps : Array Placed) (ks : List Key) : Laid :=
  { placed := ps, routes := #[.down "chain" ks] }

def valid : Laid := chain #[box "a" 0, point "b" 100, box "c" 200] ["a", "b", "c"]
def inverted : Laid := chain #[point "a" 0, point "b" 100, point "c" 50] ["a", "b", "c"]
def missing : Laid := chain #[point "a" 0, point "c" 200] ["a", "b", "c"]
def boundary : Laid :=
  chain #[box "a" 0, point "b" (ROWH * BOXROWS), box "c" (ROWH * BOXROWS)] ["a", "b", "c"]

-- Finite evaluations: a valid long route and equality at both segment boundaries pass.
#guard valid.edgesDescend
#guard boundary.edgesDescend
-- Red controls: the retained baseline accepted both of these routes.
#guard !inverted.edgesDescend
#guard !missing.edgesDescend
-- Red controls: missing initial and final keys fail whenever a segment uses them.
#guard !(chain #[point "b" 100, point "c" 200] ["a", "b", "c"]).edgesDescend
#guard !(chain #[point "a" 0, point "b" 100] ["a", "b", "c"]).edgesDescend
-- Existing two-key behavior stays: valid, inverted, and missing pairs.
#guard (chain #[point "a" 0, point "b" 100] ["a", "b"]).edgesDescend
#guard !(chain #[point "a" 100, point "b" 0] ["a", "b"]).edgesDescend
#guard !(chain #[point "a" 0] ["a", "b"]).edgesDescend
-- Routes without segments pass, including a missing singleton key.
#guard (chain #[] []).edgesDescend
#guard (chain #[] ["absent"]).edgesDescend
#guard ({} : Laid).edgesDescend
-- Back and loop routes remain outside this downward-only check.
#guard ({ routes := #[.back "back" "absent1" "absent2" 0, .loop "loop" "absent"] } : Laid).edgesDescend
-- Duplicate keys use the same first occurrence as drawing lookup.
#guard (chain #[point "a" 0, point "a" 1000, point "b" 100, point "c" 200]
  ["a", "b", "c"]).edgesDescend
#guard !(chain #[point "a" 1000, point "a" 0, point "b" 100, point "c" 200]
  ["a", "b", "c"]).edgesDescend
-- Dimensions are a different finite check.
#guard (chain #[point "a" (-100), point "b" (-50)] ["a", "b"]).edgesDescend
#guard !(chain #[point "a" (-100), point "b" (-50)] ["a", "b"]).dimsValid
-- One failing downward route rejects the whole layout, beside a passing route.
#guard !({ valid with routes := #[.down "valid" ["a", "b", "c"],
  .down "inverted" ["c", "b", "a"]] } : Laid).edgesDescend

-- Reader: a successful whole-layout check gives the last adjacent segment at this real layout.
example : boundary.segmentDescends "b" "c" = true :=
  Laid.edgesDescend_down_pairs boundary rfl "chain" ["a", "b", "c"] 1000 1000000
    List.mem_cons_self ("b", "c") (List.mem_cons_of_mem _ List.mem_cons_self)

#eval IO.println s!"ROUTES valid={valid.edgesDescend}, boundary={boundary.edgesDescend}, inverted={inverted.edgesDescend}, missing={missing.edgesDescend}"
end RouteControls
