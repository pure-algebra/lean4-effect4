import Tools.View.Tube.Draw
import Whatwg.Html.Node.SvgBoard

/-!
# Tools.View.Tube.Board.Film

Fixed structures draw once. Their scalar channels use the kit's changes-only writer.
The public boundary checks each key's tube and filled outline fields across snapshots.
This writer supplies no path interpolation or observation of store events.
-/

namespace Tools.View.Tube.Board
open Tools.View Whatwg.Html

/-- A mark at a snapshot, selected by its existing key. -/
def atKey (marks : List Mark) (key : String) : Option Mark :=
  marks.find? (·.key == key)

/-- One scalar channel over existing snapshots. -/
def channel {α : Type} (frames : List (List Mark)) (key : String)
    (read : Option Mark → α) : List α :=
  frames.map fun frame => read (atKey frame key)

/-- The invariant rendering fields; stroke width and dash remain scalar channels. -/
def sameStructure (before after : Mark) : Bool :=
  before.tube == after.tube && before.fromEnd == after.fromEnd &&
    before.layer == after.layer && before.tone == after.tone &&
    before.fill == after.fill && before.level == after.level &&
    before.round == after.round && before.roundStart == after.roundStart &&
    (before.fill == .stroke || (before.width == after.width && before.dash == after.dash))

/-- A located refusal for a repeated key or a changed invariant rendering field. -/
def structureIssue (frames : List (List Mark)) : Option String :=
  let all := frames.flatten
  frames.zipIdx.findSome? fun (frame, index) =>
    frame.findSome? fun mark =>
      if frame.countP (·.key == mark.key) > 1 then
        some s!"snapshot[{index}].{mark.key}: the key occurs more than once"
      else match atKey all mark.key with
      | some first => if sameStructure first mark then none else
          some s!"snapshot[{index}].{mark.key}: invariant rendering fields change"
      | none => some s!"snapshot[{index}].{mark.key}: the mark has no first occurrence"

/-- Admit only distinct keys and fixed rendering structures across all snapshots. -/
def check (frames : List (List Mark)) : Except String Unit :=
  match structureIssue frames with
  | none => .ok ()
  | some why => .error why

/-- A stroke with no dash has the SVG dash-array keyword `none`. -/
def dashArray : Option (Int × Nat) → String
  | none => "none"
  | some dash => (dashText dash).1

/-- A stroke with no dash has zero dash offset. -/
def dashOffset : Option (Int × Nat) → String
  | none => "0"
  | some dash => (dashText dash).2

/-- A fixed path placed by reference, with the mark's scalar attributes. -/
def reference (ident : String) (part : Part) (mark : Mark) (anims : List SvgNode) : SvgNode :=
  let attrs := [.attr .href ("#" ++ ident), .className ("tube-" ++ part.tone.name)]
  let paint := if part.filled then [.fill .currentColor] else
      [.fill .none, .stroke .currentColor, .strokeWidth (.fixed 3 mark.width),
        .strokeLinecap (if mark.round then .round else .butt), .strokeLinejoin .round] ++
        match mark.dash with
        | some dash => let (a, o) := dashText dash
                       [.attr .stroke_dasharray a, .attr .stroke_dashoffset o]
        | none => []
  .element .use (attrs ++ paint) anims

/-- The fixed paths with only changed opacity, width, and dash values written on ticks. -/
private def uncheckedFilm (id : String) (W H : Nat) (frames : List (List Mark))
    (beat : Nat := 1000) : SvgNode :=
  let all := frames.flatten
  let marks := (all.map (·.key)).eraseDups.filterMap (atKey all)
  let paths := (marks.flatMap fun m => m.parts.map fun p => p.d m).eraseDups
  let defs := paths.zipIdx.map fun (path, k) => pathDef s!"{id}-p{k}" path []
  let play : Smil.Play := { beat, replay := some id }
  let write (key attr : String) (read : Option Mark → String) : List SvgNode :=
    Smil.marking play 0 beat attr (channel frames key read)
  let nodes := (List.range (depth marks + 1)).flatMap fun lv =>
    (List.range LAYERS).flatMap fun layer =>
      (marks.filter (·.level == lv)).flatMap fun m =>
        (m.parts.filter (·.layer == layer)).map fun p =>
          let shown := channel frames m.key fun seen => if seen.isSome then "1" else "0"
          let anims := if p.filled then [] else
            write m.key "stroke-width" (fun seen => num (seen.getD m).width) ++
            write m.key "stroke-dasharray"
              (fun seen => dashArray (seen.getD m).dash) ++
            write m.key "stroke-dashoffset"
              (fun seen => dashOffset (seen.getD m).dash)
          .element .g [.attr .opacity (shown.headD "0")]
            (Smil.marking play 0 beat "opacity" shown ++
              [reference s!"{id}-p{(paths.idxOf? (p.d m)).getD 0}" p m anims])
  Svg.Frame.svg { width := W, height := H, ratio := 1 }
    [.className "tube-view", .ident id] (Svg.defs defs :: nodes)

/-- Write a changes-only film after checking its fixed-structure admission. -/
def film (id : String) (W H : Nat) (frames : List (List Mark))
    (beat : Nat := 1000) : Except String SvgNode := do
  check frames
  return uncheckedFilm id W H frames beat

-- A repeated snapshot writes no scalar animation; an absent key changes its opacity.
#guard (Smil.changesOf (channel [[], [], []] "missing"
  (fun seen => if seen.isSome then (1 : Nat) else 0))).length == 1
#guard channel [[unitOf "one" (straight 0 0 0 10000 40000) 20000], []] "one"
  (fun seen => seen.isSome) == [true, false]

-- A changed path cannot silently retain the first path under the same key.
#guard
  let before := unitOf "one" (straight 0 0 0 10000 40000) 20000
  let after := { before with tube := straight 0 0 0 10000 50000 }
  !(check [[before], [after]]).isOk
-- A repeated key cannot silently select its first occurrence.
#guard
  let mark := unitOf "one" (straight 0 0 0 10000 40000) 20000
  !(check [[mark, mark]]).isOk

-- An undashed stroke becomes dashed and returns to an undashed stroke.
#guard
  let mark := { unitOf "one" (straight 0 0 0 10000 40000) 20000 with dash := none }
  let dashed := { mark with dash := some (20000, 10000) }
  let frames := [[mark], [dashed], [mark]]
  (check frames).isOk &&
    channel frames "one" (fun seen => dashArray (seen.getD mark).dash) ==
      ["none", "10 100000", "none"] &&
    channel frames "one" (fun seen => dashOffset (seen.getD mark).dash) == ["0", "-20", "0"]

end Tools.View.Tube.Board
