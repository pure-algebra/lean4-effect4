import Tools.View.Glyph
import Tools.View.Grid
import Tools.View.Organic
import Whatwg.Svg.Scene.Layout

/-!
# Tools.View.Cell — a value drawn by its type (VS-2, decisions row 367)

The picture of a value is a fold of its type (row 367, point 1). `typed` is a `TyAlgebra` whose
carrier is a reader: a function from a value to its picture, or to nothing when the value does not
fit the type. A value that the type does not read is drawn raw by `raw`, a `ValAlgebra` over the
value's own tags. Each constructor's mark is its row of `Tools.View.Glyph.table` (the sorts `type`
and `value`).

**The composition grammar.** The parts sit together by four rules, and `problems` checks the
first two of every picture:

1. *One row grid.* Every part is whole rows high, and its first line stands on its row's
   baseline, so the text of every part of a row shares one baseline.
2. *No container draws a frame.* Space and alignment group the parts. Only a body or a vessel
   keeps an outline: the deferred's dot, the handle's tag.
3. *Tone carries the hierarchy* (Bertin's value). Data is in the ink: a literal, an identity's
   numeral. A label and a structure mark are muted: a field's name, a list's front, an option's
   shelf.
4. *One reading direction.* A record is a system of rows, its names once in a muted column at the
   left, like the staves of a score. A list is a lane read from its front, a thin tick, with its
   elements left to right. A list of records is a group of rows whose columns are its elements:
   the field names once at the left, each element a column, the first at the front.

The parts are put together by lean4-whatwg's layout (`Whatwg.Svg.Scene.Layout`, S22): each part
is laid out at its origin, and whatever holds it moves it into place. A keyed call moves by an
instance of the package's `Moves`. Each call is keyed by the path of the part it draws: a field's
name, a list's position. Each part names its mark, so a step's motion reads the part's kind
(`Shape.kind`) from the picture. A position keys a list's element here; the next slice (VS-3)
keys an element that holds an identity by that identity.
-/

namespace Tools.View
open Whatwg.Svg.Scene (Moves IVec)

/-- **A keyed call moves by whole logical pixels**, on both axes: so a picture of calls is laid
out by the package's `Layout`, and its laws hold of it. -/
instance : Moves IVec (Keyed Call) where
  move d c := c.move d.x d.y
  move_zero c := by
    cases c
    simp only [Keyed.move, Whatwg.Svg.Scene.IVec.zero_x, Whatwg.Svg.Scene.IVec.zero_y, Call.move_zero]
  move_move d e c := by
    cases c
    simp only [Keyed.move, Call.move_move, Whatwg.Svg.Scene.IVec.add_x, Whatwg.Svg.Scene.IVec.add_y]

end Tools.View

namespace Tools.View.Cell
open Effect4 Effect4.Program Tools.View
open Tools.View.Glyph (Shape)
open Whatwg.Svg.Scene (Layout)

/-- A value of the machine's stores. -/
abbrev Val := Effect4.Store.Val

/-- A layout of keyed calls. -/
abbrev Lay := Layout (Keyed Call)

/-- **A picture laid out at its origin**: its layout, and the mark of each part it draws, by the
part's key. -/
structure Fig where
  lay : Lay
  marks : List (Key × Shape) := []

namespace Fig

def w (f : Fig) : Nat := f.lay.w
def h (f : Fig) : Nat := f.lay.h

/-- The picture's keys under the part `k`: the picture's own key becomes `k`. -/
def under (k : String) (f : Fig) : Fig :=
  let re (key : Key) : Key := if key.isEmpty then k else k ++ "/" ++ key
  ⟨f.lay.map fun c => ⟨re c.key, c.call⟩, f.marks.map fun (key, s) => (re key, s)⟩

end Fig

/-! ## The grid of a value picture, in logical pixels -/

/-- A character of the data face, and a row. -/
def CW : Nat := CELL.toNat
def RH : Nat := ROWH.toNat
/-- The gap between two parts of a row: two cells. -/
def GAP : Nat := 2 * CW
/-- The room a list's front takes before its first element. -/
def FRONT : Nat := CW
/-- The width of a name in the label face, at most this many pixels a character. -/
def LABEL_ADVANCE : Nat := 6

/-- A height rounded up to whole rows: every part ends on the row grid (rule 1). -/
def snap (h : Nat) : Nat := (h + RH - 1) / RH * RH

/-- The same layout in a room of whole rows. -/
def rows (l : Lay) : Lay := ⟨l.w, snap l.h, l.items⟩

/-- A name in the label face, on the baseline of the row at `y`. -/
def labelAt (key : Key) (x y : Nat) (s : String) : Keyed Call :=
  ⟨key, .text .label x (y + BASE) (LABEL_ADVANCE * s.length) s⟩

/-- The width of the widest of some names. -/
def labelWidth (names : List String) : Nat := names.foldl (fun m n => max m (LABEL_ADVANCE * n.length)) 0

/-- A frame with round corners, `weight` thousandths of a pixel thick inside its box, in a role. -/
def ringAt (role : Role) (x y w h r : Int) (weight : Int := 1000) : Keyed Call :=
  ⟨"", .shape role 1000 (Grow.ring (1000 * x) (1000 * y) (1000 * w) (1000 * h) (1000 * r) weight)⟩

/-- A list's front: a thin tick in the rule's tone, down the rows of the list. -/
def front (h : Nat) : Lay := ⟨1, h, [⟨"", Call.vrule .rule 0 4 (h - 8) 1⟩]⟩

/-! ## The parts -/

/-- One part: its room and its calls, with the mark it draws. -/
def leaf (w h : Nat) (calls : List (Keyed Call)) (s : Shape) : Fig := ⟨⟨w, h, calls⟩, [("", s)]⟩

/-- **A literal**, in the data face: one cell a character, one row high. -/
def atom (s : String) : Fig :=
  leaf (CW * s.length) RH [⟨"", .cells 0 BASE s.length s⟩] .atom

/-- **A deferred's handle**: its numeral in the hollow dot, which stretches to a pill for a long
numeral. It stays hollow: a cell does not say whether the deferred is resolved. -/
def promise (n : Nat) : Fig :=
  let s := toString n
  let w := max 18 (CW * s.length + 8)
  leaf w RH [ringAt .ink 0 3 w 18 9, ⟨"", .cells (((w - CW * s.length) / 2 : Nat) : Int) BASE s.length s⟩]
    .hollowDot

/-- **A handle**: its numeral on a tag. -/
def tag (s : String) : Fig :=
  let w := CW * s.length + 8
  leaf w RH [ringAt .rule 0 4 w 16 2, ⟨"", .cells 4 BASE s.length s⟩] .tag

/-- The parts of a row, each under its position. -/
def positioned (items : List Fig) : List Fig := items.zipIdx.map fun (f, i) => f.under (toString i)

/-- **A list**: a lane read from its front, the thin tick, with its elements left to right, two
cells apart. An empty list is its front alone. -/
def lane (items : List Fig) : Fig :=
  let parts := positioned items
  let h := snap (parts.foldl (fun m f => max m f.h) RH)
  ⟨Layout.beside (if parts.isEmpty then 0 else FRONT) (front h) (Layout.row GAP (parts.map (rows ·.lay))),
   ("", .cells) :: parts.flatMap (·.marks)⟩

/-- **A list of records**: a group of rows, one for each field, the field names once in a muted
column at the left, then the front, then each element a column, the first at the front. A field
an element lacks leaves its place empty. -/
def grid (heads : List String) (elements : List (List (String × Fig))) : Fig :=
  let cols := elements.zipIdx.map fun (fs, i) => fs.map fun (n, f) => (n, (f.under n).under (toString i))
  let heights := heads.map fun n =>
    snap (cols.foldl (fun m fs => max m (((fs.lookup n).map (·.h)).getD RH)) RH)
  let tops := (heights.foldl (fun (y, out) h => (y + h, out ++ [y])) (0, ([] : List Nat))).2
  let total := heights.foldl (· + ·) 0
  let labels : Lay := ⟨labelWidth heads, total, (heads.zip tops).map fun (n, y) => labelAt "" 0 y n⟩
  let column (fs : List (String × Fig)) : Lay :=
    Layout.column 0 ((heads.zip heights).map fun (n, h) =>
      match fs.lookup n with
      | some f => ⟨f.w, h, f.lay.items⟩
      | none => ⟨0, h, []⟩)
  ⟨Layout.beside GAP labels (Layout.beside FRONT (front total) (Layout.row GAP (cols.map column))),
   ("", .cells) :: cols.flatMap (·.flatMap (·.2.marks))⟩

/-- **A tuple**: its parts in a row, four cells apart, each under its position. -/
def seq (items : List Fig) : Fig :=
  let parts := positioned items
  ⟨Layout.row (2 * GAP) (parts.map (rows ·.lay)), ("", .cells) :: parts.flatMap (·.marks)⟩

/-- **A record**: a system of rows, one for each field, the names once in a muted column at the
left and each field's picture on its row, under its name. -/
def system (fields : List (String × Fig)) : Fig :=
  let parts := fields.map fun (n, f) => (n, f.under n)
  let lw := labelWidth (parts.map (·.1)) + GAP
  let ls := parts.map fun (n, f) => Layout.beside 0 ⟨lw, snap f.h, [labelAt n 0 0 n]⟩ (rows f.lay)
  ⟨if ls.isEmpty then ⟨0, RH, []⟩ else Layout.column 0 ls, ("", .panel) :: parts.flatMap (·.2.marks)⟩

/-- **An option**: a low shelf in the rule's tone, empty or holding the value's picture under
`some`. -/
def slot (inner : Option Fig) : Fig :=
  let f := (inner.map (·.under "some")).getD ⟨⟨CW, RH, []⟩, []⟩
  let body := rows (Layout.inset 2 0 2 0 f.lay)
  let shelf : List (Keyed Call) :=
    [⟨"", Call.vrule .rule 0 (body.h - 7) 4 1⟩, ⟨"", Call.hrule .rule 0 (body.h - 3) body.w 1⟩,
     ⟨"", Call.vrule .rule (body.w - 1) (body.h - 7) 4 1⟩]
  ⟨Layout.over ⟨body.w, body.h, shelf⟩ body, ("", .slot) :: f.marks⟩

/-- **An exit**: the final bar ‖, then what follows it under `after`. -/
def exitBar (f : Fig) : Fig :=
  let f := f.under "after"
  let bars : Lay := ⟨CW, RH, [⟨"", Call.vrule .ink 0 4 16 1⟩, ⟨"", Call.vrule .ink 3 4 16 2⟩]⟩
  ⟨Layout.beside CW bars (rows f.lay), ("", .exitBar) :: f.marks⟩

/-! ## The composition grammar, checked -/

/-- **What a picture breaks of the composition grammar**, in words: a text off the row grid
(rule 1), and a frame drawn by a container (rule 2). None for a picture that keeps it. -/
def problems (f : Fig) : List String :=
  let markOf (k : Key) : Option Shape := (f.marks.find? (·.1 == k)).map (·.2)
  f.lay.items.filterMap fun c => match c.call with
    | .cells _ base _ _ | .text _ _ base _ _ =>
      if (base - BASE) % ROWH != 0 then some s!"off the row grid: {c.key}" else none
    | .shape _ _ _ =>
      if (markOf c.key).any (·.kind == .container) then some s!"a container drawn by a frame: {c.key}" else none
    | _ => none

/-! ## The two algebras -/

/-- A part as a reader answers it: its picture, and a record's fields drawn one by one, so a
list of records can set them in columns. -/
structure Pic where
  fig : Fig
  fields : Option (List (String × Fig)) := none

/-- A negative integer as the value writes it: `negInt n` is `-(n + 1)`. -/
def negative (n : Nat) : String := s!"-{n + 1}"

/-- A list's picture: a grid when every element is a record, a lane otherwise. -/
def listOf (ps : List Pic) : Fig :=
  match ps.mapM (·.fields) with
  | some (fs :: rest) => grid (fs.map (·.1)) (fs :: rest)
  | _ => lane (ps.map (·.fig))

/-- **A value drawn raw**, by its own tags: where no type reads it. -/
def raw : Store.ValAlgebra (fun _ => Fig) where
  val_unit := atom "()"
  val_bool b := atom (toString b)
  val_nat n := atom (toString n)
  val_str s := atom s.quote
  val_bytes bs := atom s!"{bs.length} bytes"
  val_list xs := lane xs
  val_pair a b := seq [a, b]
  val_none := slot none
  val_some a := slot (some a)
  val_ctor i args := system (("ctor", atom (toString i)) :: args.zipIdx.map fun (a, j) => (toString j, a))
  val_ref _ _ := tag "node"
  val_handle _ n := tag (toString n)
  val_negInt n := atom (negative n)
  val_float _ := atom "float"

/-- A value drawn raw. -/
def drawRaw (v : Val) : Fig := Store.cata_val raw v

/-- A reader: a value's picture at a type, or none when the value does not fit it. -/
abbrev Reader := Val → Option Pic

/-- A part that is no record. -/
def part (f : Fig) : Option Pic := some ⟨f, none⟩

/-- **A value drawn by its type**: one reader for each constructor of `Ty`. A record reads its
fields by name, in the type's order; a missing field is an empty shelf where the type marks it
optional, and otherwise the record does not fit. A union reads by its first arm that fits. -/
def typed : TyAlgebra (fun _ => Reader) where
  ty_never := fun _ => none
  ty_unit := fun | .unit => part (atom "()") | _ => none
  ty_nat := fun | .nat n => part (atom (toString n)) | _ => none
  ty_int := fun | .nat n => part (atom (toString n)) | .negInt n => part (atom (negative n)) | _ => none
  ty_string := fun | .str s => part (atom s.quote) | _ => none
  ty_bool := fun | .bool b => part (atom (toString b)) | _ => none
  ty_handle := fun _ => fun | .handle _ n => part (tag (toString n)) | _ => none
  ty_option := fun r => fun
    | .none => part (slot none)
    | .some x => (r x).bind fun p => part (slot (some p.fig))
    | _ => none
  ty_list := fun r => fun | .list xs => (xs.mapM r).bind fun ps => part (listOf ps) | _ => none
  ty_prod := fun a b => fun
    | .list [x, y] | .pair x y => do part (seq [(← a x).fig, (← b y).fig])
    | _ => none
  ty_except := fun a b => fun | .ctor 0 [x] => a x | .ctor 1 [x] => b x | _ => none
  ty_exitOf := fun a _ => fun
    | .ctor 0 [x] => (a x).bind fun p => part (exitBar p.fig)
    | .ctor 1 [c] => part (exitBar (drawRaw c))
    | _ => none
  ty_causeOf := fun _ v => part (drawRaw v)
  ty_fiberOf := fun _ _ => fun | .handle 1 n => part (tag (toString n)) | _ => none
  ty_union := fun a b v => (a v).orElse fun _ => b v
  ty_lit := fun s => fun | .str t => if t == s then part (atom t.quote) else none | _ => none
  ty_refOf := fun _ => fun | .handle 2 n => part (tag (toString n)) | _ => none
  ty_deferredOf := fun _ _ => fun | .handle 3 n => part (promise n) | _ => none
  ty_var := fun _ v => part (drawRaw v)
  ty_unknown := fun v => part (drawRaw v)
  ty_record := fun fields v => do
    let entries ← Machine.Record.entries v
    let rows ← fields.mapM fun (name, optional, r) =>
      match entries.lookup name with
      | some x => (r x).map fun p => (name, p.fig)
      | none => if optional then some (name, slot none) else none
    pure ⟨system rows, some rows⟩
  ty_map := fun _ r v => do
    let entries ← Machine.Map.read v
    part (system (← entries.mapM fun (k, x) => (r x).map fun p => (k, p.fig)))
  ty_tuple := fun rs => fun
    | .list xs =>
      if xs.length == rs.length then
        ((rs.zip xs).mapM fun (p : Reader × Val) => p.1 p.2).bind fun ps => part (seq (ps.map (·.fig)))
      else none
    | _ => none
  ty_app := fun _ _ v => part (drawRaw v)
  ty_null := fun v => part (drawRaw v)
  ty_undefined := fun v => part (drawRaw v)
  ty_number := fun
    | .nat n => part (atom (toString n))
    | .negInt n => part (atom (negative n))
    | .float _ => part (atom "float")
    | _ => none
  ty_bytes := fun | .bytes bs => part (atom s!"{bs.length} bytes") | _ => none
  ty_contextOf := fun _ v => part (drawRaw v)

/-- Whether the type reads the value: the value fits the type, as the picture draws it. -/
def reads (t : Ty) (v : Val) : Bool := (cata_ty typed t v).isSome

/-- **A value's picture at a type**: the type's reading, or the value drawn raw where the type
does not read it. -/
def draw (t : Ty) (v : Val) : Fig := ((cata_ty typed t v).map (·.fig)).getD (drawRaw v)

end Tools.View.Cell
