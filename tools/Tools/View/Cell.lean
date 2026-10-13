import Tools.View.Glyph
import Tools.View.Grid
import Tools.View.Organic
import Whatwg.Svg.Scene.Layout

/-!
# Tools.View.Cell — a value drawn by its type (VS-2, decisions row 367)

The picture of a value is a fold of its type (row 367, point 1). `typed` is a `TyAlgebra` whose
carrier is a reader: a function from a value to its picture, or to nothing when the value does not
fit the type. `cata_ty typed t` reads a value at `t`:

* a record is a panel of its fields, each drawn by its field's type;
* a list is a row of cells, the first at the left;
* a tuple is its parts side by side in a frame with round ends;
* an option is a cup, empty or holding;
* a deferred is the hollow dot with its numeral, a handle its numeral on a tag;
* a scalar is its literal.

A value that the type does not read is drawn raw by `raw`, a `ValAlgebra` over the value's own
tags. Each constructor's mark is its row of `Tools.View.Glyph.table` (the sorts `type` and
`value`).

The parts are put together by lean4-whatwg's layout (`Whatwg.Svg.Scene.Layout`, S22): each part
is laid out at its origin, and whatever holds it moves it into place (`beside`, `above`, `row`,
`column`, `inset`, `over`), so the room of a part does not depend on where it stands. A keyed
call moves by an instance of the package's `Moves`. Each call is keyed by the path of the part
it draws: a field's name, a list's position. Each part names its mark, so a step's motion can
read the part's kind (`Shape.kind`) from the picture. A position keys a list's element here; the
next slice (VS-3) keys an element that holds an identity by that identity.
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
/-- The room inside a cell: across, then down. -/
def PAD : Nat := 6
def RISE : Nat := 4
/-- The width of a name in the label face, at most this many pixels a character. -/
def LABEL_ADVANCE : Nat := 7

/-! ## The parts -/

/-- One part: its room and its calls, with the mark it draws. -/
def leaf (w h : Nat) (calls : List (Keyed Call)) (s : Shape) : Fig := ⟨⟨w, h, calls⟩, [("", s)]⟩

/-- A frame with round corners, `weight` thousandths of a pixel thick inside its box, in a role. -/
def ringAt (role : Role) (x y w h r : Int) (weight : Int := 1000) : Keyed Call :=
  ⟨"", .shape role 1000 (Grow.ring (1000 * x) (1000 * y) (1000 * w) (1000 * h) (1000 * r) weight)⟩

/-- Calls drawn at the room of a layout, before it. -/
def behind (l : Lay) (calls : List (Keyed Call)) : Lay := Layout.over ⟨l.w, l.h, calls⟩ l

/-- A part centred down a height (ask W15 of the asks to lean4-whatwg). -/
def middle (h : Nat) (l : Lay) : Lay :=
  let top := (h - l.h) / 2
  Layout.inset 0 top 0 (h - l.h - top) l

/-- The places where two parts in a row meet: the sum of the widths before each part but the
first. -/
def edges (sizes : List Nat) : List Nat :=
  (sizes.dropLast.foldl (fun (at_, out) s => (at_ + s, out ++ [at_ + s])) (0, ([] : List Nat))).2

/-- **A literal**, in the data face: one cell a character, one row high. -/
def atom (s : String) : Fig :=
  leaf (CW * s.length) RH [⟨"", .cells 0 BASE s.length s⟩] .atom

/-- **A deferred's handle**: its numeral in the hollow dot, which stretches to a pill for a long
numeral. It stays hollow: a cell does not say whether the deferred is resolved. -/
def promise (n : Nat) : Fig :=
  let s := toString n
  let w := max 20 (CW * s.length + 10)
  leaf w RH [ringAt .ink 0 2 w 20 10 1500, ⟨"", .cells (((w - CW * s.length) / 2 : Nat) : Int) BASE s.length s⟩]
    .hollowDot

/-- **A handle**: its numeral on a tag. -/
def tag (s : String) : Fig :=
  let w := CW * s.length + 2 * PAD
  leaf w RH [ringAt .ink 0 3 w 18 3, ⟨"", .cells PAD BASE s.length s⟩] .tag

/-- The parts of a row, each under its position, each in its cell's room at the height of the
tallest. -/
def boxes (items : List Fig) : List Fig × List Lay :=
  let parts := items.zipIdx.map fun (f, i) => f.under (toString i)
  let inner := parts.foldl (fun m f => max m f.h) RH
  (parts, parts.map fun f => Layout.inset PAD RISE PAD RISE (middle inner f.lay))

/-- **A list**: its elements in a row of cells, the first at the left, each under its position.
The cells touch, with a rule where two meet. An empty list is one empty cell. -/
def cells (items : List Fig) : Fig :=
  let (parts, bs) := boxes items
  if parts.isEmpty then leaf (2 * PAD + CW) (RH + 2 * RISE) [ringAt .rule 0 0 (2 * PAD + CW) (RH + 2 * RISE) 2] .cells else
  let row := Layout.row 0 bs
  let rules := (edges (bs.map (·.w))).map fun (x : Nat) => (⟨"", Call.vrule .rule x 0 row.h 1⟩ : Keyed Call)
  ⟨behind (Layout.over row ⟨row.w, row.h, rules⟩) [ringAt .rule 0 0 row.w row.h 2],
   ("", .cells) :: parts.flatMap (·.marks)⟩

/-- **A tuple**: its parts side by side, each under its position, in a frame whose corners are
rounder than a list's, at most a row's half. -/
def tuple (items : List Fig) : Fig :=
  let (parts, bs) := boxes items
  let row := Layout.inset PAD 0 PAD 0 (Layout.row 0 bs)
  ⟨behind row [ringAt .rule 0 0 row.w row.h (min (row.h / 2) (RH / 2))], ("", .cells) :: parts.flatMap (·.marks)⟩

/-- **A record**: a panel of its fields, one row each, ruled apart. The field's name is in the
label face at the left, and its picture at the right, under its name. -/
def panel (fields : List (String × Fig)) : Fig :=
  let parts := fields.map fun (n, f) => (n, f.under n)
  let nameW := parts.foldl (fun m (n, _) => max m (LABEL_ADVANCE * n.length)) 0
  let rows := parts.map fun (n, f) =>
    let name : Lay := ⟨PAD + nameW + 2 * PAD, max RH f.h,
      [⟨n, .text .label PAD BASE (LABEL_ADVANCE * n.length) n⟩]⟩
    Layout.inset 0 RISE PAD RISE (Layout.beside 0 name f.lay)
  let col := Layout.column 0 rows
  let rules := (edges (rows.map (·.h))).map fun (y : Nat) => (⟨"", Call.hrule .rule 0 y col.w 1⟩ : Keyed Call)
  let col : Lay := if rows.isEmpty then ⟨2 * PAD, RH, []⟩ else col
  ⟨behind (Layout.over col ⟨col.w, col.h, rules⟩) [ringAt .rule 0 0 col.w col.h 4],
   ("", .panel) :: parts.flatMap (·.2.marks)⟩

/-- **An option**: a cup, empty or holding the value's picture under `some`. Its walls rise a
third of its height and its top is open, so an empty cup is not an empty list's closed cell. -/
def slot (inner : Option Fig) : Fig :=
  let f := (inner.map (·.under "some")).getD ⟨⟨CW, RH, []⟩, []⟩
  let body := Layout.inset PAD 0 PAD RISE f.lay
  let top := body.h - body.h / 3
  let walls : List (Keyed Call) :=
    [⟨"", Call.vrule .rule 0 top (body.h - top) 1⟩, ⟨"", Call.hrule .rule 0 (body.h - 1) body.w 1⟩,
     ⟨"", Call.vrule .rule (body.w - 1) top (body.h - top) 1⟩]
  ⟨behind body walls, ("", .slot) :: f.marks⟩

/-- **An exit**: the final bar ‖, then what follows it under `after`. -/
def exitBar (f : Fig) : Fig :=
  let f := f.under "after"
  let bars : Lay := ⟨2 * PAD, RH, [⟨"", Call.vrule .ink 0 2 20 1⟩, ⟨"", Call.vrule .ink 3 2 20 2⟩]⟩
  ⟨Layout.beside 0 bars f.lay, ("", .exitBar) :: f.marks⟩

/-! ## The two algebras -/

/-- A negative integer as the value writes it: `negInt n` is `-(n + 1)`. -/
def negative (n : Nat) : String := s!"-{n + 1}"

/-- **A value drawn raw**, by its own tags: where no type reads it. -/
def raw : Store.ValAlgebra (fun _ => Fig) where
  val_unit := atom "()"
  val_bool b := atom (toString b)
  val_nat n := atom (toString n)
  val_str s := atom s.quote
  val_bytes bs := atom s!"{bs.length} bytes"
  val_list xs := cells xs
  val_pair a b := tuple [a, b]
  val_none := slot none
  val_some a := slot (some a)
  val_ctor i args := panel (("ctor", atom (toString i)) :: args.zipIdx.map fun (a, j) => (toString j, a))
  val_ref _ _ := tag "node"
  val_handle _ n := tag (toString n)
  val_negInt n := atom (negative n)
  val_float _ := atom "float"

/-- A value drawn raw. -/
def drawRaw (v : Val) : Fig := Store.cata_val raw v

/-- A reader: a value's picture at a type, or none when the value does not fit it. -/
abbrev Reader := Val → Option Fig

/-- **A value drawn by its type**: one reader for each constructor of `Ty`. A record reads its
fields by name, in the type's order; a missing field is an empty cup where the type marks it
optional, and otherwise the record does not fit. A union reads by its first arm that fits. -/
def typed : TyAlgebra (fun _ => Reader) where
  ty_never := fun _ => none
  ty_unit := fun | .unit => some (atom "()") | _ => none
  ty_nat := fun | .nat n => some (atom (toString n)) | _ => none
  ty_int := fun | .nat n => some (atom (toString n)) | .negInt n => some (atom (negative n)) | _ => none
  ty_string := fun | .str s => some (atom s.quote) | _ => none
  ty_bool := fun | .bool b => some (atom (toString b)) | _ => none
  ty_handle := fun _ => fun | .handle _ n => some (tag (toString n)) | _ => none
  ty_option := fun r => fun | .none => some (slot none) | .some x => (r x).map (slot ∘ some) | _ => none
  ty_list := fun r => fun | .list xs => (xs.mapM r).map cells | _ => none
  ty_prod := fun a b => fun
    | .list [x, y] | .pair x y => do pure (tuple [← a x, ← b y])
    | _ => none
  ty_except := fun a b => fun | .ctor 0 [x] => a x | .ctor 1 [x] => b x | _ => none
  ty_exitOf := fun a _ => fun
    | .ctor 0 [x] => (a x).map exitBar
    | .ctor 1 [c] => some (exitBar (drawRaw c))
    | _ => none
  ty_causeOf := fun _ v => some (drawRaw v)
  ty_fiberOf := fun _ _ => fun | .handle 1 n => some (tag (toString n)) | _ => none
  ty_union := fun a b v => (a v).orElse fun _ => b v
  ty_lit := fun s => fun | .str t => if t == s then some (atom t.quote) else none | _ => none
  ty_refOf := fun _ => fun | .handle 2 n => some (tag (toString n)) | _ => none
  ty_deferredOf := fun _ _ => fun | .handle 3 n => some (promise n) | _ => none
  ty_var := fun _ v => some (drawRaw v)
  ty_unknown := fun v => some (drawRaw v)
  ty_record := fun fields v => do
    let entries ← Machine.Record.entries v
    let rows ← fields.mapM fun (name, optional, r) =>
      match entries.lookup name with
      | some x => (r x).map (name, ·)
      | none => if optional then some (name, slot none) else none
    pure (panel rows)
  ty_map := fun _ r v => do
    let entries ← Machine.Map.read v
    pure (panel (← entries.mapM fun (k, x) => (r x).map (k, ·)))
  ty_tuple := fun rs => fun
    | .list xs => if xs.length == rs.length then ((rs.zip xs).mapM fun (p : Reader × Val) => p.1 p.2).map tuple else none
    | _ => none
  ty_app := fun _ _ v => some (drawRaw v)
  ty_null := fun v => some (drawRaw v)
  ty_undefined := fun v => some (drawRaw v)
  ty_number := fun
    | .nat n => some (atom (toString n))
    | .negInt n => some (atom (negative n))
    | .float _ => some (atom "float")
    | _ => none
  ty_bytes := fun | .bytes bs => some (atom s!"{bs.length} bytes") | _ => none
  ty_contextOf := fun _ v => some (drawRaw v)

/-- Whether the type reads the value: the value fits the type, as the picture draws it. -/
def reads (t : Ty) (v : Val) : Bool := (cata_ty typed t v).isSome

/-- **A value's picture at a type**: the type's reading, or the value drawn raw where the type
does not read it. -/
def draw (t : Ty) (v : Val) : Fig := (cata_ty typed t v).getD (drawRaw v)

end Tools.View.Cell
