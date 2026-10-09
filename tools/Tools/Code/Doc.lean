/-!
# A document, and its layout at a width

The readable form of printed code. A document is text, breaks and groups, after Wadler's "A
prettier printer" (2003) with Lindig's strict variant of its search. A layout lays each group
flat when it fits the rest of its line, and broken otherwise, outermost first. Equal documents
at equal widths are equal bytes.

A break that a layout takes keeps what the flat print had there. So the only freedom of a layout
is the choice, at each group, between flat and broken, and `undo_layout` states it: undo every
break that a layout took, and the flat print comes back, at every width. The flat print of a
printed TypeScript expression is the pinned house print, byte for byte
(`Tools.Code.Ts.flat_fold_expr`, `tools/Tools/Code/TypeScript.lean`). Together: a readable file is
the checked bytes with whitespace changed at breaks, and nothing else.

Two indents. A `nest` indents the lines of its broken groups; a `block` indents every line
inside it, and starts its contents in the broken mode, so each statement of a block finds its
own layout. The house print indents its blocks and nothing else, so the flat print counts the
blocks' indents alone.
-/

namespace Tools.Code

/-- A document. -/
inductive Doc where
  | nil
  /-- text with no newline in it -/
  | text (s : String)
  /-- an optional break: `flat` when its group lies flat; `broken`, a newline and the indent
  when its group breaks -/
  | line (flat broken : String)
  /-- a newline, always -/
  | hard
  /-- the lines of broken groups inside indent `i` more -/
  | nest (i : Nat) (d : Doc)
  /-- every line inside indents `i` more, and the contents start broken -/
  | block (i : Nat) (d : Doc)
  /-- flat when it fits, else broken -/
  | group (d : Doc)
  | cat (a b : Doc)
deriving Inhabited, Repr

instance : Append Doc := ⟨Doc.cat⟩

/-- `++` on documents is `cat`. -/
theorem Doc.append_def (a b : Doc) : a ++ b = .cat a b := rfl

/-- How a group lies. -/
inductive Mode where
  | flat
  | broken
deriving DecidableEq, Repr

/-- The width of a text in columns: its UTF-8 bytes. A printed program is ASCII outside its string
literals, where a byte is a column; a literal with other characters only breaks a line earlier.
The measure rests on no axiom (`String.length` rests on `Classical.choice` in this toolchain). -/
def width (s : String) : Nat := s.utf8ByteSize

/-- A run of spaces. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- The flat print: every group flat, and a hard newline at the blocks' indent `b`. -/
def Doc.flat (b : Nat) : Doc → String
  | .nil => ""
  | .text s => s
  | .line f _ => f
  | .hard => "\n" ++ spaces b
  | .nest _ d => d.flat b
  | .block j d => d.flat (b + j)
  | .group d => d.flat b
  | .cat a c => a.flat b ++ c.flat b

/-! ## Fitting -/

/-- What a room holds after a document laid out in a mode: it overflows, a newline ends it, or
some room is left. -/
inductive Fit where
  | over
  | ends
  | left (r : Nat)

/-- How a document fits a room of `r` columns, in the mode `m`. A group inside is measured flat. -/
def Doc.fit (m : Mode) : Doc → Nat → Fit
  | .nil, r => .left r
  | .text s, r => if width s ≤ r then .left (r - width s) else .over
  | .line f _, r =>
    match m with
    | .flat => if width f ≤ r then .left (r - width f) else .over
    | .broken => .ends
  | .hard, _ => .ends
  | .nest _ d, r => d.fit m r
  | .block _ d, r => d.fit .broken r
  | .group d, r => d.fit .flat r
  | .cat a c, r =>
    match a.fit m r with
    | .left r' => c.fit m r'
    | x => x

/-- An item of the rest of a document: the blocks' indent, the indent, the mode, the document. -/
abbrev Item := Nat × Nat × Mode × Doc

/-- Whether the rest of a document fits a room of `r` up to its first newline. -/
def fits : List Item → Nat → Bool
  | [], _ => true
  | (_, _, m, d) :: z, r =>
    match d.fit m r with
    | .over => false
    | .ends => true
    | .left r' => fits z r'

/-! ## The layout -/

/-- A piece of a layout: text; a break taken, with its flat text, its broken text and its indent;
or a hard newline, with the blocks' indent and its indent. -/
inductive Piece where
  | text (s : String)
  | brk (flat broken : String) (indent : Nat)
  | nl (blocks indent : Nat)
deriving Repr

/-- A piece as output. -/
def Piece.out : Piece → String
  | .text s => s
  | .brk _ broken i => broken ++ "\n" ++ spaces i
  | .nl _ i => "\n" ++ spaces i

/-- A piece with its break undone: the flat text of a break, a hard newline at the blocks'
indent. -/
def Piece.undo : Piece → String
  | .text s => s
  | .brk f _ _ => f
  | .nl b _ => "\n" ++ spaces b

/-- The pieces of a document at the width `w`: the blocks' indent `b`, the indent `i`, the mode
`m`, the rest `z` and the column `k`. It answers the pieces and the column after them. -/
def Doc.go (w : Nat) : Nat → Nat → Mode → Doc → List Item → Nat → List Piece × Nat
  | _, _, _, .nil, _, k => ([], k)
  | _, _, _, .text s, _, k => ([.text s], k + width s)
  | _, _, .flat, .line f _, _, k => ([.text f], k + width f)
  | _, i, .broken, .line f bk, _, _ => ([.brk f bk i], i)
  | b, i, _, .hard, _, _ => ([.nl b i], i)
  | b, i, m, .nest j d, z, k => d.go w b (if m = .broken then i + j else i) m z k
  | b, i, _, .block j d, z, k => d.go w (b + j) (i + j) .broken z k
  | b, i, .flat, .group d, z, k => d.go w b i .flat z k
  | b, i, .broken, .group d, z, k =>
    d.go w b i (if fits ((b, i, .flat, d) :: z) (w - k) then .flat else .broken) z k
  | b, i, m, .cat a c, z, k =>
    let ra := a.go w b i m ((b, i, m, c) :: z) k
    let rc := c.go w b i m z ra.2
    (ra.1 ++ rc.1, rc.2)

/-- The layout of a document at the width `w`. -/
def Doc.layout (w : Nat) (d : Doc) : String := String.join ((d.go w 0 0 .broken [] 0).1.map Piece.out)

/-- Pieces with their breaks undone. -/
def undo : List Piece → String
  | [] => ""
  | p :: ps => p.undo ++ undo ps

theorem undo_append : ∀ a b : List Piece, undo (a ++ b) = undo a ++ undo b
  | [], b => by simp only [List.nil_append, undo, String.empty_append]
  | p :: a, b => by simp only [List.cons_append, undo, undo_append a b, String.append_assoc]

/-- Undoing the breaks of a document's pieces gives its flat print, whatever the width, the
indent, the mode, the rest and the column. -/
theorem undo_go (w : Nat) (d : Doc) :
    ∀ (b i : Nat) (m : Mode) (z : List Item) (k : Nat), undo (d.go w b i m z k).1 = d.flat b := by
  induction d with
  | nil => intro b i m z k; rfl
  | text s => intro b i m z k; simp only [Doc.go, undo, String.append_empty, Piece.undo, Doc.flat]
  | line f bk =>
    intro b i m z k
    cases m <;> simp only [Doc.go, undo, String.append_empty, Piece.undo, Doc.flat]
  | hard => intro b i m z k; simp only [Doc.go, undo, String.append_empty, Piece.undo, Doc.flat]
  | nest j d ih => intro b i m z k; exact ih _ _ _ _ _
  | block j d ih => intro b i m z k; exact ih _ _ _ _ _
  | group d ih => intro b i m z k; cases m <;> exact ih _ _ _ _ _
  | cat a c iha ihc =>
    intro b i m z k
    simp only [Doc.go, Doc.flat, undo_append, iha, ihc]

/-- **Undo a layout's breaks and the flat print comes back**, at every width. -/
theorem undo_layout (w : Nat) (d : Doc) : undo (d.go w 0 0 .broken [] 0).1 = d.flat 0 :=
  undo_go w d 0 0 .broken [] 0

/-! ## Builders -/

namespace Doc

/-- Items with a comma between: `", "` flat, a comma and a newline broken. -/
def commas : List Doc → Doc
  | [] => .nil
  | [x] => x
  | x :: rest => x ++ .line ", " "," ++ commas rest

/-- Items between `op` and `cl`, as one group: flat, `op`, `pad`, the items with `", "`, `pad`,
`cl`; broken, one item a line, indented two, and no comma after the last, as Effect's own source
writes it (`vendor/effect-4.0.1/src/internal/effect.ts`). No items is `op` and `cl` alone. -/
def delimited (op cl pad : String) : List Doc → Doc
  | [] => .text (op ++ cl)
  | items => .group (.text op ++ .nest 2 (.line pad "" ++ commas items) ++ .line pad "" ++ .text cl)

/-- The flat print of items with commas between is the items' flat prints joined by `", "`. -/
theorem flat_commas (b : Nat) : ∀ items : List Doc,
    (commas items).flat b = String.intercalate ", " (items.map (·.flat b))
  | [] => by simp only [commas, flat, List.map_nil, String.intercalate_nil]
  | [x] => by simp only [commas, List.map_cons, List.map_nil, String.intercalate_singleton]
  | x :: y :: rest => by
    simp only [commas, append_def, flat, flat_commas b (y :: rest), List.map_cons,
      String.intercalate_cons_cons]

/-- The flat print of no items between delimiters. -/
theorem flat_delimited_nil (b : Nat) (op cl pad : String) : (delimited op cl pad []).flat b = op ++ cl :=
  rfl

/-- The flat print of items between delimiters: the house's inline form. -/
theorem flat_delimited (b : Nat) (op cl pad : String) (items : List Doc) (h : items ≠ []) :
    (delimited op cl pad items).flat b =
      op ++ pad ++ String.intercalate ", " (items.map (·.flat b)) ++ pad ++ cl := by
  cases items with
  | nil => exact absurd rfl h
  | cons x rest =>
    simp only [delimited, append_def, flat, flat_commas b (x :: rest), String.append_assoc]

end Doc

end Tools.Code
