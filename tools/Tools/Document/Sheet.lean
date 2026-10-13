import Whatwg.Css.Syntax.Serialize

/-!
# Tools.Document.Sheet — the page's rules, read by CSS's own grammar

The site's rules are a file, `page.css` (`path`). The design language's rule for them (decisions
row 354, point 1: the look is the only data of a colour or a face; row 366, point 3: no ornament
without a meaning) is checked on the tokens of CSS Syntax 3, as the standard's tokenizer reads
them (`Whatwg.Css.Syntax.tokenizeText`, lean4-whatwg slice K2; ask W5). A comment is no token, so
nothing a comment says is checked. A selector is no declaration, so `#main` is not a colour.

The check reads each declaration with the preludes of the blocks around it (`declarations`). A
fold over the tokens keeps the preludes of the open blocks: `{` opens a block under the tokens
read since the last boundary, `}` closes it, and a run of tokens that ends at `;` or `}` and opens
with a name and a colon is a declaration. That is the part of CSS Syntax 3's parser that the check
needs; it goes when the package's parser lands (slice K4 of its CSS plan).

A refusal names the declaration and the preludes it stands under, in the tokens' own writing
(`Whatwg.Css.Syntax.serialize`), and the reason: a located refusal.
-/

namespace Tools.Document.Sheet
open Whatwg.Css.Syntax

/-- The file of the page's own rules (`page.css`), from the repository's root. Every page of the
site links it. The rules read the looks' custom properties: the ground, the ink and the rule's
colour; the families of the name, data, label and title faces; the weight of a rule and of a frame;
the radius of a corner. The band behind a code block and a table's head is the look's band: the
rule's colour at the band's tone over the ground, as the view draws the band behind a lit row. A
measure, a size and a space are the page's.

**The status marks** (decisions row 354, point 2) are drawn here once, before the word of a status,
keyed on its `data-status`: a mark of the promise-and-keeping family, in `currentColor` and with no
hue. Proved is a filled circle; modulo a circle filled on its left half; a planned goal (`goal`, a
claim's or a plan node's) a hollow circle; open a dashed circle; refuted
the failure cross `×` of the notation. A circle's outline is the look's frame. A circle is a
pseudo-element with no content, which a screen reader does not read; the cross is text with an
empty alternative (`content: "×" / ""`), after a plain `content` for a browser without the
alternative. A circle's fill is a background, so print and a forced-colours mode are told to keep
it. The word beside the mark names the status, to a reader and to an agent. `absent`, `assumed`
and `missing` take no mark. -/
def path : System.FilePath := "tools/Tools/Document/page.css"

/-- A declaration of a sheet: its name, lowercased, its value, and the preludes of the blocks it
stands in, innermost first. -/
structure Decl where
  context : List (List Token)
  name : String
  value : List Token

/-- The tokens with the whitespace at either end dropped. -/
def trim (ts : List Token) : List Token :=
  ((ts.dropWhile (· == .whitespace)).reverse.dropWhile (· == .whitespace)).reverse

/-- A run of tokens as a declaration in `context`, where it opens with a name and a colon. -/
def Decl.of? (context : List (List Token)) (run : List Token) : Option Decl :=
  match trim run with
  | .ident n :: rest =>
    match rest.dropWhile (· == .whitespace) with
    | .colon :: value => some { context, name := (String.ofList n).toLower, value := trim value }
    | _ => none
  | _ => none

/-- The fold's state: the preludes of the open blocks, innermost first; the tokens since the last
boundary, last first; the declarations so far, last first. -/
structure Walk where
  blocks : List (List Token) := []
  run : List Token := []
  found : List Decl := []

/-- The run closed at a boundary: a declaration where it is one. -/
def Walk.close (w : Walk) : List Decl :=
  match Decl.of? w.blocks w.run.reverse with
  | some d => d :: w.found
  | none => w.found

/-- One token: a block opens under the run, closes, or a run ends; any other token joins the run. -/
def Walk.step (w : Walk) : Token → Walk
  | .openCurly => { w with blocks := trim w.run.reverse :: w.blocks, run := [] }
  | .closeCurly => { blocks := w.blocks.drop 1, run := [], found := w.close }
  | .semicolon => { w with run := [], found := w.close }
  | t => { w with run := t :: w.run }

/-- **The declarations of a sheet**, in order, each with the preludes it stands under. -/
def declarations (css : String) : List Decl :=
  ((tokenizeText css).foldl Walk.step {}).found.reverse

/-- The functions that write a colour. -/
def colourFunctions : List String :=
  ["rgb", "rgba", "hsl", "hsla", "hwb", "lab", "lch", "oklab", "oklch", "color"]

/-- The properties that draw an ornament with no meaning (row 366, point 3). -/
def ornaments : List String := ["box-shadow", "text-shadow", "filter", "backdrop-filter"]

/-- The custom properties a value reads with `var()`. -/
def reads : List Token → List String
  | .function f :: rest =>
    let later := reads rest
    if (String.ofList f).toLower == "var" then
      match rest.dropWhile (· == .whitespace) with
      | .ident n :: _ => String.ofList n :: later
      | _ => later
    else later
  | _ :: rest => reads rest
  | [] => []

/-- What in a declaration is a literal colour or family, or an ornament with no meaning, if
anything. A hash in a value is a colour. An `@font-face` rule names the family it defines, so its
declarations may write one. -/
def Decl.problem (d : Decl) : Option String :=
  let fns := d.value.filterMap fun | .function f => some (String.ofList f).toLower | _ => none
  let hash := d.value.any fun | .hash .. => true | _ => false
  let inFace := d.context.any (·.head? == some (.atKeyword "font-face".toList))
  if hash || fns.any colourFunctions.contains then some "a literal colour"
  else if ornaments.contains d.name then some s!"an ornament with no meaning ({d.name})"
  else if let some g := fns.find? (·.endsWith "gradient") then
    some s!"an ornament with no meaning ({g}())"
  else if inFace then none
  else if d.name == "font-family" && d.value.head? != some (.function "var".toList) then
    some "a literal family"
  else if d.name == "font" && !(reads d.value).any (·.startsWith "--e4-font-") then
    some "a font without the look's family"
  else none

/-- A declaration as the sheet writes it, under its preludes, outermost first. -/
def Decl.locate (d : Decl) : String :=
  let text (ts : List Token) := String.ofList (serialize ts)
  let preludes := d.context.reverse.map fun p => s!"`{text p}`"
  " › ".intercalate (preludes ++ [s!"`{d.name}: {text d.value}`"])

/-- **The design language's rule for the page's rules**: the first declaration of `css` that writes
a literal colour, a family not taken from the look, a shadow, a gradient or a filter, located, with
the reason; or none. -/
def problem (css : String) : Option String :=
  (declarations css).findSome? fun d => d.problem.map fun why => s!"{d.locate}: {why}"

end Tools.Document.Sheet
