import Tools.Document.Html
import Tools.Document.Json

/-!
# Tools.Site — the documentation site, as standard files (decisions row 363)

A site is a folder of standard files that any static host serves (Cloudflare Pages, row 363,
point 2): each page a folder with its `index.html` and its `document.json`; the page's rules
(`page.css`) and the looks (`looks.css`) once, at the root; and the host's `_headers` and
`404.html`. Every page goes through the same HTML fold as the semantics page, so the HTML
Standard's content model checks each one (`Document.html`), and every page's document is also
written as the JSON contract (`Tools.Document.Json`), which a framework reads later (row 363,
point 3). Lean is the source of every file (point 1); nothing here reads a written page back.

A page links the two style files by its depth, so the folder previews from any server path: the
studio's server serves it at `/.lake/gen/site/`.
-/

namespace Tools.Site

open Tools.Document Tools.View

/-- One page: its folder under the site's root (`[]` for the root, `["semantics"]`), and its
document. -/
structure Page where
  path : List String
  doc : Document

/-- The way from a page's folder up to the root. -/
def up (path : List String) : String := String.join (path.map fun _ => "../")

/-- The sheet of a page at `path`: the root's `page.css` and `looks.css`. -/
def sheet (path : List String) : Html.Sheet := .link (up path ++ "page.css") (some (up path ++ "looks.css"))

/-- The looks of every page: the dark base, and the paper look for a light preference and print. -/
def looksCss : String := Html.looks {} Look.paper

/-- Write one page into the site at `dir`: its HTML, checked, and its document as JSON. -/
def writePage (dir : System.FilePath) (p : Page) : IO (Except String Unit) := do
  let folder := p.path.foldl (· / ·) dir
  match Html.Document.html p.doc (sheet p.path) {} Look.paper with
  | .error why => return .error s!"{"/".intercalate p.path}: {why}"
  | .ok html =>
    IO.FS.createDirAll folder
    IO.FS.writeFile (folder / "index.html") html
    IO.FS.writeFile (folder / "document.json") ((Json.Document.json p.doc).pretty ++ "\n")
    return .ok ()

/-- Cloudflare Pages' headers: no sniffing, a strict referrer, no script, styles and images from
the site alone (the looks stand in a file, and a page's only inline part is none), and JSON as
JSON. -/
def headers : String :=
  "/*\n  X-Content-Type-Options: nosniff\n  Referrer-Policy: strict-origin-when-cross-origin\n" ++
  "  Content-Security-Policy: default-src 'self'; script-src 'none'; object-src 'none'; base-uri 'none'\n" ++
  "/*.json\n  Content-Type: application/json; charset=utf-8\n"

end Tools.Site
