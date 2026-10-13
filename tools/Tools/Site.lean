import Std.Data.HashMap
import Tools.Document.Html
import Tools.Document.Json
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Print.Render

/-!
# Tools.Site — the documentation site as one value (decisions row 363)

A site is one value: its pages in reading order, the root first, each a folder path and a
`Tools.Document`. Every file of the site is a fold of that value:

* each page's `index.html`, through one shell, its Markdown twin (`index.md`, which an agent
  reads and the language check reads) and its document as JSON (`document.json`);
* the site's navigation on every page: the sections in the header, the breadcrumbs, the parts of
  the page ("On this page"), the previous and next pages, and the contents page;
* `site.json`, the pages with their titles and parts, the contract of a framework's navigation.

**Split.** A producer writes one document; `split` makes it pages. Each part that the split's rule
names becomes a page of its own, one folder down, and a list of links stands in its place. So the
semantics report stays one document, whose Markdown is `generated/semantics.md`, and the site
gives each concept and each requirement a page.

**References.** A page's references resolve in its space, the document it was split from: a part
on the same page by its fragment, a part of another page by a relative link and its fragment,
and a page's own part by the page.

**The shell is the typed tree of `lean4-whatwg`.** Its elements are written in `html!`, so the
HTML Standard's content model admits every element of the shell where it stands when Lean
compiles this module. A node folded from data enters the shell at a typed position, and `admit`
checks it there at the run, with the located refusal of `Content.explain`. So a page's tree is
valid by construction (`Element.valid`), and the serializer writes only such a tree.

**Checks** (`Site.check`), before any file is written: a page path is unique, and its parent is a
page; a reference resolves in its space; a relative link resolves to a page or a file of the
site.

A page links the style files by its depth, so the folder previews from any server path: the
studio's server serves it at `/.lake/gen/site/`.
-/

namespace Tools.Site

open Tools.Document Tools.View
open Whatwg.Html
open Whatwg.Html.Content (Ctx Refusal)

/-! ## The value -/

/-- One page: its folder under the site's root (`[]` for the root, `["semantics"]`), its document,
its space, the document it was split from, where its references resolve, and the key of the part
it was split from, if any. -/
structure Page where
  path : List String
  doc : Document
  space : String := ""
  key : Option String := none

/-- A site: its pages in reading order, the root first, and the other files it writes, by their
paths from the root. -/
structure Site where
  pages : List Page
  files : List String := []

/-- A path as the folders of a link, with a slash after each. -/
def folders (path : List String) : String := String.join (path.map (· ++ "/"))

/-- The way from a page's folder up to the root. -/
def up (path : List String) : String := String.join (path.map fun _ => "../")

/-- A link from the page at `here` to the page at `there`, as the shortest relative path. -/
def linkTo (here there : List String) : String :=
  let common := (here.zip there).takeWhile (fun (a, b) => a == b) |>.length
  let s := up (here.drop common) ++ folders (there.drop common)
  if s.isEmpty then "./" else s

/-! ## Split -/

/-- A part's key as a folder: its last `:`-separated run, lowercased, with every character but a
letter, a digit and `-` written `-`. -/
def slug (key : String) : String :=
  ((key.splitOn ":").getLast?.getD key).map fun c =>
    let c := c.toLower
    if c.isAlphanum || c == '-' then c else '-'

/-- A block kept on its page, or the link that stands in for a part made a page. -/
private abbrev Kept := Sum Block Line

/-- Consecutive links as one list. -/
private def gather : List Kept → List Block
  | [] => []
  | .inl b :: rest => b :: gather rest
  | .inr l :: rest =>
    match gather rest with
    | .items ls :: more => .items (l :: ls) :: more
    | more => .items [l] :: more

-- The split is a paramorphism, not a fold: a part that stays on its page keeps its original body,
-- which a fold's algebra no longer sees. Pairing each case with the identity fold would make it a
-- fold at the cost of a second carrier; the two mutual functions below say it directly.
mutual
  /-- A block on the page at `path`: kept, or a part made a page, with the pages below it. -/
  private def splitBlock (cut : List String → String → Bool) (path : List String)
      (producer : List String) (space : String) : Block → List Kept × List Page
    | .part k t body =>
      if cut path k then
        let here := path ++ [slug k]
        let (kept, pages) := splitBlocks cut here producer space body
        -- the link, with the part's first paragraph when it opens with one
        let summary : Line := match body with
          | .para l :: _ => .text ": " :: l
          | _ => []
        ([.inr (.link (slug k ++ "/") t :: summary)],
          { path := here, space, key := some k, doc := { title := t, producer, body := gather kept } } :: pages)
      else ([.inl (.part k t body)], [])
    | b => ([.inl b], [])
  private def splitBlocks (cut : List String → String → Bool) (path : List String)
      (producer : List String) (space : String) : List Block → List Kept × List Page
    | [] => ([], [])
    | b :: bs =>
      let (k1, p1) := splitBlock cut path producer space b
      let (k2, p2) := splitBlocks cut path producer space bs
      (k1 ++ k2, p1 ++ p2)
end

/-- **A document as pages** at `path`: each part that `cut` names, given the page it stands on,
becomes a page one folder down, split the same way; consecutive such parts leave one list of
links, each with its part's first paragraph when the part opens with one. The pages are in the document's order, each before the pages below it. -/
def split (cut : List String → String → Bool) (path : List String) (space : String) (d : Document) :
    List Page :=
  let (kept, pages) := splitBlocks cut path d.producer space d.body
  { path, space, doc := { d with body := gather kept } } :: pages

/-! ## Folds of the site -/

/-- A page's parts and their sub-parts: the two levels of "On this page". A monoid fold
(`Algebra.collect`) that reads no line. -/
def parts (d : Document) : List (String × String × List (String × String)) :=
  Block.collect (Algebra.collect (fun _ => []) fun k t sub => [(k, t, sub.map fun (k', t', _) => (k', t'))]) d.body

/-- Every key of a page, at every depth: its parts' and its figures'. -/
def keys (d : Document) : List String :=
  Block.collect { Algebra.collect (fun _ => []) (fun k _ body => k :: body) with graph := fun k _ _ _ => [k] } d.body

/-- The page that each key names in each space, and whether the key is the page's own: the key of
the part it was split from, or a part on it. -/
def keyIndex (s : Site) : Std.HashMap (String × String) (List String × Bool) :=
  s.pages.foldl (init := {}) fun m p =>
    let m := match p.key with
      | some k => m.insert (p.space, k) (p.path, true)
      | none => m
    (keys p.doc).foldl (fun m k => m.insert (p.space, k) (p.path, false)) m

/-- The link of a reference from page `p`: a part of the same page by its fragment, a page by its
folder, a part of another page by both. A key no page holds falls back to a fragment, which
`Site.check` has refused before any page is written. -/
def target (ix : Std.HashMap (String × String) (List String × Bool)) (p : Page) (k : String) : String :=
  match ix[(p.space, k)]? with
  | some (path, true) => linkTo p.path path
  | some (path, false) => if path == p.path then Html.fragment k else linkTo p.path path ++ Html.fragment k
  | none => Html.fragment k

/-- The page at a path. -/
def Site.at? (s : Site) (path : List String) : Option Page := s.pages.find? (·.path == path)

/-- The sections: the pages one folder below the root. -/
def Site.sections (s : Site) : List Page := s.pages.filter (·.path.length == 1)

/-- The previous and the next page in reading order. -/
def Site.around (s : Site) (p : Page) : Option Page × Option Page :=
  let i := s.pages.findIdx (·.path == p.path)
  ((if i == 0 then none else s.pages[i - 1]?), s.pages[i + 1]?)

/-! ## Checks -/

/-- A link's path from the root, from the page at `here`, without its fragment, and whether it
names a folder; `none` for a link off the site. -/
def resolve (here : List String) (href : String) : Option (List String × Bool) :=
  let href := (href.splitOn "#").head!
  if href.startsWith "https://" || href.startsWith "http://" || href.startsWith "mailto:" then none
  else
    let (start, rest) := if href.startsWith "/" then ([], (href.drop 1).toString) else (here, href)
    let segs := (rest.splitOn "/").foldl (fun acc seg =>
      match seg with
      | "." | "" => acc
      | ".." => acc.dropLast
      | _ => acc ++ [seg]) start
    some (segs, rest.isEmpty || rest.endsWith "/")

/-- The links of a page's document: a monoid fold of its lines. -/
def links (d : Document) : List String :=
  Block.collect (Algebra.collect (·.filterMap fun | .link h _ => some h | _ => none)) d.body

/-- **The site's checks**, each refusal by name: a repeated path, a page with no parent, a page's own
check (`Document.check`, where a reference may name a part of its space on another page), a key
twice in one space, and a relative link to no page or file. -/
def Site.check (s : Site) : List String := Id.run do
  let mut errors : Array String := #[]
  let paths := s.pages.map (·.path)
  if !paths.contains [] then errors := errors.push "no page at the root"
  for p in s.pages do
    let place := "/" ++ folders p.path
    if (paths.filter (· == p.path)).length > 1 then errors := errors.push s!"{place}: two pages at this path"
    if !p.path.isEmpty && !paths.contains p.path.dropLast then errors := errors.push s!"{place}: no page above it"
  let ix := keyIndex s
  for p in s.pages do
    if let .error es := p.doc.check (fun k => ix.contains (p.space, k)) then
      errors := errors ++ (es.map (s!"/{folders p.path}: " ++ ·)).toArray
  let mut seen : Std.HashSet (String × String) := {}
  for p in s.pages do
    for k in p.key.toList ++ keys p.doc do
      if seen.contains (p.space, k) then errors := errors.push s!"/{folders p.path}: key {k} twice in space {p.space.quote}"
      seen := seen.insert (p.space, k)
  let pageFiles := s.pages.map fun p => p.path ++ ["document.json"]
  for p in s.pages do
    for h in links p.doc do
      match resolve p.path h with
      | none => pure ()
      | some (r, folder) =>
        let ok := if folder then paths.contains r
          else pageFiles.contains r || s.files.contains ("/".intercalate r)
        unless ok do errors := errors.push s!"/{folders p.path}: link {h}: no page or file of the site"
  return errors.toList

/-! ## The shell

Each position of the shell is a context of the content model, named once. A node's type is its
position, so a node checked for one place cannot stand in another. -/

abbrev InHtml := Ctx.child Ctx.document .html
abbrev InHead := Ctx.child InHtml .head
abbrev InBody := Ctx.child InHtml .body
abbrev InMain := Ctx.child InBody .main
abbrev InSiteList := Ctx.child (Ctx.child (Ctx.child InBody .header) .nav) .ol
abbrev InCrumbs := Ctx.child (Ctx.child InMain .nav) .ol
abbrev InPager := Ctx.child InMain .nav
abbrev InToc := Ctx.child (Ctx.child InMain .nav) .ol
abbrev InTocSub := Ctx.child (Ctx.child InToc .li) .ol
abbrev InFooterList := Ctx.child (Ctx.child InBody .footer) .ul

/-- **A node folded from data, admitted at the position its type names**, with its proof, or the
located refusal of the content model (ask W1 to `lean4-whatwg`, `Child.check?`). -/
def admit {ctx : Ctx} (n : RawNode) : Except Refusal (Child ctx) :=
  match h : Content.explain ctx n with
  | none => .ok ⟨n, (Content.explain_none_iff ctx n).mp h⟩
  | some r => .error r

/-- Where a page's styles stand: the looks file and the rules file, linked (a page of the site),
or the looks inline and the rules linked (the studio's specimen, in a look of its own). -/
inductive Styles where
  | files (looks rules : String)
  | inlineLooks (looks : String) (rules : String)

/-- A section of the site's navigation; the current one is marked. -/
def sectionItem (href label : String) (current : Option String) : Child InSiteList :=
  match current with
  | some how => html! <li><a href={href} aria-current={how}>{E.txt label}</a></li>
  | none => html! <li><a href={href}>{E.txt label}</a></li>

/-- A breadcrumb; the last is the page itself. -/
def crumb (href label : String) (last : Bool) : Child InCrumbs :=
  if last then html! <li><a href={href} aria-current="page">{E.txt label}</a></li>
  else html! <li><a href={href}>{E.txt label}</a></li>

/-- A link to a neighbouring page in reading order. -/
def pagerLink (rel href label : String) : Child InPager :=
  if rel == "prev" then html! <a rel="prev" href={href}><span class="label">"Previous"</span>{E.txt label}</a>
  else html! <a rel="next" href={href}><span class="label">"Next"</span>{E.txt label}</a>

def tocSub (k t : String) : Child InTocSub := html! <li><a href={Html.fragment k}>{E.txt t}</a></li>

/-- A part of the page, with its own parts below it. -/
def tocItem (k t : String) (sub : List (String × String)) : Child InToc :=
  if sub.isEmpty then html! <li><a href={Html.fragment k}>{E.txt t}</a></li>
  else html! <li><a href={Html.fragment k}>{E.txt t}</a>{E.el (E.ol (sub.map fun (k, t) => tocSub k t))}</li>

def footerLine (line : String) : Child InFooterList := html! <li>{E.txt line}</li>

def footerLink (href label : String) : Child InFooterList := html! <li><a href={href}>{E.txt label}</a></li>

/-- The page's title, the first heading of its content, with the key of the part it was split from
beside it (decisions row 366, point 4). -/
def heading (title : String) : Option String → Child InMain
  | some k => html! <h1 id={k}>{E.txt title}<a class="key" href={Html.fragment k}>{E.txt k}</a></h1>
  | none => html! <h1>{E.txt title}</h1>

/-- The head: the encoding, the viewport, the title in the browser's tab and the styles. Its
content model is ordered, so its elements are written out: only the texts and links are data.
Its type names its tag, so the ordered model of `html` reads it whatever the styles. -/
def head (tabTitle : String) : Styles → Element .head InHtml
  | .files looks rules => html! <head><meta charset="utf-8" /><meta name="viewport" content="width=device-width, initial-scale=1" /><title>{E.txt tabTitle}</title><link rel="stylesheet" href={looks} /><link rel="stylesheet" href={rules} /></head>
  | .inlineLooks looks rules => html! <head><meta charset="utf-8" /><meta name="viewport" content="width=device-width, initial-scale=1" /><title>{E.txt tabTitle}</title><style>{E.txt looks}</style><link rel="stylesheet" href={rules} /></head>

/-- The head takes no attribute, whatever its styles. -/
theorem head_attrs (tabTitle : String) (styles : Styles) : (head tabTitle styles).attrs = [] := by
  cases styles <;> rfl

/-- The head in the place of `html`'s first child. -/
def headChild (tabTitle : String) (styles : Styles) : Child InHtml :=
  Child.of (head tabTitle styles) (by rw [head_attrs]; admits)

/-- What a page's shell holds beyond its document. Empty lists leave their element out. -/
structure Shell where
  /-- the title in the browser's tab -/
  tabTitle : String
  styles : Styles
  /-- the link to the root, from this page -/
  home : String
  /-- the key of the part the page was split from, shown beside its title -/
  key : Option String := none
  sections : List (Child InSiteList) := []
  crumbs : List (Child InCrumbs) := []
  toc : List (Child InToc) := []
  pager : List (Child InPager) := []
  footer : List (Child InFooterList) := []

/-- **The page**: the head, the site's header, the content (breadcrumbs, the title, the parts of
the page, the document's blocks, the neighbouring pages), and the footer. The parts come after the
title, so a reader meets the title first; on a wide screen the rules float them into the margin
beside the content, as a margin note. -/
def render (s : Shell) (title : String) (blocks : List (Child InMain)) : Element .html Ctx.document :=
  let header : Child InBody :=
    if s.sections.isEmpty then html! <header><a class="home" href={s.home}>"Effect4"</a></header>
    else html! <header><a class="home" href={s.home}>"Effect4"</a><nav aria-label="Site">{E.el (E.ol s.sections)}</nav></header>
  let toc : List (Child InMain) := if s.toc.isEmpty then [] else
    [html! <nav class="toc" aria-labelledby="toc-label"><p id="toc-label" class="label">"On this page"</p>{E.el (E.ol s.toc)}</nav>]
  let crumbs : List (Child InMain) := if s.crumbs.isEmpty then [] else
    [html! <nav class="crumbs" aria-label="Breadcrumb">{E.el (E.ol s.crumbs)}</nav>]
  let pager : List (Child InMain) := if s.pager.isEmpty then [] else
    -- the attribute's name as a literal, which the `admits` tactic reads
    [E.el (E.nav s.pager [A.a_class "pager", ⟨.aria_, "aria-label", "Pages"⟩])]
  let footer : List (Child InBody) := if s.footer.isEmpty then [] else
    [html! <footer><p class="label">"Provenance"</p>{E.el (E.ul s.footer)}</footer>]
  let main : Child InBody := E.el (E.main (crumbs ++ [heading title s.key] ++ toc ++ blocks ++ pager) [A.a_id "content"])
  let body : Child InHtml := E.el (E.body ([html! <a class="skip" href="#content">"Skip to the content"</a>, header] ++
    [main] ++ footer))
  html! <html lang="en">{headChild s.tabTitle s.styles}{body}</html>

/-- The blocks of a document, folded with a reference's link from `target`, each admitted in the
page's `main`. A refusal names the element names along its path. -/
def blocks (target : String → String) (d : Document) : Except String (List (Child InMain)) :=
  ((Block.foldList (Html.algebra target) d.body).flatMap (· 2)).mapM fun n =>
    match admit n with
    | .ok c => .ok c
    | .error r => .error ("HTML refused: " ++ Html.describe n r)

/-- The text of a page. -/
def text (e : Element .html Ctx.document) : String := Print.renderDoc e.toRaw

/-! ## A page of the site -/

/-- The shell of a page of the site: its styles, sections, breadcrumbs, parts, neighbours and
footer, every link relative to the page's folder. -/
def Site.shell (s : Site) (p : Page) : Shell :=
  let href (q : List String) := linkTo p.path q
  let (prev, next) := s.around p
  { tabTitle := if p.path.isEmpty then p.doc.title else p.doc.title ++ " · Effect4"
    styles := .files (up p.path ++ "looks.css") (up p.path ++ "page.css")
    home := href []
    key := p.key
    sections := s.sections.map fun q =>
      sectionItem (href q.path) q.doc.title
        (if q.path == p.path then some "page" else if q.path.isPrefixOf p.path then some "true" else none)
    crumbs := if p.path.length < 2 then [] else
      ((List.range p.path.length).filterMap fun k =>
        (s.at? (p.path.take (k + 1))).map fun q => crumb (href q.path) q.doc.title (k + 1 == p.path.length))
    toc := (parts p.doc).map fun (k, t, sub) => tocItem k t sub
    pager := (prev.map fun q => pagerLink "prev" (href q.path) q.doc.title).toList ++
      (next.map fun q => pagerLink "next" (href q.path) q.doc.title).toList
    footer := p.doc.producer.map footerLine ++
      [footerLink "document.json" "This page as data (effect4-document/1)",
       footerLink (href ["contents"]) "Every page of the site"] }

/-- A page of the site as its HTML, with the site's key index (`keyIndex`, computed once). -/
def Site.html (s : Site) (ix : Std.HashMap (String × String) (List String × Bool)) (p : Page) :
    Except String String := do
  return text (render (s.shell p) p.doc.title (← blocks (target ix p) p.doc))

/-- **The contents page**: every page under each section, deeper pages with their parent. -/
def contents (s : Site) : Document where
  title := "Contents"
  body := [.para [.text "Every page of the site, by section."]] ++
    s.sections.map fun sec =>
      .part (slug (String.join sec.path)) sec.doc.title
        [.items (s.pages.filter (fun q => sec.path.isPrefixOf q.path) |>.map fun q =>
          let link := Inline.link (linkTo ["contents"] q.path) q.doc.title
          match s.at? q.path.dropLast with
          | some parent => if q.path.length > 2 then [link, .text " · in ", .text parent.doc.title] else [link]
          | none => [link])]

/-! ## The site's files -/

/-- The site's pages and parts as JSON (`effect4-site/1`): the contract of a framework's
navigation, beside each page's document. -/
def Site.json (s : Site) : Lean.Json :=
  Lean.Json.mkObj [("format", "effect4-site/1"),
    ("pages", .arr (s.pages.map fun p => Lean.Json.mkObj [
      ("path", folders p.path), ("title", p.doc.title),
      ("parts", .arr ((parts p.doc).map fun (k, t, _) =>
        Lean.Json.mkObj [("key", k), ("title", t)]).toArray)]).toArray)]

/-- The looks of every page: the dark base, the paper look (`paper`, read from its token file) for
a light preference and print, and the rules that draw a picture's marks in them
(`Tools.View.Tokens.rules`). -/
def looksCss (paper : Look) : String := Html.looks {} paper ++ Tokens.rules

/-- Write every page of a checked site into `dir`: its HTML and its document as JSON. -/
def Site.write (s : Site) (dir : System.FilePath) : IO (List String) := do
  let mut errors := s.check
  unless errors.isEmpty do return errors
  let ix := keyIndex s
  for p in s.pages do
    match s.html ix p with
    | .error why => errors := errors ++ [s!"/{folders p.path}: {why}"]
    | .ok html =>
      let folder := p.path.foldl (· / ·) dir
      IO.FS.createDirAll folder
      IO.FS.writeFile (folder / "index.html") html
      IO.FS.writeFile (folder / "index.md") p.doc.markdown
      IO.FS.writeFile (folder / "document.json") ((Json.Document.json p.doc).pretty ++ "\n")
  IO.FS.writeFile (dir / "site.json") ((s.json).pretty ++ "\n")
  return errors

/-- Cloudflare Pages' headers: no sniffing, a strict referrer, no script, styles and images from
the site alone (the looks stand in a file, and a page's only inline part is none), and JSON as
JSON. -/
def headers : String :=
  "/*\n  X-Content-Type-Options: nosniff\n  Referrer-Policy: strict-origin-when-cross-origin\n" ++
  "  Content-Security-Policy: default-src 'self'; script-src 'none'; object-src 'none'; base-uri 'none'\n" ++
  "/*.json\n  Content-Type: application/json; charset=utf-8\n"

end Tools.Site
