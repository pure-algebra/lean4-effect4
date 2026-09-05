import Effect4.Surface.Deploy

/-!
# Surface.Site: pages, routes and the endpoints they use

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.7, with the
docs app site of §13.3 as the fixture.

A **site** is the browser side of one application: a list of pages, each named
by a route template, each declaring which endpoints it reads and, at most, one
form it posts. The declarations are what a client emitter and a route table are
functions of, and `Site.resolves` is the fact that joins them to a real api:
every endpoint a page names exists, and a form's endpoint takes a payload.

Like `Effect4/Surface/Deploy.lean`, this module does **not** import
`Effect4/Surface/Api.lean` (wave 2a, written beside this one). An endpoint is
named by the triple `(api, group, endpoint)` and the endpoint table is an
argument, so the fact is decidable as soon as the table is and the two modules
do not have to land in one order.

It imports `Effect4/Surface/Deploy.lean` for one reason only: the ASCII word
alphabet (`asciiWordStart`, `asciiWordContinue`) that a binding name and a path
parameter share, plus the three shared bag helpers (`rootBag`,
`descriptionBag`, `optionalStr`). Duplicating those four bytes of predicate in
two modules is exactly the "two places that could disagree" §13.6 rule 2
refuses.

| | |
| --- | --- |
| Carrier | `Page` (4 fields), `Site` (3 fields) |
| Operations | `pathTemplateLegal`, `Page.check`, `Site.check`, `Site.resolves`, `Page.json`, `Site.json`, `routesJson` |
| Laws | `Page.wellFormed_iff`, `Site.wellFormed_iff`, `Site.resolves_iff`, `Site.checkPages_ok_iff`, `Site.form_endpoint_has_payload` |
| Structure | a route-indexed list of pages, plus a relation to an endpoint table that is an argument rather than an import |
| Payoff | a page that names an endpoint that does not exist, or posts a form to an endpoint with no payload, is refused before a line of client code is emitted |
| Anti-vacuity | the `DocsWeb` fixture of §13.3: `decide` receipts for `WellFormed` and `Resolves`, an `Arch.accepts` receipt for the view, one refusing `#guard` per clause |
| Generation | `routesJson` (rule `surface.site.routes`) |

## The path template check, and the row it owes

`pathTemplateLegal` decides a route over UTF-8 bytes, the route
`Effect4/Store/Utf8.lean` takes and `Effect4/Surface/Spell.lean` takes,
because `ByteArray.toList` does not reduce in the kernel on this toolchain. It
admits exactly:

* the root, `"/"`;
* otherwise a leading `/` followed by one or more `/`-separated segments, each
  of which is either
  * a **literal**: one or more bytes from `A-Z`, `a-z`, `0-9`, `-`, `.`, `_`,
    `~` (RFC 3986's unreserved set), or
  * a **parameter**: `:` followed by an ASCII word (`^[A-Za-z_][A-Za-z0-9_]*$`).

An empty segment is refused, so `//a`, `/a//b` and a trailing `/a/` are all
refused; a route with no leading `/` is refused; a percent escape, a query
string and a fragment are refused, because a route template is not a URL.

**The owed row.** Wave 2a's `Api.lean` owns `Path` and `Path.parse?`. The two
must agree: `pathTemplateLegal r = true ↔ (Path.parse? r).isSome`, for every
`r`. That is a theorem this module cannot state, because it does not import the
type; it is owed by the wave that has both, and until it lands a route may be
legal here and unparsable there. Nothing in this module claims otherwise.

## What is deliberately not here

* **The DOM.** A page has a route and the endpoints it uses, and no markup.
  The join point for markup is lean4-whatwg's `Whatwg.Html`, and it is a later
  packet, not a v1 omission to be filled in by a string.
* **A title field.** §15.3: the semantics live in the annotation bag, so a
  page's title is its `title` key and its prose is its `description` key. The
  carrier has no second spelling of either.
* **More than one form per page.** §4.7 gives `form : Option _`. A page that
  posts to two endpoints is two pages or a later carrier; it is not a list
  here, because the payload clause is stated once per page.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema
open Effect4.Arch (accepts)

/-! ## Path templates -/

/-- A byte admitted inside a literal path segment: RFC 3986's unreserved set,
`A-Z`, `a-z`, `0-9`, `-`, `.`, `_`, `~`. -/
def pathLiteralByte (byte : UInt8) : Bool :=
  (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) ||
    (48 ≤ byte && byte ≤ 57) ||
    byte == 45 || byte == 46 || byte == 95 || byte == 126

/-- One segment: `:name` with an ASCII word after the colon, or a non-empty run
of literal bytes. The empty segment is refused, which is what rules out `//`
and a trailing slash. -/
def pathSegmentLegal : List UInt8 → Bool
  | [] => false
  | byte :: rest =>
    if byte == 58 then
      match rest with
      | [] => false
      | first :: more => asciiWordStart first && more.all asciiWordContinue
    else pathLiteralByte byte && rest.all pathLiteralByte

/-- Split a byte list on `/`, keeping empty pieces so that `//` is visible to
`pathSegmentLegal` as an empty segment. -/
def splitOnSlash : List UInt8 → List (List UInt8)
  | [] => [[]]
  | byte :: rest =>
    if byte == 47 then [] :: splitOnSlash rest
    else
      match splitOnSlash rest with
      | [] => [[byte]]
      | first :: more => (byte :: first) :: more

/-- A legal path template, decided over UTF-8 bytes. This module's header says
exactly what is admitted, and names the agreement with wave 2a's `Path.parse?`
as an owed row. -/
def pathTemplateLegal (route : String) : Bool :=
  match route.toUTF8.data.toList with
  | [] => false
  | first :: rest =>
    first == 47 && (rest.isEmpty || (splitOnSlash rest).all pathSegmentLegal)

/-! ## The carriers -/

/--
One page of a site.

`uses` and `form` name endpoints by the triple `(api, group, endpoint)`; the
triple is the api module's own coordinates, and `Site.resolves` is where it is
checked against a real table. There is no `title` field: §15.3 puts the title
and the prose in `annotations`, read through `Effect4/Surface/Annotate.lean`'s
keys.
-/
structure Page where
  /-- The route template this page is served at. -/
  route : String
  /-- The endpoints the page reads, as `(api, group, endpoint)`. -/
  uses : List (String × String × String) := []
  /-- The endpoint the page's form posts to, when it has one. -/
  form : Option (String × String × String) := none
  /-- The page's annotation bag: its `identifier`, `description` and `title`. -/
  annotations : Annotations := none
deriving DecidableEq

/-- A named set of pages: the browser surface of one application. -/
structure Site where
  /-- The site's name; a legal generated binding, because the client module is
  named after it. -/
  name : String
  /-- Its pages, in declaration order. -/
  pages : List Page := []
  /-- The root annotation bag: the `identifier` and `description` of §15.2. -/
  annotations : Annotations := none
deriving DecidableEq

namespace Page

/-- Clause: the route is a legal path template. -/
def routeLegal (page : Page) : Bool := pathTemplateLegal page.route

/-- Clause (§15.2): the page's bag carries an `identifier`. -/
def identified (page : Page) : Bool := (identifierIn page.annotations).isSome

/-- Clause (§15.2): the page's bag carries a `description`. -/
def described (page : Page) : Bool := (descriptionIn page.annotations).isSome

/-- Every endpoint the page names: the ones it reads, and the one its form
posts to. The one place the two are read together. -/
def references (page : Page) : List (String × String × String) :=
  page.uses ++ (match page.form with | some row => [row] | none => [])

/-- The clauses of a page, in the order a check reads them. The site's name is
carried in so the refusal names the site the page belongs to. -/
def clauses (site : String) (page : Page) : List (Bool × Refusal) :=
  [ (page.routeLegal, .routeIllegal site page.route)
  , (page.identified, .identifierMissing "page" page.route)
  , (page.described, .descriptionMissing "page" page.route) ]

/-- Check a page of a site: the clauses in order, first refusal wins. -/
def check (site : String) (page : Page) : Except Refusal Unit :=
  firstRefusal (page.clauses site)

/-- The proposition a capability opts into. -/
def WellFormed (site : String) (page : Page) : Prop := Page.check site page = .ok ()

instance (site : String) (page : Page) : Decidable (Page.WellFormed site page) := by
  unfold Page.WellFormed; infer_instance

/-- The route is a legal path template. -/
def RouteLegal (page : Page) : Prop := page.routeLegal = true
/-- The page's bag carries an `identifier`. -/
def Identified (page : Page) : Prop := page.identified = true
/-- The page's bag carries a `description`. -/
def Described (page : Page) : Prop := page.described = true

/-- Well-formedness is exactly the conjunction of the named clauses. -/
theorem wellFormed_iff (site : String) (page : Page) :
    Page.WellFormed site page ↔
      (Page.RouteLegal page ∧ Page.Identified page ∧ Page.Described page) := by
  rw [Page.WellFormed, Page.check, firstRefusal_ok_iff]
  simp [Page.clauses, Page.RouteLegal, Page.Identified, Page.Described]

end Page

namespace Site

/-- Every route, in declaration order. -/
def routes (site : Site) : List String := site.pages.map Page.route

/-- Clause: the site's name is a legal generated binding, because the client
module is named after it. -/
def nameLegal (site : Site) : Bool := identifier site.name

/-- Clause (§15.2): the root bag carries an `identifier`. -/
def identified (site : Site) : Bool := (identifierIn site.annotations).isSome

/-- Clause (§15.2): the root bag carries a `description`. -/
def described (site : Site) : Bool := (descriptionIn site.annotations).isSome

/-- Clause: no two pages share a route. -/
def routesDistinct (site : Site) : Bool := namesUnique site.routes

/-- The clauses of a site's own row, in the order a check reads them. -/
def clauses (site : Site) : List (Bool × Refusal) :=
  [ (site.nameLegal, .nameIllegal "site" site.name)
  , (site.identified, .identifierMissing "site" site.name)
  , (site.described, .descriptionMissing "site" site.name)
  , (site.routesDistinct, .routeDuplicate site.name (firstDuplicate site.routes)) ]

/-- Check every page of a site, first refusal wins. -/
def checkPages (site : Site) : List Page → Except Refusal Unit
  | [] => .ok ()
  | page :: rest =>
    match Page.check site.name page with
    | .error refusal => .error refusal
    | .ok _ => site.checkPages rest

/-- Check a site: its own clauses, then every page's, first refusal wins. -/
def check (site : Site) : Except Refusal Unit :=
  Except.bind (firstRefusal site.clauses) fun _ => site.checkPages site.pages

/-- The proposition a capability opts into. -/
def WellFormed (site : Site) : Prop := Site.check site = .ok ()

instance (site : Site) : Decidable (Site.WellFormed site) := by
  unfold Site.WellFormed; infer_instance

/-- The Bool projection, for a battery that wants one. -/
def wellFormed (site : Site) : Bool := decide (Site.WellFormed site)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (site : Site) :
    Site.wellFormed site = true ↔ Site.WellFormed site := by
  simp [Site.wellFormed]

/-- The site's name is a legal generated binding. -/
def NameLegal (site : Site) : Prop := site.nameLegal = true
/-- The root bag carries an `identifier`. -/
def Identified (site : Site) : Prop := site.identified = true
/-- The root bag carries a `description`. -/
def Described (site : Site) : Prop := site.described = true
/-- No two pages share a route. -/
def RoutesDistinct (site : Site) : Prop := site.routesDistinct = true

/-- The page walk succeeds exactly when every page is well-formed. -/
theorem checkPages_ok_iff (site : Site) :
    ∀ pages : List Page,
      site.checkPages pages = .ok () ↔
        ∀ page ∈ pages, Page.WellFormed site.name page
  | [] => by simp [Site.checkPages]
  | page :: rest => by
    simp only [Site.checkPages]
    cases answer : Page.check site.name page with
    | error refusal => simp [Page.WellFormed, answer]
    | ok value =>
      cases value
      simp [Page.WellFormed, answer, checkPages_ok_iff site rest]

/-- Well-formedness is exactly the site's own clauses and its pages'. -/
theorem wellFormed_iff (site : Site) :
    Site.WellFormed site ↔
      (Site.NameLegal site ∧ Site.Identified site ∧ Site.Described site ∧
        Site.RoutesDistinct site ∧
        ∀ page ∈ site.pages, Page.WellFormed site.name page) := by
  rw [Site.WellFormed, Site.check, exceptSeq_ok_iff, firstRefusal_ok_iff,
    checkPages_ok_iff site site.pages]
  simp [Site.clauses, Site.NameLegal, Site.Identified, Site.Described,
    Site.RoutesDistinct, and_assoc]

/-! ### The site law: `resolves`

The endpoint table is `(api, group, endpoint, hasPayload)`, which a later wave
computes from `Api.endpointTable`. It is an argument here for the reason in
this module's header.
-/

/-- Whether the table knows an endpoint. -/
def endpointKnown (table : List (String × String × String × Bool))
    (row : String × String × String) : Bool :=
  table.any fun entry =>
    entry.1 == row.1 && entry.2.1 == row.2.1 && entry.2.2.1 == row.2.2

/-- Whether the table knows an endpoint *and* records that it takes a
payload. -/
def endpointHasPayload (table : List (String × String × String × Bool))
    (row : String × String × String) : Bool :=
  table.any fun entry =>
    entry.1 == row.1 && entry.2.1 == row.2.1 && entry.2.2.1 == row.2.2 && entry.2.2.2

/-- Clause: every endpoint every page names exists in the table. -/
def usesResolve (site : Site) (table : List (String × String × String × Bool)) : Bool :=
  site.pages.all fun page => page.references.all (endpointKnown table)

/-- The first page and endpoint the table does not know, for the refusal to
name. -/
def firstUnknownUse (site : Site) (table : List (String × String × String × Bool)) :
    Option (String × String) :=
  site.pages.findSome? fun page =>
    (page.references.find? fun row => !(endpointKnown table row)).map fun row =>
      (page.route, row.2.2)

/-- Clause: every form posts to an endpoint that takes a payload. -/
def formsHavePayload (site : Site) (table : List (String × String × String × Bool)) :
    Bool :=
  site.pages.all fun page =>
    match page.form with
    | some row => endpointHasPayload table row
    | none => true

/-- The first form whose endpoint takes no payload, for the refusal to name. -/
def firstFormWithoutPayload (site : Site)
    (table : List (String × String × String × Bool)) : Option (String × String) :=
  site.pages.findSome? fun page =>
    match page.form with
    | some row =>
      if endpointHasPayload table row then none else some (page.route, row.2.2)
    | none => none

/-- The clauses of the site law, in the order a check reads them. -/
def resolvesClauses (site : Site) (table : List (String × String × String × Bool)) :
    List (Bool × Refusal) :=
  [ (site.usesResolve table, .usesUnknownEndpoint site.name
      ((site.firstUnknownUse table |>.map Prod.fst).getD "")
      ((site.firstUnknownUse table |>.map Prod.snd).getD ""))
  , (site.formsHavePayload table, .formWithoutPayload site.name
      ((site.firstFormWithoutPayload table |>.map Prod.fst).getD "")
      ((site.firstFormWithoutPayload table |>.map Prod.snd).getD "")) ]

/-- Every endpoint every page names exists, and every form's endpoint takes a
payload. First refusal wins. -/
def resolves (site : Site) (table : List (String × String × String × Bool)) :
    Except Refusal Unit :=
  firstRefusal (site.resolvesClauses table)

/-- The proposition a capability opts into. -/
def Resolves (site : Site) (table : List (String × String × String × Bool)) : Prop :=
  Site.resolves site table = .ok ()

instance (site : Site) (table : List (String × String × String × Bool)) :
    Decidable (Site.Resolves site table) := by
  unfold Site.Resolves; infer_instance

/-- Every endpoint every page names exists in the table. -/
def UsesResolve (site : Site) (table : List (String × String × String × Bool)) : Prop :=
  site.usesResolve table = true
/-- Every form posts to an endpoint that takes a payload. -/
def FormsHavePayload (site : Site) (table : List (String × String × String × Bool)) :
    Prop := site.formsHavePayload table = true

/-- The site law is exactly its two clauses. -/
theorem resolves_iff (site : Site) (table : List (String × String × String × Bool)) :
    Site.Resolves site table ↔
      (Site.UsesResolve site table ∧ Site.FormsHavePayload site table) := by
  rw [Site.Resolves, Site.resolves, firstRefusal_ok_iff]
  simp [Site.resolvesClauses, Site.UsesResolve, Site.FormsHavePayload]

/-- In a resolving site every form posts to an endpoint the table records a
payload for. This is the clause a form emitter rests on: the request body it
writes has a schema, by the kernel, before a line is emitted. -/
theorem form_endpoint_has_payload (site : Site)
    (table : List (String × String × String × Bool)) (ok : Site.Resolves site table)
    (page : Page) (mem : page ∈ site.pages) (row : String × String × String)
    (posts : page.form = some row) : endpointHasPayload table row = true := by
  have clauses := (Site.resolves_iff site table).mp ok
  have page_ok := List.all_eq_true.mp clauses.2 page mem
  rw [posts] at page_ok
  exact page_ok

/-! ### Projections -/

/-- One endpoint reference as a JSON value. -/
def endpointRefJson (row : String × String × String) : Json :=
  .obj [("api", .str row.1), ("group", .str row.2.1), ("endpoint", .str row.2.2)]

end Site

/-- The page as a JSON value: the view's payload, with its semantics read off
its bag through the §15.1 keys. -/
def Page.json (page : Page) : Json :=
  .obj
    [ ("route", .str page.route)
    , ("uses", .arr (page.uses.map Site.endpointRefJson))
    , ("form",
        match page.form with
        | some row => Site.endpointRefJson row
        | none => .null)
    , ("identifier", optionalStr (identifierIn page.annotations))
    , ("description", optionalStr (descriptionIn page.annotations)) ]

/-- The site as a JSON value: the view's payload. -/
def Site.json (site : Site) : Json :=
  .obj
    [ ("name", .str site.name)
    , ("pages", .arr (site.pages.map Page.json))
    , ("identifier", optionalStr (identifierIn site.annotations))
    , ("description", optionalStr (descriptionIn site.annotations)) ]

/-! ## The view -/

/-- The endpoint reference's representation. -/
def endpointRefRep : Representation :=
  Schema.struct
    [ Schema.property "api" Schema.string
    , Schema.property "group" Schema.string
    , Schema.property "endpoint" Schema.string ]

/-- The page view's representation. -/
def pageRep : Representation :=
  Schema.struct
    [ Schema.property "route" Schema.string
    , Schema.property "uses" (Schema.array (Schema.reference "EndpointRef"))
    , Schema.property "form"
        (Schema.anyOf (Schema.reference "EndpointRef") [Schema.null])
    , Schema.property "identifier" (Schema.anyOf Schema.string [Schema.null])
    , Schema.property "description" (Schema.anyOf Schema.string [Schema.null]) ]

/-- The site view, for registration at `["surface", "site"]`.

`Effect4/Surface/Views.lean` is wave 1a's and this wave does not edit it; the
registration of this document is an owed row. -/
def siteDoc : Document :=
  { representation :=
      Schema.struct
        [ Schema.property "name" Schema.string
        , Schema.property "pages" (Schema.array (Schema.reference "Page"))
        , Schema.property "identifier" (Schema.anyOf Schema.string [Schema.null])
        , Schema.property "description" (Schema.anyOf Schema.string [Schema.null]) ]
    references := [⟨"EndpointRef", endpointRefRep⟩, ⟨"Page", pageRep⟩] }

/-! ## Generation -/

/--
The site's route table: `routes.generated.json` of §13.4.

This is the emitted artifact, not the view: it carries each page's semantics
inline, because the consumer of a route table is a build step and a human
reading a build step's output, and §15.3 says those come from the bag rather
than from a second field. It is total: every field of a page renders, and a
page with no semantics is refused by `Site.check` long before this is called.

surface: rule.surface.site.routes
-/
def routesJson (site : Site) : Json :=
  .obj
    [ ("site", .str site.name)
    , ("description", optionalStr (descriptionIn site.annotations))
    , ("pages", .arr (site.pages.map fun page =>
        .obj
          [ ("route", .str page.route)
          , ("description", optionalStr (descriptionIn page.annotations))
          , ("uses", .arr (page.uses.map Site.endpointRefJson))
          , ("form",
              match page.form with
              | some row => Site.endpointRefJson row
              | none => .null) ])) ]

/-! ## Anti-vacuity: the docs app site of the plan's §13.3

Site `DocsWeb`: pages `/`, `/docs` (uses `docs.list`), `/docs/:slug` (uses
`docs.get`, form `feedback.create`), `/search` (uses `search.query`).
-/

/-- The endpoint table the docs api of §13.3 yields. A later wave computes this
from `Api.endpointTable`; here it is the fixture the site law is checked
against. `feedback.create` is the one endpoint with a payload. -/
def docsEndpointTable : List (String × String × String × Bool) :=
  [ ("DocsApi", "health", "get", false)
  , ("DocsApi", "docs", "list", false)
  , ("DocsApi", "docs", "get", false)
  , ("DocsApi", "search", "query", false)
  , ("DocsApi", "feedback", "create", true) ]

/-- The reference application's site. -/
def docsSite : Site :=
  { name := "DocsWeb"
    pages :=
      [ { route := "/"
          annotations := rootBag "home" "The landing page." }
      , { route := "/docs"
          uses := [("DocsApi", "docs", "list")]
          annotations := rootBag "docsIndex" "Every documentation page, by section." }
      , { route := "/docs/:slug"
          uses := [("DocsApi", "docs", "get")]
          form := some ("DocsApi", "feedback", "create")
          annotations := rootBag "doc" "One documentation page, with its feedback form." }
      , { route := "/search"
          uses := [("DocsApi", "search", "query")]
          annotations := rootBag "search" "Full-text search over the documentation." } ]
    annotations := rootBag "DocsWeb" "The browser surface of the documentation site." }

/-- The fixture site is well-formed, by the kernel. -/
theorem docsSite_wellFormed : Site.WellFormed docsSite := by decide

/-- And it resolves against the docs api's endpoint table, by the kernel. -/
theorem docsSite_resolves : Site.Resolves docsSite docsEndpointTable := by decide

/-- The clause read off `resolves_iff` rather than `decide`d again: the shape a
capability of §14.3 opts into. -/
theorem docsSite_formsHavePayload : Site.FormsHavePayload docsSite docsEndpointTable :=
  ((Site.resolves_iff docsSite docsEndpointTable).mp docsSite_resolves).2

-- the view accepts its own payload, and refuses one that is not
#guard accepts siteDoc docsSite.json = true
#guard accepts siteDoc (.obj [("name", .str "DocsWeb")]) = false

-- the path template check: what it admits
#guard pathTemplateLegal "/"
#guard pathTemplateLegal "/docs"
#guard pathTemplateLegal "/docs/:slug"
#guard pathTemplateLegal "/a/:b/c"
#guard pathTemplateLegal "/api/v1.2/_x~y"
-- and what it refuses
#guard pathTemplateLegal "" == false
#guard pathTemplateLegal "docs" == false
#guard pathTemplateLegal "/docs/" == false
#guard pathTemplateLegal "//docs" == false
#guard pathTemplateLegal "/docs/:" == false
#guard pathTemplateLegal "/docs/:1bad" == false
#guard pathTemplateLegal "/docs%20x" == false
#guard pathTemplateLegal "/docs?q=1" == false

-- one refusal per clause of a page, each naming the clause and what failed
private def unrootedPage : Page :=
  { route := "docs", annotations := rootBag "bad" "A page with no leading slash." }

private def unidentifiedPage : Page := { route := "/x" }

private def undescribedPage : Page :=
  { route := "/x", annotations := identifierKey.singleton "x" }

#guard Site.check { docsSite with pages := [unrootedPage] } ==
  .error (.routeIllegal "DocsWeb" "docs")
#guard Site.check { docsSite with pages := [unidentifiedPage] } ==
  .error (.identifierMissing "page" "/x")
#guard Site.check { docsSite with pages := [undescribedPage] } ==
  .error (.descriptionMissing "page" "/x")

-- one refusal per clause of a site
#guard Site.check { docsSite with name := "class" } ==
  .error (.nameIllegal "site" "class")
#guard Site.check { docsSite with annotations := none } ==
  .error (.identifierMissing "site" "DocsWeb")
#guard Site.check { docsSite with annotations := identifierKey.singleton "DocsWeb" } ==
  .error (.descriptionMissing "site" "DocsWeb")
private def twiceRouted : List Page :=
  [ { route := "/x", annotations := rootBag "one" "The first." }
  , { route := "/x", annotations := rootBag "two" "The second." } ]

#guard Site.check { docsSite with pages := twiceRouted } ==
  .error (.routeDuplicate "DocsWeb" "/x")
#guard Site.check docsSite == .ok ()

-- and one per clause of the site law
#guard Site.resolves docsSite docsEndpointTable == .ok ()
#guard Site.resolves docsSite [] ==
  .error (.usesUnknownEndpoint "DocsWeb" "/docs" "list")
#guard Site.resolves docsSite
    [ ("DocsApi", "docs", "list", false), ("DocsApi", "docs", "get", false)
    , ("DocsApi", "search", "query", false), ("DocsApi", "feedback", "create", false) ] ==
  .error (.formWithoutPayload "DocsWeb" "/docs/:slug" "create")

-- the Bool projection agrees with the check
#guard Site.wellFormed docsSite
#guard Site.wellFormed { docsSite with name := "class" } == false

-- the emitted route table names every page and every endpoint it uses
#guard routesJson docsSite ==
  .obj
    [ ("site", .str "DocsWeb")
    , ("description", .str "The browser surface of the documentation site.")
    , ("pages", .arr
        [ .obj [ ("route", .str "/"), ("description", .str "The landing page.")
               , ("uses", .arr []), ("form", .null) ]
        , .obj [ ("route", .str "/docs")
               , ("description", .str "Every documentation page, by section.")
               , ("uses", .arr [.obj [("api", .str "DocsApi"), ("group", .str "docs"),
                   ("endpoint", .str "list")]])
               , ("form", .null) ]
        , .obj [ ("route", .str "/docs/:slug")
               , ("description", .str "One documentation page, with its feedback form.")
               , ("uses", .arr [.obj [("api", .str "DocsApi"), ("group", .str "docs"),
                   ("endpoint", .str "get")]])
               , ("form", .obj [("api", .str "DocsApi"), ("group", .str "feedback"),
                   ("endpoint", .str "create")]) ]
        , .obj [ ("route", .str "/search")
               , ("description", .str "Full-text search over the documentation.")
               , ("uses", .arr [.obj [("api", .str "DocsApi"), ("group", .str "search"),
                   ("endpoint", .str "query")]])
               , ("form", .null) ] ]) ]

end Effect4.Surface
