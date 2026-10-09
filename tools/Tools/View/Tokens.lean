import Lean.Data.Json
import Tools.View.Look
import Tools.Code.Doc

/-!
# A look as design tokens, and as CSS

A look's file is a document of the W3C Design Tokens Community Group's format, 2025.10
(`https://www.designtokens.org/tr/2025.10/format/`): groups of tokens, each a `$value` of a
standard `$type`. A look uses only the format's own types:

| Group | Tokens | Type |
| --- | --- | --- |
| `color` | `ground`, `ink`, `rule`, `host`, `failure`, `resource` | `color`, sRGB, with its `hex` |
| `tone` | `band` | `number`, from 0 to 1 |
| `font` | `data`, `name`, `label`, `title` | `typography`: `fontFamily`, `fontSize`, `fontWeight` |
| `stroke` | `edge`, `frame`, `rule`, `radius` | `dimension`, in `px` |
| `organic` | `trunk`, `fine`, `flare`, `wave` | `dimension`, in `px` |
| `organic` | `noise` | `number`, from 0 to 1 |
| `motion` | `step`, `stagger`, `enter` | `duration` |
| `motion` | `move`, `leave`, `write`, `draw`, `expand` | `transition` |

What the format has no type for stands in `$extensions`, under the key `effect4.view`: the
look's scheme and hue (on the document), a face's `fontStyle`, an edge's `curve` and `reach`, and a
transition's `easing` by name with its exact CSS form. A transition's `timingFunction` is the
nearest cubic Bézier (`Ease.bezier`); a reader takes the easing from its name.

**Reading** (`readLook`) lays a document over a base look: each token present replaces the
base's value, and every other value stays. So a look file names only what it changes. A name the
look does not have, a type that is not the token's, or a value out of its range is refused with
the token's path and the reason. A `lineHeight` or a `letterSpacing` is refused too: the row of
the grid sets the line, and the data face takes one cell a character.

**Writing** (`tokens`, `render`) gives every token, in a fixed order, laid out at 100 columns by
the document printer of the code plane (`Tools.Code.Doc`). The driver checks that each look it
reads comes back from its own written form (`View.lean`, `look-round-trip`): a finite check.

**CSS** (`css`, `rules`): a look's tokens as CSS custom properties on `[data-look="<name>"]`, and
the class rules that colour and set the type of a picture's SVG (`Tools.View.Output`) through
them. The names are the tokens' paths, joined by hyphens, under the prefix `--e4-`.
-/

namespace Tools.View.Tokens

open Lean (Json JsonNumber)
open Tools.Code (Doc)
open Tools.View

/-! ## An ordered document of JSON -/

/-- A JSON document whose objects keep their fields in the order written. -/
inductive J where
  | obj (fields : List (String × J))
  | arr (items : List J)
  | str (s : String)
  | num (s : String)
  | bool (b : Bool)

mutual
/-- A document as a `Doc`: each object and array is a group, flat when it fits. -/
def J.doc : J → Doc
  | .obj fs => Doc.delimited "{" "}" "" (J.fieldDocs fs)
  | .arr xs => Doc.delimited "[" "]" "" (J.itemDocs xs)
  | .str s => .text (Json.str s).compress
  | .num s => .text s
  | .bool b => .text (toString b)
/-- The fields of an object, each `"name": value`. -/
def J.fieldDocs : List (String × J) → List Doc
  | [] => []
  | (k, v) :: rest => (.text ((Json.str k).compress ++ ": ") ++ v.doc) :: J.fieldDocs rest
/-- The items of an array. -/
def J.itemDocs : List J → List Doc
  | [] => []
  | x :: rest => x.doc :: J.itemDocs rest
end

/-- A document laid out at 100 columns, with a final newline. -/
def J.render (j : J) : String := Doc.layout 100 j.doc ++ "\n"

/-! ## Writing -/

/-- The key of this tool's extensions. -/
def extKey : String := "effect4.view"

/-- A number of `10^-places` units. -/
def J.dec (v : Int) (places : Nat) : J := .num (decimal v places)

/-- A colour token's value: sRGB components to four places, and the exact `hex`. -/
def colorValue (c : Rgb) : J :=
  let comp (v : Nat) : J := .dec (roundDiv (v * 10000) 255) 4
  .obj [("colorSpace", .str "srgb"),
    ("components", .arr [comp (c / 0x10000 % 0x100), comp (c / 0x100 % 0x100), comp (c % 0x100)]),
    ("hex", .str c.css)]

/-- A dimension of thousandths of a pixel. -/
def pxValue (milli : Nat) : J := .obj [("value", .dec milli 3), ("unit", .str "px")]

/-- A duration of milliseconds. -/
def msValue (ms : Nat) : J := .obj [("value", .num (toString ms)), ("unit", .str "ms")]

/-- A transition token. -/
def transitionToken (tr : Transition) : J :=
  let (y1, y2) := tr.ease.bezier
  .obj [("$type", .str "transition"), ("$value", .obj [("duration", msValue tr.duration), ("delay", msValue tr.delay),
      ("timingFunction", .arr [.num "0.333", .dec y1 3, .num "0.667", .dec y2 3])]),
    ("$extensions", .obj [(extKey, .obj [("easing", .str tr.ease.name), ("css", .str tr.ease.css)])])]

/-- A face's typography token. -/
def fontToken (f : Font) : J :=
  .obj [("$value", .obj [("fontFamily", .arr (f.family.map .str)), ("fontSize", pxValue f.size),
      ("fontWeight", .num (toString f.weight))]),
    ("$extensions", .obj [(extKey, .obj [("fontStyle", .str f.style)])])]

/-- **A look's tokens**, every one, in order. -/
def tokens (L : Look) : J :=
  .obj [
    ("$description", .str L.description),
    ("$extensions", .obj [(extKey, .obj [("scheme", .str L.scheme.name), ("hue", .bool L.hue)])]),
    ("color", .obj ([("$type", .str "color")] ++
      Role.all.map fun role => (role.tokenName, .obj [("$value", colorValue (L.palette.of role))]))),
    ("tone", .obj [("$type", .str "number"), ("band", .obj [("$value", .dec L.band 3)])]),
    ("font", .obj ([("$type", .str "typography")] ++
      Face.all.map fun face => (face.tokenName, fontToken (L.faces.of face)))),
    ("stroke", .obj [("$type", .str "dimension"),
      ("edge", .obj [("$value", pxValue (L.strokes.edge * 1000)),
        ("$extensions", .obj [(extKey, .obj [("curve", .str L.curve.name), ("reach", .dec L.reach 3)])])]),
      ("frame", .obj [("$value", pxValue (L.strokes.frame * 1000))]),
      ("rule", .obj [("$value", pxValue (L.strokes.rule * 1000))]),
      ("radius", .obj [("$value", pxValue L.strokes.radius)])]),
    ("organic", .obj [
      ("trunk", .obj [("$type", .str "dimension"), ("$value", pxValue L.organic.trunk)]),
      ("fine", .obj [("$type", .str "dimension"), ("$value", pxValue L.organic.fine)]),
      ("flare", .obj [("$type", .str "dimension"), ("$value", pxValue L.organic.flare)]),
      ("noise", .obj [("$type", .str "number"), ("$value", .dec L.organic.noise 3)]),
      ("wave", .obj [("$type", .str "dimension"), ("$value", pxValue L.organic.wave)])]),
    ("motion", .obj [
      ("step", .obj [("$type", .str "duration"), ("$value", msValue L.motion.step)]),
      ("move", transitionToken L.motion.move),
      ("leave", transitionToken L.motion.leave),
      ("write", transitionToken L.motion.write),
      ("draw", transitionToken L.motion.draw),
      ("expand", transitionToken L.motion.expand),
      ("stagger", .obj [("$type", .str "duration"), ("$value", msValue L.motion.stagger)]),
      ("enter", .obj [("$type", .str "duration"), ("$value", msValue L.motion.enterFrom)])])]

/-- A look's token file. -/
def render (L : Look) : String := (tokens L).render

/-! ## Reading -/

/-- A reading's result: a value, or the path of a token and the reason it is refused. -/
abbrev Read := Except String

/-- The fields of an object, in order of name. -/
def fieldsOf (path : String) : Json → Read (List (String × Json))
  | .obj kvs => pure kvs.toList
  | _ => throw s!"{path}: not an object"

/-- The names every group and token may hold besides its members. -/
def metaNames : List String := ["$type", "$description", "$extensions", "$deprecated"]

/-- Refuse a field that is not one of `names`. -/
def onlyNames (path : String) (fs : List (String × Json)) (names : List String) : Read Unit :=
  match fs.find? fun (k, _) => !(names.contains k || metaNames.contains k || k == "$value") with
  | some (k, _) => throw s!"{path}.{k}: a look has no such token"
  | none => pure ()

/-- Refuse a declared type that is not `ty`; an empty `ty` is a group of mixed types. -/
def typed (path ty : String) (fs : List (String × Json)) : Read Unit :=
  if ty.isEmpty then pure () else
  match fs.lookup "$type" with
  | none => pure ()
  | some (.str t) => if t == ty then pure () else throw s!"{path}: the type is {t}, not {ty}"
  | some _ => throw s!"{path}.$type: not a string"

/-- A string. -/
def str (path : String) : Json → Read String
  | .str s => pure s
  | _ => throw s!"{path}: not a string"

/-- A number in units of `10^-places`, rounded to the nearest. -/
def scaled (path : String) (places : Nat) : Json → Read Int
  | .num n =>
    pure (if n.exponent ≤ places then n.mantissa * 10 ^ (places - n.exponent)
      else roundDiv n.mantissa (10 ^ (n.exponent - places)))
  | _ => throw s!"{path}: not a number"

/-- A whole number in units of `10^-places`, from `lo` to `hi`. -/
def within (path : String) (places : Nat) (lo hi : Int) (j : Json) : Read Nat := do
  let v ← scaled path places j
  if lo ≤ v && v ≤ hi then pure v.toNat else throw s!"{path}: {decimal v places} is outside {decimal lo places} to {decimal hi places}"

/-- A hexadecimal digit's value. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A colour from `#rrggbb`. -/
def hexColor (path s : String) : Read Rgb :=
  match s.toList with
  | '#' :: ds =>
    if ds.length != 6 then throw s!"{path}: {s} is not #rrggbb" else
    ds.foldlM (fun acc c => match hexDigit c with
      | some d => pure (16 * acc + d)
      | none => throw s!"{path}: {s} is not #rrggbb") 0
  | _ => throw s!"{path}: {s} is not #rrggbb"

/-- A colour token's value: its `hex` when it has one, else its sRGB components. -/
def readColor (path : String) (j : Json) : Read Rgb := do
  let fs ← fieldsOf path j
  match fs.lookup "hex" with
  | some h => hexColor s!"{path}.hex" (← str s!"{path}.hex" h)
  | none =>
    match fs.lookup "colorSpace", fs.lookup "components" with
    | some (.str "srgb"), some (.arr cs) =>
      match cs.toList with
      | [r, g, b] =>
        let ch (i : String) (c : Json) : Read Nat := do
          let v ← within s!"{path}.components.{i}" 4 0 10000 c
          pure (roundDiv (v * 255) 10000).toNat
        pure (0x10000 * (← ch "0" r) + 0x100 * (← ch "1" g) + (← ch "2" b))
      | _ => throw s!"{path}.components: not three numbers"
    | some (.str space), _ => throw s!"{path}.colorSpace: {space} is not srgb; a look's colours are sRGB"
    | _, _ => throw s!"{path}: no hex and no sRGB components"

/-- A dimension in thousandths of a pixel. -/
def readPx (path : String) (j : Json) : Read Nat := do
  let fs ← fieldsOf path j
  match fs.lookup "unit" with
  | some (.str "px") => within s!"{path}.value" 3 0 1000000 ((fs.lookup "value").getD .null)
  | some (.str u) => throw s!"{path}.unit: {u} has no size in a picture; write px"
  | _ => throw s!"{path}.unit: missing"

/-- A duration in milliseconds. -/
def readMs (path : String) (j : Json) : Read Nat := do
  let fs ← fieldsOf path j
  let v := (fs.lookup "value").getD .null
  match fs.lookup "unit" with
  | some (.str "ms") => within s!"{path}.value" 0 0 60000 v
  | some (.str "s") => within s!"{path}.value" 3 0 60000 v
  | _ => throw s!"{path}.unit: not ms or s"

/-- The fields of a token's `$extensions` under this tool's key. -/
def extOf (path : String) (fs : List (String × Json)) : Read (List (String × Json)) := do
  match fs.lookup "$extensions" with
  | none => pure []
  | some x =>
    match (← fieldsOf s!"{path}.$extensions" x).lookup extKey with
    | none => pure []
    | some e => fieldsOf s!"{path}.$extensions.{extKey}" e

/-- A token: its fields, after checking its type against its group's. -/
def token (path ty : String) (j : Json) : Read (List (String × Json)) := do
  let fs ← fieldsOf path j
  typed path ty fs
  if (fs.lookup "$value").isNone then throw s!"{path}: no $value" else pure fs

/-- The font weights the format names, and their numbers. -/
def weightNames : List (String × Nat) :=
  [("thin", 100), ("hairline", 100), ("extra-light", 200), ("ultra-light", 200), ("light", 300),
    ("normal", 400), ("regular", 400), ("book", 400), ("medium", 500), ("semi-bold", 600),
    ("demi-bold", 600), ("bold", 700), ("extra-bold", 800), ("ultra-bold", 800), ("black", 900),
    ("heavy", 900), ("extra-black", 950), ("ultra-black", 950)]

/-- A face over a base face. -/
def readFont (path : String) (base : Font) (j : Json) : Read Font := do
  let fs ← token path "typography" j
  let v ← fieldsOf s!"{path}.$value" ((fs.lookup "$value").getD .null)
  onlyNames s!"{path}.$value" v ["fontFamily", "fontSize", "fontWeight"]
  let mut f := base
  if let some fam := v.lookup "fontFamily" then
    match fam with
    | .str s => f := { f with family := [s] }
    | .arr xs => f := { f with family := ← xs.toList.mapM (str s!"{path}.$value.fontFamily") }
    | _ => throw s!"{path}.$value.fontFamily: not a string or a list of strings"
  if let some sz := v.lookup "fontSize" then f := { f with size := ← readPx s!"{path}.$value.fontSize" sz }
  if let some w := v.lookup "fontWeight" then
    match w with
    | .str s =>
      match weightNames.lookup s with
      | some n => f := { f with weight := n }
      | none => throw s!"{path}.$value.fontWeight: {s} is no weight's name"
    | w => f := { f with weight := ← within s!"{path}.$value.fontWeight" 0 1 1000 w }
  let e ← extOf path fs
  onlyNames s!"{path}.$extensions.{extKey}" e ["fontStyle"]
  if let some st := e.lookup "fontStyle" then
    match ← str s!"{path}.$extensions.{extKey}.fontStyle" st with
    | "italic" => f := { f with italic := true }
    | "normal" => f := { f with italic := false }
    | s => throw s!"{path}.$extensions.{extKey}.fontStyle: {s} is not italic or normal"
  pure f

/-- A transition over a base transition. Its easing is read from its name; its `timingFunction`
is the nearest cubic Bézier, written for other tools, and not read. -/
def readTransition (path : String) (base : Transition) (j : Json) : Read Transition := do
  let fs ← token path "transition" j
  let v ← fieldsOf s!"{path}.$value" ((fs.lookup "$value").getD .null)
  onlyNames s!"{path}.$value" v ["duration", "delay", "timingFunction"]
  let mut tr := base
  if let some d := v.lookup "duration" then tr := { tr with duration := ← readMs s!"{path}.$value.duration" d }
  if let some d := v.lookup "delay" then tr := { tr with delay := ← readMs s!"{path}.$value.delay" d }
  let e ← extOf path fs
  onlyNames s!"{path}.$extensions.{extKey}" e ["easing", "css"]
  if let some n := e.lookup "easing" then
    let s ← str s!"{path}.$extensions.{extKey}.easing" n
    match Ease.ofName? s with
    | some ease => tr := { tr with ease }
    | none => throw s!"{path}.$extensions.{extKey}.easing: {s} is not one of {Ease.all.map (·.name)}"
  pure tr

/-- A duration token. -/
def readDuration (path : String) (j : Json) : Read Nat := do
  let fs ← token path "duration" j
  readMs s!"{path}.$value" ((fs.lookup "$value").getD .null)

/-- The members of a group that are present, after checking the group's names and type. -/
def group (path ty : String) (names : List String) (j : Json) : Read (List (String × Json)) := do
  let fs ← fieldsOf path j
  onlyNames path fs names
  typed path ty fs
  pure fs

/-- **A look read over a base**: each token the document holds replaces the base's value. The
look takes the name `name`. -/
def readLook (base : Look) (name : String) (j : Json) : Read Look := do
  let top ← fieldsOf "" j
  onlyNames "" top ["$schema", "color", "tone", "font", "stroke", "organic", "motion"]
  let mut L := { base with name }
  if let some d := top.lookup "$description" then L := { L with description := ← str "$description" d }
  let e ← extOf "" top
  onlyNames s!"$extensions.{extKey}" e ["scheme", "hue"]
  if let some s := e.lookup "scheme" then
    match ← str s!"$extensions.{extKey}.scheme" s with
    | "dark" => L := { L with scheme := .dark }
    | "light" => L := { L with scheme := .light }
    | x => throw s!"$extensions.{extKey}.scheme: {x} is not dark or light"
  if let some h := e.lookup "hue" then
    match h with
    | .bool b => L := { L with hue := b }
    | _ => throw s!"$extensions.{extKey}.hue: not true or false"
  if let some c := top.lookup "color" then
    let fs ← group "color" "color" (Role.all.map (·.tokenName)) c
    for role in Role.all do
      if let some t := fs.lookup role.tokenName then
        let path := s!"color.{role.tokenName}"
        let tf ← token path "color" t
        L := { L with palette := L.palette.set role (← readColor s!"{path}.$value" ((tf.lookup "$value").getD .null)) }
  if let some c := top.lookup "tone" then
    let fs ← group "tone" "number" ["band"] c
    if let some t := fs.lookup "band" then
      let tf ← token "tone.band" "number" t
      L := { L with band := ← within "tone.band.$value" 3 0 1000 ((tf.lookup "$value").getD .null) }
  if let some c := top.lookup "font" then
    let fs ← group "font" "typography" (Face.all.map (·.tokenName)) c
    for face in Face.all do
      if let some t := fs.lookup face.tokenName then
        L := { L with faces := L.faces.set face (← readFont s!"font.{face.tokenName}" (L.faces.of face) t) }
  if let some c := top.lookup "stroke" then
    let fs ← group "stroke" "dimension" ["edge", "frame", "rule", "radius"] c
    let weight (path : String) (t : Json) : Read Nat := do
      let tf ← token path "dimension" t
      let v ← readPx s!"{path}.$value" ((tf.lookup "$value").getD .null)
      if v % 1000 == 0 then pure (v / 1000) else throw s!"{path}.$value: a stroke is a whole number of pixels"
    if let some t := fs.lookup "edge" then
      L := { L with strokes := { L.strokes with edge := ← weight "stroke.edge" t } }
      let x ← extOf "stroke.edge" (← fieldsOf "stroke.edge" t)
      onlyNames s!"stroke.edge.$extensions.{extKey}" x ["curve", "reach"]
      if let some cv := x.lookup "curve" then
        let s ← str s!"stroke.edge.$extensions.{extKey}.curve" cv
        match Curve.ofName? s with
        | some curve => L := { L with curve }
        | none => throw s!"stroke.edge.$extensions.{extKey}.curve: {s} is not bumpY, linear or stepY"
      if let some r := x.lookup "reach" then
        L := { L with reach := ← within s!"stroke.edge.$extensions.{extKey}.reach" 3 0 1000 r }
    if let some t := fs.lookup "frame" then
      L := { L with strokes := { L.strokes with frame := ← weight "stroke.frame" t } }
    if let some t := fs.lookup "rule" then
      L := { L with strokes := { L.strokes with rule := ← weight "stroke.rule" t } }
    if let some t := fs.lookup "radius" then
      let tf ← token "stroke.radius" "dimension" t
      L := { L with strokes := { L.strokes with radius := ← readPx "stroke.radius.$value" ((tf.lookup "$value").getD .null) } }
  if let some c := top.lookup "organic" then
    let fs ← group "organic" "" ["trunk", "fine", "flare", "noise", "wave"] c
    let px (path : String) (t : Json) : Read Nat := do
      let tf ← token path "dimension" t
      readPx s!"{path}.$value" ((tf.lookup "$value").getD .null)
    let mut o := L.organic
    if let some t := fs.lookup "trunk" then o := { o with trunk := ← px "organic.trunk" t }
    if let some t := fs.lookup "fine" then o := { o with fine := ← px "organic.fine" t }
    if let some t := fs.lookup "flare" then o := { o with flare := ← px "organic.flare" t }
    if let some t := fs.lookup "wave" then o := { o with wave := ← px "organic.wave" t }
    if let some t := fs.lookup "noise" then
      let tf ← token "organic.noise" "number" t
      o := { o with noise := ← within "organic.noise.$value" 3 0 1000 ((tf.lookup "$value").getD .null) }
    L := { L with organic := o }
  if let some c := top.lookup "motion" then
    let fs ← group "motion" "" ["step", "move", "leave", "write", "draw", "expand", "stagger", "enter"] c
    let mut m := L.motion
    if let some t := fs.lookup "step" then
      let step ← readDuration "motion.step" t
      if step == 0 then throw "motion.step: a step lasts some time" else m := { m with step }
    if let some t := fs.lookup "move" then m := { m with move := ← readTransition "motion.move" m.move t }
    if let some t := fs.lookup "leave" then m := { m with leave := ← readTransition "motion.leave" m.leave t }
    if let some t := fs.lookup "write" then m := { m with write := ← readTransition "motion.write" m.write t }
    if let some t := fs.lookup "draw" then m := { m with draw := ← readTransition "motion.draw" m.draw t }
    if let some t := fs.lookup "expand" then m := { m with expand := ← readTransition "motion.expand" m.expand t }
    if let some t := fs.lookup "stagger" then m := { m with stagger := ← readDuration "motion.stagger" t }
    if let some t := fs.lookup "enter" then m := { m with enterFrom := ← readDuration "motion.enter" t }
    L := { L with motion := m }
  pure L

/-- A look read from a token file's text over a base. -/
def parseLook (base : Look) (name text : String) : Read Look := do
  readLook base name (← Json.parse text)

/-- Whether a look comes back from its own written form, over any base. -/
def roundTrips (base L : Look) : Bool :=
  match parseLook base L.name (render L) with
  | .ok L' => decide (L' = L)
  | .error _ => false

/-! ## CSS -/

/-- **A look as CSS custom properties** on `[data-look="<name>"]`. A colour is the one each role
is drawn in (`Look.color`), so the hue rule holds in CSS too. -/
def css (L : Look) : String :=
  let font (face : Face) : List String :=
    let f := L.faces.of face
    [s!"--e4-font-{face.tokenName}-family: {f.cssFamily};", s!"--e4-font-{face.tokenName}-size: {f.px}px;",
      s!"--e4-font-{face.tokenName}-weight: {f.weight};", s!"--e4-font-{face.tokenName}-style: {f.style};"]
  let tr (n : String) (t : Transition) : List String :=
    [s!"--e4-motion-{n}-duration: {t.duration}ms;", s!"--e4-motion-{n}-delay: {t.delay}ms;",
      s!"--e4-motion-{n}-easing: {t.ease.css};"]
  let m := L.motion
  let props :=
    [s!"color-scheme: {L.scheme.name};"] ++
    Role.all.map (fun role => s!"--e4-color-{role.tokenName}: {(L.color role).css};") ++
    [s!"--e4-tone-band: {decimal L.band 3};"] ++
    Face.all.flatMap font ++
    [s!"--e4-stroke-edge: {L.strokes.edge}px;", s!"--e4-stroke-frame: {L.strokes.frame}px;",
      s!"--e4-stroke-rule: {L.strokes.rule}px;", s!"--e4-stroke-radius: {decimal L.strokes.radius 3}px;",
      s!"--e4-organic-trunk: {decimal L.organic.trunk 3}px;", s!"--e4-organic-fine: {decimal L.organic.fine 3}px;",
      s!"--e4-organic-flare: {decimal L.organic.flare 3}px;", s!"--e4-organic-noise: {decimal L.organic.noise 3};",
      s!"--e4-organic-wave: {decimal L.organic.wave 3}px;", s!"--e4-motion-step: {m.step}ms;"] ++
    tr "move" m.move ++ tr "leave" m.leave ++ tr "write" m.write ++ tr "draw" m.draw ++
    tr "expand" m.expand ++
    [s!"--e4-motion-stagger: {m.stagger}ms;", s!"--e4-motion-enter: {m.enterFrom}ms;"]
  s!"[data-look=\"{L.name}\"] " ++ "{\n" ++ String.join (props.map ("  " ++ · ++ "\n")) ++ "}\n"

/-- **The class rules** of a picture's SVG, the same for every look: each class takes its colour
and its type from the look's custom properties. -/
def rules : String :=
  let lines :=
    [".e4-view { background: var(--e4-color-ground); }"] ++
    Role.all.map (fun role => s!".e4-fill-{role.tokenName} \{ fill: var(--e4-color-{role.tokenName}); }") ++
    Role.all.map (fun role => s!".e4-stroke-{role.tokenName} \{ stroke: var(--e4-color-{role.tokenName}); }") ++
    [".e4-text { fill: var(--e4-color-ink); }"] ++
    Face.all.map fun face =>
      s!".e4-face-{face.tokenName} \{ font-family: var(--e4-font-{face.tokenName}-family); font-size: var(--e4-font-{face.tokenName}-size); font-weight: var(--e4-font-{face.tokenName}-weight); font-style: var(--e4-font-{face.tokenName}-style); }"
  String.join (lines.map (· ++ "\n"))

end Tools.View.Tokens
