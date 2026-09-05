/-!
# OCaml5.Ml.Identifier

The generated-identifier profile of the OCaml target: what a name may look like, which names are
taken, and the total injective mangling that turns a Lean name into an OCaml one.

Precedent: `TypeScript.Identifier` in the estate's TypeScript target package — "the deliberately
narrow generated-binding profile: identifier characters the compiler accepts and no reserved
word". This module is its OCaml counterpart and, like it, knows nothing about any effect system.

OCaml manual references are to the 5.1.1 manual:

* §11.1 *Lexical conventions*, "Identifiers" and "Keywords" — the character class and the
  55 reserved words;
* §11.1, "Integer literals", "Floating-point literals", "Character literals", "String literals" —
  the escape sequences `escString` and `escChar` produce;
* §11.4 *Names* — the capitalisation rule: a `value-name` and a `field-name` begin with a
  lowercase letter or `_`, a `constr-name`, `tag-name` and `module-name` with an uppercase
  letter, and a `typeconstr-name` follows the `value-name` class.

Nothing here allocates; every function is total and the mangling is injective by an exhibited
left inverse (`unmangleField`).
-/

namespace OCaml5.Ml

/-! ## Literals

`escString` is the body of a `" … "` literal and `escChar` the body of a `' … '` literal, both in
the escapes of §11.1. Anything outside printable ASCII becomes a `\DDD` decimal escape, which is
the one escape form every OCaml backend agrees on byte for byte: `\uXXXX` is not OCaml, and a raw
byte above 126 in a source file makes the literal depend on the file's encoding. -/

/-- Three decimal digits, zero-padded: the `\DDD` escape's payload. -/
private def pad3 (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 3 then s else if s.length == 2 then "0" ++ s else "00" ++ s

/-- One character inside a `" … "` literal. -/
private def escStringChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\t' then "\\t"
  else if c == '\n' then "\\n"
  else if c.toNat < 32 || c.toNat > 126 then "\\" ++ pad3 c.toNat
  else String.singleton c

/-- The body of an OCaml string literal (§11.1, "String literals"). Total, and injective on the
printable-ASCII-plus-control alphabet: every escape is self-delimiting. -/
def escString (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++ escStringChar c

/-- The body of an OCaml character literal (§11.1, "Character literals"). A `'` must be escaped
here and a `"` need not be, which is why this is not `escString`. -/
def escChar (c : Char) : String :=
  if c == '\'' then "\\'"
  else if c == '\\' then "\\\\"
  else if c == '\t' then "\\t"
  else if c == '\n' then "\\n"
  else if c.toNat < 32 || c.toNat > 126 then "\\" ++ pad3 c.toNat
  else String.singleton c

/-! ## Reserved words -/

/-- The 56 keywords of OCaml 5.1.1 (§11.1, "Keywords"), in the manual's own order. -/
def reservedWords : List String :=
  ["and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done", "downto",
   "else", "end", "exception", "external", "false", "for", "fun", "function", "functor",
   "if", "in", "include", "inherit", "initializer", "land", "lazy", "let", "lor", "lsl",
   "lsr", "lxor", "match", "method", "mod", "module", "mutable", "new", "nonrec", "object",
   "of", "open", "or", "private", "rec", "sig", "struct", "then", "to", "true", "try",
   "type", "val", "virtual", "when", "while", "with"]

/-- Names that are legal but that a generator must not produce, because the reader would take
them for something else. One entry: a record field named `exit` is legal, but `f.exit` reads as
`Stdlib.exit` at a glance, and the avatar spells it `exit_` (`avatar/deep_fibers.ml:194`). -/
def shadowedNames : List String := ["exit"]

/-- The names `mangleField` steps around: the keywords, plus `shadowedNames`. -/
def reservedNames : List String := reservedWords ++ shadowedNames

/-! ## The character classes of §11.1 and §11.4 -/

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentRest (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_' || c == '\''

/-- `ident` of §11.1: a letter or `_`, then letters, digits, `_` and `'`. -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isIdentStart c && rest.all isIdentRest

/-- `value-name`, `field-name`, `typeconstr-name`, `label-name` (§11.4): an `ident` that does not
begin with an uppercase letter, and is not a keyword. -/
def isLowerIdent (s : String) : Bool :=
  isIdent s && (match s.toList with
                | [] => false
                | c :: _ => !c.isUpper)
    && !reservedWords.contains s

/-- `constr-name`, `module-name`, `modtype-name` and a polymorphic-variant `tag-name` (§11.4):
an `ident` beginning with an uppercase letter. Keywords cannot be reached — every keyword is
lowercase — so no keyword test is needed. -/
def isUpperIdent (s : String) : Bool :=
  isIdent s && (match s.toList with
                | [] => false
                | c :: _ => c.isUpper)

/-- A qualified spelling `A.B.c` (§11.4, "extended names"): every segment but the last is a
module name, the last is `p`. -/
def isQualified (p : String → Bool) (s : String) : Bool :=
  match s.splitOn "." with
  | [] => false
  | [one] => p one
  | segs =>
      match segs.reverse with
      | [] => false
      | last :: mods => p last && mods.all isUpperIdent

/-- A qualified value name: `f`, `M.f`, `Effect.Deep.continue`. -/
def isValuePath (s : String) : Bool := isQualified isLowerIdent s

/-- A qualified constructor name: `Some`, `Effect.Unhandled`. The list constructors `[]` and
`::`, which the syntax spells as constructor names, are admitted here because OCaml admits them
in constructor position. -/
def isCtorPath (s : String) : Bool :=
  s == "[]" || s == "::" || s == "()" || s == "true" || s == "false" || isQualified isUpperIdent s

/-- A qualified type constructor name: `int`, `Effect.t`, `Effect.Deep.continuation`. -/
def isTypePath (s : String) : Bool := isQualified isLowerIdent s

/-- A module path: `M`, `M.N`. -/
def isModulePath (s : String) : Bool := isQualified isUpperIdent s

/-- A type variable name, without its `'` (§11.2, `'ident`). -/
def isTyVar (s : String) : Bool := isIdent s

/-! ## The mangling

`mangleField` is **total** and **injective**; `unmangleField` is an exhibited left inverse, and
`MlTest` runs the round trip over every field name the estate's descriptions render plus a row of
adversarial ones. The code, character by character:

| source | image |
| --- | --- |
| a lowercase letter or a digit | itself |
| an uppercase `X` | `_` ++ lowercase `X` (this is camelCase → snake_case) |
| `_` | `_0` |
| `'` | `_1` |
| anything else, code `c` | `_2` ++ three decimal digits of `c` |

and a result that is in `reservedNames` gets one `_` appended. That last step cannot collide: no
image of the character code ends in a bare `_`, because every escape `_` is followed by a letter
or a digit. `exit` → `exit_` is `avatar/deep_fibers.ml:194`.

The naive alternative, a plain camelCase → snake_case, is **not** injective: `aB` and `a_b` both
go to `a_b`. Here they are separated, `a_b` and `a_0b`. A simulation relation is stated field by
field, so a collision in the field mangling is a hole in the relation. -/

private def encChar (c : Char) : String :=
  if c.isLower || c.isDigit then String.singleton c
  else if c.isUpper then "_" ++ String.singleton (Char.ofNat (c.toNat + 32))
  else if c == '_' then "_0"
  else if c == '\'' then "_1"
  else "_2" ++ pad3 c.toNat

/-- The character code, before the reserved-name escape. -/
def mangleCore (s : String) : String := s.foldl (init := "") fun acc c => acc ++ encChar c

/-- A Lean field name as an OCaml record label. Total; `unmangleField` is a left inverse. -/
def mangleField (s : String) : String :=
  let e := mangleCore s
  if reservedNames.contains e then e ++ "_" else e

private def decodeAux : List Char → List Char
  | [] => []
  | '_' :: [] => []                                        -- the reserved-name escape
  | '_' :: '0' :: rest => '_' :: decodeAux rest
  | '_' :: '1' :: rest => '\'' :: decodeAux rest
  | '_' :: '2' :: a :: b :: c :: rest =>
      Char.ofNat (100 * (a.toNat - 48) + 10 * (b.toNat - 48) + (c.toNat - 48))
        :: decodeAux rest
  | '_' :: x :: rest => Char.ofNat (x.toNat - 32) :: decodeAux rest
  | c :: rest => c :: decodeAux rest

/-- The left inverse of `mangleField`: `unmangleField (mangleField s) = s` for every `s`. -/
def unmangleField (s : String) : String := String.ofList (decodeAux s.toList)

/-- A Lean value name as an OCaml value name. The same code as `mangleField`; the two are one
function under two names because OCaml's `value-name` and `field-name` are one lexical class
(§11.4). -/
def valueName (s : String) : String := mangleField s

/-- The type-name code before the reserved-name escape: the field code minus the leading `_` an
initial capital produces. -/
private def typeNameCore (s : String) : String :=
  let e := mangleCore s
  if e.startsWith "_" then (e.drop 1).toString else e

/-- A Lean type name as an OCaml type name: the same code as a field, minus the leading `_` an
initial capital produces, and — as for `mangleField` — one `_` appended when the result is a
reserved word (`Val` → `val_`: `val` is a keyword, `avatar/deep_stores.ml`). Injective on names
whose first character is an uppercase ASCII letter. -/
def typeName (s : String) : String :=
  let e := typeNameCore s
  if reservedNames.contains e then e ++ "_" else e

/-- A Lean constructor name as an OCaml constructor name. With an empty prefix the initial is
capitalised (`resumeAwait` → `ResumeAwait`); with a prefix the prefix supplies the required
capital and the Lean name is kept verbatim (`"C"`, `evaluate` → `Cevaluate`), which is the
scheme `avatar/deep_fibers.ml` uses to keep `Cmd` and `RunDecision` from colliding with each
other and with `WithFiberAction`. Injective for a fixed prefix. -/
def ctorName (pfx : String) (s : String) : String :=
  if pfx.isEmpty then
    match s.toList with
    | [] => s
    | c :: rest => String.ofList (Char.ofNat (if c.isLower then c.toNat - 32 else c.toNat) :: rest)
  else pfx ++ s

/-- A Lean namespace or structure name as an OCaml module name: `typeName`, capitalised back.
`RunFiber` → `Run_fiber`, so that a module and the type it defines are distinguishable. -/
def moduleName (s : String) : String := ctorName "" (typeNameCore s)

/-- A Lean universe or type parameter as an OCaml type variable, without the `'`. Lean spells
its carrier parameters with Greek letters, which are not OCaml identifier characters, so the
Greek block is transliterated and anything else goes through `mangleCore`. -/
def tyVarName (s : String) : String :=
  match s with
  | "α" => "a" | "β" => "b" | "γ" => "c" | "δ" => "d" | "ε" => "e" | "ζ" => "z"
  | "η" => "h" | "θ" => "th" | "ι" => "i" | "κ" => "k" | "λ" => "l" | "μ" => "m"
  | "ν" => "nu" | "ξ" => "x" | "ο" => "o" | "π" => "p" | "ρ" => "r" | "σ" => "s"
  | "τ" => "t" | "υ" => "u" | "φ" => "f" | "χ" => "ch" | "ψ" => "ps" | "ω" => "w"
  | _ =>
    let e := mangleCore s
    if e.startsWith "_" then (e.drop 1).toString else e

/-! ## Checks -/

#guard escString "perform\tNumber" == "perform\\tNumber"
#guard escString "a\"b\\c" == "a\\\"b\\\\c"
#guard escChar '\'' == "\\'"
#guard escChar 'a' == "a"

#guard reservedWords.length == 56
#guard reservedNames.length == 57

#guard mangleField "aB" == "a_b"
#guard mangleField "a_b" == "a_0b"
#guard mangleField "exit" == "exit_"
#guard mangleField "type" == "type_"
#guard mangleField "currentOpCount" == "current_op_count"
#guard typeName "RunFiber" == "run_fiber"
#guard typeName "WithFiberAction" == "with_fiber_action"
#guard moduleName "RunFiber" == "Run_fiber"
#guard ctorName "" "resumeAwait" == "ResumeAwait"
#guard ctorName "C" "drainDue" == "CdrainDue"
#guard ctorName "D" "yieldVerdict" == "DyieldVerdict"
#guard tyVarName "ν" == "nu"
#guard tyVarName "α" == "a"
#guard tyVarName "u" == "u"

-- The round trip, on the adversarial row: the two names a naive camel-to-snake would collapse,
-- every keyword shape, the empty name, and the escapes.
#guard ["exit", "type", "currentOpCount", "a_b", "aB", "x'", "ABC", "", "let", "a__b",
        "a.b", "ν", "f0", "_x", "with"].all
  (fun n => unmangleField (mangleField n) == n)

-- The profile predicates agree with the manual's classes.
#guard isLowerIdent "run_fiber" && isLowerIdent "exit_" && isLowerIdent "_x"
#guard !isLowerIdent "RunFiber" && !isLowerIdent "with" && !isLowerIdent "a-b"
#guard isUpperIdent "Some" && !isUpperIdent "some"
#guard isValuePath "Effect.Deep.continue" && isValuePath "f"
#guard !isValuePath "Effect.Deep.Continue"
#guard isCtorPath "Effect.Unhandled" && isCtorPath "[]" && isCtorPath "::"
#guard isTypePath "Effect.t" && isTypePath "int"
#guard isModulePath "Effect.Deep" && !isModulePath "Effect.t"

end OCaml5.Ml
