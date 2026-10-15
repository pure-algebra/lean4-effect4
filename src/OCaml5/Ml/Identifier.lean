/-!
# OCaml5.Ml.Identifier

The generated-identifier profile of the OCaml target: what a name may look like, which names are
taken, how a string literal is escaped, and how a Lean type parameter becomes a type variable.
The route's own naming of declarations, fields and constructors is `OCaml5.Lcnf.Naming`.

Precedent: `TypeScript.Identifier` in the estate's TypeScript target package — "the deliberately
narrow generated-binding profile: identifier characters the compiler accepts and no reserved
word". This module is its OCaml counterpart and, like it, knows nothing about any effect system.

OCaml manual references are to the 5.1.1 manual:

* §11.1 *Lexical conventions*, "Identifiers" and "Keywords" — the character class and the
  55 reserved words;
* §11.1, "String literals" — the escape sequences `escString` produces;
* §11.4 *Names* — the capitalisation rule: a `value-name` and a `field-name` begin with a
  lowercase letter or `_`, a `constr-name`, `tag-name` and `module-name` with an uppercase
  letter, and a `typeconstr-name` follows the `value-name` class.

Every function here is total.
-/

namespace OCaml5.Ml

/-! ## Literals

`escString` is the body of a `" … "` literal, in the escapes of §11.1. Anything outside
printable ASCII becomes a `\DDD` decimal escape, which is the one escape form every OCaml backend
agrees on byte for byte: `\uXXXX` is not OCaml, and a raw byte above 126 in a source file makes
the literal depend on the file's encoding. The route writes no character literal: a Lean `Char`
is its code point, an `int` (the type row of `Char`, `OCaml5.Lcnf.typeRows`). -/

/-- Three decimal digits, zero-padded: the `\DDD` escape's payload. -/
private def pad3 (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 3 then s else if s.length == 2 then "0" ++ s else "00" ++ s

/-- One UTF-8 byte inside a `" … "` literal. OCaml decimal escapes encode bytes,
not Unicode scalar numbers. -/
private def escStringByte (b : UInt8) : String :=
  let c := Char.ofNat b.toNat
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\t' then "\\t"
  else if c == '\n' then "\\n"
  else if c.toNat < 32 || c.toNat > 126 then "\\" ++ pad3 c.toNat
  else String.singleton c

/-- The body of an OCaml string literal (§11.1, "String literals"). Non-ASCII scalars
are first encoded as UTF-8, then each byte gets a three-digit escape. -/
def escString (s : String) : String :=
  s.toUTF8.data.foldl (init := "") fun acc b => acc ++ escStringByte b

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

/-- A qualified type constructor name: `int`, `Effect.t`, `Effect.Deep.continuation`. -/
def isTypePath (s : String) : Bool := isQualified isLowerIdent s

/-! ## Type variables

A Lean type parameter becomes an OCaml type variable through a character code: a lowercase letter
or a digit is itself, an uppercase `X` is `_` and lowercase `X`, `_` is `_0`, `'` is `_1`, and any
other character is `_2` and its three-digit code. Lean spells its carrier parameters with Greek
letters, which are not OCaml identifier characters, so the Greek block is transliterated first. -/

private def encChar (c : Char) : String :=
  if c.isLower || c.isDigit then String.singleton c
  else if c.isUpper then "_" ++ String.singleton (Char.ofNat (c.toNat + 32))
  else if c == '_' then "_0"
  else if c == '\'' then "_1"
  else "_2" ++ pad3 c.toNat

/-- The character code, before the reserved-name escape. -/
def mangleCore (s : String) : String := s.foldl (init := "") fun acc c => acc ++ encChar c

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

#guard reservedWords.length == 56
#guard reservedNames.length == 57

#guard tyVarName "ν" == "nu"
#guard tyVarName "α" == "a"
#guard tyVarName "u" == "u"
#guard tyVarName "St" == "st"

-- The profile predicates agree with the manual's classes.
#guard isLowerIdent "run_fiber" && isLowerIdent "exit_" && isLowerIdent "_x"
#guard !isLowerIdent "RunFiber" && !isLowerIdent "with" && !isLowerIdent "a-b"
#guard isUpperIdent "Some" && !isUpperIdent "some"
#guard isTypePath "Effect.t" && isTypePath "int" && !isTypePath "Effect.T"

end OCaml5.Ml
