import Effect4.Program.Native
import Effect4.Store.Canonical

/-!
# Program.Wire

Owner: the canonical bytes of an `Eff` program, and the exact decoder.

A program crosses a boundary — the store, the OCaml host, the daemon — as bytes, and the
bytes have to be a function of the program alone and decode back to exactly that program,
or the address of a program means nothing and a host could run something other than what
it was sent. The framing is `Store.Canonical`'s: every value is `tag :: be64 length ++
payload`. Inductives use one tag, `Tag.ctor`, whose payload is the constructor's 0-based
index (in declaration order) as a `Nat` frame followed by the framed arguments; a
structure is constructor 0 with its fields in declaration order; the mutual list types
(`Terms`, `Stmts`, `Effs`) are inductives with `nil` = 0 and `cons` = 1.

The decoder is length-directed and exact: a wrong tag, a bad index, a short payload, a
leading zero digit, an unconsumed byte inside a frame or after the program are refusals,
never repairs. It is total: fuel bounds the recursion, and the byte length is more than
enough fuel because every frame costs at least nine bytes.

Laws owed: `decodeProgram (encodeProgram p) = some p` (checked on the corpus below,
theorem pending) and exactness, `decodeProgram b = some p → b = encodeProgram p` (pending).
The same rule is implemented on the OCaml side (`ocaml/eff`) from the same
constructor order, and the goldens `tools/EffWire.lean` prints are the cross-check.
-/

namespace Effect4.Program.Wire

open Effect4 Effect4.Store Effect4.Program
open Effect4.Supervision (ForkOptions MaskMode ObserverMode)

/-- A constructor frame: the index, then the framed arguments. -/
def ctor (i : Nat) (args : List Bytes) : Bytes :=
  framed Tag.ctor (encode i ++ args.flatten)

/-! ## Encoding -/

def encLit : Lit → Bytes
  | .unit => ctor 0 []
  | .nat n => ctor 1 [encode n]
  | .bool b => ctor 2 [encode b]
  | .str s => ctor 3 [encode s]

mutual
  def encTerm : Term → Bytes
    | .var i => ctor 0 [encode i]
    | .lit l => ctor 1 [encLit l]
    | .app atom args => ctor 2 [encode atom, encTerms args]
  def encTerms : Terms → Bytes
    | .nil => ctor 0 []
    | .cons h t => ctor 1 [encTerm h, encTerms t]
end

def encOptTerm : Option Term → Bytes
  | none => framed Tag.none []
  | some t => framed Tag.some (encTerm t)

def encCause : CauseTerm → Bytes
  | .fail t => ctor 0 [encTerm t]
  | .die t => ctor 1 [encTerm t]
  | .interrupt o => ctor 2 [encOptTerm o]
  | .both a b => ctor 3 [encCause a, encCause b]

def encFn : Machine.FnName → Bytes
  | .incr => ctor 0 []
  | .double => ctor 1 []
  | .zeroWhenPositive => ctor 2 []
  | .noChange => ctor 3 []
  | .takeAndBump => ctor 4 []

def encStrategy : FinalizerStrategy → Bytes
  | .sequential => ctor 0 []
  | .parallel => ctor 1 []

def encOp : NativeOp → Bytes
  | .refMake => ctor 0 []
  | .refGet => ctor 1 []
  | .refSet => ctor 2 []
  | .refGetAndSet => ctor 3 []
  | .refSetAndGet => ctor 4 []
  | .refUpdate f => ctor 5 [encFn f]
  | .refGetAndUpdate f => ctor 6 [encFn f]
  | .refUpdateAndGet f => ctor 7 [encFn f]
  | .refUpdateSome f => ctor 8 [encFn f]
  | .refGetAndUpdateSome f => ctor 9 [encFn f]
  | .refUpdateSomeAndGet f => ctor 10 [encFn f]
  | .refModify f => ctor 11 [encFn f]
  | .refModifySome f => ctor 12 [encFn f]
  | .deferredMake => ctor 13 []
  | .deferredIsDone => ctor 14 []
  | .deferredPoll => ctor 15 []
  | .deferredSucceed => ctor 16 []
  | .deferredFail => ctor 17 []
  | .deferredAwait => ctor 18 []
  | .scopeMake s => ctor 19 [encStrategy s]

def encMask : MaskMode → Bytes
  | .interruptible => ctor 0 []
  | .uninterruptible => ctor 1 []
  | .inherit => ctor 2 []

def encMode : ObserverMode → Bytes
  | .awaitValue => ctor 0 []
  | .joinEffect => ctor 1 []

def encFork (o : ForkOptions) : Bytes :=
  ctor 0 [encode o.startImmediately, encode o.daemon, encMask o.maskMode]

mutual
  def encEff : Eff NativeOp → Bytes
    | .succeed v => ctor 0 [encTerm v]
    | .fail e => ctor 1 [encTerm e]
    | .failCause c => ctor 2 [encCause c]
    | .yieldError e => ctor 3 [encTerm e]
    | .sync t => ctor 4 [encTerm t]
    | .suspend b => ctor 5 [encEff b]
    | .perform op r => ctor 6 [encOp op, encTerm r]
    | .bind a b => ctor 7 [encEff a, encEff b]
    | .gen body => ctor 8 [encStmts body]
    | .catchCause b h => ctor 9 [encEff b, encEff h]
    | .matchCause b v c => ctor 10 [encEff b, encEff v, encEff c]
    | .onExit b f => ctor 11 [encEff b, encEff f]
    | .exit b => ctor 12 [encEff b]
    | .uninterruptible b => ctor 13 [encEff b]
    | .interruptible b => ctor 14 [encEff b]
    | .branch t a b => ctor 15 [encTerm t, encEff a, encEff b]
    | .whileLoop i t s b => ctor 16 [encTerm i, encTerm t, encTerm s, encEff b]
    | .yieldNow p => ctor 17 [encode p]
    | .callback reg r => ctor 18 [encOp reg, encTerm r]
    | .awaitFiber f m => ctor 19 [encTerm f, encMode m]
    | .withFiber a => ctor 20 [encAction a]
    | .scoped b => ctor 21 [encEff b]
    | .acquireRelease a r => ctor 22 [encEff a, encEff r]
    | .choose site l r => ctor 23 [encode site, encEff l, encEff r]
  def encStmt : Stmt NativeOp → Bytes
    | .bindYield e => ctor 0 [encEff e]
    | .yieldDiscard e => ctor 1 [encEff e]
    | .ret v => ctor 2 [encTerm v]
    | .ifElse t a b => ctor 3 [encTerm t, encStmts a, encStmts b]
    | .whileTrue b => ctor 4 [encStmts b]
    | .breakLoop => ctor 5 []
  def encStmts : Stmts NativeOp → Bytes
    | .nil => ctor 0 []
    | .cons h t => ctor 1 [encStmt h, encStmts t]
  def encEffs : Effs NativeOp → Bytes
    | .nil => ctor 0 []
    | .cons h t => ctor 1 [encEff h, encEffs t]
  def encAction : ActionTerm NativeOp → Bytes
    | .fork p o => ctor 0 [encEff p, encFork o]
    | .forkIn p o s => ctor 1 [encEff p, encFork o, encTerm s]
    | .forkScoped p o => ctor 2 [encEff p, encFork o]
    | .runIn t s => ctor 3 [encTerm t, encTerm s]
    | .interrupt t => ctor 4 [encTerm t]
    | .interruptScoped t => ctor 5 [encTerm t]
    | .interruptAll t i => ctor 6 [encTerm t, encOptTerm i]
    | .awaitAll t => ctor 7 [encTerm t]
    | .awaitAllFailFast t => ctor 8 [encTerm t]
    | .snapshotChildren => ctor 9 []
    | .awaitNewChildren s => ctor 10 [encTerm s]
    | .raceAll es => ctor 11 [encEffs es]
    | .setContext c => ctor 12 [encTerm c]
    | .getContext => ctor 13 []
    | .getId => ctor 14 []
    | .closeScope s e => ctor 15 [encTerm s, encTerm e]
end

/-- The canonical bytes of a program. -/
def encodeProgram : Eff NativeOp → Bytes := encEff

instance : Canonical (Eff NativeOp) := ⟨encodeProgram⟩

/-! ## Decoding: frames -/

/-- Big-endian bytes as a number. -/
def natOfDigits (b : Bytes) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- One frame: the tag, its payload, the rest. -/
def readFrame : Bytes → Option (UInt8 × Bytes × Bytes)
  | [] => none
  | tag :: rest =>
    if rest.length < 8 then none else
      let len := natOfDigits (rest.take 8)
      let body := rest.drop 8
      if body.length < len then none else some (tag, body.take len, body.drop len)

/-- Nothing may be left over. -/
def done : Bytes → Option Unit
  | [] => some ()
  | _ => none

def readNat (b : Bytes) : Option (Nat × Bytes) := do
  let (tag, payload, rest) ← readFrame b
  guard (tag = Tag.nat)
  guard (payload.head? ≠ some 0)
  pure (natOfDigits payload, rest)

def readBool (b : Bytes) : Option (Bool × Bytes) := do
  let (tag, payload, rest) ← readFrame b
  guard (tag = Tag.bool)
  match payload with
  | [0] => pure (false, rest)
  | [1] => pure (true, rest)
  | _ => none

/-- Whether a byte is a UTF-8 continuation byte, and its six payload bits. -/
def contBits (b : UInt8) : Option Nat :=
  if b.toNat < 0x80 || b.toNat ≥ 0xC0 then none else some (b.toNat - 0x80)

/-- Strict UTF-8: shortest forms only, no surrogates, at most `0x10FFFF`. Fuel is the byte
count. Written here rather than through `String.fromUTF8?` because that route reaches
`Classical.choice` on this toolchain and this is a semantic definition. -/
def utf8Chars : Nat → Bytes → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b0 :: rest =>
    let x := b0.toNat
    if x < 0x80 then do
      let cs ← utf8Chars fuel rest
      pure (Char.ofNat x :: cs)
    else if x < 0xC2 then none
    else if x < 0xE0 then
      match rest with
      | b1 :: rest' => do
        let c1 ← contBits b1
        let cs ← utf8Chars fuel rest'
        pure (Char.ofNat ((x - 0xC0) * 64 + c1) :: cs)
      | _ => none
    else if x < 0xF0 then
      match rest with
      | b1 :: b2 :: rest' => do
        let c1 ← contBits b1
        let c2 ← contBits b2
        let n := (x - 0xE0) * 4096 + c1 * 64 + c2
        guard (n ≥ 0x800 ∧ (n < 0xD800 ∨ n > 0xDFFF))
        let cs ← utf8Chars fuel rest'
        pure (Char.ofNat n :: cs)
      | _ => none
    else if x < 0xF5 then
      match rest with
      | b1 :: b2 :: b3 :: rest' => do
        let c1 ← contBits b1
        let c2 ← contBits b2
        let c3 ← contBits b3
        let n := (x - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3
        guard (n ≥ 0x10000 ∧ n ≤ 0x10FFFF)
        let cs ← utf8Chars fuel rest'
        pure (Char.ofNat n :: cs)
      | _ => none
    else none

/-- A string frame: strict UTF-8, and the string's own bytes must be the payload (the
exactness of this frame is checked, not assumed). -/
def readString (b : Bytes) : Option (String × Bytes) := do
  let (tag, payload, rest) ← readFrame b
  guard (tag = Tag.string)
  let cs ← utf8Chars payload.length payload
  let s := String.ofList cs
  guard (s.toUTF8.data.toList = payload)
  pure (s, rest)

/-- A constructor frame: the index, the argument bytes, the rest. -/
def readCtor (b : Bytes) : Option (Nat × Bytes × Bytes) := do
  let (tag, payload, rest) ← readFrame b
  guard (tag = Tag.ctor)
  let (i, args) ← readNat payload
  pure (i, args, rest)

/-! ## Decoding: the families, under fuel -/

def decLit (b : Bytes) : Option (Lit × Bytes) := do
  let (i, args, rest) ← readCtor b
  match i with
  | 0 => do done args; pure (.unit, rest)
  | 1 => do let (n, r) ← readNat args; done r; pure (.nat n, rest)
  | 2 => do let (x, r) ← readBool args; done r; pure (.bool x, rest)
  | 3 => do let (s, r) ← readString args; done r; pure (.str s, rest)
  | _ => none

mutual
  def decTerm : Nat → Bytes → Option (Term × Bytes)
    | 0, _ => none
    | fuel + 1, b => do
      let (i, args, rest) ← readCtor b
      match i with
      | 0 => do let (n, r) ← readNat args; done r; pure (.var n, rest)
      | 1 => do let (l, r) ← decLit args; done r; pure (.lit l, rest)
      | 2 => do
        let (atom, r) ← readString args
        let (ts, r) ← decTerms fuel r
        done r
        pure (.app atom ts, rest)
      | _ => none
  def decTerms : Nat → Bytes → Option (Terms × Bytes)
    | 0, _ => none
    | fuel + 1, b => do
      let (i, args, rest) ← readCtor b
      match i with
      | 0 => do done args; pure (.nil, rest)
      | 1 => do
        let (h, r) ← decTerm fuel args
        let (t, r) ← decTerms fuel r
        done r
        pure (.cons h t, rest)
      | _ => none
end

def decOptTerm (fuel : Nat) (b : Bytes) : Option (Option Term × Bytes) := do
  let (tag, payload, rest) ← readFrame b
  if tag = Tag.none then do done payload; pure (none, rest)
  else if tag = Tag.some then do
    let (t, r) ← decTerm fuel payload
    done r
    pure (some t, rest)
  else none

def decCause : Nat → Bytes → Option (CauseTerm × Bytes)
  | 0, _ => none
  | fuel + 1, b => do
    let (i, args, rest) ← readCtor b
    match i with
    | 0 => do let (t, r) ← decTerm fuel args; done r; pure (.fail t, rest)
    | 1 => do let (t, r) ← decTerm fuel args; done r; pure (.die t, rest)
    | 2 => do let (o, r) ← decOptTerm fuel args; done r; pure (.interrupt o, rest)
    | 3 => do
      let (a, r) ← decCause fuel args
      let (c, r) ← decCause fuel r
      done r
      pure (.both a c, rest)
    | _ => none

/-- A constructor with no arguments, by index. -/
def decEnum (table : List α) (b : Bytes) : Option (α × Bytes) := do
  let (i, args, rest) ← readCtor b
  done args
  let x ← table[i]?
  pure (x, rest)

def decFn : Bytes → Option (Machine.FnName × Bytes) :=
  decEnum [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

def decStrategy : Bytes → Option (FinalizerStrategy × Bytes) :=
  decEnum [.sequential, .parallel]

def decMask : Bytes → Option (MaskMode × Bytes) :=
  decEnum [.interruptible, .uninterruptible, .inherit]

def decMode : Bytes → Option (ObserverMode × Bytes) :=
  decEnum [.awaitValue, .joinEffect]

def decOp (b : Bytes) : Option (NativeOp × Bytes) := do
  let (i, args, rest) ← readCtor b
  let withFn (k : Machine.FnName → NativeOp) : Option (NativeOp × Bytes) := do
    let (f, r) ← decFn args
    done r
    pure (k f, rest)
  let bare (op : NativeOp) : Option (NativeOp × Bytes) := do
    done args
    pure (op, rest)
  match i with
  | 0 => bare .refMake
  | 1 => bare .refGet
  | 2 => bare .refSet
  | 3 => bare .refGetAndSet
  | 4 => bare .refSetAndGet
  | 5 => withFn .refUpdate
  | 6 => withFn .refGetAndUpdate
  | 7 => withFn .refUpdateAndGet
  | 8 => withFn .refUpdateSome
  | 9 => withFn .refGetAndUpdateSome
  | 10 => withFn .refUpdateSomeAndGet
  | 11 => withFn .refModify
  | 12 => withFn .refModifySome
  | 13 => bare .deferredMake
  | 14 => bare .deferredIsDone
  | 15 => bare .deferredPoll
  | 16 => bare .deferredSucceed
  | 17 => bare .deferredFail
  | 18 => bare .deferredAwait
  | 19 => do
    let (s, r) ← decStrategy args
    done r
    pure (.scopeMake s, rest)
  | _ => none

def decFork (b : Bytes) : Option (ForkOptions × Bytes) := do
  let (i, args, rest) ← readCtor b
  guard (i = 0)
  let (si, r) ← readBool args
  let (d, r) ← readBool r
  let (m, r) ← decMask r
  done r
  pure ({ startImmediately := si, daemon := d, maskMode := m }, rest)

mutual
  def decEff : Nat → Bytes → Option (Eff NativeOp × Bytes)
    | 0, _ => none
    | fuel + 1, b => do
      let (i, args, rest) ← readCtor b
      match i with
      | 0 => do let (v, r) ← decTerm fuel args; done r; pure (.succeed v, rest)
      | 1 => do let (e, r) ← decTerm fuel args; done r; pure (.fail e, rest)
      | 2 => do let (c, r) ← decCause fuel args; done r; pure (.failCause c, rest)
      | 3 => do let (e, r) ← decTerm fuel args; done r; pure (.yieldError e, rest)
      | 4 => do let (t, r) ← decTerm fuel args; done r; pure (.sync t, rest)
      | 5 => do let (e, r) ← decEff fuel args; done r; pure (.suspend e, rest)
      | 6 => do
        let (op, r) ← decOp args
        let (t, r) ← decTerm fuel r
        done r
        pure (.perform op t, rest)
      | 7 => do
        let (a, r) ← decEff fuel args
        let (c, r) ← decEff fuel r
        done r
        pure (.bind a c, rest)
      | 8 => do let (s, r) ← decStmts fuel args; done r; pure (.gen s, rest)
      | 9 => do
        let (a, r) ← decEff fuel args
        let (h, r) ← decEff fuel r
        done r
        pure (.catchCause a h, rest)
      | 10 => do
        let (a, r) ← decEff fuel args
        let (v, r) ← decEff fuel r
        let (c, r) ← decEff fuel r
        done r
        pure (.matchCause a v c, rest)
      | 11 => do
        let (a, r) ← decEff fuel args
        let (f, r) ← decEff fuel r
        done r
        pure (.onExit a f, rest)
      | 12 => do let (e, r) ← decEff fuel args; done r; pure (.exit e, rest)
      | 13 => do let (e, r) ← decEff fuel args; done r; pure (.uninterruptible e, rest)
      | 14 => do let (e, r) ← decEff fuel args; done r; pure (.interruptible e, rest)
      | 15 => do
        let (t, r) ← decTerm fuel args
        let (a, r) ← decEff fuel r
        let (c, r) ← decEff fuel r
        done r
        pure (.branch t a c, rest)
      | 16 => do
        let (i0, r) ← decTerm fuel args
        let (t, r) ← decTerm fuel r
        let (s, r) ← decTerm fuel r
        let (body, r) ← decEff fuel r
        done r
        pure (.whileLoop i0 t s body, rest)
      | 17 => do let (p, r) ← readNat args; done r; pure (.yieldNow p, rest)
      | 18 => do
        let (op, r) ← decOp args
        let (t, r) ← decTerm fuel r
        done r
        pure (.callback op t, rest)
      | 19 => do
        let (f, r) ← decTerm fuel args
        let (m, r) ← decMode r
        done r
        pure (.awaitFiber f m, rest)
      | 20 => do let (a, r) ← decAction fuel args; done r; pure (.withFiber a, rest)
      | 21 => do let (e, r) ← decEff fuel args; done r; pure (.scoped e, rest)
      | 22 => do
        let (a, r) ← decEff fuel args
        let (rel, r) ← decEff fuel r
        done r
        pure (.acquireRelease a rel, rest)
      | 23 => do
        let (site, r) ← readNat args
        let (l, r) ← decEff fuel r
        let (rr, r) ← decEff fuel r
        done r
        pure (.choose site l rr, rest)
      | _ => none
  def decStmt : Nat → Bytes → Option (Stmt NativeOp × Bytes)
    | 0, _ => none
    | fuel + 1, b => do
      let (i, args, rest) ← readCtor b
      match i with
      | 0 => do let (e, r) ← decEff fuel args; done r; pure (.bindYield e, rest)
      | 1 => do let (e, r) ← decEff fuel args; done r; pure (.yieldDiscard e, rest)
      | 2 => do let (v, r) ← decTerm fuel args; done r; pure (.ret v, rest)
      | 3 => do
        let (t, r) ← decTerm fuel args
        let (a, r) ← decStmts fuel r
        let (c, r) ← decStmts fuel r
        done r
        pure (.ifElse t a c, rest)
      | 4 => do let (s, r) ← decStmts fuel args; done r; pure (.whileTrue s, rest)
      | 5 => do done args; pure (.breakLoop, rest)
      | _ => none
  def decStmts : Nat → Bytes → Option (Stmts NativeOp × Bytes)
    | 0, _ => none
    | fuel + 1, b => do
      let (i, args, rest) ← readCtor b
      match i with
      | 0 => do done args; pure (.nil, rest)
      | 1 => do
        let (h, r) ← decStmt fuel args
        let (t, r) ← decStmts fuel r
        done r
        pure (.cons h t, rest)
      | _ => none
  def decEffs : Nat → Bytes → Option (Effs NativeOp × Bytes)
    | 0, _ => none
    | fuel + 1, b => do
      let (i, args, rest) ← readCtor b
      match i with
      | 0 => do done args; pure (.nil, rest)
      | 1 => do
        let (h, r) ← decEff fuel args
        let (t, r) ← decEffs fuel r
        done r
        pure (.cons h t, rest)
      | _ => none
  def decAction : Nat → Bytes → Option (ActionTerm NativeOp × Bytes)
    | 0, _ => none
    | fuel + 1, b => do
      let (i, args, rest) ← readCtor b
      match i with
      | 0 => do
        let (p, r) ← decEff fuel args
        let (o, r) ← decFork r
        done r
        pure (.fork p o, rest)
      | 1 => do
        let (p, r) ← decEff fuel args
        let (o, r) ← decFork r
        let (s, r) ← decTerm fuel r
        done r
        pure (.forkIn p o s, rest)
      | 2 => do
        let (p, r) ← decEff fuel args
        let (o, r) ← decFork r
        done r
        pure (.forkScoped p o, rest)
      | 3 => do
        let (t, r) ← decTerm fuel args
        let (s, r) ← decTerm fuel r
        done r
        pure (.runIn t s, rest)
      | 4 => do let (t, r) ← decTerm fuel args; done r; pure (.interrupt t, rest)
      | 5 => do let (t, r) ← decTerm fuel args; done r; pure (.interruptScoped t, rest)
      | 6 => do
        let (t, r) ← decTerm fuel args
        let (o, r) ← decOptTerm fuel r
        done r
        pure (.interruptAll t o, rest)
      | 7 => do let (t, r) ← decTerm fuel args; done r; pure (.awaitAll t, rest)
      | 8 => do let (t, r) ← decTerm fuel args; done r; pure (.awaitAllFailFast t, rest)
      | 9 => do done args; pure (.snapshotChildren, rest)
      | 10 => do let (s, r) ← decTerm fuel args; done r; pure (.awaitNewChildren s, rest)
      | 11 => do let (es, r) ← decEffs fuel args; done r; pure (.raceAll es, rest)
      | 12 => do let (c, r) ← decTerm fuel args; done r; pure (.setContext c, rest)
      | 13 => do done args; pure (.getContext, rest)
      | 14 => do done args; pure (.getId, rest)
      | 15 => do
        let (s, r) ← decTerm fuel args
        let (e, r) ← decTerm fuel r
        done r
        pure (.closeScope s e, rest)
      | _ => none
end

/-- The exact decoder: the whole byte string is one program and nothing else. Fuel is the
byte length plus one: every frame costs at least nine bytes, so nesting is shallower. -/
def decodeProgram (b : Bytes) : Option (Eff NativeOp) := do
  let (p, rest) ← decEff (b.length + 1) b
  done rest
  pure p

/-! ## The corpus, round-tripped -/

namespace Corpus

def forkOptions : ForkOptions := { startImmediately := false, daemon := false, maskMode := .inherit }

def p42 : Eff NativeOp := .succeed (.lit (.nat 42))
def pBind : Eff NativeOp :=
  .bind (.succeed (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))
def pFork : Eff NativeOp :=
  .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 7)))) forkOptions))
    (.awaitFiber (.var 0) .awaitValue)
def pAwait : Eff NativeOp :=
  .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))
def pGen : Eff NativeOp :=
  .gen (.cons (.bindYield (.succeed (.lit (.nat 3))))
    (.cons (.ifElse (.app "isZero" (.cons (.var 0) .nil)) (.cons (.ret (.lit (.bool true))) .nil)
      (.cons (.ret (.lit (.bool false))) .nil)) .nil))
/-- A loop that iterates: the cell is bound in front of the loop (`.var 0`), the cursor
(`.var 1`) starts at `0` and steps by `succ` while `isZero` holds, and each trip updates the
cell. The cell is what makes the body well-typed — `refUpdate`'s request row is
`Ref.Ref<number>` (`Native.lean`), not a number, so the cursor cannot stand in for it. -/
def pLoop : Eff NativeOp :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.whileLoop (.lit (.nat 0)) (.app "isZero" (.cons (.var 1) .nil))
      (.app "succ" (.cons (.var 1) .nil)) (.perform (.refUpdate .incr) (.var 0)))
def pCatch : Eff NativeOp :=
  .catchCause (.failCause (.both (.fail (.lit (.nat 1))) (.interrupt none)))
    (.succeed (.lit .unit))
/-- A scope acquired and released: `Scope.make` under an ambient `scoped`, then
`Scope.close` on that handle with a reified exit. Spelled as the pair rather than
`acquireRelease` for two reasons: `acquireRelease` binds the resource and the exit, so its
release cannot be `interruptAll`, which wants a list of fibers and a fiber id; and this cut
compiles `acquireRelease` to the frontier (`Compile.lean`), so a program built on it has no
Lean verdict to compare. -/
def pScope : Eff NativeOp :=
  .scoped (.bind (.perform (.scopeMake .parallel) (.lit .unit))
    (.bind (.exit (.succeed (.lit (.nat 1))))
      (.withFiber (.closeScope (.var 0) (.var 1)))))

def all : List (String × Eff NativeOp) :=
  [("p42", p42), ("pBind", pBind), ("pFork", pFork), ("pAwait", pAwait), ("pGen", pGen),
   ("pLoop", pLoop), ("pCatch", pCatch), ("pScope", pScope)]

end Corpus

-- Every corpus program is well-typed at the native signature, so `Api.printDecl` answers
-- for each and the rc.112 differential runs the declaration rather than a bare expression.
#guard Corpus.all.all fun (_, p) => (typeOf nativeSignature p).isSome
#guard Corpus.all.all fun (_, p) => decodeProgram (encodeProgram p) = some p
-- A byte appended or dropped is refused.
#guard Corpus.all.all fun (_, p) => decodeProgram (encodeProgram p ++ [0]) = none
#guard Corpus.all.all fun (_, p) => decodeProgram (encodeProgram p).dropLast = none
-- A non-canonical natural (leading zero digit) is refused.
#guard decodeProgram (framed Tag.ctor (framed Tag.nat [0, 17] ++ encTerm (.lit .unit))) = none

end Effect4.Program.Wire
