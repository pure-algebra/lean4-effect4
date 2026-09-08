import Std

/-!
# Ingest.Taxonomy

The closed refusal alphabet of the ingestion specification. Both recognizers receive
this table through Tools.TsGen, including the total active/reserved partition and the
literal detail templates. A detail substitutes its one `{value}` field, never paraphrases.
The enumeration pattern follows foldlab Cas/Lift/Taxonomy.lean at
4005d34f249cda25134ac2bddff514e3a068bc1e (read-only source).
-/

namespace Effect4.Ingest

inductive Code
  | paramShape
  | spineEscape
  | yieldPosition
  | bindShape
  | stmtShape
  | opReceiver
  | opUnknown
  | branch
  | loop
  | handler
  | returnShape
  | nodeShape
  | argDynamic
  | argClosure
  | refUnbound
  | refForward
  | answerHigherOrder
  | failNotDocumented
  | importOpaque
  | helperUnpinned
  | typeParam
  | node
  | program
deriving DecidableEq, BEq, Repr

inductive Spectrum
  | classification | applicativeGap | monadic | instrument
deriving DecidableEq, BEq, Repr

def Spectrum.wire : Spectrum → String
  | .classification => "classification"
  | .applicativeGap => "applicative-gap"
  | .monadic => "monadic"
  | .instrument => "instrument"

inductive Status
  | active | reserved
deriving DecidableEq, BEq, Repr

def Status.wire : Status → String
  | .active => "active"
  | .reserved => "reserved"

namespace Code

def wire : Code → String
  | .paramShape => "E-PARAM-SHAPE"
  | .spineEscape => "E-SPINE-ESCAPE"
  | .yieldPosition => "E-YIELD-POSITION"
  | .bindShape => "E-BIND-SHAPE"
  | .stmtShape => "E-STMT-SHAPE"
  | .opReceiver => "E-OP-RECEIVER"
  | .opUnknown => "E-OP-UNKNOWN"
  | .branch => "E-BRANCH"
  | .loop => "E-LOOP"
  | .handler => "E-HANDLER"
  | .returnShape => "E-RETURN-SHAPE"
  | .nodeShape => "E-NODE-SHAPE"
  | .argDynamic => "E-ARG-DYNAMIC"
  | .argClosure => "E-ARG-CLOSURE"
  | .refUnbound => "E-REF-UNBOUND"
  | .refForward => "E-REF-FORWARD"
  | .answerHigherOrder => "E-ANSWER-HIGHER-ORDER"
  | .failNotDocumented => "E-FAIL-NOT-DOCUMENTED"
  | .importOpaque => "E-IMPORT-OPAQUE"
  | .helperUnpinned => "E-HELPER-UNPINNED"
  | .typeParam => "E-TYPE-PARAM"
  | .node => "E-NODE"
  | .program => "E-PROGRAM"

def all : List Code :=
  [.paramShape, .spineEscape, .yieldPosition, .bindShape, .stmtShape, .opReceiver, .opUnknown, .branch, .loop, .handler, .returnShape, .nodeShape, .argDynamic, .argClosure, .refUnbound, .refForward, .answerHigherOrder, .failNotDocumented, .importOpaque, .helperUnpinned, .typeParam, .node, .program]

theorem all_complete (c : Code) : c ∈ all := by cases c <;> simp [all]

def spectrum : Code → Spectrum
  | .paramShape => .classification
  | .spineEscape => .monadic
  | .yieldPosition => .monadic
  | .bindShape => .applicativeGap
  | .stmtShape => .classification
  | .opReceiver => .classification
  | .opUnknown => .classification
  | .branch => .monadic
  | .loop => .monadic
  | .handler => .monadic
  | .returnShape => .classification
  | .nodeShape => .classification
  | .argDynamic => .classification
  | .argClosure => .classification
  | .refUnbound => .classification
  | .refForward => .classification
  | .answerHigherOrder => .classification
  | .failNotDocumented => .classification
  | .importOpaque => .classification
  | .helperUnpinned => .instrument
  | .typeParam => .classification
  | .node => .instrument
  | .program => .instrument

def status : Code → Status
  | .helperUnpinned => .reserved
  | _ => .active

theorem reserved_iff (c : Code) : status c = .reserved ↔ c = .helperUnpinned := by
  cases c <;> decide

def detailTemplate : Code → String
  | .paramShape => "unit parameters: {value}"
  | .spineEscape => "spine escape: {value}"
  | .yieldPosition => "yield position: {value}"
  | .bindShape => "binding shape: {value}"
  | .stmtShape => "statement shape: {value}"
  | .opReceiver => "unresolved receiver: {value}"
  | .opUnknown => "unknown head: {value}"
  | .branch => "branch shape: {value}"
  | .loop => "loop shape: {value}"
  | .handler => "unsupported handler: {value}"
  | .returnShape => "return shape: {value}"
  | .nodeShape => "syntax shape: {value}"
  | .argDynamic => "dynamic argument: {value}"
  | .argClosure => "unknown closure: {value}"
  | .refUnbound => "unbound reference: {value}"
  | .refForward => "forward reference: {value}"
  | .answerHigherOrder => "answer called: {value}"
  | .failNotDocumented => "failure payload: {value}"
  | .importOpaque => "opaque import: {value}"
  | .helperUnpinned => "reserved helper: {value}"
  | .typeParam => "type parameter: {value}"
  | .node => "fragment node: {value}"
  | .program => "program shape: {value}"

#guard all.length == 23
#guard (all.map wire).eraseDups.length == all.length
#guard all.filter (fun c => status c == .reserved) == [.helperUnpinned]

end Code
end Effect4.Ingest
