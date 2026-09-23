import Effect4.Api

set_option maxRecDepth 10000
open Effect4 Effect4.Machine Effect4.Program
def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def budget : Nat := 120
def evaluate : Api.Decision := .evaluate Api.root
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def replyRoot (answer : Completion Val Err Defect FiberId Ann) (token : Nat := 0) :
    Api.Decision := .answerAsync Api.root token answer
/-- Park on a fresh deferred: the masked region has to be suspended for a decision to land. -/
def waiting : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))

/-- `catchAll(uninterruptible(await >> fail 42), _ => succeed 0)`. -/
def escape : NativeEff :=
  .catchIf yes (.uninterruptible (.bind waiting (.fail (n 42)))) (.succeed (n 0))
/-- The region resumes with no interrupt recorded. -/
def quiet : List Api.Decision := [evaluate, replyRoot (.ofExit (.success .unit))]
/-- The interrupt is recorded while the root is masked, then the region resumes. -/
def poisoned : List Api.Decision :=
  [evaluate, interruptRoot, replyRoot (.ofExit (.success .unit))]


#guard typeOf nativeSignature escape = some ⟨.nat, .never, .empty⟩
#guard (Api.replay escape budget quiet).exit = some (.success (.nat 0))
#eval (Api.replay escape budget poisoned).exit.map fun (ex : ExitV) => match ex with
  | .success _ => []
  | .failure cause => cause.reasons.map fun (reason : Reason Err Defect FiberId Ann) => match reason with
    | .interrupt who ann => (ReasonTag.interrupt, who, ann.entries)
    | .fail _ ann => (ReasonTag.fail, none, ann.entries)
    | .die _ ann => (ReasonTag.die, none, ann.entries)

#guard (Api.replay escape budget poisoned).exit = some (.failure
  ((Cause.interrupt (some Api.root)).annotate (stackAnnotationsOf Api.root) false))
