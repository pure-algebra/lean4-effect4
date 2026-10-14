import Tools.View.GraphContact
import Tools.View.GraphCheck

open Tools.View

private def fixture : Laid :=
  { placed := #[⟨"source→part", 24, 40, 0, none, 1000⟩,
      ⟨"target/fork/→part", 24, 120, 48, some ⟨"target/fork/→part", "", "", false⟩, 1000⟩],
    marks := #[.bar "plain mark" 24 48 40],
    attachments := #[⟨"source→part", "plain mark"⟩],
    routes := #[.down "arbitrary identity" ["source→part", "target/fork/→part"]],
    width := 120, height := 200 }

private def refusal (l : Laid) (site : GraphCheck.Site) (index : Nat)
    (field : GraphCheck.Field) (reason : GraphCheck.Reason) : Bool :=
  match GraphCheck.laid l with
  | .error r => r == ⟨site, index, field, reason⟩
  | .ok _ => false

#guard (GraphCheck.laid fixture).isOk
#guard refusal { fixture with attachments := #[⟨"missing", "plain mark"⟩] }
  .attachment 0 .source (.unresolvedKey "missing")
#guard refusal { fixture with attachments := #[⟨"source→part", "missing"⟩] }
  .attachment 0 .target (.unresolvedKey "missing")
#guard refusal { fixture with attachments := #[⟨"target/fork/→part", "plain mark"⟩] }
  .attachment 0 .source .notPoint
#guard refusal { fixture with marks := #[.bar "plain mark" 0 8 40] }
  .attachment 0 .target .offMark
#guard refusal { fixture with attachments := fixture.attachments ++ fixture.attachments }
  .attachment 1 .key .duplicateKey
#guard refusal { fixture with marks := fixture.marks ++ fixture.marks }
  .mark 1 .key .duplicateKey
#guard let cs := GraphContact.collect {} fixture
  cs.length == 2 && cs[0]?.any (fun c => decide (c.surface = .bar "plain mark") && c.item == "source→part") &&
    cs[1]?.any (fun c => decide (c.surface = .node) && c.item == "target/fork/→part" && c.docked)
#guard let cs := GraphContact.collect {} { fixture with routes := #[.down "arbitrary identity" ["source→part", "target/fork/→part"] 500] }
  cs[1]?.any fun c => !c.docked && c.point.2 < 120
#guard (GraphContact.collect {} { fixture with routes := #[.down "hidden" ["source→part", "target/fork/→part"] 0] }).isEmpty

-- Both sides of one mark share its incidence role, independently of endpoint spelling.
private def forkTopology : Laid :=
  { fixture with routes := #[
      .down "in" ["target/fork/→part", "source→part"],
      .down "out one" ["source→part", "target/fork/→part"],
      .down "out two" ["source→part", "target/fork/→part"]] }
#guard (GraphContact.degrees forkTopology (GraphAttachment.Index.of forkTopology)).get? "plain mark" == some (1, 2)
#guard GraphContact.junction 1 2 == .fork
#guard GraphContact.junction 2 1 == .join
#guard GraphContact.junction 2 2 == .mixed
#guard GraphContact.junction 1 1 == .through

