module
public import Effect4.Library.PubSub.Data
meta import Effect4.Step.Elab.Inputs

/-! Source terms of the six pure steps. There is no runtime PubSub wrapper here. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PubSub
open Effect4.Program.Authoring

def initialStep : TermSrc := Data.initial.term (fun {t} (x : Effect4.Modules.Input [] t) => nomatch x)
def subscribeStep (id cell : TermSrc) : TermSrc := Data.subscribe.term
  (input_sources% (Data.NamedInputs) { cell := cell, id := id })
def tryPublishStep (message cell : TermSrc) : TermSrc := Data.tryPublish.term
  (input_sources% (Data.PublishInputs) { cell := cell, message := message })
def pollStep (id cell : TermSrc) : TermSrc := Data.poll.term
  (input_sources% (Data.NamedInputs) { id := id, cell := cell })
def unsubscribeStep (id cell : TermSrc) : TermSrc := Data.unsubscribe.term
  (input_sources% (Data.NamedInputs) { cell := cell, id := id })
def slideStep (cell : TermSrc) : TermSrc := Data.slide.term
  (input_sources% (Data.CellInputs) { cell := cell })
end Effect4.PubSub
