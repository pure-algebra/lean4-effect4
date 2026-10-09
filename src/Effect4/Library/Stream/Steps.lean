module

public import Effect4.Program.Authoring
public import Effect4.Library.Words

@[expose] public section

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- **The step at the end**: the cursor keeps its accumulator and takes the leftover. -/
def endStep (acc leftover : TermSrc) : TermSrc := app "pair" [acc, app "some" [leftover]]

/-- **The step at a chunk**: the cursor takes the next accumulator and stays open. -/
def chunkStep (next : TermSrc) : TermSrc := app "pair" [next, noneT]

end Effect4.Stream
