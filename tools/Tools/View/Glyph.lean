import Lean
import Effect4

/-!
# Tools.View.Glyph — the one vocabulary of marks, as data, with its check (VS-1, row 367)

The visual language draws each sort by a fold (decisions row 367, point 1). Every fold draws a
constructor by the same mark: a fork is one arrow in the program's picture, the score and a
module's motion (point 6). This module holds that vocabulary once.

* `Shape`: the marks, each with what it draws and its glyph in text (`Shape.glyph`), after the
  design language (`git:4a81cc034:docs/design/design-language.md`, §2, §3, §9) and row 354's
  promise-and-keeping family (hollow promised, filled kept).
* `table`: one `Row` per constructor of each sort the pictures fold: its mark, the variant that
  tells it from a sibling, its spoken word and what it draws.
* `sorts`: the sorts, each with its constructors as the environment declares them (`ctors_of%`), so
  a constructor added to the language is in the list at the next build.
* `check`: Moody's semiotic clarity ("The Physics of Notations", 2009) as four refusals: a
  constructor with no row or with two (deficit), a row with no constructor or a mark no row uses
  (excess), two constructors of one sort drawn alike (overload), and one word drawn by two marks
  (redundancy). The module's build runs it, so the tool does not build with a gap.

A list carrier (`Stmts`, `Effs`) has no row: its picture is the series of its elements. A tag of
another sort (`ReasonTag`) has none either.
-/

namespace Tools.View.Glyph
open Lean

open Elab Term in
/-- **The constructors of an inductive type**, as names, read from the environment where the term
is elaborated. -/
elab "ctors_of% " i:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  let .inductInfo info ← getConstInfo n | throwError "{n} is not an inductive type"
  return toExpr info.ctors

/-- The marks of the visual language; what each draws is `Shape.means`. -/
inductive Shape where
  | box | value | series | parallel | block | alternative | loop | region | bracket | openBracket
  | rail | arrow | blockedArrow | spider | rest | hollowBox | filledBox | hollowDot | filledDot
  | port | probe | call | library | cross | hash | reasons | exitBar | hole | enter | barLine
  | fermata | caesura | panel | cells | slot | tag | atom
  deriving DecidableEq, Repr, Inhabited

/-- What each mark draws. -/
def Shape.means : Shape → String
  | .box => "an operation that runs once: a box with its word"
  | .value => "a value that leaves its box on the success wire"
  | .series => "one part wired into the next: sequence"
  | .parallel => "parts side by side, each its own wire: a merge"
  | .block => "a block of statements, read top to bottom"
  | .alternative => "alternatives side by side, one of them taken: a handler, a branch"
  | .loop => "a wire that returns to an earlier point: a loop"
  | .region => "an enclosure that provides what its inside reads: a layer, a service, a context"
  | .bracket => "the bracket of a scope, [k … k]: closed, its span whole"
  | .openBracket => "the open bracket [ of a scope still open: a close owed"
  | .rail => "the double rail of an uninterruptible span: delivery blocked, never dropped"
  | .arrow => "a directed arrow from a parent's lane to a child's: a fork"
  | .blockedArrow => "the blocked arrow ⊣: an interrupt, Talmy's Antagonist"
  | .spider => "the spider: one completion fused to every waiter"
  | .rest => "a rest: the fiber lets go of its turn"
  | .hollowBox => "the hollow box with its token: a park, a queued task (promised)"
  | .filledBox => "the filled box with the same token: a resume, a run task (kept)"
  | .hollowDot => "the hollow dot: a promise not yet kept, a finalizer registered or a deferred unresolved"
  | .filledDot => "the filled dot: a finalizer run (kept)"
  | .port => "a port of the row protocol: !request then ?answer"
  | .probe => "a read of the machine's own state"
  | .call => "a call of a named definition"
  | .library => "a block of named definitions"
  | .cross => "the reason ×: a typed failure"
  | .hash => "the reason #: a defect"
  | .reasons => "a cause: its reasons in order on one line, × # ⊣"
  | .exitBar => "the final bar ‖: an exit, the reasons after it"
  | .hole => "a hole: the place a frame's result returns to"
  | .enter => "the entry ▶: a fiber enters its loop"
  | .barLine => "the bar line across every staff: a host's decision"
  | .fermata => "the fermata 𝄐: a frontier, held live"
  | .caesura => "the caesura //: a halt on malformed code"
  | .panel => "a record: a system of rows, the names once in a muted column at the left"
  | .cells => "a list or a tuple: a lane read from its front, the elements left to right"
  | .slot => "an option: a low shelf that holds a value or stands empty"
  | .tag => "a handle into the machine's stores: its numeral on a tag"
  | .atom => "a value written as its literal: a number, a string, a truth value"

/-- A mark in text, for a terminal and for words. -/
def Shape.glyph : Shape → String
  | .box => "[ ]" | .value => "─●" | .series => "─▶" | .parallel => "═" | .block => "▤"
  | .alternative => "⑂" | .loop => "↺" | .region => "⌜ ⌟" | .bracket => "[ ]" | .openBracket => "[ ┄"
  | .rail => "═══"
  | .arrow => "──▶" | .blockedArrow => "⊣" | .spider => "◉" | .rest => "┄" | .hollowBox => "□"
  | .filledBox => "■" | .hollowDot => "○" | .filledDot => "●" | .port => "!?" | .probe => "⌕"
  | .call => "⟦ ⟧" | .library => "❏" | .cross => "×" | .hash => "#" | .reasons => "× ⊣"
  | .exitBar => "‖"
  | .hole => "◌" | .enter => "▶" | .barLine => "│" | .fermata => "𝄐" | .caesura => "//"
  | .panel => "{ }" | .cells => "[│]" | .slot => "⊔" | .tag => "#n" | .atom => "1"

/-- **The physical kinds** (the owner's "imagined physics", decisions row 367): how a mark behaves,
so that its motion follows from its kind and is never drawn case by case. After Gemini's review
(`docs/research/2026-10-12-visual-semantics/gemini-review.md`), revised: an operation and a failure
are bodies, and only an interrupt is a force. -/
inductive Kind where
  | body | vessel | container | wire | bond | force | cadence
  deriving DecidableEq, Repr, Inhabited

/-- What each kind is. -/
def Kind.means : Kind → String
  | .body => "a thing with an identity that persists and moves: a value, an operation, a failure on its wire, a handle"
  | .vessel => "a form promised hollow and kept filled: a park, a task, a finalizer, a hole, a deferred, an option"
  | .container => "an enclosure that holds others, and some must close: a scope, a region, a rail, a record, a list"
  | .wire => "a path that carries a value: a sequence, a loop, a branch, a rest"
  | .bond => "a relation between bodies: a fork's arrow, a spider's legs, a port"
  | .force => "an impulse that arrives, is blocked or lands, and is spent: an interrupt"
  | .cadence => "a mark in the reading's time that stands still: a bar line, an exit, a fermata, a caesura"

/-- **A mark's kind.** -/
def Shape.kind : Shape → Kind
  | .value | .box | .call | .cross | .hash | .reasons | .enter | .probe | .tag | .atom => .body
  | .hollowBox | .filledBox | .hollowDot | .filledDot | .hole | .slot => .vessel
  | .block | .region | .bracket | .openBracket | .rail | .library | .panel | .cells => .container
  | .series | .parallel | .loop | .alternative | .rest => .wire
  | .arrow | .spider | .port => .bond
  | .blockedArrow => .force
  | .barLine | .exitBar | .fermata | .caesura => .cadence

/-- The primitives of a motion that CSS states exactly (decisions row 354, point 4), and the still
mark, which moves by none. -/
inductive Primitive where
  | translate | scale | clip | opacity | still
  deriving DecidableEq, Repr, Inhabited

/-- One track of a kind's motion: what moves, by which primitive. -/
structure Track where
  primitive : Primitive
  how : String

/-- **A kind's motion grammar**: how a mark of the kind enters, changes and leaves, one track each,
within one beat (row 367, point 10). Nothing loops and nothing pulses (row 354, point 5). -/
structure Grammar where
  enter : Track
  change : Track
  leave : Track

/-- The motion grammar of each kind. -/
def Kind.grammar : Kind → Grammar
  | .body => ⟨⟨.scale, "grows from its centre"⟩, ⟨.translate, "moves along a shallow arc and settles"⟩,
      ⟨.opacity, "docks in its target and fades"⟩⟩
  | .vessel => ⟨⟨.clip, "its outline is drawn from its start edge"⟩, ⟨.opacity, "its fill comes in: the promise kept"⟩,
      ⟨.opacity, "fades"⟩⟩
  | .container => ⟨⟨.clip, "opens from its leading edge along the reading"⟩, ⟨.scale, "grows about its anchor to hold what enters"⟩,
      ⟨.clip, "closes toward its trailing edge"⟩⟩
  | .wire => ⟨⟨.clip, "is drawn along its direction"⟩, ⟨.still, "carries; nothing moves on it"⟩,
      ⟨.clip, "is taken in along its direction, from its tail"⟩⟩
  | .bond => ⟨⟨.clip, "grows from its source along its direction"⟩, ⟨.opacity, "a leg fills when its end arrives"⟩,
      ⟨.opacity, "fades when the relation ends"⟩⟩
  | .force => ⟨⟨.translate, "travels along its direction to its target"⟩, ⟨.still, "stops at a bar: a rail holds it, or it lands"⟩,
      ⟨.opacity, "fades as its reason is written"⟩⟩
  | .cadence => ⟨⟨.clip, "is drawn from top to bottom"⟩, ⟨.still, "stands"⟩,
      ⟨.opacity, "recedes in tone as the cursor passes"⟩⟩

/-- One constructor's mark: its shape, the variant that tells it from a sibling of the same shape
and word, its spoken word (a verb of the dictionary where there is one), and what it draws. -/
structure Row where
  ctor : Name
  shape : Shape
  variant : String := ""
  word : String
  means : String

/-- A sort the pictures fold: its name and its constructors. -/
structure SortCtors where
  name : String
  ctors : List Name

/-- **The table**: one row per constructor of each sort in `sorts`. -/
def table : List Row := [
  -- the program (`Eff`, `src/Effect4/Program/Eff.lean`)
  ⟨``Effect4.Program.Eff.succeed, .value, "", "succeed", "a value leaves on the success wire"⟩,
  ⟨``Effect4.Program.Eff.fail, .cross, "", "fail", "a typed failure, the reason ×"⟩,
  ⟨``Effect4.Program.Eff.failCause, .cross, "cause", "fail", "a failure with a whole cause"⟩,
  ⟨``Effect4.Program.Eff.sync, .box, "", "run", "a synchronous step"⟩,
  ⟨``Effect4.Program.Eff.suspend, .box, "lazy", "suspend", "a program built when it is reached"⟩,
  ⟨``Effect4.Program.Eff.perform, .port, "", "perform", "a row's request and its answer"⟩,
  ⟨``Effect4.Program.Eff.bind, .series, "", "bind", "the first part's value wired into the rest"⟩,
  ⟨``Effect4.Program.Eff.gen, .block, "", "generate", "a block of statements"⟩,
  ⟨``Effect4.Program.Eff.catchCause, .alternative, "", "catch", "a handler beside the failure wire"⟩,
  ⟨``Effect4.Program.Eff.matchCause, .alternative, "both arms", "match", "one arm per exit, one taken"⟩,
  ⟨``Effect4.Program.Eff.onExit, .hollowDot, "", "on exit", "a program registered to run at the exit"⟩,
  ⟨``Effect4.Program.Eff.exit, .exitBar, "", "exit", "an exit taken as a program"⟩,
  ⟨``Effect4.Program.Eff.uninterruptible, .rail, "", "mask", "the span under the double rail"⟩,
  ⟨``Effect4.Program.Eff.interruptible, .rail, "lifted", "unmask", "a span that interrupts may reach"⟩,
  ⟨``Effect4.Program.Eff.yieldNow, .rest, "", "yield", "the fiber gives up its turn"⟩,
  ⟨``Effect4.Program.Eff.awaitFiber, .spider, "", "await", "a leg of the fiber's exit"⟩,
  ⟨``Effect4.Program.Eff.withFiber, .probe, "fiber", "read", "the current fiber, read"⟩,
  ⟨``Effect4.Program.Eff.scoped, .bracket, "", "scope", "a scope around its inside"⟩,
  ⟨``Effect4.Program.Eff.acquireRelease, .bracket, "acquire and release", "scope", "an acquire, its use, its release at close"⟩,
  ⟨``Effect4.Program.Eff.provideLayer, .region, "layer", "provide", "the services a layer builds, around the inside"⟩,
  ⟨``Effect4.Program.Eff.service, .probe, "service", "read", "a service read from the context"⟩,
  ⟨``Effect4.Program.Eff.provideService, .region, "service", "provide", "one service, around the inside"⟩,
  ⟨``Effect4.Program.Eff.catchIf, .alternative, "if", "catch", "a handler for the failures a test admits"⟩,
  ⟨``Effect4.Program.Eff.select, .alternative, "select", "select", "the arm a tag picks"⟩,
  ⟨``Effect4.Program.Eff.iterate, .loop, "", "iterate", "a body run while its test holds"⟩,
  ⟨``Effect4.Program.Eff.restore, .rail, "restore", "restore", "the interruptibility saved at the mask's entry"⟩,
  ⟨``Effect4.Program.Eff.defs, .library, "", "define", "named definitions, then their body"⟩,
  ⟨``Effect4.Program.Eff.invoke, .call, "", "invoke", "a call of a named definition"⟩,
  ⟨``Effect4.Program.Eff.provideContext, .region, "context", "provide", "a whole context, around the inside"⟩,
  -- statements (`Stmt`)
  ⟨``Effect4.Program.Stmt.bindYield, .series, "yield*", "bind", "a statement's value bound to a name"⟩,
  ⟨``Effect4.Program.Stmt.yieldDiscard, .series, "discard", "bind", "a statement run for its effect"⟩,
  ⟨``Effect4.Program.Stmt.ret, .value, "return", "succeed", "the block's value"⟩,
  ⟨``Effect4.Program.Stmt.ifElse, .alternative, "if", "branch", "two arms, one taken"⟩,
  ⟨``Effect4.Program.Stmt.whileTrue, .loop, "while", "loop", "statements run while a test holds"⟩,
  ⟨``Effect4.Program.Stmt.breakLoop, .loop, "break", "break", "the way out of the loop"⟩,
  -- fiber actions (`ActionTerm`)
  ⟨``Effect4.Program.ActionTerm.fork, .arrow, "", "fork", "a child fiber; the parent continues"⟩,
  ⟨``Effect4.Program.ActionTerm.forkIn, .arrow, "in a scope", "fork", "a child whose life a scope holds"⟩,
  ⟨``Effect4.Program.ActionTerm.forkScoped, .arrow, "scoped", "fork", "a child in the current scope"⟩,
  ⟨``Effect4.Program.ActionTerm.runIn, .bracket, "run in", "scope", "a program run in a given scope"⟩,
  ⟨``Effect4.Program.ActionTerm.interrupt, .blockedArrow, "", "interrupt", "an interrupt sent to a fiber"⟩,
  ⟨``Effect4.Program.ActionTerm.interruptScoped, .blockedArrow, "scoped", "interrupt", "an interrupt to a scope's fibers"⟩,
  ⟨``Effect4.Program.ActionTerm.interruptAll, .blockedArrow, "all", "interrupt", "an interrupt to every fiber given"⟩,
  ⟨``Effect4.Program.ActionTerm.awaitAll, .spider, "all", "await", "one leg per fiber, all exits"⟩,
  ⟨``Effect4.Program.ActionTerm.awaitAllFailFast, .spider, "all, fail fast", "await", "all exits, or the first failure"⟩,
  ⟨``Effect4.Program.ActionTerm.snapshotChildren, .probe, "children", "read", "the fiber's children, read"⟩,
  ⟨``Effect4.Program.ActionTerm.awaitNewChildren, .spider, "new children", "await", "the children forked since a snapshot"⟩,
  ⟨``Effect4.Program.ActionTerm.raceAll, .spider, "race", "race", "the first exit settles; the others take ⊣"⟩,
  ⟨``Effect4.Program.ActionTerm.raceAllFirst, .spider, "race, first", "race", "the first exit of any kind settles"⟩,
  ⟨``Effect4.Program.ActionTerm.getId, .probe, "id", "read", "the fiber's identity, read"⟩,
  ⟨``Effect4.Program.ActionTerm.closeScope, .bracket, "close", "close", "a scope closed with an exit"⟩,
  ⟨``Effect4.Program.ActionTerm.getInterruptible, .probe, "interruptibility", "read", "the fiber's interruptibility, read"⟩,
  ⟨``Effect4.Program.ActionTerm.context, .probe, "context", "read", "the fiber's context, read"⟩,
  -- layers (`LayerTerm`)
  ⟨``Effect4.Program.LayerTerm.succeed, .value, "layer", "succeed", "a layer that holds a built service"⟩,
  ⟨``Effect4.Program.LayerTerm.effect, .box, "layer", "run", "a layer built by a program"⟩,
  ⟨``Effect4.Program.LayerTerm.effectDiscard, .box, "layer, discard", "run", "a program run for its effect when the layer builds"⟩,
  ⟨``Effect4.Program.LayerTerm.provide, .region, "layer", "provide", "a layer's services, around another layer"⟩,
  ⟨``Effect4.Program.LayerTerm.provideMerge, .region, "layer, merge", "provide", "provided and kept beside"⟩,
  ⟨``Effect4.Program.LayerTerm.merge, .parallel, "", "merge", "two layers side by side"⟩,
  ⟨``Effect4.Program.LayerTerm.fresh, .box, "fresh", "build", "a layer built anew, not shared"⟩,
  ⟨``Effect4.Program.LayerTerm.orDie, .hash, "or die", "die", "a layer's failure made a defect"⟩,
  ⟨``Effect4.Program.LayerTerm.ref, .call, "layer", "invoke", "a named layer, shared"⟩,
  ⟨``Effect4.Program.LayerTerm.mergeAll, .parallel, "all", "merge", "many layers side by side"⟩,
  -- causes written in a program (`CauseTerm`)
  ⟨``Effect4.Program.CauseTerm.fail, .cross, "", "fail", "the reason ×"⟩,
  ⟨``Effect4.Program.CauseTerm.die, .hash, "", "die", "the reason #"⟩,
  ⟨``Effect4.Program.CauseTerm.interrupt, .blockedArrow, "", "interrupt", "the reason ⊣"⟩,
  ⟨``Effect4.Program.CauseTerm.both, .reasons, "", "combine", "two causes in order, one line of reasons"⟩,
  -- the machine's runtime code and frames (`Prim`, `src/Effect4/Machine/Frames.lean`)
  ⟨``Effect4.Prim.success, .value, "", "succeed", "a value, compiled"⟩,
  ⟨``Effect4.Prim.failure, .cross, "cause", "fail", "a cause, compiled"⟩,
  ⟨``Effect4.Prim.sync, .box, "", "run", "a synchronous step, compiled"⟩,
  ⟨``Effect4.Prim.suspend, .box, "lazy", "suspend", "a suspended program, compiled"⟩,
  ⟨``Effect4.Prim.withFiber, .probe, "fiber", "read", "the current fiber, read"⟩,
  ⟨``Effect4.Prim.yieldableError, .cross, "yieldable", "fail", "an error yielded as a program"⟩,
  ⟨``Effect4.Prim.iterator, .loop, "iterator", "iterate", "a generator's steps"⟩,
  ⟨``Effect4.Prim.onSuccess, .hole, "success", "continue", "the hole a success returns to"⟩,
  ⟨``Effect4.Prim.onSuccessConst, .hole, "success, constant", "continue", "a hole that ignores the value"⟩,
  ⟨``Effect4.Prim.onFailure, .hole, "failure", "continue", "the hole a failure returns to"⟩,
  ⟨``Effect4.Prim.onSuccessAndFailure, .hole, "both", "continue", "a hole for either exit"⟩,
  ⟨``Effect4.Prim.exitFrame, .hole, "exit", "continue", "the hole that takes the exit itself"⟩,
  ⟨``Effect4.Prim.onExit, .hollowDot, "frame", "on exit", "the frame that runs a program at the exit"⟩,
  ⟨``Effect4.Prim.setInterruptible, .rail, "boundary", "mask", "the frame that restores the saved flag"⟩,
  ⟨``Effect4.Prim.whileLoop, .loop, "while", "loop", "a loop, compiled"⟩,
  ⟨``Effect4.Prim.yieldNowWith, .rest, "", "yield", "a yield, compiled"⟩,
  ⟨``Effect4.Prim.async, .hollowBox, "async", "park", "a park on a host registration"⟩,
  ⟨``Effect4.Prim.asyncFinalizer, .hollowDot, "async", "cancel", "the removal of a registration"⟩,
  -- the frames' events (`FrameEvent`)
  ⟨``Effect4.FrameEvent.popped, .hole, "popped", "pop", "a hole filled: the frame popped"⟩,
  ⟨``Effect4.FrameEvent.ranContAll, .hole, "passed", "pass", "a frame passed on a failure's walk"⟩,
  ⟨``Effect4.FrameEvent.pushed, .hole, "pushed", "push", "a hole opened: the frame pushed"⟩,
  ⟨``Effect4.FrameEvent.ranFinalizer, .filledDot, "frame", "finalize", "a finalizer run from a frame"⟩,
  ⟨``Effect4.FrameEvent.substituted, .hole, "substituted", "substitute", "a frame replaced by its continuation"⟩,
  ⟨``Effect4.FrameEvent.deferred, .blockedArrow, "deferred", "interrupt", "a deferred interrupt delivered"⟩,
  ⟨``Effect4.FrameEvent.yielded, .rest, "yielded", "yield", "the fiber gave up its turn"⟩,
  -- the run's events, the score (`RunEvent`, `src/Effect4/Machine/Fibers.lean`)
  ⟨``Effect4.Machine.RunEvent.forked, .arrow, "event", "fork", "a child's birth"⟩,
  ⟨``Effect4.Machine.RunEvent.started, .enter, "", "enter", "a fiber enters its loop"⟩,
  ⟨``Effect4.Machine.RunEvent.scheduledTask, .hollowBox, "task", "queue", "a task queued on a dispatcher"⟩,
  ⟨``Effect4.Machine.RunEvent.ranTask, .filledBox, "task", "dispatch", "a queued task run"⟩,
  ⟨``Effect4.Machine.RunEvent.yieldInjected, .rest, "injected", "yield", "a yield the machine adds"⟩,
  ⟨``Effect4.Machine.RunEvent.parkedOn, .hollowBox, "", "park", "a park on a token"⟩,
  ⟨``Effect4.Machine.RunEvent.resumedWith, .filledBox, "", "resume", "the resume on the same token"⟩,
  ⟨``Effect4.Machine.RunEvent.interruptRecorded, .blockedArrow, "recorded", "interrupt", "an interrupt recorded on its target"⟩,
  ⟨``Effect4.Machine.RunEvent.interruptDeferred, .blockedArrow, "deferred", "interrupt", "an interrupt held over the rail"⟩,
  ⟨``Effect4.Machine.RunEvent.childrenInterrupted, .blockedArrow, "children", "interrupt", "a fiber's children interrupted"⟩,
  ⟨``Effect4.Machine.RunEvent.observerFired, .spider, "observed", "observe", "an exit reaching one leg"⟩,
  ⟨``Effect4.Machine.RunEvent.frame, .hole, "event", "frame", "a frame event on the fiber"⟩,
  ⟨``Effect4.Machine.RunEvent.finalizerProgram, .filledDot, "program", "finalize", "a finalizer run against an exit"⟩,
  ⟨``Effect4.Machine.RunEvent.scopeLinked, .bracket, "linked", "link", "a fiber linked to a scope as a finalizer"⟩,
  ⟨``Effect4.Machine.RunEvent.scopeClosedOnLink, .bracket, "closed on link", "close", "a link to a scope already closed"⟩,
  ⟨``Effect4.Machine.RunEvent.raceStarted, .spider, "started", "race", "a race begun"⟩,
  ⟨``Effect4.Machine.RunEvent.raceLaunched, .arrow, "race entrant", "fork", "an entrant forked"⟩,
  ⟨``Effect4.Machine.RunEvent.raceSettled, .spider, "settled", "race", "the race's first exit"⟩,
  ⟨``Effect4.Machine.RunEvent.contextSet, .region, "context set", "provide", "a fiber's context replaced"⟩,
  ⟨``Effect4.Machine.RunEvent.callback, .port, "callback", "register", "a callback registered"⟩,
  ⟨``Effect4.Machine.RunEvent.exited, .exitBar, "", "exit", "a fiber's exit, its reasons after it"⟩,
  -- the host's decisions (`RunDecision`): one bar line each, the verb written above
  ⟨``Effect4.Machine.RunDecision.fire, .barLine, "drain", "decide", "the host drains one dispatcher"⟩,
  ⟨``Effect4.Machine.RunDecision.flush, .barLine, "flush", "decide", "the host runs every armed dispatcher"⟩,
  ⟨``Effect4.Machine.RunDecision.evaluate, .barLine, "evaluate", "decide", "the host runs one fiber"⟩,
  ⟨``Effect4.Machine.RunDecision.yieldVerdict, .barLine, "verdict", "decide", "the host decides a yield"⟩,
  ⟨``Effect4.Machine.RunDecision.answerAsync, .barLine, "answer", "decide", "the host answers a park"⟩,
  ⟨``Effect4.Machine.RunDecision.interruptFrom, .barLine, "interrupt", "decide", "the host sends an interrupt"⟩,
  ⟨``Effect4.Machine.RunDecision.installMiddleware, .barLine, "install", "decide", "the host installs middleware"⟩,
  ⟨``Effect4.Machine.RunDecision.advance, .barLine, "advance", "decide", "the host advances the clock"⟩,
  -- observers: the legs of a completion (`Observer`)
  ⟨``Effect4.Machine.Observer.resumeAwait, .spider, "await", "observe", "a waiter resumed by the exit"⟩,
  ⟨``Effect4.Machine.Observer.untrackChild, .spider, "untrack", "observe", "a parent letting go of its child"⟩,
  ⟨``Effect4.Machine.Observer.dropScopeFinalizer, .hollowDot, "drop", "unregister", "a child's finalizer dropped from its scope"⟩,
  ⟨``Effect4.Machine.Observer.countdown, .spider, "countdown", "observe", "one of n exits counted"⟩,
  ⟨``Effect4.Machine.Observer.raceCallback, .spider, "race", "observe", "an entrant's exit reaching the race"⟩,
  ⟨``Effect4.Machine.Observer.callback, .port, "callback", "register", "a callback keyed on an exit"⟩,
  -- reasons, exits and scopes (`Reason`, `Exit`, `ScopeState`)
  ⟨``Effect4.Reason.fail, .cross, "", "fail", "the reason ×"⟩,
  ⟨``Effect4.Reason.die, .hash, "", "die", "the reason #"⟩,
  ⟨``Effect4.Reason.interrupt, .blockedArrow, "", "interrupt", "the reason ⊣ and its interruptor"⟩,
  ⟨``Effect4.Exit.success, .exitBar, "success", "exit", "‖ and the value"⟩,
  ⟨``Effect4.Exit.failure, .exitBar, "failure", "exit", "‖ and the reasons, in order"⟩,
  ⟨``Effect4.ScopeState.empty, .openBracket, "empty", "hold", "a scope with nothing registered yet: its close owed"⟩,
  ⟨``Effect4.ScopeState.openEmpty, .openBracket, "none", "hold", "an open scope, no finalizer"⟩,
  ⟨``Effect4.ScopeState.openInline, .openBracket, "one", "hold", "an open scope, one finalizer"⟩,
  ⟨``Effect4.ScopeState.openMap, .openBracket, "many", "hold", "an open scope, finalizers by key"⟩,
  ⟨``Effect4.ScopeState.closed, .bracket, "closed", "close", "a closed scope, its span whole, its exit kept"⟩,
  -- outcomes, frontiers and halts (`Outcome`, `FrontierReason`, `Stuck`)
  ⟨``Effect4.Api.Outcome.finished, .exitBar, "finished", "finish", "the run's final bar"⟩,
  ⟨``Effect4.Api.Outcome.frontier, .fermata, "", "wait", "the run held live"⟩,
  ⟨``Effect4.Api.Outcome.stuck, .caesura, "", "halt", "a halt, outside every typed state"⟩,
  ⟨``Effect4.Api.FrontierReason.commandFuel, .fermata, "budget", "wait", "a command budget spent"⟩,
  ⟨``Effect4.Api.FrontierReason.compileFuel, .fermata, "compile budget", "wait", "a compile budget spent"⟩,
  ⟨``Effect4.Api.FrontierReason.awaitHost, .fermata, "host", "wait", "a host answer owed"⟩,
  ⟨``Effect4.Api.FrontierReason.awaitTimer, .fermata, "timer", "wait", "a timer owed"⟩,
  ⟨``Effect4.Api.FrontierReason.awaitDecision, .fermata, "decision", "wait", "a decision owed"⟩,
  ⟨``Effect4.Machine.Stuck.unknownFiber, .caesura, "fiber", "halt", "a fiber no store holds"⟩,
  ⟨``Effect4.Machine.Stuck.unknownScope, .caesura, "scope", "halt", "a scope no store holds"⟩,
  ⟨``Effect4.Machine.Stuck.unknownRace, .caesura, "race", "halt", "a race no store holds"⟩,
  -- types: a value drawn by its type (`Ty`, `src/Effect4/Program/Ty.lean`; `Tools.View.Cell`)
  ⟨``Effect4.Program.Ty.never, .atom, "never", "never", "no value: the type has none"⟩,
  ⟨``Effect4.Program.Ty.unit, .atom, "unit", "unit", "the one value ()"⟩,
  ⟨``Effect4.Program.Ty.nat, .atom, "nat", "number", "a natural number, its numeral"⟩,
  ⟨``Effect4.Program.Ty.int, .atom, "int", "number", "an integer, its numeral"⟩,
  ⟨``Effect4.Program.Ty.string, .atom, "string", "string", "a string, quoted"⟩,
  ⟨``Effect4.Program.Ty.bool, .atom, "bool", "truth", "true or false"⟩,
  ⟨``Effect4.Program.Ty.handle, .tag, "named", "handle", "a handle of a named kind, its numeral"⟩,
  ⟨``Effect4.Program.Ty.option, .slot, "", "option", "a cup: the value, or empty"⟩,
  ⟨``Effect4.Program.Ty.list, .cells, "", "list", "a row of cells, the first at the left"⟩,
  ⟨``Effect4.Program.Ty.prod, .cells, "pair", "pair", "two cells side by side"⟩,
  ⟨``Effect4.Program.Ty.except, .alternative, "except", "either", "one of two arms, the one the value takes"⟩,
  ⟨``Effect4.Program.Ty.exitOf, .exitBar, "type", "exit", "an exit: ‖ and its value or its reasons"⟩,
  ⟨``Effect4.Program.Ty.causeOf, .reasons, "type", "cause", "a cause, its reasons in order"⟩,
  ⟨``Effect4.Program.Ty.fiberOf, .tag, "fiber", "handle", "a fiber's handle, its numeral"⟩,
  ⟨``Effect4.Program.Ty.union, .alternative, "union", "either", "one of its arms, the first that reads the value"⟩,
  ⟨``Effect4.Program.Ty.lit, .atom, "literal", "literal", "the one value it names"⟩,
  ⟨``Effect4.Program.Ty.refOf, .tag, "ref", "handle", "a reference cell's handle"⟩,
  ⟨``Effect4.Program.Ty.deferredOf, .hollowDot, "deferred", "promise", "a deferred's handle, hollow while it is owed"⟩,
  ⟨``Effect4.Program.Ty.var, .atom, "variable", "variable", "a type variable: the value drawn raw"⟩,
  ⟨``Effect4.Program.Ty.unknown, .atom, "unknown", "unknown", "an unknown type: the value drawn raw"⟩,
  ⟨``Effect4.Program.Ty.record, .panel, "", "record", "a panel of named fields"⟩,
  ⟨``Effect4.Program.Ty.map, .panel, "map", "map", "a panel of keys and their values"⟩,
  ⟨``Effect4.Program.Ty.tuple, .cells, "tuple", "tuple", "cells side by side, by position"⟩,
  ⟨``Effect4.Program.Ty.app, .call, "type", "apply", "a named type applied: the value drawn raw"⟩,
  ⟨``Effect4.Program.Ty.null, .atom, "null", "null", "the value null"⟩,
  ⟨``Effect4.Program.Ty.undefined, .atom, "undefined", "undefined", "the value undefined"⟩,
  ⟨``Effect4.Program.Ty.number, .atom, "number", "number", "a number, its numeral"⟩,
  ⟨``Effect4.Program.Ty.bytes, .atom, "bytes", "bytes", "bytes, by their count"⟩,
  ⟨``Effect4.Program.Ty.contextOf, .region, "context type", "context", "a context: the value drawn raw"⟩,
  -- values drawn raw, where no type reads them (`Store.Val`, `src/Effect4/Store/Carrier/Val.lean`)
  ⟨``Effect4.Store.Val.unit, .atom, "unit", "unit", "the one value ()"⟩,
  ⟨``Effect4.Store.Val.bool, .atom, "bool", "truth", "true or false"⟩,
  ⟨``Effect4.Store.Val.nat, .atom, "nat", "number", "a natural number"⟩,
  ⟨``Effect4.Store.Val.str, .atom, "string", "string", "a string, quoted"⟩,
  ⟨``Effect4.Store.Val.bytes, .atom, "bytes", "bytes", "bytes, by their count"⟩,
  ⟨``Effect4.Store.Val.list, .cells, "", "list", "a row of cells"⟩,
  ⟨``Effect4.Store.Val.pair, .cells, "pair", "pair", "two cells side by side"⟩,
  ⟨``Effect4.Store.Val.none, .slot, "empty", "option", "an empty cup"⟩,
  ⟨``Effect4.Store.Val.some, .slot, "", "option", "a cup that holds a value"⟩,
  ⟨``Effect4.Store.Val.ctor, .panel, "constructor", "construct", "a constructor's index and its arguments"⟩,
  ⟨``Effect4.Store.Val.ref, .tag, "node", "address", "a reference to a node"⟩,
  ⟨``Effect4.Store.Val.handle, .tag, "", "handle", "a handle into a store, its numeral"⟩,
  ⟨``Effect4.Store.Val.negInt, .atom, "negative", "number", "a negative integer"⟩,
  ⟨``Effect4.Store.Val.float, .atom, "float", "number", "a binary64 number"⟩]

/-- **The sorts the pictures fold**, each with its constructors as the environment declares them. -/
def sorts : List SortCtors := [
  ⟨"program", ctors_of% Effect4.Program.Eff⟩,
  ⟨"statement", ctors_of% Effect4.Program.Stmt⟩,
  ⟨"fiber action", ctors_of% Effect4.Program.ActionTerm⟩,
  ⟨"layer", ctors_of% Effect4.Program.LayerTerm⟩,
  ⟨"cause term", ctors_of% Effect4.Program.CauseTerm⟩,
  ⟨"runtime code and frame", ctors_of% Effect4.Prim⟩,
  ⟨"frame event", ctors_of% Effect4.FrameEvent⟩,
  ⟨"run event", ctors_of% Effect4.Machine.RunEvent⟩,
  ⟨"decision", ctors_of% Effect4.Machine.RunDecision⟩,
  ⟨"observer", ctors_of% Effect4.Machine.Observer⟩,
  ⟨"reason", ctors_of% Effect4.Reason⟩,
  ⟨"exit", ctors_of% Effect4.Exit⟩,
  ⟨"scope state", ctors_of% Effect4.ScopeState⟩,
  ⟨"outcome", ctors_of% Effect4.Api.Outcome⟩,
  ⟨"frontier", ctors_of% Effect4.Api.FrontierReason⟩,
  ⟨"halt", ctors_of% Effect4.Machine.Stuck⟩,
  ⟨"type", ctors_of% Effect4.Program.Ty⟩,
  ⟨"value", ctors_of% Effect4.Store.Val⟩]

/-- The shapes, by their constructors, in order. -/
def shapeNames : List Name := ctors_of% Shape

/-- **Semiotic clarity**, every refusal in words; none for a vocabulary that passes. -/
def check (sorts : List SortCtors) (rows : List Row) (shapes : List Name) : List String :=
  let all := sorts.flatMap (·.ctors)
  let rowsOf (c : Name) := rows.filter (·.ctor == c)
  let deficit := all.filterMap fun c =>
    match (rowsOf c).length with
    | 0 => some s!"deficit: {c} has no mark"
    | 1 => none
    | n => some s!"deficit: {c} has {n} rows"
  let excess := rows.filterMap fun r =>
    if all.contains r.ctor then none else some s!"excess: {r.ctor} is no constructor of a sort drawn"
  let unused := (shapes.zipIdx.filter fun (_, i) => !rows.any (·.shape.ctorIdx == i)).map fun (s, _) =>
    s!"excess: the mark {s} draws nothing"
  let overload := sorts.flatMap fun s =>
    let mine := rows.filter (s.ctors.contains ·.ctor)
    mine.zipIdx.flatMap fun (r, i) => (mine.drop (i + 1)).filterMap fun q =>
      if q.shape == r.shape && q.variant == r.variant && q.word == r.word then
        some s!"overload: {r.ctor} and {q.ctor} are drawn alike ({r.word}, {r.variant})"
      else none
  let words := rows.foldl (fun ws r => if ws.contains r.word then ws else ws ++ [r.word]) []
  let redundancy := words.filterMap fun w =>
    let shapes := (rows.filter (·.word == w)).foldl
      (fun ss r => if ss.contains r.shape then ss else ss ++ [r.shape]) []
    if shapes.length > 1 then some s!"redundancy: \"{w}\" is drawn by {shapes.length} marks" else none
  deficit ++ excess ++ unused ++ overload ++ redundancy

/-- The vocabulary's refusals, at the table and the sorts as they stand. -/
def problems : List String := check sorts table shapeNames

-- the tool builds only with a vocabulary that passes (row 367, point 6)
#guard problems.isEmpty

end Tools.View.Glyph
