# Living quantities: numbers as units, flows and one level

Status: research note (history, not authority). 2026-10-13, after the owner's review of VS-2's
value pictures: "we need a sort of visual language to show numbers and quantities and their flow
and change relative to each other"; "number ints like cap message offers should be converted to
some visual language that relates the flow between them ideally emphasizing organic visual
semantics to give feeling of life"; and "much more advanced capabilities being landed on PC to
create the higher order abstractions needed for this".

The sketch `sketch.html` beside this note draws the language on the Queue scene of `cells.html`
(capacity 2, nine steps). Its values are the scene's; its placement is by hand. Nothing in it is
derived yet.

## 1. The language

Four layers, each the image of something the semantics already has.

| Layer | What it draws | The picture | Its source in the semantics |
| --- | --- | --- | --- |
| Units in places | a quantity at one moment | a bounded place is a vessel with one slot for each unit of its bound: a hollow slot is room (promised), a droplet a unit held (kept); an unbounded place is a lane of parked requests (the hollow box) | the cell: a list field is a place, its length the count; a bound is a role |
| Flows along channels | a change in one step | a unit travels along a channel from one place to another; a channel's width is what it carries in the step (da Vinci's rule, `Tools.View.Organic`); idle, it is the finest line | the keyed join of the cell before and after: a unit that leaves one place and enters another is one key moving |
| One level | the run's quantities, relative to each other | on one axis, takers waiting are a deficit below zero, held units fill the vessel up to its brim, offers waiting are pressure above it; the level is the monotone curve through the counts | the journal: one column for each command (row 367, point 10) |
| Totals as channels | where the units went over the run | the run's flows summed; the branches of a split sum to the trunk | conservation: a unit enters by an offer and leaves by a take |

The four numbers of the Queue's cell (capacity, held, offers waiting, takers waiting) become one
picture: how full, how much pressure, how much demand. In the first profile one signed level
decides all three, except while a wake is in flight (step 8 of the scene: a unit held and its
taker woken, not yet gone). The picture shows that exception and does not hide it.

The life is in the form, not in loops. A channel thickens with what it carries and thins to the
finest line when idle; a unit travels on a shallow arc and settles (`Kind.grammar` of a body);
the level rises and falls by a curve that never overshoots, so it invents no quantity. Nothing
loops and nothing pulses (row 354, point 5). Noise in the strokes stays off by default (row 354,
point 9).

## 2. What Effect4 derives, and what a module declares

A module declares only roles, as data, in its own view file (row 367, point 5):
`src/Effect4/Library/Queue/View.lean`.

| Role | The Queue's | Meaning |
| --- | --- | --- |
| a place | `msgs`, `offers`, `takers` | a list field whose length is a count |
| a bound | `msgs` by `cap` | the place is a vessel with `cap` slots |
| an inlet, an outlet | `offers` before `msgs`, `takers` after it | where units wait to enter, and where requests wait for units |
| an identity | `id` of a taker and of an offer | the key a unit keeps from place to place |
| a unit's payload | `rest` of an offer, an element of `msgs` | what a droplet carries and shows |

Everything else is a fold:

1. the marking: the cell value and the roles to places with their units;
2. the flows of a step: the keyed join of two markings, a unit keyed by its identity, or a
   message by the edit that moves it (FIFO: the front leaves, the rest slide);
3. the level and the totals: a fold of the journal's markings.

## 3. The abstractions the package should give

Each is a value with laws, generic in its things, beside S22's `Layout`, `Layers`, `Ease`,
`Timeline` and the monotone curve. The asks list carries them as W16 to W22.

| Ask | Abstraction | Laws that make it trustworthy | Prior art |
| --- | --- | --- | --- |
| W16 | scales: linear with an exact inverse, bands for the beats of a run, ticks | the inverse undoes the scale; bands tile their range | d3-scale |
| W17 | a ribbon: a stroke whose width varies along a curve, as one closed outline, with a collar where it meets a body; a split whose branch widths sum to the trunk | the outline stays in its band; at a split the widths add (conservation); a moved ribbon is the ribbon moved | da Vinci's rule; `Tools.View.Organic` (`stroke`, `collar`) |
| W18 | a flow network laid out: nodes with values, links with widths, on `Layers` | at each node what enters equals what leaves; links do not cross a node | d3-sankey |
| W19 | areas and stacks: an area between two curves, stacked layers, a signed baseline (a deficit below zero), through the monotone curve | at each beat a layer's height is its value on the scale | d3-shape `area`, `stack` |
| W20 | units in a vessel: n units in c slots, the order kept and the room shown; above a threshold, one mark for k units | the count is kept; the front stays at the front | Isotype (Neurath); ATOM, a grammar of unit visualizations (Park, Drucker, Fernandez, Elmqvist, 2018), recalled |
| W21 | a body moved along a path in one beat, and a keyed join in which a key that leaves one place and enters another is one move, not an exit and an enter | the end frame is the target; a reader who prefers reduced motion sees it | d3's `selection.join`; the package's `Plan.ofJoin`, `Motion.later` |
| W22 | a vessel: a rounded hull around a layout's room, with openings where ribbons meet it, as one outline | the hull holds the room; an opening is where a ribbon's collar stands | the capsule of the sketch |

## 4. Order of work

1. The owner judges the sketch and the questions below.
2. The PC seat builds W16 to W22, after K4.
3. Effect4 writes the Queue's roles in `Library/Queue/View.lean`, the marking fold and the join's
   flows, and draws the scene with the package's values (VS-3 becomes the flows of a step).
4. Then Semaphore, Pool and PubSub, each by roles alone: if a module needs a picture of its own,
   the roles are missing a word.

## 5. Questions for the owner

1. Are place, bound, inlet, outlet, identity and payload the right words for every module? A
   Semaphore's permits are units in a vessel, a Pool's items too, and a PubSub has one inlet and
   many outlets.
2. Is the one level the Queue's history view, with the score's lanes beside it, or instead of
   them?
3. Does the organic noise stay off (row 354, point 9), or does a living picture want it on in a
   proved band?

## 6. What this note does not establish

The sketch is by hand: no picture in it is a fold's image, and no layout law holds of it. The
signed level is read from the scene; that it decides the three counts in the first profile is
an observation of the model, not a theorem. Nothing here is a ruling: a ruling is made only when
written into `docs/core/decisions.md`.
