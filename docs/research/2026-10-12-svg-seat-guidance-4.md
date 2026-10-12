# SVG seat, guidance 4: the owner's rulings on Effect4's adoption (2026-10-12, evening)

From the Effect4 coordinator to the SVG seat. The owner ruled in Effect4's session, as decisions
row 360 of lean4-effect4 records. The pre-probe that the rulings answer is
`2026-10-12-pc-svg-alignment-scope.md`, copied beside this note. Take this note as the owner's
direction, as before.

## The rulings that bear on the seat

1. **The motion's mechanism is the kit's.** `Whatwg.Svg.Scene` owns the types, the laws and the
   CSS writer (`Whatwg.Html.Node.SvgMotion`). Effect4's design language owns what each change
   means, and its look owns the numbers. Effect4 deletes its own join, easing reader and
   samplers when its port lands.
2. **One pin move, at S14.** Effect4's typed picture writer landed at S10 (lean4-effect4
   `784068a8e`): 51 pictures agree element by element with the string writer it replaced, and
   the 51 streams are byte-identical. Effect4's pin moves next to the commit of S14.
3. **After S14, the seat builds what Effect4's ports ask for first.** The craft note's modules
   follow when Effect4's view needs one.
4. **The coordinator writes Effect4's port**, on the Mac, from the seat's ports
   `WhatwgTest/Html/SvgKit.lean`, `SvgStroke.lean` and `SvgMotion.lean`. The seat edits no
   Effect4 file.
5. **The PC's Effect4 checkout is current**: `C:\Users\kokok\Dev\lean4-effect4` is at
   `c7504d691`. Since `707b9a01e`, slice D2 set the look's default noise to 0, and the look
   `organic` turns it on. The finding of `branch.html` holds for that look alone.
6. **Two checks at a look's read, on the kit's laws.**
   - The look's `move` transition takes an easing that passes `Easing.bounded`, and every kept
     thing takes that one timing. So `Kept.moment` holds for kept things.
   - The look's noise is at most `Branch.wobbleRoom` for its widths, with a refusal that names
     the field.

## What Effect4 needs from S14

- S14 committed: `Scene.Plan`, `Metrics` and `Scale`. The owner pushes `html/svg`.
- `Plan` closing debt D124: an exit with its own change, a kept line that changes its shape, and
  no track for a thing that stays.
- Optional, from the adoption probe: the definitions that a consumer imports reach Lean alone.
  That means the `aesop` attributes of `Whatwg/Svg/Data/Mask.lean` and
  `Whatwg/Svg/Value/Grammar.lean` move into their law modules.

The ports will name further debts as they land. Each comes to the seat as a note like this one.
