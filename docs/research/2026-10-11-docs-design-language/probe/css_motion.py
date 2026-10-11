#!/usr/bin/env python3
"""A probe, not a landing: one step of the view's motion as one SVG with CSS keyframes.

The view writes a step as up to 19 sampled SVG pictures (`tools/Drivers/View.lean`, `writeFrames`).
This probe reads only the two frames at rest, joins their elements by `data-key`, and writes the
next frame once, with CSS that plays the step: the D3 join of `Tools.View.Motion`, read on SVG.

- A run of consecutive elements with one key is one object. Objects are joined by
  (key, the object's rank among the objects of that key).
- update: an object whose elements all moved by one vector translates from its old place
  (FLIP), on the look's `move` transition; any other kept object cross-fades.
- enter: a line of the tree writes itself (a clip opening rightward), staggered; in the graph,
  level by level from the top, a route wipes downward and a box expands on the spring.
- exit: an old object fades on the look's `leave` transition.

The timings and easings are the look's custom properties (`--e4-motion-*`, `Tools.View.Tokens`),
read from `tools/view/out/looks/looks.css`. A loop holds each step `HOLD` ms after it plays.

    python3 css_motion.py FRAMES_DIR OLD NEW OUT.svg
"""

import re
import sys
from pathlib import Path

STEP, HOLD = 600, 1800          # the look's step, and the hold before the loop replays it
PERIOD = STEP + HOLD
MOVE = (0, 270, "settle")
LEAVE = (0, 150, "leave")
WRITE = (180, 180, "linear")
STAGGER = 36
ENTER_FROM, DRAW, EXPAND = 180, 132, 216

EASE = {
    "settle": "linear(0, 0.054, 0.171, 0.306, 0.438, 0.555, 0.654, 0.734, 0.799, 0.849, 0.888, 0.918, 0.941, 0.958, 0.97, 0.98, 0.986, 0.992, 0.995, 0.998, 1)",
    "leave": "linear(0, 0, 0.001, 0.003, 0.008, 0.015, 0.027, 0.042, 0.064, 0.091, 0.125, 0.166, 0.216, 0.274, 0.343, 0.421, 0.512, 0.614, 0.729, 0.857, 1)",
    "linear": "linear",
    "out": "linear(0, 0.143, 0.271, 0.386, 0.488, 0.579, 0.657, 0.726, 0.784, 0.834, 0.875, 0.909, 0.936, 0.958, 0.973, 0.985, 0.992, 0.997, 0.999, 1, 1)",
    "spring": "linear(0, 0.059, 0.195, 0.363, 0.531, 0.681, 0.804, 0.898, 0.964, 1.007, 1.032, 1.043, 1.045, 1.041, 1.034, 1.026, 1.019, 1.012, 1.007, 1.003, 1)",
}

KEY = re.compile(r' data-key="([^"]*)"')
NUM = re.compile(r'-?\d+(?:\.\d+)?')


def objects(lines):
    """The frame's lines, with each run of one key grouped: (key or None, [lines], rank)."""
    out, seen = [], {}
    for line in lines:
        m = KEY.search(line)
        key = m.group(1) if m else None
        if key is not None and out and out[-1][0] == key:
            out[-1][1].append(line)
        else:
            rank = seen.get(key, 0)
            if key is not None:
                seen[key] = rank + 1
            out.append((key, [line], rank))
    return out


def coords(line):
    """The geometry numbers of an element: x/y/width/height of a rect or text, a path's data."""
    if "<path" in line:
        d = re.search(r' d="([^"]*)"', line).group(1)
        nums = [float(v) for v in NUM.findall(d)]
        return [(nums[i], nums[i + 1]) for i in range(0, len(nums) - 1, 2)]
    pts = []
    for a, b in (("x", "y"),):
        mx, my = re.search(rf' {a}="([^"]*)"', line), re.search(rf' {b}="([^"]*)"', line)
        if mx and my:
            pts.append((float(mx.group(1)), float(my.group(1))))
    return pts


def strip(line):
    """An element with its geometry removed: equal for two elements that differ by a move."""
    line = re.sub(r' d="[^"]*"', "", line)
    return re.sub(r' (x|y)="[^"]*"', "", line)


def shift(old, new):
    """The one vector that moves every element of `old` onto `new`, if there is one."""
    if len(old) != len(new):
        return None
    vec = None
    for a, b in zip(old, new):
        if strip(a) != strip(b):
            return None
        pa, pb = coords(a), coords(b)
        if len(pa) != len(pb):
            return None
        for (x0, y0), (x1, y1) in zip(pa, pb):
            v = (round(x0 - x1, 3), round(y0 - y1, 3))
            if vec is None:
                vec = v
            elif abs(vec[0] - v[0]) > 0.01 or abs(vec[1] - v[1]) > 0.01:
                return None
    return vec


def box(lines):
    """The bounding box of an object's geometry."""
    pts = [p for line in lines for p in coords(line)]
    xs, ys = [p[0] for p in pts], [p[1] for p in pts]
    return (min(xs), min(ys), max(xs), max(ys)) if pts else (0, 0, 0, 0)


class Keyframes:
    """One `@keyframes` rule per distinct (kind, delay, duration, ease), over the loop's period."""

    def __init__(self, prefix):
        self.rules = {}
        self.prefix = prefix

    def name(self, kind, delay, dur, ease):
        sig = (kind, delay, dur, ease)
        if sig not in self.rules:
            self.rules[sig] = f"{self.prefix}{kind}{len(self.rules)}"
        return self.rules[sig]

    def css(self):
        frames = {
            "move": ("transform: translate(var(--dx), var(--dy))", "transform: none"),
            "fade": ("opacity: 0", "opacity: 1"),
            "gone": ("opacity: 1", "opacity: 0"),
            "write": ("clip-path: inset(0 100% 0 0)", "clip-path: inset(0 0 0 0)"),
            "wipe": ("clip-path: inset(0 0 100% 0)", "clip-path: inset(0 0 0 0)"),
            "grow": ("transform: scale(0)", "transform: scale(1)"),
        }
        out = []
        for (kind, delay, dur, ease), name in self.rules.items():
            a, b = 100 * delay / PERIOD, 100 * (delay + dur) / PERIOD
            start, end = frames[kind]
            if kind == "gone":   # an exit is visible before its step and gone after it
                out.append(f"@keyframes {name} {{ 0%, {a:.3f}% {{ {start}; animation-timing-function: {EASE[ease]}; }}"
                           f" {b:.3f}%, 100% {{ {end}; }} }}")
            else:
                out.append(f"@keyframes {name} {{ 0%, {a:.3f}% {{ {start}; animation-timing-function: {EASE[ease]}; }}"
                           f" {b:.3f}%, 100% {{ {end}; }} }}")
        return "\n".join(out)


def step_svg(old_lines, new_lines, prefix):
    olds = {(k, r): ls for k, ls, r in objects(old_lines) if k is not None}
    news = objects(new_lines)
    new_ids = {(k, r) for k, _, r in news if k is not None}
    kf = Keyframes(prefix)

    # The graph's new objects enter level by level, from the top (Motion.sampleLaid).
    graph_top = min((box(ls)[1] for k, ls, _ in news if k and "<path" in "".join(ls)), default=1e9)
    entering = [(k, ls) for k, ls, r in news if k is not None and (k, r) not in olds]
    levels = sorted({round(box(ls)[3]) for k, ls in entering if box(ls)[1] >= graph_top})
    slot = (STEP - ENTER_FROM) // max(1, len(levels))
    writing = [k for k, ls in entering if box(ls)[1] < graph_top]

    body = []
    for key, lines, rank in news:
        if key is None:
            body.extend(lines)
            continue
        inner = "\n".join(lines)
        old = olds.get((key, rank))
        if old is not None:
            vec = shift(old, lines)
            if vec == (0, 0):
                body.append(inner)
            elif vec is not None:
                n = kf.name("move", *MOVE)
                body.append(f'<g class="o" style="--dx:{vec[0]}px;--dy:{vec[1]}px;animation-name:{n}">\n{inner}\n</g>')
            else:
                n = kf.name("fade", MOVE[0], MOVE[1], "settle")
                body.append(f'<g class="o" style="animation-name:{n}">\n{inner}\n</g>')
            continue
        x0, y0, x1, y1 = box(lines)
        if y0 < graph_top:
            i = writing.index(key)
            n = kf.name("write", WRITE[0] + i * STAGGER, WRITE[1], "linear")
        else:
            start = ENTER_FROM + levels.index(round(y1)) * slot
            if "→" in key:
                n = kf.name("wipe", start, min(DRAW, slot * 45 // 100), "out")
            else:
                n = kf.name("grow", start + slot * 40 // 100, min(EXPAND, slot * 60 // 100), "spring")
        body.append(f'<g class="o" style="animation-name:{n}">\n{inner}\n</g>')

    # The old objects that no new object keeps leave, above the new frame.
    for key, lines, rank in objects(old_lines):
        if key is not None and (key, rank) not in new_ids:
            inner = "\n".join(lines)
            n = kf.name("gone", LEAVE[0], LEAVE[1], "leave")
            body.append(f'<g class="o" style="animation-name:{n}">\n{inner}\n</g>')

    style = (
        ".o { animation-duration: %dms; animation-iteration-count: infinite; animation-fill-mode: both;"
        " transform-box: fill-box; transform-origin: center; }\n%s\n"
        "@media (prefers-reduced-motion: reduce) { .o { animation: none; } }"
    ) % (PERIOD, kf.css())
    return style, body


def main():
    frames, old, new, out = Path(sys.argv[1]), sys.argv[2], sys.argv[3], Path(sys.argv[4])
    old_lines = (frames / f"{old}.svg").read_text().splitlines()
    new_lines = (frames / f"{new}.svg").read_text().splitlines()
    head, tail = new_lines[0], new_lines[-1]
    # The page keeps the larger of the two frames' heights for the whole step (Motion.sampleLaid).
    h_old = int(re.search(r'height="(\d+)"', old_lines[0]).group(1))
    h_new = int(re.search(r'height="(\d+)"', head).group(1))
    w = int(re.search(r'width="(\d+)"', head).group(1))
    h = max(h_old, h_new)
    head = re.sub(r'height="\d+" viewBox="0 0 (\d+) \d+"', f'height="{h}" viewBox="0 0 \\1 {h}"', head)
    # Keyframe names and clip ids are global to a page that inlines several figures: prefix them.
    prefix = f"s{new}-"
    rename = lambda l: re.sub(r'(id="|url\(#)c(\d+)', lambda m: f"{m.group(1)}{prefix}c{m.group(2)}", l)
    old_lines = [re.sub(r'(id="|url\(#)c(\d+)', lambda m: f"{m.group(1)}{prefix}old{m.group(2)}", l) for l in old_lines]
    new_lines = [rename(l) for l in new_lines]
    style, body = step_svg(old_lines[1:-1], new_lines[1:-1], prefix)
    out.write_text("\n".join([head, f"<style>\n{style}\n</style>", *body, tail]) + "\n")
    print(f"{out}: {len(body)} objects, {w}x{h}")


if __name__ == "__main__":
    main()
