#!/usr/bin/env python3
"""Host-only G2 comparison from emitted connector cubics, not a production renderer.

Adaptation of Yuksel, Continuity-Enhancing Degree Elevation and Splits (2026),
sections 3, 5 and 6. https://doi.org/10.1145/3799902.3811063
Fraction arithmetic checks the construction before SVG decimal serialization.
This probe establishes neither global simplicity nor a Lean integer error bound.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import shutil
import xml.etree.ElementTree as ET

from check_connectors import SVG, cubic_contours, point


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def mul(a, k):
    return tuple(x * k for x in a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def normal(a, h):
    if dot(h, h) == 0:
        raise ValueError("stationary endpoint cannot define a normal")
    return sub(a, mul(h, dot(a, h) / dot(h, h)))


def jet(c, end):
    v = sub(c[3], c[2]) if end else sub(c[1], c[0])
    a = add(sub(c[3], mul(c[2], 2)), c[1]) if end else add(sub(c[2], mul(c[1], 2)), c[0])
    return v, a


def linear(c):
    h = sub(c[3], c[0])
    return dot(h, h) != 0 and all(cross(sub(p, c[0]), h) == 0 for p in c[1:3])


def g2(a, b):
    va, aa = jet(a, True)
    vb, ab = jet(b, False)
    if a[3] != b[0] or cross(va, vb) != 0 or dot(va, vb) <= 0:
        return False
    axis = 0 if vb[0] else 1
    ratio = va[axis] / vb[axis]
    return normal(aa, va) == mul(normal(ab, vb), ratio * ratio)


def split(c, start_second, end_second):
    """Paper equations 40–53, lambda=1/4; normalized durations 1/4,1/2,1/4."""
    b0, b1, b2, b3 = c
    p1 = add(mul(b0, F(3, 4)), mul(b1, F(1, 4)))
    p2 = add(add(mul(b0, F(9, 16)), mul(b1, F(3, 8))), mul(start_second, F(1, 16)))
    r1 = add(add(mul(end_second, F(1, 16)), mul(b2, F(3, 8))), mul(b3, F(9, 16)))
    r2 = add(mul(b2, F(1, 4)), mul(b3, F(3, 4)))
    q0 = add(add(mul(p2, F(17, 12)), mul(p1, F(-1, 2))),
             add(mul(r1, F(1, 4)), mul(r2, F(-1, 6))))
    q3 = add(add(mul(r1, F(17, 12)), mul(r2, F(-1, 2))),
             add(mul(p2, F(1, 4)), mul(p1, F(-1, 6))))
    q1 = sub(mul(q0, 3), mul(p2, 2))
    q2 = sub(mul(q3, 3), mul(r1, 2))
    return [(b0, p1, p2, q0), (q0, q1, q2, q3), (q3, r1, r2, b3)]


def smooth(side):
    starts = [c[2] for c in side]
    ends = [c[1] for c in side]
    for i, (a, b) in enumerate(zip(side, side[1:])):
        va, aa = jet(a, True)
        vb, ab = jet(b, False)
        if a[3] != b[0] or cross(va, vb) != 0 or dot(va, vb) <= 0:
            raise ValueError("input side is not regular G1")
        na, nb = normal(aa, va), normal(ab, vb)
        if linear(a) or linear(b):
            da, db = mul(na, -1), mul(nb, -1)
        else:
            axis = 0 if vb[0] else 1
            alpha2 = (va[axis] / vb[axis]) ** 2
            da = mul(sub(mul(nb, alpha2), na), 1 / (1 + alpha2 ** 2))
            db = mul(da, -alpha2)
        ends[i] = add(a[1], da)
        starts[i + 1] = add(b[2], db)
    # Horizontal lips meet the flat painted node/bar surface with zero curvature.
    if side:
        v, a = jet(side[0], False)
        if v[0] and v[1] == 0:
            starts[0] = sub(starts[0], normal(a, v))
        v, a = jet(side[-1], True)
        if v[0] and v[1] == 0:
            ends[-1] = sub(ends[-1], normal(a, v))
    result = [piece for c, start, end in zip(side, starts, ends) for piece in split(c, start, end)]
    if not all(g2(a, b) for a, b in zip(result, result[1:])):
        raise ValueError("rational G2 construction check failed")
    return result


def number(x):
    return f"{float(x):.12f}".rstrip("0").rstrip(".") or "0"


def serialize(cs):
    pair = lambda p: " ".join(number(v) for v in p)
    return "M " + pair(cs[0][0]) + " " + " ".join("C " + " ".join(pair(p) for p in c[1:]) for c in cs) + " Z"


def displacement(old, new):
    largest = 0.0
    for i, c in enumerate(old):
        for j in range(33):
            t = j / 32
            part = 0 if t < .25 else 1 if t < .75 else 2
            u = t * 4 if part == 0 else (t - .25) * 2 if part == 1 else (t - .75) * 4
            a = point(c, t)
            b = point(new[3 * i + part], u)
            largest = max(largest, float(dot(sub(a, b), sub(a, b))) ** .5)
    return largest


def transform(source, target):
    data = source.read_bytes()
    root = ET.fromstring(data)
    report = {"file": source.name, "sha256": hashlib.sha256(data).hexdigest(),
              "connectors": 0, "rational_g2_joins": 0, "sampled_max_displacement_px": 0.0}

    def walk(el, key=""):
        key = el.get("data-key", key)
        if el.tag == f"{{{SVG}}}path" and "→" in key and "e4-fill-ink" in el.get("class", "").split():
            contours = cubic_contours(el.get("d", ""))
            if len(contours) != 1 or not contours[0].closed:
                raise ValueError("expected one closed connector")
            cs = contours[0].cubics
            n = (len(cs) - 2) // 2
            if len(cs) != 2 * n + 2 or n < 1:
                raise ValueError("not paired sides and two caps")
            a, b = cs[:n], cs[n + 1:-1]
            aa, bb = smooth(a), smooth(b)
            el.set("d", serialize(aa + [cs[n]] + bb + [cs[-1]]))
            report["connectors"] += 1
            report["rational_g2_joins"] += len(aa) + len(bb) - 2
            report["sampled_max_displacement_px"] = max(report["sampled_max_displacement_px"],
                                                        displacement(a, aa), displacement(b, bb))
        for child in el:
            walk(child, key)

    walk(root)
    ET.register_namespace("", SVG)
    target.write_text(ET.tostring(root, encoding="unicode"), encoding="utf-8")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    if args.source.resolve() == args.out.resolve():
        parser.error("study output must differ from source")
    args.out.mkdir(parents=True, exist_ok=True)
    reports = []
    for path in sorted(args.source.rglob("*.svg")):
        dest = args.out / path.relative_to(args.source)
        dest.parent.mkdir(parents=True, exist_ok=True)
        reports.append(transform(path, dest))
    for path in args.source.rglob("look.css"):
        shutil.copy2(path, args.out / path.relative_to(args.source))
    for path in args.source.rglob("motion.json"):
        manifest = json.loads(path.read_text(encoding="utf-8"))
        manifest["title"] += " · G2 study"
        manifest["description"] += " Host-only curvature experiment; decimal SVG approximation; not production geometry."
        (args.out / path.relative_to(args.source)).write_text(json.dumps(manifest), encoding="utf-8")
    result = {"scope": "Exact rational construction, sampled displacement; SVG coordinates rounded to 12 decimals.",
              "source": str(args.source), "files": len(reports),
              "connectors": sum(r["connectors"] for r in reports),
              "rational_g2_joins": sum(r["rational_g2_joins"] for r in reports),
              "sampled_max_displacement_px": max((r["sampled_max_displacement_px"] for r in reports), default=0),
              "reports": reports}
    (args.out / "study.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "reports"}, indent=2))


if __name__ == "__main__":
    main()
