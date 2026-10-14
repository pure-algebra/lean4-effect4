#!/usr/bin/env python3
"""Finite curvature diagnostics for emitted organic connector contours.

Decimal coordinates are exact Fractions. For regular cubic endpoints,
v=B' and a=B'' give signed curvature cross(v,a)/|v|^3. The equality test
squares the two numerators and speed denominators, retaining their signs.
Floating point appears only in human-facing magnitudes and angles.

The profile is the existing symmetric paired-side M/C/Z format. Deliberate
transverse caps are excluded. Flat bar/node contacts are reported separately;
they are not a computation of the whole graph's visible filled union.
"""

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
import xml.etree.ElementTree as ET

from check_connectors import (SVG, angle, cross, cubic_contours, endpoint_handle,
                              input_files, keyed_paths, subtract, tangent)
from inspect_svg import validate_svg


def endpoint_derivatives(c, end):
    if end:
        v = tuple(3 * (c[3][i] - c[2][i]) for i in (0, 1))
        a = tuple(6 * (c[3][i] - 2 * c[2][i] + c[1][i]) for i in (0, 1))
    else:
        v = tuple(3 * (c[1][i] - c[0][i]) for i in (0, 1))
        a = tuple(6 * (c[2][i] - 2 * c[1][i] + c[0][i]) for i in (0, 1))
    return v, a


def curvature(c, end):
    v, a = endpoint_derivatives(c, end)
    speed2 = sum(x * x for x in v)
    if speed2 == 0:
        return None
    numerator = cross(v, a)
    return numerator, speed2


def curvature_value(signature):
    return float(signature[0]) / float(signature[1]) ** 1.5


def curvature_agrees(a, b):
    if a is None or b is None:
        return None
    an, av = a
    bn, bv = b
    # Squaring alone would wrongly accept an opposite signed curvature.
    same_sign = (an > 0) == (bn > 0) and (an < 0) == (bn < 0)
    return same_sign and an * an * bv ** 3 == bn * bn * av ** 3


def seam(before, after):
    u, v = endpoint_handle(before, True), endpoint_handle(after, False)
    determinant = cross(u, v)
    dot = sum(x * y for x, y in zip(u, v))
    va, _ = endpoint_derivatives(before, True)
    vb, _ = endpoint_derivatives(after, False)
    ka, kb = curvature(before, True), curvature(after, False)
    fa, fb = (curvature_value(k) if k is not None else None for k in (ka, kb))
    return {
        "point": [float(x) for x in before[3]],
        "exact_point": [str(x) for x in before[3]],
        "contact_agrees": before[3] == after[0],
        "tangent_agrees": determinant == 0 and dot > 0,
        "derivative_agrees": va == vb and va != (0, 0),
        "angle_degrees": angle(tangent(before, True), tangent(after, False)),
        "exact_tangent_cross": str(determinant),
        "exact_tangent_dot": str(dot),
        "incoming_handle_length": math.hypot(*map(float, u)),
        "outgoing_handle_length": math.hypot(*map(float, v)),
        "incoming_curvature": fa,
        "outgoing_curvature": fb,
        "curvature_jump": abs(fa - fb) if fa is not None and fb is not None else None,
        "exact_curvature_agrees": curvature_agrees(ka, kb),
        "regular_curvature": ka is not None and kb is not None,
    }


def inside(point, crop):
    if crop is None:
        return False
    x, y, w, h = crop
    return x <= point[0] <= x + w and y <= point[1] <= y + h


def flat_contact(point, c):
    direction = subtract(c[3], c[0])
    if direction == (0, 0):
        return False
    # Repeated-control encoding is not required for a flat boundary segment.
    if any(cross(subtract(p, c[0]), direction) != 0 for p in c[1:]):
        return False
    delta = subtract(point, c[0])
    dot = sum(a * b for a, b in zip(delta, direction))
    return cross(delta, direction) == 0 and 0 <= dot <= sum(x * x for x in direction)


def other_boundaries(root):
    result = []

    def walk(element, key="", transformed=False):
        key = element.get("data-key", key)
        transformed = transformed or bool(element.get("transform"))
        if element.tag == f"{{{SVG}}}path" and "e4-fill-ink" in element.get("class", "").split() and "→" not in key:
            if transformed:
                raise ValueError("transformed geometry is outside the raw emitted-coordinate profile")
            for contour in cubic_contours(element.get("d", "")):
                result.extend((key, index, c) for index, c in enumerate(contour.cubics))
        for child in element:
            walk(child, key, transformed)

    walk(root)
    return result


def require_raw_geometry(root):
    def walk(element, transformed=False):
        transformed = transformed or bool(element.get("transform"))
        if element.tag == f"{{{SVG}}}path" and transformed:
            raise ValueError("transformed geometry is outside the raw emitted-coordinate profile")
        for child in element:
            walk(child, transformed)
    walk(root)


def mouths(curves, boundaries):
    n = len(curves) // 2 - 1
    candidates = (("source_right", 0, False), ("target_right", n - 1, True),
                  ("target_left", n + 1, False), ("source_left", 2 * n, True))
    result = []
    for name, index, end in candidates:
        c = curves[index]
        point = c[3] if end else c[0]
        direction = endpoint_handle(c, end)
        k = curvature(c, end)
        for key, other_index, other in boundaries:
            if flat_contact(point, other):
                flat_direction = subtract(other[3], other[0])
                result.append({
                    "mouth": name, "segment": index,
                    "point": [float(x) for x in point],
                    "boundary_key": key, "boundary_segment": other_index,
                    "tangent_line_agrees": cross(direction, flat_direction) == 0,
                    "connector_curvature": curvature_value(k) if k is not None else None,
                    "exact_connector_curvature_numerator": str(k[0]) if k is not None else None,
                    "exact_connector_speed_squared": str(k[1]) if k is not None else None,
                    "exact_curvature_agrees_with_flat": k[0] == 0 if k is not None else None,
                    "flat_boundary_curvature": 0.0,
                    "curvature_jump": abs(curvature_value(k)) if k is not None else None,
                    "scope": "exact contact with a supplied flat segment; no filled-union theorem",
                })
    return result


def diagnose(path, crop=None):
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    validate_svg(text, str(path))
    root = ET.fromstring(text)
    require_raw_geometry(root)
    boundaries = other_boundaries(root)
    rows, contacts = [], []
    formats = []
    groups = keyed_paths(root)
    for key, paths in groups.items():
        if len(paths) != 1:
            formats.append({"key": key, "reason": "multiple filled paths"})
            continue
        path_index, data = paths[0]
        contours = cubic_contours(data)
        if len(contours) != 1 or not contours[0].closed:
            formats.append({"key": key, "reason": "not one closed contour"})
            continue
        curves = contours[0].cubics
        if not curves or curves[-1][3] != contours[0].start:
            formats.append({"key": key, "reason": "close hides an additional edge"})
            continue
        if len(curves) < 4 or len(curves) % 2:
            formats.append({"key": key, "reason": "not two equal sides plus caps"})
            continue
        n = len(curves) // 2 - 1
        if any(curves[i][0] != curves[i][1] or curves[i][2] != curves[i][3] for i in (n, 2 * n + 1)):
            formats.append({"key": key, "reason": "wrong transverse-cap encoding"})
            continue
        for i in (*range(n - 1), *range(n + 1, 2 * n)):
            try:
                row = seam(curves[i], curves[i + 1])
            except ValueError as error:
                formats.append({"key": key, "join_after": i, "reason": str(error)})
                continue
            row.update(key=key, path_index=path_index, join_after=i,
                       side="right_forward" if i < n else "left_return",
                       in_crop=inside(row["point"], crop))
            rows.append(row)
        for row in mouths(curves, boundaries):
            row.update(key=key, path_index=path_index, in_crop=inside(row["point"], crop))
            contacts.append(row)
    return {"file": path.as_posix(), "sha256": hashlib.sha256(raw).hexdigest(),
            "connectors": len(groups), "format_issues": formats,
            "seams": rows, "flat_contacts": contacts}


def rank(rows):
    return sorted(rows, key=lambda x: x.get("curvature_jump") or 0, reverse=True)


def at(c, t):
    s = 1 - t
    return tuple(s ** 3 * float(c[0][i]) + 3 * s * s * t * float(c[1][i]) +
                 3 * s * t * t * float(c[2][i]) + t ** 3 * float(c[3][i]) for i in (0, 1))


def velocity(c, t):
    s = 1 - t
    return tuple(3 * (s * s * float(c[1][i] - c[0][i]) +
                      2 * s * t * float(c[2][i] - c[1][i]) +
                      t * t * float(c[3][i] - c[2][i])) for i in (0, 1))


def sampled_shape(curves, steps):
    """Finite polyline crossings and paired-side separation; no topology theorem."""
    n = len(curves) // 2 - 1
    right = curves[:n]
    left = [tuple(reversed(c)) for c in reversed(curves[n + 1:-1])]
    widths, gaps, backwards, speed = [], [], [], []
    for side_name, side in (("right", right), ("left", left)):
        for i, c in enumerate(side):
            chord = subtract(c[3], c[0])
            for j in range(steps + 1):
                t = j / steps
                v = velocity(c, t)
                speed.append(math.hypot(*v))
                if sum(float(a) * b for a, b in zip(chord, v)) < -1e-10:
                    backwards.append({"side": side_name, "segment": i, "t": t, "point": at(c, t)})
    for i, (r, l) in enumerate(zip(right, left)):
        for j in range(steps + 1):
            t = j / steps
            pr, pl = at(r, t), at(l, t)
            delta = subtract(pr, pl)
            v = tuple((a + b) / 2 for a, b in zip(velocity(r, t), velocity(l, t)))
            length = math.hypot(*v)
            widths.append((math.hypot(*delta), i, t, pr, pl))
            if length > 1e-12:
                gaps.append((cross(v, delta) / length, i, t))
    polygon = [at(c, j / steps) for c in curves for j in range(steps)]
    segments = list(zip(polygon, polygon[1:] + polygon[:1]))
    crossings = []
    for i, (a, b) in enumerate(segments):
        for j in range(i + 2, len(segments)):
            if i == 0 and j == len(segments) - 1:
                continue
            c, d = segments[j]
            if max(a[0], b[0]) < min(c[0], d[0]) or max(c[0], d[0]) < min(a[0], b[0]) or \
               max(a[1], b[1]) < min(c[1], d[1]) or max(c[1], d[1]) < min(a[1], b[1]):
                continue
            ab, cd = subtract(b, a), subtract(d, c)
            ac, ad = cross(ab, subtract(c, a)), cross(ab, subtract(d, a))
            ca, cb = cross(cd, subtract(a, c)), cross(cd, subtract(b, c))
            if ac * ad < -1e-20 and ca * cb < -1e-20:
                determinant = cross(ab, cd)
                t = cross(subtract(c, a), cd) / determinant
                crossings.append({"polyline_segments": [i, j],
                                  "point": [a[k] + t * ab[k] for k in (0, 1)]})
    minimum = min(widths)
    return {"scope": "finite uniform-parameter samples; strict polyline crossings and local chord backtracking",
            "samples_per_cubic": steps, "side_cubics": n,
            "min_paired_distance": minimum[0], "min_distance_segment": minimum[1],
            "min_distance_t": minimum[2], "min_distance_points": minimum[3:],
            "min_oriented_normal_gap": min((x[0] for x in gaps), default=None),
            "max_oriented_normal_gap": max((x[0] for x in gaps), default=None),
            "normal_gap_sign_changes": bool(gaps and min(x[0] for x in gaps) < 0 < max(x[0] for x in gaps)),
            "min_sampled_speed": min(speed, default=None),
            "backtracking_samples": len(backwards), "first_backtracking": backwards[:8],
            "proper_polyline_crossings": len(crossings), "first_crossings": crossings[:8]}


def diagnose_shape(path, key, steps):
    matches = keyed_paths(ET.parse(path).getroot()).get(key, [])
    if len(matches) != 1:
        raise ValueError(f"shape key {key} has {len(matches)} paths in {path}")
    contours = cubic_contours(matches[0][1])
    if len(contours) != 1:
        raise ValueError("shape probe requires a single contour")
    return dict(sampled_shape(contours[0].cubics, steps), file=path.as_posix(), key=key)


def self_test():
    p = lambda x, y: (Fraction(x), Fraction(y))
    straight = (p(0, 0), p(1, 0), p(2, 0), p(3, 0))
    continued = (p(3, 0), p(4, 0), p(5, 0), p(6, 0))
    bent = (p(3, 0), p(4, 0), p(5, 1), p(6, 1))
    good = seam(straight, continued)
    red = seam(straight, bent)
    assert good["exact_curvature_agrees"] and good["tangent_agrees"]
    assert red["derivative_agrees"] and red["tangent_agrees"]
    assert not red["exact_curvature_agrees"] and abs(red["curvature_jump"] - 2 / 3) < 1e-12
    assert curvature_agrees((Fraction(2), Fraction(4)), (Fraction(16), Fraction(16)))
    assert not curvature_agrees((Fraction(2), Fraction(4)), (Fraction(-16), Fraction(16)))
    stationary = (p(3, 0), p(3, 0), p(4, 1), p(6, 1))
    assert curvature(stationary, False) is None
    stationary_line = (p(3, 0), p(3, 0), p(5, 0), p(6, 0))
    stationary_seam = seam(straight, stationary_line)
    assert stationary_seam["tangent_agrees"] and not stationary_seam["regular_curvature"]
    assert stationary_seam["exact_curvature_agrees"] is None
    constant = (p(3, 0),) * 4
    try:
        endpoint_handle(constant, False)
        raise AssertionError("constant cubic accepted as having a tangent")
    except ValueError:
        pass
    tangent_red = seam(straight, (p(3, 0), p(4, 1), p(5, 1), p(6, 1)))
    assert not tangent_red["tangent_agrees"]
    assert flat_contact(p(1, 0), straight) and not flat_contact(p(1, 1), straight)
    lip = (p(0, 0), p(1, 0), p(2, 1), p(2, 2))
    closed_body = (lip, continued, (p(6, 0), p(6, 0), p(6, 0), p(6, 0)),
                   continued, lip, (p(2, 2), p(2, 2), p(0, 0), p(0, 0)))
    contact = next(row for row in mouths(closed_body, [("bar", 0, straight)])
                   if row["mouth"] == "source_right")
    assert contact["tangent_line_agrees"] and not contact["exact_curvature_agrees_with_flat"]
    assert abs(contact["curvature_jump"] - 2 / 3) < 1e-12
    return {"result": "pass", "C1_but_curvature_jump_red_control": red,
            "opposite_signed_curvature_control": True,
            "stationary_endpoint_curvature_is_undefined": True,
            "stationary_G1_seam": stationary_seam,
            "constant_cubic_has_no_tangent": True,
            "flat_bar_lip_red_control": contact,
            "tangent_failure_control": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="*", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--crop", nargs=4, type=float, metavar=("X", "Y", "W", "H"))
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument("--max-curvature-jump", type=float,
                        help="optional red-capable cutoff, in reciprocal SVG user units")
    parser.add_argument("--json", type=Path)
    parser.add_argument("--compact", action="store_true", help="retain summaries and ranked findings, omitting every seam")
    parser.add_argument("--shape-key", help="also sample this connector's shape in each input SVG")
    parser.add_argument("--shape-samples", type=int, default=32)
    args = parser.parse_args()
    if not (args.inputs or args.self_test):
        parser.error("provide SVG inputs or --self-test")
    if args.top < 1 or not 2 <= args.shape_samples <= 128 or args.max_curvature_jump is not None and (
            not math.isfinite(args.max_curvature_jump) or args.max_curvature_jump < 0):
        parser.error("top must be positive and curvature cutoff finite and nonnegative")
    try:
        output = {"scope": "finite emitted cubic contours; curvature in reciprocal SVG user units; no whole-graph union proof"}
        if args.self_test:
            output["self_test"] = self_test()
        paths = input_files(args.inputs)
        files = [diagnose(path, args.crop) for path in paths]
        if args.shape_key:
            output["sampled_shapes"] = [diagnose_shape(path, args.shape_key, args.shape_samples) for path in paths]
        seams = [dict(row, file=file["file"]) for file in files for row in file["seams"]]
        contacts = [dict(row, file=file["file"]) for file in files for row in file["flat_contacts"]]
        threshold = args.max_curvature_jump
        threshold_bad = [row for row in seams if threshold is not None and
                         row["curvature_jump"] is not None and row["curvature_jump"] > threshold]
        tangent_bad = [row for row in seams if not row["tangent_agrees"] or not row["contact_agrees"]]
        formats = sum(len(file["format_issues"]) for file in files)
        output.update(files=files, worst_seams=rank(seams)[:args.top],
                      worst_flat_contacts=rank(contacts)[:args.top],
                      crop_seams=rank([row for row in seams if row["in_crop"]]),
                      crop_flat_contacts=rank([row for row in contacts if row["in_crop"]]),
                      summary={"files": len(files), "connectors": sum(f["connectors"] for f in files),
                               "side_seams": len(seams), "exact_tangent_failures": len(tangent_bad),
                               "exact_curvature_failures": sum(row["exact_curvature_agrees"] is False for row in seams),
                               "nonregular_curvature_seams": sum(not row["regular_curvature"] for row in seams),
                               "format_issues": formats, "flat_contacts": len(contacts),
                               "curvature_cutoff": threshold, "cutoff_failures": len(threshold_bad)})
        failed = bool(tangent_bad or formats or threshold_bad or args.inputs and not seams)
        output["summary"]["result"] = "fail" if failed else "pass"
        if args.compact:
            output["files"] = [{"file": f["file"], "sha256": f["sha256"], "connectors": f["connectors"],
                                "side_seams": len(f["seams"]), "format_issues": f["format_issues"],
                                "exact_tangent_failures": sum(not x["tangent_agrees"] for x in f["seams"]),
                                "exact_curvature_failures": sum(x["exact_curvature_agrees"] is False for x in f["seams"]),
                                "max_curvature_jump": max((x["curvature_jump"] or 0 for x in f["seams"]), default=0),
                                "flat_contacts": len(f["flat_contacts"])} for f in files]
    except (ValueError, OSError, ET.ParseError, AssertionError) as error:
        output = {"error": str(error)}
        failed = True
    text = json.dumps(output, ensure_ascii=True, indent=2) + "\n"
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text, encoding="utf-8")
    print(text, end="")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
