#!/usr/bin/env python3
"""Finite contour checks for generated organic bumpY graph fixtures.

The profile is one filled M C... Z contour per keyed forward connector. The
constructor emits n left-side cubics, an end cap, n reversed right-side cubics,
and a start cap. This checker infers the two caps from that fixed format. It
checks every side junction, including flare necks, without producer metadata.
It checks emitted coordinates, not SVG pixels or arbitrary path topology.

Examples:
  python tools/view/check_connectors.py --self-test
  python tools/view/check_connectors.py tools/view/out/graph-flows-final
  python tools/view/check_connectors.py --kink-fixture BASELINE/009.svg
"""

import argparse
from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import re
import sys
import xml.etree.ElementTree as ET

from inspect_svg import NUMBER, SVG, validate_svg


@dataclass(frozen=True)
class Contour:
    start: tuple
    cubics: tuple
    closed: bool


def cubic_contours(data):
    """Read the emitted absolute M/C/Z profile after the shared syntax check."""
    tokens = re.findall(r"[A-Za-z]|" + NUMBER.pattern, data)
    contours, curves, start, current, closed = [], [], None, None, False
    index, command = 0, None
    while index < len(tokens):
        if tokens[index].isalpha():
            command = tokens[index]
            index += 1
            if command == "Z":
                if start is None or closed:
                    raise ValueError("close without an open contour")
                closed = True
                current = start
                command = None
                continue
            if command not in ("M", "C"):
                raise ValueError("outside emitted absolute M/C/Z profile")
        if command is None:
            raise ValueError("missing command")
        count = 2 if command == "M" else 6
        values = list(map(float, tokens[index:index + count]))
        if len(values) != count or not all(map(math.isfinite, values)):
            raise ValueError("nonfinite or missing coordinate")
        index += count
        if command == "M":
            if start is not None:
                contours.append(Contour(start, tuple(curves), closed))
            start = current = tuple(values)
            curves, closed = [], False
            # Implicit moveto continuations are lines, outside this profile.
            command = None
        else:
            if current is None or closed:
                raise ValueError("cubic without an open contour")
            curve = (current, tuple(values[:2]), tuple(values[2:4]), tuple(values[4:]))
            curves.append(curve)
            current = curve[-1]
    if start is not None:
        contours.append(Contour(start, tuple(curves), closed))
    return tuple(contours)


def subtract(a, b):
    return a[0] - b[0], a[1] - b[1]


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def tangent(curve, end):
    """Use the first nonzero endpoint jet when the first derivative vanishes."""
    origin = curve[3] if end else curve[0]
    candidates = (2, 1, 0) if end else (1, 2, 3)
    for index in candidates:
        direction = subtract(origin, curve[index]) if end else subtract(curve[index], origin)
        if not all(map(math.isfinite, direction)):
            raise ValueError("nonfinite tangent arithmetic")
        length = math.hypot(*direction)
        if not math.isfinite(length):
            raise ValueError("nonfinite tangent length")
        if length > 0:
            return tuple(value / length for value in direction)
    raise ValueError("constant cubic has no tangent")


def angle(a, b):
    # atan2 avoids acos amplification when two emitted directions agree exactly.
    return math.degrees(math.atan2(abs(cross(a, b)), sum(x * y for x, y in zip(a, b))))


def check_contour(contour, degrees=0.0, position_tolerance=1e-6):
    """Check the symmetric two-side format and all its internal side joins."""
    issues, checked = [], 0
    curves = contour.cubics
    if not contour.closed:
        issues.append({"code": "OPEN", "detail": "contour has no close command"})
    if len(curves) < 6 or len(curves) % 2:
        issues.append({"code": "FORMAT", "detail": "expected 2*n+2 cubics with n >= 2"})
        return issues, checked
    n = len(curves) // 2 - 1
    for index in (n, 2 * n + 1):
        cap = curves[index]
        if cap[0] != cap[1] or cap[2] != cap[3]:
            issues.append({"code": "CAP", "segment": index,
                           "detail": "transverse cap must use the emitted straight-cubic encoding"})
    if math.dist(curves[-1][3], contour.start) > position_tolerance:
        issues.append({"code": "POSITION", "segment": len(curves) - 1,
                       "detail": "last cubic does not return to the moveto; Z hides a closing edge"})
    for index in (*range(n - 1), *range(n + 1, 2 * n)):
        before, after = curves[index:index + 2]
        if math.dist(before[3], after[0]) > position_tolerance:
            issues.append({"code": "POSITION", "join_after": index,
                           "detail": "side cubics do not share their endpoint"})
        try:
            mismatch = angle(tangent(before, True), tangent(after, False))
        except ValueError as error:
            issues.append({"code": "TANGENT", "join_after": index, "detail": str(error)})
            continue
        checked += 1
        if mismatch > degrees + 1e-7:
            issues.append({"code": "TANGENT", "join_after": index,
                           "point": before[3], "angle_degrees": mismatch,
                           "detail": "oriented endpoint tangents exceed the requested angle plus 1e-7 degree arithmetic tolerance"})
    return issues, checked


def keyed_paths(root):
    """Keep filled forward-route paths; inherit their existing data-key groups."""
    groups, path_index = {}, 0

    def walk(element, key=""):
        nonlocal path_index
        key = element.get("data-key", key)
        if element.tag == f"{{{SVG}}}path":
            path_index += 1
            classes = element.get("class", "").split()
            if "→" in key and "e4-fill-ink" in classes:
                groups.setdefault(key, []).append((path_index, element.get("d", "")))
        for child in element:
            walk(child, key)

    walk(root)
    return groups


def check_svg(path, degrees=0.0):
    data = path.read_bytes()
    return check_svg_text(data.decode("utf-8"), str(path), degrees, hashlib.sha256(data).hexdigest())


def check_svg_text(text, name="fixture.svg", degrees=0.0, digest=None):
    result = {"file": name, "sha256": digest or hashlib.sha256(text.encode()).hexdigest(),
              "connectors": 0, "side_joins": 0, "issues": []}
    try:
        validate_svg(text, name)
        groups = keyed_paths(ET.fromstring(text))
    except (ValueError, ET.ParseError) as error:
        result["issues"].append({"code": "SVG", "detail": str(error)})
        return result
    result["connectors"] = len(groups)
    for key, paths in groups.items():
        if len(paths) != 1:
            result["issues"].append({"code": "MULTIPLE_PATHS", "key": key,
                                     "paths": [index for index, _ in paths],
                                     "detail": "connector consists of overlapping filled pieces"})
            continue
        index, data = paths[0]
        try:
            contours = cubic_contours(data)
            if len(contours) != 1:
                issues, count = [{"code": "MULTIPLE_SUBPATHS",
                                  "detail": "one path element still contains separate contours"}], 0
            else:
                issues, count = check_contour(contours[0], degrees)
        except ValueError as error:
            issues, count = [{"code": "PROFILE", "detail": str(error)}], 0
        result["side_joins"] += count
        result["issues"].extend({"key": key, "path": index, **issue} for issue in issues)
    return result


# The retained numerical control comes from the emitted 009.svg at 98d32093d.
KINK_BODY = ((93.2, 512.0), (93.305, 511.407), (93.455, 509.501), (93.834, 508.443))
KINK_COLLAR = ((99.2, 512.0), (95.888, 512.0), (93.2, 509.312), (93.2, 506.0))


def point(curve, t):
    s = 1 - t
    return tuple(s ** 3 * curve[0][i] + 3 * s * s * t * curve[1][i] +
                 3 * s * t * t * curve[2][i] + t ** 3 * curve[3][i] for i in range(2))


def derivative(curve, t):
    s = 1 - t
    return tuple(3 * (s * s * (curve[1][i] - curve[0][i]) +
                     2 * s * t * (curve[2][i] - curve[1][i]) +
                     t * t * (curve[3][i] - curve[2][i])) for i in range(2))


def right_at_y(curve, y):
    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = (lo + hi) / 2
        if point(curve, mid)[1] > y:
            lo = mid
        else:
            hi = mid
    return point(curve, (lo + hi) / 2)[0]


def kink_probe(body=KINK_BODY, collar=KINK_COLLAR):
    """Solve the named crossing, then confirm that the exposed side switches."""
    t, u = 0.956, 0.720
    for _ in range(12):
        a, b = point(body, t), point(collar, u)
        da, db = derivative(body, t), derivative(collar, u)
        determinant = cross(da, db)
        if abs(determinant) < 1e-12:
            raise ValueError("singular crossing control")
        delta = subtract(b, a)
        t += cross(delta, db) / determinant
        u += cross(delta, da) / determinant
    a, b = point(body, t), point(collar, u)
    if not (0 < t < 1 and 0 < u < 1) or math.dist(a, b) > 1e-8:
        raise ValueError("crossing control does not converge inside both cubics")
    da, db = derivative(body, t), derivative(collar, u)
    mismatch = angle(tuple(x / math.hypot(*da) for x in da),
                     tuple(x / math.hypot(*db) for x in db))
    switches = [{"y": y, "body_right": right_at_y(body, y),
                 "collar_right": right_at_y(collar, y)} for y in (508.5, 508.7)]
    if not (43 < mismatch < 44 and
            switches[0]["body_right"] > switches[0]["collar_right"] and
            switches[1]["body_right"] < switches[1]["collar_right"]):
        raise ValueError("named silhouette kink control changed")
    return {"point": a, "body_t": t, "collar_t": u,
            "angle_degrees": mismatch, "boundary_switch": switches,
            "crop": [89, 503, 14, 12]}


def check_kink_fixture(path):
    validate_svg(path.read_text(encoding="utf-8"), path.name)
    paths = keyed_paths(ET.parse(path).getroot()).get("[]/fork→[1]", [])
    if [index for index, _ in paths] != [5, 6]:
        raise ValueError("expected retained route body path 5 and collar path 6")
    body = cubic_contours(paths[0][1])[0].cubics
    collar = cubic_contours(paths[1][1])[0].cubics
    if len(body) != 18 or len(collar) != 4 or body[9] != KINK_BODY or collar[2] != KINK_COLLAR:
        raise ValueError("retained emitted cubic signature changed")
    return {"file": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "key": "[]/fork→[1]", "body_path": 5, "collar_path": 6,
            "body_cubic": 9, "collar_cubic": 2, "expected_defect": kink_probe(body[9], collar[2])}


def self_test():
    good = "M0,0C0,1 0,2 0,3C0,4 0,5 0,6C0,6 2,6 2,6C2,5 2,4 2,3C2,2 2,1 2,0C2,0 0,0 0,0Z"
    cases = [
        ("smooth", good, None),
        ("kink", good.replace("C0,4", "C1,4"), "TANGENT"),
        ("reverse tangent", good.replace("C0,4", "C0,2"), "TANGENT"),
        ("zero first handle", good.replace("C0,4", "C0,3"), None),
        ("hidden close edge", good.replace("C2,0 0,0 0,0Z", "C2,0 0,1 0,1Z"), "POSITION"),
        ("curved cap", good.replace("C0,6 2,6 2,6", "C1,7 2,6 2,6"), "CAP"),
        ("missing close", good[:-1], "OPEN"),
        ("odd segment count", good.replace("C0,4 0,5 0,6", ""), "FORMAT"),
    ]
    for name, data, expected in cases:
        issues, count = check_contour(cubic_contours(data)[0])
        if expected is None:
            assert not issues and count == 2, (name, issues)
        else:
            assert expected in [issue["code"] for issue in issues], (name, issues)
    assert len(cubic_contours(good + good)) == 2
    try:
        cubic_contours(good.replace("C0,1", "C1e999,1"))
        raise AssertionError("nonfinite coordinate accepted")
    except ValueError:
        pass
    assert 43 < kink_probe()["angle_degrees"] < 44
    def svg(*paths):
        return f'<svg xmlns="{SVG}" width="40" height="40"><g data-key="a→b">' + \
            ''.join(f'<path class="e4-fill-ink" d="{data}"/>' for data in paths) + '</g></svg>'
    document_cases = [
        ("emitted single contour", svg(good), None),
        ("separate filled pieces", svg(good, good), "MULTIPLE_PATHS"),
        ("cosmetic one path", svg(good + good), "MULTIPLE_SUBPATHS"),
        ("nonfinite emitted coordinate", svg(good.replace("C0,1", "C1e999,1")), "SVG"),
    ]
    for name, text, expected in document_cases:
        result = check_svg_text(text)
        if expected is None:
            assert not result["issues"] and result["side_joins"] == 2, (name, result)
        else:
            assert expected in [issue["code"] for issue in result["issues"]], (name, result)
    return {"self_tests": len(cases) + 3 + len(document_cases), "result": "pass"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="*", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--kink-fixture", type=Path, help="confirm the named retained baseline defect")
    parser.add_argument("--angle-degrees", type=float, default=0.0,
                        help="requested emitted angle tolerance; default 0 plus 1e-7 degree arithmetic tolerance")
    parser.add_argument("--json", type=Path, help="also save the complete diagnostic")
    args = parser.parse_args()
    if not (0 <= args.angle_degrees < 90 and math.isfinite(args.angle_degrees)):
        parser.error("angle tolerance must be finite and between 0 and 90 degrees")
    if not (args.inputs or args.self_test or args.kink_fixture):
        parser.error("provide SVG inputs, --self-test, or --kink-fixture")
    output = {"scope": "finite generated organic bumpY forward connectors; no global topology or pixel claim"}
    failed = False
    try:
        if args.self_test:
            output["tests"] = self_test()
        if args.kink_fixture:
            output["kink_fixture"] = check_kink_fixture(args.kink_fixture)
        files = []
        for source in args.inputs:
            found = sorted(source.glob("*.svg")) if source.is_dir() else [source]
            if not found:
                raise ValueError(f"no SVG files in {source}")
            files.extend(found)
        if files:
            output["files"] = [check_svg(path, args.angle_degrees) for path in files]
            connectors = sum(file["connectors"] for file in output["files"])
            issues = sum(len(file["issues"]) for file in output["files"])
            if connectors == 0:
                output["issues"] = [{"code": "EMPTY", "detail": "inputs contain no organic forward connectors"}]
                issues += 1
            failed = issues > 0
            output["summary"] = {"files": len(files), "connectors": connectors,
                                 "side_joins": sum(file["side_joins"] for file in output["files"]),
                                 "issues": issues, "angle_degrees": args.angle_degrees,
                                 "arithmetic_angle_tolerance": 1e-7,
                                 "result": "fail" if failed else "pass"}
    except (ValueError, OSError, ET.ParseError, AssertionError) as error:
        output["error"] = str(error)
        failed = True
    text = json.dumps(output, ensure_ascii=True, indent=2) + "\n"
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text, encoding="utf-8")
    print(text, end="")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
