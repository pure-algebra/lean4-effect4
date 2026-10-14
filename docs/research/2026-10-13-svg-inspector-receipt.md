# 2026-10-13 seat SVG inspector receipt

**The one thing to know before merging:** The inspector keeps source SVG bytes and path data in its embedded payload.
Browser rendering remains unverified in this seat because browser navigation rejects the `file://` protocol.

## Base and head

Branch: `codex/inspect-svg`.
Base: `e9cf615b5047ac3a4d1be053291434fd757b9b7d`.
Code head: `70c0f5169286bc880a1828ecc6d03198327c2ff1`.
The following receipt commit changes only this receipt.

## Changed files

- `tools/view/inspect_svg.py` adds XML, ID, local reference and path grammar checks.
- `tools/view/inspect_svg.py` writes inspection HTML with full views, endpoint crops, theme panels and browser raster probes.
- `docs/research/2026-10-13-svg-inspector-receipt.md` records commands, evidence and limits.

## Commands and results

Commands run from `C:/Users/kokok/Dev/lean4-effect4-inspect-svg`.

```powershell
python tools/view/inspect_svg.py --self-test
```

Result: `self-test passed: 6 valid paths, 14 refused paths, 5 refused SVG controls`.
The controls include missing path arguments, commas, arc flags, duplicate IDs and broken local references.

```powershell
python -m py_compile tools/view/inspect_svg.py
```

Result: exit zero.

```powershell
python tools/view/inspect_svg.py C:/Users/kokok/.codex/worktrees/pegs-port/lean4-effect4/tools/view/out/language-graphs --out tools/view/out/language-graphs-inspect.html --crop '148 480 24 38' --zoom 20
```

Result: `validated 10 SVG files / 265 paths / 84 IDs / 84 local references`.
The output is `tools/view/out/language-graphs-inspect.html`.

```powershell
python tools/view/inspect_svg.py C:/Users/kokok/.codex/worktrees/pegs-port/lean4-effect4/tools/view/out/language-graphs --compare C:/Users/kokok/.codex/worktrees/pegs-port/lean4-effect4/tools/view/out/language-graphs --out tools/view/out/language-graphs-inspect.html --crop '148 480 24 38' --zoom 20
```

Result: both directories pass the same checks.
This finite probe exercises comparison packaging using the same source directory twice.
The final output uses the single-directory command above.

```powershell
python -c "from pathlib import Path; import re,json,hashlib; p=Path('tools/view/out/language-graphs-inspect.html'); s=p.read_text(encoding='utf-8'); j=json.loads(re.search(r'<script id=\""payload\"" type=\""application/json\"">(.*?)</script>',s,re.S).group(1)); assert all(f['text'].encode()==(Path(g['label'])/f['name']).read_bytes() and f['sha256']==hashlib.sha256((Path(g['label'])/f['name']).read_bytes()).hexdigest() for g in j['sets'] for f in g['frames']); Path('tools/view/out/inspect-ui.js').write_text(s.split('<script>')[1].split('</script>')[0],encoding='utf-8'); print('embedded original SVG byte equality and SHA256 passed')"
node --check tools/view/out/inspect-ui.js
git diff --check
```

Result: embedded original SVG byte equality and SHA256 pass.
The JavaScript parser and whitespace checks exit zero.

## Axiom output

No Lean declaration changed.

## Evidence

Finite probes establish the listed checks on the measured generated files and malformed controls.
The HTML contains the original SVG bytes in JSON.
Each display clones the SVG and changes the viewport, theme attribute and local IDs.
The browser checks that each clone retains every original path `d` value.
Shadow roots isolate each panel's CSS.
The URL records frame, crop, look and zoom for repeated observations.
The browser raster probe reports RGBA and SVG coordinates at pixel centers.
These raster observations are host-only evidence.

## Landed theorems and their placement

None.

## Open obligations

Browser rendering, crop controls and raster probes still need a run in the existing preview workflow.
This checker does not establish CSS grammar, geometric contact, path simplicity or mathematical correctness of generated curves.
Local references cover URL references, fragment hrefs and ARIA ID lists.
The checker does not validate external resources or CSS ID selectors.
Only trusted generated SVG directories belong in the inspector.

## Proposed decisions rows

None.
