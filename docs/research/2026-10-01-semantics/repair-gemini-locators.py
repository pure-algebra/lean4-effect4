#!/usr/bin/env python3
"""Repair the Gemini drafts' declaration names and line locators against the current tree
(coordinator, 2026-10-01). The names follow the registry, which the producer checks; every line
number is recomputed from the declaration's position in the cited file, so a merge that moves a
declaration moves its locators. Run from the repository root; then run check-gemini-drafts.py."""
import pathlib, re, subprocess

G = 'docs/research/2026-10-01-semantics/gemini/'
FILES = ['semantics-v1.md', 'receipt-documentation.md', 'implementation-inventory.md']
# Names the drafts invented, mapped to the declarations the registry cites (reading, 2026-10-01).
RENAME = [
    ('Effect4.Program.Typed.M6bLoopStep.stepLoopPreserves', 'Effect4.Program.Typed.M6Ledger.step_loop'),
    ('Effect4.Program.Typed.M6cDeliverStep.stepDeliverPreserves', 'Effect4.Program.Typed.M6Ledger.step_deliver'),
    ('`stepLoopPreserves`', '`M6Ledger.step_loop`'), ('`stepDeliverPreserves`', '`M6Ledger.step_deliver`'),
    ('Effect4.Program.Typed.fits_of_subN', 'Effect4.Program.Typed.fits_subN'), ('`fits_of_subN`', '`fits_subN`'),
    ('Effect4.Machine.DriveState.lift', 'Effect4.Machine.Lift.driveState_lift'),
    ('[`lift`](file:///src/Effect4/Laws/Machine/Lift.lean', '[`driveState_lift`](file:///src/Effect4/Laws/Machine/Lift.lean'),
    ('Effect4.Program.Typed.sub_antisymm_on_canonical', 'Effect4.Program.Ty.sub_antisymm_canonical'),
    ('`sub_antisymm_on_canonical`', '`sub_antisymm_canonical`'),
    ('Effect4.Api.HostSession.Step.allowsAnswer_inv', 'Effect4.Run.allows_answer'),
    ('Effect4.Api.Frontier.awaitHost_inv', 'Effect4.Api.observe_awaitingAsync_iff'),
    ('`frontier_awaitHost`', '`observe_awaitingAsync_iff`'),
    ('[`decode_iff`](file:///src/Effect4/Schema/Codec.lean', '[`decode_iff`](file:///src/Effect4/Laws/Schema/Codec.lean'),
    ('[`decode_encode`](file:///src/Effect4/Schema/Codec.lean', '[`decode_encode`](file:///src/Effect4/Laws/Schema/Codec.lean'),
]
DECL = r'^\s*(@\[[^\]]*\]\s*)?(private |protected |noncomputable )*(theorem|def|abbrev|structure|inductive|instance|opaque|class)\s+'

def files_named(path):
    if '/' in path:
        return [path] if pathlib.Path(path).exists() else []
    out = subprocess.run(['bash', '-c', f"find src tools Test -name '{path}'"], capture_output=True, text=True).stdout.split()
    return out

def decl_line(path, leaf, near):
    """The declaration of `leaf` in `path` nearest the stated line, or None."""
    lines = pathlib.Path(path).read_text().split('\n')
    hits = [i + 1 for i, l in enumerate(lines) if re.match(DECL + r'([A-Za-z_.]*\.)?' + re.escape(leaf) + r'\b', l)]
    if not hits and re.match(r'^[A-Z]', leaf):  # a module-level name (a command or file stem) keeps its line
        return None
    return min(hits, key=lambda h: abs(h - near)) if hits else None

link = re.compile(r'(file:///(?:Users/pooks/Dev/lean4-effect4/)?((?:src|Test|tools)/[^#)\s]+\.lean)#L)(\d+)')
plain = re.compile(r'(\(`((?:src|Test|tools)/[^`:]+\.lean|\w+\.lean):)(\d+)(`)')
ident = re.compile(r'`([A-Za-z_][\w.]*)`')
changed = 0
for f in FILES:
    p = pathlib.Path(G + f); text = p.read_text()
    for old, new in RENAME:
        text = text.replace(old, new)
    out = []
    for line in text.split('\n'):
        def fix(m, kind):
            global changed
            path, at = m.group(2), int(m.group(3))
            names = [n for n in ident.findall(line[max(0, m.start() - 160):m.start()]) if not n.endswith('.lean')]
            cands = files_named(path)
            # a cell naming one declaration gets that declaration's exact line
            if len(names) == 1:
                for c in cands:
                    hit = decl_line(c, names[0].split('.')[-1], at)
                    if hit and hit != at:
                        changed += 1
                        return m.group(1) + str(hit) + (m.group(4) if kind == 'plain' else '')
                    if hit == at:
                        return m.group(0)
            # keep the locator when any name of the cell is declared within three lines of it
            for c in cands:
                for n in names:
                    hit = decl_line(c, n.split('.')[-1], at)
                    if hit and abs(hit - at) <= 3:
                        return m.group(0)
            # else move it to the declaration of the cell's last name that the file declares
            for c in cands:
                for n in reversed(names):
                    hit = decl_line(c, n.split('.')[-1], at)
                    if hit:
                        changed += 1
                        return m.group(1) + str(hit) + (m.group(4) if kind == 'plain' else '')
            return m.group(0)
        line = link.sub(lambda m: fix(m, 'link'), line)
        line = plain.sub(lambda m: fix(m, 'plain'), line)
        out.append(line)
    p.write_text('\n'.join(out))
print(f'names renamed per the registry; {changed} line numbers recomputed')
