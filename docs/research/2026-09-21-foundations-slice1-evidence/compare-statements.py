from pathlib import Path
import re
root = Path(__file__).parent
def read(name):
    chunks = re.split(r"(?=STATEMENT Effect4\.)", (root / name).read_text())
    result = {}
    for chunk in chunks[1:]:
        key, body = chunk.split(" ", 2)[1:]
        result[key] = " ".join(body.split())
    return result
old = read("all-statements-before.log")
new = read("all-statements-after.log")
assert old.keys() == new.keys(), "obligation set changed"
changed = [key for key in old if old[key] != new[key]]
print(f"{len(old)} statements; {len(changed)} changed")
for key in changed:
    print(key)
expected = {"Effect4.Program.Sched.M1Origin." + leaf for leaf in
    ["actionAt_fork", "actionAt_forkIn", "actionAt_not_forkScoped", "actionAt_raceAll",
     "fork_rel", "forkIn_rel", "raceAll_rel"]}
assert set(changed) == expected, "unapproved statement change"
