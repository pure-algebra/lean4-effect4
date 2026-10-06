"""Independent finite integer mirrors; no Effect/Lean execution or proof.
Clock domain: finite whole nonnegative milliseconds, no sleepers/fibers.
Timer domain: scalar deadlines, distinct identities, no dispatcher/resumption.
Source owners retained in transition/source/main/.
"""
from dataclasses import dataclass, replace
import json, platform

@dataclass(frozen=True)
class Clock:
    millis: int = 0
    wall_ns: int = 0
    mono_ns: int = 0

def set_time(c, value):
    assert value >= 0
    delta = max(0, value - c.millis)
    return Clock(value, value * 1_000_000, c.mono_ns + delta * 1_000_000)

def adjust(c, delta):
    assert delta >= 0
    # TestClock.run snapshots both nanosecond coordinates before advanceTo,
    # then uses adjustmentNanos to assign their exact final adjustment.
    return Clock(c.millis + delta, c.wall_ns + delta * 1_000_000,
                 c.mono_ns + delta * 1_000_000)

@dataclass(frozen=True)
class Timer:
    now: int
    target: int | None
    waits: tuple

def step(t, delta):
    assert delta >= 0
    target = t.target if t.target is not None else t.now + delta
    due = [(deadline, index, key) for index, (key, deadline) in enumerate(t.waits)
           if deadline <= target]
    if due:
        deadline, index, key = min(due)
        return key, Timer(deadline, target, t.waits[:index] + t.waits[index+1:])
    return None, Timer(target, None, t.waits)

results=[]
def check(name, condition, observation):
    assert condition, name
    results.append(dict(name=name, passed=True, observation=observation))

a=adjust(set_time(adjust(Clock(),10),4),3)
b=adjust(Clock(),7)
check('same_wall_different_monotonic', a.millis==b.millis==7 and a.wall_ns==b.wall_ns==7_000_000 and a.mono_ns==13_000_000 and b.mono_ns==7_000_000, {'history_a':a.__dict__,'history_b':b.__dict__})
c=adjust(adjust(Clock(),4),3)
check('positive_forward_adjustment_composes', c==b, c.__dict__)
d=set_time(adjust(Clock(),10),4)
check('backwards_wall_set_preserves_elapsed', d.mono_ns==10_000_000 and d.millis==4, d.__dict__)
check('wall_only_reconstruction_mutant_refused', a.mono_ns != a.millis*1_000_000, {'incorrect_reconstruction':a.millis*1_000_000,'actual_mirror':a.mono_ns})
first_key, first=step(Timer(5,10,(('sleep',8),)),100)
check('active_target_survives_due_fire', first_key=='sleep' and first==Timer(8,10,()), first.__dict__)
second_key, second=step(first,100)
check('active_target_survives_completion', second_key is None and second==Timer(10,None,()), second.__dict__)
third_key, third=step(second,100)
check('new_advance_uses_delta_after_completion', third_key is None and third==Timer(110,None,()), third.__dict__)
_, mistaken_fresh=step(replace(first,target=None),100)
check('dropping_target_resumption_mutant_refused', mistaken_fresh.now==108 and mistaken_fresh!=second, {'proper_existing_phase':second.__dict__,'fresh_phase_mutant':mistaken_fresh.__dict__})
print(json.dumps({'python':platform.python_version(),'kind':'independent finite mirror controls','count':len(results),'results':results,'exclusions':['Effect execution','Lean proof','fractional/nonfinite/negative times','sleep callback effects','full driver suspension','runtime agreement']},indent=2))
