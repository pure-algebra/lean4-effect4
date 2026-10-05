#!/usr/bin/env python3
"""Finite mirror of TxModel; no Lean or Effect4 runtime execution.

Only wait-list-only cancellation is an explicitly hypothetical extension.
"""
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
import hashlib
import json
import platform

ROOT = Path(__file__).resolve().parent
SOURCE = Path('/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-05-claude-lead/tx-probes/TxModel.lean')


@dataclass
class Acc:
    store: list
    reads: list
    writes: list


def pure(value):
    return lambda acc: ('ok', value, acc)


def bind(body, cont):
    def run(acc):
        status, value, after = body(acc)
        return cont(value)(after) if status == 'ok' else (status, value, after)
    return run


def get(cell):
    def run(acc):
        out = deepcopy(acc)
        out.reads.insert(0, cell)
        return 'ok', deepcopy(out.store[cell] if cell < len(out.store) else []), out
    return run


def put(cell, values):
    def run(acc):
        out = deepcopy(acc)
        if cell < len(out.store):
            out.store[cell] = deepcopy(values)
        out.reads.insert(0, cell)
        out.writes.insert(0, cell)
        return 'ok', None, out
    return run


def retry(acc):
    return 'retry', None, acc


def or_else(left, right, keep_left_writes=False):
    def run(acc):
        status, value, after = left(acc)
        if status != 'retry':
            return status, value, after
        reset = deepcopy(after if keep_left_writes else acc)
        reset.reads = after.reads[:]
        return right(reset)
    return run


def take(q):
    return bind(get(q), lambda ms: retry if not ms else bind(put(q, ms[1:]), lambda _: pure(ms[0])))


def offer(q, capacity, value):
    return bind(get(q), lambda ms: retry if len(ms) >= capacity else put(q, ms + [value]))


def enlist(t, ident):
    return bind(get(t), lambda ts: put(t, ts + [ident]))


def serve(q, t, ident):
    def with_tickets(ts):
        if not ts or ts[0] != ident:
            return retry
        return bind(get(q), lambda ms: retry if not ms else
                    bind(put(q, ms[1:]), lambda _: bind(put(t, ts[1:]), lambda _: pure(ms[0]))))
    return bind(get(t), with_tickets)


def two(first, second):
    return bind(first, lambda a: bind(second, lambda b: pure([a, b])))


def world(store):
    return {'store': deepcopy(store), 'waiting': [], 'attempts': 0}


def attempt(w, ident, body):
    out = deepcopy(w)
    out['attempts'] += 1
    out['waiting'] = [(i, cells) for i, cells in out['waiting'] if i != ident]
    status, value, acc = body(Acc(deepcopy(out['store']), [], []))
    signals = []
    if status == 'ok':
        signals = [i for i, cells in out['waiting'] if any(c in acc.writes for c in cells)]
        out['store'] = acc.store
        out['waiting'] = [(i, cells) for i, cells in out['waiting'] if i not in signals]
    elif status == 'retry':
        out['waiting'].append((ident, acc.reads))
    return out, {'status': status, 'value': value, 'signals': signals,
                 'reads': acc.reads, 'writes': acc.writes, 'state': deepcopy(out)}


def main():
    source = SOURCE.read_bytes()
    (ROOT/'TxModel.snapshot.lean').write_bytes(source)
    (ROOT/'TxModel.snapshot.out').write_bytes(SOURCE.with_suffix('.out').read_bytes())
    results, checks = {}, []
    def check(label, condition):
        assert condition, label
        checks.append(label)
    def event(trace, label, w, ident, body):
        out, record = attempt(w, ident, body)
        trace.append({'operation': label, **record})
        return out, record

    # Enrollment inside the attempted body rolls back on retry.
    trace=[]; w=world([[], []])
    fair=lambda ident: bind(enlist(1,ident), lambda _: serve(0,1,ident))
    w,r=event(trace,'request 1: enlist then serve',w,1,fair(1))
    check('retry rolls back ticket 1',r['status']=='retry' and w['store'][1]==[])
    w,r=event(trace,'request 2: enlist then serve',w,2,fair(2))
    w,r=event(trace,'offer 10',w,9,offer(0,1,10))
    check('unticketed waiters both signalled',r['signals']==[1,2])
    w,r=event(trace,'request 2 retries first',w,2,fair(2))
    check('later request consumes 10',r['status']=='ok' and r['value']==10)
    results['enrollment_inside_body']=trace

    # Committed per-queue enrollments can create opposite orders.
    trace=[]; w=world([[10],[20],[],[]])
    for ident,cell in [(1,2),(2,3),(1,3),(2,2)]:
        w,r=event(trace,f'enlist request {ident} on ticket cell {cell}',w,ident,enlist(cell,ident))
    before=deepcopy(w['store'])
    p=two(serve(0,2,1),serve(1,3,1))
    q=two(serve(1,3,2),serve(0,2,2))
    w,rp=event(trace,'P serves A then B atomically',w,1,p)
    w,rq=event(trace,'Q serves B then A atomically',w,2,q)
    check('opposite ticket orders force both retries',rp['status']==rq['status']=='retry')
    check('both retries roll back payload and ticket removal',w['store']==before)
    check('the model quiet condition accepts the blocked cycle',all(body(Acc(deepcopy(w['store']),[],[]))[0]=='retry' for body in [p,q]))
    results['fair_composition_ticket_cycle']=trace

    trace=[]; w=world([[10],[20],[],[]])
    for ident in [1,2]:
        w,r=event(trace,f'enlist request {ident} on both queues in one commit',w,ident,
                  bind(enlist(2,ident),lambda _,ident=ident: enlist(3,ident)))
    w,r=event(trace,'P serves both queues atomically',w,1,p)
    check('coordinated ticket order permits atomic composition',r['status']=='ok' and r['value']==[10,20])
    results['coordinated_enrollment_control']=trace

    # Capacity zero: these bodies cannot exchange a message.
    for capacity in [0,1]:
        trace=[]; w=world([[]])
        w,r=event(trace,'take waits',w,1,take(0))
        w,ro=event(trace,f'offer 10 capacity {capacity}',w,2,offer(0,capacity,10))
        w,rt=event(trace,'take retries',w,1,take(0))
        check(f'capacity {capacity} expected offer status',ro['status']==('retry' if capacity==0 else 'ok'))
        check(f'capacity {capacity} expected take status',rt['status']==('retry' if capacity==0 else 'ok'))
        results[f'capacity_{capacity}']=trace

    # orElse must roll back the left branch, retain outer writes, and union reads.
    left=bind(take(0),lambda value: bind(offer(1,1,value),lambda _:pure([value])))
    for wrong in [False,True]:
        choice=bind(put(2,[99]),lambda _:or_else(left,get(0),keep_left_writes=wrong))
        w,r=attempt(world([[5],[8],[]]),1,choice)
        check(f'orElse mutant={wrong} expected answer',r['value']==([] if wrong else [5]))
        if not wrong:
            check('orElse keeps outer write and rolls back left write',w['store']==[[5],[8],[99]] and r['writes']==[2])
            check('orElse retains left read dependencies',set(r['reads'])=={0,1,2})
        results[f'orElse_keep_left_writes_{wrong}']=r
    for cell in [0,1]:
        w,r=attempt(world([[],[]]),1,or_else(take(0),take(1)))
        check(f'both alternatives retry on both cells before write {cell}',set(w['waiting'][0][1])=={0,1})
        w,r=attempt(w,2,offer(cell,1,7))
        check(f'write to alternative {cell} signals request',r['signals']==[1])
        results[f'orElse_dependency_{cell}']=r

    # Hypothetical cleanup that unregisters only the generic retry waiter.
    trace=[]; w=world([[],[]])
    w,r=event(trace,'enlist request 1',w,1,enlist(1,1))
    w,r=event(trace,'request 1 serves empty queue',w,1,serve(0,1,1))
    w['waiting']=[p for p in w['waiting'] if p[0]!=1]
    trace.append({'operation':'HYPOTHETICAL cancellation: remove retry waiter only','state':deepcopy(w)})
    w,r=event(trace,'enlist request 2',w,2,enlist(1,2))
    w,r=event(trace,'request 2 attempts serve',w,2,serve(0,1,2))
    w,ro=event(trace,'offer 10',w,9,offer(0,1,10))
    w,r=event(trace,'request 2 retries',w,2,serve(0,1,2))
    check('waiter-only cancellation leaves ticket obstruction',r['status']=='retry' and w['store']==[[10],[1,2]] and ro['signals']==[])
    remove_ticket=bind(get(1),lambda ts:put(1,[i for i in ts if i!=1]))
    w,r=event(trace,'CONTROL remove cancelled ticket by committed write',w,99,remove_ticket)
    check('ticket cleanup signals the follower',r['signals']==[2])
    w,r=event(trace,'request 2 retries after ticket cleanup',w,2,serve(0,1,2))
    check('ticket cleanup control lets follower consume',r['status']=='ok' and r['value']==10)
    results['cancellation_extension']=trace

    output={'python':platform.python_version(),'source_sha256':hashlib.sha256(source).hexdigest(),
            'source_unchanged_during_run':source==SOURCE.read_bytes(),
            'checks':checks,'checks_passed':len(checks),'results':results,
            'limits':'Finite Python mirror. Cancellation operation is hypothetical and explicitly absent from TxModel. No Lean, runtime, theorem, or production reachability claim.'}
    (ROOT/'results.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:output[k] for k in ['python','checks_passed','source_sha256','source_unchanged_during_run']},sort_keys=True))


if __name__=='__main__':
    main()
