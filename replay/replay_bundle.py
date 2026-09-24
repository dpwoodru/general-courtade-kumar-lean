#!/usr/bin/env python3
"""CK release kit: layered-shard kernel replay over an extracted BUNDLE_DIR (portable driver).

Semantics are those of Lane I's frozen tools/replay_sharded.py (same shard program tools/ReplayShard.lean, same
checks, same summary.json fields); only the host-specific paths are replaced by arguments.

usage: replay_bundle.py --bundle BUNDLE_DIR --plan PLAN.tsv --out OUTDIR [--workers N] [--only K1,K2,...]
                        [--axioms D1,D2] [--lean-cmd "CMD"] [--sysroot DIR] [--replay-shard FILE]
  BUNDLE_DIR   extracted bundle: BUNDLE_DIR/closure (45,500 modules) and BUNDLE_DIR/packages/<pkg> (8 packages)
  PLAN.tsv     'id<TAB>height<TAB>m1,m2,...' (kit: replay/plan.tsv, 1,225 shards, 45,500 modules)
  --lean-cmd   command that runs Lean 4.33.0 (default 'lean'); may carry a prefix, e.g. a slot limiter
  --sysroot    toolchain prefix (default: output of `<lean-cmd> --print-prefix`); exported as LEAN_SYSROOT so that
               `findSysroot` inside ReplayShard.lean resolves Init/Lean/Std from the pinned toolchain
Runs `<lean-cmd> --run ReplayShard.lean --shard PLAN K [--axioms ...]` for every selected shard with
LEAN_PATH = BUNDLE_DIR/closure : BUNDLE_DIR/packages/{aesop,batteries,importGraph,LeanSearchClient,mathlib,plausible,
proofwidgets,Qq}; then checks that every selected shard printed SHARD_REPLAY_OK, that its MOD lines are exactly its plan
modules, that no module was replayed twice, and collects the axiom lines. Writes OUTDIR/summary.json; the result is
SHARDED_REPLAY_OK only if ALL plan shards were selected and passed (with --only: PARTIAL_OK / PARTIAL_FAIL).
"""
import json, os, re, shlex, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

PKGS = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']
HERE = os.path.dirname(os.path.abspath(__file__))


def arg(flag, default=None):
    return sys.argv[sys.argv.index(flag) + 1] if flag in sys.argv else default


def main():
    bundle = os.path.abspath(arg('--bundle'))
    plan = os.path.abspath(arg('--plan'))
    outdir = os.path.abspath(arg('--out'))
    workers = int(arg('--workers', '1'))
    axioms = arg('--axioms', '')
    lean = shlex.split(arg('--lean-cmd', 'lean'))
    sysroot = arg('--sysroot') or subprocess.run(lean + ['--print-prefix'], capture_output=True, text=True,
                                                   check=True).stdout.strip()
    rs = os.path.abspath(arg('--replay-shard', os.path.join(HERE, 'ReplayShard.lean')))
    only = set(x for x in (arg('--only', '') or '').split(',') if x)
    os.makedirs(outdir, exist_ok=True)
    lp = [os.path.join(bundle, 'closure')] + [os.path.join(bundle, 'packages', p) for p in PKGS]
    for d in lp:
        if not os.path.isdir(d):
            raise SystemExit('missing LEAN_PATH root %s' % d)
    ngck = sum(1 for e in lp if os.path.isdir(os.path.join(e, 'GeneralCK')))
    if ngck != 1:
        raise SystemExit('FATAL: %d GeneralCK providers on the path' % ngck)
    shards = []
    for line in open(plan):
        if line.strip():
            k, h, mods = line.rstrip('\n').split('\t')
            shards.append((int(k), int(h), [m for m in mods.split(',') if m]))
    env = dict(os.environ, LEAN_PATH=':'.join(lp), LEAN_SYSROOT=sysroot,
               PATH=os.path.join(sysroot, 'bin') + ':' + os.environ.get('PATH', ''))
    timer = ['/usr/bin/time', '-f', 'TIME %e %M'] if os.path.exists('/usr/bin/time') else []

    def run(sh):
        k, h, mods = sh
        out = os.path.join(outdir, 'shard_%04d.out' % k)
        if os.path.exists(out) and ('SHARD_REPLAY_OK %d ' % k) in open(out).read():
            return k, 'CACHED_OK'
        cmd = timer + lean + ['--run', rs, '--shard', plan, str(k)] + (['--axioms', axioms] if axioms else [])
        with open(out, 'w') as f:
            r = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env, cwd=outdir)
        ok = r.returncode == 0 and ('SHARD_REPLAY_OK %d ' % k) in open(out).read()
        print('shard %d height %d modules %d rc %d %s' % (k, h, len(mods), r.returncode, 'OK' if ok else 'FAIL'),
              flush=True)
        return k, 'OK' if ok else 'FAIL'

    todo = [s for s in shards if not only or str(s[0]) in only]
    t0 = time.time()
    with ThreadPoolExecutor(workers) as ex:
        list(ex.map(run, todo))
    replayed, dup, fails, axlines, stats = {}, [], [], [], {}
    for k, h, mods in todo:
        out = os.path.join(outdir, 'shard_%04d.out' % k)
        txt = open(out).read() if os.path.exists(out) else ''
        if ('SHARD_REPLAY_OK %d ' % k) not in txt:
            fails.append(k)
            continue
        got = re.findall(r'^MOD (\S+) consts=', txt, re.M)
        if sorted(got) != sorted(mods):
            fails.append(k)
        for m in got:
            if m in replayed:
                dup.append(m)
            replayed[m] = k
        axlines += [l for l in txt.splitlines() if 'depends on axioms' in l]
        mt = re.search(r'TIME ([\d.]+) (\d+)', txt)
        if mt:
            stats[k] = (float(mt.group(1)), int(mt.group(2)))
    sel_mods = [m for _, _, mods in todo for m in mods]
    missing = [m for m in sel_mods if m not in replayed]
    complete = len(todo) == len(shards)
    ok = not fails and not missing and not dup
    summary = {'plan': plan, 'shards': len(shards), 'selected_shards': len(todo), 'failed_shards': fails,
               'plan_modules': sum(len(m) for _, _, m in shards), 'selected_modules': len(sel_mods),
               'replayed_modules': len(replayed), 'missing': missing[:50], 'duplicates': dup[:50], 'axioms': axlines,
               'wall_s': round(time.time() - t0, 1),
               'max_shard_rss_kb': max((v[1] for v in stats.values()), default=None),
               'sum_shard_time_s': round(sum(v[0] for v in stats.values()), 1),
               'per_shard_time_rss': {str(k): v for k, v in sorted(stats.items())},
               'result': ('SHARDED_REPLAY_OK' if ok else 'SHARDED_REPLAY_INCOMPLETE') if complete else
                         ('PARTIAL_OK' if ok else 'PARTIAL_FAIL')}
    json.dump(summary, open(os.path.join(outdir, 'summary.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k not in ('missing', 'per_shard_time_rss')}, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
