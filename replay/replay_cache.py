#!/usr/bin/env python3
"""Content-keyed cache of layered-shard kernel replays (incremental final replay).

The frozen harness (tools/ReplayShard.lean + tools/replay_sharded.py, see REPLAY.md) is NOT modified; this tool
only decides which shard results of earlier runs can be reused for a new closure, writes a reduced plan in the same
TSV format for the unreplayed rest, and combines both into one verdict.

Merkle key of a module M (target = non-trusted module, trusted = Init/Lean/Std/Lake/Mathlib/Batteries/Aesop/Qq/
ProofWidgets/Plausible/ImportGraph/LeanSearchClient, exactly as in ReplayShard/OleanClosure):
    key(M) = sha256('rc1|' + PKGFP + '|' + M + '|' + token(M.olean) + '|' +
                    ','.join(d + '=' + key(d) for d in sorted(set(direct imports of M))))
    key(trusted T) = sha256('T|' + T + '|' + PKGFP)
token(f) = 'sha:' + sha256(bytes of f), except for files of the campaign's append-only hard-link assembly root, where
token(f) = 'stat:dev:ino:size:mtime_ns' (the same identity drift check A re-verifies every tick).
PKGFP = sha256 over (path, size, mtime_ns) of every .olean/.olean.private/.olean.server file of the toolchain and of
the eight packages. Equal keys => identical import closures (same module names, same bytes).

Reuse rule (sound by weakening): a shard S of an earlier run that printed SHARD_REPLAY_OK with MOD lines for exactly
its modules replayed every m in S against constants of closure(D(S)) plus the modules of S before m, where D(S) is
the set of direct imports of S's modules. If every m in S and every d in D(S) lies in the new closure F (or is a
trusted module of F's graph) with the SAME key as at run time, then all of those constants are in F with the same
bytes, so each m in S is kernel-checked relative to a sub-environment of F. `reduce` reuses exactly such shards.
Keys at run time are established either by keys computed before the run and equal after it (--keys-before), or by
drift evidence (--since): every file of closure(S u D(S)) unchanged since the run started (assembly root: drift baseline
stat key and no ASM_CHANGED in any drift report since; lane roots: drift sha history; packages: mtimes).

usage:
  replay_cache.py graph   --lp LP_FILE_OR_STRING --out G.json ROOT...
  replay_cache.py keys    --graph G.json --out K.json
  replay_cache.py record  --plan PLAN.tsv --shards DIR --graph G.json --keys K.json --by WHO
                          (--keys-before K0.json | --since ISO_UTC --evidence TEXT) [--note TEXT]
  replay_cache.py reduce  --plan PLAN.tsv --graph G.json --keys K.json --out REDUCED.tsv --covered COV.json
  replay_cache.py verdict --plan PLAN.tsv --covered COV.json --reduced REDUCED.tsv --rshards DIR --keys K.json
                          --out VERDICT.json
  replay_cache.py status
"""
import calendar, glob, hashlib, json, os, re, subprocess, sys, time

# Campaign-internal locations. Only the graph / keys / record / record-closure / reduce / status subcommands
# use them; they ran inside the campaign workspace. `verdict`, the only subcommand the release kit calls
# (BUILD/replay_fresh.sh), reads at most CACHE, which does not exist outside the campaign, so no cached
# shard result can be used.
H = os.environ.get('CK_CAMPAIGN_HOME', '/nonexistent/campaign-home')
L = H + '/workspace'
I = L + '/replay-lane'
ASM = L + '/assembly-root'
LEAN_WRAPPER = L + '/bin/lean-wrapper'
TC = H + '/.elan/toolchains/leanprover--lean4---v4.33.0'
TC_BIN = TC + '/bin'
P = H + '/base/packages'
PKGS = [P + '/' + x for x in ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible',
                              'proofwidgets', 'Qq']]
RC = I + '/work/rcache'
CACHE = RC + '/cache.jsonl'
SHACACHE = RC + '/shacache.json'
DRIFT = I + '/work/drift'
WATCHED_EXTRA_ROOTS = ()   # campaign-internal: extra LEAN_PATH roots covered by the drift watch (names omitted)
OLEAN_SUFFIXES = ('.olean', '.olean.private', '.olean.server')


def load_cache_entries():
    """All parsable cache entries; a torn/unparsable line (possible if an external writer bypassed the lock) is
    skipped with a warning, never trusted."""
    out, bad = [], 0
    if os.path.exists(CACHE):
        for line in open(CACHE, errors='replace'):
            if not line.strip():
                continue
            try:
                e = json.loads(line)
            except Exception:
                bad += 1
                continue
            if isinstance(e, dict) and 'id' in e and 'mods' in e:
                out.append(e)
            else:
                bad += 1
    # ids are plan_sha#k; the same shard recorded from two runs (e.g. workstation and cluster copies of one sub-shard) shares
    # it. Disambiguate later duplicates deterministically (file order), so reduce and verdict name the same entry.
    seen = set()
    for e in out:
        if e['id'] in seen:
            e['id'] = '%s@%s' % (e['id'], e.get('out_sha', '')[:12])
        seen.add(e['id'])
    if bad:
        print('WARNING: %d unparsable cache lines skipped' % bad, file=sys.stderr)
    return out


def append_cache(entries):
    """Append entries under an exclusive flock (cache.jsonl.lock), one write per entry."""
    import fcntl
    os.makedirs(RC, exist_ok=True)
    with open(CACHE + '.lock', 'w') as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        with open(CACHE, 'a') as cf:
            for e in entries:
                cf.write(json.dumps(e) + '\n')
            cf.flush()
            os.fsync(cf.fileno())


def now():
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())


def iso_epoch(s):
    return calendar.timegm(time.strptime(s, '%Y-%m-%dT%H:%M:%SZ'))


def arg(flag, default=None):
    return sys.argv[sys.argv.index(flag) + 1] if flag in sys.argv else default


def positional():
    out, skip = [], False
    for a in sys.argv[2:]:
        if skip:
            skip = False
            continue
        if a.startswith('--'):
            skip = True
            continue
        out.append(a)
    return out


def sha256_str(s):
    return hashlib.sha256(s.encode()).hexdigest()


def file_sha(p):
    h = hashlib.sha256()
    fd = os.open(p, os.O_RDONLY)
    try:
        while True:
            b = os.read(fd, 1 << 22)
            if not b:
                break
            h.update(b)
        try:
            os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)  # do not pollute the page cache of a loaded host
        except Exception:
            pass
    finally:
        os.close(fd)
    return h.hexdigest()


def stkey(st):
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns]


def pkg_fingerprint():
    h = hashlib.sha256()
    n, maxm = 0, 0
    for base in [TC + '/lib/lean'] + PKGS:
        for dp, dn, fn in os.walk(base):
            dn.sort()
            for f in sorted(fn):
                if f.endswith(OLEAN_SUFFIXES):
                    p = os.path.join(dp, f)
                    st = os.stat(p)
                    h.update(('%s|%d|%d\n' % (os.path.relpath(p, H), st.st_size, st.st_mtime_ns)).encode())
                    n += 1
                    maxm = max(maxm, st.st_mtime_ns)
    return h.hexdigest(), n, maxm


def load_plan(path):
    shards = []
    for line in open(path):
        if line.strip():
            k, h, mods = line.rstrip('\n').split('\t')
            shards.append((int(k), int(h), [m for m in mods.split(',') if m]))
    return shards


# ---------------------------------------------------------------------------------------------------- graph
def cmd_graph():
    lp = arg('--lp')
    if os.path.exists(lp):
        lp = open(lp).read().strip()
    out = arg('--out')
    roots = positional()
    ngck = sum(1 for e in lp.split(':') if os.path.isdir(os.path.join(e, 'GeneralCK')))
    if ngck != 1:
        raise SystemExit('FATAL: %d GeneralCK providers on the path' % ngck)
    env = dict(os.environ, LEAN_PATH=lp, PATH=TC_BIN + ':' + os.environ.get('PATH', ''))
    src_tsv = arg('--tsv')
    if src_tsv:
        # reuse an OleanClosure TSV produced over the SAME LEAN_PATH (e.g. by make_manifest.py); caller's duty
        import shutil
        shutil.copyfile(src_tsv, out + '.tsv')
    else:
        with open(out + '.tsv', 'w') as f, open(out + '.err', 'w') as e:
            r = subprocess.run([LEAN_WRAPPER, '--prio', 'hi', '--rss', '3000', '--run', I + '/tools/OleanClosure.lean'] +
                               roots, stdout=f, stderr=e, env=env, cwd=I)
        if r.returncode != 0:
            raise SystemExit('OleanClosure rc %d (see %s.err)' % (r.returncode, out))
    g = {}
    for line in open(out + '.tsv'):
        parts = line.rstrip('\n').split('\t')
        if len(parts) != 4:
            continue
        m, p, size, rest = parts
        if rest == 'TRUSTED':
            g[m] = {'path': p, 'trusted': True}
        else:
            g[m] = {'path': p, 'real': os.path.realpath(p), 'trusted': False,
                    'imports': sorted(set(x for x in rest.split(',') if x))}
    missing = sorted({d for e in g.values() if not e['trusted'] for d in e['imports'] if d not in g})
    if missing:
        raise SystemExit('graph not import-closed: %s' % missing[:10])
    json.dump({'lp': lp, 'roots': roots, 'time': now(), 'modules': g}, open(out, 'w'))
    print('graph', out, 'modules', len(g), 'targets', sum(1 for e in g.values() if not e['trusted']))


# ---------------------------------------------------------------------------------------------------- keys
def load_shacache():
    sc = json.load(open(SHACACHE)) if os.path.exists(SHACACHE) else {}
    return sc


def seed_from_drift(sc):
    """Seed content shas from Lane I's drift state (lane roots, sha keyed by [ino,size,mtime_ns]) and from the
    assembly-root manifest (entries that carry a sha, valid while the drift baseline stat key is unchanged)."""
    try:
        st = json.load(open(DRIFT + '/state.json'))
    except Exception:
        return 0
    n = 0
    for p, rec in st.get('files', {}).items():
        try:
            s = os.stat(p)
        except FileNotFoundError:
            continue
        if [s.st_ino, s.st_size, s.st_mtime_ns] == rec['k'] and p not in sc:
            sc[p] = stkey(s) + [rec['sha']]
            n += 1
    base = st.get('asm', {})
    for line in open(ASM + '/ASM_MANIFEST.tsv'):
        if line.startswith('#'):
            continue
        rel, src, real, size, sha, agree = line.rstrip('\n').split('\t')
        if not re.fullmatch(r'[0-9a-f]{64}', sha) or not rel.endswith('.olean'):
            continue
        p = os.path.join(ASM, rel)
        try:
            s = os.stat(p)
        except FileNotFoundError:
            continue
        if base.get(rel) == [s.st_ino, s.st_size, s.st_mtime_ns] and p not in sc:
            sc[p] = stkey(s) + [sha]
            n += 1
    return n


def content_sha(sc, ent, stats):
    """Identity token of the bytes of a target olean (graph entry `ent`). Files reached through the campaign's assembly root
    (classified by their LEAN_PATH location; many are symlinks into a shared historical root): 'stat:dev:ino:size:mtime_ns'
    of the file reached through that path (the assembly root is append-only and drift check A re-verifies exactly this
    stat identity on every tick; hashing its ~70 GB would thrash a swapping host). All other files: 'sha:' +
    content sha256 of the real file (seeded from the drift state, else hashed once and cached by stat key)."""
    if ent['path'].startswith(ASM + '/'):
        stats['stat_token'] += 1
        return 'stat:%d:%d:%d:%d' % tuple(stkey(os.stat(ent['path'])))
    real = ent['real']
    s = os.stat(real)
    k = stkey(s)
    e = sc.get(real)
    if e and e[:4] == k:
        stats['cached'] += 1
        return 'sha:' + e[4]
    h = file_sha(real)
    s2 = os.stat(real)
    if stkey(s2) != k:
        raise SystemExit('file changed while hashing: %s' % real)
    sc[real] = k + [h]
    stats['hashed'] += 1
    stats['hashed_bytes'] += s.st_size
    return 'sha:' + h


def compute_keys(g, sc, pkgfp):
    mods = g['modules']
    keys, shas, stats = {}, {}, {'cached': 0, 'hashed': 0, 'hashed_bytes': 0, 'stat_token': 0}
    for root in sorted(mods):
        if root in keys:
            continue
        stack = [(root, False)]
        while stack:
            m, expanded = stack.pop()
            if m in keys:
                continue
            e = mods[m]
            if e['trusted']:
                keys[m] = sha256_str('T|%s|%s' % (m, pkgfp))
                continue
            if not expanded:
                stack.append((m, True))
                for d in e['imports']:
                    if d not in keys:
                        stack.append((d, False))
                continue
            sha = content_sha(sc, e, stats)
            shas[m] = sha
            keys[m] = sha256_str('rc1|%s|%s|%s|%s' % (pkgfp, m, sha, ','.join('%s=%s' % (d, keys[d])
                                                                               for d in e['imports'])))
    return keys, shas, stats


def cmd_keys():
    g = json.load(open(arg('--graph')))
    out = arg('--out')
    os.makedirs(RC, exist_ok=True)
    sc = load_shacache()
    seeded = seed_from_drift(sc)
    pkgfp, npkg, maxm = pkg_fingerprint()
    t0 = time.time()
    keys, shas, stats = compute_keys(g, sc, pkgfp)
    tmp = SHACACHE + '.tmp'
    json.dump(sc, open(tmp, 'w'))
    os.replace(tmp, SHACACHE)
    json.dump({'graph': os.path.abspath(arg('--graph')), 'time': now(), 'pkgfp': pkgfp, 'pkg_files': npkg,
               'pkg_max_mtime_ns': maxm, 'keys': keys, 'shas': shas, 'stats': stats}, open(out, 'w'))
    print('keys', out, 'modules', len(keys), 'targets', len(shas), 'seeded', seeded, 'stats', stats,
          'pkgfp', pkgfp[:16], 'pkg_files', npkg, 's', round(time.time() - t0, 1))


# ---------------------------------------------------------------------------------------------------- record
def closure_of(g, start):
    mods, seen, stack = g['modules'], set(), list(start)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        e = mods[m]
        if not e['trusted']:
            stack.extend(e['imports'])
    return seen


def drift_evidence_files(g, since_iso):
    """{real: why} for every target file of graph g that Lane I's drift watch cannot certify as unchanged since
    since_iso (empty dict = all certified), plus a global problem string or ''."""
    T = iso_epoch(since_iso)
    st = json.load(open(DRIFT + '/state.json'))
    reports = sorted(glob.glob(DRIFT + '/report_2*.json'))
    rj = [(r, json.load(open(r))) for r in reports]
    init = [d for r, d in rj if d.get('init')]
    base_time = iso_epoch(init[-1]['time']) if init else None
    if base_time is None or base_time > T:
        return {}, 'drift baseline %s later than run start' % (init[-1]['time'] if init else None)
    later = [(r, d) for r, d in rj if iso_epoch(d['time']) >= T]
    if not later:
        return {}, 'no drift report after run start'
    for r, d in later:
        if d['events'].get('ASM_CHANGED'):
            return {}, 'ASM_CHANGED in %s' % r
    # resolution stability: no olean of a closure namespace deleted anywhere since the run start
    spaces = {m.split('.')[0] for m, e in g['modules'].items() if not e['trusted']}
    for r, d in later:
        for x in d['events'].get('DELETED', []):
            p = x.get('path', '')
            rel = p[len(L) + 1:].split('/') if p.startswith(L + '/') else []
            if len(rel) >= 3 and rel[2] in spaces:
                return {}, 'DELETED %s (closure namespace) in %s' % (p, r)
    lp_roots = g['lp'].split(':')
    for e in lp_roots:
        ok = (e == ASM or e.startswith(P + '/') or e.startswith(I + '/final/views/') or
              (e.startswith(L + '/') and (e.endswith('/root') or e.split(L + '/')[1] in
                                          WATCHED_EXTRA_ROOTS)))
        if not ok:
            return {}, 'LEAN_PATH root not covered by the drift watch: %s' % e
    asm_base = st.get('asm', {})
    files = st.get('files', {})
    by_key = {}
    for p, rec in files.items():
        by_key.setdefault(tuple(rec['k']), []).append(rec)

    def certified(rec):
        return (iso_epoch(rec['first_seen']) <= T and
                not any(iso_epoch(h['until']) > T for h in rec.get('history', [])))
    bad = {}
    for m, e in g['modules'].items():
        if e['trusted']:
            continue
        if e['path'].startswith(ASM + '/'):
            s = os.stat(e['path'])
            if asm_base.get(os.path.relpath(e['path'], ASM)) != [s.st_ino, s.st_size, s.st_mtime_ns]:
                bad[e['real']] = 'asm stat key differs from drift baseline'
            continue
        real = e['real']
        s = os.stat(real)
        recs = by_key.get((s.st_ino, s.st_size, s.st_mtime_ns), [])   # every watched path of this very file
        if not recs:
            bad[real] = 'not watched by drift, or changed after the last drift tick'
        elif not any(certified(r) for r in recs):
            bad[real] = 'first seen or changed after run start'
    return bad, ''


def cmd_record():
    plan, sdir = arg('--plan'), arg('--shards')
    g = json.load(open(arg('--graph')))
    K = json.load(open(arg('--keys')))
    keys = K['keys']
    by, note = arg('--by'), arg('--note', '')
    lp_used = arg('--lp-used')
    if lp_used and os.path.exists(lp_used):
        lp_used = open(lp_used).read().strip()
    if lp_used != g['lp']:
        raise SystemExit('the graph must be computed under the LEAN_PATH used by the run (--lp-used)')
    if os.path.abspath(arg('--graph')) != K['graph']:
        raise SystemExit('keys were computed from a different graph')
    k0 = json.load(open(arg('--keys-before')))['keys'] if arg('--keys-before') else None
    since = arg('--since')
    if k0 is None and not since:
        raise SystemExit('need --keys-before or --since')
    bad, glob_problem = {}, ''
    if k0 is None:
        if K['pkg_max_mtime_ns'] >= iso_epoch(since) * 10 ** 9:
            glob_problem = 'package oleans modified after run start'
        else:
            bad, glob_problem = drift_evidence_files(g, since)
        if glob_problem:
            raise SystemExit('no drift evidence: ' + glob_problem)
        print('drift evidence: %d target files, %d not certified' %
              (sum(1 for e in g['modules'].values() if not e['trusted']), len(bad)))
    os.makedirs(RC, exist_ok=True)
    mods = g['modules']
    verified = {}
    if arg('--verified-shas'):
        for line in open(arg('--verified-shas')):
            p = line.split()
            if len(p) >= 2 and re.fullmatch(r'[0-9a-f]{64}', p[1]):
                verified[p[0]] = p[1]
        okv = {m for m, s in verified.items() if K['shas'].get(m) == 'sha:' + s}
        print('verified-shas: %d given, %d equal to the current content sha' % (len(verified), len(okv)))
        verified = okv
    n_ok, n_rec, skipped = 0, 0, []
    existing = set()
    for e in load_cache_entries():
        if e.get('plan_sha'):
            existing.add((e['plan_sha'], e['k'], e['out_sha']))
    plan_sha = file_sha(plan)
    new_entries = []
    only_ids = set()
    for part in (arg('--only-ids', '') or '').split(','):
        if '-' in part:
            lo, hi = part.split('-')
            only_ids.update(range(int(lo), int(hi) + 1))
        elif part.strip():
            only_ids.add(int(part))
    for k, h, ms in load_plan(plan):
        if only_ids and k not in only_ids:
            continue
        out = os.path.join(sdir, 'shard_%04d.out' % k)
        if not os.path.exists(out):
            skipped.append((k, 'no output'))
            continue
        txt = open(out).read()
        mok = re.search(r'^SHARD_REPLAY_OK %d modules=(\d+) constants=(\d+)' % k, txt, re.M)
        if not mok:
            skipped.append((k, 'no SHARD_REPLAY_OK'))
            continue
        n_ok += 1
        mm = re.findall(r'^MOD (\S+) consts=(\d+)', txt, re.M)
        if sorted(m for m, _ in mm) != sorted(ms) or 'REPLAY_FAIL' in txt or 'SHARD_INVALID' in txt:
            skipped.append((k, 'MOD lines differ from plan'))
            continue
        if any(m not in mods or mods[m]['trusted'] for m in ms):
            skipped.append((k, 'module not in graph'))
            continue
        base = sorted({d for m in ms for d in mods[m]['imports']})
        if k0 is not None:
            badk = [x for x in ms + base if k0.get(x) != keys.get(x)]
            if badk:
                skipped.append((k, 'key changed during run: %s' % badk[:3]))
                continue
            evidence = 'keys before run == keys after run'
        else:
            if bad:
                hit = [mods[x]['real'] for x in closure_of(g, ms + base)
                       if not mods[x]['trusted'] and mods[x]['real'] in bad and x not in verified]
                if hit:
                    skipped.append((k, 'not certified: %s (%s)' % (hit[0], bad[hit[0]])))
                    continue
            vused = sorted(x for x in closure_of(g, ms + base) if x in verified)
            evidence = 'drift watch: every closure file unchanged since run start %s%s; %s' % (
                since, ('; content-verified (sha of the remotely used bytes == current content sha): %s' %
                        ','.join(vused)) if vused else '', arg('--evidence', ''))
        out_sha = file_sha(out)
        if (plan_sha, k, out_sha) in existing:
            continue
        new_entries.append({'id': '%s#%d' % (plan_sha[:12], k), 'plan': os.path.abspath(plan), 'plan_sha': plan_sha,
                            'k': k, 'height': h, 'out': os.path.abspath(out), 'out_sha': out_sha,
                            'constants': int(mok.group(2)), 'mods': {m: keys[m] for m in ms},
                            'base': {d: keys[d] for d in base}, 'pkgfp': K['pkgfp'], 'lp_used': g['lp'], 'by': by,
                            'evidence': evidence, 'note': note, 'recorded': now()})
        n_rec += 1
    append_cache(new_entries)
    print('record: shards OK %d, recorded %d, skipped %d' % (n_ok, n_rec, len(skipped)))
    for s in skipped[:20]:
        print('  skipped', s)


def cmd_record_closure():
    """Register a monolithic `ReplayClosure.lean --json` REPLAY_OK run as ONE whole-closure entry.
    ReplayClosure replays every target of closure(roots) in topological order against the trusted base plus the
    targets replayed before it, so the entry is reusable for a closure F only if ALL its modules lie in F with equal
    keys (base = {}). Evidence: the replay JSON records the olean path of every module; each must resolve (realpath)
    to the file the current graph resolves, and the drift watch must certify every file unchanged since --since
    (or give --keys-before)."""
    jp = arg('--json')
    rj = json.load(open(jp))
    g = json.load(open(arg('--graph')))
    K = json.load(open(arg('--keys')))
    keys = K['keys']
    if os.path.abspath(arg('--graph')) != K['graph']:
        raise SystemExit('keys were computed from a different graph')
    if rj.get('result') != 'REPLAY_OK':
        raise SystemExit('replay result is %r, not REPLAY_OK' % rj.get('result'))
    mods = rj['modules'] if isinstance(rj['modules'], list) else []
    jm = {x['module']: x['path'] for x in mods}
    T = {m for m, e in g['modules'].items() if not e['trusted']}
    if set(jm) != T:
        raise SystemExit('replayed module set (%d) != current closure of the graph (%d): missing %s extra %s' % (
            len(jm), len(T), sorted(T - set(jm))[:3], sorted(set(jm) - T)[:3]))
    def same_file(p, q):
        try:
            a, b = os.stat(p), os.stat(q)
        except FileNotFoundError:
            return False
        if (a.st_dev, a.st_ino) == (b.st_dev, b.st_ino):
            return True
        return a.st_size == b.st_size and file_sha(p) == file_sha(q)
    diff = [m for m, p in jm.items() if not same_file(p, g['modules'][m]['path'])]
    if diff:
        raise SystemExit('%d modules resolve to a different file than at replay time, e.g. %s' % (len(diff), diff[:3]))
    k0 = json.load(open(arg('--keys-before')))['keys'] if arg('--keys-before') else None
    since = arg('--since')
    if k0 is not None:
        bad = [m for m in jm if k0.get(m) != keys.get(m)]
        if bad:
            raise SystemExit('keys changed during the run: %s' % bad[:3])
        evidence = 'keys before run == keys after run'
    else:
        if not since:
            raise SystemExit('need --keys-before or --since')
        if K['pkg_max_mtime_ns'] >= iso_epoch(since) * 10 ** 9:
            raise SystemExit('package oleans modified after run start')
        badf, why = drift_evidence_files(g, since)
        if why:
            raise SystemExit('no drift evidence: ' + why)
        if badf:
            raise SystemExit('%d files not certified unchanged since %s, e.g. %s' % (len(badf), since,
                                                                                  list(badf.items())[:2]))
        evidence = 'drift watch: all %d closure files unchanged since run start %s; paths match the replay JSON' % (
            len(jm), since)
    os.makedirs(RC, exist_ok=True)
    js = file_sha(jp)
    ent = {'kind': 'closure', 'id': 'closure:%s' % js[:12], 'json': os.path.abspath(jp), 'json_sha': js,
           'out': os.path.abspath(jp), 'out_sha': js, 'roots': rj.get('roots'),
           'constants': rj.get('target_constants'), 'mods': {m: keys[m] for m in jm}, 'base': {},
           'axioms': rj.get('axioms'), 'pkgfp': K['pkgfp'], 'by': arg('--by'), 'evidence': evidence,
           'note': arg('--note', ''), 'recorded': now()}
    append_cache([ent])
    print('record-closure: %s roots %s modules %d constants %s' % (ent['id'], ent['roots'], len(jm),
                                                                    ent['constants']))


# ---------------------------------------------------------------------------------------------------- reduce
def cmd_reduce():
    plan = load_plan(arg('--plan'))
    g = json.load(open(arg('--graph')))
    K = json.load(open(arg('--keys')))
    keys = K['keys']
    F = {m for m, e in g['modules'].items() if not e['trusted']}
    pm = [m for _, _, ms in plan for m in ms]
    if set(pm) != F or len(pm) != len(F):
        raise SystemExit('plan modules (%d, %d distinct) != graph targets (%d)' % (len(pm), len(set(pm)), len(F)))
    entries = load_cache_entries()
    deny = set(x for x in (arg('--by-deny', '') or '').split(',') if x)
    if deny:
        entries = [e for e in entries if e.get('by') not in deny]
    covered, used = {}, set()
    for e in entries:
        if not all(m in F and keys.get(m) == km for m, km in e['mods'].items()):
            continue
        if not all(keys.get(d) == kd for d, kd in e['base'].items()):
            continue
        if not os.path.exists(e['out']) or file_sha(e['out']) != e['out_sha']:
            continue
        for m in e['mods']:
            if m not in covered:
                covered[m] = e['id']
                used.add(e['id'])
    n_left = 0
    with open(arg('--out'), 'w') as f:
        for k, h, ms in plan:
            rest = [m for m in ms if m not in covered]
            if rest:
                f.write('%d\t%d\t%s\n' % (k, h, ','.join(rest)))
                n_left += len(rest)
    json.dump({'plan': os.path.abspath(arg('--plan')), 'keys': os.path.abspath(arg('--keys')), 'time': now(),
               'covered': covered, 'entries_used': sorted(used), 'n_plan': len(pm), 'n_covered': len(covered),
               'n_left': n_left}, open(arg('--covered'), 'w'), indent=0)
    by = {}
    ent_by = {e['id']: e.get('by') for e in entries}
    for m, eid in covered.items():
        by[ent_by.get(eid)] = by.get(ent_by.get(eid), 0) + 1
    print('reduce: plan modules %d, covered by cache %d (%d cached shards; modules by producer %s), left %d -> %s' %
          (len(pm), len(covered), len(used), by, n_left, arg('--out')))


# ---------------------------------------------------------------------------------------------------- verdict
def cmd_verdict():
    plan = load_plan(arg('--plan'))
    cov = json.load(open(arg('--covered')))
    red = load_plan(arg('--reduced'))
    rdir = arg('--rshards')
    keys = json.load(open(arg('--keys')))['keys']
    entries = {e['id']: e for e in load_cache_entries()}
    problems = []
    # re-check every cache entry used: output bytes and all keys unchanged now
    for eid in cov['entries_used']:
        e = entries.get(eid)
        if not e:
            problems.append('cache entry vanished: %s' % eid)
            continue
        if file_sha(e['out']) != e['out_sha']:
            problems.append('cached shard output changed: %s' % e['out'])
        bad = [x for x, kx in list(e['mods'].items()) + list(e['base'].items()) if keys.get(x) != kx]
        if bad:
            problems.append('key changed since reduce: %s %s' % (eid, bad[:3]))
    replayed = {}
    summ = {}
    if red:
        sp = os.path.join(rdir, 'summary.json')
        summ = json.load(open(sp)) if os.path.exists(sp) else {}
        if summ.get('result') != 'SHARDED_REPLAY_OK':
            problems.append('reduced run not SHARDED_REPLAY_OK: %s' % summ.get('result'))
        for k, h, ms in red:
            out = os.path.join(rdir, 'shard_%04d.out' % k)
            txt = open(out).read() if os.path.exists(out) else ''
            if not re.search(r'^SHARD_REPLAY_OK %d ' % k, txt, re.M):
                problems.append('reduced shard %d not OK' % k)
                continue
            for m in re.findall(r'^MOD (\S+) consts=', txt, re.M):
                if m in replayed:
                    problems.append('duplicate replay %s' % m)
                replayed[m] = k
    allm = [m for _, _, ms in plan for m in ms]
    both = [m for m in allm if m in replayed and m in cov['covered']]
    none = [m for m in allm if m not in replayed and m not in cov['covered']]
    extra = [m for m in replayed if m not in set(allm)]
    if both:
        problems.append('%d modules both cached and replayed' % len(both))
    if none:
        problems.append('%d modules neither cached nor replayed: %s' % (len(none), none[:5]))
    if extra:
        problems.append('%d replayed modules not in plan' % len(extra))
    res = {'time': now(), 'plan': os.path.abspath(arg('--plan')), 'plan_modules': len(allm),
           'covered_by_cache': len(cov['covered']), 'cache_entries_used': len(cov['entries_used']),
           'replayed_now': len(replayed), 'reduced_plan': os.path.abspath(arg('--reduced')),
           'reduced_summary': summ, 'problems': problems,
           'result': 'INCREMENTAL_REPLAY_OK' if not problems else 'INCREMENTAL_REPLAY_FAIL'}
    json.dump(res, open(arg('--out'), 'w'), indent=1)
    print(res['result'], 'plan', len(allm), 'cached', len(cov['covered']), 'replayed', len(replayed),
          'problems', problems[:5])
    sys.exit(0 if not problems else 1)


def cmd_status():
    entries = load_cache_entries()
    by = {}
    for e in entries:
        b = by.setdefault((e['by'], e.get('plan') or e.get('json')), [0, 0, 0])
        b[0] += 1
        b[1] += len(e['mods'])
        b[2] += e.get('constants') or 0
    print('cache entries', len(entries))
    for (who, plan), (n, nm, nc) in sorted(by.items()):
        print('  %-10s shards %5d modules %6d constants %9d  %s' % (who, n, nm, nc, plan))


if __name__ == '__main__':
    {'graph': cmd_graph, 'keys': cmd_keys, 'record': cmd_record, 'record-closure': cmd_record_closure,
     'reduce': cmd_reduce, 'verdict': cmd_verdict,
     'status': cmd_status}[sys.argv[1]]()
