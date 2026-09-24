#!/usr/bin/env python3
"""build_plain.py — rebuild the General Courtade–Kumar closure from the v3 sources with plain `lean` (no Lake).

Compiles every module of the closure (or of the closure of --target) in topological order into a FRESH output root,
with N parallel `lean` processes and a memory budget, exactly as the campaign's clean build (Lane CB) did:

  plain       (45,348 modules) cwd = SRC, `lean -j 1 -M 0 --json -o OUT/M.olean -i OUT/M.ilean M/Path.lean`
  lake        (111 modules)   the same plus `--setup M.setup.json`, the Lake-4.33 setup record of package
                               `general-ck` (the olean records the package name; bytes then equal CB's)
  prefix:DIR  (39 modules)    compiled from a hard-linked staging copy DIR/M/Path.lean (cwd = stage), so the main
                               module name carries the historical prefix (bytes then equal CB's)
  abs:DIR     (2 modules)     CB emulated an absolute source path of the original host; not reproducible elsewhere,
                               so they are compiled `plain` here and are EXPECTED to differ from CB's bytes
  --canonical                  compile everything `plain` (all bytes that differ from CB's then differ only by module
                               name / package name / embedded path)

LEAN_PATH = OUT : the package roots (Mathlib db584cd6… and its 7 dependencies). Nothing is read from any other
olean root. A module is started when all of its closure imports have compiled with rc 0; its outputs are marked done
only after rc 0 (restart-safe: modules without a done-marker are recompiled).

usage:
  build_plain.py --src SRC --manifest SOURCES_MANIFEST.tsv --packages PKGDIR --out OUT
                 [--lean LEAN] [--jobs N] [--mem-gb M] [--target M1,M2] [--canonical]
                 [--expect CLEAN_BUILD_HASHES.tsv] [--default-rss-gb G] [--lean-threads T]
  PKGDIR is either a directory holding the 8 package roots (aesop batteries importGraph LeanSearchClient mathlib
  plausible proofwidgets Qq; e.g. BUNDLE_DIR/packages of the v2 bundle) or a colon-separated list of roots.
Writes OUT/.build/results.tsv (module, recipe, rc, wall_s, maxrss_kb, olean_sha256, expected, match) and
OUT/.build/summary.json. Exit 0 iff every selected module compiled with rc 0 (and, with --expect, report matches).
"""
import argparse
import collections
import hashlib
import json
import os
import shutil
import subprocess
import sys
import threading
import time

PKGS = ["aesop", "batteries", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq"]


def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def read_tsv(path):
    hdr = None
    for line in open(path):
        line = line.rstrip("\n")
        if not line:
            continue
        if line.startswith("#"):
            if hdr is None:
                hdr = [h.lstrip("#") for h in line.split("\t")]
            continue
        yield dict(zip(hdr, line.split("\t")))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True)
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--packages", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--mem-gb", type=float, default=64.0)
    ap.add_argument("--target", default="")
    ap.add_argument("--canonical", action="store_true")
    ap.add_argument("--expect", default="")
    ap.add_argument("--default-rss-gb", type=float, default=8.0)
    ap.add_argument("--lean-threads", type=int, default=1)
    a = ap.parse_args()

    src = os.path.realpath(a.src)
    out = os.path.realpath(a.out)
    bd = os.path.join(out, ".build")
    for d in ("logs", "done", "setup", "prefix_stage"):
        os.makedirs(os.path.join(bd, d), exist_ok=True)
    if os.path.isdir(a.packages) and all(os.path.isdir(os.path.join(a.packages, p)) for p in PKGS):
        pkg_roots = [os.path.join(os.path.realpath(a.packages), p) for p in PKGS]
    else:
        pkg_roots = [os.path.realpath(x) for x in a.packages.split(":") if x]
    for r in pkg_roots:
        if not os.path.isdir(r):
            sys.exit("package root missing: " + r)
    lean_path = ":".join([out] + pkg_roots)

    man = {r["module"]: r for r in read_tsv(a.manifest)}
    deps = {m: [d for d in r["closure_imports"].split(",") if d] for m, r in man.items()}
    expect, est_rss = {}, {}
    if a.expect:
        for r in read_tsv(a.expect):
            expect[r["module"]] = r["olean_sha256"]
            if r.get("maxrss_kb"):
                try:
                    est_rss[r["module"]] = int(r["maxrss_kb"]) / 1048576.0
                except ValueError:
                    pass
    # selection: closure of the targets (default: everything in the manifest)
    if a.target:
        sel, stack = set(), [t for t in a.target.split(",") if t]
        while stack:
            m = stack.pop()
            if m in sel:
                continue
            if m not in man:
                sys.exit("unknown module: " + m)
            sel.add(m)
            stack.extend(deps[m])
    else:
        sel = set(man)

    def recipe(m):
        r = "plain" if a.canonical else (man[m].get("recipe") or "plain")
        return "plain" if r.startswith("abs:") else r

    def done_marker(m):
        return os.path.join(bd, "done", m)

    def is_done(m):
        p = done_marker(m)
        if not os.path.exists(p):
            return False
        o = os.path.join(out, m.replace(".", "/") + ".olean")
        try:
            sha, size = open(p).read().split()[:2]
            return os.path.getsize(o) == int(size)
        except (OSError, ValueError):
            return False

    lock = threading.Lock()
    done = {m for m in sel if is_done(m)}
    failed, running = set(), {}
    results = []
    rdeps = collections.defaultdict(list)
    for m in sel:
        for d in deps[m]:
            rdeps[d].append(m)
    # longest remaining chain first (keeps the critical path busy)
    height = {}
    order = sorted(sel, key=lambda x: int(man[x]["height"]))
    for m in reversed(order):
        height[m] = 1 + max((height[x] for x in rdeps[m] if x in sel), default=0)

    def command(m):
        rel = m.replace(".", "/")
        r = recipe(m)
        o, i = os.path.join(out, rel + ".olean"), os.path.join(out, rel + ".ilean")
        os.makedirs(os.path.dirname(o), exist_ok=True)
        args = [a.lean, "-j", str(a.lean_threads), "-M", "0", "--json"]
        cwd, srcarg = src, rel + ".lean"
        if r == "lake":
            sp = os.path.join(bd, "setup", m + ".setup.json")
            body = json.dumps({"plugins": [], "package": "general-ck", "options": {}, "name": m, "isModule": False,
                               "importArts": {}, "dynlibs": []}) + "\n"
            with open(sp, "w") as f:
                f.write(body)
            args += ["--setup", sp]
        elif r.startswith("prefix:"):
            pre = r.split(":", 1)[1]
            stage = os.path.join(bd, "prefix_stage")
            dst = os.path.join(stage, pre, rel + ".lean")
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            if not os.path.exists(dst):
                try:
                    os.link(os.path.join(src, rel + ".lean"), dst)   # a real directory entry: Lean names by realpath
                except OSError:
                    shutil.copyfile(os.path.join(src, rel + ".lean"), dst)
            cwd, srcarg = stage, pre + "/" + rel + ".lean"
        return args + ["-o", o, "-i", i, srcarg], cwd, o

    def run(m):
        cmd, cwd, o = command(m)
        logb = os.path.join(bd, "logs", m)
        timev = ["/usr/bin/time", "-v", "-o", logb + ".time"] if os.path.exists("/usr/bin/time") else []
        env = dict(os.environ, LEAN_PATH=lean_path)
        t0 = time.time()
        with open(logb + ".jsonl", "w") as fo, open(logb + ".err", "w") as fe:
            rc = subprocess.call(timev + cmd, cwd=cwd, env=env, stdout=fo, stderr=fe)
        wall = time.time() - t0
        rss = ""
        if timev and os.path.exists(logb + ".time"):
            for line in open(logb + ".time"):
                if "Maximum resident set size" in line:
                    rss = line.split(":")[1].strip()
        errs = 0
        for line in open(logb + ".jsonl", errors="replace"):
            if '"severity":"error"' in line.replace(" ", ""):
                errs += 1
        osha = sha256(o) if rc == 0 and os.path.exists(o) else ""
        ok = rc == 0 and errs == 0 and osha
        if ok:
            with open(done_marker(m), "w") as f:
                f.write("%s %d\n" % (osha, os.path.getsize(o)))
        exp = expect.get(m, "")
        match = ("IDENTICAL" if osha == exp else "DIFFERENT") if (exp and osha) else ""
        with lock:
            results.append((m, recipe(m), rc, errs, round(wall, 1), rss, osha, exp, match))
            running.pop(m, None)
            (done if ok else failed).add(m)
        print("%s %s rc=%d errors=%d %.1fs rss_kb=%s %s" % ("OK  " if ok else "FAIL", m, rc, errs, wall, rss, match),
              flush=True)

    budget = a.mem_gb
    t_start = time.time()
    while True:
        with lock:
            pending = [m for m in sel if m not in done and m not in failed and m not in running]
            blocked = [m for m in pending if any(d in failed for d in deps[m])]
            for m in blocked:
                failed.add(m)
                results.append((m, recipe(m), -1, 0, 0, "", "", expect.get(m, ""), "SKIPPED_DEP_FAILED"))
            ready = [m for m in pending if m not in blocked and all(d in done for d in deps[m])]
            ready.sort(key=lambda x: -height[x])
            used = sum(est_rss.get(x, a.default_rss_gb) for x in running)
            nrun = len(running)
        if not pending and not running:
            break
        started = False
        for m in ready:
            need = est_rss.get(m, a.default_rss_gb)
            if nrun >= a.jobs or (nrun > 0 and used + need > budget):
                break
            with lock:
                running[m] = time.time()
            threading.Thread(target=run, args=(m,), daemon=True).start()
            nrun += 1
            used += need
            started = True
        if not started:
            time.sleep(0.5)
    ok = not failed
    with open(os.path.join(bd, "results.tsv"), "w") as f:
        f.write("#module\trecipe\trc\terrors\twall_s\tmaxrss_kb\tolean_sha256\texpected_sha256\tmatch\n")
        for r in sorted(results):
            f.write("\t".join(str(x) for x in r) + "\n")
    cnt = collections.Counter(r[8] for r in results)
    summ = dict(selected=len(sel), built=len([r for r in results if r[2] == 0]), failed=sorted(failed)[:50],
                n_failed=len(failed), skipped_already_done=len(sel) - len(results), matches=dict(cnt),
                wall_s=round(time.time() - t_start, 1), lean_path=lean_path, canonical=a.canonical)
    json.dump(summ, open(os.path.join(bd, "summary.json"), "w"), indent=1)
    print(json.dumps(summ, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
