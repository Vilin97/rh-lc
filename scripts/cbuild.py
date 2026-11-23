#!/usr/bin/env python3
"""Lake-free parallel builder for this project. Run it from the repository root. Never use `lake build` here.

Rebuild changed sources and modules with interface errors or changed transitive interfaces.
Track successfully compiled source revisions separately from the published public .olean.
Scheduling is topological with longest-remaining-path priority.
usage: cbuild.py [-j N] [--lake-traces] [--defer-failed-dependents | --fallback-artifacts]

Each module is compiled with Lake's arguments and a small --setup file, so its outputs match Lake's byte for byte.
--lake-traces also runs scripts/lake_traces.py after a clean build, so stock `lake build --no-build` accepts the outputs.

Outputs go to .lake/build/lib/lean. Compiler errors go to .lake/cbuild/errs/<module>.log.
Environment overrides: CBUILD_REPO, CBUILD_LEAN, LEANWRAP_ERRDIR, CBUILD_LOG, CBUILD_FAILED, CBUILD_TMP.

With lean.final, --defer-failed-dependents records the original Lean diagnostics,
skips fallback compilation, and defers modules whose imports failed this pass.
The adjacent cbuild-defer-checkouts.txt can list checkout paths that use this mode
by default with lean.final. --fallback-artifacts selects the original behavior.
"""
import os, re, sys, subprocess, time, heapq, threading, collections, json
from pathlib import Path
pass_started = time.monotonic()
REPO = os.path.abspath(os.environ.get('CBUILD_REPO', os.getcwd())); LIB = f'{REPO}/.lake/build/lib/lean'
STATE = f'{REPO}/.lake/cbuild'; os.makedirs(STATE, exist_ok=True)
LEAN = os.environ.get('CBUILD_LEAN') or subprocess.run(['elan', 'which', 'lean'], cwd=REPO, capture_output=True, text=True, check=True).stdout.strip()
J = int(sys.argv[sys.argv.index('-j') + 1]) if '-j' in sys.argv else 90
DEFER_FAILED = '--defer-failed-dependents' in sys.argv
FALLBACK_ARTIFACTS = '--fallback-artifacts' in sys.argv
if DEFER_FAILED and FALLBACK_ARTIFACTS:
    sys.exit('Choose one of --defer-failed-dependents and --fallback-artifacts')
if not (DEFER_FAILED or FALLBACK_ARTIFACTS) and Path(LEAN).name == 'lean.final':
    defaults_path = Path(__file__).with_name('cbuild-defer-checkouts.txt')
    try:
        DEFER_FAILED = os.path.realpath(REPO) in defaults_path.read_text().splitlines()
    except FileNotFoundError:
        pass
import tomllib
_lake = tomllib.load(open(f'{REPO}/lakefile.toml', 'rb'))
PACKAGE = _lake['name']
def _flatten(d, prefix=''):
    out = {}
    for k, v in d.items():
        if isinstance(v, dict): out.update(_flatten(v, f'{prefix}{k}.'))
        else: out[prefix + k] = v
    return out
def _glob(g, m):
    if g.endswith('.+'): return m.startswith(g[:-1])
    if g.endswith('.*'): return m == g[:-2] or m.startswith(g[:-1])
    return m == g
_LIBS = [(l.get('globs', l.get('roots', [l['name']])),
          {**_flatten(_lake.get('leanOptions', {})), **_flatten(l.get('leanOptions', {}))},
          list(_lake.get('moreLeanArgs', [])) + list(l.get('moreLeanArgs', []))) for l in _lake.get('lean_lib', [])]
_DEFAULT = (_flatten(_lake.get('leanOptions', {})), list(_lake.get('moreLeanArgs', [])))
def module_config(m):
    for globs, options, args in _LIBS:
        if any(_glob(g, m) for g in globs): return options, args
    return _DEFAULT
_MODULE_HEADER = re.compile(r'(?:\s+|--[^\n]*\n|/-.*?-/)*module\b', re.S)
env = dict(os.environ)
env.setdefault('LEANWRAP_ERRDIR', f'{STATE}/errs'); os.makedirs(env['LEANWRAP_ERRDIR'], exist_ok=True)
if DEFER_FAILED:
    env['LEANWRAP_NO_FALLBACK'] = '1'
    print('build mode: defer failed dependents', flush=True)
elif FALLBACK_ARTIFACTS:
    env.pop('LEANWRAP_NO_FALLBACK', None)
IMP = re.compile(r'^(?:public\s+|private\s+|meta\s+)*import\s+(?:(all)\s+)?(\S+)', re.M)

mods = {}
for root, _, fs in os.walk(f'{REPO}/src'):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(root, f); m = os.path.relpath(p, f'{REPO}/src')[:-5].replace('/', '.')
            if m == 'Challenge': continue
            mods[m] = p
deps = {}
import_all = {}
for m, p in mods.items():
    imports = [(kind, d) for kind, d in IMP.findall(open(p, encoding='utf-8').read()) if d in mods]
    deps[m] = [d for _, d in imports]
    if all_deps := {d for kind, d in imports if kind == 'all'}:
        import_all[m] = all_deps
all_targets = set().union(*import_all.values())
rdeps = collections.defaultdict(list)
for m, ds in deps.items():
    for d in ds: rdeps[d].append(m)
# height = longest path to a sink (for priority)
order = []; indeg = {m: len(deps[m]) for m in mods}
q = collections.deque(m for m in mods if indeg[m] == 0)
while q:
    m = q.popleft(); order.append(m)
    for u in rdeps[m]:
        indeg[u] -= 1
        if indeg[u] == 0: q.append(u)
height = {}
if len(order) != len(mods):
    sys.exit(f'import graph settled {len(order)}/{len(mods)} modules')
for m in reversed(order):
    height[m] = 1 + max((height[u] for u in rdeps[m]), default=0)

def olean(m): return f'{LIB}/{m.replace(".", "/")}.olean'
def artifact_stat(path):
    try:
        return os.stat(path)
    except FileNotFoundError:
        return None

def signature(info):
    return (info.st_mtime_ns, info.st_ctime_ns, info.st_size) if info is not None else None

def stamp_path(artifact):
    return artifact.removesuffix('.olean') + '.cbuild-source'

def stamp_data(source, artifact):
    return json.dumps([LEAN, 'lake-identical-v1', source, artifact]) + '\n'

def source_is_stale(artifact, source_info, artifact_info):
    if artifact_info is None or source_info is None:
        return True
    try:
        with open(stamp_path(artifact)) as stamp:
            return stamp.read() != stamp_data(signature(source_info), signature(artifact_info))
    except FileNotFoundError:
        return source_info.st_mtime_ns > artifact_info.st_mtime_ns

artifact_info = {m: artifact_stat(olean(m)) for m in mods}
omt = {m: info.st_mtime_ns if info is not None else None for m, info in artifact_info.items()}
# non-transitive self-staleness; propagation happens only when a rebuilt module's public .olean changes
self_stale = set()
for m in mods:
    o = omt[m]
    blanked = os.path.exists(f"{env['LEANWRAP_ERRDIR']}/src.{m}.json")   # built with errors/blanking
    # modules still carrying interface errors are rebuilt every pass: their errors may come from any
    # (transitive) upstream interface, and module-system imports are transitive
    if blanked or source_is_stale(olean(m), artifact_stat(mods[m]), artifact_info[m]) or (
        '--strict' in sys.argv and any((omt[d] or 0) > o for d in deps[m])
    ):
        self_stale.add(m)
print(f'modules {len(mods)} self-stale {len(self_stale)}', flush=True)

# ---- transitive interface fingerprints: a module is current only if the public interfaces of its whole
# import closure are byte-identical to what it was last compiled against
import hashlib, concurrent.futures as _cf
def _h(*parts):
    x = hashlib.blake2b(digest_size=16)
    for p in parts: x.update(p.encode()); x.update(b'\0')
    return x.hexdigest()
def pub_hash(path):
    x = hashlib.blake2b(digest_size=16)
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''): x.update(chunk)
    return x.hexdigest()
def input_path(m): return olean(m)[:-6] + '.cbuild-input'
def read_input(m):
    try: return open(input_path(m)).read().strip()
    except OSError: return None
def write_input(m, v):
    t = input_path(m) + '.tmp'
    with open(t, 'w') as f: f.write(v + '\n')
    os.replace(t, input_path(m))

def hash_public_batch(modules):
    return [(m, pub_hash(olean(m))) for m in modules]

phash = {}
have = [m for m in mods if omt[m] is not None]
batches = (have[i:i+128] for i in range(0, len(have), 128))
with _cf.ThreadPoolExecutor(4) as executor:
    for hashes in executor.map(hash_public_batch, batches):
        phash.update(hashes)
def full_artifact_paths(m):
    base = olean(m).removesuffix('.olean')
    return [base + suffix for suffix in ('.olean.server', '.olean.private', '.ir.sig', '.ir')]

def full_artifact_hash(m):
    return _h(*(pub_hash(p) if artifact_stat(p) is not None else 'MISSING' for p in full_artifact_paths(m)))

# An `import all` consumer can see private declarations and their bodies.
full_hashes = {m: full_artifact_hash(m) for m in all_targets}
full_mtimes = {
    m: max((info.st_mtime_ns for p in full_artifact_paths(m) if (info := artifact_stat(p))), default=0)
    for m in all_targets
}

def input_fp(m, closure):
    if all_deps := import_all.get(m):
        return _h(*sorted(_h(closure[d], full_hashes[d]) if d in all_deps else closure[d] for d in deps[m]))
    return _h(*sorted(closure[d] for d in deps[m]))

initial_closure = {}
newest_import = {}
seeded = {}
stored_inputs = {}
all_current = not self_stale
for m in order:
    initial_input = input_fp(m, initial_closure)
    initial_closure[m] = _h(phash.get(m, 'MISSING'), initial_input)
    stored_inputs[m] = read_input(m)
    all_current = all_current and stored_inputs[m] == initial_input
    newest_import[m] = max(
        (max(omt[d] or 0, newest_import[d], full_mtimes[d] if d in import_all.get(m, ()) else 0) for d in deps[m]),
        default=0,
    )
    if m not in self_stale and m not in import_all and omt[m] is not None:
        build_stamp = artifact_stat(stamp_path(olean(m)))
        last_built = build_stamp.st_mtime_ns if build_stamp is not None else omt[m]
        if last_built >= newest_import[m]:
            # Compare with these prior inputs even if an upstream rebuild changes them in this pass.
            seeded[m] = initial_input

_ns = sum(1 for m, stored in stored_inputs.items() if stored is None and m not in seeded)
print(f'transitive check: {len(seeded)} seeded current, {_ns} without an input fingerprint', flush=True)

def write_lake_traces():
    if '--lake-traces' not in sys.argv: return
    tool = str(Path(__file__).with_name('lake_traces.py'))
    rc = subprocess.run([sys.executable, tool, '-j', str(min(J, 48))], env=dict(os.environ, CBUILD_REPO=REPO, CBUILD_LEAN=LEAN)).returncode
    if rc: sys.exit(rc)

def finish(built, changed, failed, deferred=()):
    failure_path = os.environ.get('CBUILD_FAILED', f'{STATE}/failed')
    with open(failure_path, 'w') as failures:
        failures.write('\n'.join(sorted(failed)))
    if DEFER_FAILED:
        with open(failure_path + '.deferred', 'w') as skipped:
            skipped.write('\n'.join(sorted(deferred)))
        print(f'Deferred {len(deferred)} modules with a failed upstream dependency', flush=True)
    print(f'{time.strftime("%H:%M:%S")} FINISHED built {built} changed {len(changed)} failed {len(failed)}'
          f' in {time.monotonic()-pass_started:.0f}s; settled {len(mods)}/{len(mods)}', flush=True)

log = open(os.environ.get('CBUILD_LOG', f'{STATE}/build.log'), 'a')
TMP = os.environ.get('CBUILD_TMP', f'{STATE}/tmp'); os.makedirs(TMP, exist_ok=True)
# All source and artifact stamps and stored transitive fingerprints already match.
# Missing fingerprints still go through the scheduler so eligible stamps get written.
if all_current:
    finish(0, (), ())
    write_lake_traces()
    sys.exit(0)

# The search path Lake would use, computed without running Lake.
_packages = json.load(open(f'{REPO}/lake-manifest.json')).get('packages', [])
_libdir = subprocess.run([LEAN, '--print-libdir'], capture_output=True, text=True, check=True).stdout.strip()
env['LEAN_PATH'] = ':'.join([f"{REPO}/.lake/packages/{p['name']}/.lake/build/lib/lean" for p in reversed(_packages)] + [LIB, _libdir])
cfp = {}
pending = {m: len(deps[m]) for m in mods}
heap = [(-height[m], m) for m in mods if pending[m] == 0]
heapq.heapify(heap)
lock = threading.Lock(); cv = threading.Condition(lock)
settled = 0; built = 0; changed = set(); failed = set(); running = 0; t0 = time.time()
unavailable = set()

def same(a, b):
    try:
        if os.path.getsize(a) != os.path.getsize(b): return False
        return open(a, 'rb').read() == open(b, 'rb').read()
    except OSError: return False

def build(m):
    """returns (rc, secs, public_olean_changed)"""
    rel = os.path.relpath(mods[m], REPO); o = olean(m)
    os.makedirs(os.path.dirname(o), exist_ok=True)
    tdir = os.path.join(TMP, m); os.makedirs(tdir, exist_ok=True)
    to = os.path.join(tdir, 'X.olean')
    s = time.time()
    source_revision = signature(artifact_stat(mods[m]))
    options, args = module_config(m)
    setup = os.path.join(tdir, 'setup.json')
    with open(mods[m], encoding='utf-8') as source, open(setup, 'w') as out:
        json.dump({'name': m, 'package': PACKAGE, 'isModule': bool(_MODULE_HEADER.match(source.read(20000))),
                   'importArts': {}, 'dynlibs': [], 'plugins': [], 'options': options}, out)
    r = subprocess.run([LEAN] + args + ['--json', rel, '-o', to, '-i', os.path.join(tdir, 'X.ilean'),
                        '-c', os.path.join(tdir, 'X.c'), '--setup', setup], cwd=REPO, env=env, capture_output=True)
    secs = time.time() - s
    if r.returncode != 0:
        with open(os.path.join(env['LEANWRAP_ERRDIR'], f'{m}.log'), 'wb') as diagnostics:
            diagnostics.write(r.stdout + r.stderr)
        subprocess.run(['rm', '-rf', tdir]); return r.returncode, secs, not DEFER_FAILED
    ch = not same(to, o)
    base = o[:-6]
    for f in os.listdir(tdir):
        if not f.startswith('X.'):
            continue
        suffix = f[1:]   # 'X.olean.private' -> '.olean.private'
        dst = base + suffix
        if suffix == '.c':
            dst = f"{REPO}/.lake/build/ir/{m.replace('.', '/')}.c"
            os.makedirs(os.path.dirname(dst), exist_ok=True)
        if suffix == '.olean' and not ch:
            continue      # keep old public olean (and its mtime)
        os.replace(os.path.join(tdir, f), dst)
    # A source edit during compilation invalidates this record on the next pass.
    # The public artifact keeps its mtime if its contents did not change.
    temp_stamp = os.path.join(tdir, 'source-stamp')
    with open(temp_stamp, 'w') as stamp:
        stamp.write(stamp_data(source_revision, signature(artifact_stat(o))))
    os.replace(temp_stamp, stamp_path(o))
    subprocess.run(['rm', '-rf', tdir])
    return 0, secs, ch

def update_module(m):
    ifp = input_fp(m, cfp)
    stored = stored_inputs[m]
    previous = seeded.get(m) if stored is None else stored
    need = m in self_stale or previous != ifp
    rc, secs, ch = 0, 0.0, False
    if need:
        if any(d in failed and omt.get(d) is None for d in deps[m]):
            rc, ch = 1, True
        else:
            rc, secs, ch = build(m)
    if rc == 0:
        if ch or m not in phash: phash[m] = pub_hash(olean(m))
        if need and m in all_targets: full_hashes[m] = full_artifact_hash(m)
        if need or stored is None: write_input(m, ifp)
        cfp[m] = _h(phash[m], ifp)
    else:
        cfp[m] = _h('FAILED', ifp)
    return need, rc, secs, ch

def worker():
    global settled, running, built
    while True:
        with cv:
            while not heap and settled < len(mods):
                if running == 0 and not heap: break
                cv.wait(5)
            if not heap: return
            _, m = heapq.heappop(heap); running += 1
            defer = DEFER_FAILED and not unavailable.isdisjoint(deps[m])
        if not defer:
            need, rc, secs, ch = update_module(m)
        with cv:
            running -= 1; settled += 1
            if defer:
                unavailable.add(m)
            elif need:
                built += 1
                if rc != 0:
                    failed.add(m)
                    unavailable.add(m)
                if ch: changed.add(m)
                log.write(f'{time.strftime("%H:%M:%S")}\t{"OK" if rc == 0 else "FAIL"}\t{secs:.1f}\t{"CHG" if ch else "same"}\t{m}\n')
                if built % 500 == 0:
                    el = time.time() - t0
                    print(f'{time.strftime("%H:%M:%S")} built {built} settled {settled}/{len(mods)} changed {len(changed)} failed {len(failed)} rate {built/el:.1f}/s', flush=True)
            for u in rdeps[m]:
                pending[u] -= 1
                if pending[u] == 0: heapq.heappush(heap, (-height[u], u))
            cv.notify_all()

ths = [threading.Thread(target=worker, daemon=True) for _ in range(J)]
for t in ths: t.start()
for t in ths: t.join()
if settled != len(mods):
    sys.exit(f'build settled {settled}/{len(mods)} modules')
finish(built, changed, failed, unavailable - failed)
if failed:
    sys.exit(1)
write_lake_traces()
