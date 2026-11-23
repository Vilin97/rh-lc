#!/usr/bin/env python3
"""Write the .hash and .trace files that let stock `lake build` accept outputs built by scripts/cbuild.py.

Run from the repository root after a build. It compiles nothing. It reimplements Lake 4.36's module input hash
(Lake/Build/Module.lean), so check it with `--check` against real Lake traces after any toolchain bump.

usage: lake_traces.py [-j N] [--check]
  --check   write nothing; compare with the .trace files already present (for example from a real Lake build)
"""
import collections, concurrent.futures as cf, ctypes, json, os, subprocess, sys, tempfile, tomllib

REPO = os.path.abspath(os.environ.get('CBUILD_REPO', os.getcwd()))
J = int(sys.argv[sys.argv.index('-j') + 1]) if '-j' in sys.argv else 32
CHECK = '--check' in sys.argv
LEAN = os.environ.get('CBUILD_LEAN') or subprocess.run(['elan', 'which', 'lean'], cwd=REPO, capture_output=True, text=True, check=True).stdout.strip()
M64 = (1 << 64) - 1; NIL = 1723

C_HASH = r"""
typedef unsigned long long u64; typedef unsigned long sz;
u64 lean_hash_str(sz len, const unsigned char *s, u64 seed) {
  const u64 m = 0xc6a4a7935bd1e995ULL; const int r = 47; u64 h = seed ^ (len * m); sz n = len / 8;
  for (sz i = 0; i < n; i++) { u64 k; __builtin_memcpy(&k, s + 8 * i, 8); k *= m; k ^= k >> r; k *= m; h ^= k; h *= m; }
  const unsigned char *t = s + 8 * n;
  switch (len & 7) { case 7: h ^= (u64)t[6] << 48; case 6: h ^= (u64)t[5] << 40; case 5: h ^= (u64)t[4] << 32;
    case 4: h ^= (u64)t[3] << 24; case 3: h ^= (u64)t[2] << 16; case 2: h ^= (u64)t[1] << 8; case 1: h ^= (u64)t[0]; h *= m; }
  h ^= h >> r; h *= m; h ^= h >> r; return h; }
"""
def load_hasher():
    state = f'{REPO}/.lake/cbuild'; os.makedirs(state, exist_ok=True); so = f'{state}/leanhash.so'
    if not os.path.exists(so):
        with tempfile.TemporaryDirectory(dir=state) as d:
            src = f'{d}/h.c'; open(src, 'w').write(C_HASH); tmp = f'{d}/h.so'
            subprocess.run([os.path.join(os.path.dirname(os.path.realpath(LEAN)), 'clang'), '-O2', '-shared', '-fPIC', '-nostdlib', '-fuse-ld=lld', src, '-o', tmp], check=True)
            os.replace(tmp, so)
    f = ctypes.CDLL(so).lean_hash_str; f.restype = ctypes.c_uint64; f.argtypes = [ctypes.c_size_t, ctypes.c_char_p, ctypes.c_uint64]
    return f
_hash_str = load_hasher()
def bhash(b): return _hash_str(len(b), b, 11)
MURMUR = 0xc6a4a7935bd1e995
def mix(h, k):   # lean_uint64_mix_hash
    k = (k * MURMUR) & M64; k ^= k >> 47; k ^= MURMUR
    return ((h ^ k) * MURMUR) & M64
def of_hashable(x): return mix(NIL, x)
def shash(s): return bhash(s.encode())
def name_hash(n):
    h = NIL
    for part in n.split('.'): h = mix(h, shash(part))
    return h
def hex16(x): return f'{x:016x}'

def flatten(d, pre=''):
    out = {}
    for k, v in d.items():
        if isinstance(v, dict): out.update(flatten(v, f'{pre}{k}.'))
        else: out[pre + k] = v
    return out
def opt_value(v): return ('true' if v else 'false') if isinstance(v, bool) else str(v)
def options_hash(opts):
    t = NIL
    for n in sorted(opts, key=lambda n: (name_hash(n), n)):
        t = mix(t, of_hashable(shash(f'-D{n}={opt_value(opts[n])}')))
    return t
def glob_match(g, m):
    if g.endswith('.+'): return m.startswith(g[:-1])
    if g.endswith('.*'): return m == g[:-2] or m.startswith(g[:-1])
    return m == g

cfg = tomllib.load(open(f'{REPO}/lakefile.toml', 'rb'))
PKG = cfg['name']; SRC = os.path.join(REPO, cfg.get('srcDir', '.')); PLATFORM_INDEPENDENT = cfg.get('platformIndependent', None)
if PLATFORM_INDEPENDENT is not True: sys.exit('lake_traces.py supports platformIndependent = true only')
LIBS = []
for l in cfg.get('lean_lib', []):
    roots = l.get('roots', [l['name']])
    LIBS.append({'name': l['name'], 'globs': l.get('globs', roots), 'opts': {**flatten(cfg.get('leanOptions', {})), **flatten(l.get('leanOptions', {}))},
                 'args': list(cfg.get('moreLeanArgs', [])) + list(l.get('moreLeanArgs', []))})
    LIBS[-1]['opts_hash'] = options_hash(LIBS[-1]['opts']); h = NIL
    for a in LIBS[-1]['args']: h = mix(h, of_hashable(shash(a)))   # Lake's ComputeHash (Array α)
    LIBS[-1]['args_hash'] = h
    LIBS[-1]['extra'] = mix(NIL, NIL)
def lib_of(m):
    for l in LIBS:
        if any(glob_match(g, m) for g in l['globs']): return l
    return None

def parse_header(path):
    s = open(path, encoding='utf-8', errors='replace').read(); i = 0; n = len(s); toks = []
    while i < n:
        c = s[i]
        if c.isspace(): i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = n if j < 0 else j + 1; continue
        if s.startswith('/-', i):
            d = 1; i += 2
            while i < n and d:
                if s.startswith('/-', i): d += 1; i += 2
                elif s.startswith('-/', i): d -= 1; i += 2
                else: i += 1
            continue
        j = i
        while j < n and not s[j].isspace(): j += 1
        toks.append(s[i:j]); i = j
        if toks[-1] not in ('module', 'prelude', 'public', 'meta', 'import', 'all') and (len(toks) < 2 or toks[-2] not in ('import', 'all')): break
    k = 0; is_mod = False; imports = []
    if k < len(toks) and toks[k] == 'module': is_mod = True; k += 1
    if k < len(toks) and toks[k] == 'prelude': k += 1
    while k < len(toks):
        pub = meta = al = False
        if toks[k] == 'public': pub = True; k += 1
        if k < len(toks) and toks[k] == 'meta': meta = True; k += 1
        if k >= len(toks) or toks[k] != 'import': break
        k += 1
        if k < len(toks) and toks[k] == 'all': al = True; k += 1
        if k >= len(toks): break
        imports.append((toks[k].replace('«', '').replace('»', ''), pub or not is_mod, meta, al)); k += 1
    return is_mod, imports

# ---- workspace
packages = [p['name'] for p in json.load(open(f'{REPO}/lake-manifest.json')).get('packages', [])]
where = {}
for p in packages:
    d = f'{REPO}/.lake/packages/{p}'; lib = f'{d}/.lake/build/lib/lean'
    for root, _, fs in os.walk(lib):
        for f in fs:
            if f.endswith('.olean'):
                rel = os.path.relpath(os.path.join(root, f), lib)[:-6]
                src = next((c for c in (f'{d}/{rel}.lean', f'{d}/src/{rel}.lean') if os.path.exists(c)), None)
                where.setdefault(rel.replace('/', '.'), (p, f'{lib}/{rel}', src))
PLIB = f'{REPO}/.lake/build/lib/lean'; project = {}
for root, _, fs in os.walk(SRC):
    if '/.lake' in root: continue
    for f in fs:
        if f.endswith('.lean'):
            rel = os.path.relpath(os.path.join(root, f), SRC)[:-5]; m = rel.replace('/', '.')
            if lib_of(m) is not None and os.path.exists(f'{PLIB}/{rel}.olean'):
                project[m] = rel; where[m] = (PKG, f'{PLIB}/{rel}', os.path.join(root, f))
print(f'workspace: {len(project)} built project modules, {len(where) - len(project)} dependency modules', flush=True)

def lean_trace():
    githash = subprocess.run([LEAN, '--githash'], capture_output=True, text=True, check=True).stdout.strip()
    for m, (p, base, _) in where.items():
        if p != PKG and os.path.exists(base + '.trace'):
            for k, v in json.load(open(base + '.trace')).get('inputs', []):
                if k.startswith('Lean ') and githash in k: return int(v, 16)
    sys.exit('no dependency trace records this Lean commit; rebuild or re-fetch the dependencies with this toolchain')
LEAN_HASH = lean_trace()

def art_hash(path, trust_sidecar):
    if trust_sidecar:
        try:
            s = open(path + '.hash').read().strip()
            if len(s) == 16: return int(s, 16)
        except OSError: pass
    with open(path, 'rb') as f: return of_hashable(bhash(f.read()))

SUFFIXES = ('.olean', '.olean.server', '.olean.private', '.ilean', '.ir.sig', '.ir')
def load_module(m):
    p, base, src = where[m]
    if src is None: return m, None
    is_mod, imports = parse_header(src); own = p == PKG; h = {}
    for suf in (SUFFIXES if is_mod else ('.olean', '.ilean')):
        if not os.path.exists(base + suf): return m, None
        h[suf] = art_hash(base + suf, not own)
    out = {'is_mod': is_mod, 'imports': imports, 'h': h}
    if own:
        c = f'{REPO}/.lake/build/ir/{project[m]}.c'
        out['c'] = art_hash(c, False) if os.path.exists(c) else None; out['c_path'] = c
        raw = open(src, 'rb').read().replace(b'\r\n', b'\n'); out['src'] = of_hashable(bhash(raw))
    return m, out
with cf.ThreadPoolExecutor(J) as ex: data = dict(ex.map(load_module, list(where), chunksize=64))
print('hashed outputs and sources', flush=True)

# ---- import traces, exactly as ModuleImportInfo.addImport folds them
Export = collections.namedtuple('Export', 'trans meta all legacy irsig arts metaArts irArts allArts')
exports = {}; unavailable = set()
def info_for(m):
    d = data[m]; trace = trans = metaT = allT = legacy = irTr = irTrans = NIL; non_mod = not d['is_mod']
    for name, public, is_meta, imp_all in d['imports']:
        if name not in where: continue
        e = exports.get(name)
        if e is None: return None
        if non_mod: trace = mix(mix(trace, e.legacy), e.allArts)
        elif imp_all: trace = mix(mix(trace, e.all), e.allArts)
        elif is_meta: trace = mix(mix(trace, e.meta), e.metaArts)
        else: trace = mix(mix(trace, e.trans), e.arts)
        legacy = mix(mix(legacy, e.legacy), e.allArts)
        if imp_all: allT = mix(mix(allT, e.all), e.allArts)
        elif is_meta: allT = mix(mix(allT, e.meta), e.metaArts)
        else: allT = mix(mix(allT, e.trans), e.arts)
        metaT = mix(mix(metaT, e.meta), e.metaArts)
        if non_mod or imp_all: irTr = mix(mix(irTr, e.all), e.allArts)
        else: irTr = mix(mix(irTr, e.irsig), e.irArts)
        if public:
            if is_meta: trans = mix(mix(trans, e.meta), e.metaArts)
            else: trans = mix(mix(trans, e.trans), e.arts)
            irTrans = mix(mix(irTrans, e.irsig), e.irArts)
    return trace, trans, metaT, allT, legacy, irTrans
def make_export(m, r):
    d = data[m]; h = d['h']; _, trans, metaT, allT, legacy, irTrans = r; ol = mix(NIL, h['.olean'])
    if d['is_mod']:
        ir_arts = mix(ol, h['.ir.sig']); meta = mix(ir_arts, h['.ir'])
        al = mix(mix(mix(mix(ol, h['.olean.server']), h['.olean.private']), h['.ir.sig']), h['.ir'])
    else: ir_arts = meta = al = ol
    return Export(trans, metaT, allT, legacy, irTrans, ol, meta, ir_arts, al)
def dep_hash(m, import_trace):
    l = lib_of(m); d = data[m]
    deps = mix(mix(NIL, l['extra']), import_trace)
    libs = NIL
    for _ in range(4): libs = mix(libs, NIL)
    t = mix(mix(NIL, deps), libs); t = mix(t, LEAN_HASH); t = mix(t, d['src']); t = mix(t, l['opts_hash'])
    t = mix(t, of_hashable(11 if d['is_mod'] else 13)); t = mix(t, of_hashable(name_hash(m)))
    t = mix(t, of_hashable(mix(shash(PKG), 13))); t = mix(t, l['args_hash'])
    return t

# iterative topological walk over everything
state = {}; order = []
for root in where:
    if root in state: continue
    stack = [(root, 0)]; state[root] = 1
    while stack:
        m, i = stack.pop(); imps = data[m]['imports'] if data.get(m) else []
        while i < len(imps) and (imps[i][0] not in where or imps[i][0] in state): i += 1
        if i < len(imps):
            stack.append((m, i + 1)); state[imps[i][0]] = 1; stack.append((imps[i][0], 0))
        else: order.append(m)
result = {}
for m in order:
    if data.get(m) is None: continue
    r = info_for(m)
    if r is None: unavailable.add(m); continue
    exports[m] = make_export(m, r)
    if m in project: result[m] = dep_hash(m, r[0])
print(f'computed {len(result)} module traces; {len(unavailable)} modules wait on an unbuilt import', flush=True)

def outputs_json(m):
    d = data[m]; h = d['h']; x = lambda suf: f'{hex16(h[suf])}{suf}'
    o = {'m': d['is_mod'], 'o': [x('.olean')] + ([x('.olean.server'), x('.olean.private')] if d['is_mod'] else []), 'i': x('.ilean')}
    if d['is_mod']: o['rs'] = x('.ir.sig'); o['r'] = x('.ir')
    if d.get('c') is not None: o['c'] = f"{hex16(d['c'])}.c"
    return o
if CHECK:
    same = bad = out_bad = absent = 0; ex = []
    for m, v in result.items():
        try: t = json.load(open(f'{PLIB}/{project[m]}.trace'))
        except OSError: absent += 1; continue
        if t['depHash'] == hex16(v): same += 1
        else:
            bad += 1
            if len(ex) < 5: ex.append((m, t['depHash'], hex16(v)))
        if t.get('outputs') != outputs_json(m): out_bad += 1
    print(f'CHECK depHash equal {same}, different {bad}, outputs different {out_bad}, no real trace {absent}')
    for x in ex: print('  ', x)
    if ex and '--explain' in sys.argv:
        def tree(v):
            if isinstance(v, str): return int(v, 16)
            h = NIL
            for _, c in v: h = mix(h, tree(c))
            return h
        m = ex[0][0]; t = json.load(open(f'{PLIB}/{project[m]}.trace')); l = lib_of(m); d = data[m]; real = dict(t['inputs'])
        print('real tree folds to depHash:', hex16(tree(t['inputs'])) == t['depHash'])
        r = info_for(m); mine = {'deps': mix(mix(NIL, l['extra']), r[0]), 'options': l['opts_hash']}
        for k, v in t['inputs']:
            ours = mine.get(k)
            if k.startswith('Lean '): ours = LEAN_HASH
            elif k.endswith('.lean'): ours = d['src']
            elif k.startswith('isModule'): ours = of_hashable(11 if d['is_mod'] else 13)
            elif k.startswith('Module.name'): ours = of_hashable(name_hash(m))
            elif k.startswith('Package.id'): ours = of_hashable(mix(shash(PKG), 13))
            elif k.startswith('Module.leanArgs'): ours = l['args_hash']
            elif k == 'libs':
                ours = NIL
                for _ in range(4): ours = mix(ours, NIL)
            print(f'  {k[:28]:28} real {hex16(tree(v))} ours {hex16(ours) if ours is not None else None} {"OK" if ours == tree(v) else "DIFF"}')
        rd = dict(real['deps']); print('  extraDep', hex16(tree(rd[[k for k in rd if k.endswith('extraDep')][0]])), hex16(l['extra']), ' imports', hex16(tree(rd['imports'])), hex16(r[0]))
        rim = rd['imports']; shown = 0; i = 0
        for name, public, is_meta, imp_all in d['imports']:
            if name not in where: continue
            e = exports[name]; a, b = rim[i], rim[i + 1]; i += 2
            want = (e.all, e.allArts) if imp_all else (e.meta, e.metaArts) if is_meta else (e.trans, e.arts)
            if (int(a[1], 16), int(b[1], 16)) != want and shown < 4:
                shown += 1; print('  import', name[-40:], 'pub', public, 'meta', is_meta, 'all', imp_all, '| real', a[0][-26:], a[1], b[1], '| ours', hex16(want[0]), hex16(want[1]))
        print('  import entries real', len(rim), 'ours', i)
    sys.exit(1 if bad or out_bad else 0)

missing_c = 0
def write(m):
    d = data[m]; base = f'{PLIB}/{project[m]}'
    if d.get('c') is None: return 1
    for suf, v in d['h'].items(): open(base + suf + '.hash', 'w').write(hex16(v))
    open(d['c_path'] + '.hash', 'w').write(hex16(d['c']))
    tmp = base + '.trace.tmp'
    json.dump({'schemaVersion': '2025-09-10', 'depHash': hex16(result[m]), 'inputs': [], 'outputs': outputs_json(m), 'log': [], 'synthetic': False}, open(tmp, 'w'))
    os.replace(tmp, base + '.trace'); return 0
with cf.ThreadPoolExecutor(J) as ex: missing_c = sum(ex.map(write, list(result), chunksize=64))
print(f'wrote {len(result) - missing_c} Lake traces; {missing_c} modules have no .c file and got no trace', flush=True)
sys.exit(1 if missing_c or unavailable else 0)
