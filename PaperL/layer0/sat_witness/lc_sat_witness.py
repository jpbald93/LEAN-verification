#!/usr/bin/env python3
"""lc_sat.py -- layer-8 only (satisfiability), the job list enabled. Derived from lc_mod.py.

Step 1 (mutation). For every theorem/lemma, make small changes to its CONCLUSION
(flip a relation, negate an equality, bump a numeral, -1 -> 1, True <-> False)
and keep the original proof unchanged. A meaningful statement is "killed": Lean
must reject the proof. A mutant whose own proof still compiles is a SURVIVOR and
needs a human look (vacuous or weak statement, or an equivalent mutation).
Errors are attributed by line: only errors inside the mutated theorem count.

Step 2 (hypotheses).
 (a) Contradiction probe: try to prove False from the theorem's own hypotheses
     with automation (omega, decide, simp_all, norm_num, linarith, nlinarith,
     tauto). Success = RED FLAG: the theorem would be vacuously true. A control
     example with the same binders and goal True is compiled alongside; if the
     control fails the probe is marked invalid instead of passing silently.
 (b) Satisfiability certificate: build  example : exists <all binders>, True
     (section variables included, [Fact P] becomes (_ : Fact P)). A local model
     (untrusted) proposes a proof with concrete values; ONLY Lean decides.
     Compiles = the hypotheses are proven jointly satisfiable. The statement is
     built by this script, never by the model, so the model cannot weaken it.

Resumable: every result is appended to results.jsonl and skipped on restart.
Identical files (same sha256) are audited once and reused across repos.
"""
import os, re, sys, json, hashlib, subprocess, time, threading, bisect, urllib.request
from concurrent.futures import ThreadPoolExecutor

HOME = os.path.expanduser('~')
ROOT = HOME
OUT = os.path.join(HOME, 'leancheck', 'out', os.environ.get('SAT_OUT', 'paperL_sat'))
WORK = os.path.join(OUT, 'work')
RES = os.path.join(OUT, 'results.jsonl')
LAKE = os.path.join(HOME, '.elan', 'bin', 'lake')
WORKERS = int(os.environ.get('WORKERS', '8'))
CTIMEOUT = int(os.environ.get('CTIMEOUT', '900'))
MODEL = os.environ.get('MODEL', 'qwen3:32b')
TRIES = int(os.environ.get('TRIES', '3'))
LLM_TIMEOUT = int(os.environ.get('LLM_TIMEOUT', '600'))
SAT_BUDGET = int(os.environ.get('SAT_BUDGET', '72000'))  # wall-clock cap for the whole layer, seconds
REPOS = [(r, '.') for r in ('paperL_jack',)]
LIMIT = [x for x in os.environ.get('LIMIT', '').split(',') if x]

os.makedirs(WORK, exist_ok=True)
lock = threading.Lock()
done = {}
if os.path.exists(RES):
    for ln in open(RES, encoding='utf-8'):
        try:
            r = json.loads(ln); done[r['key']] = r
        except Exception:
            pass


def log(*a):
    with lock:
        print(time.strftime('%Y-%m-%d %H:%M:%S'), *a, flush=True)


def record(r):
    with lock:
        done[r['key']] = r
        with open(RES, 'a', encoding='utf-8') as f:
            f.write(json.dumps(r, ensure_ascii=False) + '\n')


OPEN, CLOSE = '([{⦃⟨', ')]}⦄⟩'
DECL = re.compile(r'^([ \t]*)(?:@\[[^\]\n]*\][ \t]*\n?[ \t]*)?(?:(?:private|protected|noncomputable)[ \t]+)*'
                  r'(theorem|lemma)[ \t]+([^\s(\[{⦃:]+)', re.M)
ERR = re.compile(r'\.lean:(\d+):(\d+): error')
HEART = re.compile(r'maximum number of heartbeats|\(deterministic\) timeout|maxRecDepth')


def comment_spans(text):
    """[start, end) spans of Lean comments (`--` line comments and nested `/- ... -/` block/doc
    comments), skipping string literals, so prose inside them is never read as a declaration."""
    spans, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); j = n if j < 0 else j
            spans.append((i, j)); i = j
        elif text.startswith('/-', i):
            j, depth = i + 2, 1
            while j < n and depth:
                if text.startswith('/-', j): depth += 1; j += 2
                elif text.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            spans.append((i, j)); i = j
        else:
            i += 1
    return spans


def in_spans(spans, off):
    k = bisect.bisect_right(spans, (off, float('inf'))) - 1
    return k >= 0 and spans[k][0] <= off < spans[k][1]
FORBID = ['sorry', 'admit', 'native_decide', 'sorryAx', 'axiom', 'unsafe', 'implemented_by',
          'macro', 'elab', '@[', 'opaque', 'extern']


def find_assign(s, st):
    d = 0
    for i in range(st, len(s) - 1):
        c = s[i]
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif c == ':' and s[i + 1] == '=' and d == 0: return i
    return -1


def top_colon(s):
    d = 0
    for i, c in enumerate(s):
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif c == ':' and d == 0 and (i + 1 >= len(s) or s[i + 1] != '='): return i
    return -1


WITNESS_TABLE = json.load(open(os.environ['WITNESS_TABLE'])) if os.environ.get('WITNESS_TABLE') else {}

def groups(b):
    gs, d, st = [], 0, None
    for i, c in enumerate(b):
        if c in OPEN:
            if d == 0: st = i
            d += 1
        elif c in CLOSE:
            d -= 1
            if d == 0 and st is not None:
                gs.append(b[st:i + 1]); st = None
    return gs


def convert(g):
    o, inner = g[0], g[1:-1].strip().replace('Type*', 'Type')
    if o == '[':
        if re.match(r"^[A-Za-z_][\w'₀-₉]*\s*:\s", inner):
            return '(' + inner + ')'
        return '(_ : ' + inner + ')'
    return '(' + inner + ')'


def gnames(g):
    if g[0] == '[':
        m = re.match(r"^\[\s*([A-Za-z_][\w'₀-₉]*)\s*:\s", g)
        return [m.group(1)] if m else []
    inner = g[1:-1]
    return inner.split(':')[0].split() if ':' in inner else inner.split()


TOK = re.compile(r"[A-Za-z_][\w'₀-₉!?]*")
HYPWORDS = ('≠', '=', '≤', '<', '≥', '>', '∣', '∧', '∨', '¬', '∈', '∉', '↔', '→', 'IsUnit', 'Prime',
            'Fact', 'Odd', 'Even', 'Squarefree', 'Coprime', 'IsPrimitiveRoot', 'Irreducible', 'Nonempty')


def has_hyp(gs):
    for g in gs:
        if g[0] == '[': return True
        ns = gnames(g)
        ty = g[1:-1].split(':', 1)[1] if ':' in g else ''
        if any(n.startswith('h') for n in ns) or any(w in ty for w in HYPWORDS): return True
    return False


SCOPE_OPEN = re.compile(r'^(?:noncomputable[ \t]+)?(?:section|namespace)\b')


def scoped_vgroups(lines, upto):
    """binder groups of the `variable` commands in scope at line index `upto`:
    section/namespace-scoped (dropped at the matching `end`), multi-line commands joined."""
    stack = [[]]
    k = 0
    while k < upto:
        ln = lines[k]; st = ln.strip()
        if ln[:1] not in (' ', '\t'):
            if SCOPE_OPEN.match(st):
                stack.append([])
            elif re.match(r'^end\b', st):
                if len(stack) > 1: stack.pop()
            elif re.match(r'^variable\b', st):
                body = st[len('variable'):]
                j = k + 1
                while j < upto and lines[j][:1] in (' ', '\t') and lines[j].strip():
                    body += ' ' + lines[j].strip(); j += 1
                stack[-1].append(body)
                k = j; continue
        k += 1
    gs, seen = [], set()
    for sc in stack:
        for body in sc:
            for g in groups(body):
                if g not in seen: seen.add(g); gs.append(g)
    return gs


def parse(text):
    lines = text.split('\n')
    starts = [0]
    for ln in lines[:-1]: starts.append(starts[-1] + len(ln) + 1)
    lno = lambda off: bisect.bisect_right(starts, off)  # 1-based
    decls = []
    cspans = comment_spans(text)
    for m in DECL.finditer(text):
        if in_spans(cspans, m.start(2)): continue  # keyword inside a comment/docstring: prose, not code
        indent = len(m.group(1).expandtabs())
        name, ne = m.group(3), m.end()
        a = find_assign(text, ne)
        sig = text[ne:a] if a >= 0 else ''
        c = top_colon(sig) if a >= 0 else -1
        if a < 0 or c < 0:
            decls.append(dict(name=name, unparsed=True)); continue
        i0, ia = lno(m.start()) - 1, lno(a) - 1
        end = len(lines) - 1
        for k in range(ia + 1, len(lines)):
            ln = lines[k]
            if ln.strip() == '': continue
            if len(ln) - len(ln.lstrip()) <= indent:
                end = k - 1; break
        while end > ia and lines[end].strip() == '': end -= 1
        vgroups = scoped_vgroups(lines, i0)
        # preamble: doc comment, @[..] lines and `... in` command prefixes directly above the decl
        p0, k, inpre = i0, i0 - 1, []
        while k >= 0:
            ln = lines[k].strip()
            if ln.endswith('-/'):
                j = k
                while j >= 0 and '/-' not in lines[j]: j -= 1
                if j < 0: break
                p0 = k = j; k -= 1; continue
            if re.match(r'^(attribute\b|open\b|set_option\b|include\b|omit\b).*\bin$', ln):
                inpre.insert(0, lines[k]); p0 = k; k -= 1; continue
            if ln.startswith('@['):
                p0 = k; k -= 1; continue
            break
        decls.append(dict(name=name, l0=i0 + 1, p0=p0 + 1, l1=end + 1, ins=end + 1, cs=ne + c + 1, ce=a,
                          binders=sig[:c], conclusion=sig[c + 1:], vgroups=vgroups,
                          inpre='\n'.join(inpre)))
    return decls


def lean_run(pd, text, tag):
    p = os.path.join(WORK, tag + '.lean')
    with open(p, 'w', encoding='utf-8') as f: f.write(text)
    t0 = time.time()
    try:
        r = subprocess.run([LAKE, 'env', 'lean', p], cwd=pd, capture_output=True, text=True, timeout=CTIMEOUT)
        out, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        out, rc = 'TIMEOUT', 'timeout'
    finally:
        try: os.remove(p)
        except OSError: pass
    return rc, [int(x.group(1)) for x in ERR.finditer(out)], out, round(time.time() - t0, 1)


def first_err(out, lo=None, hi=None):
    L = out.splitlines()
    for i, ln in enumerate(L):
        m = ERR.search(ln)
        if m and (lo is None or lo <= int(m.group(1)) <= hi):
            return '\n'.join(L[i:i + 12])[:1500]
    return ''


def insert_after(text, idx, block):
    lines = text.split('\n')
    add = ['', *block.split('\n')]
    new = lines[:idx] + add + lines[idx:]
    return '\n'.join(new), idx + 2, idx + len(add)   # 1-based range of the inserted block


OPS = [('eq->ne', r'(?<![:=<>≠!])=(?![=>])', '≠'), ('ne->eq', r'≠', '='), ('le->gt', r'≤', '>'),
       ('ge->lt', r'≥', '<'), ('lt->ge', r'(?<![<\-])<(?![;=|>\-])', '≥'),
       ('gt->le', r'(?<![\-=>|<])>(?![=>])', '≤'), ('neg1->1', r'-[ ]?1(?![\d.])', '1'),
       ('True->False', r'\bTrue\b', 'False'), ('False->True', r'\bFalse\b', 'True')]
LIT = r"(?<![\w.'])(\d+)(?![\w.])"


def mutants(conc):
    ops, lits = [], []
    for nm, pat, rep in OPS:
        for m in re.finditer(pat, conc):
            ops.append((f'{nm}@{m.start()}', conc[:m.start()] + rep + conc[m.end():]))
    for m in re.finditer(LIT, conc):
        n = int(m.group(1))
        lits.append((f'lit{n}->{n + 1}@{m.start()}', conc[:m.start()] + str(n + 1) + conc[m.end():]))
    return (ops[:6] + lits[:3])[:8]


# ---------------- jobs ----------------
def job_baseline(pd, fsha, text):
    key = f'base|{fsha}'
    if key in done: return done[key]['status'] == 'ok'
    rc, errs, out, dt = lean_run(pd, text, 'b' + fsha[:16])
    st = 'ok' if rc == 0 and not errs else 'BASELINE-FAIL'
    record(dict(key=key, step='baseline', fsha=fsha, status=st, secs=dt, err=first_err(out)))
    return st == 'ok'


def job_mut(pd, fsha, text, d, mid, newc):
    key = f'mut|{fsha}|{d["name"]}|{mid}'
    if key in done: return
    t = text[:d['cs']] + newc + text[d['ce']:]
    rc, errs, out, dt = lean_run(pd, t, hashlib.md5(key.encode()).hexdigest())
    lo = d.get('p0', d['l0'])            # errors on the doc comment / decl head count (heartbeat errors land there)
    mine = [e for e in errs if lo <= e <= d['l1']]
    why = ''
    if rc == 'timeout':
        st, why = 'killed-timeout', 'wall-clock timeout %ds' % CTIMEOUT
    elif mine:
        e1 = first_err(out, lo, d['l1'])
        if HEART.search(e1): st, why = 'killed-timeout', 'heartbeat limit'
        else: st = 'killed'
    elif rc != 0 and not errs:
        st, why = 'error-unattributed', 'exit %s with no error line' % rc
    else:
        # the mutated theorem itself compiled; errors (if any) are in later declarations that use it
        st = 'SURVIVED'
        if errs: why = 'own proof compiled; downstream errors at lines %s' % sorted(set(errs))[:5]
    record(dict(key=key, step='mut', fsha=fsha, thm=d['name'], mut=mid, status=st, why=why, rc=rc,
                original=d['conclusion'].strip()[:500], mutated=newc.strip()[:500], secs=dt,
                err=first_err(out, lo, d['l1'])[:400]))


PROBE = ('  first\n  | omega\n  | decide\n  | (simp_all; done)\n  | (norm_num at *; done)\n'
         '  | linarith\n  | nlinarith\n  | tauto')


def job_contra(pd, fsha, text, d):
    key = f'contra|{fsha}|{d["name"]}'
    if key in done: return
    gs = groups(d['binders'])
    if not has_hyp(gs):
        record(dict(key=key, step='contra', fsha=fsha, thm=d['name'], status='no-hyp')); return
    b = d['binders'].rstrip()
    ctl = 'example' + b + ' : True := trivial'
    prb = 'example' + b + ' : False := by\n' + PROBE
    t, c0, c1 = insert_after(text, d['ins'], ctl)
    t, p0, p1 = insert_after(t, c1, prb)
    rc, errs, out, dt = lean_run(pd, t, hashlib.md5(key.encode()).hexdigest())
    if rc == 'timeout': st = 'timeout'
    elif any(c0 <= e <= c1 for e in errs): st = 'probe-invalid'
    elif any(p0 <= e <= p1 for e in errs): st = 'ok'
    elif rc != 0: st = 'error-unattributed'   # e.g. OOM kill (exit 137): not evidence of contradiction
    else: st = 'CONTRADICTORY'
    record(dict(key=key, step='contra', fsha=fsha, thm=d['name'], status=st, secs=dt,
                err=first_err(out, c0, c1)[:400] if st == 'probe-invalid' else ''))


def sat_groups(d):
    """binder groups of the satisfiability statement: the in-scope section variables the theorem
    uses (instance groups follow the variables they mention), then the theorem's own binders."""
    gs = groups(d['binders'])
    used = set(TOK.findall(d['binders'] + ' ' + d['conclusion']))
    vg, inc = d['vgroups'], set()
    changed = True
    while changed:
        changed = False
        for i, g in enumerate(vg):
            if i in inc: continue
            if g[0] == '[':
                deps = [x for x in TOK.findall(g) if any(x in gnames(h) for h in vg if h[0] != '[')]
                if deps and all(any(x in gnames(vg[j]) for j in inc) for x in deps):
                    inc.add(i); changed = True
            elif any(n in used for n in gnames(g)):
                inc.add(i); changed = True
                used |= set(TOK.findall(g))   # e.g. (o : Orientation ℝ V (Fin 2)) pulls in V
    return [vg[i] for i in sorted(inc)] + gs, gs


SATPROP = re.compile(r'[≤≥<>≠=∈∉∧∨¬∣↔∀∃]|\b(?:IsUnit|Prime|Fact|Odd|Even|Squarefree|Coprime|IsPrimitiveRoot|'
                     r'Irreducible|Nonempty|Collinear|IsCollinear|Cospherical|Concyclic|Function\.Injective)\b')


def slot_kinds(allg):
    """one slot per bound name, in order: (name, kind, type) with kind in type|inst|prop|data."""
    out = []
    for g in allg:
        cg = convert(g)
        inner = cg[1:-1]
        if ':' not in inner: continue
        nm, ty = inner.split(':', 1); ty = ty.strip(); names = nm.split()
        if g[0] == '[' or names == ['_']: kind = 'inst'
        elif re.match(r'^(Type|Sort)\b', ty): kind = 'type'
        elif SATPROP.search(ty) or ty == 'Prop': kind = 'prop'
        else: kind = 'data'
        for n in names: out.append((n, kind, ty))
    return out


def sat_stmt(d):
    allg, gs = sat_groups(d)
    if not allg: return 'True', gs, []
    return '∃ ' + ' '.join(convert(g) for g in allg) + ', True', gs, slot_kinds(allg)


def clean_llm(s):
    s = re.sub(r'<think>.*?</think>', '', s, flags=re.S).strip()
    s = re.sub(r'^```[a-zA-Z]*\n?', '', s); s = re.sub(r'\n?```\s*$', '', s).strip()
    if s.startswith('by\n') or s == 'by': s = s[2:].lstrip('\n')
    return s


def llm(messages):
    body = json.dumps(dict(model=MODEL, messages=messages, stream=False, think=False,
                           options=dict(temperature=0.3, num_ctx=16384))).encode()
    req = urllib.request.Request('http://localhost:11434/api/chat', data=body,
                                 headers={'Content-Type': 'application/json'})
    with urllib.request.urlopen(req, timeout=1800) as r:
        return json.loads(r.read())['message']['content']


DEFNAME = re.compile(r'^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:noncomputable|private|protected)[ \t]+)*'
                     r'(?:def|abbrev)[ \t]+([A-Za-z_][\w\'₀-₉]*)', re.M)


def repo_defs(pd, text, seen=None):
    """def/abbrev names from the repo-local modules this file (transitively) imports; names from
    modules that are NOT imported would be unknown identifiers and poison every simp alternative."""
    seen = set() if seen is None else seen
    names = []
    for m in re.finditer(r'^import\s+(\S+)', text, re.M):
        fp = os.path.join(pd, *m.group(1).split('.')) + '.lean'
        if fp in seen or not os.path.exists(fp): continue
        seen.add(fp)
        t = open(fp, encoding='utf-8').read()
        names += repo_defs(pd, t, seen) + DEFNAME.findall(t)
    return names


def auto_tac(text, d, pd=None):
    """deterministic closing tactic for a hypothesis slot (the repo's local defs are unfolded)."""
    upto = '\n'.join(text.split('\n')[:d['ins']])
    defs = list(dict.fromkeys(DEFNAME.findall(upto) + (repo_defs(pd, text) if pd else [])))[-30:]
    ds = ', '.join(defs)
    sl = (', ' + ds) if ds else ''
    o = lambda extra: ' [%s]' % ', '.join([x for x in extra + [ds] if x]) if (extra or ds) else ''
    fin3 = ('funext_iff, Fin.forall_fin_succ, cross_apply, Matrix.vec3_dotProduct, Fin.sum_univ_three, '
            'Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons')
    alts = ['decide', 'rfl', 'exact ⟨by norm_num⟩', 'exact ⟨by simp⟩', 'positivity',
            '(norm_num%s; done)' % o([]), '(simp%s; done)' % o([]),
            '(norm_num%s; done)' % o(['Complex.ext_iff']), '(simp%s; done)' % o(['Complex.ext_iff']),
            '(norm_num%s; done)' % o(['Prod.ext_iff']), '(norm_num%s; done)' % o([fin3]),
            '(ring_nf; done)', '(simp%s; ring_nf; done)' % o([]), '(norm_num%s; ring_nf; done)' % o(['Complex.ext_iff']),
            # last alternative fails with the residual goal, which is the useful feedback for the model
            '(norm_num%s)' % o(['Complex.ext_iff'])]
    return 'first | ' + ' | '.join(alts)


INSTTAC = 'first | exact inferInstance | exact ⟨by simp⟩ | exact ⟨by norm_num⟩ | exact ⟨by decide⟩'


def build_term(slots, wit, auto):
    """anonymous-constructor certificate. `wit` maps slot name -> model term/tactic (may be partial)."""
    parts = []
    for i, (n, kind, ty) in enumerate(slots):
        w = (wit.get(n) if isinstance(wit, dict) else None) or ''
        w = ' '.join(str(w).split())
        if kind in ('prop', 'inst'):
            base = auto if kind == 'prop' else INSTTAC + ' | ' + auto
            if w and w.lower() != 'auto':
                tac = (w[3:] + '; done') if w.startswith('by ') else 'exact (%s)' % w   # partial progress must not win `first`
                parts.append('(by first | (%s) | %s)' % (tac, base))
            else:
                parts.append('(by %s)' % base)
        elif kind == 'type':
            later = ' '.join(t for (_, k2, t) in slots[i + 1:] if k2 == 'inst')
            dflt = 'ℂ' if re.search(r'ℝ|Real|Normed|Inner', later) else 'ℚ'
            # a model "witness" that is just a bound/section name (K, V, ...) is not a concrete type
            if w and (w in {x[0] for x in slots} or re.fullmatch(r"[A-Z][\w'₀-₉]*", w)):
                w = ''
            if dflt == 'ℂ': w = ''   # real inner-product/normed setting: ℂ (dim 2, has an orientation) always
            parts.append('(%s)' % (w or dflt))
        else:
            dflt = 'exact Complex.orientation | exact %d | exact (fun _ => %d) | exact default' % (i + 1, i + 1)
            # a model term that does not elaborate falls back to the deterministic default
            parts.append('(by first | exact (%s) | %s)' % (w, dflt) if w else '(by first | %s)' % dflt)
    return 'exact ⟨' + ', '.join(parts + ['trivial']) + '⟩' if parts else 'trivial'


def det_witnesses(slots):
    """a few deterministic witness patterns (bounded: <= 3 extra Lean runs per statement)."""
    tyof = {}
    for n, k, t in slots:
        if k == 'type': tyof[n] = 'ℂ' if any(k2 == 'inst' and re.search(r'ℝ|Normed|Inner', t2) for _, k2, t2 in slots) else 'ℚ'
    runs, cur, prev = [], [], None
    for n, k, t in slots:
        if k == 'data' and t == prev: cur.append(n)
        else:
            if len(cur) >= 2: runs.append((prev, cur))
            cur, prev = ([n], t) if k == 'data' else ([], None)
    if len(cur) >= 2: runs.append((prev, cur))
    cands = []
    for gen in ('sum0', 'sum0I', 'distinct'):
        w = {}
        for t, ns in runs:
            cplx = t.strip() == 'ℂ' or tyof.get(t.strip()) == 'ℂ'
            if gen == 'sum0':
                vals = [str(j + 1) for j in range(len(ns) - 1)]
            elif gen == 'sum0I':
                if not cplx: continue
                vals = ['1', 'Complex.I'] + ['%d' % (j + 2) for j in range(len(ns) - 3)]
                vals = vals[:len(ns) - 1]
            else:
                vals = (['0', '1', 'Complex.I', '2', '3'] if cplx else [str(j) for j in range(len(ns))])[:len(ns)]
                for n, v in zip(ns, vals): w[n] = v
                continue
            for n, v in zip(ns, vals): w[n] = v
            w[ns[-1]] = '-(%s)' % ' + '.join('(%s)' % v for v in vals)
        if w and w not in cands: cands.append(w)
    return cands


def llm_json(messages):
    # no `format='json'`: with qwen3 on this ollama it returns empty/degenerate replies (done=false)
    body = json.dumps(dict(model=MODEL, messages=messages, stream=False, think=False,
                           options=dict(temperature=0.3, num_ctx=16384, num_predict=800))).encode()
    req = urllib.request.Request('http://localhost:11434/api/chat', data=body,
                                 headers={'Content-Type': 'application/json'})
    with urllib.request.urlopen(req, timeout=LLM_TIMEOUT) as r:
        resp = json.loads(r.read())
    txt = clean_llm(resp.get('message', {}).get('content', ''))
    if not resp.get('done', True) or not txt.strip('/ \n'):
        raise ValueError('empty/incomplete model reply (done=%s)' % resp.get('done'))
    m = re.search(r'\{.*\}', txt, re.S)
    if not m: raise ValueError('no JSON in model reply: %r' % txt[:200])
    return json.loads(m.group(0))


SAT_T0 = [time.time()]


def job_sat(pd, fsha, text, d):
    key = f'sat|{fsha}|{d["name"]}'
    if key in done and done[key]['status'] != 'llm-error': return
    stmt, gs, slots = sat_stmt(d)
    nhyp = sum(1 for s in slots if s[1] == 'prop')          # propositional hypotheses only
    kind = 'closed' if not slots else ('hyp-free' if nhyp == 0 else 'hyps')
    pre = (d.get('inpre') + '\n') if d.get('inpre') else ''
    head = pre + 'example : ' + stmt + ' := by\n'
    base = dict(key=key, step='sat', fsha=fsha, thm=d['name'], stmt=stmt, kind=kind, nslots=len(slots), nhyp=nhyp)
    t, e0, e1 = insert_after(text, d['ins'], head + '  sorry')
    rc, errs, out, dt = lean_run(pd, t, hashlib.md5((key + 'ctl').encode()).hexdigest())
    if rc == 'timeout' or any(e0 <= e <= e1 for e in errs):
        record(dict(base, status='stmt-invalid', err=('TIMEOUT' if rc == 'timeout' else first_err(out, e0, e1))[:600])); return
    auto = auto_tac(text, d, pd)

    def attempt(proof, tag):
        bad = [w for w in FORBID if w in proof]
        if bad: return False, 'forbidden tokens %s' % bad
        body = '\n'.join('  ' + x for x in proof.split('\n'))
        t, a0, a1 = insert_after(text, d['ins'], head + body)
        rc, errs, out, dt = lean_run(pd, t, hashlib.md5((key + tag).encode()).hexdigest())
        if rc == 'timeout': return False, 'timeout'
        if not any(a0 <= e <= a1 for e in errs) and rc == 0: return True, ''
        if not any(a0 <= e <= a1 for e in errs):
            return False, 'exit %s: %s' % (rc, out[-400:])
        return False, first_err(out, a0, a1) or out[-1200:]

    tbl = WITNESS_TABLE.get(d['name']) if WITNESS_TABLE else None
    if tbl:
        pr = build_term(slots, tbl, auto)
        ok, errt = attempt(pr, 'tbl')
        if ok:
            record(dict(base, status='SAT-CERTIFIED', proof=pr, attempts=0, by='curated-witness')); return
        if os.environ.get('TABLE_ONLY'):
            record(dict(base, status='unresolved', history=['table: ' + errt[:400]])); return
    # pass 0: deterministic witnesses (no model)
    det = build_term(slots, {}, auto)
    ok, err0 = attempt(det, 'det')
    if ok:
        record(dict(base, status='SAT-CERTIFIED', proof=det, attempts=0, by='deterministic')); return
    for j, w in enumerate(det_witnesses(slots)):
        pr = build_term(slots, w, auto)
        ok, _e = attempt(pr, 'det%d' % j)
        if ok:
            record(dict(base, status='SAT-CERTIFIED', proof=pr, attempts=0, by='deterministic-pattern')); return
    if not slots:
        record(dict(base, status='unresolved', history=[err0[:300]])); return
    lines = text.split('\n')
    ctx = '\n'.join(lines[:12]) + '\n...\n' + '\n'.join(lines[:d['ins']])[-3500:]
    slot_txt = '\n'.join('  %s : %s   [%s]' % s for s in slots)
    msgs = [dict(role='system', content='You pick concrete witnesses for Lean 4 + Mathlib existential statements. '
                                        'Reply with a single JSON object only.'),
            dict(role='user', content=(
                f'FILE CONTEXT (truncated; the example is placed right after `{d["name"]}`, so its definitions,'
                f' namespaces and opens are in scope):\n{ctx}\n\nGOAL (built by a script, do not change it):\n{head}\n'
                f'Bound names in order, with kind (type = a concrete type such as ℚ, ℝ, ℂ; data = a concrete value;'
                f' prop = a hypothesis to prove; inst = a typeclass instance):\n{slot_txt}\n\n'
                'Choose values that make EVERY hypothesis true. Reply with JSON {"witness": {name: string}}. For type/data'
                ' give a Lean term (e.g. "ℚ", "(3 : ℂ)", "Complex.I", "![1, 0, 0]", "((0 : ℚ), (1 : ℚ))"). For prop/inst give'
                ' either "auto" (the script tries decide/norm_num/simp with local definitions unfolded) or a one-line'
                ' tactic starting with "by ". No sorry/admit/native_decide. Hints: a real inner product space (of dimension 2)'
                ' can be ℂ, its orientation `Complex.orientation`; a field can be ℚ; a vector in Fin 3 → K can be'
                ' `![1, 0, 0]`.'))]
    hist = [('det: ' + err0)[:300]]
    for k in range(1, TRIES + 1):
        if time.time() - SAT_T0[0] > SAT_BUDGET:
            hist.append('layer-8 wall-clock budget %ds exhausted' % SAT_BUDGET); break
        try:
            j = llm_json(msgs)
            wit = j.get('witness', j) if isinstance(j, dict) else {}
        except Exception as ex:
            hist.append(('llm: ' + str(ex))[:300]); wit = None
        if wit is None:
            if k == TRIES: break
            continue
        proof = build_term(slots, wit, auto)
        ok, err = attempt(proof, str(k))
        if ok:
            record(dict(base, status='SAT-CERTIFIED', proof=proof, attempts=k, by='model-witness')); return
        hist.append(err[:300])
        msgs += [dict(role='assistant', content=json.dumps(dict(witness=wit), ensure_ascii=False)),
                 dict(role='user', content='Lean rejected the certificate built from your witnesses:\n' + err[:1500] +
                      '\nReturn corrected JSON {"witness": {...}} only.')]
    record(dict(base, status='unresolved', history=hist))


# ---------------- layer 8b: link hand-written `*_sat` witnesses ----------------
# Layer 8 above only credits certificates it generates itself. A repo may also contain hand-written
# non-vacuity witnesses (`X_sat`). This step credits theorem X as SAT-BY-WITNESS, reported
# SEPARATELY from SAT-CERTIFIED and never altering a layer-8 record, only when ALL hold:
#   (a) the witness W is a theorem of the repo named `*_sat`, and it claims X: either W's name is
#       exactly X ++ "_sat" (route `name`), or W's docstring names X in backticks (route `doc`);
#   (b) Lean (not the regex) finds, in W's elaborated proof term (zeta/beta-reduced, following only
#       W's own auxiliary declarations, never other theorems), an application of X with at least
#       arity(X) arguments, all of them closed terms (no free/bound variables, no metavariables).
#       A closed full application of X instantiates every binder and discharges every hypothesis of
#       X at concrete data, which is itself a Lean-checked proof that X's hypotheses are jointly
#       satisfiable;
#   (c) W depends only on the standard axioms (propext, Classical.choice, Quot.sound);
#   (d) X resolves to exactly one audited declaration (by module + short name).
# Claims that fail (b)-(d) are recorded as `link-rejected` with the reason, never credited.
SATLINK_STD_AX = {'propext', 'Classical.choice', 'Quot.sound'}
SATLINK_PROBE = r'''

open Lean Meta in
run_meta do
  let env ← getEnv
  let mods := env.header.moduleNames
  let repoMods : Array String := #[%s]
  let mut wits : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if n.isInternal then continue
    unless n.toString.endsWith "_sat" do continue
    if ci matches .thmInfo _ then wits := wits.push n
  for w in wits do
    let ax ← collectAxioms w
    let doc := (← findDocString? env w).getD ""
    let mut work : Array Name := #[w]
    let mut seen : NameSet := {}
    let mut hits : Array Json := #[]
    for _ in [0:256] do
      if work.isEmpty then break
      let c := work.back!; work := work.pop
      if seen.contains c then continue
      seen := seen.insert c
      let some v := (← getConstInfo c).value? (allowOpaque := true) | continue
      let v ← zetaReduce v
      let v ← Core.transform v (post := fun e => return .done e.headBeta)
      let ref ← IO.mkRef (#[] : Array Expr)
      v.forEach fun e => do
        if e.isApp && e.getAppFn.isConst then ref.modify (·.push e)
        if let .const k _ := e then
          if k.isInternal && w.isPrefixOf k then ref.modify (·.push e)
      for e in (← ref.get) do
        if let .const k _ := e then
          if !seen.contains k then work := work.push k
          continue
        let f := e.getAppFn.constName!
        if f == w then continue
        let some fi := env.find? f | continue
        unless fi matches .thmInfo _ do continue
        let m := match env.getModuleIdxFor? f with
          | some i => (mods[i.toNat]!).toString
          | none => "<current>"
        unless m == "<current>" || repoMods.contains m do continue
        let args := e.getAppArgs
        let closed := args.all (fun a => !a.hasLooseBVars && !a.hasFVar && !a.hasMVar)
        let ar ← forallTelescope fi.type fun xs _ => pure xs.size
        hits := hits.push (Json.mkObj [("target", toJson f.toString), ("module", toJson m),
          ("nargs", toJson args.size), ("arity", toJson ar), ("closed", toJson closed)])
    IO.println ("SATLINK " ++ (Json.mkObj [("w", toJson w.toString), ("axioms", toJson (ax.map (·.toString))),
      ("doc", toJson doc), ("hits", Json.arr hits)]).compress)
'''


def modname(path_rel_pd):
    return '.'.join(os.path.splitext(path_rel_pd)[0].split(os.sep))


def job_satlink(files, repomap):
    """layer 8b: run the Lean probe on every file declaring a `*_sat` theorem, then link."""
    allmods = sorted({modname(rel) for fl in repomap.values() for rel, _, _ in fl})
    mod2f = {}
    for fl in repomap.values():
        for rel, fs, ns in fl: mod2f[modname(rel)] = (fs, set(ns))
    links, rejected = {}, []
    for fsha, f in files.items():
        if not any(d['name'].endswith('_sat') for d in f['decls']): continue
        key = 'satlinkrun|' + hashlib.sha256((fsha + '|' + '|'.join(sorted(files))).encode()).hexdigest()  # any repo file change re-probes
        if key in done and done[key]['status'] == 'ok':
            rows = done[key]['rows']
        else:
            probe = SATLINK_PROBE % ', '.join(json.dumps(m, ensure_ascii=False) for m in allmods)
            rc, errs, out, dt = lean_run(f['pd'], f['text'] + '\n' + probe, 'sl' + fsha[:16])
            rows = [json.loads(ln[8:]) for ln in out.splitlines() if ln.startswith('SATLINK ')]
            st = 'ok' if rc == 0 and not errs else 'probe-failed'
            record(dict(key=key, step='satlinkrun', fsha=fsha, status=st, secs=dt, rows=rows,
                        err='' if st == 'ok' else (first_err(out) or out[-600:])))
            if st != 'ok': log('satlink probe failed on', f['path']); continue
        fmod = None
        for m, (fs, _) in mod2f.items():
            if fs == fsha: fmod = m
        for row in rows:
            w = row['w']
            # relative (source-level, possibly dotted) name of W: the longest audited decl name of this
            # file that W's full Lean name ends with; e.g. `Morley.MorleyConfig.swap_sat` -> `MorleyConfig.swap_sat`
            wrel = [d['name'] for d in f['decls'] if w == d['name'] or w.endswith('.' + d['name'])]
            wshort = max(wrel, key=len) if wrel else w.split('.')[-1]
            claims = {}
            if wshort.endswith('_sat') and len(wshort) > 4: claims[wshort[:-4]] = 'name'
            for x in re.findall(r'`([^`\s]+)`', row.get('doc', '')):
                # longest dotted suffix of x that is an audited name (`MorleyConfig.swap`, not `swap`);
                # if none, the last component as before
                parts = x.split('.')
                sfx = [s for s in ('.'.join(parts[i:]) for i in range(len(parts)))
                       if any(s in ns for _, ns in mod2f.values())]
                claims.setdefault(sfx[0] if sfx else parts[-1], 'doc')
            badax = sorted(set(row.get('axioms', [])) - SATLINK_STD_AX)
            for x, route in claims.items():
                if x.endswith('_sat') or x == wshort: continue   # witnesses are not targets
                hs = [h for h in row['hits'] if h['target'] == x or h['target'].endswith('.' + x)]  # full dotted name
                why = None
                if badax: why = 'witness uses nonstandard axioms %s' % badax
                elif not hs: why = 'claimed but not applied in the proof term'
                tmods = {(fmod if h['module'] == '<current>' else h['module']) for h in hs}
                if not why and len(tmods) != 1: why = 'target name ambiguous across modules %s' % sorted(tmods)
                good = [h for h in hs if h['closed'] and h['nargs'] >= h['arity']]
                if not why and not good: why = 'no closed full application (hypotheses not discharged at concrete data)'
                tm = next(iter(tmods)) if tmods else None
                if not why and (tm not in mod2f or x not in mod2f[tm][1]): why = 'target is not an audited theorem'
                if why:
                    audited = any(x in ns for _, ns in mod2f.values())
                    if hs or (route == 'name' and audited):   # a `*_sat` name with no such theorem is no claim
                        rejected.append(dict(witness=w, target=x, route=route, why=why))
                    continue
                tfs = mod2f[tm][0]
                lk = f'satlink|{tfs}|{x}'
                if lk in links:
                    links[lk]['also'].append(w); continue
                links[lk] = dict(key=lk, step='satlink', fsha=tfs, thm=x, status='SAT-BY-WITNESS', witness=w,
                                 witness_file=f['path'], target_module=tm, route=route, also=[],
                                 app=dict(nargs=good[0]['nargs'], arity=good[0]['arity']))
    # one snapshot record per run (results.jsonl is append-only; the newest snapshot supersedes older ones)
    record(dict(key='satlinkset', step='satlinkset', status='ok', time=time.strftime('%Y-%m-%d %H:%M:%S'),
                links=list(links.values()), rejected=rejected))
    log(f'layer 8b: {len(links)} witness links, {len(rejected)} rejected claims')


# ---------------- driver ----------------
def collect(only):
    files, repomap = {}, {}
    for repo, ld in REPOS:
        if only and repo not in only: continue
        pd = os.path.join(ROOT, repo, ld)
        repomap[repo] = []
        for dp, dn, fn in os.walk(pd):
            dn[:] = [x for x in dn if x not in ('.lake', 'tests', '.git', 'scratch', 'tmp')]
            for f in sorted(fn):
                if not f.endswith('.lean'): continue
                p = os.path.join(dp, f)
                text = open(p, encoding='utf-8').read()
                fsha = hashlib.sha256(text.encode()).hexdigest()
                decls = parse(text)
                if not decls: continue
                repomap[repo].append((os.path.relpath(p, pd), fsha, [x['name'] for x in decls]))
                if fsha not in files:
                    files[fsha] = dict(pd=pd, text=text, decls=decls, path=os.path.relpath(p, ROOT))
    return files, repomap


def summary(files, repomap):
    R = list(done.values())
    lines = ['# Lean statement audit (jack)', '', f'Generated {time.strftime("%Y-%m-%d %H:%M %Z")}', '']
    tot = dict(thm=0, mut=0, killed=0, surv=0, tout=0, contra=0, sat=0, unres=0, nohyp=0, invalid=0)
    for repo, fl in repomap.items():
        thms = [(fs, n) for _, fs, ns in fl for n in ns]
        mr = [r for r in R if r['step'] == 'mut' and (r['fsha'], r['thm']) in set(thms)]
        cr = [r for r in R if r['step'] == 'contra' and (r['fsha'], r['thm']) in set(thms)]
        sr = [r for r in R if r['step'] == 'sat' and (r['fsha'], r['thm']) in set(thms)]
        c = lambda L, s: sum(1 for r in L if r['status'] == s)
        lines += [f'## {repo}', f'- theorems: {len(thms)}',
                  f'- step 1 mutants: {len(mr)} | killed {c(mr,"killed")} | killed-timeout {c(mr,"killed-timeout")} | SURVIVED {c(mr,"SURVIVED")} | unattributed {c(mr,"error-unattributed")}',
                  f'- step 2a contradiction probe: CONTRADICTORY {c(cr,"CONTRADICTORY")} | ok {c(cr,"ok")} | no-hyp {c(cr,"no-hyp")} | invalid {c(cr,"probe-invalid")} | timeout {c(cr,"timeout")}',
                  f'- step 2b satisfiable: CERTIFIED {c(sr,"SAT-CERTIFIED")} | unresolved {c(sr,"unresolved")} | stmt-invalid {c(sr,"stmt-invalid")} | llm-error {c(sr,"llm-error")}']
        LS = done.get('satlinkset', {})
        lr = [r for r in LS.get('links', []) if (r['fsha'], r['thm']) in set(thms)]
        srC = {r['thm'] for r in sr if r['status'] == 'SAT-CERTIFIED'}
        lines.append(f'- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): {len(lr)} '
                     f'[{sum(1 for r in lr if r["thm"] not in srC)} of them not certified by step 2b] | '
                     f'rejected claims {len(LS.get("rejected", []))}')
        for r in sorted(lr, key=lambda r: r['thm']):
            lines.append(f'  - SAT-BY-WITNESS `{r["thm"]}` <- `{r["witness"]}` (route {r["route"]}, closed application '
                         f'{r["app"]["nargs"]}/{r["app"]["arity"]} args)')
        for r in LS.get('rejected', []):
            if True:
                lines.append(f'  - witness claim REJECTED `{r["target"]}` <- `{r["witness"]}`: {r["why"]}')
        for r in mr:
            if r['status'] == 'killed-timeout':
                lines.append(f'  - killed by timeout `{r["thm"]}` [{r["mut"]}] ({r.get("why","")})')
            if r['status'] in ('SURVIVED', 'error-unattributed'):
                lines.append(f'  - {r["status"]} detail: {r.get("why","")}')
            if r['status'] == 'SURVIVED':
                lines.append(f'  - SURVIVOR `{r["thm"]}` [{r["mut"]}]: `{r["original"][:160]}` -> `{r["mutated"][:160]}`')
        for r in cr:
            if r['status'] == 'CONTRADICTORY': lines.append(f'  - RED FLAG contradictory hypotheses: `{r["thm"]}`')
        for r in sr:
            if r['status'] in ('unresolved', 'stmt-invalid') and not any(x['thm'] == r['thm'] and x['fsha'] == r['fsha'] for x in lr):
                lines.append(f'  - needs manual satisfiability check: `{r["thm"]}` ({r["status"]})')
        noth = [n for (fs, n) in thms if not any(r['step'] == 'mut' and r['fsha'] == fs and r['thm'] == n for r in R)]
        if noth: lines.append(f'  - no mutants generated (manual look): {", ".join(sorted(set(noth))[:40])}')
        lines.append('')
        tot['thm'] += len(thms); tot['mut'] += len(mr); tot['killed'] += c(mr, 'killed') + c(mr, 'killed-timeout'); tot['surv'] += c(mr, 'SURVIVED')
        tot['tout'] += c(mr, 'killed-timeout'); tot['contra'] += c(cr, 'CONTRADICTORY'); tot['sat'] += c(sr, 'SAT-CERTIFIED')
        tot['unres'] += c(sr, 'unresolved') + c(sr, 'stmt-invalid'); tot['invalid'] += c(cr, 'probe-invalid')
    bf = [r for r in R if r['step'] == 'baseline' and r['status'] != 'ok']
    lines[4:4] = ['## TOTAL (per repo, duplicates counted in each repo)', json.dumps(tot), '',
                  f'Baseline failures (files skipped): {len(bf)}', '']
    open(os.path.join(OUT, 'summary.md'), 'w', encoding='utf-8').write('\n'.join(lines) + '\n')


def main():
    only = set(sys.argv[1:])
    files, repomap = collect(only)
    nthm = sum(len(f['decls']) for f in files.values())
    log(f'unique files {len(files)}, unique theorems {nthm}, repos {len(repomap)}')
    with ThreadPoolExecutor(WORKERS) as ex:
        ok = dict(zip(files, ex.map(lambda k: job_baseline(files[k]['pd'], k, files[k]['text']), files)))
    log('baseline:', sum(ok.values()), 'ok of', len(ok))
    jobs = []   # mutation/contradiction skipped: this script runs layer 8 only
    log('step1+2a jobs:', len(jobs))
    sat = []
    for k, f in files.items():
        if not ok[k]: continue
        for d in f['decls']:
            if d.get('unparsed'): continue
            if LIMIT:
                names = [x.split('/')[-1] for x in LIMIT]
                if d['name'] not in names: continue
            sat.append((f['pd'], k, f['text'], d))
    log('step2b jobs:', len(sat)); SAT_T0[0] = time.time()
    with ThreadPoolExecutor(2) as ex:
        for i, _ in enumerate(ex.map(lambda a: job_sat(*a), sat), 1):
            if i % 10 == 0: summary(files, repomap); log(f'step2b {i}/{len(sat)}')
    job_satlink(files, repomap)
    summary(files, repomap)
    log('ALL DONE')


if __name__ == '__main__':
    main()
