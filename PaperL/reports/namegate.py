#!/usr/bin/env python3
"""Layer 11 name/line gate for Paper L (v0.11).

Checks every `Clifford/<File>.lean:N` citation in DRAFT.md against a line-numbered dump of the
pinned tree. All citation forms are read: backticked, inside code comments, comma lists
(`File.lean:119,152`) and table rows. For each cited line the line must be a declaration. Where the
draft writes a citation in the form `name` (`File.lean:N`), the declaration name is checked too.
Table rows of §3.1/§3.2/§3.3 are additionally checked against the name in the first column.

Usage:
    ssh jackagent@<host> 'cd ~/paperL_jack && for f in Clifford/*.lean Clifford.lean gate.sh; do \
        echo "@@@ $f"; grep -n "" "$f"; done' > tree.txt
    python3 namegate.py DRAFT.md tree.txt            # counts + PASS/FAIL
    python3 namegate.py DRAFT.md tree.txt --report   # also emit the markdown report
"""
import re
import sys
import collections

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)?'
    r'(theorem|def|lemma|abbrev|structure|inductive|instance|class|opaque)\s+([^\s:({]+)'
)
CITE = re.compile(r'(Clifford/[A-Za-z0-9]+\.lean):([0-9][0-9,]*)')
ATTR = re.compile(r'`([A-Za-z_][A-Za-z0-9_.\']*)`\s*\(\s*`?\s*(Clifford/[A-Za-z0-9]+\.lean):([0-9][0-9,]*)\s*`?\s*\)')
ROW = re.compile(r'^\|\s*[^|]+\|\s*`([^`]+)`\s*\|\s*`(Clifford/[^`:]+):(\d+)`')


def load_tree(path):
    tree, cur = collections.defaultdict(dict), None
    for raw in open(path, encoding='utf-8', errors='replace'):
        raw = raw.rstrip('\n')
        if raw.startswith('@@@ '):
            cur = raw[4:].strip()
            continue
        m = re.match(r'^(\d+):(.*)$', raw)
        if m and cur:
            tree[cur][int(m.group(1))] = m.group(2)
    return tree


def decl_at(tree, f, line):
    m = DECL.match(tree.get(f, {}).get(int(line), ''))
    return (m.group(1), m.group(2)) if m else (None, None)


def main():
    draft_path, tree_path = sys.argv[1], sys.argv[2]
    report = '--report' in sys.argv
    tree = load_tree(tree_path)
    text = open(draft_path, encoding='utf-8').read()

    occurrences = []
    for m in CITE.finditer(text):
        f, nums = m.group(1), m.group(2)
        occurrences.append((m.start(), f, nums))

    pairs, occ_count = set(), 0
    for _, f, nums in occurrences:
        for n in [x for x in nums.split(',') if x.strip()]:
            pairs.add((f, int(n)))
            occ_count += 1
    distinct = sorted(pairs, key=lambda x: (x[0], x[1]))

    fails = []
    resolved = {}
    for f, l in distinct:
        kind, name = decl_at(tree, f, l)
        resolved[(f, l)] = name if kind else None
        if kind is None:
            fails.append((f, l, 'NOT A DECLARATION', tree.get(f, {}).get(int(l), '')[:70]))

    attr_checks = 0
    for m in ATTR.finditer(text):
        want, f, nums = m.group(1), m.group(2), m.group(3)
        for n in [x for x in nums.split(',') if x.strip()]:
            _, got = decl_at(tree, f, n)
            attr_checks += 1
            short = want.split('.')[-1]
            if not (got == short or (got or '').endswith('.' + short)):
                fails.append((f, n, f'ATTRIBUTION: expected {want}, found {got}', ''))

    rows = []
    for i, line in enumerate(text.splitlines(), 1):
        m = ROW.match(line)
        if not m:
            continue
        name, f, l = m.group(1), m.group(2), m.group(3)
        kind, got = decl_at(tree, f, l)
        short = name.split('.')[-1]
        ok = got == short or (got or '').endswith('.' + short)
        rows.append((i, name, f, l, got, ok))
        if not ok:
            fails.append((f, l, f'TABLE ROW {i}: expected {name}, found {got}', ''))

    for m in re.finditer(r'`:\d+`', text):
        fails.append(('(in text)', m.group(0)[1:-1], 'SHORTHAND CONTINUATION: write the full `Clifford/File.lean:N`', ''))
    bare = [m.group(0) for m in re.finditer(r'(?<![\w.])lines? \d+[^,\d]', text)]
    ranges = [b for b in bare if b.startswith('lines ')]
    singles = [b for b in bare if b.startswith('line ')]

    print(f'occurrences: {occ_count}  distinct pairs: {len(distinct)}  '
          f'attribution checks: {attr_checks}  table rows: {len(rows)}')
    print(f'bare-line tokens: {len(singles)} single, {len(ranges)} "lines A-B"/ranges')
    if fails:
        print(f'FAIL: {len(fails)}')
        for x in fails:
            print('  ', x)
        sys.exit(1)
    print('PASS: every citation resolves to a declaration; every attributed name and table row matches')

    if report:
        out = []
        out.append('# Layer 11 — name/line gate, Paper L v1.0\n')
        out.append('Instrument: `namegate.py` (this directory), run against a full line-numbered dump '
                   'of the pinned tree (`jack:~/paperL_jack`, `Clifford/MorleyKernel.lean` sha '
                   '`4beb169a…`, gate 37 declarations). It reads every `Clifford/File.lean:N` citation, not only backticked '
                   'ones: prose, code comments, comma lists and table rows.\n')
        out.append(f'**Result: PASS.** {occ_count} citation occurrences, {len(distinct)} distinct '
                   f'`file:line` pairs, all resolving to a declaration; {attr_checks} attribution '
                   f'checks in the `` `name` (`file:line`) `` form all matching; {len(rows)} table '
                   f'rows (gate list, bridges, statement declarations) all matching the attributed '
                   f'name.\n')
        out.append('## Distinct citations\n')
        out.append('| file:line | declaration found |')
        out.append('|---|---|')
        for f, l in distinct:
            out.append(f'| `{f}:{l}` | `{resolved[(f, l)]}` |')
        out.append('\n## Table rows checked (name → declaration at line)\n')
        out.append('| draft line | name in draft | file:line | declaration found |')
        out.append('|---|---|---|---|')
        for i, name, f, l, got, ok in rows:
            out.append(f'| {i} | `{name}` | `{f}:{l}` | `{got}` |')
        out.append('\n## What this gate does not check\n')
        out.append('Names and lines only. It does not compare signatures or hypotheses; the '
                   'signature anchors for the statement declarations are the rows of §1.3 of the '
                   'verification record, which anchor a line, not a type. The hypothesis-level audit '
                   'is layer 12\'s job, run on v0.1; the reviewer passes on v0.2, v0.3, v0.7, v0.9 and '
                   'v0.10 are recorded in Appendix C of the verification record.\n')
        open('L11_NAMEGATE.md', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
        print('report written: L11_NAMEGATE.md')


if __name__ == '__main__':
    main()
