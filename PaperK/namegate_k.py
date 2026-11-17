#!/usr/bin/env python3
"""Paper K — Layer 11 name/line gate (draft-time).

Checks two things against a repo snapshot taken at the pinned commit:

  * every \\decl{Name} in paperk.tex exists as a theorem/lemma/def/structure in the development
    (repo snapshot, plus the ungated general-n file, reported separately);
  * every \\src{Namespace}{File}{Line} anchor points at a line that begins a declaration.

Usage: python3 namegate_k.py [paperk.tex] [snapshot_dir]

Exit code 0 = PASS. Reports every failure with its name.
"""
import os
import re
import sys

TEX = sys.argv[1] if len(sys.argv) > 1 else "paperk.tex"
SNAP = sys.argv[2] if len(sys.argv) > 2 else "repo_snapshot_62ccf87"
GENERAL_N = os.path.join(os.path.dirname(TEX), "layer0", "paperK_general_n.lean")

DECL_RE = re.compile(r"(?:@\[[^\]]*\]\s*)?(theorem|lemma|def|noncomputable def|structure)\s+([A-Za-z0-9_']+)")
SRC_RE = re.compile(r"\\src\{([^}]*)\}\{([^}]*)\}\{(\d+)\}")
DECLARED = re.compile(r"\\decl\{([^}]*)\}")

text = open(TEX, encoding="utf-8").read()

files = {}
for fn in sorted(os.listdir(SNAP)):
    if fn.endswith(".lean"):
        files[fn] = open(os.path.join(SNAP, fn), encoding="utf-8").read()
if os.path.exists(GENERAL_N):
    files["paperK_general_n.lean (UNGATED)"] = open(GENERAL_N, encoding="utf-8").read()


def declarations_in(body):
    names = set()
    for line in body.split("\n"):
        m = DECL_RE.match(line.strip())
        if m:
            names.add(m.group(2))
    return names


by_file = {fn: declarations_in(b) for fn, b in files.items()}
all_names = set().union(*by_file.values()) if by_file else set()

fail = 0
decls = [d.replace("\\_", "_").split(".")[-1] for d in DECLARED.findall(text)]
decls = [d for d in decls if re.fullmatch(r"[A-Za-z0-9_']+", d)]
missing = []
for d in sorted(set(decls)):
    if d not in all_names:
        hits = [fn for fn, names in by_file.items() if d in names]
        if not hits:
            missing.append(d)
print(f"decls checked: {len(set(decls))}")
for d in missing:
    print(f"  MISSING DECL: {d}")
    fail = 1

anchors = SRC_RE.findall(text)
print(f"anchors checked: {len(anchors)}")
for _ns, fn, line in anchors:
    path = os.path.join(SNAP, fn)
    if not os.path.exists(path):
        print(f"  MISSING FILE: {fn}")
        fail = 1
        continue
    lines = open(path, encoding="utf-8").read().split("\n")
    ln = int(line)
    if ln > len(lines):
        print(f"  OUT OF RANGE: {fn}:{ln}")
        fail = 1
        continue
    if not DECL_RE.match(lines[ln - 1].strip()):
        print(f"  NOT A DECLARATION: {fn}:{ln} -> {lines[ln - 1].strip()[:70]}")
        fail = 1

repo_names = set().union(*[by_file[fn] for fn in by_file if "UNGATED" not in fn]) if by_file else set()
ungated = sorted(n for n in set(decls) if n in by_file.get("paperK_general_n.lean (UNGATED)", set()) and n not in repo_names)
print(f"decls that live only in the ungated general-n file: {len(ungated)}")
for n in ungated:
    print(f"  UNGATED: {n}")

print("NAME GATE PASS" if not fail else "NAME GATE FAIL")
sys.exit(0 if not fail else 1)
