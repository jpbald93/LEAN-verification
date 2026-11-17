#!/usr/bin/env python3
"""Paper I layer 11 (name/line anchors).

For every \\decl{X} in the paper: X must exist as a declaration in one of the four
pinned repositories.  For every \\src{repo}{dir}{file}{line}: that line of the pinned
tree must be a declaration, and its name must be one of the \\decl names given in the
same table row (the "declaration of that name" check).

Usage: python3 namegate_i.py [--tex paperi.tex] [--cache DIR] [--refresh] [--md]
"""
import argparse
import os
import re
import subprocess
import sys

HOSTS = {
    "paperi_quad": ("jackagent@100.72.132.55", "~/final_quad"),
    "paperi_circles": ("jackagent@100.72.132.55", "~/final_circles"),
    "paperi_arbelos": ("john@100.101.160.66", "~/lean/final_arbelos"),
    "paperi_inversion": ("john@100.101.160.66", "~/lean/final_inversion"),
}

DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
                     r"(theorem|lemma|def|abbrev|structure|class|instance|opaque)\s+([A-Za-z0-9_'!?.]+)")
FETCH = (r"cd {path} && echo HEAD $(git rev-parse --short HEAD) && "
         r"git status --porcelain | head -20 && "
         r"find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | "
         r"while read f; do awk -v F=\"$f\" "
         r"'/^(private |protected |noncomputable |partial |unsafe )*(theorem|lemma|def|abbrev|structure|class|instance|opaque) /"
         r"{{print F\"\\t\"NR\"\\t\"$0}}' \"$f\"; done")


def fetch(repo, cache, refresh):
    host, path = HOSTS[repo]
    out = os.path.join(cache, repo + ".tsv")
    if os.path.exists(out) and not refresh:
        return out
    cmd = "ssh -o BatchMode=yes -o ConnectTimeout=20 " + host + " \"" + FETCH.format(path=path).replace('"', '\\"') + "\""
    # simpler: build remote command without nested quoting games
    remote = ("cd %s && echo \"#HEAD $(git rev-parse --short HEAD)\" && "
              "find . -name '*.lean' -not -path './.lake/*' -not -path './scratch/*' | LC_ALL=C sort | "
              "while read f; do awk -v F=\"$f\" '"
              "/^(private |protected |noncomputable |partial |unsafe )*"
              "(theorem|lemma|def|abbrev|structure|class|instance|opaque) /"
              " { print F \"\\t\" NR \"\\t\" $0 }' \"$f\"; done") % path
    r = subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=20", host, remote],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit("ssh %s failed: %s" % (host, r.stderr.strip()))
    with open(out, "w") as fh:
        fh.write(r.stdout)
    return out


def load(path):
    head, dirty, decls = "?", [], {}
    for line in open(path):
        line = line.rstrip("\n")
        if line.startswith("#HEAD "):
            head = line.split()[1]
            continue
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        f, ln, text = parts[0], parts[1], parts[2]
        m = DECL_RE.match(text.lstrip())
        if not m:
            continue
        f = f[2:] if f.startswith("./") else f
        decls[(f, int(ln))] = m.group(2)
    return head, decls


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tex", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "paperi.tex"))
    ap.add_argument("--cache", default="/tmp/afmrun/paperI/anchors")
    ap.add_argument("--refresh", action="store_true")
    ap.add_argument("--md", action="store_true")
    a = ap.parse_args()
    os.makedirs(a.cache, exist_ok=True)

    heads, trees = {}, {}
    for repo in HOSTS:
        p = fetch(repo, a.cache, a.refresh)
        heads[repo], trees[repo] = load(p)

    tex = open(a.tex).read()
    body = tex.split(r"\begin{document}", 1)[-1]
    body = re.sub(r"(?<!\\)%.*", "", body)  # strip comments

    decltok = re.compile(r"\\decl\{([^}]*)\}")
    srctok = re.compile(r"\\src\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}")

    all_names = {}
    for name in decltok.findall(body):
        for n in [x.strip() for x in name.split(",") if x.strip()]:
            all_names.setdefault(n, 0)
            all_names[n] += 1

    missing = []
    for n in sorted(all_names):
        short = n.split(".")[-1]
        found = any(short in {d.split(".")[-1] for d in trees[r].values()} for r in trees)
        if not found:
            missing.append(n)

    anchor_rows, bad_line, bad_name, unmatched = 0, [], [], []
    for lineno, line in enumerate(body.splitlines(), 1):
        if r"\src{" not in line:
            continue
        decls = [x.strip() for name in decltok.findall(line) for x in name.split(",") if x.strip()]
        shorts = {d.split(".")[-1] for d in decls}
        # one anchor per \src, plus bare ", N" continuation numbers
        pos = 0
        for m in srctok.finditer(line):
            repo, d, f, ln = m.group(1), m.group(2), m.group(3), m.group(4)
            if m.start() < pos:
                continue
            nums = [ln]
            rest = line[m.end():]
            cont = re.match(r"\s*((?:,\s*\d+)+)", rest)
            if cont:
                nums += [x.strip() for x in cont.group(1).split(",") if x.strip()]
            for n in nums:
                anchor_rows += 1
                key = ("%s/%s.lean" % (d, f), int(n))
                if key not in trees.get(repo, {}):
                    got = None
                    # try to find the file under a different dir spelling
                    cand = [k for k in trees.get(repo, {}) if k[0].endswith("/%s.lean" % f)]
                    if cand:
                        k2 = [k for k in cand if k[1] == int(n)]
                        got = trees[repo][k2[0]] if k2 else None
                    bad_line.append((lineno, repo, d, f, n, got))
                    continue
                got = trees[repo][key]
                gs = got.split(".")[-1]
                if shorts and gs not in shorts:
                    bad_name.append((lineno, repo, "%s.lean:%s" % (f, n), got, sorted(shorts)))
            pos = m.end()
        if r"\decl{" in line:
            pass

    # decls inside a row with anchors must exist in that row's repo
    repo_by_line = {}
    for lineno, line in enumerate(body.splitlines(), 1):
        m = srctok.search(line)
        if m:
            repo_by_line[lineno] = m.group(1)
    # (row-level repo presence check)
    row_missing = []
    for lineno, line in enumerate(body.splitlines(), 1):
        if lineno not in repo_by_line:
            continue
        repo = repo_by_line[lineno]
        decls = [x.strip() for name in decltok.findall(line) for x in name.split(",") if x.strip()]
        names = {d.split(".")[-1] for d in trees[repo].values()}
        for d in decls:
            if d.split(".")[-1] not in names:
                row_missing.append((lineno, repo, d))

    out = []
    p = out.append
    p("# Paper I — Layer 11: name and line anchors\n")
    p("Generated by `AFM/PaperI/namegate_i.sh` against the final trees:\n")
    for r in HOSTS:
        p("- `%s` at `%s` (%s)" % (r, HOSTS[r][1], heads[r]))
    p("")
    p("| check | count | failures |")
    p("|---|---|---|")
    p("| `\\decl` names in the paper | %d | %d |" % (len(all_names), len(missing)))
    p("| `\\src` anchors | %d | %d not a declaration |" % (anchor_rows, len(bad_line)))
    p("| anchor name matches its row's `\\decl` | %d | %d |" % (anchor_rows, len(bad_name)))
    p("| row `\\decl` present in row's repo | %d | %d |" % (sum(len(decltok.findall(l)) for n, l in enumerate(body.splitlines(), 1) if n in repo_by_line), len(row_missing)))
    p("")
    if not (missing or bad_line or bad_name or row_missing):
        p("**NAME GATE PASS**")
    else:
        p("**NAME GATE FAIL**\n")
        for n in missing:
            p("- DECL MISSING: `%s` not found in any pinned tree" % n)
        for lineno, repo, d, f, n, got in bad_line:
            p("- SRC NOT A DECLARATION: line %d `\\src{%s}{%s}{%s}{%s}`%s" % (lineno, repo, d, f, n, (" (found: `%s`)" % got) if got else ""))
        for lineno, repo, loc, got, shorts in bad_name:
            p("- NAME MISMATCH: line %d `%s` declares `%s`, row decls %s" % (lineno, loc, got, shorts))
        for lineno, repo, d in row_missing:
            p("- ROW DECL MISSING in %s: line %d `%s`" % (repo, lineno, d))
        for r in HOSTS:
            pass
    print("\n".join(out))
    return 0 if not (missing or bad_line or bad_name or row_missing) else 1


if __name__ == "__main__":
    sys.exit(main())
