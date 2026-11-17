#!/usr/bin/env python3
"""L15 gate: mechanical consistency of L15_COMPARE.md against src/.

Checks
  1. every backticked identifier `PaperK*.name` (namespace matched case-insensitively, so a
     misspelt namespace is caught) names a declaration in the file owning that namespace;
     every quoted Lean block (```lean ... ``` whose first line is `-- file: src/<f>.lean`)
     appears verbatim (whitespace-normalised) in that file, and every declaration it
     introduces is declared there;
  2. every SOURCE: block (the fenced block on the lines after a line `SOURCE:`) appears
     verbatim in src/main.tex after whitespace normalisation;
  3. every row of every table whose header has a `verdict` column carries a verdict in
     {E, O, N} and a non-empty `reason`;
  plus: the negative result is present (a `Negative result` heading and the phrase
  `does not fix`), and at least one table row exists.

Usage: python3 check_l15.py [path/to/L15_COMPARE.md]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "L15_COMPARE.md")
SRC = os.path.join(HERE, "src")
NS_FILE = {
    "PaperK": "paperK_lie_core.lean",
    "PaperK2": "paperK_degenerate2d.lean",
    "PaperK3": "paperK_3d.lean",
    "PaperKn": "paperK_general_n.lean",
}
DECL_RE = r"(?:theorem|lemma|def|abbrev|structure|instance|inductive|class)"


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def read(p):
    with open(p, encoding="utf-8") as f:
        return f.read()


def declared(text, name):
    pat = (r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
           + DECL_RE + r"\s+" + re.escape(name) + r"(?![A-Za-z0-9_'])")
    return re.search(pat, text, re.M) is not None


def main():
    fails = []
    md = read(MD)
    lean = {ns: read(os.path.join(SRC, f)) for ns, f in NS_FILE.items()}
    for ns, txt in lean.items():
        if not re.search(r"^namespace " + ns + r"\s*$", txt, re.M):
            fails.append(f"namespace {ns} not opened in {NS_FILE[ns]}")
    tex_n = norm(read(os.path.join(SRC, "main.tex")))

    # fenced blocks with their preceding line
    lines = md.split("\n")
    blocks = []  # (lang, prev_nonempty_line, body, lineno)
    i = 0
    while i < len(lines):
        m = re.match(r"^```(\w*)\s*$", lines[i])
        if m:
            lang = m.group(1)
            j = i + 1
            while j < len(lines) and not re.match(r"^```\s*$", lines[j]):
                j += 1
            if j >= len(lines):
                fails.append(f"unterminated code fence at line {i+1}")
                break
            k = i - 1
            while k >= 0 and not lines[k].strip():
                k -= 1
            prev = lines[k].strip() if k >= 0 else ""
            blocks.append((lang, prev, "\n".join(lines[i + 1:j]), i + 1))
            i = j + 1
        else:
            i += 1

    # prose with fenced blocks removed (identifiers are collected from prose + tables)
    prose = re.sub(r"^```\w*\s*$.*?^```\s*$", "", md, flags=re.S | re.M)

    # 1a. backticked identifiers
    ids = set()
    for m in re.finditer(r"`([^`\n]+)`", prose):
        tok = m.group(1).strip()
        # namespace = "PaperK" plus optional alphanumeric suffix (no "_": file names like
        # `paperK_3d.lean` are not identifiers)
        mm = re.fullmatch(r"(paperk[A-Za-z0-9]*)\.([A-Za-z_][A-Za-z0-9_'.]*)", tok, re.I)
        if not mm or tok.endswith((".lean", ".md", ".py", ".tex")):
            continue
        ns, name = mm.group(1), mm.group(2)
        ids.add((ns, name))
    for ns, name in sorted(ids):
        if ns not in lean:
            fails.append(f"identifier `{ns}.{name}`: unknown namespace {ns!r} "
                         f"(expected one of {sorted(lean)})")
        elif not declared(lean[ns], name):
            fails.append(f"identifier `{ns}.{name}` not declared in src/{NS_FILE[ns]}")

    # 1b. quoted Lean signature blocks
    nlean = 0
    file_ns = {v: k for k, v in NS_FILE.items()}
    for lang, prev, body, ln in blocks:
        if lang != "lean":
            continue
        nlean += 1
        bl = body.split("\n")
        mf = re.match(r"^--\s*file:\s*src/(\S+\.lean)\s*$", bl[0].strip()) if bl else None
        if not mf or mf.group(1) not in file_ns:
            fails.append(f"lean block at md line {ln}: first line must be '-- file: src/<one of the four>.lean'")
            continue
        fname = mf.group(1)
        sig = "\n".join(bl[1:])
        if norm(sig) not in norm(lean[file_ns[fname]]):
            fails.append(f"lean block at md line {ln}: not verbatim in src/{fname}")
        for dm in re.finditer(DECL_RE + r"\s+([A-Za-z_][A-Za-z0-9_'.]*)", sig):
            nm = dm.group(1)
            if not declared(lean[file_ns[fname]], nm):
                fails.append(f"lean block at md line {ln}: {nm} not declared in src/{fname}")
            ids.add((file_ns[fname], nm))

    # 2. SOURCE: blocks
    nquote = 0
    for lang, prev, body, ln in blocks:
        if prev != "SOURCE:":
            continue
        nquote += 1
        if not norm(body):
            fails.append(f"SOURCE block at md line {ln} is empty")
        elif norm(body) not in tex_n:
            fails.append(f"SOURCE block at md line {ln} not verbatim in src/main.tex: "
                         f"{norm(body)[:80]!r}...")
    stray = len(re.findall(r"^SOURCE:\s*$", md, re.M))
    if stray != nquote:
        fails.append(f"{stray} 'SOURCE:' markers but {nquote} attached fenced blocks")

    # 3. verdict tables
    nrows = 0
    tl = [l for l in prose.split("\n")]
    i = 0
    while i < len(tl):
        if tl[i].lstrip().startswith("|") and i + 1 < len(tl) and re.match(r"^\s*\|[\s:|-]+\|\s*$", tl[i + 1]):
            hdr = [c.strip().lower() for c in tl[i].strip().strip("|").split("|")]
            j = i + 2
            rows = []
            while j < len(tl) and tl[j].lstrip().startswith("|"):
                rows.append((j + 1, [c.strip() for c in tl[j].strip().strip("|").split("|")]))
                j += 1
            if "verdict" in hdr:
                if "reason" not in hdr:
                    fails.append(f"table at prose line {i+1}: verdict column without reason column")
                vi = hdr.index("verdict")
                ri = hdr.index("reason") if "reason" in hdr else None
                for rl, cells in rows:
                    nrows += 1
                    label = cells[0] if cells else "?"
                    if len(cells) != len(hdr):
                        fails.append(f"row {label!r}: {len(cells)} cells, header has {len(hdr)}")
                        continue
                    v = cells[vi].replace("*", "").strip()
                    if v not in {"E", "O", "N"}:
                        fails.append(f"row {label!r}: verdict {cells[vi]!r} not in {{E,O,N}}")
                    if ri is None or len(norm(cells[ri]).replace("*", "")) < 10:
                        fails.append(f"row {label!r}: empty or trivial reason")
            i = j
        else:
            i += 1
    if nrows == 0:
        fails.append("no verdict table rows found")

    # negative result must be present
    if not re.search(r"^#+ .*Negative result", md, re.M | re.I):
        fails.append("no 'Negative result' heading")
    if "does not fix" not in md:
        fails.append("negative result phrase 'does not fix' missing")

    if fails:
        print("L15 GATE FAIL")
        for f in fails:
            print("  - " + f)
        return 1
    print(f"L15 GATE PASS ({nrows} rows, {len(ids)} ids, {nquote} source quotes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
