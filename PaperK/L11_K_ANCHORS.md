# Paper K — Layer 11: name and line anchors (draft v5)

Draft: `paperk.tex` (17 pp, 0 undefined refs), built 2026-11-17 11:20 EST from v4 after the round-3 review
triage (`REVIEW_TRIAGE_k3.md`: Astra fix-check 0 open MAJOR, 2 partial and 3 new minor; Opus 2 MAJOR +
14 minor); sha256 `88d925345f1b4e39a5995caf973e69c4b6b8f000a6961f491c098bfcc6d7aa87`, PDF
`75b03c324792f6e2d2a43d516e1557c4d00dd169f65d51b28126fd0ecac4d289` (415,643 bytes). Repository snapshot at
the pinned commit `464a59d` (parent `62ccf87`).

Checker: `namegate_k.py` — every `\decl{Name}` must exist as a declaration in the snapshot, and every
`\src{File}{Line}` anchor must point at a line that begins a declaration. Snapshot dir `repo_flat_464a59d`
(the six library files at `464a59d`).

```
decls checked: 57
anchors checked: 18
decls that live only in the ungated general-n file: 0
NAME GATE PASS
```

Scope of the gate: 57 **base names**, from 67 namespace-qualified `\decl{...}` declarations in 116 uses. The
checker strips the namespace (`d.split(".")[-1]`), so `PaperK.equal_power` and `PaperK2.equal_power` are
indistinguishable to it. All 67 qualified names were resolved in their own namespaces by hand during the
round-3 review (Opus) and during triage: none is wrong. The gate does not check namespaces, and the paper's
preamble comment says so.

Changes from v4: none in the gate's scope. v5 changed §9 (battery scope note, linter provenance, Mathlib
pin), §11 (contribution framing), §7 (simplex wording, square clause), §5 (numerics figures), the appendix
caption, and re-pointed the evidence paths to the published folder (`numerics/...`, `layer13/...`,
`layer15/...`, `SCOUT.md`).

Anchors are text, not links: they resolve against the public tree at
`https://github.com/jpbald93/paperk_apollonius/tree/464a59df987e149e1e545cbd5299196ecce354ed`, which the
availability section names.
