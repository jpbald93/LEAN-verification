# Paper K — Layer 11: name and line anchors (draft v4)

Draft: `paperk.tex` (16 pp, 0 undefined refs), built 2026-11-17 09:07 EST from v3 after the round-2 review
triage (`REVIEW_TRIAGE_k2.md`: Argon 9 MINOR / Astra 6 MAJOR + 10 MINOR, all 25 dispositioned);
sha256 `49920863db5b02f64bbf62718c2516835915facf74e3127ab48a00dc92c3e846`, PDF
`bf01d137a656f8047377e2619b0be0ab7fb3c97bf5e352b1e4e56faa49760c6f`
(412,921 bytes). Repository snapshot at the pinned commit `464a59d` (parent `62ccf87`), which is the commit
that brings `PaperK/GeneralN.lean` into the gate — so the general-n declarations are gated.

Checker: `namegate_k.py` — every `\decl{Name}` must exist as a declaration in the snapshot, and every
`\src{File}{Line}` anchor must point at a line that begins a declaration. Snapshot dir `repo_flat_464a59d`
(the six library files at `464a59d`).

```
decls checked: 57
anchors checked: 18
decls that live only in the ungated general-n file: 0
NAME GATE PASS
```

Difference from draft v2 (recorded 2026-11-16 18:15 at `464a59d`): 56 → **57** base names checked, because v3
added `\decl{PaperK3.tetraFamR}` in §7. The 57 are base names: 67 namespace-qualified `\decl{...}` uses are
checked against the snapshot, and all 67 resolve.

Also fixed in v4, outside the gate's scope: every `\decl{...}` name now prints with a real underscore.
Inside the `\url`-based `\decl` macro the escaped form `\_` was being typeset as a literal backslash plus
underscore, so v1–v3 showed names such as `PaperK.B\_G\_cofactor\_row`; the macro argument now carries the
bare underscore and prints as `PaperK.B_G_cofactor_row`.

Anchors are text, not links: they resolve against the public tree at
`https://github.com/jpbald93/paperk_apollonius/tree/464a59df987e149e1e545cbd5299196ecce354ed`, which the
availability section names.
