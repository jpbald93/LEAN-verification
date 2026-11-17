# Paper K — Layer 11: name and line anchors (draft v2)

Draft: `paperk.tex` (15 pp, 0 undefined refs), built 2026-11-16 18:15 EST from the v2 that carries all 36
`REVIEW_k_draft1.md` findings; sha256 `c2ddafe7`, PDF `c713bcab`. Repository snapshot at the pinned commit
`464a59d` (parent `62ccf87`), which is the commit that brings `PaperK/GeneralN.lean` into the gate — so the
general-n declarations are no longer "ungated".

Checker: `namegate_k.py` — every `\decl{Name}` must exist as a declaration in the snapshot, and every
`\src{File}{Line}` anchor must point at a line that begins a declaration. Snapshot dir `repo_flat_464a59d`
(the six library files at `464a59d`).

```
decls checked: 56
anchors checked: 18
decls that live only in the ungated general-n file: 0
NAME GATE PASS
```

Difference from draft v1.1 (recorded 2026-11-16 16:12 at `62ccf87`): 54 → **56** names checked, and the seven
names that were reported as living only in the ungated general-n file (`Cyc`, `aff`, `brief_E_false`,
`cex_orth`, `cex_pt_ne`, `simplex_E1`, `simplex_circumradius`) are now ordinary gated declarations — the
promotion stage added them to `gate.sh`'s `REQUIRED` list, which is what moved the gate from 60 to 73.

Anchors are text, not links: the repository still has no public remote, and the paper says so in its
availability section rather than printing dead URLs. Phase 9's deposit kit carries the push.
