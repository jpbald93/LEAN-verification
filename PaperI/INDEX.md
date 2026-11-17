# Paper I — supporting material

Companion to *Bicentric quadrilaterals, the arbelos, coaxal circles and inversion in Lean 4*.
The four Lean developments are separate repositories (`paperi_quad`, `paperi_circles`,
`paperi_arbelos`, `paperi_inversion`), pinned at the commits the paper cites. This folder holds the
evidence that is not code: prior art, the layer reports, the receipts, the battery reports, the reviews
and the name-gate output.

| item | what it is |
|---|---|
| `SCOUT.md` | prior-art scout, written before any proof was dispatched (`AFM/NOVELTY_SCOUT_PROTOCOL.md`) |
| `L11_ANCHORS.md` | Layer 11 name/line gate: every `\decl` and `\src` in the paper checked against the four trees |
| `namegate_i.py`, `namegate_i.sh` | the checker behind `L11_ANCHORS.md` |
| `L14_REPORT.md` | Layer 14 (Mathlib-vocabulary restatements), 50 restatements, no findings |
| `layer10/` | final commits: gate and tamper outputs, the four Layer-10 bridge modules, the battery reports quoted in §7, and `RECEIPTS.md` (clean-export rebuilds) |
| `layer13/` | Layer 13 blind re-formalisation: the blind statement file, the four comparer files, the comparator reports, the Bankoff naming audit and the gap-closure note |
| `layer15/` | Layer 15 classical comparison (both halves) and its Lean files |
| `reviews/` | the three external reviews of round 1 and the consolidated triage of both rounds (`REVIEW_TRIAGE_v4.md`, `REVIEW_TRIAGE_v5.md`) |

Notes that a reader of the paper needs:

- The battery numbers in the paper are quoted from `layer10/battery_final_*.md` at the four pinned
  commits; the survivors are named there individually.
- The shift from "fresh clone" to "clean export" in the paper is because the repositories had no remote
  when the receipts were taken; `layer10/RECEIPTS.md` records the export procedure and digests.
- Layer 13's blind input is more damaged than the paper's first draft said; `layer13/` carries the
  reports rather than a repaired input, and §7 of the paper describes it accordingly.
