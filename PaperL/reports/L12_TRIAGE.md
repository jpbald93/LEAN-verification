# Layer 12 — finding triage (2026-11-24)

Reviewer: Astra-class model (`gpt-6-astra`) via `opencode run`, brief `pl_review/BRIEF.md`, evidence
package = `DRAFT.md` v0.1 + `ANCHORS.md` + `REPORT_L10.md` + battery notes + `SCOUT.md`.
Verdict delivered: **MAJOR — 5 MAJOR / 6 MINOR / 0 NOTE**. All 11 findings were triaged the same day;
none was rejected.

| id | severity | disposition | what changed in `DRAFT.md` |
|---|---|---|---|
| L12-01 | MAJOR | applied | §1: "the second intersections of pairs … give n(n−1)/2 points; these lie on a circle" replaced by the subfamily-indexed description (each triple gives a level-3 circle; each quadruple a level-4 point) |
| L12-02 | MAJOR | applied | §2.1: the prose after `IsGCircleS` now states that the first disjunct is *any* `Metric.sphere o r` (r > 0 circle, r = 0 point-circle, r < 0 empty set), and that the empty case is carried rather than excluded |
| L12-03 | MAJOR | applied | §2.1: "differs … in exactly one respect" replaced by the two real differences (carrier `Set (OnePoint ℂ)`; generalized-circle clause at odd levels, sphere points at even) |
| L12-04 | MAJOR | applied + anchored | §4: the promotion/scratch timings now name their provenance (`notes/math-papers.md` rounds 26/26b) and state that the battery report covers jack only; §5.4 says the same of john |
| L12-05 | MAJOR | applied | §3: a paragraph records the layer-11 name gate (`L11_NAMEGATE.md`, 66 citations, PASS) and its extended anchor appendix covering the carrier/transport/terminal declarations that `ANCHORS.md` does not list |
| L12-06 | MINOR | applied | §2.4: "parent level-5 object" → "parent object — the subfamily obtained by deleting `c i`, whose object sits at level `2k+5` (level 5 only when k = 0)" |
| L12-07 | MINOR | applied | §3.2, L10.9: `crossVec` bridge marked **2×3 matrices only** |
| L12-08 | MINOR | applied | §3.2: the `cD_eq_zero_iff` sentence now says what it ties (the `Cospherical ∨ Collinear` reading) and that it does not bridge `IsGCircleS` |
| L12-09 | MINOR | applied | §3: scratch 5,611 = 5,344 + 267, promoted file 5,600 after the two gate-forced edits; no longer presented as a partition of the pinned file |
| L12-10 | MINOR | applied | §5.3: the §4 denominators **include** the 16 unattributed rows; those rows yield no verdict, so decisive counts are smaller |
| L12-11 | MINOR | applied | §5.5: the eight unused hypotheses belong to auxiliary lemmas; removing them strengthens those lemmas, and §2's headline statements are unaffected |

After the edits the draft is v0.2. The applied changes are textual only: no statement, number or
citation was altered; §3's tables and §4's figures are untouched (the name gate was re-run after the
edits and still passes 66/66).
