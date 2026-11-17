# SCOUT — prior-art search for Paper K (centres and concurrency of Apollonius solutions, ℝⁿ)

- **Date:** 2026-11-10 (UTC). **Purpose:** decide, *before* any proof dispatch, whether a formalisation paper on
  this subject can be novel. First run of `AFM/NOVELTY_SCOUT_PROTOCOL.md`, so this scout precedes all proofs.
- **Tools:** arXiv API (https), GitHub code search (`gh`, authed), Mathlib source at our pin on jack, AFP topic
  listing (checked for Paper J today, same page), web search.
- **Classification:** `EXISTS-FULL` / `EXISTS-PARTIAL` / `NONE-FOUND` (see protocol). Here the relevant axis is
  **formalisation**, since the mathematics itself is recently published and is not ours.
- **Caveat:** this is a *first-pass* scout. It decides dispatch, not the final claim wording; the pre-draft
  re-run is still required by the protocol.

## 0. Log

1. 2026-11-10, arXiv `id_list=2604.03067` and its HTML: read the abstract, introduction, §3.1–§3.2 statements,
   and the §4 corollary list. Source paper identified: **M. Płatek, *On the Inscribed Sphere and Concurrent
   Lines through the Centers of Apollonius Spheres in ℝⁿ*, arXiv:2604.03067v1, submitted 2026-04-03.**
2. arXiv `"Morita" AND "spheres" AND "tangent"` → 3 hits, only one relevant (2604.03067 itself); the other two
   are unrelated topology papers.
3. arXiv `"Lie sphere geometry" AND formalization` → **0**. `"Apollonius problem" AND "n dimensions"` → 0.
   `"Soddy line"` → 0. So no formalisation and, notably, no arXiv paper even uses "Soddy line" as a term.
4. GitHub code search, `language:Lean`: `Apollonius problem` → 1 hit, `tadamcz/annals-results` data tree (the
   local–global packing paper's candidate statement, unrelated). `Apollonian gasket` → **0**.
   `Apollonian` (25 hits, seen for Paper J) → no formalisation of the Apollonius *problem*, only packing
   number theory, atlas-lean's "Wanted" statement, and `trureturing`'s unrelated files.
5. Mathlib at pin `0df444a360`: no Lie sphere geometry, no Apollonius, no concurrency-of-centres material
   (re-checked today for Paper J; `Mathlib/Geometry/Euclidean/Sphere/` holds six files, all tangency/power).
6. AFP geometry topic page (all entries, read today for Paper J): nothing on Lie sphere geometry, Apollonius
   spheres, Soddy lines or concurrency of centres.
7. Web search: Płatek's paper is the only current source for the concurrency results; "Soddy line" as a term is
   used in triangle-centre literature (the line through the two Soddy centres), so the object is classical even
   though the general concurrency statement is new.

## 1. Candidate claims and verdicts

Source statements are Płatek's. Verdicts are about **prior formalisation**.

| # | Candidate claim (to be formalised) | Source | Verdict | Evidence |
|---|---|---|---|---|
| K1 | Given `n+2` cycles in ℝⁿ, with `{A_i, A_i'}` the two Apollonius cycles of `X ∖ {X_i}` for each `i`, all lines through the centres of `A_i`, `A_i'` are concurrent at one point `P_X` | Prop 3.1 | **NONE-FOUND** | no Lean/Coq/Isabelle/AFP development on Apollonius spheres at all (§0.3–6) |
| K2 | Two-step construction: the `n·2ⁿ` lines through the centres of the second-generation cycles `B_i, B_i'` also pass through `P_X` | Thm 3.4 | **NONE-FOUND** | same; no formal Lie sphere geometry exists anywhere (arXiv 0, GitHub 0) |
| K3 | Plane corollaries: concurrency of perpendicular bisectors and of angle bisectors recovered as instances; **Outer Apollonius' Circles Theorem** (a new triangle statement, author-added to ETC `X(1)`), and the duality `P, I, O₁` collinear ⟺ `P, I, O₂` collinear | Cors 4.1–4.4 | **NONE-FOUND** | the triangle-centre facts are classical; the general derivation and Cor 4.2 are 2026 and unformalised |
| K4 | Morita's theorem in 3D (four mutually tangent spheres + an outer sphere; the four inner spheres' inscribed sphere) and its `n`-dimensional generalisation: a cycle tangent to the hyperplane sets `T_i` exists, and its centre is `P_X` | Thm 3.6, Cor 4.7 | **NONE-FOUND** | Morita's own 3D theorem unformalised; the generalisation is 2026 |
| K5 | Soddy line as an instance; concurrency on the Soddy line for an Apollonian gasket, `n`-dimensional | Cors 4.9–4.11 | **NONE-FOUND** | packing number theory is formalised nowhere in Lean either (`soddy` hits = one repo, tangent families only) |
| K6 | General-n formal development of the Lie-quadric model: cycles as null projective points, tangency ⟺ orthogonality, Lie transformations, and `P_X` as a derived point | §2–3 | **NONE-FOUND** | no Lie sphere geometry in any proof assistant (§0.3) |

No row is `EXISTS-FULL`, and there is no `EXISTS-PARTIAL` competitor for any row: the closest existing Lean work
(`augmented-descartes-lean`) treats **mutually tangent** families through the augmented curvature–centre matrix,
which is a strict special case of "arbitrary `n+2` cycles", and it contains no centre-concurrency result. That
repo is a resource to build on, not a competitor.

## 2. Closest existing formal work, and why it is not prior art

- `JD-Jones-ASES/augmented-descartes-lean` — Descartes/Soddy identities, converses, completion, congruence, for
  tangent families only, matrix form, no Lie geometry, no concurrency. Its `Qₙ`/Lorentz machinery is the
  natural starting point for the null-cone model, and `Completion.lean` already manipulates `Qₙ`-orthogonal
  decompositions — but the objects there are `n+2` tangent members, not the `2(n+2)` Apollonius cycles of an
  arbitrary configuration.
- `facebookresearch/atlas-lean`, `lean-genius`, Coq `DescartesCircles.v` — 2D, algebraic, tangent-only.

## 3. Published mathematics (citations for the paper)

- M. Płatek, *On the Inscribed Sphere and Concurrent Lines through the Centers of Apollonius Spheres in ℝⁿ*,
  arXiv:2604.03067 (3 Apr 2026) — **the paper we would formalise.** Its two main results are Prop 3.1 + Thm 3.4
  (concurrency), and Thm 3.6 (existence of the inscribed cycle, centre = `P_X`).
- K. Morita, the 3D inscribed-sphere theorem (cited in Płatek as [15]) — the special case our K4 generalises.
- Apollonius of Perga problem; Lie sphere geometry (Cecil, *Lie Sphere Geometry*; Blaschke) — the framework.
- Classical triangle centres: incenter/circumcentre as Apollonius instances; "Soddy line" in triangle-centre
  literature. These appear in ETC (Encyclopedia of Triangle Centers).

## 4. Gaps of this search

- zbMATH/MathSciNet not searched; a formalisation in a non-indexed repository would be missed.
- GitHub code search does not see private or unindexed repos, and caps results.
- I did **not** verify Płatek's proofs. Formalising a 2026 paper means we inherit its correctness risk; the
  failure mode is discovering a gap or a wrong statement mid-build. The n = 2 instances (K1, K3) can be
  verified numerically first, cheaply.
- Zenodo/arXiv listing for Płatek v2+ not checked beyond v1.

## 5. What the paper may claim, and the feasibility note

- May claim: **first formal proof** of Płatek's concurrency and inscribed-cycle theorems, plus whatever
  `n = 2`/`n = 3` instances we prove by coordinates. Must not claim the mathematics as ours; must cite
  arXiv:2604.03067 in the title-level abstract, not a footnote.
- Infrastructure cost is the real risk, not novelty: nothing of Lie sphere geometry exists in Mathlib. The
  staged plan in `PAPER_K_PLAN.md` starts with coordinate proofs of the `n = 2` statements (no new
  infrastructure), then Morita in 3D (needs only sphere tangency + a linear solve), and only then the general
  `n` null-cone development.
- Honest fallback: if the general-n development proves too heavy, the paper is still a legitimate paper on the
  `n = 2` and `n = 3` cases (concurrency, outer-Apollonius theorem, Morita), all `NONE-FOUND`.
